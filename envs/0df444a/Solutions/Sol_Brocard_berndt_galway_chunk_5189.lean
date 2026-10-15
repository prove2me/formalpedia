-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5189
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T15:02:40.484386+00:00
-- url     : https://prove2.me/submissions/d69f6b88-727e-4590-92e2-7719d939da19

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 933093525 ≤ n < 933273381 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 933094775 1250 933093525 933093571
    0x130606090e0718060f080f22050a0506130c0b0412020607051608011e061508060d060e031305030d0c021014030108060121050d08190c0801031118 64
    0x3895140c9480b00c40c43c84400000b036550f9006403603251410095460305200d80750b00ba034141441c80281d8400c0031604c0c10715002e00340381b188a00d0f29035585000384112510410030b500c8050901ca0192084910480c200301100180003494014070000c00312055824174240c034001c0d417603280f11007418000740326910014034002071080801c9aa1044149a44500142e65807851054002d00d000055079040f00080040c00c900d029061042d502100c00682c0c4511402340c40001c1181c01c144018001980109031f13400315800300b80e007880f40e56008100d0070011559411610f40c41c2d0b421240700c0d40305a129a010703c1c09919007a610590140c1090380c103464030b0030824014a0103072003003121707841c000c20104004000011400703000101ca41c104c9410000c050f004210301c4800d40700103c3c001e00080e00761750103d1210304169201c0c4901d40c3e03114028104500b4a0105e480f4140d05039034440c1c01d80d20004200f04014010b0242a00301001e40420898842c04680c008540c90750300079a00903c41491006907a007041c1001d = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 933096025 1250 933094775 933094787
    0xb0c07080d0f0504050f160b0a030e06040303021213020f040507030209031204050f0f09011a07150c090b031e18060106020f0f0d080a2315130606090e07 67
    0x3116820105021080b424a112401801c040b00e06030f940f8419403040c02c0c6a280046005144001c070721115030b6150341480301080051340300c2144001055607821702d601d505c07601804840d010314803d030740240c2c2d118400200002032110241c00f0071340306039184802e080141c0e101520383c403940c6d02c1550046010b0380c034400300394002d000e18540160540104811710034914a5840203109894007190300c0307095a82000c00740708005500c40d00c03183d04440715400508c00380084080040c0b14a403c2c20b80c2c245003590940d078090b08202c4500206e10078a80f036110140a5981020601010f8051051868214500100080f141043c039030172600c501e101034400b20381d003d140070460716009490f0750100c0b005940d44000003540c0741c2c1409000700042c000c941d0010407080780071070503044946490b039400180b500c0b10301d2000300500b21810500060b06101c50070480c24602c855140e2711031803c040d0a41c1410300d2990500041e150703e440e41c8030505240c03000920450b500f0000302000e85064008024007aa101c100230344507 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 933097275 1250 933096025 933096037
    0x8070f0c0206030c1b032b06031b140f0f0f040f0e0d020f010905030414121b01020106080c1509190b0d0b010807020d14040315060501030b0d0b0c0708 66
    0x2c90800410030403040b403000d00034800b20020031100e0a603170090034112a100d00600d034001401003002e501001c41d00c164001442003400c0c6050000038503565075a03e680e90023091000a1602400d05031080000c0c011082000900980550764200f0710f004560009655802d03407001d0502c00c44141c900c0b009161501d5010044812400f841085080c2c00d1400482d030b14215118a10014030a142060b00c80c400306005076201c2c2a40b00e0001c40c20241461031400041007030b0045c2540012801407549240001041401090880c03000b9000d00300300c941000a00392083d0341c010b40b000780e000c076009144a0f264001d1a020101401251b41c1e15808a9000500030910082080c1000d0382c0c40c28001ca018400b4100428080d80142c0082002d04a084c00544000320b0031250040560400c00320681424014000e4402c4e100c004449a464070741c90760755140413488900300000707906944080511140d60075110b800141c40049803c805000c90702c1c0c1e5940e00f264001004218016408a0b522082100c044288c0340 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 933098525 1250 933097275 933097279
    0xe1009051c02010c390503191d090a09081201050108100501021209030102071211010c031406091807060306050306090a080a050c0c090f04060b042708041a0705010c0f08070f0c02 78
    0x2c6800002e09046559030422310403207004424552040b009240902c0442007030300400704040781e0001b103010821800701c070011b0608826030b171280340c00400615950010001542016503203052541000d0004112440003001c28451310800707403090290b6a000500d00d201d02c1101062103070386007558808680a4040c240300201116004903040200070f4016600302d480c000084020011020620002c506075030740741c1c0c080c14800140201082c80e5090540045502c110300040910507114040106440d004160344042d0001c2c4c0d444c90107102c50301c3d0a000c03543d00650400010205160b041d203c10a55104100280c0c0510030700040800c18140c3c2441a8080e007900200b184800c1d2038010002600b280044401701d9400b85800500c03d914580351140b41040c1056050340404441e20003240c2101020f40e21099400c2ca2040c04001141c0300b80c0130044038020403149203951500c5080c40c2050030740c0d20300c1c4500d60600080203840030041e46d100030906e60051a0b4603021990314485041030b2406000f401d4003039 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 933099775 1250 933098525 933098627
    0x50d0b0f030d111908070b0a240806060402090307232706181311040608070302010206220803040609051b12150403030e1009051c02010c 60
    0x50b440030b0b0480c090b202c503000110142c40030034280e225840404a90390500908251003070050001040d28661041c2d030140c4a1600000d001c010700c4006400c80034800410b0860a006100c1480041304c140406900180b040d9401c0d1706020b44800000d460f8072507400744c0040340701c5040d02040100c140c040404e06144018043d80340c00200100300f03144d0141303c00c0351102a007601c0c8001c50040d0400719002904641c555201a13503540751021380c40c045c528858000d6031000c440f203603200c8060740e0794840c031801800c803000140b04007440c52001a0400340c000b440c0745403804210440c1c2a608048032504104141e02c204070580d20361362450200000c001c20230700900b181c41060202640844519136456000100b100d040304e140d075007180f9555481c404101172800303008900f40400c0000780660821000d8040400955803010303601d49451080381e40582094440b039100701c0540903640d480302d0f050007007109148000d0020505002010b000c1c20018029500900400b0641c0003150040c4001c45440401d40c0c4480 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 933101025 1250 933099775 933099793
    0x90306020d020a030b18180304030c0b040509070503040f02150c0f011d070f05190510180905010303021e0304081209120601120602090a0506070f1110050d0b0f03 71
    0x1001c000d4110801e480b011170300d4441403400c44c0c5030207020f18140b40c8002e00b0120441d680e49000003401000d01042074498801032201000164035404400082c1c8180342116485504d41410050308600180080c4244a0101b00340000715143c104403034540d680655190151050740403400040c4d10070404400c5950145c507008000e514410340101d164000a6024040030001c414020f6449000520031407802c142d000e40100054100844017004030010780c4940c03400183e862001c02c44014109011800148c40000152700380b04081e104c90b4054100f10804100355810f556029541c0c0001034031011981c0485410003410480410072100030340301c00d90a540c85034103c103e0380d0340c15410148059209128100c041d0072421400a00241220b20b24108655460156125400294441c1c03955035042a0000400320f026105d00f4000c20840b03200768510b02c00c0001d141050405c40a156032110f01c205080801003501c00c0e8044190b40504d8403c0c100042c61440c4000061039260000f03814503010b016042e04 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 933102275 1250 933101025 933101047
    0x2041d06031e01020a120b13270b0906090a1709220905190c031209081506040b010c02150d0209040c0203030921042303060901020c0c0102072409030602 67
    0xd4a607102c1c172600d40030b14843c409201442681c520084c0f103074100141c0c42e0300c2c0c003042c180e90b040401031010242e9040a046020402d010304540c1405003960004010800c0c0881540100a8254030050820207060f003181c0995501e01c032003d0000c1010320030708020410101e0f958401c4956110aa610341c1e02003090301c400300590006d009150415500d6003d0010600700c00100c052603545041da100d28407114050459846030918405003a03a201000841c100c041038501082020701807200c1d40442c0ea00765442d0007410030094403040b8248604001c2600c00840c0103840d90b43c1420386400c0201111502d40801d0780010000f400340142040c2d00600344118400c003643c021006601404480d000e40d510600402c60400e00d4500602c2e00c601210300030401088404a807402c90300c0083c2e4411055000c0584810011713140600580e802080b0707950010340100d41c03407410861103550150a0001c7e000507840d0814602c400c401e039164041c604584031100c50640740c82001c03c4000380d507002404540b5404480a = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 933103525 1250 933102275 933102277
    0x40f0606090b09101416030338150f0d090b180a0f060b19320d0611030103030306050a05090f070c1b030605160302041d06031e0102 58
    0x450200420510080854000b150004649041c000540a440b810300c200a08980d000b010599401501009010b4500815a551950500c00740656004505181230a80700f4403c80d0035622482d0003032403543e0010f1001108069072001d0224211824a00d9481ca21203101071407180e040b41042c00000000c0011440843e45c3c810b0010750301403c0c94a041d0340e189800345520501f5848601010740c0500c20640006502c6001030400d10f10680000c5104001480499404c0c2400981240d281400010a00005a0030745064082c4020300c8142502d0b05041070980208a203940140b44c00342c2c4111002d0002c0c01015080604103001e0095001d58a41e0742e82001401049a4003e162243d0000c4100041c030745016581c0328012036440c0b00c0184c00ba02c403200140c80500c2170060458540d0601c00c002d80c0c450a520314a00d008502840011403240380200c042180071080c0804601454030610041c0202c5031f00d040f80c0390302ca00d9000f0490406848910010b85048494205101c016610410701e541c1418190 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 933104775 1250 933103525 933103529
    0x803040b13050f010207270e03030a152709080a110106050d230c12100506040e030304020d030201060801050705071203050c03160309050f0a020108092e0b040f06 71
    0xe100c1c0c215603841d60200305060084040c1980180d001c072406010100c1d95440301d1a0341142c413160a05204110202c040946005600040b082c0d0000720411424202c98010f481142c900420103030001814a540403580981c503110b60450b800b190056440c40d44115400348071226006098035454080c00807000340380308800c00c0710100c65420503000107814205030700f1300380b0f0442d80a55602009421074064040120002043d0002442503015409164680090840c0c0c4242d1034406440b40e840d521204500742d40c0081c00d8140034901c0d011040c00700b00c0b008401c0e240c20907412603c41c2d500c8102400e00b2400340039150401c041f10752a2006000c0b215400c803004100b401c0c800c003466409440344800940c12a60101c1d0894501c8000700001400342c4023802e5401c022150b1070030f0014196083c0e8a5044c505042ca600c06602c680c01408400251f60300811103c1c1d0003009032000301403078031094076a0a4040e0f01030341c010b4080d201d101880e0341001c826401c000d18194002e8070401c400203002c608180900024 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 933106025 1250 933104775 933104797
    0x2010c0213091a1605090321031b030411150415090e1f050103021b030304080705150405030720030a05010501090b010302090303070b100506070606060306090e06150a0803040b 77
    0x5415034000e01074051040b078420a50000304c880d00920312042528036600c4001d105034580600700c03d0540444251580f10208600f004c800d68803480d0140c16240c000255020500750104284100400210795840c05500780b402511800440103002c0c0317184075070380526000890084501464001d04a51260124044800c0c1d50103e1900d0f49480c4030324048091aa01041a200c8a440d07040c000e95000b40c0041450412407002002c0e8001540321440c21908155422a442d07507002696100b4018204440c00b00094140c101c020a410f056982a0f074901c0f40310001480300400d800350903000c10841401201c0002c014080c1d4505c2d50840c42c0c900e00801090040e0603141d450074055a0655200b031090304c1d40010060001c1d454805140c40d000b038108001891101c1b008800c03580400c4984458010706602445820082200e13428004094161400d540000381c886181240540468400290103900010340c084032030030901c1c020000c14070b0341040380c220b200c042c0300020f40004e92503c01002420070381c4c04 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 933107275 1250 933106025 933106043
    0x209090711060c03010e060d03110712110301020408030304030e03010209062818030f05030c070f180902011b1110020304050a0e0103020d080a02030712050322150902010c021309 78
    0xf9191030000c180c002030042c03100681e0580d0014243e41020041415140d00070b04214007800d0180603050b05c0d000f4180c10038580100c920514404006008603080824030b000c80081d82032600301080d241d62400000c101808100e4071480070038040d14203504856062001411f0383e80c2c0c40d20200c20b551030302800b603100106070706000c43c04000c0c0c05101c0c803407034220f202120b442d50f03000ba0700d15198070a040c05620001e032000d020030045040070900c00c20101c801031100d0b00b2903c4200f8904040d02d190200c481400403152428040d00c0340060380d02c02c04502d81450706080302d4158004500b000c00d40030710040c4030290400e40203031116819a400201810440344111100e4101c20385070b08a00001c04002e110003500801c441400b44005154100546a4002288101d909000e601d0711040700b07141c040002c000200350004180401c0c02032441100e001c6181c11380d540860542c0e669115040d141c0c0c2141c0d0005d02e2a034480e502e004582c403035140c0c02c1c1541c0d00102902c800e0142000103200525400c02d080310320300c003 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 933108525 1250 933107275 933107281
    0x711120601030c17010612030e0a06030b090c21040305030105120a05120717040e01030309050618090615190f112104031a010602010518030418020909071106 69
    0x100000d9914142d9600803500d5003107600e03143e40160340c500110052a880e540750000850030788042d0381c4021032240a507032450401344c0b00390140400882c217504400201403c040401605451304c10510750002c0b030741e2845503a1f62641640c0c0094124510b4001949000303050280800d0681c060041c2d0f06039101121050446184004503d603144c40c1c44070014001d0304003a850000386100341c400f8000048c0126001c2d10400760460000c00f141e4015017190540903020360061003030641c03054220020305029240b107451720340c44440c46041c103031080468522644105001500e0360b00c504e84048003040d20415915120724410305109404c01003804088002030560150002c00c6100300000d0130b483c0c1194010b8485d41441d240544001e5140c910341171a4280d01b00000070000d4101c4501807420300340c208502515504054001342500c1c0058428a0042c8111071b918844400110841c3c04952101a01c0d4001e0b100407142d1030040c0c000c44180c2ca521000a00400041030b1700304c44003c055103254001e5510540d = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 933109775 1250 933108525 933108559
    0x303020f0d05040c09060f0506030a0e0f0109060c0f0203090409030e040606121401050112050a0212160207080c0102030d15150903050c0108040c03110d05030a0e03070504050708060d080403080711 86
    0x140c1b0920071006004e0780b41004000364104080110f410598000c03002c40c01c514103820803458802d19092400c0b1981d514070440342880340c02e00c65441801114500082d00043d4080700940d00e003e5091703014816603980312650304050246505c1c0f924004054001c0c44815070302c680240811a0183d01891558140584500c4c000004c3e00c0080c161380058403540b44421a14002600030304009080c0341500e40e0030080411038003080b60509104007901c902c200400c1c0440c4074028200700096001c000750b5800b6482da000c4030381e0041b081e0762501c0011500094911032140319043d080409501c01c0400c240c0c400c0d8866426035010b030101060300e01070011101c4401007007004452035002110064400d2404000520004a01300003415031840001c0066601c4030144c0c90fa0b0f0304541c4031b00440004580c0104580380700e41014011400101b03000c032410815440c0c4034a025040b0703280180146d00c40c0311075040303039002c2010303610680d009141c21154440e103411840c64030002c01902a210030b0b120f489422400c55400c = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 933111025 1250 933109775 933109781
    0xb04080715050a18030602032502011a0126090d140c070b070302160e1509090c09070c0b0c030604061205150a0b040203090105010e060a030f0f0303020f0d05040c09 72
    0xd50541da403410302d004a200f4046400c0b0303500055070341406040c043c3c000081801c0d40095401003c07150a190f20034441c00c0c1020303000c524045100307001d5904144000c441d003000d505280003003890a0030030140058540d90724540c0f81d0b80c12403001f10f42d00f40500074084c0f0b1310380010321403104107000e0300c940d444d4112850001115000b4841c003600c0c83d5010a4042c0000105207000c6e040c014880e00440381030b4081000404080480307078000020202c4d00504000341880c03200245008000c05407141a940d0401c40c3c45161200b000b0b043c458051400003011030030140c4502c5001e02075075040807940711541016003030101b2550084d07038242e01c558140358012030301c01c00100d240480150300178024411214441f40c030031b218030001450407403040d07542c58500f80f160f02e45000a500c103410700b9000185560501a82001120300a86194001d0085400030310004055841c400c103099001411040544050325044000c1d01c101c58003103580f050049840c51001751503400003802988208050b90019445155020031 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 933112275 1250 933111025 933111059
    0xc14040617120a0e060d0c080c0a0c020625030323280f0c020703060c03021207080c0d0e0c030d02011a0609040902030f03030411090103030f050d090c0b040807 70
    0x6507088000c001c02e1a1480c0c1006061101c1c903400c024011016000006060340c00070407880444a40f210002c401595003c221207602880d10780e10079081003011500281600b012400003401981c00107400c4040500e01000c0320f0352019164144c460f48a81d602e002000341400b40b08240c4800314280700d10b10080300c1e03d042144545180b6510054205880704105801d034030b2001040f0485544480020b1a0b2140f80a051145580c079001015024039625090080725425043c0404152050004402c101500d00080380c201006180c0400652100121301c4142d105962041d580305140100000141c1e501041090552800700c0651301c25001042d0b00740c1c2aa4280108200c9090004154182c2c514010016250300b840c00b610000b01c00e02a40d01180c90304254411744403080d0701c00f0003000304000e260b55081400007420303100d100d215459940e015090f110001031030402e020021030550385400c5194405c44100f5000300c10b1142440d0f40e00c401c2d00c456400340c01115582c1c02000e00200344408042603501c0 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 933113525 1250 933112275 933112319
    0x105071205060102061e180f011d0724050906070f02040b2e0c060c030b03060a060f030303051306060b0405040f0e1507090f06091401030b01080406020c0a0c140406 72
    0x600c440b000000c6c20740008002c20036030415282a48410900004021056103002250300000303403030036055260400d54400d82d075090110360001d58248250050b210900d58980c103048806c0950000c184005da505000700c007422900440045075100910280c0d0040110540c0240c400b008a80e039070b8400d02a00a20f4403c0c03100207260300c0104040d0f003c03d182e01040070860035280440300c824807561040c040d90000c100d80d400090b110800070320249401e20500b03403c40e0400800f04a042d180c00c042018015a9201c00760502d6669000a0900c03040d1940d207080c41544075200b00419912403820305c415421a0290a001b54a40102c0480b502c0d024840c1c580d00c1541d020040030001403920000c0c00d4a40001c044108001504d40c001a0302e000121801d8050412610744010490420204c030035140a01e5203a07d04250404a13648001d0343c100c0002ea07081904040c015030303150061030744c1614096003081d00422039980b020000910703a004003010500c800c02200e080c441155150a14601c00d241214020b03 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 933114775 1250 933113525 933113551
    0x1e1e07020105101a0702060309031305060a12180f030305040b06042a02031b07152a030216090605090112050601060c02031009031806090f050f03030c010507120506010206 75
    0x800809080001411040b0704109503c0c0785c132040740c0c00700d40135410a680c050f4282d440850340a80140c0d41c020260090300d402e0328460b09298801800410744905150030713960895540000c00c84000081440710401900b00e003224100c0d03801490014001c1000711003c0e25003040003808982d0b2071030540a900c0c003511110440104564060f0401c181850341c1c2d40300e580a61004021a90701c1d42280e0558805004070350028020062a161007803251041a800a0341001f00c0040400030400f2100000604144403d84954825685140592030310014205074507955a0300034001550141a821078800e84200740d607011010703640c07900c000d88059030031000100640c00c0070005121035842440490b00c03490004040725200403000d0015821168411403d0303001444020030703c0303109404c0d800010000d02051403d44041880c2404140b94031019010b441d12441c044005104995030400983d044084d40340c008004508000c44050144980110702d00c1b24941031000042c03e070360010402c0c80c82419540441 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 933116025 1250 933114775 933114779
    0x8030d0b0315041a070e100f0c053007080a1803240c0207050a050609120d0201150803042105010e01090b1e0103050a06051e1e0702010510 61
    0x18101611408090030340511900c8011042c0d0300c0e2140b01c860041d40103880306000c02200440f20102044000c00d07410505c590104682c81e26107401e0640b8000120710b10744840900510042115801124070024000303124903500304d50001107030313608a000590461011085004d00c2104528180219600902198001e0109545890244020b2510f183c2500400c101098603540d801c01350f203d8040b605076000749285611040d080d40c6100340151410f51b40002d00d159464200007802019007402118000c4001107009503030f645405010140e002c00c142d05444c100e00311041c0003070080c140f0305c01d80700c1c0075002d0703800000e403580f004000c40d4190b500b41040b0709204800000c081c01c0101b0144000c1b81c403903507120354200c050802881900790b202d01c6551000c0301402c20764501204800d0f0440f9044440071882e00400c0081c2000640c11030507541300c00301051594a2442d003110062190084410410407401080524074072109800700480340c000704181252078110080b82240c10440700484002111181 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 933117275 1250 933116025 933116047
    0x62304030b061504030303020a090b090307060f030e151e1b072d060e010213120206190206090d05032a0d0207141b060a030216081b06100803 62
    0x120715849100a80740d464151941d8540c1032041c2c0c01170b0710581c00250302041340c01d001c5500c0360818004141c10380c3c000741016001400203444107000d10602060142c4011017000c00c03802908208018900344040d03800030050f060507d52920401c03101041e11042c250360b00782d008182018854000c03c50401604622007284148134a40c0d403003510265031240d00d030300305015003c07141440d19001c00c0100040c1c0c2c0350100e040c5030402c140c4003614a5200181d0043c031030812000201c20326070f412100801c41d00005a20305001241c0b0600c644050a01514a8140d11060305600060418080c005000c22200c4c006058030b4116880e0006440400b003c0c8003490030039074541c4504507c18002044140542e00d8007034a401c0140c01c0f80c0c00000c0c01c641c0c426100b0490718604078144401003151080ca0a40300c61014540000b03440b506c19210103105142d40428620110004040c0175403081e503201c1c0043d40da5042c4884100a009240707080010b1510a03c2d001902d241c00e640b00600458070100011801c2c0150300700 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 933118525 1250 933117275 933117293
    0x3050c0d0c02070522060504110a0302160204020307021c0c0b061314091e01020301080706050d0e0706050702090a0b010f052107110d020a020616020d0609030906230403 74
    0x641401144900d901c040344e00d035a02d8176131401c9903491420701c403004000c41c144082910075a5101912591170044a15041c4140c4011a6070f44034403485c0042e91a00c040341c403184030002403c80a0341040c404000c00c0071203a000114500c00100c4540d07036003c0355000c281c040f01c0c030080958000701500703840e201081031803e080317101c40401c000203140820b81d541c640b17580100241c001c07621100c95510481215805804003031344a04400400e60080d459513044c040c042d0394808107449140c00308040000c0c4416489a0b5034445a10384075014151130b206586c1d4400101550050074059118814540111322204490311030904042c40684500b02c1140c444081562560040501140b03c1d8002d000d00040c62022081d10034424660b5482d466050000c40049503d0003504030907980942d4008541280541c0e40c00098070b241144120b440c05940190f440400c5900b01e90810080c881410b1903514420160001d440780c0030354446942e40c5061040c003132407900086040001041c0d40401c200414070100f50910 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 933119775 1250 933118525 933118541
    0x2712020307171f39080f06060a020709110403230606010509040b04050f0a0e030f03061e040507030504050c0f0d02040b041814070909030e12011113030b0703050c0d 72
    0x50710001d0004454902c07400503d0704114150b1070300c0c08119000d13103c05040040200300440c0d9203030445d80c0d494038640d04844ca85020380098841c40700444c610720130341d00c20000000607102040080c07144000e0381d183d00040d07070000d00040f201d91507860400036040b005885c041322444900c0b4024141c0d0b45440005640fa41d105841494220340c0b22640480c4544640c000c1c64001e1003d503902c002c182ca4580c161b4400c491880c41c462480c0e8200300042101c104131401640c2d0400c90440344407171a000c072480740001038243e602c1c401d1b400070b00700f204100740150558070080c03280d806941551655483c00040110b42c1e0110903280c0c0e4004545500000541801c2e840503040301006000020141c03060f010a20001d0380568044a407070314248000480c3d90018421071008104200c2c0130302c49005190790162180c0000340340640505a40908a2000360003508103810442d06152100c1d91451012115041c50515000503076807662014042040d40380b0030711546105a0000090034140450140110040c242c2a = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 933121025 1250 933119775 933119833
    0xc0f0d030818011802100c02150a051e0703030b0108060a14030f1e0708060f07030c0905040606090e091501120302070801050f0a0e0705030d271202030717 68
    0x1111045000700920600078540900302013081d002c0c11a2042200303c410740c2d2200b030100080103c1c44001a01c58589500e5800b0750800e8550f141c54141004481d1806003042d8032400c40d140342030003141c030781508004000ea640265420b000020000700150780d40001903c4458200e80b040c80704001e1041c00041c02c0907249001410340b00212180400146855144d00c103810240030884103007210b0f4032081004a00800d4108040d04880c6031900f400c6406481c0180080207050301c480341c1802a51140c0d86810141c600140100200c644800004200c20250f001703901c00c001142c00422500f1a000512640b46040c03111030500d1682070000104a40c2c828101c2207040d81308a6001081c0c3c42002e004407807103001b624400f500e103441c28804000c1510316104a10755250010030081c800d0303480c013240c0c92500d05054101038102c1540c84c44481c04007458094070101f03079400c0c50008500c050096484c40382c20390084045664490b2240c9081200600c16900c01100e0b90256a80c03100401444000f03401e00700748 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 933122275 1250 933121025 933121051
    0xf0103050421090512062203080601050703021e0c0411040b0906070f060c030f050a0504050a0b1b070b1509100504050606040b031006030e16090b030a08070c05030c0f0d0308 76
    0x500c4010605200b80c0c40317220806504000e080110340b01450710104500d118000c1104251410342d280a0812000a0003440c1003002c0090103106040c020400e540b440c6c80c0c0d01c0c40d000e4140680300203090311038030740200d060722803410074a255290000090031b803811f071248281c290f89003820902c00c010141d0300c10744084810303008040340400800c4140c4151021044542c90108000c450b140e95101210001131420754400e2801003400003142d00001c0701c8000ca07070711a140c1902c5440e01c03016441903040001420360000400140358007040380c0b24400d20b00500240303140e411075038007960410030a00700c22240c10458141d1000c0801c541c1c68190807050b086400545060301c1c09803104508140c0c3c2d0710450310320042944070602040081d078103104400b080d14a00c00a04000240c80c0b40f2803c0420091051100791a201d004004c40e503038061101c44080c030740c0300c4501a0b480c0310901c2c00b20401190361142c80d100307024510050910341041c00d4003419640300188090b498806176039003610f00d0304010380841d02a0340 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 933123525 1250 933122275 933122279
    0x9020102061519090911060a050d050a02132706030321060b07110306060f01090306020d0b030604030906110d0c140c120109060f0b15031f0303030b0f010305042109 72
    0x1100c1c484050032015030040350303103401e42c10514041c5501c5c40146000742d00801021223000e81c403e00f581c1c1c20311040307100450741d89c9400340103501a005203098180040c180010000c1d19407001009034a1070700001940d04841c5114041c200704072507040c4000b4000c40c4641d1008a504c0082c1458880b032050090700004690742c4a801480707c540090004072564402038900f00c4451500300b140c1e5030700810882d41d20300960b100c030000038044841444020a9aa00031601401d04009500100c0395018058112441454203060080280d04a071095a01088640040080c024800703e0004145006a1107850031000a50740d046140b03005800170b00540c1c0a4089180384540e6001c0b801d0b51050700d028008100d2074040e0610000b01c0c2c8007240d141c0d510a10344204a40c8540300d803009a480d1070040c04043d5141c0d513420b488a01a660000b14816009074140008020540c255100c4850800c040d00c52102c01141d42d00150304955042d103000c0c01406008550340300704041d51401c0c600103016031600780b483c15 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 933124775 1250 933123525 933123559
    0x50709060c140d08070201140705040b070302010e0d03051906031e11030d030e011a030a1403071506090b06120402040c050c100b150a0e0d1109040321090201020615 72
    0x4612a043c1c600184121040c4082c040e4240a02496040402083d07641c509206402030150f21841c8038040f4108004504541031500079801030110079400d80c01ea5852040c0003800400402c02190780c02e4449280107108400603110f0300c0340e5020360351b0104d81120101842c2d481140d982e0b80f842e40c110b075131240d030700c00d5100740d61010310040c4444141500e010880c8074000d180700e401c0d101e00c84000e041c589101c17803400c0c240703540000342d03000003030f0f0000c85000702011103203081400c40c030030a0405846d00001174a481d0300090f90368400c0b01101c0c01c2c070030704102c072010000c1040801c2c42440d00420b1030301c0300030000c01c01500c2c282d48440ca10b50000c0c10003600d0305001c00d40c2c80d801c01d4404015440400d43d10501c2140c00c0c200101105558607003046a50700c0c040b050031000d0240303000e60740c150b40207102c1480b03404100404510380d558296001040f02001c1d203400d140081000402c1c500001030f02401e00340c0c011501c80c6600940b9203203a4160003914540c5d4840708603886101004200c1540074000e1a0800580 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 933126025 1250 933124775 933124783
    0x6070204020c0a0302011b080f04110a080f122a0c041406090610080403050a0c0804080318060c030a110a0827011d0112060302120304050112050709060c14 68
    0x2d081500507046030000c0d0309002c1d007101c0301c245101c0c1c0c001c41380010a601c1585e001c440742d40c1c0222a000c1043c89a2038a0500521503221502d80642100a0040202e800c0d1030000d05207100700c500d00c0480e4980c800c3e0600d0541c107801b586d0200da0100c50060f03030411413104145001400040d200d41203d041808920009003903c014a194107148040c400c00c1c444036003004071425920031400d4034448602040400003d102c0c1d807005201500f000404210500c13034a10aa82410641d6004040152155101c4c03061584951021903641c6000c0c0c102c42d965400d5040000940310440c80000186007041034200099804a4552540d15498000c4480c04000640e900024000c4070b446030804e141091405007100081207108541c281c1403107d529812445500061802040da100c20701c1c1c00507889001c400100b010b880b035078100a600c11486040d0010b50903000000e4400c4900980c0c0d0000100c1400500d0021118251740c4071300020700c100c0e414440035008030402101644140420707004500c5a504032418 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 933127275 1250 933126025 933126037
    0x2f070f120512090120030a090f200a05030d051312110a080604080d0b0d021806130e07061b0c140111010e1c030e010615030606020604200607020402 65
    0x49031020411003040001105a1039003d0243e80082000810340540c0007419800304201e180c14120000004600743c407503420049130700b41c1c081040e010580d4031340340095006041c0b50180000081310800304a00e8981288080d00700c0f04050060885000301d0070b42100c9070703403142e150b0403004c5100c00701c0003810099840100440502a055000616000d0380420503d0042613104941c50744c130070420f00c80030071a00800c85200020a039000202c902241e80481c0e036013030b40b09001940c41176601c1d0440c90481b40e4078101130710486045445107620406d00724004102d50a010358140c440d40140401e01c009800350341c1410789403400241102c0310f44026900d5030640303210340d0080b005040c400c400010665170480100044814000c0080c8034224000c1a0703207943d180000c07003002920488240c4030024500075808000c02c030400300e0091240a0300c0f09034450418440080c86000607140c0100018030703600c04074210b8001c40d808903400501c06121038101068003454102c25910600c20002400107039194130040c40 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 933128525 1250 933127275 933127277
    0x2090607050d030c080f16090b03041202070b0c032203080f070213091110050f0c0a05070506030403120203070e0402070f060f06050a05040e071205070305012f070f12 73
    0x20042c0000c44000d060320030315036014050003141d42c18130010368407140303072940e102c0303d40d22100c0404045484d045502501d01c3e803000881e0a40041884103102e9421038222005456401712480d269490001180320b1241d00282c81c40ea40040c0025504e80070140d403580041d0110394442c0d190543c41ea15003941715400310b54201070a4000245003000c50401d900007640401143d203040001403010f0b11003c400c2428070f01000c2c0304003a030708014032046000e00c0c1561020322103003280300d8468080e4410180e4918074888144e44610442000041c10319000007103c0c40350394140c0c0c501e290741c2c1225140c1c0380a904003401d41400e002d91000719140c20b031640d20203403148071301404003400c03000c0d02800c000013210407074130f91a102641001400d0000e81ca450b04103100b255810384000454070f042d10281410020240c0011540c200144003440c02c0c8000014a102501d000300020841405160880d41103001c50407002031492a007003540d6455251150041c0103105c3c00340d891058201c500b81d03170390002c104014242c54 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 933129775 1250 933128525 933128533
    0x120f0218070518030601050604030b100e01080d030f0504030e10110d09060e030a030f050f0c1c0f02030301050f0f130e01020a09060e0a05090c12040506041406040c17010209060705 79
    0x102d14903440f20aa40403100c16005080d05504000119000784075500003e02007100e0240440c04400020300e4220007001440c0300040a561590300c407540328a880c00d203410010b07042090344041e4407154804e05000b9680368403505620285241480003844164070008180181c8941d05a1850b50a100c1e41400c0c811795501c5828403401c10202501c04403008070400d009910410300c0d20006504041c5221800840e401d000740c880c09110a0b4000f10310803040c8000490003400900400100c40304162447c0c40c149495903166145060412a40e90000b403240c1e40c2e2000d014a210030b01810b00c03014900100c00060300d04412070b200e10407010251440c4208400107a036001941c000c0d442c0d030120300c050103403035149002081c041c1c8070070000355404d00d60f010b1103104000241c007159640d011281120091042440030701d81c24505818203984522084070150744251000344141000c00c00802d4030362040ea480a55190b220713041101d4208120941c030740f9015036640c2048010155901c000161400a02c680c0042c = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 933131025 1250 933129775 933129787
    0x70501060527011e080a08040602060f1302011b020402070c030c15020309040e151e180a03030510091109031509031b0132090304120f02180705 63
    0x4000001c49070074144103901046201c07002c0b91000e0461040c1195015000c1446000100049102002d03460b800280c451080b05480c01c01c104845026100300c0d0303126000c3e12000e5541d80010310b05218102c621f28200c06c0580220001503006015174005c03501c083c1002c60080500b0307404182240c0c029482902d081080c03d00400400c41c1c07000c1c400c0081d15440404018400170031401a42e41d01490245034400c5403a48034a1218031070801c01e005c10103401420f030303500364142510207441e0b06203042d00c10103a1540040004046a5410070000e50040c0d40038024591030042d070b1003c400400010b088048444d114109c0001c1d5403181d4001c0c0f800b00140d0404156850b02c2240c101460060b0300c1001d19407a0070840c0804c2154400401503c0d0340d40c5038240d40b09001c01d0444026401080010440244502e1403280d240012411075403e818035400700b25450714030b850301205190340740928440d20034184001d11100c2d000910525400204602c0030300305e550124070b14150710740b24800448110b40001c4e400720700 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 933132275 1250 933131025 933131029
    0x130f02040302151b0c0d0f08190906020601050604060503010303120b0910210f02090c0409020a050306030f0c0f0f03010b040504050606100c020a1a0c0a1b0e060604050909120705010605 81
    0x40e020010041307000401040b44001c002c11011288031501400344c10543c81c000f400d000701d032021110121290700d51075405401e00000134102018600858005119401c000725080c106281168140da017143c4909045a29642e0304948204070740300c00c3d50010b81c031142d41c0359098403552416401802a8032007440700720304120b22074002d4114803802100301952038a0100200c0e68912540c0301003034040d02c01160307503602e001c00307a1054031466104065040c03002850310300150703029000c0c60007a902101540c8807000624031640e0b541d52004003c59020124946090303d80ca032151000110a902800108072802c03002c0024044600c201c0c1c2c151100e401010401049107011441c41c200c070030140c00d0032200c200d061780204802400e00d010f512851200111107503c100c10b610192000c02c044201100d1500b00c89140c446000c20301789440d650390183c0102c0200d80d204403040541d106040241050382461301e840d042114420010300181600d01541b220000541403800040c858035000c1c070004540700e071034041 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 933133525 1250 933132275 933132307
    0x5060d052b05040b030105010c0201210504031403090709020a09120602030402013203040c051f0f0f050706090606030b04081e03190b0a080708060108010c020606130f0204030215 78
    0x40d0400c02c041003005000d040120400e690640340e003031038124800c01080c40180d0310b0400c00c25481e01710903295103603240796071001d4214510942c400d6560300c42c0c2c41500903d0711001c2c0402e81c0c0d5891550800b200910030b0051641c0941040e0590b440c00c50752480d60360301c503410003030300301074040e60903540010800c0150758101e030015030b050f401c00740b00b860340f1040a080341c0c0001110040700e42c919180040490103000c481041d6201400f0024140341d040e10400c010b8009500c02d2094110210b0160354100c1c404500484002442000d03030f44a040c034000884d51454000e0403000c03402c441a554550011012039407940c4080e219074840c411665a802c5000f020004031458400c501c0c0c0c02e03460030410407000c8041c02c50050b41d0483c80c02e0303000c241100000000740b1050b2043e00710100070f218000c800100b02d240041e8a604968411000300a90b090004080761106402c4a015030082c5040c030b10000111342540c8034510142c4281c0f00181426129030015504011400c11400944c0010654070300c1f41c60256 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 933134775 1250 933133525 933133603
    0xa0b13090c1a0405010816200a02090906130849051003030804020a05040f0c08010815040b101517092107080702031005041a040503040905060d05 64
    0x20341501d09091a040c002403220b08021f050488103038500010141c070900034956501d440d0000d040280c1c502203c5140303e50b0364094464160b02c04c81c0300a010480412010031400e02459504403044101419900d42d0b400a501c90495403180d04a0201103c0000c0c00d40c100c90682296000940d408040d100c0702804100081c14844111503440c140521090103400c01d2000100c03507050420b880d081c1e0742c44c0001040415907500283d0405e0a024002c1c0c12468164803d207420b00060316400110b9880d10101a41e0b03803003220840c40104100000b00d404140160812a44600209011443c0a48400c0000c464159124803400443c88510742c41d00440c10302c082d440c0e4001918001009090800480010301d220010315aa4549400054001c107024520003199219038000c0c04172049140c1d900400002400c08444c103a9460100781074890f00f1040e90300c4914025074000006608003030a00d0290300040c80c02070310705c40c0e2013007450400c070001030424050016030b903060144440c0d5180c40d403003068003402e40c10 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 933136025 1250 933134775 933134819
    0x1150c0503032a03101401020c040507031d01020f030106081f060c06060e2a090306011206061502030a030c030605031509010513020a03080a03021b0c10050703080a0b13090c 76
    0x900401c01d10b265402c4c02c0c402102d203403540036400b03c0031000050303040510b4184215086400c000400142637015006003400c030002c0400610340480c0c1e200454200d008034256200d01384401c10040000511804403240c00481c82075048004002e246801c20400d8000d900100101d0300342c0d9404030610085102d850010201003a40050515010002c44110070700364455800080260307030b996102e0101c1d0010380f012000098100c840d20f5840e04110341000449132000c403190303030501c82c0211320a1504c000310103192019400960502100b01e00580c045d2007013140030b4040540d0b80a000401d0340d0104600a04015204200c1069050048181d402e41d500282080004100f00030700d000181c9860341000210b9400c45c00c8103484c2d00c0c0604045020788140040d94244e1a000020751565410104550110302c0c0c0c22a610103402842c680165464010144042d012503050400100c20030b207660050300c0e0388000101605a40a840000c020480c0d240007400d80320300458480900c1504032070490540300001d2 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 933137275 1250 933136025 933136027
    0x14090c040e071112090907081f0905090715020303010b031504020313020108240409230d121509020307020a06150e0c030103052104090204030b190e030301150c0503032a 74
    0x1c4d010219141b5080986035004001c10180021000d82000d5030842246100c05065503000d507035403000700041c0030195007020b075074051800c00203250713aa200a002600390240d000b07982144c3ca005501000d0740c1004100c02d80344114100b03c1501ca60391403004511030007c0840c0200e07094020700005203d8800146900c003000e507107030701da800d07070075a0000d800103c2501240c02180600103460101c02c3c5110318a070006002c802140030310f100d18408500408201c4031540c9141210901d03002c101c0903507207942c078560519050690140102c030340c980c000316800281c50040b545000b403030350703240e200b21740c00305207606005500c4000502840c43c00179052a008402c801c030660843d41035840e210345038141c4080021103500303801c00c400107540c9004240c40081c101c0c1002152290342d02e0520000440d03084400c080c0340d08100c0c1d40003810501c00d00c210001c004080d0b000350706680c00c101c511481071010401da18184100001ca030750000e44d00300003d41c0714102c0780e01e20013140c42c40305001c8982c0b011420a100c2d0392100c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 933138525 1250 933137275 933137287
    0x61406030c1005090a0803030403111f0b042301080d1412043e04051030060b0405012c060112052e14090c040e071112 52
    0xd00080d90700ca000804850309800032864250660741841900000781c0c001d180d54900040d25040400518410344c0281c8440d800c5648003000c050f2128420307802a0042c104821100e440c5110961002100c40c501400000d4008140010170700c070022101400002c40240c0d200502085006021001e0800c0480c18190503480d858180c211190045800110800302140006000d00c40b2244200b80781400a001401d40e0300745000c80038080901f0342220503c110907610b0032090504040c400c41d407042e41414040c1c1805402c1c98440c03801d448070910343c0c100c1d03031144c15003c0345402c80701e444d2400264420300c00003880d410044180002c1d0f840591003c0060342e502840c406c02200807402a030700c500902140c0410b01c1d9580703001a5030041c5c90040400d034141c07800c82008500b40884440d500c5000c402c0100304184510714026040040150041e003242500c20812180035040c5584031a82055103009400d041a45a8031180c10070603040b56203000184015500f100d20078418000d02041c0c040c90054586050 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 933139775 1250 933138525 933138529
    0xf010c02060304020402090d080408030a020d11150907081002090f0307030c0b07020a0e07030212010f0609030b0912070c0f12080306010e03010b0603070306080c09090c0d030509041107061406 84
    0x1000081001e4011900080d447c0c0079580e981d40e80324541d40e4810f00d00c0d52165203400e41719035280c20880352440035210310300711090355500521443c9580f000c05001000d040c050490286600d0001400c4401320340f25032000421009424403500209040d40000140c4074000034007017182ca258101d0640340241c01c01c08041c03001ca2007209208083d038440200440d9101c5003480410b8000001c0e50100161041c14420300c0101c0d03600d5002003000503226002c0b5001d80c0d885100d00e483c0342c50b66200d02c2000c605040030030400070f0341e80ca0408d580030f44c202003510510058541c0d80d003c6540003443c100c42e4012803440510407905000c200d800034100f2048054840e100a9a8120746440050f01d114140880e000d0300a25564094204460f10b000c003500403516070400039406000380c00d580c0100c0f480c0303005541c0e5a01d4207003890500e082c49020100002c00c09941c854003880360240085c40140d003040700402199582e038646014260300c42c142c440d02107581325030a041510803a198118107507098041481072081907 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 933141025 1250 933139775 933139777
    0x12041e081c021011160515241008221403030f0709030c030b090a020d150605012105060a0807060f090b130605030c0c120a080f01030b0c130918020f010c0206 69
    0x2074076403100504051341603401c1083c904080ca80003008031f4600002040324420080300100c011014200080486c4c8212608004100c00810032034000184080005070000b40c0d540c0005901456540d00d4030300c00c5400b0340354400309101403184001c1c59400001801788940c2040351841c1e000c0310342c6c6001c41c8814110b07900c0104444c0e4a11003d0407040c2c0c0507000c01d07020f15041c45840303035140e4010001401c00c00245040300c0303103469024850503020329140d00007078154002e000c145103120705c940f441012140808082001007c0c0680120341005001c040407a07640d02c10010394020300420780b6800c00b44603482c0d8004041c120385400403100d00c0310030721121210300e01d8252000e0a417401e03400c1c019141d80e0f4501d04420350740190081680284200711903904c4d01c2504200070b01c0302c2615559000d0b0240c0d00c5144640c00c461080c4002044000008005004002400c01802c400c040d0740420b900072554445044080c0c50500c081248803001d400383c0c07402146040700d0038100c2358800303081c50048100150001069 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 933142275 1250 933141025 933141037
    0xb091608120d060e0a06030b090a0b0c0c030f07050a1b03080304110415180609150306052206050618160809010204090204030506150312041e081c021011 67
    0x800d880400e03000403090b0a90011000307400c003084480518544494000003401c990312042e40c50414880210b2010800403500d43e20356030300032040788030b65100d2821801c45540481d40ca031070140814844c40d04034604210003000342501800051402c9041810018600707650440c200403407280d012010800102c0c01416039610540044034114203141c05000300b80580381d06100c00b600f15001843c040b6050315000384c034850700502c9031010444242c0395040314084684039083c410128050f0304003000040ca058220303652010b400b8000c10241c4141c026448044250302034211803403503c87c020880c2c075051030454000c0d4150681001c0106061603492400802c01030f4050a013041701c007100003562980250111001804120011580c42e40e480c08c10b0b036141c5109a41d004100540340e1400d01243c0f500140c8904021034000282d4a490314101020640a80160721001e03020395107000060001024028102400126800b18003880712955000b03041241000c2c184014074075201d08240e000d0150401e445d0 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 933143525 1250 933142275 933142303
    0x18030f0c030309020901121401020a0e06071b0e07080f04120e061603080f010f03080f071e0c080f06101401111903030c0509010e0108220b091608 64
    0x8000c00d01d003022000b030a890100a908a401e1400000c0d04084c1481c2041d041170181450310302c0c0442c0006d0450030707031041c4a080f0002404141c1c8a02242c40c2032802402814410401491900601e03500009881c0080d80051041c1600c18200048103810607a807036841480084d4000951906544424084003090040303c00c1169442041c07600c0d45450080b80c0180001958071410501c0a142c0100b0040c0b04940d01c400e108108800003d03c0801407aa0700140c0ba800f010b030905029950540d004c09410054003034685511302d024100d0b15071102940c08041c523019400c4484420b06102040f4075100070640140581e900080070081204403224550096a841d0110302d02200507200c0103c0d45580310340480000c9024000c4010141c0541d25024045180309440602c03224041d074001359103a0050f400d4242c042480c40c1114030b580e602c500c1c0360715840300e801c41900340080c40300122000040d030f0030721041302e80c41c8400d01031022401d4100040310701c001c01c01000b001c0d020300f00391510b601c034603003c0f944007 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 933144775 1250 933143525 933143537
    0xf0a090203130807051e160326220b161e081b0601060504031e020a0b040801150b0a0c0809131107060c031a130906180618030f 56
    0x501e419a41440000c9420703004120b8985504d400d007801a00c40381101ca04a2402440c0c05240b04690004140605459411440e0300103442c51910343d04040300e030440d0401c58170700c2220032240003040c0c5100500300000200b00100e090405058004c0d001081d2a005200c501c6d2052007802244080f4105d120380c425400075003419905203502551948500c10b0400420b092400b00b00d41d41d002c80c00380445103941c988102100c105990310b40d0151040c0c8a01c0c04040c0800c02030040b013100308265030741600c14032880a40318000943c0d4403d0b4200c00358006410140442e5140c8180440054162080300c0160401031807103450b040c2c00b030501500c080140400108520b82c04140060280d03120505208000040300b07041c00304080b881c85403122648801c5c1d00300c44252501da0001400341c400e01c01e01b026003080c1c810208a0f08044010400414030102000740501e4969252400180c1c89008102d03a007000342240d034581c5031061500d00280c0d400540c1c2c40c00c4032944c191410303000c203074004402070380e19050742410 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 933146025 1250 933144775 933144781
    0xa0606110a0f020d0812152d01090f0602030414030714010f0e0a060309020111212802281505090c0d0b06040c0806100503091005100302040b0f0a090203 67
    0x102d49054014a4050b000c140085940e90305c150386c64812612401051850034036585444080000e8004d1a1007003807a24240d0b080c514140c24000a036112803442d0504000b20015603c0c13501803000e2005402040042c0c1000c6010001074040441c03c00c0014022000f0780700e402e003404400c0c0e0841c0304180541d81044038401d00381d5440d0303004180c800d41c000800352035503408940301e010180c041c1054110480c006200d40036600754407040414512004000030f0343c0c4001c14442c05184845a41207a0341a42115652480070074600c2c0b10212a0100c4100b1900a0700f0b4004a042c524080d9605034205050403844200d0341800060800c41d01e0341150f55218070000c1c081d12140c441c2442c004e80c089580303800c5280c40c80144140308991003414491041110103011841d100b0700c2c221072a40f0141c42d82600616030910b61810b183c0202c0c00b96600c222504102e40051080c003014900707842c41070320208040310140b20140203500b0a400f504100b0b07803040c3c500b844400b000e100842c0c0c059010788680000c00c1c0d408004 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 933147275 1250 933146025 933146029
    0x1c050c040305011a152820011401050102120306130906051e13022101091e06050c0306060318190305090415080a03030b0102120309060a0606110a0f02 66
    0x9440c05580c0002c020802c9601602c036140003850b070386400921171413500d01e0340b015001000085481c3c200085014178204d2100b61a41d640e0b44030030300002410b0106440c01d1285030190784030380d20807980e0008000b14551490640d10170502106822103030440d0810403000358890342d42002c07240c100000390703040d5004181c5440120018414120010496070400051200c0b98140040342404050008540d0440f0307107440410b160401e180f50310086d04000107001c841390085101c1007002c036000f00c48001241c18103041d034410f21809102c03820340840441c51041306041c0100c0d803103450f44c0619400480c41c61424000d00040d603500004082d01102c03025014441109c00050120701e4140303110a148007070442c014079000d0600e412918607580158941404068410340d6504054105c0706210050180702c0d045031001c5000d0700407078856034191b12589000e10301d0200035030011445500100081c00c59400c01052843c19104183c0c00141007184200101d10000e001149040c81d480c0e00c400c01062005041c80 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 933148525 1250 933147275 933147277
    0x903061f0302101d04021603030b0607050d0f1205041a0601120e0c03120702090705070501020408060f0f07080606030610030f020309240103260c1213050102031c050c 73
    0x20f40040f881e03019040059004180d8507030701e5880b030100040000302a41440b049010348400203041c0d440f8460617101181c000c4d03021030f14104d0302a02c00c6c1c0c5450400d0b00c0702e0303140c4801d450003180059010580140c0423039000c901c403101d04007915002d101500b0300c0d4840d003107156410f0080780810100742e40070a000307a020b150301074181e014044003400f000c40085845d540795802440058001d00890003204004c98002d8100d865040d8000c05400389a1103031541110305402c0810110303025942000003145004d42004402c2c4100c0d40d554248a0340e103490079508200050243c0702d0824003203400d0070302610f60380da0001d0f00c1e40020140c81644011082e00c1089000d00010300748403050900c0001400b0340114042681e15030011207210844140c2c09000140709414000d02c4060071a901c002058405044004200000c40340110001070800c05814116801c00010001652801d10001604802044280d02c11801014240003450030401440e40340b801519841c0009030000c0d43c1c4200040728440381744 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 933149775 1250 933148525 933148529
    0xb04140a060534020901080c030708011e0506060c0604230102161212060b0307090b270105121005040f020412120201110703030e07090204060f080613090b0f07050903061f 75
    0x10042c5c41c15503502c80080780c84941d10012a8064014000b0100d98124140200310b6100e4007c10301b4500074024141b4000207000260510364008810010341c2c00c0c0301c400300266030040740280c008202031030210102055850007800c100140703900600c031030085c07203040e10001183d094004440546a400c007000c00c9070102114020301206a00e00040070490042c91009144552115125080c61342c0c0c8980e4402924003d03c01040c4004294510f030285600340c0c1d1455600d079803010b040860501300720101d82100c281b811208200c940002403c2041245001d00942a50038503250085203098148142840004401d003c068158202e42e203000000c203200b5800a5400b088a00e0307425240d0f162441c000f00501038086d0540c620344074889003c280a182c0344200d0301101e000340c640000380c1d40605800e03500300721b004041c07a50124114002440041542c0505ca188521800f000a89440d00064a58401c00d000c0c12500401c581070100310460b80340024006d410082c44002d59003840e01a0b000c102c1030f41025 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 933151025 1250 933149775 933149779
    0xb0f072a02041d01020c0f1c180323010b040209010c03140c0f030a030501090510090e070e0709090f02041202090a020f1c2d150b04140a06053402 64
    0x81d00f00c441c05a0010342c064200e07900550151484045010b0205680b03480b0061100500c103100c507804580c240c00f58210400340402c100c81d05651903a0381e155441030300710700c00d8032042d1107040344c0240c0c0000308207200c0d1948080d13045a0443c00c008840300002c00b4a600c400c0010700340503100918031400780c20103041e80c942c0d580394001c44183c0c0c21490007075074580e00302818070f034082803c0c100045007812a43c0a0302d8402c11035003c10703241d070610704090840a840703615182265406121400b0854030003600040d44220304644490140310316094800c0c044409000301c401c41c1ca8414041480711030070042c940810b0035012510120580c42d90303650b220091244824000e400007001aa8145060420552104c0e51840200401091022242d00c09030707140790084c81c089a98810707002c0c43e15098581c0c000c3d0454508405030100b040e403200e4040070554426004030f5030100c08803490400a26080c120100a001c052410501300011441040d5007201e106024003103076280207086600c20100003a01589036030700 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 933152275 1250 933151025 933151061
    0x71e03020a060f11060106050717070b0103030503010602100b0312090a0e10032d0305030718080604121404060813020918070812120405190b0f072a0204 67
    0x3503880302924500c0d00448202c0402c2c403a8040c1440d110021645d64120b62a6490b01c51a0800668684030b10804200c01400c407041d050000c0c0000c10807544441313018500c0394031256541d50520b040a49071628200c070302c1201038203044080c210317038402007880c030008504511410b0320340140303000041c504203864008400c0386080c0c00410841c54800d1000b4800caa028290380c0c201ea44451424603450641b600f0f07003180c800d914612810000c1e124000441c1e00807420315211482c0b4903880340800000505910154190b4402000e0209000c100c0100424880d00e500384059140c0c4682c40402d0b05000311b1083d0410b0041100018515059001040c0d4615030b0080548005142c2000400312001241c803104450340310318800819204000203144640c500c048171090308010004102800310b100040c030458082c00303200904460f0080e44482c2d090b50912501c0990100d291101ca60003030356000a01c12020410304000fa603c1152541105205030340441041e4040d076059400890054044511511090a0 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 933153525 1250 933152275 933152279
    0x160b0604060816090f1b08091f050a06051816030609020403060c140a05180301061d0f0c1606020d1506050c06010e06060909190f0b01020c0d05071e03020a 68
    0x9a43d48441035501602e400c0040d02282c016440498041c0c000e0b842e82d040d00c000c0b0154250740100b0b80795910900010481d046603c0c160880c010151000030010111030700d90303042c0080c0403124019a00606001d0700c9860140411601c14600010701030600614400b4501034002880e2103500400d0241c003041c40103650b525035070300c0c04200620700c2d80041750000d1403910010110108140440b40542125602d03103003401c0070001102115a03030f00300040d46c07544d41d9003000288000031091204800c60300103102d906600e4014030b18003e00400610591085004002000b0140812141c58160507004500140c8030107000b041c00c03000703000b101400c42141503030740c0f000628942d001009121101c80c0c8810b41d0143e0341e8609003000180d805480c1d07281c1c420400e019140c010300348045855404000c121919030b480e000c400c0110203c82c1c816040080d0b85858804a04007960100710101e034542055880001c61340454890b03a8980900d0300460701140300c4101d03a103c1d0b880000c5840300146800501300302c400c507 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 933154775 1250 933153525 933153553
    0xb0307120516061106090705010815130603030e130509030a05210f180303010503030a051e210f13030e0604030b0c0a030b18040f02120a0b0a05060303160b06040608 72
    0x10544220710541c860040014006d80b004510a001c4610607100c0701005d071613051006036112206164540c00854082e014483c0075050701034440214042e48a824103100200140500301c00c41840d4000240c0c2080d061104040c0000708035074465220707140c050748401002c03031101c90381d940003420720120b503990905000000718203892945c058440d01081c0310300c5a6251030750316102d000900c122503241c0c02c05d01c06205c555005500815071404d094828090001c14a000d10304580c00070b03c4460b465a903441c010711401c100400c1788c20742040e0095200300841c42d000350110925240b800c4010100301806580c2403464580409840295a0062000c0c100e442c001c7d1401c00e0a4015940b0040000c1c2051101446410002c4440d0825070704925540095501c54645481040b0581d404a800c04202058500da59100703220184000b40b103404145500d0500200b040103541c00070300100d20940081000804808001c1403240c04aa48000030380c0165450718002401441c40c5c2e40412024000c400c01c3d15121 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 933156025 1250 933154775 933154787
    0x13090c030e0f0a03020a080a0e0a0b09090c030606030406090c1d090613030914061e09190503101e05130512070308010504092f0a08010b030712051606 66
    0x10104402c98004031895401103a454078008005809130b08501507030300c0482c042d1401130269100c181004c40c02002c04902244504116a100c1000048081002d007840e10701040041d40081400d002c090031410581c000a00900c00540002d000341d079500c4160040007100407054001344502280f5040342c00f001545000c00e01c00840d44c9441d0390042000040911300c9001a072130038281c0568a503580142000f401403041686800ca850707000c00b05000c1139650f00001400340e50840d00c44008913440742c01e40800c1c0706040700d1070302504a42503028801071040f52000544443c0e95000c2603004100c1490824055240c56003c4102040c09400c110800030b26085090350800386500c24411500380000d00e000600940c090103100400040303c80004211500d0903401076503600b40104111440300d4420400c54817120035911300070385802c0303049440009c145880c030907080c000e2034900d0007400f132904076800190702c40d001809400c1c80314503016416001e208080064444100c00c414035450704a868407070103404 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 933157275 1250 933156025 933156041
    0x510030f0905460f0614010b0a020d020f10090f02130501030309060516031413060e0102010606051c02070305040902180f012f0111160309210813090c03 67
    0x30101d041c500070310101001c40c040c00400b903c80c02c9190b940411070758a8203d0307a1240c2030f050740c55907112a0340344008040091968001d001403121140d9501007442c01034103000113031542005640140da4000c04500000c40e1000344403051460004082106203010080403600090294100054914102c40c031052903000306d043e43d000b80c90b418140e039940d510403a85480b8211008951843c00303c5800006070041082c00422404000c0701030919010a103103142103052540300b200000c05402164505580a22130034010b00110700d0000d103804d0803600f1071040ca138240000380c0507a42c1e00250713210905100700191409049884015950b910402c100b041c840500c1c11065489840000181d000f40c2d8041c40d110b030300e00c0713080800102105c440794121040c450203980100946540b14a6804200c0380003400070300030450100c0c82c51303207540c281e07041c0101070b00305540100d11a003501510b500561529007401100a80e4841d146517600c0113040c03400d51070415254460140e0034285441e440d145501a08500c107 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 933158525 1250 933157275 933157333
    0x80702030d0e03281b0c08060f0703061202031507090f0905070207140f0d03051603090305070e010b03190618051b09010906390308100510030f0905 65
    0x96446000401d000425284100e9401059445c018900360201000019403094042d088030811355950300041070801e1412598a000c039440701041000c403d4041c490400904600040381400000350307030209941d01001801c072840302884100003040b180c130403203010001d030a43c81a0a02516035600d06800070301016541c02001d405085400304070f1004600d4043c002920090042155080d80340a00030f084603075801c142c0400204200140440102e0559501c0030303071080d03866130303800f071b10f1800c016081200b560401440506100c004100f034501d0b81080d03039041650a00c829180010340c0e41c0c0b99000b403009610140c0f0328100c0c00d03c402c0c07aa0b01c0c0d81d40220b1007800d03803d1050150707041001c0085054030606040724040307030511400b07100c800c0c45642c181d0b0b103940c086100500c420740c0b8508201848210241403141c6101245035050802d0343c8801c14a4210f42c60101400003241000d0000d265104100c200b20b01705a030b039040341f00d03000589800080780260800c1c20742c0d01000c062a0659450244404111 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 933159775 1250 933158525 933158557
    0xb060c06010806061f0302070c05060f09031504230a0506040803071b0804140d020a08010b0114040312050a0c0b0702160e010e040602030c0706020a020a020907030903090501080702030d0e03 83
    0x9509007403400f00d0000b4200110844005c0340c2c160300342500290003103a4280c0d07240c81c03e240007186648035200100100f0810001030f40d200d80c5a00100f40c540508003229400b258030ba842404001000c02d00c0f080c140d07100640800ea00302d01d01e080000c0c036004060740064428401c8900380414410320800441c01004943d9402401001e4101d144110307101700340c801400141d0410040000410380300c1d080c0d0311100000c0c00700600022540000360b00e4241ca0704030603000d95450210707100640c0c000010010500c182c03000381d8100361640d02d0341d54485a908402006003c40010000049485101950307a010360040329100b590812840003503071903002a034400103c1e2010100440c1029205450034100c58559050307150315a103c2da54a006900301500380700341250305219180c0040d4039800034101c42c5d10594020050000d0b940100416440003a28a4060615009125000c40e07030140812081d10406c3c24a91030b182c5400300d080380345110303002814000070315000f8012440385020008004150240171a4 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 933161025 1250 933159775 933159781
    0x100603110906030a03030b13020c030901022104151413030507290a03020405030304150306050d1208060f040c1106010801021303110f090708180615130b060c06010806 73
    0x1000801c001034030305a605502118002001078400d80120204a0015000a582040044d803120981c0c118241e007258075000410142e1455904102e626003101c041c4030200075010010b0300044c0300e84201d002c0d0803051481489a09012802048081c001000e50044039a440d62040715800303548003a80800c8519000791200042c40b0300b40050014440c03048040d0300e2108400303822401070170764400300703a10046c5078080c8800a15658144043d0009041c0203aa100101142e00401800c071050364105512520128182602107031950842d42c10384452410980180d07100d6030300090a101031001c0240c1d002c4d003440410803200d81d0005500c003029403544222401c50340c030380d0001401c1c0e0140440403284114000030420115040207000c2040c03103406402494030520550101d281075900711110008203101c10140005050302c03003894046080c0060160240341412280102c003611826003551250414040900e0100030a60101c5c000440c000c00240d6680304007101152903890920401e0518002d0b4800 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 933162275 1250 933161025 933161029
    0x1030506030304141f080702010f09080f03060f0a09020705010f02030103051c0311030a060305100b2409120d120605010206040623040c090b0a0308070807020303070510060311 77
    0x901405020000c02035420503080071110000900301d0280745900000704190440244400030401c2c0c0401c1c0c59940300751041c9819034011b801d6904107542841d02c1450800c0640c007280940040e286030400d41c02460380e498442078001082070340501c5055903c0b840701c580c0040c03546202c0e401005000d10070030080c40543e18010903001280024800600690889070b41c80c4000c1505a2099a921070a0301300040d41c100c802c880101c071034000701c5100c01710561b62070080c820310508211200300c07551201c40c140240109000442d0150807c40a00f540c01c04013a1a036040f15680c02e02a01c00854015088803140351000c0310455503000500300703e001081c80d580c81a01003000c01e00800090b110103030001c1c4440c0c0c039503a0361031004100715014491810b402c60400490304040041107800703140143c0e452404641404210800c984203040c030701c2d1060203c9001040010320b01c00a40310fa40350851549601d4401500200341903102d4104002c1007400f4801c04030300b18045a5004000b9a030084011541060846007 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 933163525 1250 933162275 933162281
    0x220c0f0c05060103060902190909030909150b090d0203150406110a0f0e0604050d050c010f0509010806062b0e070b0c1b0102191a06040902180a15081b0103 68
    0x801610755006a00180046030040d00180042c2d0f2018210320000346014510300700c0218203401c000c075106d44610301070040c0b66020b517145002e01325145c801c1041c1145003544005c000d00318810741d0107005c008942d229495440350f040c0c4920036005001d0710465207251301c0002070900c0450301100d0b69842c10321a045130f044101c05440859405407650442e00034140007d69071000c01400726540200e08100100340c2c1e4481034031481c100c51094008001e22009400054040b1a0403040034003048018010b0800780d80c2c2c06541c1d15000303803041d01d00d00d0b84c5a504481403041c08000510320320398001d56029422120aa0b58410000560310605036424151542410035241c403500c00d21641c20740c44190b00300f0126403040c0113010228814011240f10181040390907042c02031f101401e0b40c17101803180003014400e500c8080c40b640030300c1c110b0341000b09603495800181e00c03150f1405881c1d4a4003504001030900300095010228080c400e40c9804089903071030301c1040e61030000031421a001c00c072540c60b403601540240 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 933164775 1250 933163525 933163547
    0x60b040c0c120e0a1a0a020d022404170c0d0207050f0a060302090a0e0a140a140c070512041203020c03012d060504020a03050919021806220c0f 63
    0x2030001004003440b038800702c1c2c0d01211000c1c22544820700803000900703100c162400c000c0301d1500c03c000e15110701c2d580c0d030040c0c2001d0042d10084d040d90025050300000e0001c1c500502100405520a000c2030b442d1810701101c009143c1c120710801c20700c0020003000341803001820480344000c4e45d086072044c80e100d20902080304c80c00301503e9040301c1054820300c440b5000e900a81801000904052207550f501c40752607008540c01d0318001160303603454a83e5001c02c9901080c0d690b220903148824170000c0350080000b006003100400b00c1c2e08180012642c40c1c10004107200200401f141c3e42030f403a4071070761544e000035400395007001c04502510400d00d1a004605040c041c0d00c00c08500003070500400d02210307480120382c4000380d5020804079074503540811a6900c0e480a40745c01e040c1550000380f645010440180707020004070551904060040b60307500140e03544103400d022000c00c104482e0845e1141c101041c181036000040000d4604201600c80e071441003980b02002e42485a0f441b000c1d0003074030035030682e5102c400e4 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 933166025 1250 933164775 933164783
    0x60e0a060906020c10030f050a2004080703110607050105010303022d0a030e04060504020d09050d0215150d0f06290f0603090c09090d03060501080903031609080a060b040c0c 76
    0x4a54601d030b1480c082d02d606011a03501d01b00420794211031050b1400712403048030310850340390340c4142201d1204800c843c58903c0002e02450340b4500342c10a40c00c181c1c0c1e2441d0b88070060225000500400c5280c84070310546401b150b00400078411940c4900e0080d40380d584401190b40119682e14486071300c07000c0114921003560071100604030344030082d14115410307013401c00d4054006441c0c1320b000079591110710050055000301e42d03002600110038903009e420070580b5002401194000050310a8030309410703612a4104d941043e91256011840010600358031210802811454014140b0410300c44203801100c8200480c1100005a00300581d04101c8410454103041d08480004181021ba0500100468006d03a8141c11030340010342d6400066941348080714046620f0304090080c03002142c1500503000909030900345402c030383c030700340341403aa5a0000810780040f00d62001c5030040c10034014200d101c0604070030780540d06d0301401400d001000d04011941c0c00c1c00f5501d03001103031903203c1c41899840e40c02544 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 933167275 1250 933166025 933166033
    0x9100c02180c13080318060a08070c061b02010e060f070c02090c040503010c021507090608043f0e0d020312181903151e0e0a0b01060e0a06090602 64
    0x1009081500d034000611501c0c034110108800420a42c1c010f8259000300010700045959081440c1080e4070403290316102801680c05100b5031501341c1c0c0000300706610001c10b01d4180e0078070040d4242080a031454801a40b400003480805519480c0d042d00301a8440500204072079550715006424080e5480232145034000079001c002502c014900306400c10741080041601506054a84001030f003101c0d050143c11015a02c01000c012202410a4000364054000d08080900c0d44c54000050310801006000502c101038099440000d07040c4041c1c5c000340d00612a40074600c11080011201009030109260800304400030000100b41c0303828202c40c9417465015000c0c00005001000840f1140c21001004421103140c105841d5076403101c100744a01150010659409686035040c000c042c90603200030001c1c01410886403c0f0500c050262100082c68569000510940c0404245003807240000d00104854804800003640d282e22001e5010200011507050802a5a480d015980c52400303104080c09a00 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 933168525 1250 933167275 933167299
    0x1030f26091e033c1c051e0417070315180b0406090c05060c0714190909051203130609080c030c15090c18100b0f09100c02 54
    0xb002c0c04180701941d610300100a40200100000703090035070a002c503070140c800c1d10b440d043c0d0700c07040645201c01c090113400f090818000341011850f101c258002100001190300108506413510030400c47c0c1903007e4841c03080402850340c90040507258020b00c103480b1011000c0c08014801300010500d5401c983e071050861040350340c444000c001900c060100703054505840c18148000c1034264030007600ca2403007200c0001769004ca42c600038642c40c0303e030340000e4001d403024040e5002007400041e0100580e04141c040b404001c142400141c104441c0051071714816400358000180c0340d082c0e400034965540304030309403034400003d08485003c40c0070894010f111303043c20400340004514580e00928046000306081c504d4800307030f00c0398503103540c1c003a003c5510543e008141301070640072040002904140d141020b041c01031b085900044c1c59004000d4810346000c9540c0106240c03911450040d001008001407160702d82c0444100d02e4040d41241088501850301446820461841219441d1500d0341c02400c902c0549 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 933169775 1250 933168525 933168529
    0x605100915080a0b0603011509021210060c02091005060a02210f03010e040501020904050f0a0608061e060a090908070c0509130609020d0204022b0c020c0d0606030b01030f2609 77
    0x540180141b900b555035640071684d040703070700b07081400a04907001016a0721030440d15441030030140180200d501070503040050260b00c0e4005104450300d5011582c520b4140c680c020300c0c3c0d84e24103055110756806600002c001c001030360080b5414003508031003000c4110348440400040ca00c0d01c1143e03040c020b030040c1000140807188000c1c42c015045030058000609040390080403400329070082d158001c4444e030b0362081002034800c03401203001401c4800c01034003190030104440024030007407440881250b41c00c6400103440751102c001420040002d450180007485080c100b14503180e01c01e01058035019071050010a5504048400714010815000942010045516024004c0c501e00100701d0b030054100745c0380000359442e0300143c41203880e58448011024030508031420548500f070382c1c117a0810704040c859071000d60003058030070340800140c840c5905001985083d000412454000400c003400354000413061142d020480c1400611a11000542c40407148040d81a224010480d8981c01410001c2d10070b94 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 933171025 1250 933169775 933169793
    0x6061d060d0c0b0a08011701060302011409180c0703110a0c090905011e050118180f03140a090f0605121519080a0201020610060806010810030605100915080a 69
    0x80c0941e07002c03220940c49400d40c1d00d42d5404202d0010005a98200501440c455842488039409246000300305503440c560002e0b1003a4250940f6440d244804940b654241d03d0f0340d80201c0026002e6401c1410526110b1b0380900c8640000710f00360300089006d800b1401005d40028031509150f00446a001d6091600030040301a20300c13a135048030f45540b982034180c0113480c21040000040b00c0004045080d41c1445000030052200c0780356540310500740700b140c0364908900a031101d549a080780c459200351740c46090540b42140c081c0c0791160940000515286007550002c0b2036429100d0001504031120b81e2000c00b00c85031300812800e81d03d02d0b10b449022440c01101a0b2030303d81400405000405041402d180b44101641d095004078000c2c0c001e0a008c50456078140840b540c0421386d0f41c21500801d0034800014800600103004170b05000056000c90007442c002e44d90381c002540d025070244132500c0e09400041000c00075100d4003508604022252105c2500c00b034119040e504a44001e01500c100394513004c1039 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 933172275 1250 933171025 933171049
    0x130c091d06100b0a17180c01050703050f13030b15011d1e040b0307061106010909120f0512150a230d060b09090703030915050a0f02010615020a06061d06 67
    0x92181741c1030072080182a81e40b1540c49610482030307801d88000350341880344c14041e00248080c1000310400020b000240c1010942c0d00c040903614a07181c1b40c03c08910280c041541c071790400f610f0640c4c86007c002c0b9001c403060039000290000e9030f0303072103440d00d445102c0c10300d0303e14500d41070b07510a140c8010a0441c1c0390101d6034031501403004001181c22840c040100f410184103410013800100401200b600908040001134014600152700300501e0183c1d8503800c848040c120000320401c50a0752190506034841c1040e41e9001d6102902e000c5e85040c602d4a00d5583d16180e03000b00d0188007107204c00608104529811141c190b810000c0b400342d107202008100c0704000035002252246d81d103400319401d5454032203005200d0700140000301981d604500300900560110b5120111011700f102000b01c841da44042901c82112850900540b1014404010303805004184c02c0203620350810782d840b54425900090851049000b06000c014007a1186d150526000510b8401d0071900c00d608040384042c1480e01d0f200708 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 933173525 1250 933172275 933172277
    0xf1209180f0b060a02070806130507060807050d0f050708060d0201121d070b040f0b1c020702011e02030d0f06031e1518030e010e09010b03130c091d06100b0a 69
    0x10b5445042000100960000c00c42c1c140140e122190900c14540200801900607000d203010306501410341c0d03100c0c2d50f04c038500d010f08002c1040c3d1a004c102202d00440540f080c1301200001400004400c400f441c00810040358100d00185404000c96401d080010194503c6070b01a0346008044030071140c1c40b406042c50031a602d14100c4107038080400d55034180400c0c2c01030310840c8400d0b95a2490a403209050550396000907100c50800c0114003030301c0801c00303c442c000381c0280c2000b50701d46002d1700041c2c2e0080034044190901142500c01203035403940c00300003407001c2c00d0062000c0041d0184400c0c800100c030310364000100441078071080094010101c0e65804500340c46890328404c00031b4015500c90944011001c8030301810316540d0700b0020113811510308100e541d820b10b020100c4134200030000304000c60610520f200b404001004c1060442404681e0300700c9504446140c0326a41d81d0b4081d40000c0c03412803440b8030241c0c90b0311402d01d251680070480034014100c0b50b004036405030030b00c1c40c00074036684450307032840c = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 933174775 1250 933173525 933173531
    0x801090203101a121f0b0307080a0b040908070c090612080405211005040201080c0c0c010e121203180a0201170901020d1103060306071416140106030f1209180f 70
    0x30314410740f400c0c01c2c00e04c41c181e405207420007442001751a6030301400e2a0010740092209004119540368051256030344031414140100e9011503150100340201a80309020f801c088000981d80113200f020301101c1c0882d4005001000340c60740d6816500010408680d008200ba20100720802070b6140101710070b08040d01010118004d81e00c9a01500d142c130240054114205844100300019076800c045140d0780400440d4119141150b5092040c3d00c400c00041d965060082100a940380d58881410f000c1c21b059124007241e024480680400310150401c58445da0352084030002000100004504040c042c2c0c0c0c1a110009002d8029010134030f0424000e00094080d9400c0c80100c100c15558002c041e1403c3c0c0119455561b030806209060034020010100d80c1070240c42910418130118050403150000b12000c899505000a40341c01070444400d00c16041c0ca944c2064408410301002e100c408003443e100e5198038620100d0316506550305400362046405914503130342102c5446101d44c0080070b0901c10a9400 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 933176025 1250 933174775 933174787
    0x1202060f070c0303030f0507050a030c020c1e040f0c1b14070b190c0b0118090b0f090f01060b0a0e030f0f030a02100902130c1701150801090203101a 65
    0x110419041800c059440e482c9a100070020305405110302852440e8040046c0528500001c001e03145100390121041055038032103d00c90110310a01030a40340301e00040c1041c81003165074103c0b417040000c605085d4822850141c89525455842c0314580201e1508d445103103007991300c2d196429441800300070660f46249542d01e880c442c1001030041401a210303e1600645500c80303402940c0102d0003403a6120148a500e0203041f003c68110380c2c5460444c0c801c00b101c482d090710900f00800242c81301d124010403200c558014000c483e0b8051034402d00c02e034540400c440c501581e0041e0f03c3d0a0782e056102d00e194a581c1000086842031068010740817a02c0c026040b40d0b1403403101d0400d2464000395002c00d8042c0e810208825603101d5062102820300002e2182c00d00440885400003181b0307146440280e04081c3d524603090104c82d000c0c844400481c03940110ba00030a60b5a5401d001d241240c06030581e0000c3c826500100314a0124400e503405140c46044400c8054281200041c00000e1907540d84d40c00a824040c0d = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 933177275 1250 933176025 933176047
    0x9010216061d0108090703082a0c190b19091d1009060602060f04140f0705040c0906020a2a17010f0209092e030f12020303060a120206 59
    0x5400041c1000d540d00302c0c1500c0390340021004944491100c5040050800600003100c00015100d000d8a03000f400c1e09a46062034200e41d03a0018410400c3e030210407120114040c0858049060b400440c0c090724030340c40f0011916114841854280150010404180070342c1100090301c4800c2921001c450500b6103041e030b1902c40902905425042070203802002d00d08210b4a9180350800c0d10040c0104035040c001c0c80d0070244080d448441c0240149960003603000000c1c240b240b29036801c3c500340300b45016215108144801552100e01600520340110700340740038184040d1161404104480c5250b010f4403d81c040c079604c0c2c0000c1c0700a81640540c41a510030744685501e03088020030010481021940c203448250181c96094a04201180300460710510000200391950400c0c0c991240c0240181854400e444100900080741d140c180704403030507a20004020859020000340b800e5005050b000c500c0c600549003280d03240310031106c864201d0340701e81040180701d07690130340c1002407803000706681c2c100550b4000e = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 933178525 1250 933177275 933177313
    0xa08031b0f030118060503030f0f030a150e04060c0203070f08161b1d07020a17040e0f07021e120a17100315020a05040b0c010905010f0b01031d060705090102 69
    0x8134100500501c01030070302c040c40034803801c0014807050f80914101070304400000014014000c20014001c0000005140694640d00c0035050b000e4500c19285082d071601c0c242855501c08990450b905890309803a031039041e00001c00c1e02c0085502501c400b403864101e5540c1d2a542c0c0040083e564800902050880024400401901e000c0900c074568807030315190204008142c04020401c0b206254184140301360030350301243c545041900040b010034400000c007440380c180c4c4215481052086860802e2140d41b041c0710103118003411117642203a510340409135486940329500001804542c0c40300076490044084e001c00340c00076034118180041105001003c0b040244400c070f400880540c4401d03400d004114842100324041110700c0300850411601220241580c441c0740a080328203040440c2c00c1103010025080a0701c030f6940000280807000c51120610b0103002c108007120301013402c15000d10700f403248000340912845d00020003480d050329207210960b1103074440c2480e541123005030701425610070a844 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 933179775 1250 933178525 933178529
    0x4140108010510120506010e040c090603030c020109080321090705030f07080d110c130b27090a0209041b0e0906040506060409033e1005010501020a08031b0f0301 71
    0x210b0b00d89002090040500c0300c0d0b40200f103240e2601050380d0f000c2500018818107503900d070b002204d0f1a46460a00a07216401c039884070500d242400001310402d581300750764404083c805c0c1c0315040a0313516143e01ca6120700074541d0000c01c200d0294100380c41142c1c20f02c909500140140d042d211825210320210f401c002441240d003409034411071080000740c000b081044d104040a10b4004c104103080e180d21a00c82c0b1004900b644140400645e0610598565110031100c03503004104000e40d41c201c8841c454401035400301c0200013140c0b140020019400420702e50001c0350b0050651406a480390b4030800c0d85102e1900942c03000801201c04030395460303030958550244004000500e003d1030300e4500343c0e1801c1001041c0b01d00450514640c107000035000350160800f20a02c2841160000d10420045c82c0c03410301e8441c41e1031100104481ca40c0c5288041100043c000c034499084c41260780b14801640c0c0c43c0341d0b03404000c00d584030402c0091104e20019401038513045218120074902968411075000941080e = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 933181025 1250 933179775 933179789
    0x1090308041208070f05070218090c03010b0f0f060705010914030c0c01021207020909010f020d0e0c0409030806090406020f0d1a0108010e01060f02071203020102130e04020a050f041401 81
    0xa000340002d0000c03400c181d09007540c0d40e140680903894180382c01080d81c3c803140075040500ca004100700c2e04564850340c414442c1d05560140301c0d182d140420381681c1d81c142c10034850b8040d5191045c801c010b400e0135034038002017800c0941161400c0c0400d04c103215281e8032071303c4e0549049d5a20780030000080c03003108541c480d044d941801503807511700a43ca02d07030502c0310480c1100e0541d0704c50400003070070500303400695140300d8044400c1200795558510307107405815080d40c0e0ba014180300040102002c00960300c1601c107a0307000003c45020101400910048400c401009404102003000095503803400c03000c020b9216105481c0941000040684050b05030001524800413a0300c0d494540a8500300da09a1903451009180001043d4940181c1d10103200040c02210204148180080981e6000304100341c0101004c26804040c10343d6400c0080c002e40103091291040d008000c0300060a41100c68054015074005000d003030000d16080401c0100c0300481403d80e0455241c0180110a883c21000f03071780200340c0 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 933182275 1250 933181025 933181037
    0xf070308040c081605090601111e2e090804030f0309150305041a0601170f0a05060307270f1508010e031c18051c0212181011010903 58
    0x8036282c810610200303a040106150f0100c20705116070503d200da200101c420542d0751103e16100e91340100e8403180c0172031240c640f5110714030380314640300c001030000010f501c0c116058170301040c06150341901c1007000b03482d0780300b100e0781c04680500740c1a030a92104a2261060000d14989a40c076a22203181c800748001c02d602091120000b080400071450308003030981c1d41894100401c0c034003030381c5038400420007000d506a40c852030f40000316564000c04425685803208601258185800011034003c080125030f01028039081c0400718656060000348041903800501c4034141d902160b0070404100800c6e074451484007a1100c0c11810710840e079100e07058402c0f11244028603480c0c20214200c5c00d5420012458440354020424103440704032800311a00750a050b0100810b0f1000640e158030680b1007401c0c0b024003e4014440d561a944e11f219034161001d8545409607400d07141071084001940c05400d40d041d10390110310429840500d001003255065400c503052480c03c44524412032400c4501108080340890a = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 933183525 1250 933182275 933182281
    0x21030801141f2106050108040f05070b0d02090a0504060509011a16050c030d0807091e090e06070f0c0b041112010612030e040209030d0c050c0910030b1803041701020f070308 76
    0x411001004081c0d84683d02c1030141d2444d00e4002080000002c0014080405111443c820840140201401050300d500e4141d00d410714583c07290025801080b01500c42c803038900000030070f424a030003000d084403070040c100750140c0e00c0d040031904220389038102000d00035000c1004010404210b100030003000d009030700900d075000c50542030514105074002440c040c001101c041001440e23214100d801514042000703560f00b40324182450444048542104080364240324821a0742000040d009105000d61b507600b02004511001c1990201c0140c00064080310104001401040c101e0000206c0340303201405802800380714040036421150320360042403d40d007048980d803040c560300c14011852038004441c21071426090000082d80d0703a030000050014000112507400900070144800100502c000e0072104031840c110304400b403a5103842c041111030170b0303640004c80c04c014010800f00d03440f40c00d100000c5107487e04265040000114000d001540d40d034007046a41445050038001d024103d05c65103407880541 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 933184775 1250 933183525 933183557
    0x6201912030e190312050f010909140a0f0209071b0209340f020327220207140d0c0b19090804050a080d0207091a0909060121030801141f 60
    0xe16172005103402d54200390a0210640128811030f0455510140000b0070240d03510308212a9188140742801c5070156016100074491944c0390341c0d00301031085403085c11030782d00d1080030389000385802100c801000f03202c4086001400c1201c10590070040401c0d0302d60345410b1420511050504051076645060b20038064426065000000b944501d0110300140d41041c180d00000342d40c59400f4100d0501d21102801d0b00d840c5516504016681c680c00580c016999102c0c0d00b0424001c0d600a01c0c08850742050400304d001c02c20000b003002c0c4d403801c0556441c2140c00c84983c882504101003d0401d8040c1d10102001c091745200c10700c0b40088680c480d40d0410f032618a42802c1001132080c940c8010314030382003081d80c07040103640030900009641d206200022041010303100f51403d03140c424801c03508000d01c0428040e409000013100f904a410240c4011030f05418001700c3c802400350088000e020421000060040d160800341c0ca0f42e2251010746510001750102d1200c80342141a11b910b04007269804100090b06 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 933186025 1250 933184775 933184787
    0x1808030409150902211302090f040c05060d0e07090908090d0204180309030c05010f02100510030f211407030819060e10080703030f08040302070f06201912030e1903 72
    0x5801001c1c2c04d89060950003158108c207004007051001c03006280060b040200c45c0d40d01001804c80074200580300c200c0032a640c401424400c1c041c910500c81d41c0400a51401c45014a04102c0c1d0f001c034205051030340700720902106a00f000c200700d90058070707070318260a1884040105216103000e551601401443d5080603065401290002ea041121040e042080e4a03000540d141031a0710032903000615640d99140d000d1100c4150308002d202c004203442c218240321039441c004a05020200c1c6000700c02040d01e405136207000c0120806981d6560030310030800441e01400d80540d0194003240303402d00e000001c088036000c0b100c490300f00c06c2c4001c000400b4001042030590b026005400c401e4018006141540c80c068480f0510040000800040400090406100b444040000d040d00300d100e0742041d45a0802070214421010b01104060822000c4414490002090f4243c0e0100c1107250042e00e21948411a1164020081c0010305854000c14101a00100442c2e0681048221240c14441e02c80c81d0003000 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 933187275 1250 933186025 933186031
    0x130509010512190606050d061e05010312050c1005010b0a090e0f2d01030501060602010e01020715180f03050a030e03070b06060c0708190201180803040915090221 71
    0x1944118240c6018440d000484850b101030b4080406410503152900c403029145641016400c211081511008c110301034000d8400500004403026207215645c0901088500910010300130740324101181e41d40038000c000904015880100b610368070380074070100c1001c3e15401e03800580f1001c0300055001e101644501d140010386118001c002c0300b800e00794a0314086010252a020709401e5100f400704007030b101d07900100d50314082d059000c21a580c2d04d00b010743c001e20041c4100c4000d94201290703004242018400c50313120a5210143c1022903c11107030510003060304d4401e4030000142000c0300d20100700c080d85c0320740c08a40300f6907403243d80310ba04920003404d945468085a200d1b9100f402035030f000500c41f07255a80e020f082507400945403485000c003540742184c19882707a49280942541440506184101e59203045e0003a03c1d102c0e980c003021010010041c03924401e04a560f0402d200622031010720350818210011400c2003417002a841301d0051040303900084600901001140b070086440c1c9200004c40d034 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 933188525 1250 933187275 933187279
    0xf0204050609010f03020405061f0f140a170714040e090d0306230102160e0121120e030705090f0601031b05042106060608010e101a0c010905031305090105 68
    0x5501d0490498240d41359804028407454581c4009140e5071a01504401ca403800740140c01e4040c3c410100191902c00301c40b01c0344001412107803d080314000900d0485042d0340c4660784504095024103001e400d107250142c0182c0400904a0b02c2010001c900310142c00a0001d6404030f5810f802c041003520703e41038104070558103050400e0810000b14403032754504400210f41d101c0040000380764400403818000f2840b40034034603941c0008081006200b10983c28141d80b0400d9903400550302c02d0000b00d122000c803102c01040512400c032005903640c4116048440300201908958070305803500b00140b40c00b00121007038030b9101c414500b042095030341402040314000380d0000d8080013a455000050851086000701c02c4580c0310396103580256034000e4071092080b80c00ac641007013416145e0000600040e003c3c1314000c260308004012560302d030070818254080f920103030840414942c0301550030074250850b840c5a480da55890400b1004104180002e03c0d0075513000310b00500e010f081c00c0c2000316421042e04114 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 933189775 1250 933188525 933188539
    0x22413050a120807051f0e070806090706110a0f03030509010c0c0203060c0a0c061104082b080403031d012903100b03100f1a0906010c06020f0f070f02040506 69
    0xc4103002e0030303044100040e0409103944d0740f0320f03007810001d1422030b2040d01280b0300300f40f00303201412011103a80b000000c12403042c10b0301c2e01147c5c0c1c3c5070180d50302c140c25a000402078100b50310811581d8000c007035045015a408058442c0d00c54162a042201000350f803040d80400c0e00c8008125107070702c00384035030000d82c803883c1401e001203100764000c02e5075540024070b4a000341600080400740075010760048500c0d80e034007007818480e0782840b00755034080e03800078031072411076100781082c500d07103960096a581d040e00401e128512406522003400c46124001600c284c0a0640d40e141d40040100c40039100041c242e020f4001280b4074200302d48031002d642e03030708480c0a80b2090000e08401e032a500407035406002391200c1400b180924050700000e0030a040300d840c1900391803805001d028040754603000b0241c1d80c0c1100346c030000000313000030900c403036480101e43c818005002d80d1850400281c1690107081c41c00281c500c40303030820550410705030150788000340c1520480d800310341110031403400e40070b42580300405071025 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 933191025 1250 933189775 933189779
    0x2090105030d080106030c0201020705160311241602030303070906080901060b040e180d020c090f250519111b0303042102090f0907060e0102100207022413050a 70
    0x20b0aa41040c0101d508140d00c1d071011f9000070f4800d4040c5d81c102ea4101d03080e40c802c0ca03c8180403010f00300c0c80307210865912100440010251502d205040889100500c041032517070769140c041c0f180c0e03a1285044008001e80c01d10083c01507201000038502c552810313155030720303024240320019015032002811349401740c2c10402e0910891502609a03021070382c110a684106803a180300d50406050f40c07400848a620590010b003510340d034001800041c024041d07480400544480c9413034141900100c90b408410b180030100585603d28445220244c03c0e414540313a414510b50492034101d002d94001088d000450820300008000401e0244190120050890002440152010986074060343c42100e082c5c0f90320384d00c100c40001d0002113444006500900d150002d19101187d0b5039405000d43c1c2100143c811288041784250007020034204101c4141c00800c0c10b516154003030b50282d440f0314000c98105035250740d17000324520701d600c2d00005c00742d2a195103030b01c64007060803205042c1031036441907205010f0183c1c1 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 933192275 1250 933191025 933191027
    0x305071710260106081614030c0612071d09040803060f03010509100e0a030819110406030e010e010c2a021008090f0a08030403320a0f0207030b0117150a02030402090105030d 76
    0x41b49003180d02c444841d041400f2000002414603031480301e0301b41c00c06d200040620149105026452007a0b40f16190408000401c060344122480040b00030398010290784081400b04028a0145511620040001c07880c60800f00100e42513600503104c5036115804960002600303180350050010fa600c415000780000340c40d60324020036034000070380300500c0840c804070204010050740e081507000c3d154035401150f4a82d40d9000c014014804110400550b5181c091400c40c585030600880c1c40100040d540c24020060140404918184079280070b150001c80c0b9001400580740c041c4024501c60458035550418540080c41500300250010080c42c0e98101b0206640003c00380800d0f2a04946c261a055983d201039202205885803110a035a414807101244103040d6240d0200804910480e9550343c00c62030800d8106a035038148a0000814550f203c13401409034180030054003103510b902030700b100e60041d0070130721041c0390290030344003068a103030004100007d501344440c0315070060100780c0040a45c2000480 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 933193525 1250 933192275 933192313
    0x13020d03110d1e030b03030c060f070f0f0807030230011e03050613110d0f060f02040503060a0209030c0d0615060906021f110406020709050106030507171026010608 72
    0x101c0042410707170f12001c000d0a62020816110b840840c88220390050900c4182058480012120f020000e0314030744401c40c006214103440e0031300b00229200d1910356100c1c82c106a0180d0000f040600031200b80700c510307440e00441401c55010418058004050315414081d2000402c6980803601c01d541040a00800000d140090a150300507140d521140004415280c000100c10301d000980354001c210f010180140100604007503c240d202e81e908110016540b03150702c050b4013441c449c055054102c04001004881d0700d80040656102c001d00b0307203016030305050000b83c1c1850145801c0c1c0d039030359130307407400d5800704ca9038240c0000a04810f0400150705454410020350f1400c0443c10040310b0758940e54402c08424054220748058980b40c5030300f130f40b6035440e2000255512014850525600d080400014215001c1d100b03060251501e0764400b101002900101162100003034030242d08104c520200055640034085800494500034562658004110781d01500f50b030030315080003441d038000300e4150b0910300c241c80d = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 933194775 1250 933193525 933193577
    0x907020d02060a111201060e0906100207050f19061805040b060403021c1401020c1e120703090803041d060103050c030a1a0d0f1b0312050313020d03110d 67
    0x50004c5400103801101c44814001c0c42e003026541080ca6001151176600f11000e81d80005064480c1101596503d040290080742c003200040940c1007600144010300388048520314410000c0c00501d0000800c804e072020092075030f441750000034806082040e4555841007064000d0400300ca00b071040c00c85980005031144038030f00c0002c4c818403c2090040280c03150603030811034190000240c0700300007100b00c0410301039800014003081e83c0c050040040d00c403080f515402d4950300c0c0400020b1036445504100741c140f0354801a815418001d41e000001350400c4100020805814900c40354a5250700010060641590142c01c0710f06050400c01000044046402640da00045618001c00c00c1c0844074800508001e086103110342015000e40c000041c40101800c00340710622514408280c07008013003600c054400180030040400445241e030851241c4a20003079074010103a9400060211002d5000915100396000210049210070780b0140041c4014418030184581a003400104400907000c10301c070502e460 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 933196025 1250 933194775 933194791
    0x90e0f010e060a0b030a120503011805090d0f201e030a0f050a0c0b0406021e031510111c180305030f03100e0406021c021c0504020f1504050907020d0206 67
    0x2481310142156000c10452103201e0b0080d2110307540c010500001000d9903c01d00503008004006d2000780b444040c684551446040d244014068144003039000303c440303e0b1940d001c10b04001ca002c1400c000d42e0810501002082120700040031400c000540032038a03001c60078001421074005014020f40540c02c80d4601c080c04426103045507032205460402e664a544404002c0c15140d00b04080000700401e44d8010407055005014840b0b82e180e010750601d00c01c0c40100e42e40d00343d002c5d1030040c450460409880c03504201c04641001208652041c0e109032900c441140320815035a207000c2400f56454000e07032a100e060302d1030360307980140c80d040d500c40555920074031100741c142c903c002001400c41140c03460780502a04623031424903800c1c101802c2c02d2000e5040140f00b00b1052112900382180442e84d4130859204420703842a0703001442900342240020f00d002401607030444001010002d05607a51118031003a0700520000d00d0b1980d0400c014400b10041c000c0680c0c05652200303036034a554030340020f140e075400a12 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 933197275 1250 933196025 933196031
    0xa150c061b0801091407023d020307030f0b03030703110c120f0c0f302505030c0603041e05160509060906090c0a02030c0304090e0f010e060a 62
    0x240d1820a0080002445007844019010940705065a0098a003812a10408404d00580000b01140884080c0946524002d41d1004104420020043c06101072500c49030007452a8035415662480c102c0c800c554500d20103690000c200903c86405124610403031f28880007c000d00c03500702000ca13941e44145030340075082c4104040b104210312401c008010011501070804021600d02000c1103980750400d0440b5010360051806c001c0c5182094002c3d560760020041549141e54440c0c0400038900c0200c495000d0a00002d942480e5010790420521006480b100405d04600d0000e005901c140070181e00920300c69080040d00641c1a503948050700c4c0c1007500500e4800e803101103107226155158445500810b60300800d0700510b9000c3c1e8040c084002c440c01603550030540e0b03840b03108110015034210b490b42d500103812808103e140da03000e40a440100c1c3c00303004813841c002101040314036640250b84442c03c46a2a0043c1a10199060108411042070b0100910440d00c1203060203499820081c401f84003969 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 933198525 1250 933197275 933197297
    0x181808090f041d07051002030f0433110705090114040518060a060306051513020c010f0e030a0207240f140a020c030f0c06040b0307140301080105010302040b0a15 71
    0x103a80c3d4402071200030800c2948010060750a5865152403085c411184503940021200d58000e00100864000c00704a6440b07074600b50030106103800301c1003c030040c1503400404103410201d12030320802040c25414191121500720441400051a06089803c107074055494400104500d0824500032419050111130205160b5611400004e061241e90801c0c50f440c41000e040c403580300c0c403d0f44080283da019140a0000d070340c40d881103418104003680c0d5140c1256405800c030700001e5182d070203001e08451070000071501a80700422075094544501c80700c1c8940d000000d51481c2c864040200d10018038801403920303900b17510900d210b20940380c0b010070350341030107540c411031886203100d50800000c071000d0f2400c0c90740b10251b1000c002d40d40d800d50001140244a0440c0b803140b1000b001544a4145800400305860142400345000e101d420180c408428040304220040b03440704428040c40c013800e940000010250300d5801000241d89100080034040c010010040c0503500c0301191717a04440e13800e4102058400307 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 933199775 1250 933198525 933198529
    0x6051b0c030601240c11040c0306050a1410021609021c0e0c01020d090828050109030809010b0d0804090b0111010e01060305060907140909030d06181808090f 69
    0x51240012581c0c10b001c2d6100201d200c0002c0814402001d400810055280c003860100381c0b0b1500013500301518540c018014000e0a00d400e40145082283c5803401040c11580c071404152024003a40141c122998000e00181c411b00384441e100d00e0a1400e48010001c40d546804004120702140c05002078254000030010461920700c603405000c410800c40401c8200c101034940c0f611240071000482c0140940d070151000719106200400c140d6aa2501030300e42c0c0252640c040030350310341c8031b501418800600b10205c00810028400e1306803d9020f501d9a10080c9011300c4d10340d08690014502034815a2184e404078040746940041d9419545882000200303480c401d001600c42d07403124400440c4642c01c220740111005019005031003124842e6048400f60b86442d40d165032242150701442001400c032407103511303541c5040040d02e42c00c495400c00380c82c034010007503541d0000d03103900d50040c40700350300240d040c1c01068001d441405070a080c40401110390b61103590b91032805202d103200140c07141c0c01d00543e0b04000c0d = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 933201025 1250 933199775 933199783
    0x210e1c02100503011d060108061c050312010e010e0c090f061b1608010b1f120e210a0e10030609150e060d0b0f07140c0c04110406051b 59
    0x29540041c6000034507510100300402c0b41e0b109014a44040c604000440099400c810b00d10780200b0303058448081c02d940f402c040c06070300500070881e8001c803050103625001143c81803004100c1c011a88180c20806d40c14015406484001a400810340503c1501040800032202d000c2e5030403035030704540038030361102c1c1600020705074003e09500611007000c0c1007070b0040605001486030452010055101c00b41075079000407500b03c0746c41c140b00a4101080e1091854006502c10320700440304802e05140243c05a16a43c1c02e044a0515024041d103070300644090100c464145500c0c904400000f000b14584459110020401da120081190150600d0b04441d2403e03030003504054050585008200140b0940c3c01d00c081e403840c542c0c801c80c0305010f0303030902041c19800c2c5240c500e61001d40200d0201426100d4000e203900c02a4018921070812a107494000d125904042c018202c41880310000c04c1c2010704401008110f030510411503040800400c02000b5680e0440300ba03ca81e98440c10717102003c1c401982e992814 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 933202275 1250 933201025 933201079
    0x10e0103081611091806130804030204090c030b0c0405010e100f030b2101051f12030c050109080409050f0c03100504020310050303040e240a0315091e210e 68
    0xc0810841e0801200c0242c03c104400078010010071143c46c0e4860203005100003103e240081c04c040420071090025080c0ad401c84d00526220700c0c100c16503281d5a807580d070180c801c00e44a802002c05d00040401041da848002129403c0044a15007850b0308101c60183c804580c0b02440414542c94000700f02007651016101003655000403000013000c040703000424021b0100710b9820566085082c0441c00014041200c03209a070b104200010034085a9103041d035401c50240000c4a207903403501349010009001201600003416551004103050400c146c0c00c01840c00001c225888208081c41001003400a00a02c00b045403000d96006a8a494030f102800240c081e03074004680501c0001030001e2021904c00001d842040248c07003500405042d107000700a8104e9000015031300021070f810a2011a08c0240b14542c6901d5081c000191203003a99161940000c00943c00c81d18200c1c40d00303102c024000b03136900c01701c8103d400840b608015100303054007906205c10340203144d000d03122428000c000c615440726a00300c = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 933203525 1250 933202275 933202279
    0x50c180406030507080f070f0609030b1b0d05040b0a0c1b050c210f03090d08090418060b030d050712081801060909060605090f0415180501020a0305010e0103081611 72
    0x3104d540fa101070030390380c0c95402d4010610703101d10240090740c00754002d5044161115962035078040e6256484054a1100c064904003d031441ca0340c55429000300c0034014034903c0d03200000820030b46041e0911044056004020040389800c060f8840340c40c0d50701401001d01d44050315141c000103425070414924028540b032102d0703088400c030304d1407900341c2d8400b0004003221145802150f00e0140303609403240c0c6030701a010307815800a0b0301030160800114031030060800220080d01c00640342800e598481d01c02c5030340020035940c0507138413820340340c0a0a061028800d41b00481c01e00d60301c1c0c01c103d50340d540f140810000c05042002403c4011484002c4008e042040f20201b0600910a41c0c6c1c6458203000103000e80d100440d103191030704c1d0000030541050b20015100c5c0700c581c0c030440602d44d00c685403c0070251000001001143e540e03265403100e02c00100d1014080d50184000589078203020401904070340040e0041c0a00e580000010000100d885089500c0c0c076080400c064203048480c03a00c44880044211215 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 933204775 1250 933203525 933203533
    0x9030b0c09030c0d03080a020d0e1b010201180203030d050a02070503070c05090601031407080403021f02071a04210e15070606140f24220603050c1804060305 69
    0x151036201400909045082201511a20301080c0c0c00c0200d070703070a0a040240817407030110004c0c6141a9a0b805403c42c49007030f41c0c011442540a02d03101c0c0c01e0030703260f01000c040c1170650540750700b0b9543e091046820010002c540f1041e45856600040e035a802042c01444182e47c035100001c80c030a006d0b4040d03503003556101c0126600c50142d4034004030070f88014000e043c01105000c0000e841584607001d10501458255285c000940b84c402080300c00f01c030020030540541c0700341c80e5020f10360024070000f01c1c04104410401610358507185820142c84011b26070010301000804103100203e80c0c43c03c0e01c009a444000c103192026240d01109030742c9203018103100765120b0411000d012012868800400e4000d1049000700401a1114a55900e00d000c114001c0c3d000701541c22504814140050031454060383c0c00301c01d1b000022520310074a4944d10502c501000081518100000001d0b6081c028001d4241e45c11709000d14a08030541c0201030144c0880c1d08071428181006030019103c50740103002a541200030b40f = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 933206025 1250 933204775 933204781
    0x6250c0803030f06011713050c0907020d1412010b0d0603020603070e130c0905010509060d0f0e0f0604052a0301090308150901050d060c050c06191a09061009030b 71
    0xc507141d81084560070400403032200042e05540c450070b078030040d08440310001c4525450b00740c10241559484d22044440340301d8841c503840c05980d441c1040d4480c00b159030085c120f94407404001442864105c0000f89403190521546101280314900076054464a0040c9078503244504244005000c065101a412010020605c02100d80c0665400c003042c0d030070354a0081c0d90b50700483c020112402603191000240ba40407040c04151300c41c3c8024006410010026070a044883d1540345c100d0740038004548580c0d60305d802c6002000402d0091100c2c000318400988003a140c5500c2c1c864a803000d02c0c807490103400e1081080241318a010300c1e540c03440c90740a0000c0200c00480d01d80504900019941d0315610084000705222038500741c2e0480381610b00c003501c0c8200800039541d5440c041d103040d03000c0070188402403000040a8408000c0940320303102802c8000651040c02c0701040854101c2e2a00502034264091a0a010780710041103035005201038846402201d80c40d48112810802074000905c844400c41c28 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 933207275 1250 933206025 933206039
    0x30b07021e01020904061d0604050604020d1b0f080c03011e0305150601120207030e1228060531020103110a090504050601020c010c080304110a080a0c08060606250c 72
    0x1800110304c007614200710281d1a90170940c030700010025403c040c1980100020740e107040680000d0b40000e8064009030500f45285802d50550300715501c90803016a0800c0e07482c028a6003c3e40303281c80f10920b0706000a035804e141501914611050188a002c007118909803201d07160a5040d2000441c1c012040e110180d04241a24030321560549409000484103015021405030500c01c032401c059054480442c891041014403403442c802624070380b11400b5920b1080300d0185419880010300c461041c44800d0305181d854140c04890025010300c0b07907108000c2200342040e48403081424142c2d0402c14004100d03a80348012001391820906081e40307180f01140262956070449043d1003611801c0b01c083c0301c1a510034004981c1c0e5546198001c0c009244604c05401042002c001582c03c980110300110100c510746012601041407588142e16a901520200702804044a03d41c40074019003030140c54a42801c400003000c034003507890841084140d03400b08480d8a1058903508489541c4013504901d003d6803050 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 933208525 1250 933207275 933207277
    0xb0705130314011b0c0b06040603050706020f01140402011b020d080d0b040b09060102060106081302060a0c06050a05010308093c12010b0d0f1a0907060324030b07021e0102 75
    0x1034840b400c1d03082c00003410765081454180940c60200da61405d820350180d4960140030b0303d010b018960000d80c0d039440840801c0051040c24090304a070340080c12030761000e410749402c503250050003040d5120201c1c03d100041c3c6c0e00460211441000307042006108165000017011541d0303480c0003c111410002d00303c18088001c0d00121440d0808440801100c210700c0c042c0240408100e4030680140c1080b030052140c0c5014030034580d04071a02c1e08000710701d07151580c0030552640c0024184000706840f2085001081107a024890303000601c541d062040e5450741c4d41e04800c900030303403142910840c03040d03100c0c00c81806142c000004080300302541c1c11604412284404102d8460340d840380c0200440c6040402c1d0b0320050003007103c140f1014001190441e086e49a600c0e64801c2000d044a031511500000190340f503031341d01654011580203010701025071a002000c0d007250a1030880c41c02e8041005000f4a1603070400003000d040b207410510180c03031540d51520407420a01d10b5045440c210701d50702c5c140e20030b200c0158 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 933209775 1250 933208525 933208553
    0xe040c021605040207080a11070305030d090b06030d09050616021c050d05040b030403030902040b220e150406050a1d030c0d09050607020d02030106092d02070803040b07051303 77
    0x601c501941c540741c0041c80140d10644001900070384040200c0c01d0a680300c0e010101442e0b07a00000d032400d0540703c0d034415085074040151012006d80310110b00e07041c004046000340c0c201008400815a0011a003405003042e600c600c200ca104910100d0081500c64196802c42162540100350031112004000d20002682151500780c03443c0c031820500010042c01900ac42e0700360340c074006500303003107030f440341c0d4101e01821000390103d8102c1e03100c000400c0181c80d40042d200d6104007030342c1c80943c43d00e0182c001c40d003210000a0140c1c1d15912200c40400411009915141c000c0e80104010034981d48a1583d14058400c40c01420b030721043c2c0c1140c4207456031011000d0802c3c420303002c0a50342200420714049400c10014014aa48400100480700052800e0204c0c100070707034070280002c550182d84050b0310702100d0b460419800c120a00556501c000c040c10503a20b2070650501c0c0b411070805200b52550203480c00f004200401d08103c3d4030125240600510613254482c260854201d0090344a181c00c2145030041 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 933211025 1250 933209775 933209803
    0xc051002030c0c270601090b0316110718150302030f031306080106080112060b03030406030603021f0c0f03030b0607110102010e12192c011704020906100e040c02 71
    0x43c1d1641c04071483d01580001c0500e0b2414100100c258040300a03011698025084c40d040c081140b90028504801c60065445244141003010707201000c06406042450401c24240c1c858004040c180034012210100c0c026560120300c00041c1640c800c8000d003030205194202030350500c03d11403840380480e000401000c0441590301c0c940c8803a0341c1c550050718510820300489010814402c018804800203580e106441401000003080000085000c24115402a049100040d0301d415090095013441c41c84410145030398142c05860341440da200400d00321044034000e0a10340c4000c00c0e101070502c26003181c0c0c6100300040105542c1c40d02e0342380a031203070980c03078440601650030020b2544200802141c6860b04600e44c0f8062840c10148540c04c2e060303075440d54603000c20320620390049407520b100c2110300c00102140045501414500c1400505175264021502150114103000c02c001600d0b404012034109130260780c40c0030030369002c61081c1ea840c1030301e50495400900c1e284042c00303411303070000e0160049256 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 933212275 1250 933211025 933211033
    0x31e0c0909150f0f08100c231e030f0c0714061914060f04020912120c010b0d080d020d0603020d0507051c202d0906010309020306060d0c051002030c 65
    0x84c40e50f1000107000c280c4241852600310340c88403903142600e504800e0140c05caa01e010f0000703402c002080300c40d030f42204c0d02ca96100c000101c0d88000c04980e10300d492035100c81c1c400c0050305620b0109a40c0d10320800c02884640d0505001c0385140402c14207107542d00202d4110820b4940c540307022841107403032081e00c0012800d1941440344452030b0041d000704450164101400a1501c20302c4d61003800080e45c04039100c1074101100850130045010709002e01801010300908280c0d1306c00d0780f807032071a094414060070307188a603079014060000251400104c81b03020101c0c010150b2240700e0340003000014402540701075003007881c80700410100b1a0100b0321405544046170030b0802c01300d5882c03e010f983d0a03007d900504d001d9440e04880c21342000e06c0d5070343d20050401800c0b00170004007844400e0340c821b18000c11080840c48011101d101c1c2c42d0602000358049130a2a040054100640001742e907498003900c018002e0100c5190750084c001c06040b1903024001c00341031000c8000070b001c0f0080d643e40c8288103180c52806 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 933213525 1250 933212275 933212279
    0x2070e0a02190c15110c07030f051b010f030f0b040903020a0611031302060f090d0c1706060904241b18120b1806070906020d031e0c0909150f 62
    0x402400b01403042900608106219001c00c200c03600204a00d403c003040d4880c09004692046c10f0411001b00503510585400c500030b211403414904e00254440180940f00c2409408045030340e0202d800100f10040c0d18000c0360100001d0703105401459003e50064000d801c090b545004c0c150002612400284076a90402c070148070003144c12140c0c0001c0d101c03420ba8071410f618010151420304040c003060102010807602c1e03d405980095001c9501e943d0403151010f208030304100060141c0524881d503100b00c03014180710b01d00300c40081c000802c0244014170095039a42407507010350610600040000c4030304000c0080c1c800d48001100c500c0b2400c64010009000d451485075401c001040d00c50417034200d50a21680c000e41c903500c000240500802003062004180e4404201039400c1008a004114075215115640d0030400e00a0030010700b2800c0304149070034a0385401c13150550158006034107038103160005d10800da0400c100c5880b14960300104200d81003d058000441ca80c21405084a0000c640c2d084219 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 933214775 1250 933213525 933213527
    0x9190e0a150b0d0e1009050601140d0609030e09040b180c06341115090a03030f02030f031f05030d08040b0703182a0f1502070e0a0219 59
    0x1a070924400c101481207807010450814071001500c01c0f081045004110240b0b1880960b00d840000004000042e844e45500d000b440340c240500c501406011a2070080300c020200072521019802c40024084c599580001d0141403090182e10b04c072560003461440c15003001c1c103004414000135038202c4a502107405c41c40500000000300b00c1c40030b20003d00554149604078070081c00b056141107504500c040001c0644840ba40466500d0060070f20031040031420950b03140c14810040d031041d42c211036039101003103101d0255640b4105107080f26410700c1c020b150184000800c80c194003401e03001100104021007030107007084d1584001c00940a680111000b1951b55800b0580d0794030007035000741c002c29188800714021509405289521001504020420074440390300c0011500240d00f0035150f004014448403011155250344101c005175170140c0d81c17101d0303090003442c2c000e60141d0b2240218240e1148038442d8001d0080c0300c640005c0c014211610350601d09250f00b0b101a51100c0f440c405074900c44103d110100e = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 933216025 1250 933214775 933214781
    0x10e2b0219030f060c0212071b0b0306060304061e0c0201051b131809080403210302040b0f07060e010e06040521190e040c0512090c09040b0c09190e0a 66
    0xe0342c11403e2480184140e4803202d008180c0da00003042103000c1c0c6111540401e48840003040440d10032000d40719184005090302d90000225001404030a00401c14040155100016640c000750440c6000410030480540503140c00031030b0701094681424600b00b50600307a010f40c844e03441100d89451101f01190840f40c02c03050f0303102d40030704018200c10b403901c144004111000300d5461030464400020b02888103840344081500241e20072180d05540d5203c1032809070781100c2842030400f05007819070805051146208490041040d50a11846c0105100c803d00c08560070440ca020740207402002407140401e40341e600c400e001c58080d590741c442da100002c8001d20302c515020340c40400400c00740c102928101d0400014111291100800c80b1800400d230141d9980e114210107a40036894032681c1da200a0380b00d006081c00102241401c0e0002c0d496460389445800c001c3c0e42c087d0303100c214002c0c075590705004480540114a6115000005102c4e690f8105c520364000c10250351b403070080ba88480d44c51131001415 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 933217275 1250 933216025 933216029
    0xc0b1e0a051b0309070b040906060e0901050307051314092a100806030c040e0607140c0a0f030c140304030209060f0a0b0d1e0501210f02010e2b0219 65
    0x800e0b0742c000001407000000040e5801c80080410340d40300d10b40d11401c0960641083d00040b80740750303440204121854001c0032101c0300d82ca060f038144445625000004e51900003600c05c4500074103400700b24104040680d440f12120071845008050345080001349140e030b903412401e1701300f501d8a01050340f0420000310400711110030b01c0200015070500135080e00f15415000505800d1301031044480b4040380f40e4032406408c0b24110840010406481d0040005000c036014142080902100b001a028400d5010410305002500455883c56030035a91070103c44164032410081c080301c40031304031043c44020100090081341e008031152801c0d5100c017000c000140c5400c180803580034140c4082000100684000b41410500d803040c005040c030202c0b0f103040c1000e03450740c603c480d090ba5600018003074219501c980e400c2485502c02d0308400383c2030710764500c4440a481c12010f418402e400711808415a42c90406075110742e0801c20080480c04440a034211f11145182c08034862034801c070400d11043c80103050703201 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 933218525 1250 933217275 933217291
    0x5010e030403080904091104020c0604110d080d020f0903030d0507090b0306030a020f060c010e010e0d0804081e04320319030e03013c020306010f03020a0c0b1e0a05 72
    0x86040604c0c01000020303c22441c0403240343c41c0300b003000300c1980e440388083c0a201452402078150b40c649880c0403182d510340844918807890151800d1000b08036144169030000c0300310040140d4503502509407421500422403171540c10f03c030006441407100110382001d23000301e029803100c99119885100210b130340e020403601c80e0380542c07000244001601e0408090b0388a80740c081c1116103401040c00e815400d4442690110720710b6915001a8580e00104201540c4004901d107000011824140e450752054454020b810b09201040c5510080d83c401c00403c88004080005004906030400c02c040c00c10820740f10707404032550003403e0303404160717080100361400e40d0a0f00101d846101c03110b6a505070341c0f0510784002d03550159620310561402c3c801c1500040c3c030075480401406c00813104801c0c2c401548050b2100384031a103005009011003640c109440703141600850402517150322034104215851036403690040e01009901c41442040140d8020347c80e11a41050075954042e40d8640000c42511020b8840b00 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 933219775 1250 933218525 933218527
    0xa08130c1806090207110415090608011a030a02061614030301061e030903050d0c05070803090f0609010212060d1a07030507020f06041a040218040318051801051207080f070305010e03040308 83
    0x1b5120302d000d030702c0075402d020790301c122101450303c91400700d04507112034014051603903507140703c1800059a4148520300c01000c4006081c01fa0b030f150301180b40c5000c2c03007440b00754440030203900408002c0c1160320b1804101d071682c200c0f80c90f5a55040f008261054144280418110007200f00082074880c1c040c00d41c0d140d0f0162201441d02290301c107910b00034101c0c0e5a400e0100401407014000040a101c01503000307000c104000d1285203900c20020b81441c001070151901070f031040000491400a910340307944e1250044504011102d03050410b0503044460b013000c0c501d291b0070300d020007400300d0b099032146000c1c3c40c3d564200d5020795000d50030160740380d10070380b00a0300317076950005416150450b0340302c00760b032180c8090904030a17034030308c2006c00c18480d900350340c2140411099039801c5c52a00324040d03c3c800a210481d84d4030b00041c0c003a00b0301c0e82890018040c16005101d9078521340f0a03808100407071402007050408440001c00d003914456142c2450b40401c844550804280c15981203001007038900b03482d0098005 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 933221025 1250 933219775 933219803
    0x705060717010b07030215060d02040603080c2505010c150203040b09070b070512030c0f0c06060108060a0e0612010605030a051e010c022a040c0e0f0102120a08130c1806090207 77
    0x1102030348001032610703512466020b42c9c000140c80318001c0c071006520650040e500c542c1860001820700f00c28000050550700c0d911080d013690b190071500706003181c02c00e081c501080007003801e0010301c085801c81c0d80820340d4000001d102c01c001040d102184114018015903140766103a0204100500c605c0392701401c41d5205013a00354900300250000d64028500300051490800c3c0c215541103c0e402c54410a007203500711038208013083d60410043c5502c840d00329158000c00303090035413520050030081c0009010305c0d0f037240d00c1246201b09610075030140100504452511451345000360b9580e00d010344007040b4190008090804220501078544418899000f070a0003503c0c004a00410250a0548002c10100b1150080485c2c84510460076000e40c03640c2c405031003c12120510400901c0004414110346c01200a02c5895685c4426141c0038859454030214980341c280c030b240300303100f60200040c14403494100c0004400314150389510101c016480b0901c0120f90f2003546000b28068550094441040c4c07500c0 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 933222275 1250 933221025 933221053
    0xf1511070f15380306010f15023919031a0403020a120c080307050a1808031c020c0613051009150509031912110301121103030705060717010b070302 65
    0xc60300c100140d0803401c2c070390b088003e00024a010b07000ea10081c1801c0d0214020700408100780300403a5001114002000c0e002d00710301101740d1000070320907a42c2d007081c240004800c05042d10300c480070440e9002000403014000d42840000c080240703100440d000710101c1e19440c00c0f0b200c800a01e61040e6099009424000110384800700090020b002080410084143c000d002039444409140911440d5a840303440d400d00e803801400e0f03101000d400040d00b00e54680c003088423103400403c03a0403042c140d603102c040803060000c0704006230080001c40152402068200010441c01c40807001010703000d5000c40d0032403101d481c04d071402c170740381031801800042e0b20840e600311681aa4000c150404103010899143c080d10a05683d110300a0485a400194003c17560744c0b108581c1e03000b0810348a1203580314074035551514ac0248820541b2030b40c010710200c54039060480642d41481910406c6402c54191411441c1c0b464005000717050840711403002e80401400868a03c48101c1038031040da606800801e101400b10030 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 933223525 1250 933222275 933222341
    0x8010c1b0201030b060f0301030b010f06051806090102070803030103120e0a0e160c051b1e01120b150d061d010e0711070f03031706010c0f1511070f15 66
    0x81454118134104801b14510050700019402540607088050055050035004103000c09143c0c0240204901404000c1000b08480204141684100c0c0c0325039440e03005000603402c101309a402164540400302c00042440380c88100460800c2d03040c0e030f5a0321080c182c1c40405c41789a51a0080507151011800041d113840503003440c800c2401440e08005e07075640c8095850500d014020080e00c14091507c15175050581840c404401c0101c1c50f40c519681c50402100000304801e22408084215a0310b501442826865400c1c104018045814000d82c1d9001c00034804800790085115008100091191403016400ca40e0a01c50503a00d0202d280c480b180c40302041103400303000c400300001441c060400e0010b84501b203a01e51800951281e00c030b8140c0140021142c2600007401040d190501c01034144030300004044644025507d58448110b00f558520411044018032207184003c0144000040e03140503c205220808495131040895800e102a601621410b84c1c00701091858481811410822100c42040d = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 933224775 1250 933223525 933223541
    0x3190302090a12060c170912030402040f051003050d0804150b03121c050603190215220e090106051309030e031002040812031003030e010e040e010608010c1b020103 72
    0x80180b6910703500c4515180d001604403004036441559040c40031011508240403007030255a02e40c00c0b0600d498030781c1c195511030101c0c0082d0310b20290000001011995158804180700710b86500402c854500414104424105404103031f5051040701049042075214904080c817507a80504d01303c9202400119a81c081d003500845160326000e001403d0304c25500020151448085100710034203443e40400301c44044480113070030709002c0c1d0412850402d03905024403541c86443d6065078150070140c0360824002507801042c0744114420603650803142d17680312402c110b009440c820051040a5141c100c282030072a40c861180d180c109060313203d21002001c00380d000340ca526010b41804002540c0c280000390a10b002c48003200d41d401e80c0130130709014842d0100800072440400040c60744c40e5090540c0c117110f0000340e41c4001010005540c0d500c4201c0c0e407066007a10110b03280074006002c008030324015140038103d180180d002541c80c00b440300d802148079413032000c094900c3d10700300ea007028074540045001c2d00d490 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 933226025 1250 933224775 933224779
    0x121205010317070f1704050f0901151416080a0f03020a02210f0301031506231003061e030605070504060c02040c0e0d060606020c0d0203031605070b04030813080319030209 75
    0x140100c0b070200d070b05c1c140d40c0700c080f14502001c140d480d4182010400c101c4440d03100d4900460036100144410240c03501c10300121075280c104140b0540d18040040074034401c881c2031000340041000c00354208540c60029005441071512015449100480304800300c0c0120307400d003401030b403000b943d452140c041900c1d64008011078001d054900701011168080545c42a40229501d0010441e01c040606040c410750000d040e41200149411407048128400c0e42c44604180d0300c02d64591036030f1791000d4000e038401401441d441c004030224540c441c00107440c1c82201d1006483d007509220005452a200d1412501501c4494030351000010094007803000070700003c6203000c180850b108015946a40700380d0300c0044140314803800f01e81e16080400090034514414502c4e80501c2e003032401440141c0d8040250380700240400800000b00d205030174480c2c9020426408984181340004000c42400204070007000b0000b03c3c610301807002e6076a1000315a07244121102c1c14003040060b45013030040351103038004040032400 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 933227275 1250 933226025 933226043
    0x5040603110c0a12022503060b061e0f070b0906060405060f10050f0c010207050a1401051e040501060306151a07050a0308070e04020d050a0c03060503190f0f12120501031707 76
    0x1b000241c1820542905840c0380f540440c81810000c021b81400740d810354070001da030180e040899030502c1000d130355194200072103d144040b44410781c1b520600141d50002e90896402c50150401100c55a1107590503184035000d60f0406000403080e007400ba000150814002e40300b100b604002906c01c4456802103440b032202808200b010414420090000d4002d41e4003030800f519071107100e46001141c001501c01c40c1a0141d060000f0010840da42c0d240000180038603805400340b0340d545142c11801090f4540008007542c2c900b41c500d4a8001482c600e00d030030380b114080091120411066032604601560300010b16561228500100080c031408005821114a0a00403030143c003001c0050266001401c010f03d586503a141040440c1419029464801401741410002142402d01180e19400751050b1072002c041000403000400500c0c1188401d106e030000410048103903140b0340060b84da1001ca0700304000815460141580400e507100b864100e0364047d08040c50b80212a03030105264000b00ca003910b040b04 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 933228525 1250 933227275 933227293
    0xb0301050f040e070b120703050702060114191e2702090111070306020d0518070b03060117090102030103050106081605010f0512040c1a180f15040605040603110c0a1202 74
    0x40004c1d10140c03806014881c0c0f58280000c6070851464020050000c1500301004c1c404195000318030341d41907500040300041d0a0704240c020582f86d0201c6040c0b12850300100c84000f94142003949185034002e0141142c003e100d5031400344020482d150301103400b41e1100b04440d4107110842d030f0300030310780441e042c14243d81d0384000c40380042c108038641e0700648040b9000100000b00c140e89104840d409410038554400c0742d20310000f1182c1d111801d005d603d0601000001140380e81e8018001c0009040446a840c0551301c3c1451806001c4c0d007003071104031807940c00c0072808142c884c00440d0428003014540761803000360745814011581080840c01d400c003403007810008080e0407000042807510907405114920a581c0c501a59000000c0484c10403481c4600b044c00700010101c890785a1407540d50701243d18000702407224001900a40d00305003c0e84440e50300040020346540c10070050070888100383c4040084070500c0f568002d1902c079400d400c0356190407040120001400143c41c0843d03a50b014412030712000 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 933229775 1250 933228525 933228551
    0x6060904090b070c020f120c130f110403060b06040617070e061603180b070303052707030308011a0d1d06180c030d35040623010b0301050f04 62
    0x200007500c00d280001c00e0381c3c1c0344c1c100f50306004582809011781078540b1901340d40400d0041e07468402812140c1d11030800d43c1d441c42d01d210126080005000700c3d005003044801c545040300940b9510920080720801e08002c6840d4103443c04100350b60442e0301a844110042c240c064400100d42c3c4014100010301c42c2e003d800100c56258003016200f0300c101240340700d40440e8a424050403620100c02444e090340606141800104010703010341b401203605050114a9440390f8044800300c1c104280508561543e1002103030728000300081f51030899020ba25a80c0c050b0340ca813103090000d14000303010940050010003450410351455441104540030102004950440b0343d4484c0c3e00b00760302034858200b200300d15801d0b003001c00c806121030b40c003128080b0000c090310320110f007001c0d00950710091183c4040b0b00e80660546181c401420000103414004402101444c0c5407802000409042c41d19500d02441c5030600701c5080c82c60320942d030603902622a91810340c0e10704001c01c4400d292881303100740c00c01d4641451070019 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 933231025 1250 933229775 933229793
    0xc15012d0f05211b041b050901030b030f0a120f02030702011d0d0219080f0a0233030703021201060f0c02090c04050603040c05090f0f0c0f04031a0601020d170606090409 74
    0x312008211421007851307004100310036511201e1014640d50b40794461004003175000022640c0100d000e007030110304200803800083c24040c661890310400d0194031070600030488500300294000300d0940701c0c1b0340c0b000c5000000700d07560300074110002d0200e44454198420300b90200c8124a04003c02000180c1c0f94000b40d01040b007a1646120070780e04851000c400740b01c4054103004400d400e80d00c0700020901c44111380c00103a12a90340c00b00080405c00e20403800510010003810500b81206040c00700c0343d4134180f10701c004000750300102541c0703204c20b203000021032420b2080d4048050400075030344420300140c0540811241c400701611240c00c180040000251715116040070798411801004500d40207460a424403403a980020404410115400100445c02c04032445140d007141d00040e0f01034440c03004d010000224402c80d00701404a4a21701c2d40020440225101c2602c510b03001e0342a00d0f043d40142e0310070345024038890018080c2c0c174669000030708e5030f040410107040380e00c40080020030003c125032100044 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 933232275 1250 933231025 933231043
    0x2e0b030630070812070b01050f0409021e1801081c020f07080609190f080c010b0607060e0706020d0e0105031005040204030b01030b0f1005060c15012d0f0521 69
    0x415040341c0403c000302e0070b0502c603140031215100210380ca80307040d6544110782440c05001e001c2c4075041a000141258480303502119030729a001e070110410154200048440c804103440541c4a001400d903819800e10001001c20f0403074020500511000c0c0000f21481d8109482042d1725003103100f440d09a1800e06001c1011f40003c100c0302002e824541407103c003e41c140300316185040702c0c024028100301e0010b04d400b0507a0b040550007032003240c0c4900003802080d002d4403003206419070082c0041031040134400264420b1480050a40442d200d0582d59003050380c036004815a00004541c001e1603040d52540540011a4000c060f0102c54030002c1c1c680300002c2c202c0c0c001e0381017680c1a094140060041002c0c00e43d103540c22000320070b040100e80c9080b04101b5042541c80c0204d40c000c00f03002c5071006c80c4010410183d1000082510b00d0041582c48903011411041d190203222005141040f0072061a0003a996460688030340c0c40c4070150540c1010103221010280300c0c207040d01e02c860300c0e00d4002840001d002c1425 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 933233525 1250 933232275 933232369
    0x10e0a0b040f0803040b07032a060c080a09020105040911070501050406020a0908031201060c030c050714031002090904030503040c180605100f0c0201030e0f03032e0b0306 75
    0x140300d40c2088902d150a1403190448051984200300620010b088201968101a031601d0415540c03a0400554180132090b10b0041c00007090701d4030750100300851070704103c0c820303810b941c1d0342c40c642d6407180d02c03513800c3c1e0320280e00207800311f50704010511881c8560303000181000d2042c10510b20380141c2d907036480d007160320440b8103490b1290f021810711851503109088100900e01100194140f48040700c0c07014020006114101c1440482d101c07080405006100b044100c6030410140c50400740d90b000e074140c00306828444207110b800381c0603d0006a0101e0f1080c0d60030920050003c81555549542c1912160300182050360740c007401040000c1c040020508500d07552074091000300d92540740c44240300c00007d80261642c107002e42c1c50100d104060b17001c2c1586500300e0b02440c01050302140c920805040402c65211041ca50200004000c4042020700410300c6401120129040c0101c0071401c1aa003102140151842c6490410100320145444100180f60340100c2c50307049000110301c02468a000103c5041139 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 933234775 1250 933233525 933233527
    0x601060207050613270e01090201030c03020c07030209090f07080a02101d0922030201020301030b0108031603210c08041a1618050904030503010306050604061203080402010e0a0b 78
    0x212005505028107001000300fa110306043c0444608800c0905500c0d0041e0f407094000d59150485c0d00d034400e143c1c0c004c51080c012080190842d48202c0c5800780c002a401a0b01203420070403c0c10807240700744211107580c1c000780050b0210306e045030300f0020421030207450a0a2440b450340c60382e10240d0240300180003005840018040b1901ca0700c18401610071801000042c0700e5145a1292440ca540146403003000044418000640d151400301400c00f0100030809054120030300c4250030160154015030580b4020800d01400c2d0782e031508416580d06ca00380604c0358402480d680c9070b00190050040314001d11400246000040443c1815811110030024039400501414103010911041100c0d03d0841034a00c040245185000036050b45400c0072a00c2c901c041101201c1c2c1c000c00010780ca80c0441c054500244100c036541030909009110307420a01050f26100c0c0303448040b49244c50103200c0c02c81100d881003258050309405403400c1c3c91412005006030306101743d200040403169105101074029014141041d = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 933236025 1250 933234775 933234779
    0xa201002040b042c01150c12091802090f1e041a090f0601081b04180603051219080c0d0501090c031d0309040203040c080a0305071208150f01031404050601 68
    0x103030405040c100400002d148040c0710301100e2030380d00700b44e41515440442e0840080c00038004841c04042e042c4c0180c154a07440f04803040e03080c1c1c8040d0036800c40c4d001102c2c010320586a035030310904030300c5850344442d800860401c40d4400c40c1448900c0c0d1448900350801140b40c0d4801d000814145c590b0422980c040001d21139084032503242800d81301c2e8100d5040d404881c507528040d070010f41800c0c4050f003007561070803085010882900d82c0404440c05403481c0a00e15a652020700c402001074a414082103603e40036012403890b0b5008660150341c448130141c0c10150441c0e52020b4103803042c10000d045e200183c003040002e60341b001d420780100c070b0007040106400500305d07031001c6004044540c000410032000c4000710481214110000a40d4802c08046500580c1ca4a4501d8981d8011540fa4080d00c0305000c1c1c5000c0c80305150f00003000c0e0000b1400f491041d400a80300c201c08031641c8a044038071409400f0781803856031160500d414001c0741007006040c009524a40da09000c000b40500315811a5191302c51401 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 933237275 1250 933236025 933236039
    0x70b07110102070b0f0f040b010b1c0609060e16091e05040203090d030e1f05060a030b13060c142d0418060b091e0d0c0e0a05060102030a201002040b04 66
    0xd081c0c6c1c03100b100290b2002d10f082c02c4d80d99020081e0180315161700910081121042c41c030070035641d000c601d214000c040294695070462840074058500c280f01c82c0c25010302c00514000c0a07050f03011200f880e0b070f40d01d03208103500b40311000c0103034000c03100900c440c030310382c4a8041002c0d00c0f5031005501800320072004044000046a0041c05e81d444190180300b280c03c20300070014948040c0b00210440c42030001d0125040e610600403030a103048652000c1c00340303040102440009441004982025802350340103001843c0118401d0700c0074116042c8a0301007290402491400116102d02c4054081544c0315010711101d0810040400c0e4205402c2003201403100e2103800c038070f001c1c3c6114001c000c04924113258100301003800051102c8005103103250520400869550655860b543e040080551100080c944a0303200c2181c0001c601c02100c1340ca03c050b190001242c5590700020031f40b410403000d582c40001c23040610100c4103415075100e103110a68850040022811410b500160001e401c640303800740c0c1c60754500780e4 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 933238525 1250 933237275 933237301
    0x32304060b03070807061d0f0303160311070f030b070201090c0b0d2912030d110711040e030a0309050712031815140928080706080903070b07110102070b 67
    0x48441121750101c0c60401a00d9007100461040008040d0094290142100450324620540d80c8940d8140000201c0c011070b5050641c1002c21a030103a6201d1288031034034094281c2e640b400c1d0240380451104150208006501011002d40c450080d00c00840c0810159507200b50380503961700858003c8101081142c40309003140300d45c1c0350310313150510208104610b030300d00074003900001114140039801e03d516903841d1000c100200c5824887c17650042142c0500303c102d0b082a03800c00c42c000c8500105402e10000c0a01d00740c000c65412101c428090740c58a41d40703040550007094541000c07695809000c07000240e4181c0300f4000b0101d1800781d1104101640e5a8240c0007001c181a0030034844511134940000f1407070b510824108580071320418140d901c50a2500240000340302c00c148110200850710043d400c40c4c00c2540c900e048070805030403a14504e89034502074410000c11640f00000f58030622100c7c0208101158542d0480d019061007080034002107107103402d80c0d2040c94107a507641010b5003030003041c00440c0f0b = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 933239775 1250 933238525 933238529
    0x121a0c21182a0a0b0a0203071a06030c0108131e05010c05040e0106030207030306050d060e100e061303030605132f0d11090409110f0303031303032304060b0307 70
    0x40060280140c0a02c2c0b4294800000b264501441904441c0e840b920780740c03003440c80c02402d95040d040b45c88003000b0f00c0003540d941c04800121030580d00c8507400300c01001c0a43c0c00d107010799001005009145020001182d401c000101902c4600494007943d00204411140140c0e0388940e98200d0791602048ac20400d0030340d444003281604100040000700f1030681e404181074190b640d207240169a0b20340504044014040340d410890b031000e48172403800d0412586600c461b40c0034564006803141001c1c010082c0c070450786ca40243c10380b290018400103087c115100f2890000709e100381000108280c9039404942400c56030b0148d00079142d07035200c4060180c1c0582e95403003002005810348881c0b80c0b03200c100d05112070043d07000750007a894640c60f2800c2c46402007810b992009001170010401490030b4104650301d280c080800600800d800d01c0042c4441c2004400c403407107450f180d91180c0c02484556000c400400190380040390244080c80030003802c00b000c0c041e0394080c0b8050400810f480008100301070a0145039 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 933241025 1250 933239775 933239821
    0x30c140606090118140c07170405130207050106080303040b0901050a091e03110d0c0201170c04030209070309021504060e0a0303090b18040207030801060207121a0c21 73
    0x5010081c0e41e90700c0485003415124021407100142100c9040c99014004050a10000810460400801102c03c0006c3c20340c05000d42490105410642410400ea21841c00ba2030342102620b2440299841c01c0c0e001400d520f0b01c10f400001e0115610342c0306500f5604252021a41c2032185424010211003d015080d00314000032800c02000c100b0f5900da0b4840c4a941c0b20f2805845040b000d07d00c00e0500811110200203501002d44000841024005042c034407810401c0780428400c8110b901402008a10b042c46080004001d071b203003e08503004c003c011300b0010420030030035480703501103c0180c40d000c0c0700707401a000084030070313484505024001e00211020002d80c4c0c001d550f40501000440d90096070303281100c801e02c1800c0e5a40c02c0010042c00c00f108810050745d04103000003811401c140d8070600c1c01d4102c42440c3e0a4440964803046450031410303020300064080c045403100c050107040600c041e560009524907195140443e00745445e103a00104008844112500c642000014480080158200303464 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 933242275 1250 933241025 933241033
    0x3030309230309010c0f120e01090e071e200606031203090712150c0c0605060f0919060b070b150d080906391902030a1106132403020703080402010f140403030c14 71
    0x40038400810201025444e00d240e081d04810412040c3d002d6540707811401440210000c6650f0400010740e500d81e3f082d2010b902030700c209900360103400340c0c6130705880c011062200508802850b2010610700d4110200381a51421040d41502001135030700c2c454004106034030785903000e024265041010446000030700840c06200c0c4082481c585607905001c0b2540f00d00c514003030484420a40e1003410041203150820210340000003031000c00c2c4200f80082503c20451010300703069059100042c030901000c1d00c0b00c0104505800d0003042003528200d0050040c08031040e951517825142490440d10000c640c800462100702007405110790200300340304094039019000002541c000c0340e580841d9603080304800280145028060002d2580c9c1c4080c111900c490840c0c038084c0a650f2900040190905c0241e003400f0b4a454080750340400901a00a58240c182c154586a034140d681f80c006407030140e1006001d004000740401c2111002000c00051310185000e550794000703440340d43c074042e21850500b016200c9207902c = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 933243525 1250 933242275 933242281
    0x603090d08041403040306050628030602071502030c0c010501140609040b0f10022404120809010b0a060309030909060e04030c05150103030309230309010c0f120e01090e 74
    0x1000500d00c0d080006614001d0034640d901c0c100f0500c66400a004025180030010b000000c0c02016001176018160440d0342c00700f040650507078001409540c0c0c0424a00840c030700d83c00c1002c52401e034003600303800b4050f002201030b800e03006040740100e03030080702c00b4201400c02240d6192260424805c09000d84410004480c0000910001038528040d030078200307201e80d44401c5e01781d50750b8803003000b44148010050450140301e060044069100c958920340b020488803040041c0240c0380d0743c0307582d6038011f136000070100640d111280b50840d9808030040c01c1905564882c449407040e078a48010400080015580c0062700b6070b03862030000c0c088059580550340703280c1041c00501040030102e6001c0c2d00658181000d6150841a1a00ba802e25211441900000b0742c028000403d240e0160041c9000724480c03002180c080810300030089042c03400c2d0f412051142c2c000d001c0e0340724950080e04071080742805003402c0494900155101d45d00503000c0b40717040000400c0303100300c00c0043d40c00160500107464501d1320510986 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 933244775 1250 933243525 933243541
    0x1240207080322030803100503150601050a05280908010b01080618130c030b070f0804050d0815091e070f05030a02030402060f070f1509020a05301b0603 67
    0x4040d21051604900d6848100440001d801580f50000c540c4511784035241d10300060b401c01110510311509000e030160840010400311144031031441088142c65403810a00d181d03000701d40ca60040148486101e40988110456980b808400703003030070000b561144e51190a2980140c2520b07800d1030541d050141e41da00740600c3e561180d040c0341c419140c188962045507070b0740e0000f00c00c07440c0d03211000d0100910751501006100150149030301c1844c540d100c805840d03034082d0f001c68040900f141c1c0074040b50046c400c481e0141c4c0c4107030172094101110685640105492000003209004140c0314150030200720265420600169903207103a000045042c100307031400a101000e095403000404401d01e071980000010115642c20b8281c3e005150700d40355203919103080e440e06d02110074032001e064440b174540d0540c60b180c011580c080c12103103a1f405056101007a11302400e2081200300c0d22924100c1490070b21104071003d0009100c28142d984810040c010602070780280c805129100585030700400c410803c001c0c03c0 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 933246025 1250 933244775 933244777
    0x140c0307050607051c090906062c0102030d0c020303040209060a080a0308060d060e0f060c041203052a0601030b07082e030b010f1e030c0605031e012402070803 70
    0x381c005036400c0ea61074006192503424840e050b844080c40281c0c00d40740406050344241c00c02c06881c0e00700700400090b911204140c4401610183d080100700d2503240c0000745240301030f1038014a01040c0100c07420044000391400549003010074440040c1e0003c802c00080d8985010a150005020b840f001140d41c180400c20b603d40c9a0a0000390910001c3c00c046251502c6080025a803550812000c1041c001d11006480c2c0b45d1100b013032400c150344107150200780c3c0e1900c1345046408960018916800c40b1125550582d456000790f8602e981d1940100d04a14030076040640f558000044078003c0c00d05076045140004111501406440c00c10080d0820011213410241c1d84001d07d03412803080c074440000e600d0b0500000c0742c45400080c400070004000141c00d450f60300400c2c0c140d440310404102050210000151410517920019106a081000030450300c0c1c011b00040d41c00c48170300c140c1500807911134400d0104183c400e92042060381900d45240100300c4d00f0044001c030b00c0ca550303c0507184961920441640da = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 933247275 1250 933246025 933246029
    0x10020712080709080712050f0c010e0f01050d0627021207030e1e010e0f03070807170f03040c0504050703020c15070c1509121b0803100302030a050109140c0307 70
    0x81c4a010030100e0100380c01075500000416103181201c80c01a200c600501000106890480702c030310920081c4055808086600c032500907040c3c0d1601c081c041c4103010400c940c04078403100f6041c4103041000c4005844107004d484003806007010b03620004111800f99150340e024001c412001c1070f10506c41c0340501480800d02c99085282031802141d880c4000358100d080881d0100d071005044070b441d23208070001c68103400181803a540d200a95101c0d01d100d9101c00d032644109040207080354400c001410002c0c03018400e03002c3c1c810080307a82c2820044550301020340e43d481501d050700d00da01603000c20889485c0a011300ca03031000e1107103015410b03c0002c0304003aa41d140303201126001007082400040003507100d07090100d00190000460300c04102490311120040030441405c0c1c0700380c07000030781e008002c0c0d0140126a040f504c0a200101e0500032540303542e2010740001e05001507203401d042c400030140e0340400c028021680158000100c10440e850140c040044100f042e1441340c000401000103a03a0110358042 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 933248525 1250 933247275 933247277
    0x604061a1e010e061e1c020304050a060506010e090a0f0216030e030d03090b04200607060e0c18010605091801031109010e010b1c0612080d0c0201110d0b0d020604061110020712 77
    0x606c43c5c1e90040c12581e082c880700386183c14a84080700308800c0c410006403c481403030294008010030b890341d40045a00b566220082ca40041c02200031902104a43c0d004103080601d04400604000512000800c01e0000300010b0300002c2e40028030b0120340c03806210801c000ea02c00d0a00300700008659581d4404240000d1010304264020103101194890714103042684400082c0070596a182c145080d10051482c0d0003200b0452040c000d0b020780c1070415181002c40700c1e5800b200c040e603980c603240003200c0b9940000c80c00e54000c1c00c503a07280c1c000715034004081d50195100e240380d008030900710424400e008005910041c1d0001c4003200402c03c2c1911202190b2100b03103d4007407901d07018505000500a0005070707200d0034116010b50610400e1103001c1024040041084600b44492100e50310100e00ba54486035018800d0a001c01002001c2030407948405440d10300504134132a50106034000030f0540c1c20550009010071a14940c1002c001414012013198444403d4218104a0203489060294070301c488560 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 933249775 1250 933248525 933248527
    0x1f0f061818081309050109330504060e0624090609040e0a0b040b07110715030e0607020d17010f06050f0f04060f1205090604061a1e010e061e 62
    0x120401007184010200d00e07420409440e41c0700104000c2c19203150051140c16034844ca02800440e52544030301566a0f100c42942030301c0341c00f42d4051080c452194020340360a66001d00e00e4000103544d11503000340d00c000c4c490381400e03108524100061001c21004440b01510b410400d40703100242890300002c1d03c4948106031602d40c0c585406201040c000d05114003d180b4511407005104108052030059521451081c040c05101c3c2c1c03507150003a40e49020746000300e00c1130b4000c01005c2c0101c80510041c0c0c40000c681e032901150070790341c148081d4285001a83c0c10307801038024021681c001d64200d40c0208031510344070549251907252a050000d0308205016120400000043c00c42c02c40040e43d0944000030f01e005622544c2d156202d101800c0e40e00218403003030205100d1b13240101480014814148104594000303001565950b5543d0001020340381502e100e404074206002c0a503440e000400800c0d0408251208220082180098070f0000c0c40c440f500e20445042201d800201070030181403d007003070085441 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 933251025 1250 933249775 933249791
    0x4061d160e13021302131a12070c06020310050109080a230309030628020c0c13021b030d0509010b03030a111c0305100906080d05070606081f0f0618 65
    0x420b450103006200a0340c403244181e070143c009a065401040c1408115030903800260360741034210340050507041160150f040902000700c0326050314508a51118031890160450006a6640c038101d030010350308130a00311400f10050240c0e58000b129180905070354001031208a90130760b00d644040c4050103c500c00ca09806040c042010410400e9a0510030001c0a07913050386800c0704181d0501c9508811080c0751306042420701c038065280c0c401c4401803540c0724081c040310443c5900b071041c5c210340c0d5a401d00c4410350070030803483d0840384152024560b481c501c000e55500e10480d40010300380c40001d044c0450a03450b00c104c226282c0e0b40002240d00c101e00b642400c48a1641401526040c40017600b05071510314041c241c4000580c0e40b40e07000074810992050740c00895902c8801d5401225a14010000381d5030000810803440383c018030107800c0661103504045540fa13128a031007410b20312484c0b4601a00f142c4460b0302c250104480c082c0d2200c0c100491002c0100700e03c0c224512204840004001c400c0c26622089 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 933252275 1250 933251025 933251041
    0x90a020d0203070909081e040501090b1305040507030e0c040c021e070b0301091d06040512070212030706092d0b0c160305090a06090f0509060d0b04061d160e 69
    0x980c10040104084c20002d0341a14240f000c1d940d800902c03502d05001583c022004102042d100b55019190181c2d25060018201824880c09034002c002c8442a1a044840000d03642e0700c81c041c0612583c0349540201e003042034280c5061520f013403848518400d9050060f10200a540042c3c6400175010a4500040c0340c40d8101d00300e414030b0a50b811440c0c0d45440000041100c0d400c3e908010703940030a04000c2d4401c0058040ca442d22440300381c0c0c0041854000c103000300c4c603800104020b8651280000c250b034400c4020300a4039031841d4841803007200c4a545a001c490700348941c80799940c1c2a0348800001c10455451400d540310101f0340368000030001c0101c0d2000c2620381e443c1406031425000c080c805100d05440c1ca080c00b42440c1c004003081d0307105800000010481c14440d04030031003200c12200f1283c1409040004104020000400e4242c01110b481ca0950101c0e40e281e0940c0c0c080c0d070013200b000840c5d0024400c14100501c8080714030145a016134911941461000922012569007d800d03481ca3317210b03002 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 933253525 1250 933252275 933252283
    0x3040809120703030903020f042c0f0307051b060a0507020103050a14040b010f0807060504090b120724050307020a060515100203040e01050901062001090804170705010305090a020d0203 81
    0x1280342071600c900b620201c01c040d00206028142c90007100c8840c19064007500f000305554185450807000601c074001c0c6c03041c1d4480d0142684042d035030b000c21360b08210f200c900f4052668200800543c0c8540c01490000080da0743e507078030100444d005403612464003e403140080c0003885501d2009040513030311000541c101c2d5023544000c031190080b680c40c81d5581131608103a8072103070080c0200703070103102d01040c00285804000b400c003081740d81640300d143c00c06141ca0b503244024000b07091002c3d04064000c4405046103814040540a40805500c0082d882c0f080c0c01e0007900d00301c10402c42003d01404005205400380c0000303010354656840703c008182ca0ba18000821341060602038155000500869414040c40c0c001c000b03070040c0c0701c12262180b6160303650000c0090a070001c0c42041c0115410010041080341c91101c450081d10f0000000f1400c58040d60742c03120281e100740e1103003c0242c0000c160b6000e0083c28003100006050901e0113001c80e0a110f10041c0d11005181e000070b1181002c0400c02c021910140 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 933254775 1250 933253525 933253549
    0x23100e07080403090f0e06130e07270e0f070b030709170c040204270903080c07050f07091a0f0f040f0e030a020d080708010605030f0601051605010e01060e010b03040809 74
    0x1150144000d903182c0c064011b03030b041074590324403500c402c0c10304220320106845201c0c20810b8001c0201b8186241a40f00740820082a50800000307080ca0401e802c1c03001280100c1c551582250000e12500d88050180e40c01e003c6640c00a0110607410000d119070305074050a20000d503030ba403c0040c12500c0f28845182d1030241c82e545c02c2a04207002203000281204035000b40e41d1800c080c0d550071043e05480841e144222071b0010402004a0040c50110307200303000c0c110150100a100f8802c617841d101040b844145861616030010040e039031107640e0401c603800540801c00600c04103546840001e00f400d03000829050300f60702454022660f0315000c130880c1185030090144210b64109407542d60700c1c9540020349a103890b00d01080071a24010201e503003584100e840c203040350040c0e0790342819501c4402e00c2d00c0d40f811016282c2070400c281403004005031611070501040d458450740c00080d00300009032406095a803183d102d04000c00305040100f00c0d6003000070440307a00c82e03448070500c0d9a4000480000e2240200a = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 933256025 1250 933254775 933254789
    0xd0915230d0c03020a031d1002090d0c030b010611010b130b0310050a020909090a030503060f042a180b040509060103150807030b1308180102070923100e0708040309 72
    0xc40c0403502c071550141d000700403004060f40c044c0b201d40c0c4d8101440000305181c9041c2c007617035401000c0c485c1220541ba40608100c140061200110b1344140d25042c64902041d042569031b81c82e840010060290003040310804048500002e21420401d00000358401000782c00100005860741c140c0705582d68140218a03400f915404204031074280512848000c0d0005115240180034403000302d07800b40750005030400c441da8180d5405186544400074040340240140019421603280c000d900014801c0c000c03c080380c020b44061184a080d83ca810081110154603e481000e0100800c240103103405941190103881044da030f01e400c146c0301c0c040120010b1402c070121310701d82c038240d000c08541030101041280842c1d010b500000243d89540340701503940c1da40000d0041c0010000c03c04c200400c0201c0d41030200c040d81c140191900140d4401903101510100f4050920303d90b804001c4900015460380b540e500300483c41c0b502042641881510400c078003001c0c0c40e503820300890b100000e00701403050640c1c4002c2c0601c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 933257275 1250 933256025 933256031
    0xc050d0e04110a11150103050316060f0507020d02010c090f0905090c1c15020a0c02040c0905060313051e030a081915061b1509050a02030f0d0915230d 66
    0x1224000b40702d104e614000780c2c0d903400707201c014028100400080c1c50507a07401c007028500d4101d00b58000d140145c0041011900715444480882c5a11424130400f807051905402514050000d540002c0c04c5550364001c03403050100d0b50f1000e00120310420307910000e4491309140040c668952658003481c00d002c45c640d0715409644800ca00c3d4440c1544865032803018400e05c60044d403d00c120b04110264000d94181c807001458105280001d0b00d0305422004407801e090619003166500c2d000410b07000e620071199400038106e40382481d4200300c41005a1082c06040c2d12908800c40001d0108075160310881414404200b40d480114050f0001024520145000c24204000e500b40e80300709514801105c1c030a90000c100c98986000032500001c2040c032560b076011203100141046601200020400b80f40240d9072031050805003c01614100101031030f07003501400506403080350390001000d40c020340c0c01c520222031481400c081c60f603400084480c4000c0480801d05022241d90100710300038080c503c09058002d00b = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 933258525 1250 933257275 933257287
    0x3060c0906020d090b070222061e05010801030206030c0a090e010e011802070c06050c0a06110c0c030a08030402100e06180406060c0c050d14070f14010c050d0e0411 72
    0x50840e03000c80881d0065002c0d98120140084140d450300d504d8810055424410040040146801901040e200c00c0404114403800e02d8545000102c41040c0c01c42c181040700c8040041110b884030746284028982464066240e40c19a404070b0198000078124500b5008046280009180601c541c000030304601c441020036581e44605517074010314203102d854002c0300c82140c2034030020b03a18021101000d80011459101070700d400411201540302510740011800b5030007807500040c43e1801884d808a11142e41d0075110300040a405003402c0001689a00ca980680010000a0240740980740e005030100c424803d081e107090016038140c90041ca009610a80001c0c0c018003503038030170303441c040d0100c42a6420461161240000d40740c00300c249001802400d2040c008102506e00b0440130704000340318401804125500740c4106240590302d0f04120b0385210303603110030b1051464234200c2101020091030000f040125540f0742c07503291819801c605040107000b860448183d21b0f41c0c2c01c88850014104092590380d1 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 933259775 1250 933258525 933258527
    0x60c1e14010f060f03030c120e030a080408070602011e022107020d03050c09010c1113291807030506010c0b090114130c050909100c0302030f131707050703060c 70
    0xb1022552030560310b018004503003224a807054000b542e90544900036010102d8480050701c21440380c1380020490340d04610706070381e1000d0140c465038a2040b809561901c0c00c004420341000119003180b070031a03160024020116a003600c15100c070f1704070b4820060303562000c0c3c0d49502ca003000650000e1540e04405007031081c03280e80015900d549980c150790811154481d0103102010784078106d140350029440e0082c260202c0d4291802c005d28480041c100702000c0722080205003502c1c0101c0d83c000b4446140656030b600b03811340c000d480c40e00120495219480b5119607080329000a4050100c4081590707400005000d64022054601c4880e0420851001d602d000c1068501030000d440b210b88400d0081408508030384021481c0740c24241d40a081d0031080d0b401c0800b40110280010581e503400d12a01c02414800c5116106007034580318035680159481c6020a1201d04585001c0d00e41d91a2104038501480402c0514040c656850b0041d03014940d1010507040c00392030a02d894002800440c5424041c001c61 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 933261025 1250 933259775 933259781
    0x305070b040e07090b0a1121030414010b2b0615051302091e010207032406060e09160c1502090306060916140d021201051504060c1e1401 60
    0x881c8007050030403060f502c0b90340844450340075100303480a01ea0140507003401580240010070303a61034003404481c9801c03091580e1108070903130309101102001000092005102d6070f02c145140043c1c0e00c01c002d00411081c0340200c1c602480c41d8410701d4178101c1e8141100c01c40c3c03880f08040d00e00c1d980c0020046c80005186002d42d50f510703c6600c161032040340e030407005442403091802a515040c10080100f0000880d100908402d1421840f885045006401b001b10005814044600150040c241e401100f20b581812100817140c00c0d82050060005c150500a0f240d50781e0546603034088000604016503441500060303c420f40001001031000441d050004842d40a0380c1c0604950842201260610780314141404a03686041d10001c1045400c021800c0c0018007451030007101e0301e00d0100c101d24000104000c00c040340c010400d01040c58007641c004204c9841d0800070345080d08a14074201d40381c0f900d4910080d160103550300c0001e0604464090590a030740c00003c0103412242c000c2c01c00702c90810401c1105001b = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 933262275 1250 933261025 933261029
    0xa0f060e03181f0503010e0c0f0703080f132310020d09110f030a08090d02060a0305070f0306210f0501050c120f070c06052e17010c020c010c05070305070b04 69
    0x2003c1c5000e8208080c40d44103210000e800c0d9a0322240d14590900309080049040248070f80c009800804c0b00585040174075008000e124081e66980d2014203058100d00b2040c1800b034002c40c0780800080701d20300403e4001409071020561149811011080003002ca420700c41c400c0e8000900602c0818103510400044c2c00c0040c12920986461489a107102c04100b1900305905060741c040e8041c10100e0000b0300501d00a000d110340007800d500d54240307180e00141042d80150310303c40c0040c0c0c403081805205504a4081c1c44a40b4083c10144246030500c0510807042009000c00015402d0741c185600030702611b1003080c0a40c5420000030302031842e104d5480c0352554031085c1d07000c2007001504000785858668000440c0501d40c10b5443c0e001c22007040d21407202501e4060200310400f00c03010100d02c40240d00d0f001406003c1d6002507403c032441e1a02501c0c00503080054024034190741810f01480d41c00350b01050364402700300d0900307140840303680701e040c05031034501e0030740009150b80b141000c0860016060300151003 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 933263525 1250 933262275 933262279
    0x4140a2703020705011407020406030602070203060906160315050a141002030c060a0506060d140601020111120103140a06020a020a0212012306061324110a0f060e0318 73
    0x4550384035910300e0118404548001d030058000c01c0090000d507100d018a0700860000105440c00c000407030300001d0840d4510342c81114401ea000510000b1030505100f042e50008248025000a150240503c804e61640350859410160344413a41c48005018940d840050500a8080c1180b42d8540c0a001d21003014521064828980c8604001106200200300d810ba050400d010b0001c80c0c1720441d58001501c8040e20103039000d0300a0051404407841032194074440d511610804005d800c10000190840e184c16072159200f0000b00f040c1d2071609440140981100d52203c001410700c0600c01415050002c01c0d00c008103001e00001d40b4206265001034842401802140c0c40c85145101c0b1007400c1c00c0312081c3c24864050b0a1000103290262180d1420680c803060291036285812411020b8101041503508407404486a0018804d10202e0300d01c0308602d0701115040103242d4410000c0381c19502e01070100002e040740b503117940724001c0140c1c90f00303c80e45500482007100d84070300c0016003c0b040300e00c110301d1141c = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 933264775 1250 933263525 933263561
    0xb0a0f02040902070b011e1206020d24090f0e1c022b0e010908100e100f02131e120c03021f0206090c10110c09010b040317040612020904140a 62
    0x7a540e828005864215441136500d14850740c40341d83d5209c081d40000f00c00400003541c40344280b0210300c000350004400ea500141100240b810b051041d030031201000e12a000c0a840d202102240c014009a0f00b1856001c10060028181203241c0c1203240403017070104c4991a512003030405c0b1041c0701c0004403444c00040c985604204241c0d8400445903044244208a00c0c0e40c0007540c0020804080e6200004048040b07003a03c6182d0350850b48102540c805000c56031940c0c3d80068040c101403009500c241c081c22212101d0401d440000018540346445409500c20301a003807044c000c100b213803084441000b15406010755400c108070f039820144000b4000b407803a000d80140000111000404107003d628900020282c481c1016905011140c5840400341c80c8030512481c2c40d8021a9911000700754000d15900c4c00b1955141c1c114a00b05402c0951200710140307040003400103020094100d207505015041c0c402c2c0060b02c2d40300140c009000391a40c12560004100e4000601024082d1900142c44e0300071000303c24 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 933266025 1250 933264775 933264809
    0x903071e0b0f0c040608060f0918061e160306030f032604030f0e0102120309010516030501030206071502090d060c020d210e030c0105010f15020a0b0a0f02040902070b01 74
    0xb00812100880300710800400400c800e01109000d0084603402c80d1000c0d04284d1a00f041c603001c20002201518240070320041021007040303052081251035404100300084e2404c80116103d11807210740302500220b0440f0ba03402441c5e82d498401ea03ca000119048950295107141c50b0401600c9644510b04460002c0e07050b502c1283c5081b17202601c20702440d41035980c00c0c040303078040a0440321101d82d9000d4a04600503840e4611500722254082e5000d044140d000107018140200102c10740c099241506080c1800c0500410260b528281178510a64010444c81c80c1455401a80c0b4024440c201000754000c6000340c0c25002c4c004e5030760007805800501c0c1c080340d03030701c03881c1680c1590381c28608200d50a517243c003c627080400c202d890300b00c0d8040542d440122403d00340e0032013002b403e58a0903000081d26078412030041103228000c05560f6072614580c0098a40d2081030f440e1a894611f00030300405001c5e8403884410b0740310b08284c0c101c800070000d5000441d128841e914003203000d82000e01c540548007007a41c0394 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 933267275 1250 933266025 933266041
    0x2a01110d140c160302130e1002090111101b111f090b090c090a06032a080f03031027110c0109030c06110f0d0e01090c0b070b0907080a06050903071e0b 66
    0x2c0d03840e9887d1040000c0c0b041248820341000654808071203107041000748205403c2d0404100311004040c9031108010803145611100c0175600c5080409410800c112003503c04d101520100d554450904d08203824205081c4600040c000b410341e510300109206100c40c10400300e040040798102062100b1100f0b40040e840d141c0f00482642c1c060701001d8446511000c0604c0d00403005102080c60300c20201010608580c0c0e0080c4604058800320740d80080e410000800031140300c0300e0b02400280904d100410792040304100841c101460002c0007900c002d0740c40c560b90720000f00b00c4041d20400c0050b04002e0040e2540303807030300400044069004aa4103030030300c0b204262603480d2000b030795600d2400c000207a05124519140c03802400080340141065562154600049031141c1c120002404284c1341e095601c1d4428509290b2003200140301540a030407108090003286c0d400b04000509039080ba4010450703807640d4141c0b605600c41d89c60001c00c5040034080c2420b081c03203c0a98240103901588050a040d03894000d = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 933268525 1250 933267275 933267281
    0xb07180b0414190e160e060301271b05180a030203062205120a110606060d0c0905091602060f01060503010b1b2a01110d140c16030213 59
    0x180c2400ca200e00e10700e0b003001c1e0038009641510b00c040000300c10307040350b5990606200040d0541d40021910030901c00c04098030703000300a024000805491407461985000e03d41c8a002940502d02d000d01c1c540e0396a48010100c26400c032601042900e490304c03046170b808000107443c55100c1c00c400711074441000102103d5140c030141c502c08898001d4058031042c0c1e01c0041500d16003101d4448000100744500010000c1901004800640006050150354440348080084d00b06a24003201c00300b503510880400c150b80d25170009843c4074581060b00403444100000003aa451210303500401c1e041004502044240c6040e80180c2d2564031041e001c0e2001612081c4c0c100300032410900824000c40d10401c01049481e40305c500401031485451880418054107800701030030030b0600003242070916540c015054443c0c0141c02c54030301075482420000c400c0b14610342c80b280c03290b50448114003449020050002c2c003140b9042112010340b02c180c05e03500109400318012010a409010a80c040c410f400018940b50005c0c0c4 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 933269775 1250 933268525 933268529
    0x4050607081c2403080a0503070c0b07030606092c1503011e0533010c02030a5106080d050c010c050c100903090902070c051005090108010608090a0b07180b04 69
    0x1000081c035010b002d000545007923002070524070400c020b84203007402140819030f1440c01a10386070780c0402c0d41498100000e24111894005001034102080c04040500c0384030a0b42a090a11003c2d00d81c0903594408004042404621501d405508107104100e010124a00d1000d04000c0030808200d9503d81807211042070552682c14000720504c0549441074407031039031b100b03502d4800501d000c5561021350750100741040450310044401ca4007240000d5645507100d2071410722503804a409031401c0078540104040345e11450b261140b01d0510481c0040e82c0b108581081000c1c12080040350221000b0b81c01c002c080d940906211a0103518040100304003600c540121168815904020310b0000c15140e5603400070070422070102c0c01e02041890000d4020704c40d00180100758018201c141a131480d01e020700500303206c40b0402000f00300080109507042e0380c220000303505440075850281c01c541d50309a06140b40c1146500c0207003155485508104401d0740c041c94618400c05400c880c2d006050f550080c40c0100c0c0070b07034 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 933271025 1250 933269775 933269783
    0x80a05060402030d020a0c0b09130c0305090c04020a090b090406051002030703170103020901330c06050615041203300b01170a150f0e0912090604050607081c2403 71
    0x11f0101006254217140c082c3c5140d4200801c000c103105103c0300031000312450001d101020035100c0081258a0a041c0179a0740091001ea500350b14140c0b018100070010042801340e03035801c80010035070890783d444580c0070b2406804060803400040100c0c0c43c001c3d590740c2020720201c0005410b5025130b0a055800540c0070304070399015060720b03a035900348125411946501c0b41d50003030384d50f4202d510b00d000003043c80ea200040c00d15074840c035000c40080d05004098500040c8080c0c060041d8030310075000200003804850851700c5603c08401c0203000351404860207403d1103072032a11402d20280864040d105160a8008000ca0342c90821440940704010740701d182c1c840340c0385505c6100072000240070050542100303110341111742c4080007854864508000000c02e5810100c18a01904100944048100058801013a049090381d0514950000180c40d503c1f640c06210b000301c0e400309814040005103000d4402d43e50152506c4040540007080c200000c002e042c40c0c0a4481100c048007440780080c01005206807900 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 933272275 1250 933271025 933271043
    0xc0906030b180f07030b0105041103190207020109120c0e0105040e0607030e0c130203010602010e0604150f02161248020310020a02070f0513090c080a05060402030d020a 74
    0xb120710b0390301c0000700e403415502c143c000c426480c148280284000c02c040c602c54090b07401c04d94109810321040768039a030703c00034040c0e604006100102c0e501c080c0c032008011800d1000740c0c1c1c0e44146e20048440c5289548221281d042d03c0040c0003c1240030560041510010410180a40e907644104000e030f03000c042c00912560040404550b5840c441d401002c502c0c0c120904a82c1038908800c04120525100410042e20740d81c088014007801e6030a0140c03054803555040280017500381511500c2e40c040c8803451307144d1455070340c1c100141040241d80585820f1400e8000410001c3c08604040040081c00c44c01c25001130b0065000e40c58007107820141101c40288400051414a590500c102d1030b50f103003681d44c040c40b03c1a0196400165010480341903043e516100146c0c86446a80001e40b0b4503d5a0b0001d038181800c8010038003007501c0b9420036640c101c1242d0f0000c14919102d04000c506960a5040440b4a0080c10081d9040c8400014070501a900c2079040b2114440010750403619007100000090503103030 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 933273381 1106 933272275 933272281
    0x8100b0c0a05160308040608070318201c060506040603140a060516080a0b040605281e0e07030b1f0806090403020c13060b160c0906030b 60
    0x489583e00d049002c0c25503603050aa40a1801036004100c1c1e20000104541d00c00d410000c00b801e001c940d83d0300b42c4002d80c100381448104250f001212107030b808104000c1030500800c1d61625080c0109103911161181c3d590001400c40540060740c010785402010002c0b03201940d00510142d0130030014102d14600c3c1c904901581c00081040900c48400c4c112095459002685158006115440094031003803550001d00204041d402c2940c0100f003403035a4000d1440a8107400140c05d0300c030100b000c0c12a541d582080594242c611542c0d2804800203810041101404100354020517203041c0410842c4250000c2038025421103001c00f0883c40703200d40d208055801c408c1c2282c1045003034035060030354079040c2c80181d07580740a10003c900940c1d81d0f21400041810582c881000750240240c05076860265030540942d803145110309407a030042a407030000300d0200030710030b00e0101d950200007030180766 = true := by decide +kernel

theorem cover : BRFrame.Cov 933093525 933273381 := by
  have h0 := BRFrame.cov_init 933093525
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933093525 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933093525 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933093525 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933093525 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933093525 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933093525 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933093525 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933093525 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933093525 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933093525 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933093525 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933093525 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933093525 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933093525 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933093525 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933093525 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933093525 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933093525 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933093525 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933093525 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933093525 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933093525 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933093525 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933093525 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933093525 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933093525 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933093525 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933093525 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933093525 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933093525 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933093525 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933093525 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933093525 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933093525 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933093525 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933093525 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933093525 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933093525 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933093525 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933093525 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933093525 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933093525 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933093525 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933093525 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933093525 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933093525 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933093525 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933093525 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933093525 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933093525 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933093525 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933093525 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933093525 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933093525 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933093525 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933093525 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933093525 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933093525 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933093525 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933093525 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933093525 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933093525 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933093525 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933093525 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933093525 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933093525 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933093525 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933093525 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933093525 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933093525 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933093525 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933093525 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933093525 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933093525 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933093525 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933093525 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933093525 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933093525 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933093525 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933093525 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933093525 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933093525 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933093525 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933093525 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933093525 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933093525 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933093525 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933093525 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933093525 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933093525 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933093525 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933093525 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933093525 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933093525 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933093525 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933093525 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933093525 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933093525 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933093525 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933093525 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933093525 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933093525 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933093525 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933093525 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933093525 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933093525 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933093525 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933093525 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933093525 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933093525 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933093525 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933093525 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933093525 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933093525 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933093525 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933093525 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933093525 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933093525 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933093525 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933093525 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933093525 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933093525 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933093525 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933093525 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933093525 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933093525 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933093525 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933093525 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933093525 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933093525 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933093525 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933093525 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933093525 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933093525 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933093525 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933093525 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933093525 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933093525 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933093525 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933093525 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933093525 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933093525 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933093525 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 933093525 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 933093525 ≤ n) (h2 : n < 933273381) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
