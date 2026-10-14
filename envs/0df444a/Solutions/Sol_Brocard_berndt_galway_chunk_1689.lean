-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1689
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T04:14:00.99744+00:00
-- url     : https://prove2.me/submissions/b4dde336-c217-4e16-9a79-9b70d5eeca2d

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 303597122 ≤ n < 303776978 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 303598372 1250 303597122 303597131
    0x603030f130b0f040914093301120309052d01051207030b010e0f01120213050a1509270f0b0a030606090e03030601051602040b060c0a0b0a1b03 63
    0x2a00c411410a1802000b040a556941d59841e59180072150000d00c02c103c05c181c500b29411842484042d034107441541140044c3c4010310441c034000001c8070310b03040445d405150120300801a5a041c041c014041c013a694003000c41c11299140082c01e110680c2c010714000c0780c00ca50030114400c1401c083d008440c02a008003210001000c1c0101c0f1a8005c01480c03100001d0340d1414480c101e0381581c020140e4010a82c0c9450344a40100140030168030504030250003d0304101c0d1401c03046030590b001e0802086c429041c0d00070503a83e000043c1e01050650024441d540307511843e00a01e50f0041110002060955024101c8411501d814000104000c0141020075110808070720a642107510600204900401c2007001e540c403820b16000820007406440e5400d8600640390b801e604001040d04d1060505956151901032901000d01030209040b00817600940c459200103015610324011b851510340c0700c00102500400c3d82400350089001030907002c1c0c114504500c6a8188400c0b01c8820365140c81410f0104 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 303599622 1250 303598372 303598387
    0x141006111911040c0809010c0219060b15030103120f1706130908040612060b0403020f0607110924040b1c112124040209040f0609030f170603030f 64
    0x10550842603038001d83c0a03107000c2103404e0142c0c105402030b00070080d200c0200100c0008200c280d0f5980ca034090201e5203840040350400020380c080d08243e40c2450080c0c0080844200105884440e4000fa00300310385806420040c9000c0a502054442d81c1455034581030b001c1420040d0103401807075000d0100c9025003003428111a210f1075541104079800da0201170300b6615666484010300d0880c401840080480c2002000142c510031078050307506680d001040022208600404c1101035806904c00303c40605090804902c80da50306064a03100ba61140700360040d11240200d15412a040c40c1602c5220b1494500d1005042c0c0b10b410280c44101d20512a0b00140001802c11100c113450409015034040c0a6045055070351048860b440c0310b9011800880f6504110110b40100d1601241c80c401099030207080000c0151030710383e42090b00280101c0c113058a4182c983c403075409a65103241d0640c081000707094901c03000d0354071410307440c1c400400750349421181c00c121000a490703210340300150220b02004542034 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 303600872 1250 303599622 303599633
    0x1f06030506060c07031419050d080907150c060e010507020d080a0b190f060203121603021c060315090503220807081006050d050a0b04060f1410061119 66
    0x103403640f0814070f04852a642c0d6a1601070030300e482e00c41881030b1305d0054a01021580400d000e20360000d5a1000c09082c0c424840d01c011a2494070080800d012845143c400186000c00c8500d00000c4071010395411000030325600308017054803c103000d4401d4581c5803000f0403e61603804201c0c0138000c80540b40034419a03c4042422008d46412281d855201c5004805000300d0100094134070101e50444a003c00300070303074481c1c017642c0b00d020b071000d080c00c8142003800044012030800c1c281032180015080043c00c0a40e4442109104080d54404500255540606109110340209009c1281c510741400b8003040410b80d84550303c0e030150940d02200590095080c1f080301503480b1300c1c03501901c0400200e1b11800c0e42e51902c50380d240090b0098100d40c82c036050001c100c9007002c6280d014029002801403900c0030a03540c5010740c02270018419110a56140b0b11440c03031950714003840030b806070340081120035810309442c40b22120503154494401e0120340c3e071010803d07000c003003089800d19035128000c60900344a41801c = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 303602122 1250 303600872 303600877
    0x90e160909020a0302030f07031413031202030106030209120319051305180412020c1008041103030d020d05010b28140f040801180c17010b03010f0b03061f0603050606 73
    0x40250300d0b0001c2400c0c816140e05a02843c030070040814041c4254545100940466845030742100a0442d04400161061945181c1c22001d502c07d01d001a6080a0f007140502241c100780c0200001070340018002c0450b00d80b10040320140c442290117140380003450840119060700d00b5004206000000c1040d100300601405160b00a08014091030007100358800041070b0b03500d08607001c950b8200c810b0b592074000e510000340300e155018083c1038100c050304000421b07200300000800449241454031183c8004c0d0b24140041d01e0000070aa4001d0b0f00c0ba224071000c002502d40503007028041500a100b026000303c164903c0d00100f0031409600c0c507040d0041c0d81c0032640d458440c0e609802800000540301c0c00003508100520445091400070041190b04000a00b0183c0d0101006004a001d440051003699050080420341e428060000103041190201103800c0d40e45025002c200b0035903c40f902c2240c4e040520115034803d20031380000a140c2d04171103a40e0844203041c003d08041507684d0b0300040854a5583c01c = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 303603372 1250 303602122 303602129
    0x2415031109090901060e0a050106020c0105090f030703030807020111250309080312060a06030c081f0503160608010b030c0d0b011b050a030e01020a0228240f090e1609 73
    0x1622801d1525201d0f05000e81040d11a444025403480d00180554403188079441c140d888607400f6124000d203201c01107441d60007104880da070000810041c2c205541c0c04000c58070056200e40c48481e114a0b100001a08443d6500e0012a410500300075072101c403001060690101040d0540340e002400e028101220818019044084503101c00184d80500580300c2040d41e104503002c440f02620161181412401d54000210a902084074180801c022484203549403044001ca49026103043e039a410010349015030000900740001c000d10001d22409a004200602603e080020355143d0b041c11070014440e48600f0517060400f903076880341104039038400c200350350030100b85c460141c803207035014142503480b00c02d0b0780d004402080c000d2400d000c0550001c500300e40d04980042c401c01c82c482101084800c0781d5822010124442c4080724046014000075510300c44030380c3c0003400070071a005103100c0541383c8060903910005200780950100601c00108a140394440c0d01610307107050304410402c056030203000541 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 303604622 1250 303603372 303603379
    0x1507080c03070213060b0901030b030f030406030207020f033012010b120a0b0f090903070b0c0301030615151206032108060a08031204050f060a2415031109 68
    0xe00c0c42022540007001c1c0c821a4021074500e90055076140071300c0300320b80c03075403081c40d0702d020082c0602100d40d80251301c00a001d140242c00c0d1a1241402244c90f421680182c02020201e9030201c1c5090660a1000c50b0100d400015001011503900042c1210807500c7c0d541c036982003205410104030305805996094443c8481c00c1c212405182d41c44407000e1056030000c2104200a81d00d420004012150074010700308580405800b080c56440e000c01440640311000f01442143d00c0100306200c006011040128403c0c0c0200d4422130310f0b941180f4283d03050311b0241c034980c403503000d010f00207001805c00b83d6004203135800c150a080c20340006846004000d0801c0b03030b0000e060703440c02c4c84010304040704a50124024034166503070705c42076940380400c02003041000d0244034110b80c404c1c00514040741150140c0d9410901802c202c40309072440c520820b2070302600b1078021050548404082c4808c8a1004c00564566800d41014014900300091508901c050007052000c154444603c0030035580014100e402040e40034 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 303605872 1250 303604622 303604627
    0xf0424020703140a0605010e25120b0109120803010302031011030604020901180f060909050c0f070c03080705070306051e160e0a03110906060414040b060903030c0f0609070e010302150708 82
    0x3480b00c0009021b0842740310b8000c48a0800519619650340006103150040c0d484502c5804202032030400104110002c050501060444c003098074503104240310320081c4503001c1c00340c0e00d60551041c1410002040c019040541c20010300408440003281520740c403042c1650b0068546d80002c0c0100e940013200c0c042c68041040240380403030540b003202c0224060f60000d8640c8400c40b903584141100f1658125050201000e00b40007400344807000b03070020aa071354040c9100038806a1261141d03141540048821241603007c5002001000070f24081c00c1d600c031405a404208441d43e8000340d0b2034500008000080348440504070819090164040344030021000c0c0c664280561a441c00902c1c8c4418803030340510440d401c1c03000030403500c0e0080071603050b40c88440b00c235480120303000d0901000d084025032451b44841c0a224140043e1000c00c041c0c08a03540c18001000401c010401d01d90501c000503042c04155049602c090200c8003025602504681e0b040ea08c400d9000700c02a00c502560281c018003d0514000 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 303607122 1250 303605872 303605879
    0xc020114150607120203040f0605041802120415110d020705010506060412240e03090f0f060f03150d03090f09060e16090305030f0424020703140a060501 67
    0x540c030084268940c003941021548035a2859501c50100e0426154422000c001c0301002031a5201c1c80769842c6240d0046a08298403126007107120465500241e002a401103000c01841c02c0d40280c00142d4485428214038041c0d905c0c40300402810010000b03040e0b41007a6118071341c191815400701c0e030300b03410106060b6126500c59803404040c0d44031080940d80c541c200008500645041412101200c440800001c030305030040d07555440114251548400809440d046c1404819450040d001e801c0c0510300555a1594074404100ca00310100c1d4a15009a400502200503a140c050865224001c6a400680c580e0b0360780509a6003a5000b44150f40c1100c60826118101600103100c81d0650b400c00505202d1191148804001c070740d600c0c0300710f039146952000071820188421345603800c2840540761050303800d07480c1c1e00ca99165602c440705040c0c820000083c01c0261541d600c0e000240c1d2035240128288007050400002d44d9407159010241101c03070846a0010020020003000403425031000e02030045685d07 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 303608372 1250 303607122 303607127
    0x60109060f0b04080c010c030309020603010605030702160b04062304090e10050f04140a2021060403052b0501051221030603030d0f0606180617060f040c 67
    0x2880c410000e07420305612012807612004000d48041d00da071407005003c050048001150404803940059051554607040f0401584542000398040d14a9445032a56030400190080c601440141c20104810302c20805001081008044030116605031410707025480788012065400106a807620781d08540000700000c0c1c02c00a500300c681d030700000710243c031414a2031100f00d07419294100c07111010804110005400104280207280c4900303a0b0204940304220155101c101c00d00c0351409220a15199003405541443c09a09141034843c0b4a0b1146440c05055016182e561501420080c00c2c010081144005518160064001c8402d44165040c51900211604009003000c0c06640d000f110760304898182c0c20800200302044596120005030104483c248840c0e03240c00152865506000400c084041459603005400700c158640000044080c60030300c011f405040921001040d03002c0c4020704011035908402820f01083c440701c2d501100c2d5951600081101c585010303007560040c904040c0310141036 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 303609622 1250 303608372 303608381
    0xf061524170403050403060207060207050f0a0b011502070905070e0303160b0c19030e2d102702030a080301080a17090d030c11040518010f060609030320060109 70
    0x40c64481610140c901c554045110404840140c04900b08200070400203000c0d50040a0b424059000107042004540c3d5040c1450b090f00100500b50780302c2100902072003445401c650051514404020b1840c10401c1d010f074840c511446810802680d400004003414010f0400c0141d40d54000c044d03a50310b0109066940101e224130300f056680130803200018024007174030001c0310148540d03880b001100a1807400308401900d50010084030602818a810408200c46140c00e50160380d045203054664154031212031920340c14270202e440340346c20050f940103040c1101e80d0000c0500c141070387c0b08848414900101c1c0c5058802d500081240f01d00000000d034501010030300c0c0d5a4603220740d41045140d20000c2c031400b42405000886a8480b03034020b5080d0000e401014a034812a00c40c4105014040401380020b00b110710032902032502c13029440c0c0070203400b03900b889076a141e504581d10402c0b1007424490000c081905a0200805100300d5000030b80178146031018000c60420310804503421580c40b40058030160 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 303610872 1250 303609622 303609689
    0x103030206071206061409031f090204050c070209010302090c0408060c04150f0203040b0901030f0c1707020601080a0f03121d0c0f1302160f050a021201090f0615 71
    0x300d0400848541040f075000e8401142c0d03c40c0e13100c01d0865005025401e0340c0d442403050991610941d0425102911002c04050f12a2a1a94000f4040d111801480141c0314002c00d0111008001c01020380165200c440b8141502d07015500c2a0380ca0780c1c0c1c0d07a00d0310044c1c8540d4005110501c280b800700080501600000c01c144d401400d407080407040120740603139129803020801400342c0c0041c0014000d00a03181d01401040b40c05140102d240919015100c0032105132000c40f1002401c8140242e40b40c801491301140c00c03183c2071008041039850040550780752031015200030203184900301000141442000c1c80c03400f0300301880040014114580b1892503241c1c004414050500413078500304024a4107030f44103019940c024115000d034909446080000354032140107000280151110140498004a0307001c01c46480343e002880340301018010003032903065070900300c401d80e0f040c07903201c00018281e00c0071180b41c41c1c1e1081000c80c0102e400755203007004d01c1994202101d00700d108020360310098022911085c81 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 303612122 1250 303610872 303610877
    0x403051c090b07051507180801021210031101050304080702040212070e151207140c1015081b0a1d0a051f06230d090b06060415120e06010303020607 65
    0xc42d601c0c803400300c0c203004100c005846600080c18517105000000d0256501400925040500291504030301d0154403035a040700e5400c0c0e601064024000104007210fa4000c1080124005a986156500000c0d18100903001d8104840440400d041140c903905035588564002d20a548484402140c100c4002c0122000d20016940f031808402904004104000c11803002c4201490b00000d468402040310018010074100035030045c81491810f2080c0c041d0415849007000b401e4010761914004055600e01c0115018807440d8400400081800140d482001044908080644002c04d00040c100d944554001100c000004411401e100000b00d0454403502c035a070000c200c16106d10759090380445403c00e00020100c0c6c0749100344246805883c086110720700403100f0392011010030328800301d1a0400d125056141d030300d030b80d4a841000300300d40404c2e0740144141c580c907040a01c0d00000388035214800b070341c490902604290485050205401207501c44581c0c80c103c845959491a000f5075801085442a00 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 303613372 1250 303612122 303612137
    0x20d021902120a0c0605090f03041e0b04060905190e0a0e1009032f150624090d020409050d0216090c050703080703140108010f0b01050f0d110403051c 66
    0xa400303402a90f071900b9251342c580440c0c012980e202070080c0800741c04209103214410000111303500800090028001f1001741d2084500d86d9160842e1407504c0d508505660042444240181c85e8012200004c036041102c01090000c03029800100107441ba0304080659110a0704004a02d00c940d001a401000c0d0181100c904500040030310040301c1003004003d0014101c0c100c031a100d43c2d0f651640801c0d21540b42e0302c243c111000030788210f14098a050046000b03c407540f003049a1803130850840b1425400c0c8201000a000c01030340c18800c24400e4045561084203100c004100707644495014440c619030004c225021801d40c8007010b07517540310f00c80a031440c101d001c000c007203481e00039405000f8031404191244ca04064043d50140c0740d82c0401000d80081665446803009600b5810360a24002d009501c00000c020412640349010365025440312414004204a403071003a0303022408840c1e603030541041c0020309441144518100e44200c1c4e00140403071050800d880c000a400300e440c0702c583c2800352207100 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 303614622 1250 303613372 303613393
    0x5150d0b07021e1507140304050c010801121104020a020307200f0a12020108041e14060702030a0503011202030c0a17060f0103020108060f011e030914010e0d0c06020d021902 76
    0x440d80310f1004020143c0c3c01c0111a40c01e2407600701c03a4aa040005030030102c5880d00c51a010340e01d2900100d81c15555603000f518000c80d6540c204c0c5859014100f80300140c0e070506119282c41d524103c50403500350007642c0c000794424549200340705481c0c00715840038281c05a81c034007991141c003041982a020b44074501c0d82506002c68074003000040200c0b5140110107140d203600c1c0d001910140c00041c0183d500d60700b94519500c01e0000d15031480034461080f4440d002e02e40c1300307660241c5440001042c4c5001e40d40b04000c00401640c000c0d01742c030f044070b03000f0440038401400d51002c281012960000e03241c010320103004c0031400c0c03071101d004d090040040b07801f110103ea48a0000d542d0070a828400a070104160f60b004c1605802c15100500340c83c0018103050300d81c0c10303c80500c0c400c541a10304105002030794491a280130011700042183c005d21090b03009000f515004c856150301c0701c04240c4604140a44a6008003c01c2841c0d0140c1da1f84048003801103480f03007104c5515018000031001800300501034803e404 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 303615872 1250 303614622 303614653
    0x2071805060907020c1c020d15051501230309070801060602060103050f07230415080d02011b0e061308070909050c03070e0a020c0705090408091f0503070305150d0b0702 74
    0x4440c80f40c00500c01106d10444814005800341819400e81e000080c07540030300003003100101c2200108030316040000701460150501c00f0317101540c90405042200c401c1c00a824039030f190b580d40310100242405984e0326105c403000c3c145428134541c0120f0345942400c0d00052842d0300459224103ca0081e0165915095007416182d1a61014080d10100c601814040ea030a000101540c1c0410320028100107945400074007940c80400041c5d02c101e007180d10401041c0c0b545036080c010811419800c40b4148141d490717181001d000201031045850240101203101d00d0307001b0182c1c41c20001002e500003a5a460768442c50703004060199861b0603101480b0750b207200007207801c001400104448402080c00401d4443c250420080d500c00c030020350301c03407050740e1000c15143d6915801d240214030800e00159a01004030600040555810105001b100c1c08002324036560742050841c1d901200a2070002125034585d034400440c0070708403032926000714150b81c1c900c1c200204441482e00444080d0201c80c2484001585c0 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 303617122 1250 303615872 303615883
    0x3060411031e030f07050a061a0a050307180e100603080301031709091506070b010f080114040503030a0b01110a03020106030606050303130308030705091302071a06060a08070207180506090702 84
    0xc0b00c5198420014024801880c10240803110710aa054485130005600c2d204199040300d45416640c00b95000ba41b4160b00e8000b148000400e029406002d90515050108418601070b44070300c02d10740d484030000460f02d41c0900000e420024414000c002d496180e091185080d0000d010403240c14860b42001d1074901180c000303840c0343c0c010051080c111951481c8070300c0c900400b4a4041a0080c20500c01c90380020308514031a80680101402c00032002d280c001d5043c03d44a0344000b0601e007644c90b0060102099000c4210b030341c0010811000304900c00b00c040120f0f4603d00000848080d0700446800d00101907064002d4011070740a090184903858030303001019103070701c6002c5075078020f10301c0008108000b03400b500186a01000905003e030a102104011400743e801b0600c400e000c46a0019280c4104461501c45607482465201e0021a62030644041480385c410800c10a090114200000c3c030000d01c200048805003200d1250180401460066a0081d1100381c41d06881780e000c00e800201603c3c40001d5 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 303618372 1250 303617122 303617173
    0xd0315030209060d020a170c0a0506040e070302030907260c0f100311090301050403180b07020a0302060d0b040f0608010e0a170a03060b1602100c111e0306041103 71
    0x2e400d01c2c0d82c4841080011078454090308a801010041d400075081c040800c2e402d0500031600302074610307009200e0401040011540240348102014802441000342c0701000507440751023820700507541d84440100b0ba00c1c1064540c0402900454506803000c03071400c961810b4142c1c000305d0b089411481003030781040355110301d0150541e08402014107040042d48030740c2100201d03c03510200b0510b40802c20700421b00391841194150049803441e03001030a00b201d10640b0b0402000030401c4181840ba0950010701d00390303014840603228610200300d0007804519544501034000004000300841032030b4143c0d05014015501c1400300c29480c000425032580404620401d5040d4001c0019005d901e8410b00c05c403054000072000300415541d8000411404442c00040500e51100e04480501c8010352041010500c9001c1a607802c2140488e095400a0340038a03592884010855005020708441001440d80030017107421140d2604c20a404d200c14090a480504001c500039001e0f1145c2498400d02030034400e59849 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 303619622 1250 303618372 303618379
    0x90f0f050108120d150f050a08010b010507120e04050103030914010e061204051501030c030c210809010309061803020f061603051503030a0921030c060507050c0f0d03150302 76
    0x522242080c4003240041403c2c290759440003410b50000c0c44039051015658101b105414004642803040d480c1c4841400c00921907500288055051040001c2c031034042c012006040314501c0c0a124030b03682c002e00e20b0076200100584100700b1507a60741070080074001c00f403082e49d41d8040040c0c20465035501c502c0b80340803d040c0c081c05051401030511845001810018400d44e0940900350541565008a034000d5008500644103001040d081d4209003002426562104c50310341002a44809608582e4091410098120703040303949500204006030041c05075541e00030220f51811f001070301da800c0144031a0740b1140c000c2d403c07122900040c040041d5034000c1600d0710107400d030086621604540c803a030421075004401000002810215601280c40c43d00954049004961000001d020340c11100a400000e0f415030940140d003400301c1d403809000f501076036001605441e00d80000500f014028012170300d0710241c60307046401010310600b015031600d07418000d2400080c100f00500803420f203100c5100096a8005 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 303620872 1250 303619622 303619633
    0x50a0f0506070602090d030804050c09040209071805040606180503030a080411061c020d150b1e04030206160b062b050a0b0901060611010e0c0d030306050406090f0f050108 75
    0x41045400e41051038200c030f0081e020007045219848245107044d10310f219840d806024141032903ca42042d500c2810140641420420800903030350f40f1080d190032100d1800c00744044404a052855074000c2900aa600035050204c0010320f16030241da40360001da41e41a20943e1140c0314000c040d2a07225a1078043c00290240c8085000314035190031201200500030701a6280091040d0841600860441d050850590100710040c40d802540200240400801c920b400b0090422105240c940511010307844810a10700005040091303210460b0090b5800070202c549030070f1600b00c0c41c07403004039a503c00c613404e400482c00f20301981411036606003140a1030a14104840450514800003080c2c1d0b4400e840c06e100b2402c4c00400308882d0401d03240204400e000101d0040e0501e600540300600b0390761420b0b440d80c0752070a0024800800b049200c24580100c030b501c90b01d04050304040700541100d0b000580c0c4a45484000640120246c1c458005010701400138410b20700c42230070000489000344100d6003541c01c507 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 303622122 1250 303620872 303620879
    0x90f02130317090a0906030b0a0c0212130e0c031909050c1318050d0f0e06040509040201090f080601051e010c17040e0c04170319200124050a0f 63
    0x200da03528484400c041c2e0344107081c89510000034400180e242d0100c01900c1e41c0310b0007481840042c90069070f002c0703002141071055052141000f503444040600c500d03040300c0f02017050401c00300700074605401840c0244034201c2c0c0341440d4000300800d40c41070301d0041140324180c0207a10030a24034024205006c0d00507001d040c5425080b400d1142c2000c3d2078070f0700000155964480c491f0441044850a1814028401403a0358030745c5050242200c0302c440b0380361080c04582c00044075940c1c1d601d000c0b00c056a8080c0d03207034040c54035284016240d0395590f80044e81141e400c800c0c08950724500080c054126401162081c0da041400450a00010002114240041c0c01c074005140818480300030101c2c20700000f84c05526103a5190214215041306407001210007400013400c1115064801c809401c3c11141c0c405186000104104454482a00304000c070510841c481d01104051034418100b500b50b604400038014a0450900412911050041c0c0c0c042c2100c0c5400c04102401c140c03115a0903076000c00040030b4110304 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 303623372 1250 303622122 303622133
    0x23408120c0405060c100f02090a090914060f0405120c060403080705040f030b041101050301080a030c03021c0804020312031b0d110c030a03060806070503010e040201030f0e07090f021303 82
    0x14510380d4210020440050f4944034000144200762611006d01500070a071300501098865070780c01324540900500c55800d00e940d1b403206d6481141c2c0c00c14000103d400300d919160303e1051007075010341c21703d0164000300300100f0850845644118451030591340070081d041501da165001d03550510384540e024000050009003c1d14040c0d4002802e8141141400e6032503250803040f032866001220700401c0481404108a114104020902d40c01d09009003158103028166a5407440b862001c0d04014400003410306143c02800000c4010032002d54040200000f4140500010001d4508030700071700c205400d83c040201003200b62400341030005401c8181c008050303074100c61600301603881014a551400c85001a4080000402044900001450301c0b2641ca40d03000d01240c185a0118805821a404100c02c042d4000116815115030801c048116180c0f400102c0c0249849000040c00070301c1c001e48a20000000144001225107103241800709440d1001410b083c0d00481104078815025608240005036 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 303624622 1250 303623372 303623407
    0x100f08070b03060f0f130c02010b030123130206040b0a11060f01090c140309250302060906160b09061909020916020a1a040c051c0b0a020409023408 65
    0x10014a0401100403e81c0099401c86e042d01c0b501d41e0103a0754044d80603400d50203015807e03403071004500070401925080c43c0c074880441d00d00d4940c8a420070300c0d00021087c1005121883d4882d4014040540b41c0d0f03101e0a5003070565208484000200d82855900400000002505e91080342d0117441d00816034600807000025102c0411040c052080f0500711004141d0200c02a6105800344c200815190265025154a001807000d08024815071400144050b07150340e4111001d40509a13240342c0d6403a254120210703030b10310110008050103800e800b4000302820001c2c01e280102040d1145100104640410b001160310200c0002c3d044030000c0009140000403041e240c1000395140140d4140c80700e6565213020310081249443d060001d401d0600082c003001414501c0603103026202811415961a00c550f0380c08814580100081101d00000c0c800e14203a4060714001d008840003903440704000c60500702001111301e001140f10816510002401080c18040b03915150003000c224a04022b02e0425009403 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 303625872 1250 303624622 303624649
    0x131401091a0d090809090c0406050a0e01051611011b110405130c0306060305160b0d0c180807050910030305040b0304030509100c02040630020f03010203100f08070b0306 74
    0x81d030341400240d071401c1240c09406202d031321841c2070079503500f18117003000b60321140036104c074480c42400d2005100c0d9540150450f80c4414082c10500307100c2d2000d90048130144108841e442900342d5000c030000801141ea4040c0401c51002d89540c0c290b00100810014180841d600285c200c0c4800f0314105c2c4181003540c0091b403c041300014803100c1d14816100c000e104015a4011922540e0761441041444024000b095212805000801445282c0005003085004032402a00c07100c0c0d0f40d07542007001c940a6490292800c944003210f43c0392641e50907080d5241e1085100b10f50040c0e0750640011818810f1a20200c01e13a07501d43c407140d081c02d0070254101c5598200a004800344101000f003c3c1c07096454a4000403a12070958546540460600c1803100390303001e0b030340701d5083c04d003d10440c0c000409171038250804040301c584080320f0340007141c00000d44003014004180e070076500c00030511400070103580030342080d1950300c00c1d00c105141e514880301c0d580e8845449500c590326801d002081c01881d0410910021 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 303627122 1250 303625872 303625919
    0xd0f0e0c0d0b0a240911070804170c030105010603020d0b0604060503010b0a031404060501082b0f05043b060d060b120d05030610090f060c05100204090213140109 71
    0x1c0400c2c0d00c83d485408459412880700094036104c00c0100d00410f018044140d55024a200d080a48540d030b45000b43c0680e00807040000c80f01c0307279250091002007114401444c8010000c0c8540d59540320040c0017075100e81c00880a550410300c032002c05080400460f0215001c41e503503589584e180141c1e1000c19000040d04804158503020000000040e000c04507024500455001a107035145c00d0603945443e100b1031142d180c1c0c024200c0044403803001c1e6140909408014100181c82c02007145048409102d0380d000184010400500d0442c03944c200312500100750310320300d841c42080840c060007000c0c0000407218188d2054030b051100b800602a500031724000f96020303040745895552000c100341407007031503125607001400c0030040011038503018000c1c9203052041e0600d0080181829512801d42085002d0340003030001c00c2c0480c0c4100082001801e2b9030b440940001c54507a030b21001604003075401541c0e84000320328080d00100d440c200302510a160654141c66076041c4910b049a020161080d41d10800709 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 303628372 1250 303627122 303627131
    0x170114030313090b3303150904200306090714041d01150f030b060402030915040302030306010f080c1b071a091002120d0b0a03080d0f0e0c0d0b0a 64
    0x1000300c00026040c0580780c010404139161942c5018858068400143c020341401c00d00300d41211880800760904014040c0304295950307580d4860f008485d5001d501c400743c1c00011030803c00090140b02019480380901c100c1d40c0c02e45e41c403040420940c0c0c6140946214400d9080b0100400c42d00e07840f031200790081d200241011460a002e08507080d420212585420311607516584084400b070780c151144405800c0010720008518215111100210001400113000d254000f0205010080800030280d801e4060074415145140502d0000d480760000c2d0b60042c041880c0e1482802120301801d41c5601c07590340041070360705105c940c101c001c00051110b50172109074010b0b6100415007015501c60124279814a00750a507031184000c1c02e12900160041d448011508040c102c6c9a82c10398100c121000040c0980011400b070f680c01001507126030305544003c05500c0c0006d51040008002d0304906e1003403a03180d4081290b84000c40d4010b132219500d48000d5032142500c018400065400291941c01c102d182d4000074 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 303629622 1250 303628372 303628387
    0x70f1706160e0d030e0108012106021b0d02031e1603080612100e100b0307180f06090902040b0a0b0a14040b070807020a1202090a050606121503010c1701140303 70
    0x403243e40b880003080e4002002c48866100c06e50300312100d6030043c50b0b901c030b60341c11602c0510038050003503a040c0001096180c0000d0384c1c00d010481c2da080790007200184420744080a4640700c01a40c0c030b80c840c40045030a0501c1080222610884000b903c40080c9070219681d0903c1d110b40e4200e80f1001c00608059100381c19555651580408010f80c40a10b8480f80c8002068030310154128a0000040c465900c2c46041a0070301005850121700102201d600c1451a0380380000c0c4d82c80000540381f0705001100507441c100c400244024240c02c007030341241c025581003003103040704030900c01c01074028090130460803010444c2052580c403402c03004034414140c0b042181859180c0590341c60a40c8000c00a543d20035001c0385120542c41d0884100380140381007102410102529400f01d03140410061944c6580d030b81d5100003822584401c011a10202042a142c9441d4640060048221703000c0e084d64074040d611f401070001c0260f0003003007080341c5401007400d800500c2c1e103090b0310000890742034418281c05010a01114 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 303630872 1250 303629622 303629629
    0x60604020d0207140d09081f05091906050f0f04020a0e0604020c060408090306010816090f1b03050901060603090308040f03090308031006140a0f0e0f12070f1706160e 73
    0x10100c0c4c591340809040030101d00320005250340f5250300601c4d25034110b007142048081c843c030040c2d041502d02520214040c3d884014a608001100780c120800c21035442003203003004025030000b40f0840448501051586410201c83ca445a00302d40094000485c417406000ca0041c141d1703c07a9002500030300c0503280c40c54015240d41020415a0300f10b40e103a80100710003155207020b02c2101e024005910060100042801e0b021403e155103100d2030400b00d0743c0340b00910035003e003070700074030340c00400700d2550003040d40315080050040c0000c98110314654039004020a815101c1e001c0c143c003168040d81c0702c2d110340e01d441d00c4400303a0200070380d021800d11211500000010781e2a00c06144034030a52820884440d2411202401d2035089240e540302c0905c0410108089681108501c03000c41c1842c0b90005820140b40041543d0b01400302c00181c3c01801d43d1401d00d4240400158241603a03654605a0a61641c9030012102980644660a440e402c004c1c00907596020441d0b55907031030b460519100c158425110080b = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 303632122 1250 303630872 303630893
    0x30a1a0604141008060319020103140c19020705061c09060c02030d0501060206071403070e04020d06091404020a0b0c1213091803080a02090a03050102040909030f05040503060604020d0207 82
    0x100b40c04180c1c0001e41e400d0301c2e040305581080201402c01c400c007481e141c00007a4590440344000002c00d48020050425a4400e500c02c1020b40c20100c41c9140e141031208105c4c0303040c0c0000c0466000c580d00442034010152002c0b83e41c0e001c0710000360416040500001860320074040c01502044415a10441d21001c03a00d240181a89008180c000c0c41d903910318500c0b80c00968005030040f10035035021100344420103520045a10400c40c16007d119203a4a8000e8110b400900080039070344e100d8004124000d9040b0716a012344200c40181d00c00b001302070040b4420f050240d50403103000e50b1000e60541c0c100545007100006112002d0190b00f6925a0320200c4a07010494008035800170346408903140500841c10f8510031811a860f000310304520300030306668000d02d440030052203003c01036000301d174001040e1a40785000c40a140d1000007991a036894036924801082240015000034a050101a40c3e9234061400c41e4192240600030300f401e690b44000b40b0000c1e42c0000703504038205d90308225003004598030548 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 303633372 1250 303632122 303632129
    0x14090402070b060a140102060112030c0507081609060f0501031d07061701060c0f0809190306050f07090303020d030207150e07290d1d0607050a09090b0105030a1a0604 73
    0x400b08450800000f800038a90183d04151080c10a8010070704245c0e0300080c00904544400900c811074079010b10f011242c000e66043e0003800b07485400008503800b0f1012480040e0b4917281300811307a203240d1351154181075030741600c503294083c4413801c0207000b03d510a4200f00070303804c0743c0105844428041490185030201540c09031001450340c060420130000b51300d12441c010046032900c5100703554103441d022500b03012513a00902e00000003a1104242d103404000714080c0186121841c0342c0f55990400350003030013046604c10064092000002e04250080755a282502c1d0990700408810403134040a800035071042a00340c5448031211a0009021058003d00c2c040184e004013520003a80340500000000c1c0fa185113002c20700b0720680707940c5058444071342510440d40001801040301d4051030300030001291004513840250046c00704002080b40c1110040c0640d0400796104648107590b4054041110b0302a40c80ea0300194007000840c06210083e00490f0001b070710348a850301d42040030000160319521552 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 303634622 1250 303633372 303633383
    0x5100501050406060f1209021f050d0e0a030c06051510050901080726040c030203190b0f07051815160b0c070203030405060d0e060709080d031a011409040207 69
    0x1401400359041034080c603c010400350038040081001d1400141c89012a900c5020880e91383d00c6d0200c00355651540160042d10300583c03a240161545000103102307602c410380140c2c51a00b4031035900003a0303c00080c1e4410071505940c81402c401260358604000c1c00026000c58140903a10710303041155640d143c410f10301c0030401d44415980c0c01c0c45600240800c2d00062007070060000104d08024503880c050000d40e010740e540d001b800d1031542c5614010f02e2514040e00040e4049c070841e00f801000310303091604440e07918003448204100b07941d24440da40078510110380000001b141802408941060442c8400c0310200c001c1c55044243c00d44824400d042d0040b40d080031441601c4080542846511000c142d00700e103410b00c0311450310300d040e00480da9a1285d44a0240620400520520046140e90154145200c2d0000b0740d505030a043c08010014540c034041c4038a5400b40780107400c003a501038850188214814444007120000f81e000645e185200200c114801400c100440c1c1d102da555807004003403091081 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 303635872 1250 303634622 303634631
    0x80d0e1002120901050a020a0602041e210311251706090a0813030b01090f0507020102122d0f072304090c0e030102070c0302040c0201061a13030510 65
    0x240104442140d00c0400340007590465200364820224040440d1a11902030038140d0b500c03040c80800300c1c580341174500c002d40590701c08203010610030780c5c40a03020b04d10180321521010036511038040920f0201103071140c41d800c0c0758560300940001e0041d42c00c3da0f031040d42082552840014980441c00c0140e001d200003201d224510801e000f02c3e00403040142200c2e013104014079051605500740c07a0b81d209c2d0024041d1880f00046a500010130722000c411000d1039010710320300046d50750395410902402c034114549083e1401c1100203030b0024030501c00d4444111004000b0403c0b600c800d61020034080e5803d40c14080d07413030885010421041100c2150380240a007074030501141c07034400e400030007601801022044d03000b85400c1c3c40790240c8c8060300ba641504c401c00400260f10040e82c00c1662a4003900102c00e4155001162140c01e008800044c402100e0003618180138884220707504908070b68407400750b0b02042c68111501d002c42c903440000b03040c401c13601d08402c0b03030b4081d00ca03280d0504d41402540701900c0680c94 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 303637122 1250 303635872 303635897
    0x15060102010507030c0e0607080c0f01090302070b0304020f1e1206090c06070215030a0b0a03030e040b0a080d08060d050109050618070b040e040f02221a091906080d 72
    0x920030a0f42c080504c0c6000c001201880c240203060034a40445507114003c0031071000c00307000100b4115690007200c002102d243c55a90400503028020211040c2c000d80070b11600019800b03009000c0344e200b19802041042c25800c405c0800c0300203d40d00000180c1e0038440d00d81003000c0c0c0c84001100b5004d1012000034019894a2000726113020801d4600c6402410248900b00060b02c420410b294001441e107165604c0c2d0760f80d00440070040c100742c0d07000c40c1d008075401000802e060b000000850050702c152018012050a0070a0015103000c40c4940f425640c0055503141c1c0c0e00384129110780c4c1002e80100709981040803921481d0070340e40c9101c0c4c261081e800c02d506200c208551000720b21015407920001c2c2c08054601010503240303004610035404c2c01d911030300002d0300308012807452400c2c03168000d281c0401154400c80c000c084020740d0b480c41c007280b481c101074000c0406901c288444500f0000b01001a6a6a1003900b91070070300c0401c26501841c0d8642c207021801781d105022014090748140c1c0c40300d042042 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 303638372 1250 303637122 303637127
    0x605070203060903040e04230a060203071101090c050409033606020a0209010306050403120e010e0c040605090103020607021212071110020a03050f0708030108100c0206070207091805150601 83
    0x80243c9441c040b64000c104c01c0200d1011a5503640e03109810081e01c2074544941d030801000742248600820590107405407400400c140c6501460007400e040e0b40340c0123020381c0e0001c0f4034222101c0c0f010141180003002c004200c54030341798001030301d220301c03174a4650501c0000411800000f40c5e6641c18050000c131103c02007a019804007812401004c1501c000e04c1e07001100e402050f0312140c1800064440c64445d0300107410705004102c05106440760500c1080140f40c0000114028003080d2020700c01805012084045c0f494180118015228002e110b812142d185908121196010031070403a04840d00c01c48960f9580818005412002200c0b0900f236034580c4e051174401c84c1d02181205052040e480c10154020b5aa400100b06882075450b00f0026520519204801d4a038010300034001c0c600c41e000000410f106e8004244603142c03841026041c0030060a90070181c0c5c40e03070001c86d481d00c01a0301030742c4104095505d6801203050240715019103186015181c407014100001c0500c4408a05466000d104003940d = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 303639622 1250 303638372 303638383
    0x606121207050102071101050703050418060b0a020a02090105300708070303120b09090c0d1e050f06010e04080a12090212030318010612060930030c050415110a06060605070203 77
    0x20b005d19042e40789c0240c3c2d507070140c180e0080d800f4a1034503041c044441e665255180d8003038005010500500b9494005480c4000c0d03444c1a140c000300d001d00e4010340001420b00b420303030008001d0192078843c410030b88090300c004000d810301d4141e4002d461007402c00000350000306018110286000b039036049150001900c0e08800c1d600c10a4041d406154107104114400b00042004280303180f044a0381c10a13003115050088810000d80d100550070325a50940008018002441c03020700f40045d000d882e426039982e02e010030040011640504005004c02c200c800062081c242c010072541c1e09540040c82d41426004120b030407940100c1c1d02c1341a40000240403000e02e42d1100348139054580c000034441c190400004460304000560020101c680700d08081003040741440010141c02d031510070000c01d0b698a00201441820b03807002040100b80f4040030002960710440c1201c2c2585c1c0005c02482d0342c0200200100c8642d4804140b49001c0d0155401c0c00300003038203e01482e0300074855692443e40302c102c14010541045e = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 303640872 1250 303639622 303639653
    0x270a0510080f060f01120f060902030a06050108010905161107080a060c020105130c05040c0c0501020f120f1b0d020c15070306120b07080405072c0a0e060612120705010207 75
    0x1280c42c4c84461486031ba2050004001607403012010400781840008140681019008a80c040d030002c802c000c0039907600e50054003114803d07a00c4010700d0b41d0ba12942c0040354001c1c0c54110320040707034100b040038503070040801c1603400d400c41c0126503081e5940c0180c1070501c41c0040003200c0c590f440c0da402d0310303003107909015880e000350000201d26203c00e60760342c0da404d03036031454425a40900d0300d5544981610380a860b01070403064004009560303405002c90b03007280c10303070141e43d03503400042c1c4410114401e1111003001380e00c00c0d10003102c00070303e003680380c0c54100701074001c034000c0150280c00b00903d030400319017409182201503180c0340d001d400f03081810000c1c050340d0840e0021038140100034100408202d464114542001c907604290f10240c480342090703421b200c0c03190081808054a4001d150503000901c40c90b000355100001001025140c1c000c203541030b100240d9002d00558880c0000c100b052a002003046440d240071012102e042030321040c100c1580d00000340070345203a58041201c40511403800d1500c03650 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 303642122 1250 303640872 303640879
    0x140703020c012d03110405030102130f060516030e060d020c07051513053a0312050f0a0c030225051204051c02011803150b0105270a0510080f06 63
    0x10b10f0120100c281500140d01c0c08001c045d240c08200300104203210031100503010140c0290361300c4102c5a80306034810f10601c510300080f407500c0b4001880c18822001e41c0c0080c040e6840c010400145c64a0444100c225405450343c8a1001c018030303506101284000e00360010700b0405403101614003010410100381003803c00804620800c8401806074802c000281964001c44118044440c5036529071280003068500ca00c46054044070001c1c00800b58900d030038194440c1d0780d14078001c1401c90b412801c1d1501690b5142582041c3c201042d481c2d20b507038014441c014003519005060850000c080075007894441c108040602900b103120040c081c1c14400c4161282c0c2e4a203402d458503140401184c40c48404100d402c61149503400b5482c00c5a100d0071044840c1e0b07049481e0409115140e00700031020200e211290424286400c0d10741586500400580358894000d11412028072100350440141e49509030b03090707034440d602070404504c60382c80f1003101d00c906580350768110700d915141c1e90702540b0440140a20b0310 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 303643372 1250 303642122 303642167
    0x25020f03030c0a0308101707090b0d081206011101060f030515010302030c010f03090b1801140114011b05010903270509010308070302150c0a020114060a05060307140703020c01 77
    0x52100000503c01c0f01140c0c5490282080e968241c04240440f249402c000464202501001104035001485070147e40b039000042204581e01410064840040d20001742003100500c0103840c0200b089840070b41c0400103042003c02c0400c2c0d80d800c242191a02c5c2c101d207100d504107850034070500100b00f107881503817003001e50008030075411500005d40d00c144a0740c005042001c0e410600d0700e032901c20380001008640c8500c2c569800d0070000d001200820346c00300203801a41c40e140b100700c00101c960101c070b4100c4040e030119415241c0e9103001180c400b024ad146000d0010711068194000690904c01e40d0340140c041c1e6200d002e00000761000310180d0780000652a41001c480b401401196152003856045991000490b5510020303031806034140300784038140e040c0311080380c0300700312203138202c04c00603c0b441c000390b80208400e0251a00e030b0101c1a4064820a41000d03c115003072100f42061001150080c840e820000d44200341e40b06141300d281d102c40c004400507040707a55401404d5030400b68503820040d05409502c03 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 303644622 1250 303643372 303643387
    0x709151d0d0309060906090f09091e2415152a170403030905040c0e0d0506010905090f070311120706120b0f0603040219050a0902030f09060403051b0325020f0303 71
    0x1007401343c1c03030183e890712a034ac2e1841e0308204081c5007146442a41c012441d0071020220f4204000540305404912821240581ca00c0c0725442d580d00c0b400400c45040180b400c0060700b04a58078034000c8000c0c1d00d000c00d2181c0e604202c0012a80300024242c034130301c0541a8545403c452030040c54800c1c8050404001c0c0701c05100a00000b03822a0010050310029203000415010146d404c4680101c200082c80e00318070a4a010420301c0310100c0e00394141c8034900000d201588400d00503036599400b140300301219401081e070620002d60174125804038100014482c076540d00c0940d68060034100b2940c002004159444000c03400304071a0301612a01603000c0383d200c50041d0742000411801c1c8401080244603003508101c5103500020220002c010740000341505151036203480c507080003540142c4515640c1c0e41004001441d10000066640c81b466050b03a415052443c40e8840c24505009a003500035030f80420b024ee07480108400300d0f44043d41c520540c40200001540c0140f00186216000d414041d410400440c1c = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 303645872 1250 303644622 303644639
    0x61e0909051c0e06040303200d200f01050c04081b0913021311091c0f120509131b0e0a14041d03120709151d0d030906090609 55
    0x102400600c0c1804039401c0d1001d000300f00c07004450200550341c490000b240100c103265004040c40c81034610305001c0544ea540074100243c5d030300809125280014003911285900d50320358040350030354023015421504a2940181c120303081da41c00302c901017910f20001c0340802c01c0e124200442d540011440f60101600303011a00415800407005220880b07452803400c0080454849212010b642500003038200000210101419031340d07072110701d219218190581a89141112501d0440c10450740f141000c80320960654a4021450181650300c007481020701c00703803050f5110140f880c0445007070f40d1800114800020300440220f0726140b0f00e041001f0540300810b4080d01c4180c03201050303e00c1001405030300301c1c1031000039000c0d00e0381042e29a40000140d08200241400002800e038010304029011290790718001c003250440c40078072030b0705100001104202000c40c02108100c010a004000303854031252034901041c04d0210b540c80440004070018002c000c803076405108207000c0c0a0505c0d04002c0300e407601c10030 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 303647122 1250 303645872 303645883
    0x20307020304090b0f030a120e0f060301050d0519080304020a060f09180f110306100c112718060a0608070302060906090a03050d0305070c050a030c02030709061e090905 74
    0xe03c0100341e580d00c000f040c40d1340c1e680ea0034001c031900182200c9000c05103207000d01020380c6066550012405c0300181d0788a074a001408208030140191006046a01c0c000c01c022510000349016901805900e400505016414681e5a030b1203018551a65407401c0038130502c04031403400d50080003042196111002800e42c0444c2c0c20003102c4201c0881001d40704d40f0800303100106400c115220b841850808104100030070403016610800742141d0f0307280011082d0105030340b00100d10200600a05040780c20254a2904100034001c035004202019040e8140d14100800f0301741c1034503441e12080c1411011140c0c80c4040100320342c003994141c4244000c91a0241256071100c090100a101d064007040d4100c039501d66100741e682104c0010010310509030b680c20069161705000c135403200024146400200e110f4011815002d178558413000510481b1060b8400f103a4046009504a0381030141d038600041c20403c45c00707038001400c00340c0b4400758450b14150031030048104603840f00d0300303850a10287d42c0200d00003080 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 303648372 1250 303647122 303647129
    0x40e060906030a0308060111010c0903021005040506120c040b070b04020405060312040608090c0a0f090e06040809043c2a08090a05070e0a20041a0702060703020d0f03020307020304 79
    0x5d003e14a41c94120050700c14610000c40c010080d0f20707101c041840d503903001944208a90081c2e03038103e01d07036405070000c503000e108a00520741c10410410041030b4030703a9480c440591244440681c541043c1d00c80e45081169072204c44240c2d20168444180700643c5000e04c02d098110350f08900400a0100d241c1c40c0c06014096031040000f404030001c000b600e004424407480854580062a4000303042e101d2440a203c5600c6000c4c030310030146420613284071624002962400345410180d0343d41441100c00030040502801e844d8220320303a050340074800741e00d101905040a40031802c240d108100120a1691085962114031071070480114561400e075111203a9105419401600d4004e442e555024200d03443c004491f9030042c120b2003208400103006082c42c03096801801d805409002c0c000d009020131940d010035400011080400300000c01200c91020789519614000c900841d08098154002030b060b504122801e40141c0c1015a4001000d5407001c45905001c8407420114254109050004d540e8017a030b00 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 303649622 1250 303648372 303648377
    0x108100e130c1214070602010e031c0b130222051003020c0a0506040f03090b210a09020405040503180114070318030605070314010512060f04080705030c03040e060906030a03 76
    0x100300c905120508480782c0c003418480b4803007000400d292030030841c000c5080c6a6002c05000c3e180700419081e1060007100d03c80807003040294103204180110325907a2440421030602142d445004e048241c440380101c650300700b079080300180c84000c01c560003580100c0e66007001c000c81103541c03820720080d503652003a9000c0103039034500140c4451481140c00d10b4500b807032402500c5481240100801c02041903500d4403075030300c280e440008540e078600c58140a4094019003801e000c400b411002c02e0401c808040a900043d03400b03004c580303051030b500480c0480f682a9400e5505403c0051091401c41024107165645042031030840700904250610f903409000318a0000c1c104496140c0804080d00351a400c44040c580040c8100a1400c000c2c2c4081e00030404560110300440c0620000682c1d46010459104604c440c01d01502c1c090f80d81c00e103407503c0224000c1080300d0100080c000c0784041002040900309601000004542d12070620469000101c00240030f14460402e650400585880100d080102641c0c1030 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 303650872 1250 303649622 303649651
    0x9122a03050d020d1d010f14010b0304021002210403020f0f01080f10030818090709060c38311401110a0c110904030f18030804140108100e 61
    0x101078000280c10b06605d800720a60b01404075001d840410740c0054020410801d0400c20809040c01c01921150240b044100b8041c0500020303007d0f0500c0c041e64420045984151050200034805031600d001000303510400000c0c1c08075091085080c4412035240d20041102c000051182500000f44141401407203401a280d0031404511819080d84020b4055907102c0107094891042c0301030082150301030f100c0544180d6000d404600c825024175a00d1043e5620303a600d21102c1030464880c284840724000b030781c2d9408e440d4001d40c8040c0141844d42c00720742010b2400780746e145007416a4941404940b41200341260100050f035004a151040212100540e010500c2103240304560354003401000b6221107001c2e07204000400715103196021000041c050701c20414060006541410300ca14004221002004507aa140200c002140140d41003443c46603135141c01e401080d100da6400000c0d801907400000b039480d50a0120350b5540c0c100981315449010720120010700c900d4802c51070f40000c00070740100d0742c00400 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 303652122 1250 303650872 303650887
    0x30c03011205030c0a03030506040b0a0b09010e0109050306130308071407030e01020a0b0411101b030806030f01060b090906010513030b07050903030301081005180c06030a09122a03050d02 82
    0x14420341e074901d131102040c0c03114100e0505020740900300480e0b21510451500224110515248844005407000400d4003400c250000b40191184c0d44851035181c1401464a07000987d682d0420020380b007001205803a00c50103499103806068140302a00e1039003030107240110404031520306000d6404554051802c0000e40c1030210050303003800c038100030190656840100b00803d0101400d0340601c081e005a420400b0518040310032a4110240c110444052a507081d403000400e1041d1019600500010207a81480c0c1150203c1070848103d0790140401c06d0010824000300d00d07102510650081003802d2051a1074000281c050b61340c103850200034900d01c203c0c004140010b01c50020b45420503170160490740c0e20751b11400d640399140d0035407481c40191401d00b40082c0003103107180007a0720740d08409002001600041c0c1c04002107604020030041615660344045000724035100086030700030703a0f02e44070704400107201c0002000c142c0708040d4055481e014020036900090303002d411a560400071140040e03c1d00380c03 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 303653372 1250 303652122 303652133
    0x603090102090f013f051008060108070303080115020705090411010201110406051e0c010e0102090a090209060a120f0504030806010e0a141c06020301030507061d06031504091223030c030112 83
    0x19410301c85d041c0c143c41d100c10013148a40102480050799108422104960f80e1080c0c203c0e40c1c2c0e0000d000003400104c41c28010409070302502c50320094080240103845001e9103036408544c200504032000da0354100c540c6202e0300c0301e50f028421540d64400c2480150719250070301ea0081c1ca14403403400c80d00c1c8020a00c035881c0c0b2480781401f069640f6164268028400384076a000c41034040e4100b142e15034407548100358002200000c9200b01c41380082c019140e141400d8502e40140c85407008010000c00300e5447d420340c441e400720305205042c81203101e91070b031849a0802000060891005040f0030740200c400e00b506000310780d00103004044118013120304980d00c1e4441d819031612200807032402080c050003c40003004112010032400700341c0c0c500b80d441204840c0610440240c24511010207034002c1c10800204480459031a245d4820500241000c035141e4025603455160900c40411400059950380800f260040c07c420804100801010302e5421030501100040040c071044c41050562400169000c08120 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 303654622 1250 303653372 303653477
    0x60d0b09120f0a0207090903091806031707050f01270c030203010e060601080a1a090604090c03032f060c1e04080106141002070501110c0603090102090f01 68
    0x20000c4045a01e07400002e4030200d031500034402d4000135008065012070714101500c14080c00c0ba4050ba030f03215106103480104407100411000c03e181c09a150f0201001040c80d46000c4c24002c864000160782d076003400c0c2085400c000490511008690500890070600031241040c03011050190703c000144100324501048030600c02d0344000d405509262504541e400d0110341288940710070b88403038600d0340e60340d80004c080701d00101e21861004102212074601b41401700041e40c0c030000107000040c0d0040241c9441c400c41c101e5a00c2100010440700f1b07507400c029142d05401074840440a00c80341405116000c00ea02d9240080c5a5418100c01017002c11411200c807821030311001c0d1400784941d03100d0711001038034007801007402903040a48246904110900b40011105140702d05e5a02401100b0b081800441e40702c00c5a4003540140d00c1003080a40c001d541303c1d002140030b4884c6000050391141000d050011442c1800106414012202201d5080d4900908025151007031a0110700218011000c15141c1c1d0 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 303655872 1250 303654622 303654643
    0x906040b01030e0f0d0806010207030f060b2b0204061e0506030604090b010f150503190b060f0a0210050606090d08160c0e0703060f0807090f0204080312040614060d0b09 74
    0x184603d01d84d4140740e89001c0f500881c00b404958031509250f03540001607980304c0c001d120003008441c0300165040440c1e40ca900c0300c040034000034900b0307091850149011202a6415440342d906070a81410001146840d216040c010210840911000c0381d00c3d5004400f081c880d80302c0d003070017580c0000000700542e440303a00c154203072035008240d0390495844400004000199000b040e924140111048010038000c0c3e050f02c0c8140540c52411a03607c0e003c64131440a0f090f01402d464011401f80486041500d8100140560010b580c0c0101304003ca50b8011701d0035541e000d0106400b500042000b4a625150540c0444d04c280e0054005540c85c0c0007030003024552001c800003d0544484070300f010504040414045003d0041039505011840c2c41c4c4001c01080441ea101d0352000ea13010800402071540b998000e8240309c03596107001401d007552805400d0031a0301c0340c0600342c00f68202c07100300810007580d44071300304e42c40c440e0300360452007450180041030001c81d100201410a1480070b0000f200d1036000c00054615 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 303657122 1250 303655872 303655901
    0x5060a0317040905070314180c041a0316030201090519031502091008060f13090b0109060f14010206060d0503162d02031e16030507051e0906040b0103 66
    0x31208954078a081d40140c02a042c507242020007050400e031281c05000102144e640e018001c0e5242c09903d0391003540c034481c003401c060040d070b40c9861080d5100d105960360344a101d00c1007841800309804040c01c2c10b058140e5024900e40c0d1140500250364088a0901603400540d12042c4800540002010b482403d034401850151800c4140d00d01346129000707425441d40640d00c982e0042c19003842510726001c1120b113183c006c52640c1554145152060f80e00740424414100054495099268421000c6098100700c2e00d05444002c1040034480c0340010400400050245c0082003488800007512008040c022a108219006452051090070710841d003841b00c41d18400748000e101c0e0302e13114209072545010091807421b0414020200010030f40c255071041e900502500d0301d95068a144030521302044003515552042c0c5003404030b0300c01c2d001c0820303016501500080203e10314000401c03500841c003040460a4145611104215849030f000b915000755040350040f440180c2540100d0044c0154050001c2 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 303658372 1250 303657122 303657143
    0x60f04030804050418110f1903050f15100501031109030d0309020a12080403140a0c0303020a02130218120325060605060a080f060120061608090304030605060a03 71
    0x1000307200780003042283e4055400f40503406a103603c01480d41014400589444202001c0c0c00741c42c640007000761b00d09140240a101c40c030400c240c0d40006082e56400484080d40886c40c40c5150a40800c40c183c50500040320000c4145084480036400010070301c80d06041c141c0700d81141044d0200c074001c0d030303400420280c22119003034480007000b4013900c05101c0580c080c0b030f0f48040200b1000e001f1282c7e03582c895000b261842c0b625145603140030345d06601c1c110a9060b4010002040009100000300800860095000b40298030b424010050342420041c08202420310400c00f44c400c2c1781c50300c8550175040400703c4802a00002c41c440c1139007035108604c00d442207448035a00c4803080c02d210040313450840f401440c04010407900c58007441060310074502114003082440c80004d50403401b1900050380705006241c210984a4a0301001c042c800c07000201e0703120344e0094003c0000500018400480702c07245890880114100080f20329140d11440c040600003c0d10382c00042c42d00c0d1954040c0000940c4c0c450507414 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 303659622 1250 303658372 303658379
    0x210050c0d0e03090f0303130b09040b061612030b0a06110f060a0f0e0609070302190306060b0706050f0c03130503040e070e1002012a11060403110706080108070b09060f04 75
    0x83d180d92107944c1c0f0314810300e19136491404904000056400f100c102c0b1644485850070304d0640d4429401c41c80b141a4400d8030b603070f045e804a4407030401a22110b102581e050011406510707015031030407500e600303c90816180004545150383d90300c0b00a02160140c0c106a0009105441c0b001e04007082d840401d03d4034490101400308582d0b00307901c8030002d214080010403243c80c80260345c80d12180196402c00c0030b80c0c0007010500240c645104240402c030650013486d000c49949542310800d81d0342982c4007001c2c2403800b10380d51040c018580501c039449404078001c0d9000d894003140244c19400060a0581035203c1d001214042100400c110740140921002d024131a00d0146001018040b00610391402000c0e40c012805c1101c2c0140141600406407900300d03000070003034410300340140030100c5a4108000c2c1c40c9010003008241481868040e50181e90380101d91407001070280d10b411010703809803041200a20042060f484082002d1040d0341602e801190f0f1408040000b550700d02910414a415010001d00003 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 303660872 1250 303659622 303659651
    0x9040e06040b09070518070f05070c081501091514030a06050c0409150f0612090b040f020a050307030201080c0d090b0f01090b0604050f01141e040f0909030210050c0d 73
    0x294441e40560045403502602c0d04144454400680c4c0c41201b0600c081010a1016014004030103550000d8a01141000d90030746880c00105800d9000c540d19400110150002803400449240035080c4240140b007503010070a5155450109842540740d0320108040e0082c0a5a00307008001045411940600c810f080079210401a035210b8400e610742c0d40d01d026940405031502c0c000b1082121501109440c0c06460520207450103a01504c000c440f081d61505070800103411990210f0190740207010b0040080d00034814011007080702d41101c0c1c171944c000d4408100607a8480318459000d491001d0840d00d030018100700380058031010400500c101c03003460401034000b400d034403843e040302c0040c1402c2c08002101c00510a45100c0d41c0191034020310030801d1400a1350140017603550001040150614124904d14a40c2213002c0030760340c60355660030020301040f480704803490500107003580040800840840703039000381d912040d00c006440c80c0d80d260304c009020140400e040c0c9034485010035007403140c006e208444 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 303662122 1250 303660872 303660893
    0x90c0d140a1d0a03080405100c030203060f03300f040e0907050d0c050607110a090b030601150801030b1e07171312110703060f020304050d11030306010509040e0604 72
    0x10036580382d180800100c04990a00c0b14038109000c02c0c4003410041d503068608403501300c0d00401c00c0e03ca501c10720502080e83c14180c82185080030559400607140d00748501040022142e06076034500c40c0d0721000480341d00c6501d01c10410604040007a01900c00c0c0c51408800c851030089417810090200e022800140e18168418184d2141c07510800380e0320032a4a910030059655a60180600840d030003520030720050031300350000e1004e18042d910b40d012090050300012581c20b2681c120740207031512001190700314101040780a002d0b08010321100c06c0c00b004071000a044000510000c0c204004160100700c1c00500080c4040c8240c1500000b01c10324906000040c1a0782881c10070140c0649817000001c500d00c5a4464400d41642d022441e80380441c1231031403c845615403e66580c425014000b400000168184204404500008005038580c580740c10304500b0801d80c44001e10601840d0890044404400f20480c0d034800c0742400d003541c03901c0800012400800c0320720351045040c4101c1d010b0009001c4c20031603 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 303663372 1250 303662122 303662131
    0x1c0b010308031e0403020a021003181101032304030509060c0304060302180f0306041101030b06030f070908030f09060a2a060f02091e150307080709060507020906090c0d14 75
    0x41407040f000903a40400300499041390f0140c011381000b11002d0062800380c00541c1082a03524003c1a8208203150868034030805100850740c0f602c20030885040d0b56014005d1100b0300c00845003042c1004ca0001003020f0110b4001c200404000000170360811b00da885e40162000001000100c0c0d46560300d0702000b400030760100001540f11086614400d245181280403884c00c2080980500700a03101c50391510100700c0300180d0b0505041c0c5030080c0050307548504025604c111142100d41c0c8090810b090041c1088155400024198000300201080c4171144401c880327001105031303503132550b5210f00c0c9400c950148a0714680e4807e5810007945200c802e0b40c1003038605420b03014030b4041200c2004002540101d105503c8110f4200c250340024a4518140b0643c141c107500c0c01419000d00640900c10600a80d44111107200104e030031030051100b80341c3d20801680180446050052600680341c000400a91006000034410f40c01500042c5451070840140d400424444c00240f0654050b5650740c41c040b801200e = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 303664622 1250 303663372 303663391
    0x1020421020307090c170a110f071103010e070303110c060403031707051c020304170304030504092f090f100c0201020105060901051c0813060903030e010c0309051c0b01030803 77
    0x84003060b0042e45100701032402549455282403d5211901010346c4c117401004008581c0e03441a40004110b01d140040c000f020901c07200079950310040c074089502c2c5802c80407850081e8940045480701c0c0d000050b800341030340c1d010b05001207581c10118066240c4030b40d40c0c3d40c40d0b400c50404280002059005400c0e9082c10345481d814070030560302c22500310761a000711070038849240c001450030000c1189540c01907811500034801e16481c60b80b46c80082403a5442980d0850000e880000d040103a0802c91141581c2e44001802455200085070101c170802035048a44482204002819455507501d450000c01e0a0502612211411071000c00140c9905030018041c0c1c05542071400040d10343c40e140100c907060b00c400811081207051640b142d10710f90411242c0460b40a0310401c203074900640e45130f0385c0700020b06065903202052811880c1c001c25000c00411760506014880005200007a00300d0a00001e46006480c00c0c10402e0b1400406449030007052005012a4500c40c00070060100850007940318007040f1 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 303665872 1250 303664622 303664633
    0xf1b07120e01030c080603063405070c080a02060706020d0e100c030c05071e080f040e011809020109210602070c090b03070b03061525061107020a0e0405010204210203 73
    0x200b0050b5201c030741c1201c0319545a0032480008404840c0e60580f0110082818031a01030422750240000c804100b052825000c900041010002c1140c210380c030f00060700c50396010302010702c041c5e8085461401200d000410050b00400e0611444881744d03c2050800c15030340450307040301343c200d803008020201c0c01e04080c006801c09003000307501d40c080e00c110382140d0f03480390392041070040e010507444a40101c004101e03110071013000030744400d894190141002d00a031030846045075240801030404448843e60f0f0400385405d1680070710150380c1180480d0201c0f07801ca8011510341c1d610440c01d0340201c019000040c14140302140300c40c1171000c0c2c0791710541039805a1307008000340c8906604141d5509401e1103069020741c810400540b00342050034141c0141da980d0007200307042c0342041c2c072207021048084108900c400c50300d03100581801101e01403022504056468103180070100d0300800c25203160742c010a000c009540001c502000801d504840080540d408240b00c0083c40401e8440c09007410007081e0b1192085 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 303667122 1250 303665872 303665891
    0xb0a0e01060509130c0803030907080115031509050c130510060e09070f020c15070309061404091806020c0609160b190201060f080304051201050f1b07120e0103 70
    0x14400d001c25140000c1a4101594504000d140c09824103542114815008800000c5000e0100050350007041c26102510241d802c00800908603121407180e20900341c8601820004902c90f000f0704000303a10025404900106181015407a2000306e076491a002a00380038124120f0002c2d50009004820b041417642d480c075510340e0220744c1038071103104080d80210541d0104000a010b00004040c0c00f8450042c0c903007426130040001c0119541e02c64038400c000000039001d041507442041c590185c807003820300442100036541c0c40c0d030003030150303004841040395034010700700068000113110500070340e000740e066540c4c198041a240c1c5a40c000c2d42c2280d040d2141c0e20fa02060800400020415640310392404d034142445406591380f04415881a81d0a6542c2d54402040c1c48052000724030207001c414008556961400d0b092000003100c40a4642140c1d14020034803450140c01030256070410b40755030002c0808041047c0c0d401c40f9119000005107410719000a901e200e0380c0003100c810104500340c800700442d01c0d8 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 303668372 1250 303667122 303667151
    0x50903150105060a081b0d02120901060602030a180308040f0303020706020c031005190e03030610090b07060b210705040e0a170a02010f02040b070c05010c050a0b0a0b09040b0a 77
    0x802e0080d1540040148200140d0910032601e45a203e905040c00b0808200c514000d000c44e903019984038400036800151240c802407280e890b843d041603260008021051400c00025203038054650160100030140400300c3c0c4100d2001d0500019580020103903580d55038545da02900c51034944011005401510380009546001098001c041c8034040d020744200c9000310104801000c0051036140030140c001c511540142032485584c2800d10100021a500d080450800c05004441c1a02404100035441c00344000400c2c002600c00c101d600c050040703100b10150000411800222018a14901004517103485160000400400b150001c5d030f000c000020f079002c00c10351569804000036211680710100e000041520200a100d0056207200020f00b07040b0b1840c0d14810b9a00036404000d800c80089245410300c09000a03c00040400342031200500321140c0d501601c4e204249070103006007110000041c04080c594000044c05080203003c1000b0385454942407852450540f601161146051311615003600d = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 303669622 1250 303668372 303668413
    0x7120615061409120303040309030b0108030903120a031e1407030905030a0807140d0b030c03030a080703050a09021305040c1a0405040f02041208190206010614071b06050903 76
    0x49550b5107081c0074984031107103441107a00240c2d1042d08107402c00c00d240d10500b0184040c500a602c00c0d80c80c007151a1842c140b45076400d806800c94200c0e50410807500490ba82c0015000d1040c01d051600a83c48000d549426070040682030003188008044055410810103294441e15152001e1890308105882e141c00460441d8205140104103610420820f40c2035405240349640c485910320b0000100d82c81c4003405080e94015680c4485e42d5a00c64207085410301c0c0c02e2122003001c0d04184e0055040800d0b40c40300602d1040044c082074103060391000071649041c61600850107441c0c000c4c0c4111808200039000030010030382103405a5a1a0701c4070302c00b00e040c0002c01552901c40c0e4405039103900741030400c800c001c028103408220070902a404c010020b481c10016501540450280e1401615000c0c003800c81c171180d0606c07154210440d007105005001680c1c000150424000041641c2c0c0d072500558540381c540700e40040e40244c8840011000040c0003a40800100500c0c0d0055040d80c02c11042c030342003c0e9208 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 303670872 1250 303669622 303669629
    0x1805070206130b1906080304061101050f011211030a0809040b01030605060307030213030b0f070f05090a0b09130e0105090c0906030606040917190f1107030b1807120615 74
    0x910b14507818001080d900c48505030440d0130a50900c642e0307807400700e4020072608203521207600c0d80c00100d010000750f500011000c0100c410600244442d15064030708030071000050150880b61281007480005010f00502d600842c8034000d0201c1e00300350f83c6c500380a411038000c6006944200d0074000154601e503c41c1c082e140c21a03101424140c10b603241c1100582c042c0d000080510181c88080303000001084111f045540620640c020010303a60814910007040340002c074030600d00b401002c04c815451511152800703001c031007450740394503126080300d400190368081c000702e010503040c100500103060078410341c000350040301034804440d2344500b90303000c0c040c00100c100c40d5143d045d08490001451401c25800c20640141310300c4461941c90118042000103800c00310040c52a0f01040c19000744890700502841c0340701c4105d05161820141c11080306170745120500004196100b05000300340c0701180c85035003c21411040c0d00352640c45813a0080d101140d004c01500380c412a0405481001041c95012418242c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 303672122 1250 303670872 303670891
    0xc0201050406050c120a2d0605040b010503041a04020d1505071121092103040302180f060f0105130b210606071103030706020307080910020a022a06041805070206 71
    0x1903071103e800308021718144120724241c0c0c4441108080c1d002d020f40c0c14024030100084005248d5041500340303c1103a15480c0d82c5810b0060030420700002c1040090380214040160b10140110740d50f41c40032a00062201c08028144d850340c0e5040180c080399900424844c0d403d5031341d10300c1c000750070b5098556101d40c41440b81148003124000401401c0d00040145120700025010040e00d403001040080310b5454042d009107150400b16080c000c40c5488aa1030303107078512004249070b46050041c22010843d1000c1c040b10320036038481020303040300c1c3d0090041d5021407482d0700c40316980a640b44158480355000c40c098045103030303d947c900001000c143c600c45014040c040c11243c101182583c460344816100d107a900da0620050241c0e400041841c0000d5209200701d81d514101400c0410f17032145006880d205400545005010710660190300081c952283d040b904030342c030071000803606600e15203104441d04607004540040d001c104110800c907821030300c0e6010601001580d495007001c9880b0001502c0c0c0d280b0 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 303673372 1250 303672122 303672157
    0x501090627060b0f09011502070b210403170a090201021212071404150e0f01090605090409020a0801050708040c0e071202030a020c06070e040b0d0804030f150c0201050406050c 77
    0x4282c071a4404500b41c00054000c1d02031450080000e020480260701180741602402c83c07024441c0c1d414004e0100402e1002c0201d824039105440e440d282200e4600d010040300300c0840010140b51080e82c174130105540c48400441039091055000d400303480d03d02401d078003600c1017003142c01c41c0420300c50466010640d990004561a02d4007202102c0003000c8081d013102003d401e0101040c2d10a4001041c5507c80440d01c4101046401c0c000340185c4c9054861114140f2048900c02c0000c140c1150441e4180003045500144000340c0b440050000c40340d50308180100d618003c104020700390881c4003240141d000b49030b1101080e550320503c0da1074420448203c00000c0090207040104030700c580280d50400a0304c040903007000300038440c003847c140b02143e09400080b09075014181500f09071044480410050f5407401d145002911105102d00c90782c0700c000c08001a1034940d005014140c0c1c28032211000020040c00010070b4074100a028040070340c1c1c103480796440c0501280d408a100c1080310203921150f1102d80 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 303674622 1250 303673372 303673451
    0x901140f0301050607021f0e09010501052113050307080417030703050d0c1b0c1511061b0915040302040605040c020d031d0f030c0115121709090405010906 68
    0x2425400201301245c1000d216881480300c900302c1040011031f210b469444854900303480040014200c0c043e0301c5903051003000c001c1c2c1105c0c0c01d01e5081c98034010b55501000f205540b80d80030b6228004200e24070140483c00042061700c10070020303400601c1201d001601d101e810740c0324064040e84901c1164002400304104102a1201e40100e0b00840c4c1100900d05100055400840300102c1c00d038903441c1d084039020b403030003810b01006c0c6000d1031100003002d0310718224800e44154171030f59650790340c0503241c0b500c26000000d101e20401441c104942d1200e90252800000045402400c3d82540090000300d03c114103100d404a09400c1c40e1103160b540c245141d00030f14042d40e503400203400030020f40b80760394003075514040c2100d1041010045c2c1c1d40381d0550080115601c58101a460b421640450720b80310a0505503101006801c0305221110388280e040000711900444003100c0344424882c02c401711750025400002c2000303018040d441a003107640162030178001c072242000440c0541e90080c40100d2500a1120217a = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 303675872 1250 303674622 303674629
    0x4050907030b040f060b0333060304150e030c0d140307081f0803070507092c0102250317010506041701020702120708160605030403050306010210060b0901140f030105 73
    0x284442d00c050000902c0c6480c01c00d40340300391515900648035201000007807158401100903c043c0d41d81455100e02d2401c0403218806102d0351805440074821200030005c030341071007103204011412851000b002c0080c40c80d80c0100d95180d07000565400303554000c1e400f1202085014034a8040301c0c02c409a421491030751600402d5440d4617000c7c0881c4c4010380516124400c43c0e080d1390710342d009002444025a2200c03e103150031447c002080e0440042641446440c0d001142d50100340c042c074185242e46003405040c8140828024080e40201e000026401040003070401c03810700301c0000c00c5000755210748021030b440c3e4186010700c3c001e201e2550402e00801c4104140c04a09036040c40518a8070009854001d150700014100d01c1b20311a0784040307400a80d010040c04408225540c454603541051341801031030801c0142480c0002040907052100c0080000c005a20a1104043c005441d000410001e601d4598030141500144040e90119029a5041c549840f54105607000745606040c1c0d00e1842c1c0c00c10060 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 303677122 1250 303675872 303675881
    0xe070207050904110411090f0307050307090203071803120f020105101406070510060518070c0609020a0e1801110708161a010b030a0501060e1c03020c06070503030105150405090703 79
    0x140e03110403880384c0c503a069907078a001d00c600c000419113100e51104904030402c842c0c9600c90207490f00ca584010030410068401084a4040300c400074001616030381c0c0c1c448151101c41500c1500190503180410100c10000c441880d07440c40301c038540c0c0342144d401c0240806da08881040e2a0b080e02d0a60013841001034000d010804c158a6902405160034402c0740da80d41c2c0d203003c1d0840902001c441d1a0f0340d05011500707100b0a074000408517449000002d08001c00040c001c04075030380b800b400103611100703a0015512420398280c001c0c41030144498241c9171401b1110a2090450301c0d00d0082c0d4200314448020f1030700701c404d0305d00868100d01c01d5880c2c070940d40406000c1480c445411505100990326600100c0e08c01004180289004181140c0c5c070720f88844d01c40c040f60700503049201404103c4151076402c0c1c0f03514243e01c0c605d41c0b03540d81d0044004140d040c1079140121280c10a6800400061683c04200020010b54120348060316040031003160015810320358000e0b030040540114401c00095a818800e400 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 303678372 1250 303677122 303677131
    0x1209010e090603031318452307062a110604030f0309050a0605030109090311011b08060d020d26040308031905040c2904060206010602070e0702070509 66
    0x8985c0b0f049505032440d1001110b5500004090450940012421a43d40a015560000e03291b40026908003030344140d54a00c0c072100903c002c642e51500341011320800469000c90785400401103a001841040c035007c2a201c01182d0445030700500d0400240b481c00341030815808444000007840c0c140440c40291241d404494068540802c00b0040c4009500d64000a00256005012800b0140100d050140140b020755221900511016004010040d40b0500b983c1c1501c0e0081000319540c0c8143c141100c0340301e03903000c50321103a500c2d2540401d9040c0b4688641c180034034030b68445041503500c1e03004204005060010103500000c031b0340312510000301418078200c281c1e0411402ca000c0d550301c1d4104440650484d40003151803d00010a0040c0b090b00f504a446070312015801c14400c5141c10380c0c0e8003040f9401e5201e80a2114010004d01407020350024502034842078680311141c5980d0780d168000e43e1454284205009405041000300791b00c511100014030a00050b0000c007001454481841181c1000a0 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 303679622 1250 303678372 303678379
    0x1005100302120d14092b031103040e07120207021005030105040c030e0d081012030201090605130f06181502030a05011707030b0c04080105070f12060e01030609030c05060a0e1209010e0906 82
    0x40030a61244042075902c502810f0106c400000704615150240042c40c580300c00741c41680c41400204503905e600400d07964400c0c441e107400040d401622442402900446c88000e501c0588c2c42280703038031aa844070145048610451303040c0400140311400b84d003200d140140e285241d421041c00c0c0c64005006d8940b40b03800031383c9641c80340e00f5580d5a40c01e21001000840d000c0740141d441d04144420710100e80a4149c102040040c6404281340c6030359031015041d5483c0000304459281c415800c2c00d21070301c45540480e650007903007800c800450800141e00952003202c1b0054101d03e081c00100c1d00c0758640359020034010345d0500508038075046440fa2600d0003c0285580510102000f020501c2070f800c1c001e050051606880c0e420b405550314101030400c00744440384002e10361621400704107800c0400c2c100b81c1180c0d0042000242c0003520f040407075403000b01050203002c5114036070900c00110700703a80c4007003010000901603903143c070844160702140c0c0c8074440300b00d8005090103c07000b4481c40c2442c8075a0700a40d000303 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 303680872 1250 303679622 303679639
    0x3031b0c050306010e07090608070507060e0709020a020102040806011202220204031509050706050c0a0b060d02060c06041106120406020a11060109090506010504110f03091005100302120d1409 84
    0xa0300082c0ca4000c3c02d8000101c0d8003d00020302601305d802c01114005444a814464010303d851500107006000f004006030907107454000c2401c03600d1040c03110320068100541c00395619064010083e010394024860807840b486000b00004003084244980e0305240d40c001c1090004401542c1c00e082001c8103010052586682040000002001d843d9190400101c03c1000f15414695051403030402d9240c1c1d10020500c40b04101240c1c032040c3c0400c0d04010103501c94140481a02d40c81e0108107114015038000b5040000001c0c810000040000c3d914803491042d24102da0880d521028800e29001d0300000d030381100d131902d0200300001d02c00d402070011109207123810701541d8041c00c07841d441c00700300303920103042540da819801c0140841030091502408c000e0342c1c14814001d441c0c0710780032244107082e8200d400c4403000c03000c614844014001404480b005031028450f03401c2100030340240c00300d1480124481c0030f20040804c950140481d240c0124200d6444480e10b0a0480c1d41092440e484502d1043c0c2c000d106 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 303682122 1250 303680872 303680879
    0x150501231e090a0f08010f0e0606060a03061d0916120b19050a020a0215040209011e2706050102010c0e040218030a0f02180f13080c01020d15050a03031b0c 68
    0x3c1603910001402c410b00c504513840c0c03030528038600711505030582143c01814001c5070304004500213009500020f0682e10903230340b880b003290110300800b06034102030410b000854909604521800e100b41c00b8440c4001941c4001d43c420024150007205403050b20f010140705191540440e03262841d55501c8203001901c03519035406241010101c0c0c4c022a000c01c50b13954003051b00c9140550401c400c064284894404d004141466000900182814072950b40c40c1c1c0c0503000000e4610b03400d500c0e00c5000b001803c007041f19044c0041013504066040302820003d44d803402d44000380940c414000c0311011062620741c404600e13490310600c80690b00080e258003202141c112204180c4d2820000302c40c1240c0180410030440540f03104202c1085a00f02098000040040900c40011003608509810400790b01454000300554a008011401040c2c04060294030100b07850042021035005403004428510074400c070192034100308031148969000240000f03104950200000700c006012607503071400381c800f0704601c0d540c = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 303683372 1250 303682122 303682129
    0x806070c121e0903110613090e190605060405340e030307030305010f0515120717040f1101091401050c01060b073f120e01150501231e09 60
    0xb441c21100c400a142002d0030010301c6900c41500444e0501291410b14240c0c04000d18203035601d080c01a600015075448442c50124010060140e44580c0c0c040340c613050119504002c4000c2c0f80c00c40d0301c80e02903428540000ea0503000150703410800315444a00e481c104034122201005282a013480109002c0c0a01001a90366410005410704511036580401c0560501c0c1c0322005c00c40295008074003a10049a101071000c080405444155185207510419507940050865204a040c019080c820180704184020b125200c8868580d080c0a4003950005105e0030004640343c1c10903205100b0811602d032580941503116400401a82c1d1403c4c00100e0b02c81e8446254001e598000d20b011521909004600109881e1160f02807103044203254004103500518000441008940410f580400c541e65850491058240c0e00c1400714103d01d40082042018855044940888a0284a0100e086800c01480c400c85480d116a00a4050380c1042d05103100c0d10748603500c400751550002810074082c0700d80c0000e5127 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 303684622 1250 303683372 303683417
    0x40c0e091608010b010c08070f080f07031d0f100507080c0106212607120302180613060503060d120210060602010b090c0906040302090c090a0806070c12 67
    0x10101405480107096114512420a540070309041d904040a4046983c1c010405800c844d0700f05412a95596107032170659011040c410009200d006d022402d900d80103513100c05000114400d460700f82c0f42c0c0150005520846044100c403d50118442c840c5002d20309002e50045207503001c0d401c045007400e02c00c1d40c480401e50043c901c80400caa542d14001c0100806005001c1c0919107600c458014401e03254882c9240c0c00c0240303a2207048070641c400040140d030711000444900781d4015501d505842c62440707005001c4d50050305800c282642c401c03178103400c626241c81160400d0300b0203e6203005551910a05860540000301394691059a07064104085100e40c1408040301d0400d601600c00900940d6012080310640c0d040002160700d042c1720820140c540000302500091800c81d0780d03498420790400142c0314441d60b007000750003e24100a12540035820000341c40070303000031239141817070507210790507549d5644044030380500040c00c3d0f07038a10011500d0040e184000008502e407203078145c11404023032074052 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 303685872 1250 303684622 303684631
    0xb18011701021c091101090e01150e130603170c060406090503090a0801060602070603020f180406080106030b0f0f0403051602040204050409080a02070b09011215082b020105040b040803040c0e 84
    0x10f5131140004010400c494003102860390003401e1068030b06040541d80200b120050003640d010180e20010320340351502408558100180c001c0c981c0e600c00d0004c01d003540107082a44800c665001080000e00c40b640da40c0800d60303612803000402002e6543d555150314028010401051311280010841090641c54581c4200c01a05020b400800c02502c2e2070b00c000e02c0c198440e130000c2c08040c814050104178118010460303420440c041c01d1171640c3c03038042002800400301a480002650304c0c100380007040010007192a80300301d400c0364480c80c1e1035669006c0300540d82021100100040c0c4200070440e6400f25000c100800b06001030030043c18603454102280c111356140c14150348006010960040031030b8100501000b07440c0008804c0e0801d20f40381c0028000e02900d080b07480350f85444860880c00420300303400c064000c0c08402e003102c80030090800031503148190b01041c11200210100803681cbd2500501074103008940c02140300d0240d64680d20f8001d6160030240c4201c0e4503100c030322000030301d440ba1140341c503028 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 303687122 1250 303685872 303685927
    0xb0306061e04030b0f160c1a040219080d030608070302033007031d03151909060230010803030604020903160608090c0a081005042a090b1801170102 65
    0x30790429505c8120640146031b011001c00c090489240002805240c1c420540315070410861582c0d1101e100144e0301c106900305c00c818180020300b00241803040000d100901e5400e5890400c0455207861589458019a01000e5015800325007c030720007020705035151707213102186841143d08942e491454642544503a00580019004941c01d0004020313180e40003481000880081c4000a417031460742d01d8968005122042c030518100c03043d210400c0642101050580c050300440d234501030038001c0541c4100d0b84020309540d409080e0640c400c0d1030b42c0a0213a0503a12100300460850360341c40304000107540f201c8031580d050b00600c0500c1c00140365506400c0302a0141e0f4550014501d00b403040a480c01c48500c03001c500c02c01060004008803080031030101c011007158000440c440ea264102145810340c400140300d58500f0a1160740307424100b03044250240c42d403101d0305020440403802089110219458500d42c40c0f01110b00410020501c1c3c1108150320045100160401d00c4030018581c0d000f4150b00d10500 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 303688372 1250 303687122 303687151
    0xf031306030605060c1e010207060203010e070908060108060606070f050610290702040515090c070510060b09011d060d0f0e06130f020406170a0b010b0306061e04030b 73
    0x29030107008402c00b0f80f2040c0d80d51814a011a001c0070b070755501d81d08550780450f45003810030300520800e40465070000d8014605550720b5039581501c2404101c00c440d1000017425448010403050030100c1d20130704039401c04008003242c2e1102c00822401361701802c000c07605040404032030400a101440f8051041044404d859003443c0b400f41803002000480e2209030350a910380030003c052880c1e82c0d0a0300c1503643c05840004240c4d03a0078400c0b0b414141c031304803403d0740200c10404201a80c05848002e12800d40324005403184d40c04400d6101c000d0320711a004d2012043c01c28442040554800c80c81d1064170100394410485c140e1110000c10030591000d030303070407905a0700d42e451921101518000c99140c0d24543c8020141351800b041c14030100d00b1080001001811181411800c1d5901c503009030014140c5680350a640400d0003003d103542c0c4e404140112041c801c0100000354044106040d607102c0c00000e810700d40303002500910304600c1004030300c1444510409100c0030021a00800c0b10610030080c1050004 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 303689622 1250 303688372 303688379
    0x2100b03031908090105150a09110d060f150f0e01050d0609020c0a06150302010207170708060a0c030c031a0d051609090201090f030804031106070b04030815010203040b040b03090f0313 81
    0x3420340d0402000070041800300346407c0510303141e80395100225441a800014030b0072000c2c00b060618401c0f13803001d000e2030341403a80110307523910040301140c11610312031041081690303000d50580e100b101095666010030503462189980b54014801850f00c00074071a0b002a03055100c09102080342c01c0708001c245c0c60352040e0030140800915108004c01640e946190f084034a14550000b0361b070700e18a008103140e9941c1c10042c1c81580c0c10821010340945021000d603200b0340350030018a4002c01c1c84400080000341444a5480754a00a129455204812001c00003040d40300605224500f60000c10445162080007100c1c602203a000d1544800703007a0305900458181d0903400018200303d85500220820308001c0810070000b2409821141202d07800f0030070f911500e04c030341d002a256014443c009001080c1c07040811041582c0722450511540070006542c170801300401c01203a407400740c0d018004070309604101c14080c202d031300806990300c003080d00b08a40951306124010340c02c5030032281c1100700b0b2201903002170 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 303690872 1250 303689622 303689641
    0xd0207060e03061005010f020a0b0103030c1a090d0e130e060103050105010e01121502071e05010f090305030f060f0a030602030f07030218010806030c0a0e0103120f02100b03031908 79
    0x40981d00314014400d508000c3c943e9180741401c1e10071075050150000b20901350381d0080c009141c5440d0030919020b4550795906000c0e00e00d10071020105e802181800c02081100c40e40c00d11503001700006c000030a5100744544040d103070000045107440d404030a00e1070030079504515014841e04042c0b51130240c5007551440c03034101c1c207450040e001070a050402d40014007020303480b501170090154000403a682c0400311140c01d90002d2050200c040c0c0707480c4d9031094912002800726000036109128000030070902042018082c2103c507800c500800003a400c20206810510040302e050b04244010710f03440c1d000ba0a40001801c50031a50f0007101c0750340e00801042484507402d180e0f00d9008555042c01e601d804981c5448000c042da0401c23109050010f00804100c031500e0801005260701750141040b5103041d244c1204016405092004607107543d45009a120460b219400040d000e14042e00117140c2e50001462540150030760351001600b5100500088040300441c200d114005030054613050b885050075004c1 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 303692122 1250 303690872 303690887
    0xf09060f0e03070302120d060b031305070f0b070206033409050d0215070501060e01090f0f090803040b130609140606090105100f03020d020a03140a140408030a0e0d020706 75
    0x803504580040c0f02d68404030b5004503078484142c000c10006c41c1e0b0ba013118000ca90080042c3c0d0440c520000300403041040ca9844140c1c1051080d01a0040341c40340f40c0e58041801c0c0c2c41a1500401000400c240020401401c1100185402c01c055140c1c060780030345c002c1e610021000300004107001c00003000c0e031003000c3c1d40d800c19100405418113543c2c185010b409500824046c029030071411120000004001c030a101c806c4d405400504070031045541c06507501c1025038050306c688803203980c0140c540005042d00348824882c99540d0f580c84400e450540c2d856841e02240ea140041015030560881c510410010740184103030103600b403043c1e402d01e40b402c5075460942d117405002800305004555070700050046e6a504000d074440080c0fa481d00c0701c0c0480004904078040d000741c002c460309003400841d8501500350107801c0425080718110380c4800c02c0d1365098a600607a1000340c5080074142d0208045004120301c0c05c001c5600000b085800320b0801b4082090901d014030031207446c0300507000391209201c5150b01085 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 303693372 1250 303692122 303692141
    0x4050718050402010206070e040b09070503090d050405091f0816180c080f061c0f1101081e04021c0605070906023f0a03020a140f0d0f0f09060f 63
    0xc200700074505540045d50754100504103001f03102d443d001100e541d40d49c42c1c0102c0c20070b100c05454600740e402d0030803001e0199007060703075456030900400d00440b48241c8110252021030320001c002c541641c44078040c1d902134050303003200c1108981c00c424010071540800c0004d050b040803009103603148507243c4921050480c00c104d002e1000301c0e04203800c1041c8180d00a074803a030000e041003800c00e20350b12280009400050b07142e04140060f421030035240240a02200644c444031b000d01c64080400c0307101401100d000d14100c0d00c03039816441c58000710086440c520462540584090040008031150010100c5445004a0100c2d0031544400070880000d41c04446e050043c46903000501041d00c440d4400250321002806050b205210f0082002120082d11074074500742e1b100c80f08159640441c00e500a000e5407151036640c0200b9a02007100e681d002c059411220700340d08508855003855040d42c080b001400076862681140d545500d5501d050f03108500c00c2000947c440c80000940003c161140c4054600000 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 303694622 1250 303693372 303693419
    0x2b24050f15120a0e10140f070c080d02120412020106060e0f06090303042711030403080114030a021003091b0b031b0c100b1201060b0a0c030e09040507 66
    0x101e030000380d403403801525501c0031484101c039640d9958580c600001c018105100080380314840301c01c4d03c28640d0340c1c0038003088140302c04009150b548030242201e14200a0b101440051503041a010204808030060805a803075840d000d0300d00151000200c110300300030786040c0d90030704900c1d00940e0600c0e02480380000824041c100345951a84400c0041c41c490b00045c1e13590300440000803000d81594041c4211005810564840004072004d070010071070b600d40188003140e1251030b00d50541c800c1d50403038003900c0c07113a941540c80c00e000e81e09003c00e0031806640000c0f1550036110304040303940182da800612100841599400241080075414021040702a40f181490301c020000001e105806000003284c0d0300010181104079256501226814a4800c400000075540100a003003400480581c012150500b03088810148511200e80c007507080310500c2c8503001d0050402c000700342c10329024400c0000400e010b402c11a4004000c28041030740e522007100d044030190002503050003401c81a03441902d8512012 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 303695872 1250 303694622 303694639
    0xf0c030c0c0e0601021e0601050d0807020402030f040c080a0206030606160b09060907350307170306130b030a030f050c06090d020d0c0c180603051504030809032b24050f 74
    0x88800544459049c00f449009202000309103041c01840b204407a035041d4003400c00c42d900c0c64070246030f200f0343d00150340890340001040f40004c0d031100c0010b8181c0c106500109480d20396240c0e1000c00401e58002c0c1d44203d107148142c2c00300c001080021020074032034101107000d41240e1410300100b908110341500551480180c00402c4d18805400000781601d04400c6050400307200000c0e03905034518010100c00030714003c0c0354841500040d000c14003550080c007050328559459081c514125040d102010301c01600350340440110804030b0321a544000ca40701071420102e181807034840300c40b4100142142d00451540c0400341000540394100407199440d0311502d002246032000c0c6c2ea8940b5030b950a8810f04007101886401810481410780c00f00c4011070b4810100c40c424100032003c01d07c9458110b078281c010401040009551443c00f104a4910f00070300301c0e6681c1148070042da02c2101e07018580306400410b550340342c42401e40300d0302980240038521101d52150590710b0141040700490380d4010442c0200880b = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 303697122 1250 303695872 303695923
    0x12100c02010f110912031216030c05040518061f0c02030d050a14030c0d0f0b0109050405090a08072a0806100609090e0c04111b030702010f0c030c0c0e060102 69
    0x90f003081e2030040740125004d0199081c0f28807401e155025196058452806010130700c1580d000340079503101c081c00d06840901c0603d429aa068609000e80e115580e00000310745181e048004007001c880b0f50000c0024504820051500c801c428040000a11140442c18460002d003d501c3c04000c0d00c0b18110320b501e00286006e900100041c50004507840c070603180342010020514440602040c0c40050b44008000c00ca0141851011009000c60b0b490075808035280c0f0001141d1401c0034007d05102c0d0000400400d21461507686c0c02040d40d1042005031480700c80aa403c0912007400c2d500222001107000c05c145006003071644840c00d101000e0840045c0b080180000c00c0211f4000d4001c3c421550070442c005105081d8006040c1003050450840b03034070501e1b003041c0315002e034000409480404880660204d00285160b2042d58a2207440c00181c00b003004049240500b510402012400b00d12a1902c3c8220007002d07651001510303200e401c800d6005510508002c030a590402c0b0f2103034603642903414810301007007 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 303698372 1250 303697122 303697151
    0x932010b090d03141309050a050124050714011e020307020c01030c1106010303031b030b03120a170103060b1206040b150103020c060f040507080a2012100c02010f 71
    0x795484a40100910752065080c10300034540b5401503110f00c040503540d029144060324007010203002d1090310604c1c110100f41c0e107400038403c041c142d6001102d142444514440c8400c1c404404070781c0c510401c0307410450b100c0041d001000000a00c452a800401c0c0b400c1d1002d42107000402d003042c0c06000f03510620420224503070000390585400420309000071540a1000700f00c0c2c0508a00100c810140b0940c00000101a4954440c0d001d295140e0550241c80308000401c034103644a5245055240d0f00030101c003069000300c003004140c0002603041450a28450900e80710320a0001da0064400565404a440e0a030921850954421940318042c2c003803441c1580d103140c0380c0a4003900c00c0310700c1826254000c0107079011358100d0741030802c5002124128034085202114440e012a41100c0070b0242500018152000103500e4600c1580620804840d81ca03a5004042100c0d0389016581e104104102540b19903030709000740c1c6400030b43c5c1a008610b01850400c06401e654111503480c0805142c854140c9000300b = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 303699622 1250 303698372 303698377
    0x71e0e070e060313060e0f070f0803070b0a0b120715050702060a030c141201030218040b1503010b13050a1407121a040e0d030e011406010c0204060932010b 68
    0x70040702c0564032926450f001d402e04649601c0c0043c812890440d80008101e00001d000320010b2041040b02d081a40b280780c0030958500d148594070b0240e10034402040003a084505035030744044041d0000842058010008442001d1400c1055403a0800001403207000900d807913801c0c0c03207140c41c201a491b0102c40e41c040344003440394800c084100366031000c956455520840381c09805408128080e0b0701c9403000b808100901c00207100803840b880e07411911840c0d503004080c41c9c9100e00e0304040c242d00d00f07540b088040350752400c6c40b220b0207030305550b1214241040d81e01c01d010003641c505e010301c0c002a20700d0060358110880d50718581244000010a0410410a41c8003000350041507503440c000c02c0005181c5840b146000000010b5a4000d0500803480c95511001901220300041c940d8103000000e4281043ca0803503070b21003546640030400b00001200740d4021000d045078103202034400280170796907451110850303410308844000322506542d410250081ea080c0c0904400c05c20110039510751410b0011102403 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 303700872 1250 303699622 303699647
    0xc0b0f0a03090f0212010212090615090c040302030d0e09130510020d060504020414031009020901050906121501261e0a0503030a090c090923030903071e0e07 69
    0x1616000c0c204104586a0a140791159014002e029407042000e5817a0207900a03204100d10718400c0000606400800542a1f008240b500030040c01409884d0500210030307002000e0b02100b201c200f10000040c2c80c20480420a403140e40d0700e003508980c1e413a00300040a8005400440401d1000c0042c1001c5840400d000203081c0e4402c40043c0d4400d9032459000240c61254860b0f6489071010400086265480c41410080001102a0b401d00e00c2d65a648030f049840310040603400c040528010301407410700c40151a0403036401401d103040c07184030b25291460200b01c1c034a041540e5610800403c4880c0c0c0118010f41e003580c42e002c00c68010503d040c416940c90124401400c4010705215001001c000140305000d0b4040d04182500da482c43c1c24a201006072112070412a0210b2041d0400580d16096105400b212035101e0a095160000800401015051840400303d580000c0054160565041001c03900900c648200d485484ea607840800c214441d9a03032107200480c03401ca040211090784404050380a = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 303702122 1250 303700872 303700877
    0x905010509090f070c02060f04060f05070f02011b1e0b0105010207350d030b01090b03160c0c080717011a31050106080a051005030a0605131704030c0b0f0a 68
    0x50356a504c41101c03103200c0400c0180d00000005881070800502e98001c00541e111500c0f000801e5130f80c00002c4405200c0c51402030901c00c1300a821000643c07040c2c02404a82c02c00000d2504815412f88401003848072609400b41c80784a8990b280d0104030301c0165031801008240058201d45203000742c1c1c8822080e1801c000307000ca6400740e200c43d51302c1d443c2c12512002086000c044407010180020060010114241052702080d201c00000482e424240704503480340c407194101040d034045100090300d03003041416048078141d2041030f0100e003038081000400010881651000020010145054212002c10000c5560032140e00c0115080b600c50801ea0f110f808a0a1010203e40c04c64111040c440001140403183d042e0401000044075a80308210600035101c10742e080085840f40c0c110403240368254482c60743c15402907101d50010a509a10581e400714205603003e40303188a6595054814030701b800105010003003c41d090040c0020030841c00090700101041d03a19000c021b2100f04410301605651008 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 303703372 1250 303702122 303702151
    0xa0b0604110a0e06040b040e0a06080106050d0809130531020a0302060a0909050709082a0d0507120b1602010605150d0b090405010f110f07080a02240403090501050909 73
    0x3135220b01d4101c41c0140003404541c2e44031519045010b01204044d1072841c045401c00102058402042c40f40307130300300c4500a210301c01c80401983e8811598005240c46a804903a07400041c288049502a00b403188681000032a5804080c08000843d03020844807000721100100e034500058464500100903250104c0c2c9540e10350f03601e9601110191280e0300059000c2d404c14061180132a04004c4407810340c0c0a100c20f550040810080103010510000075011384158240e141c50700509000d69a080c0c1b641c01003080e1011203031a056142600031154100320340f0115500d013000707104030705022600b5582d4410304c020701c01c507458000004c8000408030350b0588650070008a0100e0020543d000b80c140580c05400200d0740d142500300f4a00800c20f2050030003071103040c1030f40741075841c8040c02128030b500340d00e201d01e40c24001c4a440321300d11034001c01381050a5100d6003803141071001b22039601807144469a150b2000c00d01c0e29260090480c100e96001d181030140038032213416680d8414030b107542d20001e009130110 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 303704622 1250 303703372 303703397
    0x9030a06051f0f05041d010f1a032a06070219090509030301060905010e01050705010515090a02120103060908070b0114040b151804240e0117030d0513140a0b0604110a 73
    0x801c188414241c00c1e405e600c1d1241d15049095203801103a449c01c0a13002c802d40c5004000181030712040d0354904d00f210000301c954041607100c006c3d202c0c6903e00c04090032070b505215995000ca0312034000da010004103000301000c10041b4800702d005490740052a44069402d65141540151000a10703028040c103001d80c0441029060344540103440810b03403c5402030155080098003072010803100c09134035004000000c001035904449000712600e4810107044031002f80e1858450a005000c0c60760200d82040d401c00822000c54800c9040318003901018410f082d1804c0d1503003c0000b101c52140301c2074050140c0316178098901c00319505a410300365161202403076910b94880014002e150030340c102c1c07528680401d52070521502005100f015200b41d0300040401e80d03220000b080c140c1c141205440705d07a0b03104000c140003880e615004140c0011900310b40d4040c54846650306050744d0820b0110002c2c1e035000d05824828000c1032000c0c141c000f4000d450800030b0700c0c1d241034921610f2140c4540002402519240344 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 303705872 1250 303704622 303704651
    0x50904031d0a06170a051e06030703080c030301090b0418020d0606080f010e1b0603190b0a090f140705032a0d152c07030209030a06051f0f0504 63
    0x202410000414840d08075403030309400762400c02e4031015600d000e4403004c00078800c81100d00c00c40f0f00841c08817074a84d541c1030014103a802c000d071000b0449605406050b100000107017510300500009140c48028503140d6045c401904110b810040380c1510035410b14a80d080101c4c40c88201c40840c0382c0648502c4002406420250064a29540911f913a4803985c065400030082c198444a83e421f114030a40c0c102c0b040190b22812002d250444040e4407c0c02000403a05132440004540728010a000c3d01050300700b624000036515048035405482d826448809070040010107119420740d820b0520240742c6030f404d2003803006145000003003004035170612203030915260f5144803444a02c180341c00382e100355170341d019801c40e01c0150030400c3d02c82d007842c210703048041080b00c400c828070f0041c08000703040f002a40075002e030200340b12207000e03100d00141507080016904648050000100b0240190404185803c0884024200c5203030b034403080c070511180603070902c031601d00d90f840e41e42240c801b1900030681404000d0320 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 303707122 1250 303705872 303705917
    0x15010b1b0a051b130204081002130909080a1e090b1c05010306091202120313021f110c042a0201020f04120c051c0f0503090307030c0e010f05090403 65
    0x181043c416011010741020b100141e00d01c507500309444450a82d81c26090200c141c1c0a940100c41041c0c00c503408003540c009082c3e020748100c81d40502c2c00749005680712484c0003100c90300340041d11a00300004e01c0c5081144c01419174801c86000f102420076048982c40001d2008666025010207180000790002c04c00e400c0e00d0303580c0070401c0089000c02465070740f49044130042844200860300d407541c40c517400c01c0960010408070b0400e1b200501042c035555451041c403445d4203a191040340d00001c0d5121448201c0c01111400390542001d8588401d403040e9545000e10388402c00145504c220b0410032010242080c140c1011300541d00d0811980c4003001d41030090340640101207410321a401d0104001500c109071500e04017129008401c001c400b2525842400017182d0300d55500540c0204000201c40040e48044601d05014000c0060340e00700101000020300305103040e802680e80a00d103600c28400e00d0140401c860042c184580c88100711450301c000b046114000800207803e010700081481551b41c1400700 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 303708372 1250 303707122 303707143
    0xa1a06032206060b040b070c1401080403030506031002030a0f0b0405011a03042d0b09070f050603070207211407060c03050f09040617060a06031113020f0a020c0315010b1b 75
    0x403441c0c5c45e0b40e2900c01c2101030fa0000c0c40c090b900d01421000000e0800003115000303070152410b0b0348044c0c1d642c0d9251411303005420060680364242c0300e180090b5402c2c81c05032002e1405804200c0d0003081c13030146070340e941007920400d03071016210398a880010016403641544120408410591450302e0b9a518206000360400c5074601120449040800055035070322564021742e11071065803216441d0b00e40b1013169a407690240207032045180900010301582c0380c01000307194072040d248101c6081039200d42c0c0501d112a510800380402e01c0146c5800010400e0850001485203130380710042c51268a4610020290501d07940c016040c4107001880301140f0301c89100b240c0d50040041c10a22929a442204414202e0001001110f60003800e01045c0c83c0251b502038503003141e4000c0d400e0000c014081081060030b4221180b01441594200303c0b800340107400030080c00c1d04881c0c940252002081c00d1050500b4031094001a000c20220840180545155501a81d00300d18511640c140b02e0000341e408a454580d6a0302d = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 303709622 1250 303708372 303708389
    0x100506180a121a0901020901090611031909080706030207080a18270e0f0a021903061e45021305160c02130f060e0a1a0603220606 57
    0x5640081c000f24a2210194940a690121140d039070070780c9050807400350030030580c00592561420424240b069902e81407192a5005980c54060340381c0e544055503012f03da008001c175510701d000b044403800907c010401000d403402d0079840c1402a5441000500c5611070700d10a100c61104402500d14449601c0070240071243c9440000080780480e2030306440301c068142a000c1e0406111919051000c10b44591200110303004056564055003005030803086030f40c001a60b074044640000201c1c0e010301500c28400c15807944002007a49840c00d001c00d82da4950f254803c482c0207042e01e80300030140b200e07415002450300d0049504040c0c05150944c0c100c1040040654051608a6504513100703859001e103018961102c1c22029100501302e0981f080c0820900c080d6019258135100c45c0049201d8012400d44500c20300c0008404c0d454081003505c2640a07501004401e9403000000000b400703454171140380c1c041c11500f0508610342481d81c900e0440f540050220002c41c0590b10a0070070034540c00a5014002c0207 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 303710872 1250 303709622 303709649
    0x7020f060d1805030723060604050703200d060e0c030c09040605090708160f090612091703150a030807080717190e09070212130305160e100506180a 65
    0x3820404d649802465050ba545000e81c00d5011112522060000126541c1005008190b60308030800c001031800400620605849559003008000003074605004006407103e019264904c0e901d0060444286400480007070102d04180030003161078000f92903004552045007a954803404000c1006804158001c2c0d400000c10707001e200302150040142ea00c1031800c2188400b1084c4950011501e000030031040e200801d080340010722030f56110b00c901d02032442084101080c0c0c0103281d5504010010301013140201c007000030050144810203100800102c0504560903a46a421a1500c050503c80c41074010710004000481204200d2441c510b00d050340c21580341140c480c13100c82038000118103c01c140f2400206100380b030038404c2c9001c45802e401203070310b68014908900040d00002980d40080e03000c0032400804000000099400c108031901100b0071413201e0407051400100381b0112001800d017018011111006118030b071110015100d0021580721072814800070361001c20510300080d04000c0c2000080d = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 303712122 1250 303710872 303710921
    0x702120a080d0515010309030f03020c010615090816150c0201031d0c0f091302040905031b1b010302071115040f031a090601031a060a0902180f0102010207020f060d 72
    0x143c1d4030041c41000c00c0e0107a0078241101000440407100700d8680100070914800c5601c1c0c20520950160417030070b2683d000003a0341500c0d0001c2001c044c0380c10344c1001c00200624000d0107015000e00c06851028401c0c4402c88101e401d00d00301050b82c041040340d00d401c101c0c08185003c19a84070b500007580b456802d545401c0f4002e18004003640754490720a105014800c04004020344e4105400f100c0d20458950f81040031068250742004080c00c0b100c0010303921480300744a6100c612900851035242c500c003220050041c0d05103240307110100505500c01a0502d4030511516010401c0100b00b6460402d048620007138000c0c1d80c1044240c00d02550b0070003402841c0000d0040108001d60403604000d10708140b1042669441d1100381b665050240402042021240d80d0075404c003180d02c04154000000426a4030155101c9041000b04c2c2c00200404014070b2000c0100849820300a0000c4007521081c8001c2d49030059a4010808a00e00040c0485c021440024200c1d0550180c3d032042c850204001d4021071540340 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 303713372 1250 303712122 303712147
    0x31b030e010806030c0d0b040201050f1804060e040b180102040b0417120c030d05040501020d0912080108121806070501050403050a08250309230706080a110702120a08 73
    0x6601140d41e02040b50071010820078900001c14a0380ca40006042481c10201030380e03042c1404001400480c1808800d22512095031041c5015249584050f01d1140d402c103540b20400065038101d9200d0215001c030b6034207220100c0c60301c803035281d03008248040520404e940603010724024400ca13400030b00790002c01308010800c40c41d211a46000405860125103005021403c2001701d841000c10205881c2c1c02002031a8036422150001c40d40302d4010380005003000e20f036400700020b40302036143c100ca690340501820f000e4950040c070010f014145ca20010108041410007110092044001358190100400011082540c43c0c1c000c48680e60362250080c08281400e14011b01141c104007001c0b4049103c0c4000100c0c210000500104103258601c0b00301d01c0524000d03020307001810700c890f09550b41926600c17202210812035211003802c101d070800030701c045481c00c2c0f4010b2132000044e19002c0a00d04000d40081c5c0e20643c0c1080d18081501100c0220801d0240742c01d6500d4284240001040401f000c26880712084 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 303714622 1250 303713372 303713387
    0x903050c040606020d0f09120f050d030905190f050106030b091b0105070807021306060f0212030402030601051216090b040f021e090f120a050c0d0519031b03 69
    0x9105604550140019a04110540301039004080040c4c3c0030a4030040082d2003050182c010703540e0707824404035698a0300d86140d0340d21442101500c014145c15503440401600700b000900360700740c42ca0104032001259840700c0e1103407070380d520418050840380d000c0d0060010200c004d1041c1503204008102d05903691400d11041074040316041d200d409135000c2038030300c080404a40182c240e0165507881c640038003070740c0f00a16500042c000703903003001c004032406c1d080d0781c0c4a00c18000541002d8580b0200c044100314000d06d001068070359110110424010300c001a140000c94606655080706e80790103140400d88400e03d4140490b01d0302d0039060032907130002024400c0b6800341d004101e058406100304460310f220380080e8840c840020051401401440c204100d0070300180035840d400420800f444140700001480e1041e164400a50940080f402401000300c00c01c5228148141a2030700c3c98040b110303031101d50301c846c210400c4100020403803569104140c414000b4100040040100d541e1461041c14000c1084 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 303715872 1250 303714622 303714629
    0x16060c0509130c0f080c4305100905030d0e030f03070e030d0f02060610120905060a060e1015030204030c170d0302042319030b090d0918051003080a09 66
    0x511101945082c50300c5001403900c681b0401d503a1910b0166043c40000e0f4100b04014220152036552550070000c04c0140b2000301c0c507003000c02d034251942d1356504001c4d04012442843c451014030b030a015000041001c002d4035400c205021740000e51052610703400e420340c07060840310412010f00108200e49503403c90b000d080408401c0c1c0803251607681c10310302694542c1c64080c0d400c0159220600140361032500a9411068194900c3c0900346032060fa546071050395400841251141c00080400840080c0c0c1c0c03150038000c102181c0008880c1c1000d50030980f01099a010b80c050040000c0f1030310f15844d0280c1c0441c0e00640c4e02c02c846404503580d843c1c511094a400c01e414210714003400a8100e4628442d0082c1c0302692101d40700c1d1583c90b1035210741d415809180f10f1030302c0d410924041d4207242c011019000c3c88011402000664668a8002140c90030000321103019803ccc800304100c14400d04007860720315116120603940001e00c2d43c841100903031324505190f200a001200008500b40040e0340040854100d = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 303717122 1250 303715872 303715877
    0x40806040507080c0f09041b0b0d0f091113060e0f040605071e050903011b0305010f0902040e0402120a0212030a030e0a0807061e02030901060e07030216060c0509130c 73
    0x18640c80f800842c1e200d1681c4500f5991041c0340d407040c40e00710315000382950b03005441080d949450000800d0300c041441c0031a07010340a13075000464010701800050048800161040400700440c030200d030780b542081320708103030101e0080c560482d107000c0c60f030140d601c00e40140405419982e41071030100d081d0300a00c0c0c070482e8119411030401c80800c4055001e5a01c404a0250107103030000e07214a086811501600505034003036040d0348403503111556021010390034046400555001c601507040c0000b416110807142c0c0306020203841004100025020629802d41290781180d0003034119800004040c41c02401c0701000e075100300d200c3d8100d010054000000c04031111280c0701400701030050201540c48801840000c3d04644041000ca400181150302c025111480c11404424a20040f138460040740c2044038220799a82d569070b810301041490307448855008040f8034003503141020503840b180640c4040c1c14001c1800303484210100503a4003c40a40c4c0e40c000014100744000c03130030b00c80000050801000700401 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 303718372 1250 303717122 303717133
    0xa0b01031208100302010809010216051c020703030e0418080d0501061e0c020f03151005041b0f23220b070f0f03090e09010203070801090506030a020f0a0b0408060405 73
    0x4050003040e510f88901140d2070880115841c5070010359030385800410480360355508200041f02d00f003055403c00240c41c0560000c00c910113400810130004400100c100c419548100300810009500640e00010908165030100d40045c412034a0100b8a0306904010500940030401070024901540014101c0e00141e5440c0180c1c850f2003050354600c00800c1184001559018010b000750402c0e55003035141d42009000c0302d5805c55805c15030041c185d8290352400c049000c02804001d1031406004039030075240084542d40c000b5042100180900c4001c40c0c0380300c240541c07400d98040d8110300c224201e04a2a04048180d92200451607942c0001014078542e82e52115181020406103200c07000c2c0c8601c944d011b40342d004810300c0c40e280c0d00c0103140e80d60011401c001c1451400304400240107407842c0515181c800240e00d0b814040c601600c41c50703050300b08482d01440e00040120603079000560242c5103805882d4180c2540281001c82d00c1ca0585404c100b140000000d0001600322001400501c0303203000c1c109490 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 303719622 1250 303718372 303718403
    0x2010b21070906171c3c020d020c0306070e09040620070204150b0703120b0406030f1416060c030e04050c071403120a020a030f0e010605100813060c020f0a0b0103 71
    0x5e98051080c3c441000082c1d03000300341880000044600200c0702d4902010400c24001001484104094092400300582201031a610340c141c0421900d18000401c50290917945444080180516000c4018510400e031020200d0180641540300ea1440f81e03041000f009200d0704201d500302c481c0e1046000301d0055140c45600d40c1c0c082135800c00785c000d44100c0c6071400d1600340203445c2141c000816401d40d61000d5991512549660340d544203040c0110700c500b00140080400d4100416011480e04600d0071075004002403141285003070703010006490349418100452030b064141110302c0c29041c0441c030303003080c684818060540790080140004a220301000da00c483d008a00c03d075240c0c058420694840b10014020580c08036203a00500f14440d950300c1c000035802600039410701074810707266003614035955501c0203200504140141540051103420610ba19040082c0b41e9100e100111710007600407a540c403082c4071036910038044800103001c0703041100c3c65188130303080031584106c0070311080b52404855041c18 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 303720872 1250 303719622 303719653
    0x2d160203070c1203111903030e03120a020307020c12060405161202130b062109030702010806040e0f0313090605220e030f0706090b0702010b2107090617 67
    0x9510056000112148051030600f40e00c1d43e001103d903049050142801d44035015150801c513104540151081d0085218080c0c100641164046410458690400c001015003010300400d943d030000c484c5007005a0780e6446a40c22410801c55050b0140d2210722000c1c00c102464001030002d008034000c409a0b82c00c03107405502302006003100c0c81021802202540380002528100244d004040c86c042c02c0030608240c8600000e41e00e503c2455a441641c0d4510381b21420b1600b01102c0ea43e2002181004620b0804541c002814004c401030202d0300c55070f2200c40c1140000c40230b00c50626105030810407662540803031002c400a20040d401504081d0b840c0040000e418500001c00410150305e0201d80e21009000d036a000001e44018490748000b884208011450f504030300d402850003502032200000c1030043d510341304030840c030060119411617040c0380c0e0140659a035060000d4108418402d24601d4100202d0500d042c480300f0761028029070700e06800081d80d000305d0b60208505990780310a440d581e0603113070300c0f1 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 303722122 1250 303720872 303720877
    0x9050a140a0b01030813090c1d06040f090515060f0a030b030a020a15090b0d0b09100608010b07060612060b03010b0d0b071206030203030d0b0114030f0c032d160203 72
    0x241065040b08010000704207074100034550752411841084000d901d83c2410015111315035a0b1000145030102e0043d2000504500c001d03980400f00c40e054906450001d030034805039180c0c000c44a0460b501c1c004079074074448140007401800b802404040d1a280d540a1402e081d4200d030143e80c02090801c03d209209240c0803034007201e83c60b8000c0451039018101100001030681800b43c100501c80240030102d540d107421405821141211b010220f848048170040c001e1a46014103c4089000b48013003d00100e0b0300551120306440106c1162078a40e01e0504040019182950010904161426481c0c06220303180d04210481e00c0107800902c0003002da00e0920550340c92026020300141440750128031000d11a03548888003031001140030801c2034894001070700355448034041c000320071f903142072004c420350704a41002984040304015608501d401c207068815450000c3c8501031480c0000002500101000e101034015008111951000110019180c0702035100b9180418009580107800460a200004 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 303723372 1250 303722122 303722143
    0x8031008030c060711100e030c010f050c04090e190606090e0a021f2304150203030403020c1012090b010f150207030b060f03060a050f010b0403020108040b1909050a14 73
    0x100f18564440100b207076040b0492403441c980f40242410700000b54110300070041c80c40b468001460356660140111400c403041610800c00c45410300d0204064401c400301039a045608640c4003141120141481904007000e01080125030382c2d80016020900c005d42d0701c003030300343c450108040103000001d8262603520090480000c2d03000e11900d10b029480340d2204402a01c500850070700401c3c9040c0c101d4402c2140905000414540c54082010811100984510140800303540095032641c141901c0c002c2d21540c41070805800b420003000110036140c41200344860708100c500c400c0101117802d18005c1d000301c01c207201e04c1d81e8400b41d0850114900314024402200b65005800900405146590b001d0140400070031455202c008800c814000340c900b404201e1044112400000f07107845c101400c09075015040c0c2105400f408180b0007840141d80001030f1503001a0030414a001a590b0b5039051035485413445005408107081c07005000421600041c0802ca4920a14414001e01c00d090445907692440d1038 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 303724622 1250 303723372 303723397
    0xc09130203040f140f030c0606030601050910230a1509060905060d0f020c0307030c030305070203030c12090a020a0810060905090c0d0302010e0106060816091419050d0803100803 78
    0x2243c00c0c000703001d045400445054040035114100114041581503401010706104950401001c00030300e803a040c840d480c0507013000c0740d10b041d5605001d521483c4514860040060500c0014548000300b03c0c1d8000118120f00010244124103448200c59040040c60f41e400e00041144050045141c501601100741900c002510150404100329091800741000050035200598200100307402c5080520080c10024004e88403802040c40700c3c078004007243e0006000c40c00311b400c10710601446500c040105c48003901442d24684903912005205c604150011800a5106000340c00004a0300c4001c100110b030400c0c42c00c0c00704840c2e03503619022419140c00302c60a140079040038407a00e099142800c40029420301900c000106140b80801d881e0840c0c130b05801440c0481d5510381000f407400300c21046400c1c603442624180b01001e2805c2c0b20540e0810501c0d449a111354400c00707c003040303581c000e4070301d80051030004c00c1c40e148002c0c14106001140d1042c0e4080400c40702800d408650f0346000801c4420506401 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 303725872 1250 303724622 303724643
    0x11508012a0507020f0312070516080d0302072a06030b030105100603230103050c0a120b040b13050a0605100f031106090d02030a0501050f060d02090c0903070e0c0913020304 76
    0x898102d6981d0b000302c508a0740003c03d110408010740301005618042d400c203105180e035136142c90800b1403420504030b0903004041201001400341e40c40c0800c0180220b1414140581c50380800c2c505141d40454007070900382d04030600e031a000c1c480c1554031001e9040318140c0d1410010074500030249400e0740c2d070444e0445215104074a04201ca0fa21903445100d050300000c00c1030540e136070381c5410702010a4003a8000c1ea8240d1041e0540d003000e18040d10014014204007010200c06c200d265201b00840900070301c0500210504c4001450360324544400c41510340d401020384648040c1c52812000034007042d2070307107c1d5200d111800031940003c540800020340c0d81094411a90040303180c101f1419a01410315a600300b581d0344910001a28100065041349208900204a0713190009550115440061943d4422811201e2003405030b180e00041d150401601d48106548111a01c003082c42c1c41e01d203a01040005483d070003003091690200d00030b07148007081224510010038042e4480d4050703000541d4090022140c4 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 303727122 1250 303725872 303725951
    0x120c0e01170a2c010f0b0d060507030f0903021606080c030a15030c0e06030d0e21010b0306180706030c1e022109040501050904031e0c0501150801 64
    0xd80034000d5101c55601e0001c200c1d0030b45800c074000202490b012030018283c2c02c01d1140301c405000e0080105800301e0240801032007202d0030000d0f0102070360714005401c0d555514040307200c0a00c00d4000700450201d094050022140364500250355003204180d900c0071628403040827130300354810422039001745c40b0b5400e0710f800c64944054880081c076075a2100d0b141c0340303c20309000001401061804c0010050399200c880035103414070a060405104a261408100f5032024100f1507503a400c698181e0b081071065a00e00422842c01e200d4018100801c44d164984640d200f00022502100b410300301c004c25400590301d02c96601e4800750241c0d20003000700c0000c1006816580300b00c01c00007030740201c1368066104032050510302245072151015080a210702045001501c880641840d0003042d004050a0380e0461079440c1c01c1d1401032465003d5108204410020b520b0200c03041d210b0342c40100841c3e000030080208100c03404810158203440d1046000300d5080c10318100001034555401c8040c9644480080c3c2822078 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 303728372 1250 303727122 303727157
    0x1701090c05120a0b21060702011118030c0d0609120203030f1311120303011a041503020a051b030306120c031e07090f052e060e060f0a120c0e01 63
    0x140104110240740e40e51313414040f0790f07440070301c610702c200310350510094407001d002221801d02c05c3c0101400f082d6030500000c07a224603507035400c907400260f00d01c210714403011510002034104140c1024071648040b0350340e00d0505110440e440501d5051203200624540e40c030928040e6200d0000711605405a802d040c00140c0c20394140c4011901c1c0341c0300d1811540301909031000175210344443d00610140f588007100501c0b19406a0448100c001441c66141d4180ba00c0e00b50480c201c90924240d20040580214107250058000c0054807800c550001c40302c1e150700e26015540b69250800c455007489004482000b0b4000c0030045034500e141c58015014000c029088192644490b03040c66100406204015001400c4103151254210301c49000d480814141001c881000310840000131440007500c03a20502c81d401740548200100700c070300a0421994000000c40004d02e103018170b070140066601b000880b40f00c0c41d41c0c0984591100c45040d141003000c038041c2d1000b00c0b09400201200e60102d4468602101c5042 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 303729622 1250 303728372 303728407
    0x10f0e18030723121c020c070608041716020405043809070602030d0b0d08041503052503050a060f081e1f02070309030803071701090c05 60
    0x54251404080c05006586407565010000a40d0503140c0d00c9901c01d0340c0c1500265842d00510510020a412a5482c0034a41c40340b0403614000701d2500140302c58400c0e0003c40e0141c9048281240954140703076501c041c042c5c00e03d0b008880131203c002c1d840b0045a2101c200c04203641190400c21404c01d0a164107034240402403402600a07107900180c0c90407141c1c2e10b01c0d4903a02c0b0350082e111403450003d500d80480510101a80580240c1d0141c000e501d0901440da800030075900c0d10340318000c02090b06500880410108041c40d1400f070407400300064041610302c084d90301500d03103403666a000c00032a964400084450308024046001103101031900c01500307842500031580145041d14001169a03480a5403403518185612583d802c1d000003126010b2807000040403620031111202820341c40b00000342d000c40141c00340b000f02540301d0340402c403d414035114004c0440074540c01a5070590302e003000c0300c01520300744820315000030004602d0004070f540c2c54180186113101e882c503250142420b1142c01c04c4118038 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 303730872 1250 303729622 303729631
    0x92b060f0504080405060a0e090916050907021c050915090f0415060e18100e1e0c0a030e061807080c130203190912110105040201020706030518070f060207050306010f0e 74
    0x23501030780960096030b4a00c22030340640302c04c0d4003c007964421a810700c004040349602c01e40c8603018800800406079004125054810400000050710030302c00703141034815002e0114056040007440c0907002001c1c0c200343c014200c18a0483c0c0070210101d00000b0001514840d44008d40040240d540401a0038050b0305900f880520040403050b071240040d080c240e0b4440c3c216041e0f8a0055191020000d0055418110b50080c06040c0010902c8a0043d44030101240140001d0741c0c10400066540b403462003507101c281510038030740540750241490b080041101042d40e00303d2080f0300401d00001100c040c0005c00d031084007000360a21361403486444040c4000c1d080100400309094402d0000c9801d00803a104217643e462042003800001d502020005041040000d003c82a507850f0005020150b81c0000700315084404a10340881c0c16030394010821000d0303a0400020281d072141c03150200b415055042c01000741d9a196084030221a074450802d6a107400030b1113400d90504212a0034043c42c0c1c0c2480380c49034803 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 303732122 1250 303730872 303730877
    0xb0105070f0503121f050d0602090d060506091f12030c0206030708100f030b1302040227040f0c211811030105180c06092b060f0504080405060a 63
    0x90010300d856070040c28600010489150304000360032141d809803041d00c40d80051074010340065220b0400c90900002c401802003911a2441d42041c03030030800c0a404490144c90007803c0451205042d02d0880d015041c01e490700f912071110540001c10121400b507000000c545c03145404901c151074242e4900359141c01d02e105404109040c126200540c0722400250b009a08959660049180de6612402515003e070404024540442410400b1403050085160841e20706403407503040110703a2002500900c01d6200c6032160024030b544004500101c00c12003201544240d4080c00391300018540101214921f080c280041443d61013452111246243d0149140c00030980c002031007024842c2040041045000484981e4038604101945007801e000b2581c02c20715680814072404a0444460340392101440d0581c01120041400d10f000d540c0c150342c02c030044240b401959103002080da400c1d521411651000c0d10002d0801000c807400200b50f101e180e2049030004c0f031007414613080c101080840e0b0b200c81c5c251801c = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 303733372 1250 303732122 303732127
    0xd060806061e03070e01060807081e010509060d060501060f080a020316080a020f040e070f02010603231006030303020c161a181002070f091109150403050604060b1e130b0105 76
    0x11744907060070500c1e020b440302d91121022844c2880004054041c0188840c4030b45000440940083c1d029010b41415149c049403030107016540c01000c2007169800120140c02d040c14200002441d9402140c3c0e500b41140c9030f5140c20b141e03900d07854400181d10040e40d00190354046040081e40c05031040002a17003005140380d02510b0b05d900e204a102191700032f0f4100e91480601c0c20140005103800500b8072010440a00090100030300e9a100c10131082c0510305e003070300301d886080c3c03c1000c1b030341040c4061040d14001c9603041028a4a0b42401402904031005801d418440e00c0c080315001000355140008031200c5000411001da010150854143c001d840729020b483c0007100c500c00d0f9030740c2c0c0079280f0f0a03140791780d4010242c05242c840000c90140382940030000d2185401200101000094119844207400383c1d2105480c458403a09250244910392000d441806880244800c002d1113400c8400c040c00f013200d00b1003030281501c603800100c1e0104441c140d4800c2280391011960f400c0740c0c00284400302c05040490 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 303734622 1250 303733372 303733379
    0x80a030c02030c06010807050a15080105010f1202030c120c07080306130e0d08041b0810091e150b0f030a12020705031f18260403170d060806061e0307 66
    0x2840d141084e00300d246e1030307003042505101034240f030341c0480e0061601a003080c20018841c2800741c0001d106000316410042801d100440c01070281411500c40f06031560119500d02e0000341120060b0403c80d036000e0102c601d000031a507424021002e40b40341542000515195495250400103ca05081c0c11480081d48a0311699900041803040da0103002180d1601d81142c40d251400c0405161400441c0310b4100700d2000510290400084006140c049010005550961410103290b0400c1d141101410200b44540c0e820030000000c102c10300d55400d140041c002008010f0801183c0420307000e1094144d40200710500c040343c07401e17600701001061801541c4001c0c0c0c81e0b102203801c00c2c0c3c40ea2402d42508541c0c02203a0540a1517124042c000c1c0059a5198050071031076445005032000c0c42101e0604070302041042042045481c2218011680111841080d5048544090f0b51b40c11000005621a04d8158001880c3c01c0120b41c0902c00c1c24000c0c644028503114100e03c45505182c0c0c0709107509407184c5070010 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 303735872 1250 303734622 303734647
    0x14041104150c080d050702152a040e01080304090c0804020d0602210a0e07090c020a03110c04061211040b01092c15030d020f031e0d14100501050304080a030c0203 71
    0x1131030200550600454203241101d4040c0c40d01071017030224264420400e0411910560510f000030950070025038005148049072064403650050303412912401341440e000089008000004000700c80440100744a519481542070318494802c03940690015607996490000404135401403101440020750942c3c0130b00c3d010000c0d48100400c4600c1c0d01040e99444030740c03901c140204041002405000c10034401d841c1c4d2400000d444903603049005040c80307680241000011001e0060300e040c00f038060002c120055407040c0c581422500c401301540c80010094410859050a00541a42140c1a11401ca10601d0000850404c509164140c2042c01c405038402c0302170045070f415103010302c05212554880001032420103003000c241210340d40c150351000c59040b40140c4040160340340481c00d90a400344016440d0014012440b6800304204124503081d8140c8041d00c00e451554041c0c00d80020f481e52135503e440040d01e00e84000c1d54003912101c4140204d0150300e00c00d410041c03022809205480c100803c4c1c1c6e851 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 303737122 1250 303735872 303735877
    0x3090218160914030c0f0a080a0b070807020309030c010e060c1504110607110405062106090f0102180411071509021008040827060a02010614041104150c08 68
    0x241c8081404108109640c1e074001400c01c05060101d2500552038581c1c80041d80d030fa694008003d000324145001d080da260760ba4000440140001d409403019204107150006034901c0072101040401c002c0c00104465510000c262440c650024004058580d108401559007840d82a0001c1c0e025004009992029005100d006205002c20080c04482c1c1003a10301008241650390895000380004c0c080b41000c10141203c1e800500416180014580c4980b40461400c58a074843c00200b184a00d1000791690070015410b4400e16020303051341d0741121910440d500780d110740303022380c020900030a0a006c0315103059408442841c0d80d079a01c1c185405500d41c1c82070703003462010300340c0c4e64415900c0c00701c0c4040d4149503807140d40040c8940b500703180b03c3c1390039070381d100e0680246030400081903810b030f852900000d80313081c0c0c110f05440700070b00c1180c070b84207283d100034041e029500032122039002100381a40c0c541424050045044810010f1606290a161148c6030780200e00c02c40104100c0011000c4000c070302d00781c00 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 303738372 1250 303737122 303737131
    0x141213170f03040c050607030804080702030a0602120a0b12030f13171c02010221101802090f0a03050a0803100315060303080f0105150714060106020705130c02030a03090218 76
    0x10501d49903e42810301140301c241c42d911090090b03d0401802c0002580702031140d61003640284180d0b00c650050000c40d2030214a03400042c4640d10015100b4615a200310040d407040014900030300c03000c6000f40900480b61204011001940d0042c804a8021110740025000001301101c064040590361201c4080c1d0858131081d90314150440444404000c00018001e0f4243d40240020b61034441801e4400641d01080988010400c0486004c5503004194004000040000c0e20720441004074240842c03000754040c01c4486d02c0b64a00c07005d0380710541031010300c450840e07400c070300540100c03c000c1d02c03003601d41d900c01000b2103041c80c0c5041000c00046e41400509070300c0e6105034400150f040c1141f03000740080074050b0450750542862401040349a80b403d8800000c6d4070030120550f2100418030303111030b0b03200039903100d40502d0091500200b0707100d84c005441411114101c0b10070500400074002d610850340503280d0b9400581003000030314900f50080d000a940b175440074108081000801a00800d551010303079 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 303739622 1250 303738372 303738397
    0x705040609060306080a03030e030d050f010f091b0c03021c02100b040b2d060705060702120a05030402010818010219030e0c22090c0f030314121317 65
    0x2405000180c0d200044801602d0181410445242003a11480e0307501480d010050405840b41c3e0a8844c40e10180b040d00c4008230f4004003400281808018001d07200801d001d000c2c411076803020009032070b49150050340c4941d81c14801c01c0155040744d1301c04540300030310284c069096100d4200030b0881941003035840e4210b20840d43c05403002c00c91041c0715100f43e41c01c0a80061156040c2a00802259074950700001104011810123441d124001450b00200d442514042e902c1034010070310304280513000c11400d1048030542d00741d540030b000d2410202914015000450001107081c000a8010f50007150841e4100c6040c0180340d54100c031006409003a0392100120440f08000701c00800240c0d60940910410140000c0103010601c01c07840214400c55001d5958407201c04081d130062842030400c2e407045d5010341e08184a60300240c0c907448450042410f902c0100c00141900200e28090a4030005407100c1040c40e03000082103864400b224010008134076070603650240d44010019075018004001c5c05c60702ca03c203 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 303740872 1250 303739622 303739627
    0xa05041707110405060d1109040309050406061709010c120c03021603030e1e100b060705011506091d040f03032403020a0b030906010e041a04060f180b0a02070501090b0705 75
    0x20b5040c04255040500358030b0080c66800c0c0740c45c0000d03503604070300001400142d0741aa180da0301d5003406c4680234055031045810500d486404250382d640221420402d64622083e0288c549500d0101804c0316490780c0003200285103d152070380c075411160018800c2c80c00034039026080c030009010b01e000002c0071807821004a80e5420001d1003584c01444a8284601400c1c0b07a51071251440342408d44990207900980015079641c07010750056581e140658003017a0b0030400810a10104c503007000080c240740d000d1075000c00e00b41c0500007000f050f121403010381c020b0704c4060b0700501d8a4a940d01411340410401c100c05050710b40c10a4054080c45510040b200c18002c03007550074161031401800035650050300100410344080042110700300e40018100d0441743c21485c101c02d40c1d078650805045801d20801f0840d0343c4d48102c0248020b02c130450f0400300804101e5501004500d0091039030025030400600000e0841c0303403c00014900c042d89502800303046001e40300100311030246a0324414001070494100c0e01040f4007 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 303742122 1250 303740872 303740903
    0x13210212060f0a0c020a080c0f0f07180c02190b0a0c03052502031b0102030f0c1318180507090b010c05060408280909230a05041707 58
    0x20140600860034400050161070502441a0071030b2400101007401e071540300d0715840c291074800c22641d5142500301d0010b544419900801390b0311100e00c2000c0e4400da10485800300310f00c0350301280c10411140c1100f440d6500111008600005d0000110b1140541c0110034441401e544d1091211004c14400c0070aa0014a0925103401c00c0703444280d80001094138090401c08104c41c1551160303c0c04058a143d802919403402c400c85ca10310480c40410703115883c0f10440104940c0c15009180130388140510001a6640c0103a011300a02808524120b405240f0704200602000c818074400c288100600200b0280d410110840b058103030342c8130403181a80a0a010000d0f22010b102d4042c041c5003d19000380c0fa0303800d540398603540c1d13807000e48042e00702d0b43c000900b5103080011450703590800301070205c1e401c0030000b12013014000e10703c14415600000c1c2048100000c1d03407102003448105035031035030344d00d0a01d440394035800c8018200200b0440754409034400300b03010280204040d00e00d552103501c014010310362 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 303743372 1250 303742122 303742129
    0xa0c0c12051e01090803010b07060914010203060306060f011d0a0801060e061003050105090106110c0a0e040b1006050a0804020409050115060315060903030f0314070e03061605030408132102 83
    0x200d07000541841c0c1d241102c1300c000074020101716411501c0110241e511121182810f5005000c1c1400040084d40f506160100c0c0a40c10340103184100c1007201525003030740d01d03074003400580b0b10450380c1c150010f121020b00c403106488000f006001d981002c1e051000e095182c040c3c050031100b4507048420810307003860401000e031526617422030300840c0900c1c09020552401c0e0120385012818040c0d0018401d9240442c92210802c003c12042100014400d06405c0d646d0000c030032402c1c82c00e50701601c54480da04000f414411442c0404003c131141d0f6510319107070502c031007007c494086000c0c0040f03a0083e1110b07182d00124000f400b03100e0404003032080a40380a490081c000c2c003104c051440c00c60102e408100f041004540005510045030340609040c80e0000c1302890031001040d02610f0880d503c20441c0600c0081c6510940c060307c20131090b01204c3c0140c6403035515400d9103112400310b000060040000400113444540035009014000303401a911a455868641c0b000300c4502c4440c10307a140300e811140a518 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 303744622 1250 303743372 303743413
    0x6051803070f12030509062802010b0303030a1e0903030b0a061d090a1b031b1d010c140303070804020f09060904020103150f1404050f07050a0c0c1205 66
    0x9411401042024540340a41103407111500c240d08103807040c1c010140505000b00212407494100500b03039540d4042d05500300d05c0c40402c1d210213040d080404048801c20314014821202c1545008008604594615440e9070180c03e00015854140306210051a8803600d180240038240b8401e031070200d6648040742c10f1000350b0034240e011808002c1c800381e031903048411a0124401400d425100107030300e5a107142da0500905089100c00310791703200240705401810317070552200303180c0e0000c1100030003125030760f410458100c80300f0120000710aa40d007002850940c000c62441c0c6215100d044c0a10801e0000701005080d500201ca050b400f0a41e400200805c40c070b0416034004080700200c66101480c2801004074a0710600200001e05043d80c508006048080c440300038001440101c01070b8081548425100c070380c0b0841c100249010790b081c04081041e0405a6140c24491401642c030705041540c10a021248490724500544240c012030303c000c030705c005036400c554130ba030703170280c801815500707081c16050740b030390 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 303745872 1250 303744622 303744667
    0x6052e08040f11010504050d0c050f0118210b070905010e0406080c010c020127260307031404031415010806060a09090206040506070b04110102121606060f0605 70
    0x2004200000200100410840580c10880c1d480544552100517a428461034100342d03840300f100f0480108005200c02484262102a2401c4a4045a00c070055a03800800b802c100500c1e01000e405210000761400328180f800c0e41a24007010203135050325000c1c1c90450582d40c02340020740126090080b0750300208001d4840c41c050307a0805c10301c1d1401d800241c40b04601903a6504018004204078250f80c0f2401e84403034510b442c2c030303c448410b8107610301d070402c003442d580710340d0800050101c01c20705032103659001d0f0401d1804c0326000d586400e05aa4049074a00309050014045900038400480840d83c612248000035a1140003805e0f2588e01c1d0407468040720059010380c6d200c3d840801001003a41f60700713621108455044034040303206545840000c0040c00b580c0c001c00d8200501140311014800980b100340e02503409211031301f4240030134000481e2602c008042004a00c8020480a208100c4e800c1d40000e159001d41400240381d83c84803059a84002590320820014030080741d2074401c610b02c0e80c82261301 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 303747122 1250 303745872 303745877
    0x11070b0408100e16091a130e0c0303040305030301030b130b0a0903020105060a140f01020f060703020403121103041205010f140603011a09010b0703090902040f230a0e090106052e 78
    0x107051184d0b04810b140349803400742960003a100c4030f0141032520044264011900024105000c111103807620320000c06000c00ea4601c544101401c8018504010044900766a08000070b145141c1c21900c580d9204a400380c40352402808105481000c40d0743d0400701ca004440509011495000c281402400e480c8080c008621030600c11900b00000891443c42102d00e03c400d07a850340011480500503410715000e1001600c46000321400c008600b030341a801402568800e040c8410400703e42c000c00c6030f4a045c0300c80c001c0b2907540200001e208070410018000000743c8240c001060110302d02c2c0c0c40c030050761402d00b1309881032445081409143d103420702807400c4002d0140307000c07161201c40b00300140d1020018802d941403942d00107600814544038800e04c00107480e2765403081d980c50342e84000c0070f2810490b42c41511513484d0090010b0038141d1501c46a01007185000700440000c90400007000720084010300324911941da5054009820b8030340007100039402c4c85c1d880712620003a5842c0c00451514420305d1010b001c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 303748372 1250 303747122 303747133
    0xd0c080f01060e030d11010209061603110303070504090504060e1b011209080304020d050a022707050c0c0f0303040f060804020415060f0806040b130e070801110a11070b0408100e 78
    0x40c3e6140000c40529001103454402c2c02151840e900c240203101c0d40000c3c0380c1200000441c016042c1c1050034024003c7e2080d9111540100c400700c8135520b9000035200b410021b44104020000030780107801c07054010f8000e91000440404024800e880d05800000801300900c0c035a010900c0ca41c2c0200e04860b2014001d03d00b8440d01803159115401440b000744003d1061110940c41c43c1440b80030031004907420340c054110701814202c950030906001d5100c03140c1801c40100000200704600c94403e4901d165810b40c000c0c40005a03481c20040c410218000103901803100303010000e40e184480d40f500c00100b00c0b60b21401100c1c1054014042950012003c101101c0d01a003020030107140d11520b82d089140c0285044d0380343d500c4204c000b0b0003401c03480780c580e075008c02080c015440c1940c05074002200c4041d042d00302c0d0109a56030700142d091b600c1d40343c00705103002070a01c0681d2007a030041007495040203403001540c03009901d40e903020300307541c0182c0c0160f90aa0f000140c00d0714003a5a130b00c500ca0540c1c038018010310 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 303749622 1250 303748372 303748397
    0x180e0106080a0308190207080309010506060a092601180611070c0513020d020721300b0306011202100314160c060e010f060617010e06060d0c080f0106 66
    0x9540b280700c1e01000341007003840800510501c00f494181c14070604041001d550700e020504003a6090f410a88640005518003c0442ca0510700b103000c4444080881e02d49110031883d140b08103400d0030200010b981e017103c11321845442c4010a202d1030b510400c42c1060320803641224240103080b40d4540314861040070f41000342d080410650200b44017120412600d1520f00d0710711481d00000703801140d46810080f40086006403c120010305402c4541c084185040000c4c155013804480480d0b55091015a94041100300380c0c40b600c032421080c20241c69050301045505450011a00c1d01400364801d08131460040c0c1820214504085000600d101925041c80380e8907407040d1107a5902409047d5103060002c90641c21062401150781000301500007904102c02d52910300d0550203489419100d0880e207281141c0491106c1c082c903200d1212a0880c2083c250b40ea0034101c22003610b21002e889694041c405210250211101d401072a001c11426a0750490506211640303603068101a000201803013040310300301 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 303750872 1250 303749622 303749639
    0x2f1014091f0210060b040b0304020111030c030436050c0705061305210301120c15031b0f02030702040b0d081902100c02190809060c010218010809062a04180e0106 71
    0x151b0584a00c210a44e0ba00d440360310041e00c0a52000400300301a01000c52940044480840503004032154816001500121004501d48003100c0940c0504408841c14117040e8103104c950280381d00401c0d0f40d41c201d14040c0c11ba1105071a01c0c00031501010b04103191181313081041300500420020110032001c2d11000011502d0005107400140100113004140023621024810320303890240c0180350212949480b00e41c0694001d0243c0291040240d0303e05441d560301442e1351040020004003401071340914104202d641c01c02003c3c0048080081d8060740c5c030721030031011404010041c0707805c12254007182080c40041c50301a04041e40922144501454610003c440c2074020074040e0014009030301620688019280c516224000c01894617004900031070401d601240543c0207109903840100414200103000004403401e0074111404489a0011004a52004207500380141c0d120146c880d9403107100030744807181d1030581042d440001c03994160020240164064860904500d401400a000d05400c24082 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 303752122 1250 303750872 303750877
    0x4021c0b091e06031c031a0306091002030903040b03090307140c090a0207030201061509030507080c06090603090a120503010302090912041e050301092f1014091f0210060b 75
    0xb50310000e440b00008401e950f060055000c140e0454400b04114401504028000d1042981c2c0d4202486111003070407a40c900002ca8074480c01d51800100659042c64420b01d001e5000584064168401404081642401c1c4005588a0300b0310900564a81c0030b5400c0500d103800050200c2c2c07441e60010014400c182d02e421a000e5448117034070b0000750752000d5270b1a00f00d00601c12a80044040e10420321071180c0d0560181c400800c40f030207581110407481c2c8803225161a104900c2c403060340018104103840c101d06004001d10341c85200032095445250007602e038251801003040d07440d00000e00c004018011071900862340b54021300400014007030a001504480c0c01441240544640045103940390440c3d0f0034101070800242c0405402841800603901d010041e0321640304040c001e90409203503050340c1000c40080c000c035240d40207003141108280c1c01c5050321362100d2407c01d9002c040b410070105946460301c101c00d9042040d4007000c0305e030822080e00001e04048032410380078a9242091001c01038481c4075000e = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 303753372 1250 303752122 303752161
    0x90506030d050702130c0e04110306030304061b0f060209090109021c051f12050c0d050c011412090a030207060e010c1202031e031f0302060304031d04021c0b09 70
    0x2001c6544503d1030001030f100740000702e40420140e082691040744c0d25401000c0301515082a0340910a0300b000c1555188140012504550198400e0208001191140801c83c403444424420341003030305819100c4001d07295603004140d86081e00042e50881a080010b61180105aa02411410b01042840c2e000c100410340c231000d901e40d03482e00c010403a0440743c00711000a0390303903030404400542e50385d160808040c03c2e0f00380140c80500500f401c402003810a403424000165114020386002090304005540e00c40d01c013005485601000d00c425420b074100c1c40c0d445c80c001c01030f070401030140782901c1c40c000346401629080442040340080101480d640c100c00d00c001034603448001251000017099080345035009a034507441c01c2800030020b0440000c0d4001c005d5008400b500f83c449030000075a070003000100054400290018020400900032038420000b030015850a150f980a80301503020020301640c1080b5844181d0301c034145071203040701d51359100d15100010b09691541c0c0d1850800d0b01d10310040c09010 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 303754622 1250 303753372 303753377
    0x51b010f0809010b0a0314070e0601140c07120614070f0e0f06070b0f01061b020d1b0b0408070807290a122c010e03030a0b1f020303040c090506030d 65
    0x10301081400c082900442c00c04d250181905003817607a6030170401300d0441c442003481c185004003940030980141c1c205032248a4401a1a044802c807403224030864150b1041c0c5070a041c6000300000841d201c0002a50341149c90f00070348005c200d50410b19420340c845180502843c00303000c807407810004107980042c02868418012600301c00d0209103400807034494840d600c1d0051051410204006060264240c40c0f8140d500c5a40c40020056031280e44250f1005032500181d072002d81c00c075041c80018002d005100e00f0001a480700345100e0784e10045c400903504a42c11105858001140502460741d040209170010300e05059200c601603859164100041c80355048200480300018201c228140250070220602c03805035420486640048400901034082102e120346541e0000104207694a05028086022106002551468580c5641c0b00b0042a03904071440d04806040f40c0955110030bc454810b10b0116036801a542da0319003494032980103d19034004c0303a000c0c0c0c03070502480b500c2c0c0c4000490f499112800d0 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 303755872 1250 303754622 303754637
    0x106080601031d101506020601080a0b04050a0203120a021005060609040e16030507030b0115021e15010f050f030f0d0509040b0d11030c010504030f02060304030908030a0507051b010f 80
    0x104041000500d540400107910710808484c00d0443e140c0b40c0c800c08401450214414010392203440413611280b0078480e40d4400e5210360840004203500c42d600641280c0716070210f82c0405002e0303000c82d0610145803101718006c0000708540007e07a806011445074640c0c0340404000d80c0c546034001481902a10345990b002d00e03601c1d0708103001c0070010030405501010107007a40c1d0402d5030ba4a009652201c0380d00003100e942c034841c000016808031076800000a10035a40252090301169500c6030354a480720004da10aa00c82c50710201c0c5e80403046000240a44000c120514020b8240300500080d071817044501e078000d0344030414401003c00082a1488008020314001c0e41e40c0c0060400180682080c081c15540440d490040e58100103000d00340a281501c103405851910245200540e214025444094406c6036158450801490030700c00541d4000e101e1704103000c0032503d4000052440e04030200b6000072400000b403100c00e0207010000c45c650790805201442c0d80c0001100006c1c1013050280420090000c01c = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 303757122 1250 303755872 303755891
    0xa050a0209070212030f1017010b130b01080f040206090607060506190b19020c041803020706030b0604030602070807050105040309060e041104090207150524030d0e010c080702150d14010608060103 86
    0x8100400410480040c0311003050023088840c020b0040200203031081c881d00012030f41e11170031801007100f6040c058550704880e9540c2c030b80c0a80043c0c00207000f2a030128080003180c80d150703a6800035181c0180900c000240601d070a506100c424549440c900122074030401c401c000c80d1034100200c495504c1e441000100da0003c025042c1c2c9803014003480d0545c00381c180001510346055924640d124075000350708079401196a288103404a0301c07000712503908003004100900114919800410086101c2d42c809450a04e1603100c0908645041d1403c80009000031810000241d00404040001500300e4040082e070108051400d841d110740d1007526111030b008614101404032100e40c2c41c1040310003070014012171030b243d5824074903440d64124608101e080300e01601140d0800003900445600d15031924440310112000540d20303964290b03c11280160200b2504006880340c0d02c2a030003e82c2e40440140c1c840c0f40c1c8001c0c0070181c82c81072413046408414039004021566001c2c55030368004000307080014078141d0 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 303758372 1250 303757122 303757141
    0xd060606030f4a0d08090606121e0a06050108161505040909050309040e0c030708070f030219150e040c0305311a1b040810020d06080a050a0209070212030f 68
    0x40c3c00340402c00ca0150388004041650805c41c054414280c1006032821651200204590160012007045860303100821082c20008850a4240080340c84001c40e80d6020081d5500c3d01a620b0176084918550000400c0c18074210a03072584c2005054039241340c20002d5070018004045018500c01e440c10b281d02d80105605014090089071542c00c4040c0c014841c640b5900481c81e954900e0360b0030039002e44070f41800000ca42601044904c140c0d502a1008008640b0395020007000c8410140070030441e0071203031000600c80e2400040398801d00543c0d00e41e00d05000d502c0c0200422076000170300d40c030240740c10502003041003515009120290822240036011441511314803608210f141d401c028510701030725007280030848494041520603205c2c940f40d07000301c05480030444900e008510505900382d0100c0307011454005140c01429003c5000720001500a03a582c030340714504484034105503000c2e00041c0404065050015009500c504207000508a02e044e01100000602c40109000c0c0c4254081c80820414032 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 303759622 1250 303758372 303758501
    0x10221070309081506090702120d0c030b061b0705310f0e01060e0901090819020307081804140c04030b060607020901080d090806130206090d060606030f 67
    0x760020899500c24802d0294144c07070355042c0c1d035180c0300c0c2d03c1800014264500c001820303003104100003c01c505101424a00f000600420b2000c0001d040c4c8580e5010b08070344441e0094100360060340c031103a60050ba0110018204003064003e80d02403443c005a3f0780322101c0c05881180b811180c0ea480482c5c803070481071108000e140d00945a0815030509002850101c1d0540000c4107540c1260503080054a808040038200e95540300d0040c600c88041c40034038101801e0682c8402d4407401e9005a1703141202e65615070300c1d04d41c13000c2c070042584030750017490b6011420148103101c4070304c1c1b100703070241041d040c100e00011181c06148001400c1e191210005072060304d490040e502641d9010303140e80c40d5940c49230085600c41c030b58240040002504400c002071140340000d481c5001c0e030290601d8202a00094083c0521a8460300c0050703000444e40201e040015920302c1540005c210360b41c0c00051150070854268140c90003200081038488000144281620f441e0020b600e84184644030321091100104a096002 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 303760872 1250 303759622 303759629
    0x60c070b13060207080d08010608070e09191505091605120405070812090108010311040e1c110a021309020d05070e0a0e01090b06010503150d120e010221070309 70
    0x51020405040e5020400c40c40750a54902d07030265404251242c103280d5031a48001c5400001a034100d00402c142401910120b410011910b01615070b202100d000c21100c41c4169603645001310f561074980c07000200b600c284403000300c1c0d01c80c40c3c99407249004005200d0800284c0074070048a4200c90352900903014008030b80c3d032241060301d40c545518050401d1038031501c0c01c2c41488102c0c001c4070740004e4055035402c02c845a40b0310584403000e50380d003141c94814898086031641c0340c00558590b03403455462010002443d0580b60880c4d4a22171001c100310040c1007040340341c00e14041394855031042d0010f9650b0411200280240381c800203000360b03140001030111020030702c00742c07180c0900000450f12203650400380b40b25541a070300a01c84009403d800500301d03071400c080074060364500e40100b481c2e50321541c01035400c4200e59500354104000000020400e10011404864600110350b460795120b07044000d42845100900140600c02010000341e88070701c00040c144661080c00052443c2014041c01e880800b6 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 303762122 1250 303760872 303760889
    0x2100e01020a0f0b1005011110020d020903100501050a06050408070b0f070b0f01090b2b03091e050307080115032a0b0c101a09060d080a020601060f03090c05060c07 72
    0x1c0f031281d0605002d0140180c1d065201c0740e090b0760020406500a10390120000c0200f0010421413074035104081c025005041900c100903000c02045296a400704800c0c018814070f0385000402d54584801c01c084044241d110f18180030b0140700400490707401140031400c0b13921407110950b4401e190140340000344640413008280c1c0f1085000d0004030000803c05030b05807113501c44104580700a4604100d03e4103807900300500d94201e941c074940c0c0c0320122a412030003071a220781881c03040648c954400b0300c602d422580900801c0080d80c41c0400841c5410030444d402010340310020013141b030b2554a105a00700b41800f0290a100b000d003c0000c2d00c0890750b049107050003810000801040c1c640d0511035850f400705d2030b401e43e6031080380c00d5208042650320841c03d1010302403600c0c94116804501b441700c100c00041402d5400600c0d080c0690106110400034103a143c01c503070241540390b041c4500580741c002c1050202d810540b4022020000a0b40d00b041001501c00844c0d6454846042540c02c51812003a50000e801 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 303763372 1250 303762122 303762143
    0x80403020d050d020607091202010f09091e050a0c0e011404030c090c020d0242180f0c0306060d08130b18040b0d0b090708060906010501030b01080402100e01020a 71
    0x1800b20101d240c01c000d604070707403d94a41c1d4803180700850f0f010500380aa13078900d92580782950010360080310b038402c02c000d0500b4601d86007603940c908607040fa00f400340c401115521081ca81480c460b0740d03114a03603200034602c20070804601d20400041c0040c410b074030300606111250b28003d080d40c0040742603c006613401820085143e446140d40000b6000c3d40000b84098030071014103000d4940045000c1440c0400d0f208060400d80e00305401003043e13400b280e00080d084003050904503610b54541c03e0144100d649070701c00708414100081c818940b5408801e0380005070400205800c01c2c1d41d001c9412a0400c1c42250700c00102c00d40c85c00c16121a100c0e102c81c00c4001048540d00142d002c1104001c2c04c04c21030954000d03951608040d080c00151f1f0103070b12240348d12081e0071341104002104426800d402c0b403a00000c603024141c5601619240003800da88141e519400340d0010009507916004198110800f0b10b840152801c00e80e022598811a52880c242070005802c100c0801d6442040b0101c0115080b1000e9603 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 303764622 1250 303763372 303763399
    0x7051005011511030a12020d0f061d1e041b0503010903090810020f03010504180f06021c0c0203091201151205060a0e190f020406090e0c010816080408040302 69
    0x1031a454032a20b07040042501c040344081076003400301c10340d08844101e0b151201000201000070000b0351020040c5003c043e40c1c1c88c009000031603c2d00c2400c010349040a002c80e00314172101180f1002c0e00c4006e02015075034001c03020601c00d21001101c0b10780c01992020340740480542c4081c144600310000c0d00019015881c08100809041d0701030a0402241c1a800646580d14142c4006a05070304c24031094a0400508000400140c2801d91040c9074104401d80942601a06039559050880c2e40c0a02911b2103070700450309400410741700100c202407514409007044440300200d0302035241e00499000781e01c03d00200041e20071203c0d0070b41240030107121098101c1030680d25030702104511040d0754400d81d010310804c0c0008414644030320590900c28841b07002022001c10000030402000c0a5040444805007900c1c65000180c0395809090050413440f80b010505010280c02645000c203a02d001c141000644404d0000c0080903580341158000c00d46401e0340c1c0e81d03607181419a52071203954070003174005000c5064032 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 303765872 1250 303764622 303764639
    0x5040518060103110c0a0807060905011407140a09030305031005030609010906150302011b080c011a0319031409010c12030b010f020607020d05030916090209030c22020705100501 78
    0x10701ca044262002c111948030380c1104542402110307024201540721000000200788802c000d003041d28400c1c035000c02c142502d941e03840e0941b000c0d48160580b8405203070921641a07048280300d007101c5610021142041f005180051a000700d074400034050000001c0030859455460500e42c0143c2405012159241080a00240200b081401c00e5802601d07040c0a490601403a5001c2001c60760140c0d14180101c0e0741503080441d091032690100c0303041c40d0411205640034420b01591102e4020b2312841c101c44142c00003414100384030390724503003e4022035a055000194103e41621038a41419003441e884030010783c01654024000301e00035004071502c0498800c00c0d03600d81c00800450380d0a90f911502c02081c00e000740d94440d81a2118405032704a500c8514106100b10042d50344908004126112a8444c00321ba01d02020315402203085180c000940e0711244c1010880180417080903582076900c0e20003041100c21240000c61178940e201d400143d0390050020403c91144101c2c4010390400880d40e459000 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 303767122 1250 303765872 303765919
    0x1b0d020c0708060619080d030c120c17072c06120c130b040b030601050d0908031801060602190605130b0a0603031706060706090213090c0e010f08030712050405 70
    0x19840303810000c84c14640d28805d055120304561000c8000c080344000740c102a40504000842c10003044510040c0c1440e405582c024003400c41143d440310020b880403002c0004c414036000b45514240900e82210702c12110003c007041c00c81d0449240040b6040209000140d8540300740080a150502040207200d150000b400007001e6132541d0300c0107058003582d039403501c404074003403446079150031902840065103035401440140200060706500103482c00ca00d9039141e01c1034000751103122412030a002d44000c40c81d424401e82d40075040600003018000c02c00c008044182d590b42d03500401207900e8501044120340d106d1142c2d04110f03070252207a14240740c81c424200050a452101340c0000b058060a0060380140900c0a405064040d2240e898400c442e07c0d04409841548001c80c0c02000a614580651401c2e00c550080107200d00048140b00d8500728605802000c103030020001c0b000030707050130807810000208441c507040d8080f04408034802c2d178a00c107481c14080d980c07080e500406020342000005290881 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 303768372 1250 303767122 303767131
    0xf0516211104080d0201050103200301110a0c02042706200403031d0f0109032010020a060515031e01090804181d0c131d0a17031b0d020c070806 63
    0x125140104503120407402d0707c0080c800901400700700e00e1a210009885500302a10a801500108802800781140c07015503010070000380000c0c1d48080f20208510707090140000d80324100c0c510000034401101c07130b0b1600344a1024000c200c5680c406848028042440001819018240001e5107079a920305010b0000b0040c1c403241007802c10507110070715641c17806001450b402035042c1d50f91034580d4103690390919800d0001115050009442c80c45003042e5940c41d2085e0608003255002c1c2015400703074580b2200b5104054240302c62a100340040c8134042e1000139100c4582c0328083c00840800c1014940c490050154042c0031703140a00000700400d140041c02082607142c3c501e00810444040400c1203200d0011128a40880381d0300118403000992604010788015045000743c001042c03000d181111348885120b1006c0d003d250070000c175160602011103002c850588210500e03514515201c000e070b12070501c0c40c1d18051007074200881d0800341c18200d6030546017004000002c07500691748a0441d240d42e624200c8 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 303769622 1250 303768372 303768389
    0xc0f14030618030406051b0a14010e030c0a03030b180403200109051c120e0a0b0106050a080a1a040213090b0f0a0504020a0309050d050d0f0516211104 66
    0x2002c6146802003445110b40380c6520000fa50405051007012a03103984940c8a414a031019038140c2d00a404041c082c059510348100009030940c40c034400d08a0961b000100120100d40040c4200404203001141d00d00c6141c0c0d0500e00083c640c1840030003c0c001000542306641804000e2042100f0541c11007017500414840000d088540390010b044942a6004680c0040103600840c0340d01d41c8130546980c450289542504000c8901420040540c0465816025044a651004c9009010b01c0b00e011502c41c09403040c0e107022483c0103c00c1101604401c0d000c0c00440b11140e4600316841e0781a288102d02c810700b00c0080c4203654403000242c484881500034002d1039049031600c0080b441c2d905d0100181e94020b2805001040d65a28002c00c0000a41002c0c15100902d80c403145a180003d01c107200d0044d0a40c055100d564035a0780c0340003240308a61390f00301c1568003d4640010700000000c80e802014811890385444004401c2c00244007580c0c0d004c0001000609040c415522060312000c0b020304255020072 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 303770872 1250 303769622 303769633
    0x61909090510060302010c060f0b0d0501060f06080f011a0d0504050a03020106050303030603151b130f090504080d020c0f1926040e0903041e05091003050d0c0c0f1403 73
    0x344542c04807905403000034040ba1003165081d0001d002d6400c01306203400300c41c4000802008001c0412100c01c07240104941c542d5441400740858a100c5506501800769442e1841141c54039550603950b0304018020001900481b6030582c0005402c0d030b08540660101100c1840281800d01d00385a440c0c0094000320095400d003c408107090800000340d07481003100500130140c10141c2d00200f8600ba40140680341044110300c11400091081c0c0002c15600f8001d0140030751491920006040428640d002141401d0801051001041d202020341c0e01c6d14600c1a001640d030010080214604280c41d00500e060b401601040c4010401425aa42085010304042003441001d031410441d0111900001059880305000912040a06a980315401000ca008a0349441e4545040030014001982e420301a9800c0304414070050404604140c3c02000c4125040e101034110b42e0303125242c00d480d2a000c0c0c10004c405614405101c1d688011a0061524020300d0740001e86420011007508441c0040c0c600070310a0 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 303772122 1250 303770872 303770893
    0x603051002091309230f0a08270a0509370e1f05060307030b01080303151f0e0103140a0b03060f0f070f0306090c02010506130e0a0b0619090905 63
    0x12401341041c1c40c3d40c00404010b030400e203440c200c009903c407481d460302c9078440c40019a040c41010025042d040703004031803958865080c5040002000405401800c80d108800c01e40e411907100e5840d0711081c0e400c102c4014041d65612041107420180342c034410104d020304180454183e0241c08004020107240c0c01c018040e402c1445015640c4540000940c4040070b0301402604a03980d40d40d00141c0c11460080990340308581c4da840c0d401c0302840a07007207145c2d5900300100b1f01c4003c00340307a00218003004040ea103c2c070300d541c0020b035000c80030b1116141c41c10510054404604560703110781e1004c08550045c180000340c0741030400f024001400c000d040d40707000707210300c50104020f0300e61a00f005100f08a1064902d410340d41701c120449060601c118403c0c00d0688416010810b142c0500070300e1003415499000181c586040d0302007040784407600003c2c1100c1ca18000d010f58910300003140c551411034005d41c5101154842502080d640d140b41e000302840d1700c6214a0114080181d60000e092144c0242e0480740c120ba0f0 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 303773372 1250 303772122 303772159
    0x206060301090c030213061502030a0305010e0702030a08100f030507080601060c0b0403050901050f04120209100b121815100b0306090402090702010905060c07020a081507050d060305100209 83
    0x5000203455014008820401446c2601c07861101213080880401d9440d030f241d4500d19003801004c003810141c0c101060420550703a25100e90350050245001e002014100042c010752a403150000701020008058005900c186030102c4c45070007040215482c035100341c2d581c1000c0342c4511301401114000d008201c00012401d21910340e070003016400010722421074a5540d07003603d1036480351500505100047c8012022084960080c0005081d40540e0354020b9046204009900500a11200208a48280030f11590744520181c54183d0f807685049495901e91110340492514007400043c143c4c42482074554402d400c007803445004803d412200046140c07a5180000d01d80004c4035880d4000030780e40001000351130900c500c560041100d000003c2d80c0d403050340310b450071b103507085900c40d14420b4001048411402c0400c0500e008100c2003018156110000380c00f03000305007018021070100180400e036403541000f42d40c0564020765024007120020796070031101d8000f81d081700c03800c3c510490002c1c001c1000044c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 303774622 1250 303773372 303773381
    0x41703040510051e03010905550207030915090503030a030504061b080615121f08011416080403020706030f15090f0506120d0f1713030206060301 64
    0x15002800c07820390601c1c9a00c00c4034684c011250103100140e0580300e20302d207038081d41c00642c0030380b054042c041440c0ca80403484c20040b4000600030f150508985c1d2006c04100fa0982160440002a668007086c01410b00f0041d60051800d03d801c40c2242d01c002554000c164110401e0821902c440300e840f0b020104550058514480034030130203030150000c0080703441c060310a42c0701d140d20034400c003400103002403152504130a04a07034803008800b1889a0040c44103501d4241740c5121a001040906450003051102c140d000410140c03604e8440c250141c40e8441c04a8007070f035200c000d40100e41c000c128050009038100c0100900350740da40304918103581030000c2c9607c240e00f00c0744100d4042d0000c2031410718000045006002e1502c401810310b540380902c44005044500380e8004008540d004141501a48405411a4809800c00b0303c284a21000d82446440203e02c0e004009150300300404140024001990014200d43c1341d02c1c03039050306400f0060200c100e0141501414000d42c01c4440300d42d190300900d42241e = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 303775872 1250 303774622 303774629
    0x1060f05060a1e2105150d0503070b0408071b15030501030308070c050c1206061323060d0c0b030906010e010609030618060501030b090114010e1911040b04170304 71
    0x54801409015115152000c0b1440000f0074a4a44005002c414100742d003180d683c3d1403500d801340c035074080c042d8907030880c50f06010016040341c0d24405180329030f903400c1d90b07840b0b18540117024a00740c400003000c0c0412441540c00b441d0b003120b241c0030b40005248480309090514040d51440c0c2c03201c210403182040c0720703108085c1640c2e0b16494101041c2c41c0c8440030b54452000c1c0c1c40441d000e01c10114018811b0715481d10100d2542c5590b401071086040c03d008209991031100000600c061904950040d054030600c24081e8002c0600e21500140e15490007180c0c641c414001d014145810450000800c403491000079445031080034280d4000c1d9032265407070f401405003071003020700048030001c003440426a694400319070320359200c95000003460342d40d9402c07060b500709a1050310541c82800c20480744030820301031682e07030003403425243e103ca6040c019100302080001d0a4542265203ca002d0400d80300107611000703411454480498980d540d410380060590b10501511000d40600309038081c00a00000035101035 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 303776978 1106 303775872 303775877
    0x3030c07090e030c03040e1e0c0a0f0f140906070b13051207020d0b060d0203120307020c030105041211030d02070309141801050f01021e01060f05060a 66
    0x119001d818034901e02c2e81042008612800d404002c50341a608a01d51002180c0c6a000d18850800c43d01452500e20310300780d40c00d1040c412800c4000c0c010144c110360f6501d5050b9404107080741c00701503030740d003480100d0110b1a2460b014000e1001a2000e100051b00017400c2c0340c016251607080c05030a480c84681782003100340000c00c1c031106200741d0720385c1104040c165240c013081d5408030b003010000310300281541401d00702007030103561142008484960000d0840305113050180c9410f205030300503280d000151240010488003420180951031055030804003001e800501c104041e200c0380d02d03000308030800e800308000d0712034008103510141408501a43d038580700d4034107080c81c0302103001c0c481402030321500c07640c5400d48000510119590556409075401d0041195440c01030b450081e0707009419041c8551000c640384012015807000b000c4600040c10207404d03079501c20a1040c94030508221400 = true := by decide +kernel

theorem cover : BRFrame.Cov 303597122 303776978 := by
  have h0 := BRFrame.cov_init 303597122
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303597122 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303597122 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303597122 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303597122 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303597122 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303597122 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303597122 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303597122 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303597122 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303597122 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303597122 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303597122 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303597122 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303597122 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303597122 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303597122 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303597122 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303597122 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303597122 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303597122 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303597122 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303597122 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303597122 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303597122 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303597122 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303597122 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303597122 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303597122 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303597122 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303597122 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303597122 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303597122 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303597122 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303597122 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303597122 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303597122 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303597122 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303597122 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303597122 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303597122 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303597122 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303597122 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303597122 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303597122 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303597122 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303597122 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303597122 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303597122 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303597122 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303597122 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303597122 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303597122 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303597122 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303597122 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303597122 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303597122 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303597122 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303597122 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303597122 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303597122 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303597122 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303597122 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303597122 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303597122 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303597122 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303597122 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303597122 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303597122 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303597122 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303597122 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303597122 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303597122 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303597122 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303597122 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303597122 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303597122 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303597122 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303597122 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303597122 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303597122 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303597122 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303597122 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303597122 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303597122 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303597122 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303597122 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303597122 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303597122 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303597122 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303597122 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303597122 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303597122 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303597122 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303597122 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303597122 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303597122 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303597122 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303597122 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303597122 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303597122 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303597122 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303597122 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303597122 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303597122 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303597122 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303597122 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303597122 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303597122 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303597122 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303597122 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303597122 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303597122 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303597122 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303597122 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303597122 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303597122 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303597122 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303597122 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303597122 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303597122 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303597122 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303597122 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303597122 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303597122 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303597122 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303597122 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303597122 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303597122 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303597122 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303597122 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303597122 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303597122 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303597122 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303597122 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303597122 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303597122 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303597122 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303597122 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303597122 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303597122 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303597122 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303597122 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303597122 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303597122 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 303597122 ≤ n) (h2 : n < 303776978) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
