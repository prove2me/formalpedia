-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2929
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:09:45.579844+00:00
-- url     : https://prove2.me/submissions/0c236f47-8bfa-4cad-8ff9-e2fdfc5e9a5e

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 526618705 ≤ n < 526798561 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 526619955 1250 526618705 526618711
    0x80c191511100905070914010b0c010905011505010e0f0a0902070311150f0117060105130209031209040513030c0f020a1d07081005360c0301030302010f0227030f01090803 75
    0x165103c2c20102256076001c91003038035403501900c002121107a06c1c9c07542034110341d8445c20201d030065480342c07041c0000580c2402201c1d00c804000c1801001103080500043c00207542d0314450384200005d0040c980c868a40c403030007000351911401e000d641c1d188141410303603882e5200d0403903219074032644103d603040900d130340300340c50045074071358000001640d84020101e956083d8010303001441d08040c0c0104454a400510308054509280c005400d2180d4000068281081903610a00d03005e400035400d421490b0034800d49520058400d800d01820f280340d24010901d81009200400d0f1141043d0300009564070401184018042c101204e0070302d0300303014168603038030b9026601540807a8405002c2001c64640749111025640060218400c0b1000154440300c81460030780b00d080140000021604c00200c1034031501d1042c1c201b03104180e80c0f1751441c50024210390203880c940c44100c0c414841240b0601c0c800b8000c605800740c2403034100d003440c841c0700062705003500c00040d07412561034541c0032403c0050702c002641c4 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 526621205 1250 526619955 526619963
    0x703020d08180d0c2613050a030b040602072105070204060f0b090105030a06050603180c030106180f0e010e21040302030a03140d020f0301080c1915111009 68
    0x509912140d1080c2e0001050540110303040c1c00c80803500c0d0b28203101c2d03040e0441d9103024424094186080c0e002211001c040c15983c82c1e40040001901d0501d6240b45501d00018a419103003c9441403a42c0c03074a05d0100d1000c1c00007000b2a4000a00209000401000e021905201007902035900c1150304003900d598040c9000b240514101130000a01000d90080d00d0221080340401c546440c00400044500d1380c0010315401c12540c3d11314020950f030b01c49102540c4142441d4100ba80501002010b040c6040c14901d0790782e110b40e052140601c481480102e00c0704440a034140c02281c040001d108200140c5054050303401e1710b42c0382c5600c0d00f050780c2e0002002000c410304000800c201c00c01070f040b041000d210358007020f901584440e200c0c90019200d8401c091098441e035990b1410440a100840c2c1030b07a21414900002d420702000601c02c514061080440c208801c4400400030100c42c0200c1240840c5031007990600154512903848081c051405000c18140280503100d5500d0420002c60042003542002c7d1 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 526622455 1250 526621205 526621217
    0x15011b0819120603120e030f01091101090812040501031a090411040c081e1308030106030c090803090d0303050604060e01091d060903090d2429090105150f0703020d 72
    0xb44260146105040990750060307070601804851200903100b0200103509140c0510481451406540d8288a031003030b1140714a031781e0094144c109000606451140d0050710054012242c030602a52461046608851007824045071035200e00310804071101d0860180d0303402c90783e000104000c002c2090004031220808036010045105513080c12a00701008654580094041801d80404c240c812001c150b481001070740800f048404555840175541c0080e8418800320741c580c200c04c3c094541000d41c20f07010300504401581889098400501c0f0411b1209026090580ea9404504a0385480d00602c02600012701c3d010038030759464441100610b519204220305a4803807103840c10415000c105039005181d208001e5040c580c0a50403c01c10305d2031040105e419414003243c2040040b80c01d103a15035151030740840002c00b80540c00c50491140c0000007000441c64480c9103291243d0360380c01036581518810340d05000c90707010303415010a640c0301c1c0b0314103125201c50208504080541c00102c40b805012240c1e185 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 526623705 1250 526622455 526622477
    0x60e150c0607020d09030305040509060402040b07080a031a061210090207140c010302033318040605090c0303040b031518011406090f040b0102100e010b120615011b0819 74
    0x21103c5d08003601000340000c200b003000b0009860310320034450304000001c00043ca0316940d818580c403550310554044030401000b203404252a030705403054440c9080403102c18a403095980d0005101e5104040565401d50001008039040b0814140341401802d20660210f60310300084c2801d48401c200c81080e0092841070014129107135200340256409031409204c0d41c0d110703040c290310318410700201c8404070840304070050a103061075440003c6131840c0b110060030f9072914105800c0000076284000c101c241c49901419031070901c1e840020460303040b074a04c4001d9a44a031240b00700c01c2407503070748408010ba00070b102052005200a072002101c1c1201c244450120018009005100260160700500c0b6440104902040700d2802c240e0015141e056051041c0d500c8002214016021201444064080d03a076552110007407a06002c020505000d68000040001c0c2c81c101418000d100c607840080b904204104141e11030105091813004213a41e8040c0c004c0c0c0d15051006161046c0d40320780036404000170078420407 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 526624955 1250 526623705 526623707
    0x902040c18090e030910021006170105090106061b0f050d110d0804050a0b190509010501080f03030609180a080403080d290603060d050604050705042301060e150c0607020d 75
    0xc082d10850321078041c40c241070b903500400c500032071740c01164019400342d08c0c500c6942c0703502486114050800c0428000c02c0038425103205084900c02007a03010b40380e241090a011146e040b10058003c07081080a031840d0720081e1030720010210300808001e2245c42421580440b084c0c000d91580c103291101d804580707040c0c00c034440441e4000340983e8043d100750810316981004c075403e01c0791554001c0665000f0304690890100c42421903804592402d2681d6440700107101404040c4800d121014a0200a50550030410000f92440c58090210214040742c01ea0303446111001f8011032410603002041c240d140d564030306018070541c0c400c030220014a07140c00e4140c0710103000c00025100440407424003d43d07855010781885250384c0080d02a03070b488000140e40200007a01085014406c82c800c1c00900011850b100602040e502d91301c2200418950902c00d82c0a404901c080480c112040b52415184034840000070820340e15800480340c000395400140151072030300001e1014040c60f040d134200e8840840c1108 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 526626205 1250 526624955 526624961
    0xa030b0a1d0a02120a09050111040501050d090c0305030a02030406020606060a051218070303022404240207020621010603020f120a021612091d0112060902040c1809 72
    0x240c440241400c490030307551003124044465100300500300052811500315558095104111010000241c442d800c42042100c207000d641c6402d580d548603141480c1c107140001c0e220f80035826010b20542ea941c1200b80a01803240d40c110300541c5c00c40156682c0b89454200251680c1c001c2c01940094810f4a02080840c1021000c0350308143e0384c1c0d9034441c1000c03000303001070b140c500b40600301c03045065514203040c140c440240304101c01940309400604040054034041c07234800068043c0c1158500c0c0680c20003002c5103012598504c20b001007941c44103203c0c01c031516980280140e0101075008031001c00c0151884000162104000d10500c0c0c1d0200681e0744c803141101607104100c2ca841e0741a40034081e0b0503503000c101c0359081c0c000b0b0a4410140c00c0ca20300d03410307420510038400c006480e000c1020070003601d4241c10480d0701001c1c150ba04089103090201240b0403613400d4061192901300003403494601309001035984030782c4103254000e100344403045400324000c280789907515941140402c003140025039401d03248 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 526627455 1250 526626205 526626209
    0x3190c0317071502070f12030c0806090907050907052221121b0b090d180503060705090f030604030e0f0d050a020910030605100f06020c01120e030d050406020a030b0a 73
    0x3c907181103680d46988990182d000031000f290b04410700c0b4044000190002c4119448000c3e690303001824802d8581c0007080070002a00c0a8094901e410901c85071000100d0f169098550503150044140c441311000c0318641310f400341506500c030341c044a0106c100180ca024408075500003040e548144400070010000246440c0c005021020503001208064081c115002105100d150001c1000c0c6072900d4490b003001040768078550503040280c040404a411412680d94405640300c600301e030314245400329036141005052841030001c0440e4228942d0781d0301e10700480404004d000e4480074101403401400c1c01c50000f1601c0d1081071102d18503492810801c041401e283d40142c0101b030b603c00c00b6020f100c5404000740210300420030304c0c0c1e40440420180e000d0b850203030203c17a0303038401c00e907141054120010f0015040b080442d00700405880303260f03074405145480e0200d44c8200003500704103200141c1c610b103c2e0b5800c5200d0f285c141420042403200d07503800351201c1087c54a060251001100401445684034 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 526628705 1250 526627455 526627463
    0x90b10020d09030b090a0512031e07020703060f0b0d050d1b080304080702210a0b010515031501030219020304030218060102030301170a14032205130b03190c031707 72
    0x10000800103d000301c039684e80c01c2122042030b503440d8039082d00c86505040480759460900400001404024500c0001150003020744010030901c1d0309140c00025140c00c454400904400d854000951001045500c00301158900428010398440c0768981940c9841007488104045001c05245e00c081c034000900d820070b00d50f40300310b41603d9a541ca9942c0e036203a40000409a030031410303420001c43c25262884100d0446d504a500600b000102c17881d01406441d8160410f602803400f00304400a440099001c1d2600000219020400c10302c105004900034005c0030f0108900d10790300b0b0600e40c4420340110040007600c1c002e550789001503500c11003035940d5940c26510399006a0082004100d0000da44158158013481c00f01030714a41c4469440d420360303600ca1407410809030740000400a40f40002866001601e0000700c0600800f1460a400502d1203404585100c14080d2074640d20a00303581c0c14451846608803030140701c0f40018a40c100000583c0f01c1d0b000c1200d1910707800a52685200c2024103032030580f544 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 526629955 1250 526628705 526628717
    0x3020a09060305091e0313061803020103090f060f0b0103060803130e0a0b0307030305190815010516231603020a03110d120201020309210a030e100501090b10020d 71
    0x2424900b14020b110051803459207004100c00e100c000700c091030340750080d00144802540c0340d1041c42d81030004030510703500c810706101d52400c162415945140c0594200c03602400e000032064620304040441c100c120340010b09052038104118020f602c2a48244507081c000e907001c00c811905c40e854140d0724452074403c405410900c0da0700b040200040c01050340e0009481c80301040c001000b4020074945500ba400c1140441d0380401ca45521070303c41c001440c00c02445e442d005629040140b4100d14032800c141c104c40c100440052058070070142085840c19141e808640040781d071298042c041e20701c10002504070428007540f4040d9024608482e08101603d0b00100103070100c501c0e40e5a6001c18034003201c0c21a800402198640010032a50301001c580c50300d081e00050399a02d05408084e0900c0c01c2c00c4040e1002603400b00b001f445250300a81910550800d40c180000d05a482021680c507112490500340d015505044c00800c86a09940080c0544203058400c420100d41912050743c440280c130100303c0010314 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 526631205 1250 526629955 526629959
    0x41b030b0d0b0c090d0804030f0201030b010309020907050a0c020a1d0105060c1c0e0402120103060501052218170c07090b0306041209080321011403060705070507050a0905040605060103020a09 84
    0x240fa40020406010300030580c5044462580e41c48080d07400c0340d0301c20b0318540c0c55100c0e024190350300b5014440043d202482c003040398200070b0b070000f505a400a008a020000086541078003540104858140c0f030360010a2440d40640e90b0316090040380340b40c1111401101510000125402d00c9000d0700e19150351080035081c480001018a00319000000d07a20082000305814440c0c2070303d840c40105003614007690b05038640d41c118102001560310603170105001d1504000c0e18801003d040c031a03501e6120800c0b4021640e05011034020601c0c140c25100030740090f200d824401d40f000d080034024013460342c812041e603007120f6688071050100d4601c000e500da00350300810b000030001140074008075180301c00780c200200b43c240c03907040c02450b5401241f44100c0e00312402482c5940c1d41050003201d4018142080c036464011440c5010980b12200500100280540465030a0400000380079560280201910402c41c0c00c0d520b01e04a405810141d0701682c65625050204600d07510034002c4525070320340394558200240c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 526632455 1250 526631205 526631221
    0x80a0305100b03010303112e090c08060f0103060510061409040f0e01021c02031b0d0e06070c060f06060207290304051c050717030411041b030b0d0b 65
    0xc200100208600707204554003082c0101c100001d10301a5000303035192051544907062152510414602c070b02c01480b0301c0e4000c11001d100c2400d1f24040541030030004582c00d80c0c0e502d408104050180c010307400500030101003200c0c50b219030403140d04890080c00180119100c94040d15103100150042d080081c0f40c2000300341c85c14100200604c1000005400028200360b0018110700700c44940d0b0283c907032650000b80030b0074060200c41072411180340e900011880c40c1800c0c08600c4e989085800200362030000480c29016456140c0d002c00355807d10103065542e00d01d0310600041005034404001c0701c101c1d16102665110084520a407416160181c000300a580c4c185503013005201c1c846408641c450034603c91402c66051800e010b180240d200f007004010340070904010404100882206008018007400080d0105644031081010b007082c40398102d0703076070f202c5007000004154280c0c2400e41040c1021908003224100049140c181703031035035504108840e2404200105500082d001500104e07501340460011 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 526633705 1250 526632455 526632461
    0xc0302040b030f101a010311040501031d01090b01230a0501120902150306030f160303120e190b0603011112060a030c0b033117040b040e160507080a03 66
    0x80d01d4018110b60f900b501c540708151901c88065952219a0f0f21040350701030003001940c04107501c0000b42030501000041c0c01d100300860045201e1f280c1010b4685010100c084001200a00810042c034000d104502d00ea042c2984010b100303204001140407c40d0030440080c298014084111500808001c0f000346000011101d02800c2e8a8003640300b6901d02400d401a80e848450416901305e4452180d200d28010080500307108161061100d284c200b81c00c0035400195022182c1c040d690306061110482c5c0c026690781e0001c1680c0c0781a841c040c820034070450142003c0b80c03803a2030401c2c400c0000404540e21030307081c14241d0708a09a10812108180800c8000e41c2c4022845507100300007420580c1034a9598903000001e8006078408042e00c8400070510503140404041c2c41c910343e0781403524500c1120ba0403207003902c0c0040004081c000f0000c1000243d10401d074181158020320400c048203455a85401c0385003004802512004503904051080341c88460003034040c1c48210390400c0010b810409203050680203 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 526634955 1250 526633705 526633721
    0x6050d090c05031501140a120f030201020409051906080309060d090809152101030b18012919140d03030e120706050f10060f0c021206090d03090c030204 67
    0x405607200004035168800300070184246803045008992549080700c070b085410b4451100e2030041c0e50309282480b00c03003400c0c0900e14003076601440d0142e4540440c00d04038020b0080b40c020b40841424030041c0800f46d0307145008413403050384020f020042c0943d070340341880d900d10460b64010342141b8140180140700c0340c0c030b611480b010b6020302c80540c80c00a00000182500f0f0252144070860200814074103610703560201e400c004085410a4880340d9419074855907039009004004042040881050342a520420b4000d00400d100d0564446503007007100c0c61904400f003000810501800e01078910180a8900484030b104503a040304c3d032040100c0c0d060342401204818100700b03600385920f48280b903010190400010100089030002c142e00c0380b200c1e06d015010744601500801410003001c091204000e20340752554129001ba003803144115103076490941d80c210000e90003940c07044040e41502441000401c4142c0b08110400941e150101507240980c101e42d1503540c0a8403075180d6403018001401c0591001311 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 526636205 1250 526634955 526634963
    0x23010804051216020a0303032702010c290c0415080c03011e030803041a0f0603121b0f060702070803030103030507080904110c1614010c02040902010905060a0e010e0a06050d09 77
    0x111500c010313004548501c0f01c942c801c0300020399075041c0d00d24900b07020140d911604c080e24400f0094903800d400091201c4156040501200329403c000d040ba2881440c200d440003200003001c1d01e061400404503a801d030841c0c131a4134040d2041803110060740d0300c1404080c3c0f040c01c01260f2141964203003c15800051103612070000f201108890100101c1c117100040d5220354803c0c9020705035504184070403401c03d01d0140042044070740f07030b00a00220b42d5004c13401b00520070792500a11380320f0400c04400c40c1600012200b010312800366118023500002c011500718400e21083c0c08481400c2d94505a259403480240700140c0041c0c4103010120014039043d00401d0001c4004002003940c81110790204401d5022840441081d801124013400b2404659043c034000d10103880c45803403010010002030800240003000030301c00c0355a4400700c0216070050a07400090b200140c0040d88a46100da0050309208070112403e010541c0741801c1109407410300504002d807110750742d45c28180761840d15024094041004222 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 526637455 1250 526636205 526636237
    0xf0c14010e030c07060f030c020613060b0d08070507081204030602071a071206060801060c060902030a1202060108060c0406050f0912011e05010902030912030c0d06230108040512 78
    0x1c5440300040000d001640b01c501c002e000001d1a00e0350141101086812040c24507040828034003055030049015903000900ea03184888071140ca15203000280020883e2691000d444101c21040c0400c039030250038180e100d0411110034640b02c0d22113655580c02401403040225080100380700264558000d45181c3d40310b074019030245425520a4105084221010070028070a1135010b16210740601800c0002d10107402c00d4155035040040040c8880f4400c00b0103070120361180e60003800c54808200740c0c1c4142d034100c0d1b6040403074404518003d440d01d07400c0c0701d40091840355501003444501968200d800325117440d240c480c81e0200001310b25035907030028031000d035000111015801c0807203400c4c040c6030800c03a1190f90600d007500c0e20b40d03401da0448a060300661072051042c81080810703140012103108000728040100d80780e69030040525101e00c80c4500c5585501e080c00d41c0000e0384082c0194a500351980d10200400032524203004588190080700c0241495200c8100703031000d80c00c480d0040401400440803c = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 526638705 1250 526637455 526637471
    0x607021306090c050720060d020a0513030813090e03091c0c0e0a3803070f0801020d0f05060a0e07110303090601050901120807020f04022206030b010f0c1401 69
    0x20b00c08807114810041c000c40c9002502070308202c01900c40b40c508803040682c280300c3c881d50102080e060b0180400d8582c28560020300240040c2c0a00d0603100d000c02520031100d0400d49a10304500c0681000c071122094180d07000021884030080d000f221100c1034104025400c102601e0700700000000002c030070003090100d1a0290012400e1040c40001500d05c4248512050818130109000c44d1030492000302030003100c00f010301c00c58060541000000f451180781202029040c0300003410440150701800301c075480d40400107032105c01034001c1c040809040f5010462514528071f002c0641f1802c0340c2117648981c001e5000c2c00702140f0301c081c0035000501c0b1300d4070a40e17450303120910034a0742d0b000307884100040d80480010000c5250260b200741c050041c800140b01c0f0820903035100c203150300a00200034481c102440505d1200e403100d60644445126130414803900f82c1c0c003030302c101c01d03544000d00a52000074204040403c1c90350090801d201248419641d5006501c0c0988407242a04100310071003246548513000 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 526639955 1250 526638705 526638719
    0xb0a0306050906061e010c0803250c1209050904021005160516150503041205190e0301050601110a03140c01021b060112080f070c0302120309040605040b0607021306 72
    0x869201c0c00c00200140031508244c2d04100b0f890f44ca00b0b500f003020100160080d030b51a60300400d09074455a02c0212562a0f803124601c3e0751040c4100c1c1140e845050144500079402035011000f901e4103070140d407040700c0e029600002103811000302d0044580103030102d80490010706003c2609100e4100918009040c10768104424900c070300010000da80c80c0d4044a81d99240221001c0854000d001c200305a070f41c09514003001070501d0200500c0070b02418580580701d440c1a0240c1c0445a10014981c420000514606c40140c100f14104080301c0c040e600c0c110000d03101d0b5005e00520000c4a008100800c0640010b640440d01d801c410b41e1105c07440001030010070002c403801d0000e04001421794160b81e42401400c03000c1d0f441d000e07050744802030724840304450101050450088070500801ea1072096030b500074a0900c0b150a5030250f20080d04629000741d03800c82824040003804548504071fa0502440740d585d001c000c1a50a0081c0e070540c000010044100137152901140e038401e020030001203810780d50340003 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 526641205 1250 526639955 526639961
    0x60c03070c0f0b100f0b04150810260f28050304050a0f050306090102070c0312180b090a061107060f1b03020d030f090c0311240d0608060c030a0b0a0306 67
    0x90b1030704c221a00003c0c1440f0821350100c0c9580513200e0100030a04081c50001420300080e80d0020520500024201003099031995084442c050102c980440c0030032041c026484a10100d40401074105000b5864a11100240441c81030034141280c00340c2d18042c016402038449400d00c61600b1101c500c810000086e907074a596240c1d800420f00740000c071003a98500360605003450002407126075141d104101c00b400091340044590281d0f60080c2d43c1c0b280b11655080c098802800302500c1d6009107280b8000010f030030100320010881c5480a45040350060340c0e8040c280c80b0800c0c03006601920b81c00043c020702046104060317026000c441450315101c13040106100040780005804140e0060300500c115101036505070054403e10030286504004540d40c0e516070441080ca1070000501d100c18180040120b42e0780d03604400d40001c509800c0c480c50201900303040300c40b917000e180100c884e241050b0780010303918400714283e803254981c0f0f1249441d580e02c1c020321a0083c4001d03030740b0590008442c070001c000300fa100c3c4 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 526642455 1250 526641205 526641211
    0x5190f02070b0307030e1f052802030606040305010509250e0a0e01090212210301030807061a0406091515050d0e03040e01080d030f060602030a111e07030311060c03070c0f0b 76
    0x28484402200000c0f181f03c09449000344003a503140340340000003c0c410120340050329034540140d001a103e84844000810510482c0d1018000d0340c24941408840038000c6032984071001ca050f180681650904902010500c06100f810000024080050b400f25044e0b0004040545140300015110310b0990010309200070500706900c01d94800d0f011690318082800f1900703d10b0810100d2681598510340e80c2080c10302c00e800d00103702c46d0f22003052100c00039042d10304a0320020020411310081e0785507450fa0000300740180c0981c0305240540700004034150342c0003510389142ca8982d101d41c41e000c665024440a041440364418061100700800500030340850070740c0b4064040f00002e40030750111001c0c010162850541c40c2024140703402c400b0002e564000040300c01121140c01c003480a224052212814500ba5490702c0c51442c1d50080702d80c1d00c2860202d008400d89210b0b445440d0940c0c2c4034409150b40f02c41c12240c5202c00101000401d50242c05089643c41662141c807807018044100c5c0c0e1400500c0e5016 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 526643705 1250 526642455 526642483
    0x3050a0b040308070903150b402c0c0d030302121509190905010c0504030b090109200d0606061d0f090403050f0408060705190f02070b0307030e 63
    0x6101404205940703d552140c000c40980b51400400b4116256000140420b8654070707106540e03640d40381c1c42034546100c0361000c019082c010700b00030000c1000810507026241c1c2c510101c90310900b001c0ea0302c4401881083c40340b22030f03107809401a031001d14480603101c4182019030568031661407112041c1e505c1d84c0c90628400e2213540c0168131152891400d4540701030207415503590318a81008054640c903079003203540d030189098402e141081c0110103210000c0c942100302400790350900d40c8104901344c0150062045911078905040c0543c1c030544c7c803c0c202c1d0405640242101008181004442040c11002401484c01058010b003440300e5034803503003150401e510440221705000d00c0a00c1c0080d084034407544038041038510400100f810000500300c1040248028103005003c03039070402c5001244140c80c054a241d038100d41301030400880107492604118941003c90309661240900e0074800d10203020b800c0d0075034005090060818041d40c0040c0c20041030b0b4820155038034000c0d1650441007190b92030140c04 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 526644955 1250 526643705 526643723
    0xf020702010e0d0525052707170408251112160512030408031809060406150c05010b03011409120c0a060b030a0204020d05250c02010302031003050a 65
    0x514400940b5078030110500310b01c10400d296200c408100007280b0303858400100c0284040c51203a0340b00544124506410868200c44039098007100c158024256103111581d103030030110b20f903451803021101801000700c0150110078240c040f07400038651030043c140360803000cac6c0720841ca0741d8440803404c0c5440c40d001050712058084600d0200f00e0038217030f0380317400700240c101c01801c41350010340b00b040080f80740c0388a02401080501c802c3c0c08940000e20607200500b1000094950310320031440c007403604020120300c2078400e040765408200340d072400d0b1040c10210b44a9215015001c000c011090740c40444002054525540300d28044445940a2045482c13031070190f040401c1c00c1c18040d50851030400f12a60ac101459820840e28901032400990b5a181c9544440301191650340c60300482e0501e10182e00094020b4008509803481038110741103148902c1c0240ea0103090700200c071460405021485611401088a41c1801d0001d54802d4000b160b011b46204484241c5550b030303070f80d06407800030ba0031070130340344e50038 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 526646205 1250 526644955 526644967
    0xc0b0f2b09240209030d0c0212060412020c040212012105160315090b0606031801020307090801150302010503070e19121211030a0309050f0d02010c1407260c010f02 72
    0x20030880d04800111942c0d007142040ea031000030941d01c03204818041c050119501e40601150f403045800f0072440c1c541c000b41d500d40e060034902000800401611000580101c81030b080da60f050901c01c0d221034402080c0072484507448c000d8146078800240b015a001101c01c840030401080c0304001d0b130008002e011801c04d40c018610700782001d001d4000d944d1117401070b0414003200c01064015aa440c1c0148084852503903c2d01c86030b07a203980403581449445925400841000381d0b081d00040120700b207601d080000d000003801c8980014014590b400002c0c00314a0a10114204500c2003414014158002d00394060039a0113120003a240645075028241001d10034000c10100003212070b440c41000c4c014204090015182d00d411500c9024a400d41001c241e0f460140ca001d020342003041e00c3e15840c2d550140c80c20850080d030300034042c09001c12144045185040140c101c401c060044500b515001030584140300743c20f10381c40b50400825400f030310010b9000c1c4886400100284110101c59400031801a5111 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 526647455 1250 526646205 526646243
    0xc020309011b080d0c1803032003070c0e06031906020904110c0a061a09161d0604050f0613060c02100305090c0d021c03030203040c0b0f2b09 62
    0x120380d0b90a110b040d050355039030003800103400307400b6110004100341010410b98410350007200d001c080b1444401c1646400070f400018540c0090104881c640061080031300d0460300b200250b603d202d48000144015501542040703001c6030300003c00c0d003010004040d02c42682401d00e6803410f02d80c42d24030a41e051039001a15820600d031500c80d4480030395203041540d0400c52001426070316040d00c41030140903141c4840000d01552002c81c030644c04403000400150540c00d181040b0008103000c00c440b400803644c0740c0d82d5440103400b1000848044a0b0040039940740c5030524003403080310b040c01e00e006c40d004181444508000510f080011000c4e00c04c031398804480a407280100600000161040018546030000b4440d2180c804600c121a4601c15100d0720b1540782144042042c42c1000c1e6201c51020b071010410f40f04169244d001140200e00036800b01444a40358115046580300740a101d050709035040040030b5000030b40d501c001b0f20069041c1803803c8002d900341100002ea80701c0340b10031141600c20a000e03610300 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 526648705 1250 526647455 526647467
    0xc09021b0601060f231207030b18060321040b04121a01050105040e0907030203061303080105031504022b1101030c0f200709150503120903060109020c100c02030901 72
    0x140344601c0c10a0341aa045240036094061845100306007402817240ba05904005400b16045040340b40a0185c891400d850010000e103c00c52006104251003001d0302e01c00302d04068441e0044400802402c03407820150080c3c4035203580d90021382003200d0107100c00500320a40402400007009012401c44a80e40340e807800c00c0d0151b4186180018032010600103204a0740e100041e281502d8804220b6002a1148203100d8548905580000d50512801c8100300c484018201203442c180d11a440b0b060140e40c9130f4040503202c695a40c0b4054202800c1c0c0c0002d4091b140a003400b8503480c0080c1d82c4069140003054545e00c9111110030259401d44400400d180b80b540e0520910300030b541a031405030701c960a000c100814001d8000c41662000303c000100c106925000d010000041003525010050465030221050701502148503682c424000d045462901d40c00d20340440d101c41400602401642e828001c040000750080003030410f9600c20821103041e40b444500c00c1d1801400b59400441e22480b00c18001002 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 526649955 1250 526648705 526648709
    0xa1406090709090c090c0c050708010b01110a0503070f1401110a1e09180209041401150816051809040f11010203042105010209090c040e062b0c09021b0601 68
    0x1543c540b100d000c2c0803a42260854042c0d50b00c1640100301041e040300c00311400809500c2c080c00314041c004000480f50015400b400c61003c080e21840c006a007000d00e415115520f50a0117011604204111000220800c4240d5039162040a1607800070040d8400e82e42103840c8502c41c0848100d00165001000b50450041e002c8642220350310215840390300001040030000c0c3c404c0d400e84c01490215003106808030b40640304407100240080000600500784051030020070310900300c6c8035800101c811800c6102c2d882580c443c142145030340516141040c1c4c2145e403540040f080c038520b0880803c001c01d40390b03603d410184c040ca0180d03000740342c2c1c158541441c403440c51003082c0140c10b5510800080141801040c4506082c030803134040c2c41202d00355420464003910a442d100d99108008008100d4140420005001503c2a60103a14416602c0c2e10a110304080300b000381d00a07009a036200c280c000021005100d122a01c00d0710940a225582c0140001b070344c200c45910381c002d19200070b051051000800500d40 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 526651205 1250 526649955 526649969
    0xf0703080a050f04053d0b1516032d081906060c02061b1614010212070b04060603150c0810151202040b1303120e0f120a14060907 57
    0x10a508255a4181c0c0c0ca0144200c1503218140c0c0004480c0e2103282000000c0000020381c1d4072140c992011030104c0000d04801100e180700e000c0314208d000d110b190900540e405150141c401010306190340d281a121148841c60044c01c211840c5045400041d861051292801d416102d414003810030b006404821048034441c00381c0180b1300841000010b900940b5964501c2d0181e50b419a21211035104107030b9000c51000624043c4900c40109680d103a0010980c0c00b116043c200c4d608100c020394004a0f01d80c400b902c22220030390f100780045030204148805c12a040781c4607075000030703000d81d50b070b580d403e00d071140040c202d0350207580c60240c0740303059412510144d07011241c0c1148a880380c0c14420702118460400700040100700489048603211081503046601a00100703103103540f0f850724003a174490111305500045400012080e01d2a610754080d00c0c141e1072000005108591480b014401c4c0034062403402e035070b58010b1040e01d00d41c2c0b0119009090390342c2103100c0707030001e0409031400d11010352411459506c910 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 526652455 1250 526651205 526651231
    0x323070f030821040201020c060901030b090906040b090d020601090b03010f0914120405300a05101d07090f060b1902010c05130e0601120213050108060a0810020a050f0703080a05 78
    0xc130050ba800303e541c20009000311074864680c00c844c00100c000b007002c401c5807604050740c0c0d8140000c0c06800120184510700c00c040501440c1d803652119606d071040c103020440941d108100510100d840c50700000044440980001440740e00314058409882c1d00d05800d07600b040072900c07080c040150030702c1001c01c44051303111514501468000030a408941c00700600032039540307651880e0750f40030b000b13038030b010121400c002103030343c0560682441601c480013141c2000c02c991408030034502c106580b01191403c00558400b91104034505a016000703042c1a4000d441825983c00300841d51080003005007102424042e43c07480c0340b02003500c000e42114100341d91501403100500c21090328503500e002400580b8110007aa4030036031284401138400445e07034100190701d40d001040e4540190fa003c6d01442c215074003669810103a0f01c80178140140798200303000300c01c0c140e0490105610062a250024150304000c0d00d0294a0300a080c6016840343d0041103089002448032800d1110f607405600600e03800c0203101e1405 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 526653705 1250 526652455 526652461
    0x5041b060503040f020a030804030302010209030712030816030f090515011e120512030703020309010b0a0f091107060c1206140906100e0603090f060a0203010323070f030821 76
    0x26000c2d000060004192001c9032185130210340740ca0070490300456011044648983e245d28000e4040e40240607818040d01c100705002513030101d01c100802191740c05880300301d49515081d8401d190040140314007c14151229001c26607100640f15102c02e003409940134140c42d5245c509800d10705a81a403107003091101110500944c50746200c5480304607000022803031004095403820a003844011202000c100d1004010419060b4042d00110b1003028030000800c00b1090250030406502c3c014001c100c2000100d03d0203101c2c0201c0c030791002001c20089080702d07040120694030003003030760300300440c510015246860b1140d058070b15028805c040c2000d41841811510f4200214040e884020a00e07407182200d04800552580501450607a01001800581d079a10b07181d016a0303524441d04200803100e10600c00041c030440001d100742d90580307602414403608801000c0408040c05502d008080080c010f403a0000350f0302c1404036010000b9441040100d480d01c4c80640203110403e103400c0c034800c0a9402c0020 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 526654955 1250 526653705 526653707
    0x6070f02070f0501052205040204030f050105060a0311040b011b03050c0f010b0f040b061315020d020f0a170c070807060e04020a0e0415030b010308071707030914011202030a05041b06 80
    0x2542c007101e43e0700d001001020986e02d0303040301c101400c0d0312894000344000f5011082c0504c611040d0001c42c010300081c000e42d182c1d00d044c0415690107103c0a00010b800d5044801d09181603007090000440500d480c85240e04800700001000040701070440119400003101906100140b02900382004000f00070003503100300101084000180c4c052540c451540c820001640b581d48806580811481000003006d040c0c80b034407850084181c4070718450251048600b80c0001c540300099440c240d150100140c512500e4a070b541c1412922113444586209a003403141310a4480200800700040c08100700070414940313080c0f006031800041028003402540100803ca1102c3c0c2c2010454014000031f07200001c41500d002014250401c141d04020105c88002c1c0000080c000449c020f0710b24103002e010306120003408072010070003600c10300c000140400c0c0d4001c2e040241c01080103881a2800060401c001e07481204517104041f64000c43d098000d003941e55003030000740400f055028060f00c607503071a0761100600340302e0 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 526656205 1250 526654955 526654957
    0x904060e250e0907090806100320011b050703080309031806270a0506070303050a050c0301031a0a021224030334080a17090a0b0c0c010e06070f02070f050105 69
    0x9002d4001c0c3c01c0035000c0707031407540308a91a000070110794094035002c1c28410320003120003405100c1650104415500c0110507101d40840010845050b11007160316545d8903d000e180b1003042c1c03015642c50003503010000202c0c0003000110b206041000c0590f40c0c0da6060700c281d0400b40079a03a2010b004800c1405000074014954103000c40702d45204c801540c040b0501e0001030050401504400d810a1010490b1410143c040e0095800380c90b045005009580c6e0303070309400d40140400d12001c0d00c40100c20900c10000c145014406400a02891001d80340c403c01c05214280c82d81c058920f803078100720448001215603080545a01d41c07078000c41c042d515221f5103150800d152203641c0401c642d00f00e00030b24441c0100b940e1840f02400d140d480b0700c49a0b10313800c4004000c0c180c604136400c5c8010345601000003c0329075074007040d00c01b030a56122101000a48030821a200950801060031030150b5a95840c08000b4070200b0096200d0380e201e6488000308602541c2c002d050000c81d51000c4400c0e0001d003014400790303030080 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 526657455 1250 526656205 526656227
    0x110f15072d0201032c0114060301090203030a1202040f0e06040b041b031104030210020319030603030f050a0c02090a0506122a0114030c1b1f050c0904060e25 69
    0x119002c80e9031460302c003c1d100c03040241c8400d0b603003017070030310078501d200ca901908004d80c403546285800c00340f61b4a203814107080c1d94032220700951640040042c103c00600441004180d014174000c0141040c0d12034140e0038044100fa04401c0c01510000100500341c50036014001141a00b600d09124070032a0011070701d40c41c034480e0040c0c5c042c076481d80808a6104082019540150340050402082c41c0c2400ca01139125400007040d800302d9660380e03400c2c4841a0080c050142100d5161383c0d0000e410710b0858040b40c180d00706012000402c2090300100003d69074800d400c600030601c2d010001098207001040100a60030312071040103907003102408000c100c0c10b0b0a10642c0705599803007400100868440101c41401040d000f0618500c00801400202414072003d005015952110095159441003669a440382c440c03018001604004203081556222604415080000c420f003960030010000300080070b407034146d0440c9a00081d246c0c01c01c280c0466901781070b00d500081481c1c20719583c55002e40104286442 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 526658705 1250 526657455 526657457
    0x60803070b0103080d1e051b07080406051804020705070509011d15030f06011e09060b090d02040b120604060f021204080a09030b090c01021612110f15072d0201 70
    0x4501060703a851785401100c840703003042901e24201c9084899150090006a0714900c50205510000303444080c031008039118507401c04541ba043c28604401180e095100c4420310140d51070003201c0d451242c64a0025010040c441c40c05000d855040c00180f06c2c080074140e01c11442c10780304007481e0031861603001e80d503a007040001d030b035156081c001300f0080f0703103000324050000441d8400c0c1000040c2c581884400d80c0d42800c0c002c298101c1c141e60301d024040c1510382c14010750b01d260408110b086c559281a08502504510240003c24045010800194600140c40c459842504824104020441c0074801c014000c1c0800000b1800c000c0c00b2441c44088000c020001040c003040080c6410f4114003402104008661140859890349407042900f500c41c1c14100085015102d0365a00012102c1040780b001d017034403d6014402046070075601d888001d041141900c0c0e0304580540401c802c2c41e15400c0380812420108845665103025070300c0c0c0310560040303403a24491042840700d1504003800d0795201880d105902 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 526659955 1250 526658705 526658707
    0xe0103020f040b130f0e06130c12020c07050901050a03110d0c080105181c08160c061103011d010305060103030c061506030b0f0f0307090e031306020a06060803070b010308 75
    0x107500c0a0300003074440c50304560204240403d80501e0200424100360035240c1c44151260000d9883c002c4005c03240c2c069940d07070750054003624811400381d080ea0003401c0f0740c096440e00040951122030030f4030499200341d12450740d5402c00d00082c0310321b09114070030500414040d04c0c1154800e145440388410a100d00c206c0c1ca100d817820340715800c00d128031181c1680203071058070020422401c0c51451079a00309000040081c1900484d0300e554080c2c20384640e1503603000a1034a541c0483c1e0f030f810f844250000400900032017031019a007076200128603503104100b0080d034854210703030ba039504017521481407449039441c0100e06541e0100600c00034030b010811604507a414140030780c0d02c40481c038107a409000000c482c1e00c4204900e0703030001800342e455003040300749550545500c592110765000340711045045100058040d070000741d00708001c1d100c942c480e03409414400280c0b418100f01d04c5040340034a041d640300c50010307031007114078105101842c0302d50704c02010880011407418600d82d80b940002a0144400781007014 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 526661205 1250 526659955 526659967
    0xe0a06050c030403120203070b01120209010e1905090607022a040510052701150219020102010e0f0606031203060d020f040b060a030e060f040206030a020310170a05120a0e010302 78
    0x1082070f1070141d68040b01c003a40b5640c1007100290b8a40203440b040d250801e11800000320850345501041400340c024144c55030a1b800c01440c452282405450030540e84200030300c3c0c6241844034403409001c0d0020002038901400c0050b0001d02d003025040c8504d9540e40003060300044444030210803401c15400b070360082680d0742d41e00485000d018156000c40e411100400d1400302c602202e943e0000c1d40c10075029550902d0340c9404c4640c802510080800e805030f8000c1c82102c01180c4a10307114078029105200104000b11b01d20521800c0107009501800294005024070006140038042d0503100d50594540b40d007985001000109a0402100c02030b0154060710b242030900e883e0754001480c1800d02420342d0341d88080785e070b00080041000707040c0499603011702008280b070308000c0f501550045400178021030031516090480402907002030a0320758a041d030701800040c40240c0c0903011050300d0307071580903010301020750070020300b82002c0c0034141c4503c0c04100991340055810882d0948900c40038a4010b845030 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 526662455 1250 526661205 526661227
    0x2030a080121020a06211e050c1303150b1e0d02010306080d050703090b09010e01050c010e010c0c030e04090c0605070c0807080c031009080412020105070f03020c100e0a0605 76
    0x4442c40102035081440300070f022900700d400070412111440d0324070090f1441314940111008403136041900c01c144104d01d4052130304c2502d071034008079040556420554075005803504d80c0146603802e64411500c41450005018050f00070740304d4811510340940f0317103201d0010686001b240040400154510076030806070000196442503200c407000c1c2c190002158000d03030764041c0c090013a8100c41c004400050200131301081603480352040d10710b9181c068403180298103400c0e006480541040100110540d80c0311000c00d8006001d00802c541a0150b4807141c05007081c3e8100109004046031001e0b0240d42440000302c0010356903172408040394a5840d00f180c81d01b60302c0c83c1055010946a00c02034252103440310100c0d0407a408142a04042d00440c1101d207841e10700100c07002603651400e406071040b841404108404100000c1601001d481454043e107412101d98605019040c000e60990041c3e005000c9440b040c1400c1244011114107801d1100d820280b5038009081050307240180c000700900400c81c0d42c501 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 526663705 1250 526662455 526662509
    0x905060306062503021b1f03201c1802010e04050a060801090503090405100f030f0606031a090d051215030a02090c0a08060f0d1b090e01020c0c0102030a0801 69
    0x801d20801e000360400d203d402d00070f54484500c0d183e848000c4102c00100018034110402c400246008102925040307104903040e03000301050058082e00303c071410054000010f03402c0c0107213072a440705201d400e20700504056000072101e056115000360b030100a5440e025030781002502084c0c400455010030203940e0034480c00082c103865440102e0a600b80f5020000f003200100103442c2d0300c401580c003005203035580b0000400d0119580f2a4601c405c10303a100500104003801a5418514010000810440e69035543c0101d51003000c095044800d0390706040c4404130b80280000010310b0220300e440d45c24018a0303005c1c43e0300204060400140901d5400807002561424880c0403c89030300200000314901c3e140111540350b502825040c000a800c1c0c000041c442e107402800c901c0c0070b140160048440f40ca0070f55a1a00c01280e2140c0055958106500010b903051a030180408019082d4000758a42001d00105440c1c00c200d4012503040d508144503170780060b6444448107046807000d03107000d60144d40051504c510 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 526664955 1250 526663705 526663747
    0x30a0c110d050c011a0117061908010e010608121c0e070308070b100605120727050319020d080d02070b0c0415090806190b030d0f0f090506030606 64
    0x20390144072100c8011a400101810007406140000e2040e114014030130070003051000301c05408601c048910300700409440c25925400700703014002603001008400790030304100142e4400007070f682d103c41001548840a0080c1c80050240200815403954080c402c4420740c050408142000c144058101072030320681c0e0054941240140d080c2c0c0d60040d140d040c410081d901a480a9403191000301c00b06095070110326031442225803d40d01c2908007040ba0400080190015080c02c00f001420304a141d90a841840381002242c0151030288400746002c048c0f40c104003a031555018410020300c00ca50140e00c45211002c01142c0c041c43c00b50f6100b40c1c040030071000b80101c41c0090000060003041000c429922402070040d121103419085601c00c2410007150768402138003034500c0c2c40c0c103c4404103007040451103900518150444000c12119800d1001c6460015500702d4000098464203501310040c0d00503842240701d51b40785c07801c5201241000041685844060074203401600001741c0b4030b00e01c050006444003 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 526666205 1250 526664955 526664987
    0x15050118020d0204090e010605211b1206010e070215060916091a030402090a0209031002180d1b060804050c0d080906070b0402040f090309050d0c0312020f0c04090503030a0c 76
    0x985603030a18051f00810b1140070b0300380a80742010b0b0340402c8207180c40c8561031243d02d403001040c01020145188034400e00044c4c07040c1d001000803054408112050141394041d1900c004803811925062400a290004860091010030307888024840c080d2507a06c000b680c420202e00c030440a500703000201300d940e01107a034001c4c4040361420003a5485403134010020341c041d40c007c03a4201c03c02e0719520700000491051b8100c00380e040e480302040c034100c17034641d4010701070440c4002d150820001070361010411321180c1c408121203840c0c078030382d0306007540240407880409400e95291840682c505030ba10155030310002c0e6036451042c2003200d071440400a407601102c580a0020b00641d80b611581c1c0303029045010b050b41e04911550130f0089141c05450b01d4070032410090f805a8500e00000e10f03060a12280e048100026204030f0901403010000c148400d1009408240c903034014518400c0054005081401800210348100d0408082d0004503100005407a04460702400000e07862201c43c000303592007034040301c2000e = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 526667455 1250 526666205 526666211
    0xc030804022701080a020f0906030c041a04021206030d0905090117010204050d03210506060d05060a05090c04030318050d030509030106180f0f0509030403030c1502070f15050118020d020409 83
    0x41041c13400464500542c42c030954441031000120020043c03e02e03012241a1f070103610124034004285420f400c16201110f03480891400310b10080d011030140e0344104d11340b110754040402405600e040c10441003441448070710340401800c4c1081c000441c0c211040c458040803100043d01990150b400b0344c1114024500103000e080741c03a62524001d0040880c40720f00f0312844049030043d103000d54190140e540720b100005d024502d01000b01c214030005000250140b0f03000b18422101003103c0d22581003440c0240d2041b00055103a0340b45180007071010703807100b1503045229040070301081140c440d0b071040140560b05041c00781e00e89101030042801020355074860a0401080200e4420480300c0341d00000807105210341c04d11036821459024010b8540550b50b03040940e00030003040002c41d20a025000805114a007048492203c02c40001c00346d030030485d001c3e203403408a0286e4004014142c405070a580c00551000e200d0b562421225141d541914011050942c3d00016411500e0440b82d04803005411001010 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 526668705 1250 526667455 526667459
    0x204090603110102011b02120c03040302030709020309060903040501020a060b040b220e0109021509060403080409141305070311031002132c070c0c03081b010c0c030804022701 77
    0x781000b00c0300d02c0c0c8a58099441c2000c1826029198001c01c2281c00c034503001403080c22000d0789058183d600c58400c0701040d000600002c00183e500740030403401030031118405030300c90030154510f605208014007880342c1a40104820010f81e40c010030341031241034000000146605203c03001c500a4018421001d900444031070070700750841c2d60070780642c1040c0d25882c410002d031500380c4105402c0f0380800002942c45441100c40103000081c1900900700c90034040d0445051590381d81d120000354109400107540291900360045081c407131101000c1c0d022441207200560807a180e10b5154480c0070500002d022b074001821145a01c1d00c0070000f0042d09440020b00715600c205000d5030021100707050007450b044080451004000e000c03500100c1598944003030144410391514901030b100c0000008040302c41c000b2200300040441c40c10009000c1d05900c03854407080d9544105002421540154000e0b000d102d0540d0840c008a81c2c050b8072140d200b0f60603120f03503e52a840407a400100b4a482000c060b1400e440000 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 526669955 1250 526668705 526668713
    0xe040c170f070501020a020f1017010801020a08060103020313060905190c140102150109050601020c0d242c1501080a0302060129030613060909140703080f0c010204090603 75
    0x300c607a04258103020769980399140c600480c0c484405d04030207980040308084030405031500b060350030204407150400d10a1145403124004200b18240c1c1304d490107950110340d025009803c040c50355804039091800310b155150041d900e13540c0d06e040c404c000d0191550340d100001005007c000b005400384d0004140c0b00032082c9840d000c1c100b03010b140243d0b0014043c0307205903c8207500000301e0031446461010324004582c00c10007500000c0070001c280504602c05e4403180746407078840b51020b9000901682d00e80111041078010000c4c4c1041c00d11105004c5071803c01c404000768070686000c0804821a200c0303060759a9504034142c0351401c211200501c0b102c3c040000610200000389a00c1030340c0c82a02610030030780c0da58111101112080801001c0048802e20003d0003002c0d450003150b21040c000e080000382c55011211808680a94004041e440e5681c0c1c000b9003441007005503041c03c1d00054004001190441d03030b42c20418040c1d4603031500c002c2804224042042020340598014040c001d404025055481c14 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 526671205 1250 526669955 526669963
    0x50f0c19090801021b0724050a031425080402130b01051b0a0c0902030712240b0901120b10031512110405150d1104060b1207030c020a03090e040c17 65
    0x2a10a4052041240000701c140300147ca4590310390882c40540511021500c00b680c0d164090f494102c209603070768a0401c190014100080e01a0001480c1100da402490046044002040b0010300901219504100041c0d8442248038440302c1088004200b11009070300580c1c1714011000f612082000412581050110000d8140780050086403545070381d566901241d005c2741700550b845030001d1660b40e18006901480d03080000e0700740344004054448990050080d0f400051600420180d600000c0c00701d01a60348900c4101b0310b50138400040010300c229400050900804800d020240f50b180e040c482d0203240c070300c1d50410003010406424002440e83e441e01c034428500784046a13104525040c04104070340140c1d501d8000d02e02001e04501e020f181940c6410410b02024540240e1090301d440010443c603113128040c000b542190304850710386081c4001e026060b58550a00d61007194070451200000c81e0340043c1e100216141c02c0c0c0c52003856207603801e00c14452051600a034101c030501004400032000002 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 526672455 1250 526671205 526671247
    0xa0314091c05061f0302091504090506010305122a0c030706050a080f0606070303050901110c01051501050a02060f061f0503040c0e060d02091008010519050f0c1909080102 75
    0x809a0340356030368403000c401c910284000054500d1004c0a0b0500042c20b211010582003151950301c030401c192031600080984540141c2100c85421480042003080b108012181039842e820950b0390410507202100241444c400c2081500040541020022288240f02e800c07828603019054031241c03030310381c10301504a0707001ca10000005558032000681c100130b00c842041c010712006180c9840c240541d00e04801404014003e00040c1d50380e10680c480f6400d0140013040c0b00e200c2e020010410b403030705e140740410907281c0c130907810b060104c10002801c1e220350101d086540302d01810043e08290312220f01081b1501840c003130002c141c0001c58070300d200458010001d94480d510580865100c0f50b05c681d0b001d03000c0703001903640a400550865a000042c070b4108140d40d0b0111a5410103c180c1d60740740030360b0f82540c2059500a07000112002c0400603c511801426030143c43c0b44420140c9042002d64520a841a05107411041c3e00c06a28010040c1c498800c00c0c0060045c4402035445018456a4805040e609 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 526673705 1250 526672455 526672463
    0x602030304030e0108070917010b060d0b0108060603090c100512010303091514030112031b06140705030f1b071a010602010606020601080d03050c04090204080307030e010206090a0314091c 82
    0x1020320b92043d588910000380c807403403d80c2d803055a0b282c40e10652030606009010b03100304079500c4004a40c07003526440050010880c8545020440c03110f400009005136802034681c5004160400401c00c2007140041c0c583c00c1c040e81601c0440500d00d0707100045540b40202421860201d180c880000141a4403a00d060701b501d5150000280076071460b5801e60f04001c0340401c01062602c240010003000140040d031500650283c01d160154040315101c4401e0030851400454156a8580c071b4101c96a0042ca40c0325880f1059060503480e504100803030000742c0d1401480b04072014410001c500d40c885a91080d0b40e4050780c0200d140358004009007505100c2c000900460300190301e0088001002d510000e41d4504aa08060140003a180540011005490014031407494018200720000340c100aa02c000d000070080100510740716141e501e0002c0400490114130303811540a4004e010b402080490b99410065260034405014044080c0c0080e0030300a07020025440f0790324283da85800c040b03031141180b000b841 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 526674955 1250 526673705 526673717
    0xf1e1b05060c060f060109080102071b170604080904110c0604020306060303271c030203030105011205010509070315050d050c093706050a1e091b05090a0b04060203030403 75
    0x36a800e1021a0151104021990344102e02154002c0079022845030046810314020074019110b8240d2401d981c1f001d14100d42c00c480c01c46100e040146106141800780c1050040804c6e015010580740382c0d03800b40078001403c403c400260248469941782d001d41611702e0140318003900c600e0a040c40a44074802110140e000b4052400029000c1c81e000c0122090002416a43c00c0580a6103070300302071042020b4001e5401803076109404007440058055540100e2103076005550325814440010055442458003880b62800e00340148a59034503030204550101e80b41c84d000640c0860b07190340808043e1241d0120780c105038014004002c1c48070115030112004400e8030b01d000252513085000e45021062200c01c15000221f1855030002e044440d409034102043c4a0081541903c440c005408184e8640c00050610050005821002c00c00d04c52400100aa0441003041c90120340c61101082a00f07205801000400100f424055841301c0d105c4007d0400a9245501e898807401d01940e0399105940c16008100303 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 526676205 1250 526674955 526674959
    0x90c300b0306071b110d05070f0807050108220206040603090212152205010507090302041b0516021809030c100902060403060e210405101701030f1e1b 66
    0x20300241c510b00884030340d03464041c100e0480100c1894188280d004441703515020800305141ea48260407414401d0041c00035282c030760300e00b090070260702e21180c4c8108500d410521041125030707049411a0b6102a0070501403601006401d009403610b82000e600035840000404c0c042102c607815031100001510950788030b10040440107a0b0b075542ca4205100d041e00c0160b040001c0d6a113014070511a070281080368204120281c95580d190941e1403c80b4240009207070408100150300d81070148041c85040d601001030f8000e0003560007000c9204162a9003000000c406281e011525038840c0d128080d1402d2092590038140421510789079400340c98510028480c14500100142c110b1081d010380580c014001850300340780d40d81c2c10300a04580700c400f1a45004041504030703001c1800704400500d0380c000b07090542c0d80d0b081c40e003040b0211100c680072000b0496424010561152011b4076281074a421140540303c4054a203170590082e01c132440001b0841441071082c104008008a005080d024986044180c9603 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 526677455 1250 526676205 526676209
    0x2514100b0117061507120810060305150418020607200910060e010c0b0709030203010501060e03121810080103050c0402070308070c140a150510060207090c300b 70
    0x385401c107480141c1201034001c10002c2c81c0c407661303620010103106a602e061603030648400f000f034403081d810500440c5a800400c078447c00308154030310241c800d0307042c2007080d0304021400c800c21940010105000c1c0d036950960740000041780103490480b980c0280001c0d50f801440c50304a500c03100c4c0e5204010011200040e0105038900b54440e01d110b41d46900410b80c109182c084c1c11074052000b249103034148107003440c01001250000744024801c114903114807050307c2c034507c181821a41c050344140e0800c0300040714042c00741d50101e600102c00f510080320b2a116429051354076501601904000e5114120340220600d03150088407050480e4041c4c0c007030310010b20b24081031000b640300344540100041d074480c0010302003d00401e250140140038401c11004210041d035614640b140ca401c040e180740c8503004080c1290b500d94010a580300320041c1d040300030580b51540103035132000c40b4040e040440e61600041e0360100d10803040e12280d0321441e481d0f03000c00707030702d9000280f5005445884a0001420a51010024 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 526678705 1250 526677455 526677467
    0x908070807210804090603050309090606130302060318152d040201081801021b06011e05130e1209010f08060109051c02100e09010807030203032514100b01 68
    0x407040c0c42c04000d5403490a02141201c1d54049004840c1d4090034080810101e109109003800703184a000216a203246410401000c100014102d51041500300303e55584c40c10340c40c96000480394191604d9450b900c0e11074141c2528019201e01d200a4401e0020b0000c0c420002c4a90a000e0301c4112900e00400d1030940116110548414070000c101d44944041401035100d1605668840010401c00c2d100d26007200b010703401e981c81000c030f101c0c02c05000c0c611210407844c28003140d0f0044c801e5030304992104807492510700092a003403051a00c107480c1d40f804201c10980350f8201c0d01c10111902c06030f0b48142210351000d90b05401c480d80c0f10303000881840070385107000e010300071050040c4c0051710b6001c800c4e03140608100c85004403040e205000b01c0422141001a190101a40103900c0ca94590507046e00710001400008501640400015030100c0000c00150320b003c021a110701561000180309000c00c0041801c001c0c51460004140b800749001049158802190a10140380200018406d550805004640c0 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 526679955 1250 526678705 526678709
    0xd06240e011d0601050d0c0810240302070f060e060a0f0b010801090c0504030501140a1424300c0406030c0b091909020702030c0d0b041101020f07060908070807 70
    0x198100200b071a0504400624002d612100c1403400d43d142520071002101a01d810390044000f1078480380074400400a9044078101406801880c21150014801702c4003074070981d50441810315030b0004000c824441d07401d80c0e542d83c09802900c244203510070610b440740d4030305040340c6415a80b46059035030050646a03004a026070380c0705075600c07d0380d40d080154030402000710300700c4401409020000000040c80a000d410300c3ca6140c0c2c0380042c2103150100c0010159103005075103400300c1c0600d004005803200d20b0100911041c3c510f44100050100900100350310b00445195100200030b0002e005c51700d1400343d105a60031038001001d450818a00c00140f1081e50303000e002c000c00c02d884255061001d540120040d01c4600401420440c800088030fa290090707000b0740e080b01001e0354001644000798201040aa0b4445605948001100c0d0244c0c546030640305000d4402051080e007607121241070f80c4200300c1c20792103c50b900151c0d60010368030f20010300302c54014445d00d102801441000140c01c1408280001 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 526681205 1250 526679955 526679969
    0x2030304020f0d05251806050a0e0906010306090804030b09010207050706020c010c030c0c050405090d0f020a0f0b130510090c080705011428030b1e0a140d06240e01 72
    0x210058101100004000740700d0085d185a24900f000020344c0906200b2008005100e5540052070340c1c1000300b4410714810503008041d801c040c10050100300d01c3c00142d0141165080540001c1b015503a1510051074481d590020344500344490a000b00b20b4010b42c0100307035061040084801c0d032545c420007a41c86000c14086207000c40e5040384c048020a0207a80031140e554410210800c24540320400241140c40684150180c3c0d8400e8152290b42c0703030000d01c1c904400240d400145001543c2d43e443c00c80c2e40a00ca04001d1107040341c0c00105500803240700c070f008280b5a03c0401da0380c108664070301000040a00c088103030303030a00f40d418000078042c0010880c5400d5400603076803c00d0b070b90240048400070758448035041d440b9510010a07041c40842c0034000c0801100340d503901165a9464204100d8411400050100c80c10398000300c991351540c8900130402210710466800f000302817450001005202d2200c0c015001078100501d1403043e41d442d241030922038000a413004c0807191541c1d05070300380d8402402070708 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 526682455 1250 526681205 526681213
    0x7060618140a090c0b090105041703040303110708060604090303020d061e0506090f1018060f0305010602010216020108090709050f0601090e0903091c021e01030605060c0304051507020603040302030304020f0d05 92
    0x200c0304c5c250060051610001c10b0501518096580c859032860700020200340306507400109041c0304041d0b2282c0000c42c082101c2c4000c00381c1c5130505d0f0000b0388905000c0c1c90588615501c11303c8004040c000d0301626080c5140320010070459070345414422031a40640c2040c9901050754102207a03d19100c02580c6d040310000e40082040741d0200184140f0440c510395100c02d000d007a10f07030018060300c40f00006024003416552040d030b00d0866800641594010f82000041da4010b0281050b00030544524880b143e4092a00010a40740c2c0603a16081c90401d801607003c0380d0400d005c100004420090440c050030b0f0a82e0340088481c0c0c4c51400180078a0291144400da400400410005240c4006c0d0100000350050420191722a035174002106031060f0301c02900320108008904090b9a0948982c0c40200400e480c400d240412a94200c3d0700c900c1180038841c0b10b001101081c89003881c0d280140c40e401784d8082d00c0d041e5a8107260601968a8104440881c403c551007242e441aa0805560340c2a40703651143c020 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 526683705 1250 526682455 526682459
    0x20a1e0509090a050d2604030c030c06110c0c0306060603040b01090b041107060c02010b0a06170c1303210314040605280c080a05010806070507060618140a090c 70
    0x305080c41c0241420905110f804880000f1650500c00c142c440303011510f0b00021746600b4004001d1585060160100080751242004046608032601d4114950300d461b22019404c240c0c030b020001001000062070500342d02007000c6030340590000b84410100811001ca0320203030b4507081048084c1c4401c0318020b00320302d1500300401500c0840c2e00015031007400180007041030300e505030003100b042d009001c05548036a110201851204d4080c4030b14604404161036118a05080203000340100c0f0380404500411b4051380001819055903101b0350751031109070000300200c9592418000028650484403460f00010403100400140c003d1080f0114610f944200039443d5449449040c010600202881002c0c44905052500b101040d071040400d980240800545a244c4040052254800074008c0203401d1425005001c040f4002031000d60101c0c02c0d18146580c1d000910740039000e00b00139440f07507015101d40c801055070425640c00ca010710141c403a02c000016511002001c00740c41c1381d00000340081c0003c10302 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 526684955 1250 526683705 526683709
    0x2180903090d030203070204050f0105120f03090d0303111201030c0e071b03120501181a0307091d010e010f0f0911012304030c03030e0a0e010612141003020a1e05 71
    0xb8040b140d406401a00e0801ca000d8002c2016504211040c0319a0214500107005910745080c1012085240300c0c000e050750210480c9060360303441201401c034810159501e15008040c0300b80c0010b01c42034518201c013600e0350100d0082514940080c0011140c403074144030003292200703200c01218418001d65840781546507800740100345449100006504001460007448151003250181e54000d00688000d000e0402405094104a0b1404140c0140c103c0e040f03841607a02d594005407040c03c1e5070185400080094406880690001c1c100496000d83e5003001000214007a040d80020b001c41c100c036409000101031040028216415004000d0814141c9088040d071944604a08800b0005415050703540c05484004c030300321600107a108030f56030003588109104150340803060824a49040d507002000c0c6080c00100f02510744140184c0c000c201d40f01103207e040304c03a26000382ea02031400084c0c10520b400c0800f54494000d030070740030690085280840000b02102e144440300f041c4c841810140c03498a0070481 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 526686205 1250 526684955 526684969
    0x2a03030c06180c0e060316050f04020c060a020306100c0201051c0f090f02270414011d0c0325060e181609050a060903080307180b04030218090309 64
    0x2005503a410750b904000c82000684200d0345021901807482203030b500b45440c08044a003540140882c0c0250403a02e84500c0f28620380e00c5800c00c0d40c0c0104c1e908142d107540440440d000307018500001c0f866101e01c0c800d0011901e1151300030b601420040e511403840b41203012040da001e00f5521030003400180100040040044100002016a80c4110010892907000792440081c0c0b500004142d803c42181c4488004602c0d0981e084002141c90310915810040c1e40c605d81404800b00500c06404104803510911081c807003940801c64900507842c0d16448103481c0070308665a100c210b80118005d21441211501c0c050342003000f030400e60901c90380401c08504002003183d5105102c4c905c103801c46c40c43c000280c5101e50b0040c10500c11041d019807586a070700500c10003000d4846903401140075042d103007000c0c880f807a4800b1440041d640c203c50f50950360740303416200700d514002c5245059185e011450300420000c841d54020002c4a008942508440c4600001a801407406aa07a02c043e5403080259604c40c2c20080 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 526687455 1250 526686205 526686227
    0xc0f1206010309050d0f080912040302090907090f0608010c08090705040c021005152b03030b12011a040f051005220e010204090f0903020c0f190801092a0303 69
    0x21502180f06600c42c1d032032900c2c004c5010b0480c00800c9032190039a000b55440341e041a031013100c41000b0100722090041c600494801e41c0000781c010b4004400141012404002400040000103410041c04080900150041505016030140380d401e113007200948921442c8a280618017500240000a00d0141040000d0941c80c400d00d055000306407070181500801d04c10075200f01071078002908020942c1e001c1010400d41c0300c0103481c0040300040c48201c0105650258001c00380d06043c0003404102c9400021300e8800c0152004072550700b840f040d8603036484650081d421000c02aa0184004c600ca00708020503a00115280341900101003800c02842c07030b200c101c10902d8025105915000c5000d9560398007914254010000140e400060803c2184001d1041980c203907440301e000c101d1181e455800a44946002900c03910a04024201000c1039403010400b5034410141c02d01d03495002da03075240c0315002e42900d0100382c4060351291844040c0310b4009034444020456120b58803a43c0742140d400380c032903032010 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 526688705 1250 526687455 526687457
    0x170a060b070605061807050406050313050118051e1507050c160e100b16020a0513091407030b0412020a120203070213020405030a060f0924050c0f120601 67
    0x15400000d000003100000c100e140d0142001040d9454103105001c522610b04840314074a2084030100103c16a100c002d80302034800d2850001c0d81c035101c1e84030000f0890701284001c4c2295182409500e28003594661b020000c5102d00e09445078650643c401d25030485444400007490340001108600107071a9800c80c56124140342825800c00021422581c6403040a09a0614621001009000104644854903803005102107868100c034203003c4e007502c084c090110020702003200c1003510340455236000c040300080e1001030070540000c4403090401d001f501100070f083d111080700340124030540f040132900200791b036049400b0100310703152607031081211101e0640e45011402404030f03400018010181e42011580141d001310b80343c5460340100402d0314000b5100500c0d25104000c20017507a00c0115645c10740b1030300500300080a0f80140d40c200d002d88440c0c0b40081440d003a05500002942080807c01c1200d05030000410039543d43e88181050b80c4201a4485603400060080c1c0342101600c1945507404101 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 526689955 1250 526688705 526688711
    0x70504081b0a170a0302121312020a23120a0b0402060d0e1b030d0e09070f210618020a05120901150321020615061e030c09041803170a 59
    0x1650b404541d09000110400c000da80140c0c1c604014160704006c030540500c1f5510166150104070980500d240016120b54034807100c0544888080d0754030a00070100400c4130108402540301c442e40503a0001d846400090300c20740f0a5007100180c2000081c500c4d50b01580940c0c04d034000d40f60358080111940100744040189030300c503102894803d00038800418a0083d400c1c2d04142600384004050402d85645040401c00103000b5980e00b641e566001d4468004840d8240f2103207005000e8800c030347c1030b0f04105030030074141c5a000301c8491521165100c0002c4801d00c1f1403404504801680e10003d0b882080d012000107241440055038040380304074034a400110b040d00000b50741c103103030b0040c2005554a900954981403403040070048059040003410107040e80e48040c00c80c41c07030312010100006004140007409641f02290006950007040003840220314002d40c00741c0c892803d5240d500c0541e01046c0664020b508255006660190301d00c0040c00481c0c1c50385520411403040080328420074001440c850060351 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 526691205 1250 526689955 526689959
    0x7060209120111091509031b010c020d2003241e04030906080a0204030305161103070f0f240e04150314060c0403080f030a062705070504081b0a 63
    0x250074401c10b000f46202d2040c19485001c00d40401101d01c40b8481801c1c100e010401402c1340c075503404150402d1081c9415102c0e050000c980300102c40755603103950000d400480c1080294140400780343d40380121420000e9002c031111090b005d254460f01100700881c4200b180c0c0250f502c40e500106002d80c0e0100c40140044041214002150314140b002c0c0c5080c0c02080d0040021302c1415804804140d02600390581546000d00d540d81c01062803003610800c0d03428440307a5860104002c84200c0ca411803200080c211a2280e460b02c402c2c0d100c0000034481d5020402d8450400079001e0445404041943c940f0b40c180052130f110340405456190385601215409aa41e044440e10302c0d200300f0a200195018103e002422156010f0141c903180c000350106419000500003040000c0107013080700c80c1d03184d0682c400c90300e0391035540349403003c0d10850300292460080f1800702d004c1c100c0c02d44042074044100007410700458480340e1044e01c5602ca98043d919294006207030382ca0036040580b85509145002034001c40a00c0c1d = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 526692455 1250 526691205 526691239
    0x120a0302030304110102240f0a0b0f04020f041d091009170319020a0909180f1e050307060209010e010807020618070905100e1e04060f02160305130b03040807060209 72
    0x10b001e502e0161491f0461200380040007040701411a032129000004201841400c000a82e0002d4902100707072040d600041d40b1000c131040e86050b00c00504001d189202080020340c0034001000045400080911440c0e5441c1d0200c92103000784002c0d26004883c1c400c9070302203201011541c2d0b000411001ca034000541d50702000d50340707900c01041c01008560b543c0c0c514505000e48201607583e1285c092002460100d914400b280107885040d401315440f04081101c2e0303a01c05900049803583c000301800502022450005002031a0024130314a41d00340e80e241148000b0900641e0845030a88180005030b001500041000035003127000342c448801107003180d81c4660f0301c2d0701810a40b402120152518020600104402c4000c0c9e00c1d0b46401074446a40d105590008070510394103000300a1016200b95102c4600444448140d81201d240702203e10b400e400f80643c508025040d9030111a011600c011a060300003071031011482502d00481c0d010010900c0d00c011610394034065004020020b83c044001d40c034a03070500b = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 526693705 1250 526692455 526692493
    0x10090f060c0c021e03160b040e090f0a06060303110a03120519060b040603390309080a1107140d0b04030311031e0f010b0904050406060906030c05120a0302030304110102 74
    0xf00744e82400d030300c800c0524003041c1030501c0003e24807990103030b80d180c80c107212001da01401d9506440f10034032407220039a6070506903443c02881d13005011850242258520034420160098400d40f80240ca40300c0740400d4200003507030b981c096000040c0004203214004072459050f41c2043d0b4000e50341502e072a01039110100090f040b140e4980c820341c0b0600000400700b2010380c041c0075180450f80074920141144040c0c01d4600480c0c1000b0b0000c0b0030180900d260610a107000341d0010044640201c03e60f80c54444030b280c007070450b160f00b46140c14644034081d800107600c1200c2d44403a004040241c52030b0302003201d07991003020802019004809040e02e804070044400e02c060040c3d8425904203000c0c03420010003882c404031621000d815078240d10750380320040c0b0600646104035100302e40151400030345a541c504211006000781e81105443d1405c29000106200c1e08001020984a013121101209542e600245555400401c40140584c10a0000801007602803070003131501541801629886a002208100c00b = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 526694955 1250 526693705 526693729
    0xa181803120c03270b06120d0e06070c060f020c03060c040b09040e0607260615070303060506030a0f0e011a0d080d050c0a08090703170a020309030106080c0310090f060c0c02 76
    0x2c1052804c500340541002615042441a5003600c1c3c04007184901d1034888402095400130302401c8040c0314001c3d12031074100e0303034405d8009900c50300b101d80748c1d00010414600d004804006204150600d02c0318540450b08502030203250070118501803601c1c140100680005c4283c0b0390007952141c1d0740c4025a42030000c0b6100740070507910450f11103440e0078850704030443c010440e0303d1107440c00704024058880c00824040c070100c20f098143c85130a41e180840103003003180c0003150081b00101c103004601240d90019991494074020610000d100c007850a800c8604d0048a0070b13644040c42d1090100d4100b014000d0b801f50f016001c19807900c000c2c0d11204007601c00036101d2021341500050b480c003140b60b006651603081100f0300054804140341d40c542c0c002c80c2452400e414070a07000000c1c0ca20400e402002210103444d006002400350359500c0f0703002521460074071007007030182c010b04103201e42140691250381456540558801448215a290440182843c50503541400b10f030062500140c0d8420b100860 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 526696205 1250 526694955 526695011
    0x80c13090203070906050111120403031b0c060809010c020636150a1b12021b061003060c110a06050705070615050a05030a03020303011202010c020a181803120c03 71
    0x5041e1b450329000500f00c1d40c4200050005800c05201159284241c104840c2201d03054603001c4415141104120006051500020001850303850300158043c1c0004480c4d2051440c5402048140d1350240280e07118001111007400307500480d035034504400c0c0701540c51141450218400c40c0c3c1480d8046140380703000f400032040f003130b0789072200c08100e03101c03483d03005602c001d946049003613903411009070026010404040c9900c00058011400407007480a0000070b4400c181104201c804a00381307030000d00840c0843d808140c590504004011028078002c030340c888902454031000f4402c020321500c0310750040001601c80b10820404202c031030040f40c003a005804506100303003250b0701c16030300e418200440d4040340ea1080d8080d4025014072000300e0303004402d480c1140c5152240c8a9100094801241c085140e96002540204204804074845160040b0300181410241080040d03101c0806689040c40d01c4c00401400039290000504074403000e07401001c03007800181000f046d81105100c1c5030781c80410f0585442 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 526697455 1250 526696205 526696211
    0x2709100608192d200d0b0f04090317010905160305250f030b1909180209090a030810180b01140c03092107050d03050903060708010519080c130902030709 67
    0x43d21507003441080792050f21591341d024900b8480d808482c2e10b01030303800c400e940c0b203640343c0080c015510b690810750850400108200640b01c0707545009400700070001da4000710742d440440003052400c180e1213810b025005401c06400782000c2c014049010780001801c03151940e107003c0640c0031740702c038091046207012155121101ca0181c181401401c81d0341c04001d1500c04e00d20301c4240030440c9080344100c000e4500c5c4034000b251160b2a0740d5600181080300900035007180020301000850680450580701c0c051082d607607495280c5906580c20384030942c0b4025010404003880381e0104140c001d030711940070280d043c1000000185100b40750299030700001c00c17051550b000003030020708030b2401940b620a00c4041c0301a83c4480242c0d071141c1c0d565580c19008060003031906040c04014580a007058480c4040c005081768680d00c0c1c04500144106420311a240c0555003201140c244018030390609401e441800c0014142c03a4154000c101e00300582032445030305566910080005a18140300725806000440804 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 526698705 1250 526697455 526697531
    0x3040b180a0f030510060e070320030c040e071e08060f0907020715021c0807051c060e0915070e01170109050610020d0c060b0402270910060819 63
    0xd4100024aa800f0385500c2c9800010700481d54100d04258012200c1d10b000600c003001c101c4070b040080f2203a02c040c1a6a44084100b10550483300000c200342c40142c1481d1415440c3e20900365668280300001607250400500c0300d4004520924105510803030040002d1200840040403071a03403d4103840791001a0401c00003480102484a0000007d900e284020641410724050200796018101c10000c200030b0440b0104600b640b081003950100c2144440b0840d400f5030400420009002e40d200e54540300a070200007079054040030401004000c40041440c1855461013811581014421903d605001e130351701c00c503001d040d500840c2134003a02c2c507140b0025a44c00d0a5080081c03090084000b04110360050000c8038000740c0c002034142c0119400742012400030018000180a4000c540384140380b5003075043d6100f5522009001d50540d52015500100e0329103980350f82c0081012a070181e03102044001c00400e40b00001c98032151058000b0000020744016101c0c202c22000300520008000c00c0181c002e030b = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 526699955 1250 526698705 526698713
    0x100b0a020a0606120f060908040e010b090a0614070f060f0905030c01180302101104122405010503030f0706150f0e0106081603020a0c02030613030e0402070503040b180a0f03 76
    0x1a04081c007031132401e141c1202a155103524080448000040c003081d2110403581c1080620000da0303000c0c18401540d0741c0c0d0303980c603110215002e802c050603c1d0b110381ca401d540050f05a000310041c16200010384070051802c101a161404e0058a507202151040e580d004c1c1d00554000d00d02c94408071074843e40c051980c4004031243c0d01d0954555030403910807081d9007992a000a6000181700b030124542e19000305102075640b21914107402140d116501460003018250100310381000f6001410791300001603008685040c1c520350807108240112a09940200103c41041a4a034060f1894600c42c46000c20084035a0140700181140d95001c5802050242c06c02d000d80b54141d004035000d040203141c251140d01c0d2240c0e000d8a07044162141400741640040c080c071480788580340c04504280c020301140c04074101008140c14218250340107034001409030000500e41c0c070380723070086840e030b20740000080d401c203410a000d0440950054089011048003034821240a8407000011001450540c415030050351440c10 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 526701205 1250 526699955 526699961
    0x3110c19050a151e210e01050a060308040b0903030403062c120304030c0206190e010e0102070b180d0c0306050402040e0120160c0e15010903050a020108100b0a020a06 73
    0x818800c1820304442c04829401304032042c480204442c920130710b01030f1280036110000382d035829084290408090b40720320383d42031300035070503a0282c0c074001c001555440c0341c900d0440740036000050001c9400c10041110a4448000d018209401011b0fa1310701940c030f682d82401c8039045e02040540861038484074001ca01030a08074120402c1d80e5002d804005c00013000001248001070005080c031103800c1c162019922144103841201014006e105480d80e195500506007490842c00303140042c05d40308400201d54400305c0d62500700c448100400d805d06205c1140501e115880b011102d400217800c224140116402d2003003900214000d07000007a031030505005000a9442d0b00300744007502c2c1c2c10414000150340d2614030307100000c18005401606d800e03c41a4003a81450003c070090008941d40c440415001c925002d40350003810b1b11410300819455040041d207032060b43d4407014080d42c200401c1c01c8050b50103104004c0d400a9029035241d231207900d404064903180c000104100060744202c1c08603040200c1c43c8 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 526702455 1250 526701205 526701209
    0x204140f010212040b1e0c0a050610030803010e06040e100204140a080613050313061806091d0411090a050709050906060a0323040f06111603110c19050a 67
    0xc4050540f03007440488550303031441a0f12130507000741170002c0d410394400480048a11111b80482d4a2580d50162403512a41c81c03e60840c140c45900400c4045001503801d071120b8011698806210b90540e884c0030328445040c0030080ca103c1d00240c40c0e050703401f94264184002d48038500000401a296801e010f0301818070000011107a0041c000e04038203014070b1304002603071540b00780040e01d0400301028a01c0c2c01803d5010f007501071400f10541c074402144179030300141740d4000b00b0610950703584800d580b600101c5107480d442c815000c40054036007410a0f051407004246038845d029080f40c40701100804045402c480007150070b000800c0ea16000d0185c130a5110020b80000d02c0200c503d0082d908041c0005541880341c2a1901709240c2e07560400715403000310b013504c1c0202e01c0c0c00588103601490903040500172500d84042c11078150b480e014441c803c01c600102600c51803080110411401980c0e13035026a00602050703c41c0520388140042e4410a984503241882c04403415100103481c00c3c60720003401501c032096 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 526703705 1250 526702455 526702457
    0x10080c150409020703020c040e03072a1715070e030d02070303020c0625060c080c03101802070b161103040b1e0d0e0c1806240c010204140f01 62
    0x8010481180e640142618103455403210010b9840c1080d01d006c1c0e1408040000075a0014140301d0462072105012001e084440c0c041c0d1103800c03c00f0703e8190f214802e0402c1550350508032403052001c0c0080800c00f1030b0b14003410145c0c01160500c00d25101004180d80044071480006aaa4498441542028400101d04074540d000801303141d4115580030351100100c4002501409002c41d551000c4025410680b168000401100c050103085007060000380605079100c40118030154080341109541c1001c50303100d9100001501015070a003002003000d140f40b01d8803414071075000e10266020401140400d40600420303071084004007201540034003d25058050040240c01c00c1c0001c0004d00c040c03c046681000c4604100d103000d40c15007003070440d00d010f501007440255140480110308a1800210340058460441d20702560304104841d01100300012a141a000b00c0d04040101c555003100e10b10251045040900f42d05101000b00102d08a800542c0f10400d11028410114102d00b00301100018036082 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 526704955 1250 526703705 526703719
    0x16081224030a080a120e060a1508150606070b0717010515121003080d090c0e0c1909270f020c030a12020d0c1701050f100810080610080c 60
    0x1180010751100c04058000d0b1900000056044d8818810b00c80ba40056400140c01c10000d9200f505440d520101200c600540c4d618000190034084e081002400840e40500003c0c0302451800000b03c40702900505016040310040c0f00180c00202500041c9114104541d01d50001104071420200300e4038040c0c0c441c030700a0703805440f0031014180420845580481c1c0b0300302e80c0c030700e80c80c0c503107440080356115072001e403a82e90081207201035007445401c8030a90f1409011700c407005580740e5007510600c400c06d4034043c0c0c0c0c85801300030000c07101c08810340c030411055460038100700c140d54404020f960310714460340190010740040a800c0d034a4a443c4241d011070805500c045082404c0d25400a42d684030300c07218242404045494264110300795011104500c00d1403c1c01d015514064501030800581c0c00342400001e4007800000c21031342022080300d600da44000740081da0554909005031081080074054401d0000541e10126103a04100010703805440072224002c001c5180407071007818030364030071542e07445460 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 526706205 1250 526704955 526705021
    0x40605011a0a03150803040305030409051b031603060302130929060121021603120504021309020607060c05090102060a060605030f18100f06050301150b160812 70
    0xc41c1d6000c0d2031000500b4280007400103803040320340b140d05545500c012130b50710001501108010740030015004413050403406022980368500c01d158030148540a41d02d820105000103400200702d030720201d80d40d46960500007a410380300d8000c038132003840246043c45125240d032111001c00c6038a1b1150656401c42c6031000b02680142c0059148200c00a41040c0c1001900d102d52002880610090580522404011540d1342e0036500302950500c41c0800075804140c025148614107446801424450f550040c0f4070320a1503503000b4803000908101d10b059130040d405001400c00200c40d0700c280b142105554941713948442064000900d44480103042510071403e218040244640200c142c1e50451000d2003e11001e6a8080d40c03401c02d01d40305c001c04406031140c8404901540c0d0507500180c1444403070241400410380b24020f060030303030304e400040ca80948510320041141c0420080030303229000e5000160342201801c7e84425203d41c01245420320801102d005001c02c1005910318600f2403d0710009103082c1c12 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 526707455 1250 526706205 526706249
    0x2070b0c0c0111030c0a030f0f0819021e0c010501050a050604030c09230708010e0703060501050708070302070503030f1c18110a261905031905040902040305030304060501 75
    0x41280080503060183c85000f1101da59401e00a58020b0f44000e000c0350b000543c10b090044c040d208000e210340224444a00040c0c440d44075032445ca10410800010701c070043c4000242c44001d5111391260b0b2072030341c1030921441c100c2c0c90000c002c2440c0d84040002182075410078042110804260723010921034242004100001200703c00700100300c070010702c40001c03600c070745940101c2e42c4002c3c0d034603d14014040108024445800804883c141d13003c003400c640c944d41e5005010303400c56510f8020320f070200d04e0a00c984400920200d0060141030311070b20584000544d1000820f20310340080b52403610318100800c031091101e181d102080800e100d081c205010006245544050b00089250040c6c5154100c108402440cdc541c0e0110200401100300405104030003400d02e16014441509900c0d0503000342c0c0c00505d603d188540c0340f81c00c40e9400002031468038004e040c0740f03c04240341c481c00e1018000103103c0011100c0b0a84007030700c015400350700615070b2840c003031400c0002c4880c160884141c10b404d22031021000303 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 526708705 1250 526707455 526707463
    0xb0a060e090f0c28030c02030408070506030c0f270d02101d060301080c1906050306330c0c15090409240902010f050a08150d14010c02070b0c 62
    0x20140c0000408a0341c0c4814480a9080c03080300109000e1000e41440480c4d80c0c0d440c071801848949045d50704129403065003404a840c0d205a100300e0f13085601510301400145481002550410034801400303180544503884002030f0b40102007420ba40c8030041043c0c41101c0f0b81880c1d40140d681040b903086100541e5a800124985842c0e0103a40410a40c0d004114003151552085140c61400030a540d071650781d00da4400d543c0314040118103003e2042000000102c40ea80c1e00500c0607100e49032280c1d030940d03a890061044107200d440c00d81200e0184654401c842c81290300c040c68081141880f602e03907030011201c64a140000c00ea1880c0c1c0140e1209501e6030400c0005000d80b4201e140895000c240c02416090080844081149100c0c0d121a0700d120a5106000d56002074402c6200f078aa40c1035025180c001a44c1c02c0c0114841c100114400600090343c500c6207000344114960000c1c05040302d02e1a6440301e505000c64071303104100036991000e00e42d42c6039804002d960000d24031100c0041c40c19003507080b003d0315 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 526709955 1250 526708705 526708711
    0x903080703050702030c150604110913050709030b04050a1a070c020f060421051501060804030c02010c1401050711030f120403091a04050915241c0b0a060e09 69
    0x4055850b804900200d00c02e108580e0000c0c800e00880e541801c07561250b41c0d1641003641c02034401c61500d2520304611100d4400e90305000d9004050040d40d4180140510107000001c044404000400341c0102c001481000306c2806a40940b00401041105150041805a01750281001800038000704103200b42d00041c84910340350f0640d4210b2010b03280c100810100e0003070b500400c041c1c0d002841030f03002130200e00d50261500c60086003200d03a4045182105010303542c083c0a6940000c1e0401e0005011901800d07021010f02e2040c0f40c16100c2007220380740c1025010002003078100c240d44403418000341a40c80010710102c080d2503000342d460488808550b02c428441c0740c81640303081302007000140505000c0c13500140244a4491140c0c5a00314030508985154445c2c06820b11588070f0f5808581420241b500381d260070100507220301544840340c0b04400004009040351103403480108410401c540d481d180003643c501404e240441c0014000301000304440094000404000c500c100c45111951074900d1107070 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 526711205 1250 526709955 526709957
    0x7030203390301110406030b1e0a0303030e1002031e0702011503031404080303130c0b03010b04090f1b110111070b070f14040e0a180203030d021c06150906020109030807 74
    0x1250303011030102c0c2c007505850400c0f002048022400050841d0190408400302c04100d070034415000c010542d40024060015446400c00b00c508420b000090103984402480000e00c82103d81550f000700e002803c2c0d038403c070784100f40403580c1e41280c1085100e1140990308020140000e0180c440340700d642c3c1c10800c5040c44007038104440000241c0c031800254088401811009041c0c9a5915020101101802d080c00b02220aa004064000b40c082000000c1d030b41a43d10000b24103107414030f0000244060030405071282c00300c545e10f0b200f0440302850003201007249d10742c3d0384803130184111400c9420b08507040410301d494140b604200000000d0984007600350320071040d040c03c00d80ca00c00385000300c800d01103004500300e15503070004010035481c00c0c2d805010704c01c000c1c4110912200c68449100c200c80d51150710300035050351040c0821211001240c0181041804c01c04568040c0f0391441141000d80d01e09a1041c11082d40050142c0e54496200400b10098100d03070000f80451070460b80c00400c05603000705030304 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 526712455 1250 526711205 526711303
    0x3180b0a1409091f06230a0e0a06110c030708100e0f0d0201200a0c0213140c03040c0819060515060a030506040b040c02070b090105071407030203 64
    0x1619400300050b90521600980b0701803d61074500107078500340c1007520051012610f01000020796030700c52841c40c0c1c11070184200031a205100095038120302d030407444045061203010008401c498880d030f5640802400c07141c0e03a840c0307910700700803d080c24801c003083d41c54042d4006003c2401000c40018505e40e0899401e500060444d442c10b170241e081c044052032500c00380c001d601c41d9088807581500149040c40445503031960340203600c1c2200c085480b03089080ba020030320178000038026160000d00020080044840401c0400700110000302c2c0d01030485005641c030002005200174040259100c00191103120300801c44030715185420807004400460041100e5250000110342803094040304141e2080940141e495901e086c20103005894100d80c100e0040b450300f601300035070385428041c402c45602c0d140c001c1c0c8041420440b10306130a6000e070890a0521004101c04000110f51b815962581c00d00100507020240c1544101420480f441d669101c1c01c80d12035040d207401910900c00240b40c200704c80484 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 526713705 1250 526712455 526712477
    0xa080c0d0b0a14070f0219020102061308040f06050403110105040b1e090d060506041b0c03050d110c0f010f06030b06010804140115032306060d03020c04150303180b0a 73
    0x25030050f01c1034011901d03c001040041c85041600001201c102402a0b000e0b038a002900418100143c0b46408019006900020102d40409001d031441480c0c0303801030f00414501a250444144440d120f50b11003c0003c40025080052000441114554a10900c1c0030303450586000c0038003a05d401800c000d00740816a08014400b208000000c4070030000c4040d0059000426909002e001008104d800d54083d03424001180c401c089000e500c169103400350385442a1212a83c3c5007182e5580184488469040e902d801c0b99030200c141c8005040401d0a4034003c00400d0b0301e0600749802c0d00c0b0703a90092101c031030501c1030510015194200180d07100d4420320300444140ea4a0a0080001b10030105404e280e5190804916051105c41e00901c141c81c0244072039800101c0c0701400458003107214002c070242c0c1d00b02c2070100714603182002401c420700c2c0c0a403049840a00300c540001381140c0c01c160b07040102d2107002c0d000b00205600320481c801010b002852503280140341440191380b6218020035941044005844 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 526714955 1250 526713705 526713721
    0x2c0402012006010b09090901060602032217010606020708070501020c12240106020c1503040303090c0308030a0516050c0d03050c040f03080d05100317090414090c0a080c0d0b 76
    0x1154800705002021900c0d60750303503119420150740c08805200d010301c0390039000880c400b6050052400300c0b20154003c40c60944240c0c00c601c00b4030381d259011004005240800103101010b061030481d2004480000039020345088070103854041d00390300080d45900701c1c44e4100101d07a00416000400030040c1d5004542c1d40d01152041e04000c418042810481298812405142d40c00c2065a0507070720302c1d03021070706140000e0b810042c04100002181214880030000200081c1c0700340c101000080c8a4089061840e840740d45204941e0011101481c1c09a6200d08108502411080c1c0d601d00e04150300340189040000c021860302c6078203208120042c951a58085020310314000c6c1150000c00910869540f00c2d9242e01c0e0802552340145900002503041402003080a58038105400440e035000da0401c441c1d141895010959030410f850300d0794001c2d50341c42d04801c00c1c104240340c40d04c03603108003001e030100c03075600030030002200d210f50407000d640c0d07000203000f40c180c0c0c03580541010250b0300306a40500c43d07910090 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 526716205 1250 526714955 526714997
    0x405101a130b010e0a05090a0c0c050a0f11180f060307050d0303020d14010b0d1a12010e0628020304080d020735090405060103060f0f2c040201 63
    0x10303500441d01202403809070100364400c55600109070385014405030514100082010b1502406901040000c0800c580085230340c0100c501e05114203004241c108540c45a0b81442d03501d92059840311040c2c0d07010781c20094250040c40aaa8044030a040305c01c207280300031104000f001707201408152140d4040f80e100e035020813096005080c001d0100e0800d403480c2c40c0060103500100d800d040440e00740200280c0c00034084101e18107840c84ea4011504189000980a0180000c000003002445180c010300c0b010f5112080000303004140d09002007409030304c22030340c1032600c5801030141c1c25010388040c000c0031f2a042440c90507020000800b0258a036103850500c141c0030b1158581c401e01e0144001412002c00050041807001c40103484802c0301c11400207041c0b610740c00c19084103d50510030801c00c0c00c0c01450140e00240d0031000c1850b000a040342c0382d038410f9081424a8108050101c880e06080009800d20700c0100e01d03100c10000b8582c00c03148991004410f00b1406030000307051042c00b8030600c1586003441d03 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 526717455 1250 526716205 526716251
    0x50406030305120703090f080c150702150a0c05120a14010b0711040506030309010c0305040b0a0807090815041e021806102a050312010906090b0414061504050301020c060915040510 79
    0x2506540c082c01c085c0d0001cdd5980d4080100d0040102c0f481e800030300c403c00c062281125107400c0740c0310306150001e05a6400e01c0ca074001080108078030f40d00c3c06c5000f43c9142a8016901a08201c42c5290b5134401a040c0aa90304003000300c030b40d06c100e040200b0440c264602109850030f80d40d0a0a000e00e40020783e01c4c003030b6464003480d0046e000940700415032024007a0300205507030144165840710341900d9200c280585d100c0141c0f90402c25a4055540828001140340c900441a610204d0001140d000f0039070025600b44070414aa0700341131140c44c107200c0c091038030712520010030300303a818001c102030403034041ca2a01c9502c410204000c0d84241101c0c0040c00014002c1b102402030152140c0705541c1c50f0071207440280902e01030400428544070804400d408e251046d142507104800100c10103544042c01c00003074180030011400403079003d10000034151024005040d10a01c43c0c40900307620701e01842d04614100c064480e1050815507407041c0000301b0f4000c5581c59800100d503c001c03e008034a40e02c2078044841403 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 526718705 1250 526717455 526717483
    0x90510121503060f0501030c080a031d01051b010b010219020a0e0a02120108010e06010b07030206191805031c0b0a0b07020a120305270a0b13050406030305120703090f080c 75
    0x6090208460b905d90000781680d109449500e1310315204c803030140d0b9036000000014081003520600c0c0910054682c0c3d04d40d10098140342c46454258040d6404510617801500c0d6002a9190f0518690940c0c061001101d00c0c508600300e0204800d554000995204a03481001c1c03010310300602040d00c40525404a80c0c142c000030003402200d5130364000c0d050080040c0c41c0c40c0002401040c3c000306180d600d40040315880c540541c01041c2c56203174071062042c040b40b400660729016580710744540384002882c0101004034010400b554949640802c04005030008899040c1d00c01e2510740b43d00304664444a422042d1901c0e010010b03100c000030f1001c05c6900703681e50485980d40d0003070300c0e50304109a0302800801003418141044104081003104c018840f10107000071560025080d1028400302c03100c8005800c42c00603025034a081a41d6900100c1c2c04c03102207400580000303500090503028809083c50305500a1071030310782041148005d45981065010a400041c41010001014402010100304150f840b14103 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 526719955 1250 526718705 526718711
    0xa020c0316023d050f0301090b03100f0e2407261015030506010f3605011107050d0609080903070e09012304081c0207030504030309051012150306 64
    0x600684001d0b0b8000c20740120381c902c58140d480c40002c52044c01030320001c0780b48000f102c2c1141d0903c40000040c04c1c005155a80600c1000d040e080400d0700c03801450380c1142c0e03d400c00551844124403140c2449000003803880a0544c611020a5048280e55001d6005003689440d0901ca400076840030741c80100c00354202d01003222441440203841c401d40c0c1d50821905e5440d030241d08a0b032940801d80a4a50485201c0c0c003003a401c68000302141e0082c070b40541c1d0100d01d244080b00170440710003c14400040c1c0503482c0b454a1149000703000130350b008440210f119100c030005201183c03500740011110600e142008000c075440351100340c1000000800d0f0b40f0041401026a0402c2d5142d44c2030303182c000c90032a058115582007081403042c031010484000902c01200011002941d80c070380310fa49542c0d01803640b400002903140c1186141c1c000f5803000d82b10042c8a652082c1d555865403c004241c20404d8100510810412400b030b20360540002d50b03c005400600000f08540740503000158450b0b519a10207030445003 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 526721205 1250 526719955 526720009
    0x601120f05011d041211120705010c180803090d02010e06120a150503030f03070207030f030906080a0203070f0e2205060909030403031d030a0210080a050a020c031602 73
    0x615078000a06882010950b40000c88221081c00449035050750040c0002410080d280b22440c070442400c825010721400301c1c3d0074080751800380b1816901689054529940d560007100c451548010200d03480c40c41c41014504190a002845481b841400d444912840400240008590003201e2240716007500426060312a034441d1512240182d0403100c1c1007016103050005034400502440706d00a9600240c025800d18505503403e00f0207910240002065104075800040054106982a12150300c0b81c1d0310203208070700e8000061b107405400341c1000c6400e4010720400c181950305c14403040e00e000b004d1500c003409180403404240440d590b0001c000300c1030b0355881c580304064100c2e0807590003850300b9a00100350359540e4800b60b44a00842c040103000840044030b18000d014248004039170300718020181c41d080c6403103500081040304100f1035040890300c120200041c1c5440c034802e035a400210564254a80740192030059224821100c0c044074240c005008101951100a1003000c40a202150281da0781 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 526722455 1250 526721205 526721231
    0x10b07151a0d140f0d0c0602130302100908010c02030a0e010c0312060f0501142a0309040603060509161401051b16150207120f020d0203010c090515090a0e060112 71
    0x8442c81100d901841241c4c8501c084440002d130407843c09000d0742c0ea03217140e050035640320000303544810200c6902c40d01c00000800541d070f5009081d1001002d07134403030415242c903041c0a03a09448007009000150f4000740001032150381c0091008294981c04d02e801b80000a0501e0300381c40c070040040300d038600300d480c10401080c3c44000701102c80542d1400d0301c82c03070042200c5d540066018483c80301c510305500d0000c0701c8170895500560f1960700400300002901c0c209200c440102d4111015a8001c0e901e10f40c4642c180450349806104041c0e4042d05444010741c103604100380d000d00500d460300c82038100f15000034145441c000c040303ca4000c2d81a40c006603246d1030708a00000c0100003a900641d020303808a41e04d84c54005000040c68011036034640464100c050300e5403039802411360405400d80c1c010000c6003000740144e600b1301c40c000c481d02e03a507155001c005050405008005404103e0340003000030802095556a44040007002102c5c3c0c00c807940e10343c42e071700d8400494880180b040d00c1e50403a820400c421000c0 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 526723705 1250 526722455 526722473
    0x10c081c051503010e07050d0309030f0309090f0209030705120a050f0f061609030f080c0a06050f01080d02060a020310030c0f06080c07150e0c060403050a0b010b07151a0d 75
    0x250361010b82e00d800c00a024420942203d0401030101441d030300c021001c0000c0d041c03106011704568003905100c1100d41d92500e440e024841940c000310000f4912550601c14288a8031a941018945650031420081e01c4004607580d0403450140f1840782c424200481c405070000c120b4155216803100030340d600d54090b190000e0340c801107111541e100e03000d41000203094480c1c0c040e0040d8000034950f107040c80c407840c40c0c44d9020145040301c401e0780c1e440e80402400171320440400c03c0012042c03140700000b40510b04504c58101e04c1750f06822008886d084003d403841031650016210303030055170035040160340c1e032588101ca0303004080c03560006010030454480002d4003001454100f0441d00035854030340090b50307510b43d40e103102c3c41102c03401060016440d14a00044800e544081110307041441251061161100040d03c145c20550003200d03da405400c070b1204228040d20880d00400d02458801c0c10156a1b6507004104501d800f44040100c2daa00100c050724030750200c80a160090162038080840700b20b0506c1104 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 526724955 1250 526723705 526723711
    0x3270606080d111e06070c1a0f060102010615050901120f06060807030b09100b1b0304080a05010e0102030c0405190323010e0a0b0a150803040e07260105010c081c05 72
    0xa4002c4c01208554000c40c000c080010340d01140280240e1380d03407507030140c2d59842d01c0b41007500c014182c2555646401081c000e07080c02910480b0301d071a00b91404800090940b162904001100c8541c54807031071460f900071041d9a0380744400d0034001301400452481c030b4001d01d4480340202070703103040040016905401400d014001c036075030758052207051121f00c28800c140c1026961b10b420080001d00401c82e4000320005840c1003001090550307107031030359080e01031318581284e00190807540120b180001000400d11800d0b10303480440c0029030031032400d41081c103414010307441072901419016280084a250081e058809140d0000914014524895034075040f50391b114024061586060389104003c500090781041c00e0f584010650300076034030040c15202400418010031032a038040e40d4041003644060000e00040c5c21a90f01c901c403070313117821000240b00e0130801d030f402c094100010440c9099405000070083c1521000e003441c0320f82c0c7d54149014074484c0300302d05003594801c010300003400b05003c1540181f40 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 526726205 1250 526724955 526724987
    0x3120609130b1605070203120301080106091a0f01110a0807020a270c0c02030601121704080d03020304080403082b020f1b0a050a0303020a080703270606080d 69
    0x21941d600c80c40c48050050404074090414a09640000c0301800d40e84844014070485241c81424000c01d0307808240303880842c1301a070a030341c0c0c0080b005021001302441104014440f07013406016102007944100762000ca03003901d05000380281b0810500503409070326941006440780d003c9910f0308a007402d156160f50002e5204070b1049030f980000040301c5912120700420300c0480310480c00003c2510310580c00901200030b0503403d1007030200340803000d41e40038000396009003108020002d109099141024041a900d81002003c10080c0030921020400042d501c41144440c1401a92516241082005401284e00003000c180740001c9140d8520019502844e00c03018030351a44080c50102e4244106a00507011501c00411050020320720900b041c04030620b558042906540360600340340c503814140f440c440340c10b41c003080c0c0024002e070350039912001d1503912080c245010000040c40071b0b9403040c002081c00103201c00c011105808001d1000c03540c41080107000250855040312034801010340155981403c4403 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 526727455 1250 526726205 526726219
    0x90606090b0f010e0415060809070602150103060c020106050409110102101808030c0c1c020f0601051305180f01060501120506100c060b040612020916050d0207020f03031206 76
    0x29210303885005007544100010001c19004018400458103900040851640a500c810342d400d0495a004128009060703643d4a02841c0c7c07520302e034102c2c9003604503031000742154010142e00b480c900c5041c0c042e5055030707817181021401098100040340909801d80201d50311500d0820203800304041c80c41c1010a040342a000c0d540c2c3ca00e400c61029044a00705203100011080341d0740e038800014044e5000310b9101e81c400003c41d04140003c0b04043c0381040d412441901c05500c0d801590f90380750100050a0040c1059006041540c1840301151000d40c424609080c480d444002181c4100e110b490b003611035101d0203003140c2d0483c02000465010b0310541c40b41a0100c0c813041e0106101e01c0c0c0b43d0094074461140074000c10402c041d4401c003119550701ca00f20a60f4140c3d03507036000480990b95801144020007052500e404114100d004000042d40042c2604420703842842444901d0358002d0143c8480d041c1c42140140ca506d818000b0a00d04490105101d905010000b00d60000420b5005201e019200645001c = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 526728705 1250 526727455 526727459
    0x9100606200708030a050a022a211207050c12100c0509031203100b0c060a05060607030c0605100b12070f05070b0c0313120815010201020406140903150901090606 71
    0x7141c07104058007400c00e40e038004100d038881450140780180040c1406204662102d201e940080122803044000e001809400a0502e1030520f4410700300c80e414aa4480440a441400302c10316a035460401c0d8000d03540d40c0c0200c0d014040c01401d10054aa03400058850659038800d441d01e11f459200303150001884518192044041c50300c9030303040d0346001d240038005022424401640340300030f40000305a0411318412800100b10000d00c800901b021601c044014034007400e0400010303003034a070700404a500440d000d011510104e81d02c1904d000c8c0841d0081000a1a40c6800e41801074020868004011300400002ca22002038088400203209036030590320055000b1002c7c800322058455403a000d8800c0100102007244003100800454118079030b010388450038282691603100c0e0b00c0240c1c1503480402c5000c0200089250748050a4943c2c00c000d100840c6002c0c01c1c0140070b80040e207014142c2c01d050340007044161458500300048594402a60b014503094900015020b0290003200c10807140c050400b500 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 526729955 1250 526728705 526728767
    0xb120a06090902031e031c020a0219030e090403020316030203030906061f05090d020a060e03390f09090604120f080105090a140106032903120309100606 67
    0x3442c030307a0715030040180c200010000e004565202a219803942a80402c020034140020b00c1070501c082d60011075000341e00d03442e82800203170410100e51401c1036040f80c444107a80003e907002d1101d00440b24200e41b03014040c1c0312410207c0c6140101e102da0801d1290544071001416000000345204040880858205a130b502e01800310110140400c280d05420b41400307014401c0c0128094403140304050106111b008007a000202c40440c02c2d4400c0300820980302044103907003070030b10060001c150140d05130a14003003142d241d4800c5002c41d022040d0030017607034405a0003d43d6110504203200800030145007050602c0040151100000c0d90110786085910301c060906d1400f03030900341e001d00d20540b1492610b0f071800c000d10a404034010f11800b211952085026407031164085410b000c5d000310b5800141400828004481c540d0302851101b00c00250301f0044042968002220000d2021004032942c50f034a07050070b180d291118800f1a415000e041c24000325505034050703a41070328100e411144005850007042 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 526731205 1250 526729955 526729961
    0x6010b0c010b1e09040501180b0a0c03090c0506090f04050a14070f1b111002100605061c020f04080715120c1e05040b040905090708030c06040f020a0b120a0609 70
    0x100e00341029000d19041201131134402c41c04d903402401400040b5019060b440703010203031403500c441290412060f10504c404170701c0301e1080e05410b1856003001c100038145a281c0c201e6079406441081c0c425400080d0139074058440d40d01258005401074000d01c5141007041c1711102806c3c0d110f04a8001c0e08248001402c8644550319424800c01c29484078032049010100d00a02d0008130f04054580603d03070307825402c080d200d891080740c4001d684d0340a08400070040c2190400e8445645c0114030401050100b80502d00c1d12440c501c4141046541c0180e880395002501203032802103900199140c016810002003460205540010340e60866443c48040d24107500303003000312621032102c10006076100c0242106550480c605104040703950405609080d500d10903041070f50310582181703142c992039500303114620030104025805000883c1c003841c201200394240c20740e43c40c070080005d400030101c40311000c2035494030340d5504e010744440600942e4401290400c0c40e00000d05a60b0459024a40003002900b28180d04c = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 526732455 1250 526731205 526731229
    0x9010905010e07030b0606030615070b040b06012c010e0604090e060a230702120703020f0708060417030a1806020310080106060207090b1804031206090615050a030e06010b0c010b 78
    0x500300d05da611441e09006050708001c2c00c8a40200b0365a0f2a04003504003180500495032040c5542c494030301c4c0c0f5140820013904c01400c6507040c841e403488141800a8485515041e0348840c1d0310f4210b1001c0036600490b11809201c003180e03005203000502089103007040e041503803200c000d04110b41d00c540f0b400381c1c4030040b20080d09503e007001d2645141e441c040909001d1542c0c00150500c1115003025490709020315603031084d00c0c118091380c003089206a41c00014490200103000b0300303001c0c061604e1700d0345400030003005046e210b8a010f0000800500d00c101c140d4440001126014120b200b0004945081002940107440361205014811303130005130300c0780501515040c1c55041d030107040e0642c60401d810025094000443d64801604540300e0810780c00d0030f0605205501a64500c04410303c0600318070111811a0003801c0c1c0d55090000600c403001442500c407460b41918a0155601c00030b00008800811a051100c1c82e00d00a0400007d401d208101c0544407d032004070081002103a080104107004d1085 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 526733705 1250 526732455 526732463
    0x90803030c0f18040501140307140a05091807060f1b1101030903051c06030b090102120f0a0e100204050102070501020613021c050f010f0507020c010c24020309010905010e0703 77
    0x400c80c1603040c4900e50302400e00f101c0c2e041c1d444070800c0250360000e025103200741c000340c0360084102980d20552504100c030800a10420054144a000c40c2000c0740841040303014541c0500c036000701003050050341e01003540001088000303440c440c6445d41001000c2418419903200000c904403107025208001c00c500b0040285d212461103810004040154094011541c00b5008d10100348040c904070f1045085101091444401c0001e5803801c0d0b10b05080c1401c00544a40003580c81405a894418640008140c1041c451041d04440303607642c00801d4050514218005061300440b06100d0080416802800a9410907000d80b084151600c00484e610241110344860031082000c0c450003500700b1038298500c88030040e440000d038103c03607210545071510500610350944c4d5140302c100c00140451080e2a0025491b00c00741c110000c80100007442d22403804c0700907003001c1410303c650740380303901914a401140c00c02d40c03c155101c1c9400c41815000f031142c010203869030350901c46111030b80352003c600b440540e548 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 526734955 1250 526733705 526733707
    0x1508070f030f060803040f06090f03080a08060f1305010e0939190f050d050a02090c0405030a03020616091a07020103020702090c070c0803040b0d0506040624090803030c 74
    0x2410303400c0740904038900308402515665407001c5088030040c00140003420200ca5a03000c140d1805400400401040d80241401010000140002404003044500c04419132410505a8a900b00000c1d01c48060340c48460703000188042e001004912608024101c331000d41c0c0440540d0b541e400074a45940c08a0302422115122315003403c18204402e1050b84110007501701d4009019050000c1540e2040e0170050700801c2800c8001005010130700c1c01a1000340005440902144203241d50702070352a0a10200280314124403c005444106c140301035800400b0010b048035501c0560b410042d448000a03600d012214125a484030311150041092720300301c0c2c004d01c1e401c14040b03040a00f000c21503040540220304143d006c0001d440940c4d41c20020078090440c05200c0790792400207181c003010031003241d88410300a800a001c208140d10f415001d5402e5041c140d4804290350351000300040041a1035000102294000c1c20340c801550b181c589541c481d1000c0382c681d8280d543d00c6681941c1d032808201c0340350032580c038 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 526736205 1250 526734955 526734977
    0x10201110405040e0307060504050f060601031e021b010203012c0108060f0403021f1a0406050603071206030803151c050304181803020d0f1701030605060105070f080301150807 77
    0x1000e600245072013080ba410f6078240f81541da1030b00700303541c0c0075201600d8a80c800360000c807180b03005000c6160450024202089007080300c0b1680c0400d088002c0d80004025404a0b000c03552003000700003c821070a07000021542da44c1c551628103107200380c082503041005d600500304001c10701032601450594442e00010000356481400c00703001300000810440441c09004807040e00f0a1200a0400c50100c5101d00410000107a42d41203a4803809110302034440c1e411b15408200f580c403940110394200a0524007241d50700b400c1e10585016000541c4024218070000042010f40c038410440d5400540080714a54074110b007203501c4600f0703206040b40241c690381080204000e000d1032001004d006403944400070030320202d485000c0344070340b600440c15000358005440700c414880c2e00607001c2050501c141891001d04403490043c10501c401400700030041503031100420f502d68020340640b2035540e8000d4492803052a14230f07200485d03801c28801d90220750f0f544200000c9642c0901c041c42c2c41220980d4408005003 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 526737455 1250 526736205 526736209
    0x20c0a080a1220070512040f051203072111030f0406110607050a12060521060717061c08032404051e04030306050d0b10051c170d0501140f010201110405 67
    0x2a001130000c5030284520202c200c2070f14240c102030b000805c05c041c43d160744a407811007400000ca11240309100944c0041002c20b0008505101044008104103402c0d204404850b0003511864000711040c03429103c0402c80c482507000302c4c0b000704140e8585035100ca480b025207410440c0c1c0c4610a4540b0404a0b600b4494200818030446400c09105024200490403990b40c0002c503030301200040300f000c051356103e440560111020040650031204910308980c0c0580c1f0742c092407401e4070002d8506442540d8440409010b66622144208080c3d04402e800381d45c1c1c00c052580d102c820078200084d004184661948040d07510700f51050510500051281814041c603c810b0341c946460000c0044080c955138010104d40c40e1a5041600300710b6104118142e1035040015141082c800d150340010712803c002c11401c8020201c201c03031800e1441c0e00c004080d0071070005a000302e1580c05200319050055103003000015105040c0006c0039482141541d40748184840c50004900341c0743c20254143d807141042100b080710b4 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 526738705 1250 526737455 526737457
    0x30705010912081309050103060504170a0212071a0f100806040b07030f140115030f1a130209220b032b050c01050406020a02070e042004020c0a080a1220 67
    0x4902c0c0350203134140c02510341c1084c0044038000c2c0c000799034a503640d03c01c000800004018880040034074a54584c181a5850300080d40d51201001c2800310072408100e0404001440491400201d00415024280e14002c20b030700201680442c1e907140b05140258002401d24004650380d40119000040100141e4407a20250040c0c00300c0301d5280603031070752001c41001c02242e146825000e003010400303482c148904040e0040c161034000841e001c82c94901a4404e265210b14028052000000d803960300146400c1c442900090248818141c6c1040c00900c10645c150440e20058150b10300d0a2002c001813910340e0141035907080307a019800040d00343c150b0b01c10014030310030042546444071441d05615145c02410410300b9075074145e800715883c41d00803c0559106805200d2000540358010b1640054a007e803604a2061b04621400400115001c000100d640b40d81d0100d0b140c1d420502c044858031000c51809200f5540540c44040024903007911110b48203800d4019581b5250340025010981742c000203410480d = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 526739955 1250 526738705 526738717
    0x30301050603070c0b04062c030d050405100e030d0c030e0601030618150204050a0e0f0a02090a1706040b0a18020f010e19050103060605030403080f06150d0b03070501091208 76
    0xc0c422402144c01c0065001041c0c103201da441071034003043e5030081e502101c041c07811003111100d028500c00a4a20900000410384403080c4950001148036180d03810302034148a400c11824900c1c41c01c2592100d034540002008000d03030801d40400b0465a110254201d040310b10302c50041a80b0b41110380100301140ba990050b07a13200c0080303100c441c00350445540b028a503c6500090000b520b401041c20082851704e01c80b17100007485030350700808142c035103007600791f0b074040c00140715540095011907141199180c000d58079000c0c00303400c01454428128070760750303075510074003140e040703030350002000001e440e5071160f01a14900c4460107020b803c2040c0580d081046000c1d000d45158104441c0c0f000003003060b0307117400400b103903142015001c4c1c03100c0c0d041c540010203441d0281c005c1414841f0030000c0c4400641e02040702c0e40c1c0200a415404081d4640c0e800003546422800c1000c050b04001151500200a45a02c0700000c0c0c40d0403400ca41c12207035104d0064961006910030401140d6201086034003044601001b061 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 526741205 1250 526739955 526739957
    0x121003300f140d0b12010c080705030c04030218040204050901110405042f0403110f1c030314090102041d040507181104030c091a0609152a060c0c03030105060307 71
    0x11402e8000c030141d0780303a000000c1800300b21351501511400d508080c04d4415940d604840280410010070401405001015000c98200b020010016251802c0882540e001d90350042c111060b00b034080000c00c10742d0900303480c1a48241c0c907040c045403401d44140301f1020040c5440003518180391400040000501c0c00454013241404083c081c1c44d1141d400c1d1481c0c40f010300d10303646d400742c440e81142414040c1956010645004001c030101c04009952521103035842e0341c16030340da400314440551a0440c0030b003004408101c507121210040c45168038040d0080e00c02e80d081254144001424070001d0760380d440c0d05440192103a04560f9050042c0610a041b00061071039980340420310342550b118032415544170340d10031b807500d00003d0414010500b0740c4c007038030034040750301c1c40f0100720441c52400068040c8102d098162088404481d444015803c08055440d0611502c00c0320108000d82c4540a0b2880d84040e009491801003000080f5015440c000303031106407036414021400c41e03003400107000c00c50740054900c00c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 526742455 1250 526741205 526741217
    0x801061808010e1e011e020708091e1c021f0207030503070b0103170c10020c16090209010e030312060f0f03010203101e080c15121003300f 61
    0x304125009006a20010883c20001c10041c000051001020400c0c04094005030b41018465a10340444803c40d03004120000001640c9207618503101c40706204280e940c542080c42c9003d04880b406424a19481c5440107881903100d21011095206850340350b0b0300001e501603c0d00030541d4a0905901000740c648605004842d00984c0b2603e0701c42c51a040350f40c00b00c40030700c911001401005405803c58440c00c81e01442a0b090003c000c805503101c0c0701162000e540b155000c07a8482c08050100110402c2516010740d2142090300c80121002030b511040f4518003085100130320116a08001044461081c01000d0703110051310303854108103421010228050b1b100c00000c03010036103036600784001c5000d040c841600c81d10326890400e02ea48100404942e00c01d1102840c0b03420400440041802d840e0720748201d40c0400c800c41d06513150201806402c42680c20310720460204000c0400004010003924025115401000c038840d100d90540c00c002a41d404010040745414440a802252440d401c807410341082d07 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 526743705 1250 526742455 526742459
    0x3061415040909141b040b041b18150203041a071a0a0603170705010c050a2a140d080a06030c050906010309060c0e190305070b0307020c0306040305030703140708010618 74
    0x300d15003203d10208160b9146015030443c046d180512a0295582d01500c040c401d900624075142150340d020790144080c044010a403014036140c24161401504080141c100d02c1f0303100140003980d079045070152504c140c580301500025444101d00703a43c8400c1c1d000c15004102000d841500200b02c0014041386007554669902200081d0000c02000080c0c8421814039240e01c01c50a00c1801d5a510b44448000e1103002c1000d56105540512503c80b91107884d8400d10144502602210399034038107a1000d080840c501009210216002c60003030b405003d02c0c0d6403c065602c1d0603580078121646440020035072090b0b2903041040e81451002d45902c402e0505002624038a940c60310410713500d02040010004410b6100445a450110b408502d554604540103545509603965035503120010301550003072403004000100c0ca98400c000c141c0400e880903054403080d00701458040d00ca0b8100ba41d40d100402d041041140500700d00795000f5118031a5a5104491a4a0a001504c00c440b10311000c1d0075410006c000 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 526744955 1250 526743705 526743743
    0x304030f0f150b13090825020604060201060e0106020f030d09050c120709140c0702010809030409020f03061c0c0b031806090a02190806010e070c050d03061415040909 73
    0xb5254403100e040004200042503070200201c00100f000d4561480c0d160040c0000800c0c0260b081d6030b2800801a20101c2e51801c10168111206840c40d000358045c0740014040340240e07064201000300c403021050b1600310703620751a050b0b0f02c8541811740e0301007590050208000048046d00300891050188054038800c010b54030103d200e0494252940c4407540c0501d20421400556101e000307000004c9602400303ca0030b0003510800c00e0301c581078010f41081500004203034800800d0084a00070000c0480071542d078203000700b9000b80c54004840e5544103440d45455260000581d89200d0301c15640034406a00f00b509111480070703642c2020f0100e4024036140c1140307100254003001039500030301e41c1400402d904c0c2803d1040100d20103141d0440059045189410003081000242084c1510103505d0044010394515804458041540303001078440c0c440c504c1004211901540b0050503030311780300c11750400e214600e820f00503419841100340d038941c0001c0004005032130240e8080394440b0b104d501610040c08005403 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 526746205 1250 526744955 526744973
    0x3090606090c03060e13030816020f0a14010c050f0d1109030d020307060c030b060d09080f0a080403020f010c0509060904021303080d14010b0301091d01050709030c080303090304030f0f 81
    0x1180320200f0f42e104400d2041105c12408154003400c4a03100b44150f084035a001070991001510310542200c500028020082c02804810b01aa0b2081e04944c0c00000504200c20720f450311a4040d15554a00075030040070911520071a9420b02920b40602d107400c1400350050020851200502c4075180140300c241c03c113940520121204040c0c2d070740159111005800c0c0321b01200c1640d214042410b1038804404059120f036419100b201c1d05a0900003a00d840e0f50400d070440d4030a5000183c0c00c07410014100c1c01154100300700360b01440c06503007242c0b181260303041140c4c00c8641c00365107203000c144184040d109528043e0000c5c1b24120001c0c0c000f504000e80b1440038044d40b0280e410442d460203001c5216140c0d414144544885003140e07680050295140c0315030f44d0703100d10060040e1292180c59101c9085560300b07941c040c0c00206000f41c000c210b14a40160000c0042c415808100c40d00350b80b004000440381d00c0041580d000e050b50601451802c0e20b5a81c0320041c60b9001341048404210030a960b01c00b04606117 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 526747455 1250 526746205 526746221
    0xf031d01020403030210150e101a0a031d25080a0303020c060703060509060d020f0d03030c02011d1e0a051911030f0601030204110f070809180405030a0309060609 71
    0xa001603126411890007a04103140200310403203c42c940681e14040c01000c81a000498400003090361803516454114020b001403a0024184103091070300701d0041c511080028041c412041c3d07020851095001400c00071100311140420550380b2208003541680b4206082c1000d080f030307216403280301650711100fa5050071101070301a804264089000c109498041c0320803580611145804c200d81828940005d00d44003002e4880b0f03002d00e0740e05400300110b489a05580c51401d03802407401c1c00070740c131a140040282a01511600042d42400411103400740313a120194409280c40707000d82162401c070743c400f40316107501c64a980320300e2003140e8000010030b5080c004540295000791044400c1c80141c2000c8074981b07d18809c80b806075200000555003104003280041c1501e60441d03010494070001714596800d80104014110404e070001071000411958070020064a6070640d610308601018031803022809030100d8015040d604200200643e50b84a0740c040c0901c0b9210303170070004d5026141c01e0180b00301e50781c80c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 526748705 1250 526747455 526747511
    0x340506130801230702060906070e01090b07060b010e041a060307020a020a060c0b250807051306120e0d12020d060905011706090606130b1503040309031101020316030f03 74
    0x800c0340c0302c2d030720072043c008182d0200d0741d40000c001509003256102c1e91200700405102c208964514150040d03882420042c00501d2402d0361240c550300182820f00050040308042c1e40441c44e541038090b00d90070036015020b17040701c0300c0390600c04890070707803003445071070340c401002d000841c000c0208000c0140d4074030140c44c011342099682c0f080100503900d08450410400340c256009582000d40c0340315143d031104030b01e80c03100c0e40c10301c2c10300b000351180941034030240600b8503054000c40750103001141281d84840c00e100907800550051000e03c0200002d1511119038030081000500c10304c0c0150b03450700c0260020043c01241d072600052159886403554101d40c000c0e0404a03413825807003000e0040c007004000d61030700030368102c0180845003082d034009410074152001c8808401d850342c510102130b170364401850b0004801d44100e5640c7c0e2509203001044e000e0749000482e4528851445180c15520020a03100b03290b80100140900fa103583d00c003500c0c11a41403054504064a9098007801100d20784401c0e0310500c00 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 526749955 1250 526748705 526748741
    0x71d030a0c03050a0c0909080405041e0f0f05130b040818030304060e030c040b0108060d06090501050702010606112413141b0d05060412051209340506130801 69
    0x3c0f034680012544480d500006d94241031a1008020681040484003241c40460780082d04101d001c1210000710740241702080a18034266000d50141e80a4110401c1200000c100704042d50721f000005024450011000e804c4040510000c0c00089000c002171980f011020900c04040c98032800003840d560180c1c2052000074040752200816003802c0100c8020b0391800c035000d004c10144440000d122140007071246210740702c8100100f05001c031550018036243d4000c0c1c028056881c00300d070702038080c1407a4410180040c02030884908404c4020440d980c2a855204408040110000340b60303400c248043c00b990700c0082e0491030280045c0744546038020305c1600a000c1d00c5030020a0545500818024084a001b0308091107035000151002c0307a10381d44a9404800300006036041031040759140070f4005101001c10b4004140032901100041411500703082500100024854610610340010400c0c4900c0c04400f901c40113024501d441c0d4041c003110740ba42e4484e00d4445903215011402d4840d041c01c00d104044e1 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 526751205 1250 526749955 526749973
    0xe070909030c11012309040e01091b151202030a0e0a1a0c0a020601030b091e0705040518030324100903060e0c030307470708071d030a0c0305 62
    0x81d038104000305044003401c017011091545080b41a40495200900029090000c4e000b001655164403603140d042c0782d28001c01502c0a240b40c10b60340c00026111104180031200c1000901046c441740c42c80364600769580d0482404440d41406010b50805801021440e0b103c0d1044061040c04000200700d8500452209024100e100c1c80080e0b0400050000c0394950f204122a1341080d4000034007504413684202000201d0350742070300d51403c100c1d602c0b041d155011001184414809000680c02003078400c120350822942d210b180c42c140a5180c00700b9aa45250801e0000601240d80060108030681c06001c02a0307900c2c1d01c41002075005220020054007140b43c0e0001031044c03040d544140840c00c00100300070590b166400d400030303546c0d0040c0480141280c0c1241c100b400a0443c529501c0268007800301d01c10501485402100e0078000e031f2002c45091010b0074400070f0100d80c810102d1501075601900c40d964069003144821504040102e0300603014400c03a0310386c900090203645154000c50250001d0202c1c0b0b0 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 526752455 1250 526751205 526751213
    0x203120304110109061b1e0803090303150406050f012f0d1404030b04020d060603060501120605060906010503070f05090a06030b27010b0a020a15050702070f15030e070909030c 77
    0xe040c0d00f08a003044181d89407004020390644440030010380101c0d601000705907e0445410541500340c0c02406c0c400c02005100c1c241500001950049803080d81d00140fa6070b001c070601088490a220750355000811500c00c000550007120300510341000c1c0f060281a0710310047c0000301c00c3c90b0036a210405540152503d00c400f44e40070050594041e5490060b905e81392958443c0c0b9400c060140001e4810420088a80100002540306500450307110300b062150f981d4402081000c0d09000130180c0b8030a080800080321464249003061064274140c503124155200d125045030910200a1090300744001040b40c140c41f0b6807000c03e50001001144e9010425007038903010311201d10480b181c1358401103d01000340c1c0c100b046003040d66040d00d0b01250b0307042d116611031100724502401110050049210b1441001c800c034001e40000d445501c4540841e82101d95526407000382030414881d042c0258581491014910320039004010041070309400c44804603200c680c14070440742007410071404190086440740c100 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 526753705 1250 526752455 526752467
    0xb060c06090f1618020c0a050706020102070b1305120d18110a0b0c06070c110904150606020304030201020c040510050a0806070e04090809010c15060e060405010e06031902031203041101 81
    0x30800e680c00c04003d441c050b0540400f070341640690800507000300d40d1000c0204c0400080780e18030b130072200311944250703280b202038000e62042800f41c98108044000401c200728181c002e01510b40d01400170044c40014040118003504403003201c000701c03034070f40c1c410418a0344000a04954103006002d584100001501081102040c9030301500d10080d051000110014001c5071007503100780f4074105a4010407403807610704136580d604202d180d801141e00042c0303c20f001c11500c0038031504c6000c5804010310b07034481c03106a80c1d9018500c00240180d2140c007030203490b41019001300e81c1280091000855154441000a40000840d049180a58480400c000300141e005280c404003200039102049540c0c040c3c2c8070341d841031256040c2c0505015040c0010070801c01c0702142c1c0c050f50400300c80100005600c9000d21800514103130b80c0c040c490760901c0c001040b070b400050412401248001c00928a0040303020b045048040c1240307041c2d0741030080500440112817003c00441c401c034421403980c4540710001c4005481 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 526754955 1250 526753705 526753723
    0x5040f0b0907022404031206090f0b01020f1902060706110a02060a06030f0f140313030b0c132117030402010807020708070b090a090f05010f0915090b060c06090f 71
    0x110b501a2401d1000312003030740d00212044130850b2540c2e086036075600701030b182229028415424140740940c0010420101d9100f6140303501c0820b41840307246201c000480c2d1b640e0b24a028600d8580040286103810f03010000090b003101c1c0f014011034280301d03180d2603007803c43d100e40c22201d504c22000248244031a605101ca254045241700c000c005080c110f0312038506070860b0003001041c2c0070100c1c04110a000a0703c644011022400040320b668008021b1510304049180c801240d2220b00d10002c40c2c800d14100341a5451002030411241c1c0d0b1030314040c80c113102c6418007a410400c1d9449074040502041c69100d00803001103600b0707292580c07410075200051500704000c00480840d001080305100c003100c0030901c8421680c001d8005912046000c002401c80b91980d17026251151400080e45411f111507040f290480e1041111000f0850340c2d000900159580030030030b10f00386001c941d824884080c06e03501c03080030701001424683c28105501e81c0b65240c0702d41a031750a02154031000e4402c020a0b000c1080c002 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 526756205 1250 526754955 526754957
    0x3070c030b0112050c0108070c0209010f05010f02060f070f11060a05040b0c09010f0e01111c02010b1207030b0a090b0411041a03210f04060f1b260405040f0b0907 71
    0x4000180e58840c141c440c0c1170841001e041102801c0400c400e507104004401036250020004c12035541c0d174420460038001548901d80c0800c100b4180302044a002003206032055031000500d08881da5107020407501c40e0800b001400074408000001c58181070704018041c0306850341200000d0904003401d002003070100080c0f1171800380d101001100b00300d03648210f20752038061182c141804d0100580006070382d81460b00305041004e100740e0035104d4200c0070048429004404640003003114030140001d01a40c15a060258010b540c8171540c20000202218055030380801c011200080361156669262586a8150b40c10758071610142d44070040c81c540f03445a03a00d0b5101580740d0103103144580c0082030715425814508400d8200300c0d03e585c94054400011100618003003548907030398980701c0b000036102c00301c5091590000b44240078081d5904404180d420340080c7c0100348043c0c220400c51400c0c404005400e0715000c0144180000280b41d100c0c0e0080c1e0048540035840400c038504e14106101442e140201448 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 526757455 1250 526756205 526756229
    0x20616080f0a021908070b062101090b09070e04141608011e0b010c020d140f0609070807230d05100b0324040f0317010e0612120f0a02010e03070c030b01 67
    0x101c0000c4171681203d0486503c0105480c40d43d54400c0003514401200c4600c0c2d442013052481410010b9040d40003e001c20310031000c40d409901e03003d484940d20313145401406058052040440c0c040f4416040410111101504842004a81950086016200c2e44c880011170f0344070541225031610404400d62204450f040030480c0c1d90511000806510090001074001c0d910034410005021841c0009120865080c044070122800b0f034080c59504d007030480d241d1805001b8140c0100354444003180840840300e1141222182d06000180211400071001000d94000c00308921400059818000c10310034003550b038400169103c0c510289414240b4034003007005a046000b00d0028407003041d900b070607080341d046002800190a03529003980e9202100c81002c0000c070050000080040c941c2a100e880780200313403079504550309072568440da55048190340b586013280c00e10400075070300c1d036203005000104c240344001302e13103561220ba00b682940d0009030251608140300b6001c1c403e1050134505a40104907100c090 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 526758705 1250 526757455 526757503
    0x70c060e031e060a1a090c03190603051b0f0d080a0e010e0d1707060f0c1205042d08040308090a08070b2b0e010506030c0d020a03020616080f0a02 64
    0x1910703040c0061181031303800d5460911880009440000c0c005a0102070100480c6051405028005420460f0507031412034081c000c071040703007485003c0c001c100c3e9801401444010340200880804849a0070810741160b01d03e03d418515981e4040e0a9885502400d441540d80e094041d00138910900401d4060500c406400d00381c100c2e8907a2820000c145820482c40c86205040440160040c881c0580c040c00603030034070000c084500c180380d00007801e80742c0689950310042d800c1c1006105541d4100d401519016101404502000a500200c5d15843c2c1540a6582d15041c070781d207000b40c0d500f00b50004d07a64200d020908800070705090511a002d08100001080c01901d0442039840074420600c18129081c900085c07422900010137030760307582d03109a000c1440007002c0d030203005001303201c2269010f120380300f1140b83d80d109040003820101c01c503401030b010b9181e0b80d0540d02400010f900042c280c1004a445400001c0442c0e006c00142000030307184031085544407a8803100910f429422010011803d4804d208 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 526759955 1250 526758705 526758763
    0x4500102070b0f0310081c03180305070b070e03100518070b0403030302090103091a0703060501050c070e0415020c070303020607080c030f07120608010c0809010c0c0f08070c060e03 79
    0x283e414055140050940d03d6503451344c40388081c0c03600d0340001c070a8460342c1c07810b040e4207001403240390280d0500e503410050302e2740038850015540703004000500030881c10018580859007402d50796620207401d0908801c000da50a022928000c8492614044541c0d99030034000380c24085444541308420310740050170340d581000301140c80c92007244001014558001402d00136a4025080f00c2041900701d07448081e030a1049000f081c8421085519000191418a01003000c1d8080d800341d40f080030341480108034803420000d481c604a54040e1058400503001308091101d80c1c11400142512841e0201400002f4950315020785444000341c1843c00388a030840801a49107004010360380d010004154000054403544002d1f1240c803440d184900c110b505205001c00c1c00441500a6405028290355228443d030342e1807a4542203541809000f400281540c8644020580419203648124082c00e04c10746054819920110014450707804200440ca00130032a10701032500703001241c41245016001c2142c0c0c81c01c420 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 526761205 1250 526759955 526759957
    0x19110604051008041707080301170703120f031e0b03060a110702010f0509030708030903240a020715060906090f020c0606060c0703170705071203020304500102070b 72
    0x2d030000401114400183c140410081c0e030034009852049019502c034000d05017000705a1003401030071140d601030b5908881c105400102c0c0340c1183e0b00600124440241000300f110180d900703151800800d03403110184001903d030b0940741d40701512091f00009000386501c0515040000c01014800c1c29031800480c0352544036002c044a208990928180c4100e0000c902c0641d881e00651980c95014441c404000c01e82410020080c08664411421600101c8040103d42c00d164891a900860030300c4a801003a100c90040c2c0180c01c050b80304500c40031000d0303a48200030046809550042890300c1d154102004149402d00c00c0f030fa03030740d1400301041d40b13404890300d00700d0360720321010300f4082c010b070f800292185030142e047c8070402c040d5501c205542204103a02c03021540d513400040003a00c40340a620400a403c0c800c50780e0803000c4d941c0c0760300a9401c00c1c0c50005244c211503400802d910f4020b044403a4105040c14845010001d031102c0340704a1038000300e1550620f00348914941765419580034000c2404041c179110 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 526762455 1250 526761205 526761229
    0xb09010e01030f1a0a090215130e070c3e030d0e0f0d0b0603120a1d0103020904051608060a140d02040b04141801110a110f1911060405 59
    0x800c295408004d10702042112038100800003164070305404d0211008a40d0801030100b070003115404c2c205070344c0715840189440f500300359500c5034068000411002ea04007020603441122402d0104070b1030001e84441c00c420395810504010400c49080301010f116480d80030080c0c0413031010038607607084615030209540c0c0500c01c3c401c00c1404000d0654160380d59500503440d81290300a01807003001e0240303203401d1000c540d094035201d210740100e9450100c202c40030005d1b9400540c2654601004400c05900d881d8035280d03481406040507020480d8061546940c060b00d80140042e400180c11603549000007407180c0f0028100f035201c0c8040398800c10030b4001c005d5622507035100840c1c054910032034610005004104c00d60045803c14101510424100349164030396109451040c084001c0c007008131100340c220750034007112441d22401403140034006845a5803514000c0c00c00000c852007905d80a01c0340e4640ba80344840e860074220001c4400b000c01080000c0000e0401d401e032451401d140c18000040d0308040303d0 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 526763705 1250 526762455 526762463
    0x30504050915150903070b03060307060807120203040818150a030c23040e070c051e0115080106140303070b01090b06310501170705030705040e0c0405040b09010e0103 73
    0x14101003802d030551030007421038101e0000d244151080074000600d406401942e0858424080c40d41c0000f81ca121740300840c3c0c454100200500012030400303000b516a218090130b005c0800a2758400200c20b03240340c1c0300442c042c50240744059141d81005013811840700f40000c11038012a80c0801030b10444200d0000e40e54901c0c46810301117900310080d10b00310b0302c072031103038405a80003414007003140074170f2814400030010b0b03802501c0f00042c00e41e00c01702c00340d03525040044000c15641c8030440d40c1d1802240145207039062070f016000810007410101c401c054040340d40e0083c1c070301e42e55100c00030484039003005645070b0914411303000b85040401507160007a40000500c07848058946030404840a0303640e0b00708540b0b90701210181f040783c202c5c001c103a55140e80200c4a240b61102108000411190b00541d0211340a4029000d112000c0d55114030071910360b000a010501407200c1800041241c03145124081c0c403c031030381e440040d2203a140404000c103403110251224010920f100040c080501e0303011180d41541c4d00 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 526764955 1250 526763705 526763719
    0x604060c021f050106080c040f0e0a0209061201080c120c040c0519030c1b23011d060a061a0703050a0c0f11100e0105072d05160e0403050405 62
    0x20a000303a0618412007a076007441e44062200340b90802141d4010307410b8501c01d641d4801c0540c6c60790450341a0381305078013400c095450f800d00100910b200040082d580a4100c1001500742107012002c6100358100348444080b01c20300704010300c01401d00f088817060001e01201e1415009441c1010035860b041549840c0780600c0d2614403402c8400c0c060000c50302141e80e10485040032030f21151008008041d00c0254000144988d0325000d107c800291a14242d590000d604102d804c00c0310000d103a49841165080005540b212040d504c203410f50b520301202d4815880260805140420300300c0103d5280c0d401c3321140c1070032440c6214042501d1015241101c2e411b0901c02c0e0344c4c0f10351800039a0703941c4c1c0c1803800414170154000b1001c108080143d8244464105a800e601040d180d1641510314140e191035280c00144140850b102060341030759000c5100501d50341c8030408002c619074441c000250f50f0030a4902e68824032220901c1c0c1010141000245079600480b107440c10300360340c010b0a5105034415030b441425 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 526766205 1250 526764955 526764971
    0x150d020a03051c020d030b0603070302160503031819030e01050c0307150902010215062d120a0c0e1006030e0c030a050f0c030c131d101d0f060406 64
    0x340d101410300a0350304001160043c41400344040b2a0722140300500740180540300d040060036020b4055000c1064004203c40e01f15510400220b00070340212030451b900c41e0009800303c0201d0000e000460240441c54440c5004c10b2095440b1460001501401d40704143d0800186d00444c2c4c3c05880300340da00009103400b951315441115928658040d05002030200c00088050810000c01c82c0c1c031152400e80300781c007668612191703000d80540c180030803101260031802c3d940200341e0101d40d04c01c0d021009030705c42c140510300c0107480010800181c0c0c40d4000c802c1691082940300c0600071800880001420500d0f00d6240e0752800100b14150702815124101c2410f41b14040b010750841c0500a410501d140503084900f02c3c88681041a03481000000c1d01c0d07454002c00300001e40908011811400070b000281c0101001c88402d44094000c2804040c2e00500da0381c034082d40510310304c8c10711081e80415214000801da886010310749010201e45001e00c408958003420580307200d00c00c0030a449a00c150410340c0000d002e5 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 526767455 1250 526766205 526766209
    0x6010b0313140a020f0402070b0c030703060f0f09060f08120a120e070e160c08070218040f1101030902030d031505060409090501060503032502030304230315150d02 72
    0x185007400091284040b4007400d01c48003070000d441c001c0d0358000c03a06038040350702c0350707040c07004034490b102011700044100c0000072402d03100c900003160000450b140004006d82e44100815240b009a0080e808582280b0410000c0000701d00400d000303400c80c1c0d0088942985091041951401d0142c00b5200074800410324014642c0543c0c080c201104403c0004d02025802e0402c46884d51540d008242a2040b1a800304030080411803040420500da0384841c0d081c02e41c5512805039540229508a078020342d0041818042800303004480e0280748500a01c01c0344c1071070303407810885100107100d01c035041600d014019030141c4e500046000207a109030500055044109421280f6400c550300050740000c0001000201e403000e65101c0240349010304000c03c0341580391401c00d5140d21031150f59510b02d4040b210100b03070b07500d60202102c0f055031000f0100d0f4030705581e8205000a0081e011024006644581c440305100c0c142441440d1515040c0c064031012880c003108401e580084190041d4015242d00049500315 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 526768705 1250 526767455 526767481
    0xd0e071203030b130e0606030d090620101e0c0311040b0309011d030d0513020102120d1b0e1206071202070204090f06020c0d0903080a0f0507021201150b040806010b03 73
    0x50700340344c0c009000513040003c1540d038414003034913028064411a041203001611541c034090a072903080d640e00c421501d500c0314a20b0700050038001d40003203000d070421400244140d48a10000c02c0c80c1c0341190f80004010300104802c83d0000c1521400703250504d44c017042c04400c03060072075055502400307040380ca13600c0380120b05004120f2020314464401c01d1322a4100f0852001010303280001c02c844061285644021110001d0203000300001c0c09a40300340318038265010b244000d00108921070000041c072185021200c644041c3c00361400010510030040c1000f941003101d40e21403640800d00050425003416540103110148015161681c0c030743c082a414115907440d0021851203802c90501d44289100b820084000d610041d032020903172140d080403401d21030103003040030102c0340c00c0700b400c5040414068040d100d600040c10b255003001820810500180c2d078440d090142c00800c1ca00001d0f80c6070642c14000e991985a070800014464140400c001d43c40000500b241500d48003038189480741c035901c0e5070801d8 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 526769955 1250 526768705 526768729
    0x405010f0c0204090602090f03030909071407050105040f02010f021f0b0102033105030607080f0a110d1e0207110d062909070804261c020d0e071203030b 67
    0x300a051607000d401744640da40241c070801e4400c0398018105582c0b0010140e40b0b2040c044440d4000c410300b00001c1c281c80c0034500d480304e00850850010f00d814103d54a403800c40300216800c41d41c42c1480b0102d4420f45d40c2c000405208040780e40010305a5111080b01c0e10346807100c401180d01c41c9516000207000c241d100340192110b5044188032194942880ca000f52140090081051000f4503d0380700003c291400084230350190540351a6800644ca031403107a40b5a0035002403902030b069440f29083d210b40790f8200001d20140e103a400c400280910142e80b03c90204110324a620361140c010302c03034107004c105c00d602a98000001114840050b8030305103081005020351000e10820503500481c1c603250240c95030396000503141d0840704400c469036441c00c2a980b1140a58010341031032142d015090300303a01200888800e000d44050704d0341c00e0501c035148030300c011001c4038010a4010340105940c82003a03003074041d03c20f00e0800c0b60041c0107418140500d80e2504841d503400601099140c0c480a41561140780c40008 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 526771205 1250 526769955 526769959
    0x609060111012c010b010507110307150f080708220c0506040308070507050114220510051e0903030319020f0720011e0e2106090712080405010f0c02 65
    0x2c0f6550f25a218180c040e040036030b000c800c200c050a2001d0302c40c01072003071420404050711900d0030641251128000108503969880d0144601500800c6903e00b00003041091015540e40460810041e07a000340785010240c800340a011904080c00f0141104c4915040c400e46203a220f44801d580c00e090202c030300100380e40625000302d40020044140b0140d00024030250f40110101c901080e613503001117a149910021042030b410f401e1041d40b05203080c06095030071007c0341141c8051050380751000148a20400300c0b2000c04204001141c04141240c403103101039003440d90f02060b003081c0d2200301007038891000500344114a64042c03080a00301d9803607419180c00e03001950b41c050304d44019280511a80c002d0106030b10012403140f500c0001584181c0c0800b00d072503203440c140c2c041002081000d841c40ea920b648000ea1080800794451201890045060b03402c8510600418280c00c15a2a660070600590805410700020580000104500c101142c088a01c2880c4c0f02c0c11407414004100d4090800d890025 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 526772455 1250 526771205 526771211
    0xc0105090102210a02060c0f040302100c0c1806080f0318010c0b100911090f09060d0816061803080f070c050a0606050a050f011b11031905010b1008060906011101 71
    0x41000307103203640136040b020010b800b00e5090b42c0360748402c3d0003e4002c852030401c2d01a010030084c8014104040c82c00329902441c14040680c0c50540d4500c0100141c030b8025078908007042149802c40181ca008000040c501c803005040c0039856079240c540c4a10807401071640c1800c240c090380c002c9902c41d61001d0121a00138450b1850360420b0400e440c00d440c61842002100d5040641800f0190481001c03034074803c40003440d181c3c6440400047c0a8441e00091509074040844503448010442c4d10300185440321024030310340080e200a02d4100200e03000980740c3d00e28000d81c10060710000ba000f00820303401155008400d8220344d10290216004c03034800317030020144c2c003882e2103140801503d508841d054410440b030f22499291600d05018020700c14208090000301d01010070348211030b840c40380001250143d0143c0d202c404600c000700b071400d603042c03003102e00e1148014800814031400f84a840f2080b101142d41d00c038410030b40a0010800f607000740c8028801c00c50640443c034103078084c08140201c0c0c4d407800024 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 526773705 1250 526772455 526772503
    0x302100c030210060e0402010c05030408031605060c040b1e09100f020f03091311090303040807090c141c0b030d0314010f082518050a1407020c0105090102 68
    0x600c4803010038000c501500c240302203000481003d0190310242c411424500b64107603299001110751101c804001d580f1800201300102e15890309000404481024992001c1d15005070310b01145441c2006044480003282480180010301c00701c81207851040d1401041d954020400c002d4030054404c180e851540240034a032102c1000341c0003428403140d02c0c82a000d8501c1c0c102c60b0460030340c036481140c0460f03070300180000d030a40c04805c2c2039000944200034602510700744940800030a03d1035200f5001703800c10b50311110080100d05000d015507840a8068a0110804684042400f985020302c1070344030046000043c0940141c5542c0e0700c032620104006040341c207002442c203c041c00403e100d500301c0c0c0e8040810000460407903440c805420850701440010301102242c0d8001e801c2c2c5120b02d9420441800c100500001c1404040c0c1c400c16500124160005160030b0240d000f10441d40e45010180000080e6010444082e401088840400d0000c0c00c05070750300c1954600407418080107071010001540d484401e = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 526774955 1250 526773705 526773707
    0x6010e151002100f0b13060e060d1403030106081017070e1e0a0c0311180f0a120b0601120b090c030a02040902031911070f080d11030a0c091d180304030210 68
    0x101009405541122406c2d03c00303401d20040e50300c2c90080d0078a220b6008081811b500700380340180c66644c041c4203070310682c0c000c42d581c9d1030451340300f0f90124000481c210180103505c100c40340003d0060a541d1411800c0c140c026080c25144c0106100d11140d04001100084d50901c0c50901c20444d4005490031140301d203041d61815004000030040303040020316141c0d04180391413003003044508103408042e5400d03005d51100100f12070403c6503006070390401d000c0e440021781c4119800030411420701c203154015062400710001016901c2c1054241855400d059a410070340d100c80d03030155089540c41500702e6587e940d003801400a44503d83c48034450910000401640c400c02e0a03400c81c080c010660103206018160150280a008420340074051100a091041c00500c5000081c004000b032400042000d11034a080007440ea00208e41c804d0703401c0c0d150070f08140041d074010080d0000e884200807110074030781a0340d1802e800c00c00042807144418201000400103060800030380d0001c5600800e910107050340b85c80 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 526776205 1250 526774955 526774961
    0x1113060906060c0218090114040b0106080c070b1501090b0403050102030103050d140f1c0e0c012727020a02073003030c11060106090806010e151002100f 67
    0x403035051054600000450b210b88510710f40241160020201001d0010051029407900c00290904001c4e658840103042e1072141c0031403480c030444c040c00400312190b25108001e40001c0300181141c110380e03030400140c0001010700d94529006605603030300840c40039401c0700507a450006508007490110000c1400800c101c0150000c5050301e1103841170b40da98100c4082e0543d24445100d680a40010080c000410740f0907006020380141142c1032070344050142544000d00c11110039001641041d0048514042c0c0b9503003000d40315841007003842070305002c01441220390781c200105008050041a20000420890709401007512600d1402a000c564503201440040e68850492044c4412840c00c0d560075800014000c11030ba038994411140c66010b411a96022002414485101801d10040c1011303001d0b000b6080080d00d0103801c581e103d4040c0207042c07440c010701e03141c0d050344400a029812010000450700c1d40314846101d20303098a00f0b0b031043c80100426400c1c500c00c1e00c5c080d5500352800b0741014103552150 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 526777455 1250 526776205 526776209
    0x20d060f080a140a03050a1107090612030206091515121b0108090703050a0201030921020d12150303140f0a0201060f0501030902030a02010e0d0b01090c020c010206070f0c111306 78
    0x20301c0e406180c2c0001d01030f0640303c4091207000b4000c11018008025905d000311542681244a0300590b9002a100c00317030401104c200e50440768030040d041020320101901085102c0d000301e0a40018900580350b030420f141c4040c001070000300d04200c0390380303080031b1174460400904904040c0c1c020344000d02407890101502c484120221400250034038003040340701030041001b0040d00c0e0460090414034000d90015005080d2010301142c031024910080300e03501002c05550003d005860307004e003200f5000508018078059040701662420340c60070006080060340f20031010101c079414100f0240784d0100c0d401030695400740d001350120301d11000440107c0c855065000c207007641c0c20101001c02580d10f03000110b080f0b81c8440340094040d400800d504000d580203e00c2d4100086000380200090781055941003840d4ac1d003a400f115000b030b22401c092140c00c2c0c052003050b152550a1009010600c3c108000815040c2e0344600032042c0130132000b910040c0100f80f643c01e0146140035003803000c03003040d000b4000d00412242c = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 526778705 1250 526777455 526777463
    0x60216140a0e0a15050d050a03080c0d0f051b0f031503030c0a0b0105130e0d1206050a03060f1107050a200405090c011d03030d020c0a050a0b0a0e030a050d020d060f080a 74
    0x80c0b1000f003020720b0022103481d003c03071f013080003098030b500c03941c0d800d560021000d40344440d02c0000307100b603010031100c50003190790316500a2000308044c18180d41500070380d0302114101140340d10502c40f0750203054480d403c1d01d61090000700b0700580303210340d5008a8114030403044190030a0186814507400c2c01049400c090407a1025640b822038a91500824002c03680303204120700310341c3c00510309a04900e00c0307241c880c42564101c1d03800089030b40ea103000158101da11644102c44803911024929803c007994414244c840704400181031620680341c3e00e00380c484c4101c15005061b200d02c5142140044882202d14160000240041100341007000e00c0366600d084406031140026589200200b080d1580050b03410644000b070029402d22418194a1010b900000c4550466124013641d10020030000c03c514a91135000d000c1d1243c8605000040c44180c5802a8652040b0360042101440031a4070104031105141491740050b2a103442c460a50041c0155a0009003440e1000802249a02e40810605c2005104d = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 526779955 1250 526778705 526778741
    0xf0906060d110d1403030a06090614010206070f031506030504061a0a0b0a020a15050405070f030803040b33040c080609010504020f13140109060216140a0e0a 69
    0x10001005419108004000e1002c55400069031a5003804035081c2880303482142040e14241c0c6404000e491070704112503e0080ba5191401040907803500d2055502414045080004a8100a0003c1d503030b100c004d0071043c20044a4010198910301ca0f0748040503880e900000b0070940c50303903080b00902400c420b5900b85d541515102e5020700050283c51600d11602c0301801e811119482d200030f01615030080310b0312100b5801000e00140004a020110041030b103801c00002031107042c039050441ca0000c2075040f0484000d0651414008100d55005480c1d00550110314040590ba4007144072460944121010a1050300030003540c4d00140010b140b100e012005a401300074101c0487c804a40c1c0000c255036103508101040010701c100e0030300e40c00501d079240035000c12500d4007081041c082a020099844075100002c088210f01d929a4085070075001000a07200a090f1480c8841881c410400c55200f007100d141419480c00c1c51a8035590010402081ca9204104452074500720300d2002c2e143c0300301808842c5e90 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 526781205 1250 526779955 526779961
    0x31f0b0a090906061b0b0604020c060907031703041e0c03140703110301021201120614070f03050a0e030d090c0515090405090102030c0f1608161a06010f05030604140f0906 75
    0x80302c0c584030a1a804030300c0c404020101d694541c8291b461024041c5074120345c08100c06035410408201a601031411031006000992541c01c040c3c000c0403101d007a100706480c0c1081404041804005141120081110300b84000c02d514035142d5003c001c554401403009100600d0603501010206403041228020f41c40e0010908088041608074450f10040b2038840503030000511601c0820000141c450b17100e0742d40059032080314480c440301100100d51600c00a0300300100280788540c54028150002c0400d4420300c004040302c0b5143d600d030b000e075405682d50903a03218013100500c42000040c40080402a00306c1c81d4035050544000390a03840060524000c80c20480400c001c283e0510072a0b1240f129001510f0405491401e01d00903175010003985468240d02c0c05101003c545188010002005201e0345c98081c080c580c9069448a400022584d81540030241001100c2c2d8012420440e0030b04540b41403507403640c0f52030000e4024460b4220b11500b10403207408000220303520341c00392030103001484122042c40e9 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 526782455 1250 526781205 526781207
    0x6060301020406022512291e040201140406022b170c0903061612060501391109010905010b040e060f0d0605010f060903020303031f0b0a09090606 64
    0x8803840c8101401a48451480c04600e20491814902811a0400e2501d0349030381d86807a251401c1b50315020313140099481031076070280010001460454240d40b42a00c00361500c8101d08543c0e0041c3c0510800d19105280041c0031a03205420308007801c511800d09544451311170364003d64540c074140c0c804c0a20034480c2080c005468140c85204504103d541d181010480b45814002d02c90501400d1404440400e221003405a60b083c003139107104600840c091244115414801080b00d0581035040165030300c0c0403014031481c0d07401008940d0b440c004100e1001004a8040380721a08500b1208115a0950601c031050401c2400c00381c003086003104903031000d00399032990716000c2200c07800e00c901070103c0001c01003080282c4800c440c031035101100400c1100340c100c0c554041110100d050000712921507075480140b0403041d401c0c1e01c4201404592411040803425580402c2e9030344800382c06440c50802a01d0480e40804a124034040604000200075440e2109440040c05003422405012086030510324042105 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 526783705 1250 526782455 526782457
    0x31806230f1602060d0f0911091527181c020c1c0602071b121109040620030709121101030c02070504061205010b1002060f0606120108010203090606030102 68
    0x2a10305a1246840d040069408600c00040300700704130b81240050258030801c03200c6100b82d401e02105910301082011395860607200105400d48035070b105030815000e10032070111030140341400300d00c00d4451003188640980001c14a40c4100c40c5454240040020425840d0202e81c01401a400d00801c44504040c5080809007040803481c0c1c1c0d000590090b0010303041480c140c0302d042c2e00c040d100807810449041135114a01641e0080d00c5c00d0f00c2181350350120103001c40315110700c0801004d038023130800c6880900e556003583c0f80c5c3d61424054810301100b404541808516842480d03880b004a000d41222001d0010f6007046400844400300800c0380000e0010f40c43c01140301c0760501c50b234031289550080c1c102c6070045d0001d21000f41c083d4114400e03014086240d440381d205071400b60954000707141100b036540ca40315003074680702c0b9603e5000d800940c00e58030102c0d0300060a160006111100c4c3c091641c1c4d22808505940240a2104204400740700000b400b95010360085020784110020380720340c1d6840e40149030a03 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 526784955 1250 526783705 526783717
    0x604151512112b03201c02060105031b0a24090f0b3a0905010e0313180e01050c0903061003150e070b0c0d0f1707030903180623 56
    0x1d07141140140c00b0340c9074100c902c5070703c500b4031034105110000c44603030441c5010001009030700e005601c0400e8081070300c2101545407145254900c001e141301e6040101198131508551158400303a000440c0f03850090392840b1004001e0030502040141e402021108002000705044205012502c2c1103404030f01d00344907640d0b110540700b090a00520b8a4003607000203910403442e844180188911007030f8640b9202c012840c0c103240d90a00c2e000411892810300702142143c0042603010659030040041000090340a01032108661900c02008914402001c00c10080e0204c4035217001103528003400c120740107000e00701512242d0400e5003211600d5644540c038079259004c5000c05071000e030803252603441d402680e8110182c04542d80f0151075146941300040d00e0035170000b036100c0704150081d0041203a46a40b2200c031030b001c000c051400d0010910885403c41070400094018010191901009001e15028804c40405190803a0310324400c25600c02c00204002e103129101e403500c0c03001d4911030000d4500441070b0b0321 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 526786205 1250 526784955 526784989
    0x191208120c0a051e1603050408010e0c0a150504080a060207120c05060f070306080f060405060c0f1801030b0607050105090706020a020604050d0c0b0c010b030c0111060415151211 78
    0x12605040e40c92150702043e06400940650208100103078425031729a20a00d0198400d84410f5216800d000c4120b00352005116140080d40c0020b40a2005035200a010307030442d00c0369000c5241c590110001142e02e4400c0f600000c50354032900e581c0c0c40811405600800c00e4501840c0c03050141d03002108215500d88044401400d40da004001041000490701541c0d5007003001c4d820002451540c2d15465401c05070896002041e9401031400c11091060a104861b07102e981c8048041c0351400c02d1070107444034083c1c5e1104510003032901d0042c030f11990182c0e100d42c0d0003650042110b511041d540c50b0441c040d1000712206145030240c02c500091407400000c08914241c2d0060130310741000d00700b00501c5400021008203440c0d10360070400c0085c031721408400415640400e04c0001c01c40d50f02c0d2000f0305203408040b03085941002100400c0032030320031380400c403540c00503402401c0c400030076402038040002d0550750580c0308d0700e11140003000410030462008008418813074224460003d2036030040014a41c1c922445032 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 526787455 1250 526786205 526786207
    0x11040602060a05061c03020c041b080c0d1404150e0619020c010f151505040f0e1f0909020301050c03040b04030f050d06060906020f1b191208120c0a05 66
    0x512102c81900700130341c0500d003e05204020400096554110319080c1400d802680200c480c512650030140181c40745114001807827000d607901958014920980101300441110011400c6000e403005134001101038850344244003568201414481e1030b0716400c08051422234a00b5024000035000402c80f10701c01c5030400c2607070404008569081001e0f40c00240c0e405115580c038590041001000e00c9100d142140f50012600c8540c10900203040191503514039206110701031008014901d11040198284c65501405114540790040484900034000e18020010350900c14081000e04182d407100440b940228024030080d1a034084612441c4019039002c2c141140980002d80840e0140a602c980ea00d81c0e454990711b4810742c180c00c0b104550345500644001101e20b041006072940c1049004024034034440540250050a0715401e40340b9510409640038034481680e03d440c42c6600350441c2c0007072407450300310402c0312403030329020025034045d01001134441c2c1d0300004039481904032010343d50024400e450301 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 526788705 1250 526787455 526787461
    0x50609060d0902091005030d020708031b010902090f16030203041a270102120106020c010c14070e09060a1b02190206041d040b060f03070e07020f030412061104060206 73
    0x3014055010441036403007592110071400050b111250340764800c91840101800240c1410201030400ba1100010401c40d40000018408524040206c07928251070440c0b810044650542e141d016148510010b9408070240d0b0800180c50811280345200d035207042c1038100c10042481c4250100c1c0000c0d103020707209603424441c1d074640c010010101500b109005403082c9444802c1008000130910030b002c0350074980d40204042c00c0e15540b124840b07015042500103010003c4000c00000c10040f400c4001801d000600c0301e80d603900400502900c4060003071400c80d00000d01d411b480b002d949640c10762b120003a1500c0c102c00c1c1828090f80004645c207585a6030b001e020a0345030b144e400b5410028100c416a17102400f004005a1a00c0c036084807603080007124000a05890a403c100c041442d0090400b4050181c0c1c80840c9400c4e0750100310709043d91000c0c0c04000c410780f10600100c1c81e04107003c03000314480c03000180206034200c40d050005190343c8115001d2015400c801000d07019030065105203409a4449404 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 526789955 1250 526788705 526788709
    0x803031308040e040c0510030c0e040b0406090903050c071409010605030a020f040806040c0e0610051608160b0705180d1a150a090203010e0105090a0e06041a07020601050609 76
    0x44034503400e00038065141010744030301250007001d60641d001c072810701800c4020840c0d82081000902007440c50308040119104402d4003400c4080e09900a920555803010811000c1e6125030100c4042c1002110400c4044254038014100741d0042e140001c0510035658006182c08000c40c0043c0c0c0ca40b000340c40c05050b80d1810b20291090780000e0000214140c091081004c1c0302c03120340c043c0c03004241000c000d003098200b80c1082c3d403401c00990006404039504004102042d01c425054440100451806660f00d50000700d14440ba4504014010a2001c001848002d046a04c80d4514003450040e8a0300700c0300d4440480c1500c25108401408503040c2c0d00400d030308064a410001d0800303007802041041c141401c4049854400743c0c003118040c1c1d01051400801e441e5040070b0040b08081d2000c04800c40c0756505200d50b1841000c8148a910300c154000c40000e00800020b40101d40348040c5401100c065091914000d4a41d08000d2140003245050500290201d880000d44034126a0090881840d140700101 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 526791205 1250 526789955 526789981
    0x130f0c08060a23040f022e0507060b24090307030f120908010212060f0d0204140709050f03070308210906010e094e0403060e1204050409150f09060510080303 69
    0x160b60750510310700440340748101f405901c2c502e110b540c09655483e035a408928042040f5410010458020b41c441080c232940003514843c4811400780c202e0002d1307140c0d40040006441c18040c1d41005182c695103a080c902008200001a82c207007c044d11034484083d10b03913088071300300c3c05a4440c01300200d2092001c03903107d007070102a4056804000c1d00808410480d80c011034180c0b16a680380c80404003000041000d07041d80801c016000d0003040b1200e2084014220001e580d8070210301014107511800200219210b08440509141350441d003e105030a140c08500706172501024482c0001000c1e8000001d910f0910100302c003080c2c024055040210030078106004410b580d094000910013142d811100ca00c81042008100185510002280e54503030451409000703995640c510010607038480910902000d58420644e41901c8081c0d40009407960b650a1100c41c1e880c1c2c0403120348100d4a4051603840c0721007e500b0464042c0e0113003500b070100d80c0343c11845040e080814450700549400501c003041403404444 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 526792455 1250 526791205 526791229
    0xa08240904030e0603070c0203010b03070614030703090f060e0705090103021f030f2a03020408100203091f0f06211b0f08060907060305130f0c08060a23040f02 70
    0x325058043d08a5100401e0041d8810f59440c808660802c80160851500740110415800107401920030319103058006031031903403040c0da101a00800030001415080c0300c0da01ca03d0140760032042c500f035001d4040c02d20400500842620324401d0240e19008215400d01b150380d5030407a5805408004042104058a40c001541a41c194101030300c0700c15491028403a40100107200c040344004601b10040c050740140d402200311012070034140184030400000c0b401050301645040c80a0000da0740342c1d5481049030030510130440200c03901c5000c003240e005902d0f1a90018204038221038041113040d0315070042125603032500c015100a4025003450a0000c0c10950840d118807141902201c040d6499151182e1110056040750741564441010410300d04c40801418000701980d090800080c02c02c40c030b694404290000000c1c1040150030100400c0002c0081081d00400c1c0010507600c0030308040f0180c030040c01036420100c2911000312071850740704014105c1c1c1c03801994007e4039240f0000300f513824441c18401c52 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 526793705 1250 526792455 526792457
    0x142a0d0c090e030a08090114070f020a021806010e0d05030d0911100c021903051e03070b0a0617240c0708030106021f090c06050c030c120a0824090403 66
    0x34040016011000d00484184008881c00b0359203c110340c0710001d00d2034a000780391022980c184622014841840040142c000c0041d140c8114a40340b854816840c000020800942000007040d140229001521080303010b03940980c1d41c01580301410081086550003071030050400c0d00100540c1700071507055408620300512948040c112690b038134000503400804140528003003640092a4011880c1100803030031402400b100c2c0c0c4d0115400c0d81c0703d40c2d940ba9505800400d5209214072072446c106010019545a0355102c104401c45150010590000d4101840745038454050f4001010700f00b080410f001c11903148000b41d001c0b50750311030010050120800b6020401601c0100b00b018086214140258040c00864006040701600340303280f21404610008034403103552426405c1000543c010708000101d54842ca0590349411080c1e100e281144900361000b00780740f0400d02d040304010301c0030015120660321929680055502c1e01e40c0c45124020103602c001000d840001e40310024a0000c4046800c6406 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 526794955 1250 526793705 526793723
    0x150b0a05030a050601080601050d050d08060f04020a03140903040b030a0b061908040201080a0b01050714010e0106060c0c1a0a051e0d0e2802090a0b0d142a0d 69
    0x5184086414100a001d041c0d5064000070014846c10608100281c01000700f80c502c41500041c0780c40346501c0c0c541449810081040715000706d2203665541d0748050749031200074003c6503120000c080c003400400841d00c50341c19107540c7c04000780301c850020041e5411980300c54813842c42c40d5104100200100000c070425940a141408141880c001d2003107029520080350300c90304d01d42d09103030001400c82c9a0040c450303140c103800c1c8030b1a032a4991340b1201f0b0743c0005501c500e6600042e20b041040d1805020320106e150b08a40c80d1400025040c0d84c400c642450f80f80c0240c950b2610306803101001d641c2a42d00b42182250381d1030402003000701500c2600200203c4000804012480c03403544900c589580c40750700e100c40340b03d0b120203903000217610070f0081e0180c6504e18100060403034003240540303103186d80d0124041d204200480000b600c07401260414110010014403221400c3e0a41ca000003006825408045e028490081d58104203071040e41d4105004c080505962044c250100400142e00f40003403044035800c103 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 526796205 1250 526794955 526794959
    0x60a09031704170601090501090902062a0f1b030303070c020d0f06380f1e0a15021e0a0807032001020405041815150305060c041a0304150b0a 62
    0x81c2d000c1c054040324000015040d1135150504c810305480041e0002c40d001c519014101006a8504080380c01c00383e221a5192203837089001220044040c600f07211286000c0c54080510a50021a9040c845010310400110900711241403668a0008aa903140803070450b485440c0507150036130251103600e200b10700b8403103441c0b00742c2d032410140c0706402117000c0306840340980e80003039440e0820b00804084d541480c003201e01100c04005201b20301e600c855180031341d0941c5c500e1134a44601740002144500e010b49110b0361580d503292440245d5010301443c0d401402840220214544c811700c03a4030780c0702d0072003006014000d0380d03458000c0194403e14040b030a000d001e403030005030020b01c8004400146030b020001a101d51505040c88140caa00000c0188852007003030300b0b50001080381c0c0201500140c1c1e00000154500b85003844118400a50405801842410200f205000000008000391131740003204401203a00300c009402c03c0d00080d100203141249400c5145180002c4c0d1b07000307141c0b41c807004200d950034903 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 526797455 1250 526796205 526796219
    0x20d020405131a1803031b03150a080c04151508130605040b0402090907120f0507030c0b04080c010c1520161202120a03020304020102030f0301080307020906060a09031704 75
    0x380da1086080c0607488044108683c0c40076804013159a00c083e0b0002d18551b140c40c000702035448056103400e45c18400301002045500c0e4599003a0044240007030656150184c94a0000ba902c1c0441c1c1384140c4280e051504800706007502c5d1080c00c0448844000400e611614548196210a0000d0802074054072141244c00071441e07d0140300c5c000c40c05001c1000e25070500380180450301d14004c1c09402103920103032301088a051045035400c005c0b50403640c00d591898040c40c01030b0a2000c15407000c0d1a022001c400401c0c8007220b03000410440c0d1810080380d8280650301d0043d5050342458001501d0100c00d020142d100d403107a034110460280c54000b0880201d034902c00610b141341c00940000101c81000e40c19071080014815244800042c640020211000c5610100d819842100d18a10803da000b00110b01164020800c1c0c40c2d02411b2080056142d41c0c540c281640d9036048248142c2c413031040d40011441c0340c01c5ca0070445403100040d980f1403000c00d0454407240d500701d5030301c90620b07a00d841c1044001001c1e = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 526798561 1106 526797455 526797473
    0x1e0203090c370314030a0315030f11040b04020a0e0109080105060307060c0606050603160f0309080f0703020a05010219091a1912090809040c050403020d02040513 71
    0x540c032161030b820420308031940001c01030812018a0001441d0110142c132004d0081d9508001540c48901c940301c3c410a54400a410390301020b168201096400070fa560440501420114180c1800c0002c2002c80c0d201c84103140020700c0031111101d0943e80400d8800c000c2c800c8800a100354240340e000240c80395000d03c1040240189511130508101207508110300800000340402d480e0b1400c16540034602c0740081088001440700007113440c48a00a1188107a00c40d00822180e040840c0403244420950011500703030258401c40d182c602c0043c03000d0005018134031950300d80d8159601e48000182450b0340d0f44e000103010a00411011503411510000d0301c4040c11541c107601e41e5001d10303400580b540c00101880b5103640c2e040001880500111100900c4a514180c1d010441e04160480c1201c02d8052400000c0d03108a408403c035015113803903004180c100b80c42d04688076440d03d9a552f80494 = true := by decide +kernel

theorem cover : BRFrame.Cov 526618705 526798561 := by
  have h0 := BRFrame.cov_init 526618705
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526618705 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526618705 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526618705 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526618705 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526618705 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526618705 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526618705 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526618705 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526618705 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526618705 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526618705 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526618705 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526618705 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526618705 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526618705 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526618705 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526618705 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526618705 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526618705 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526618705 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526618705 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526618705 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526618705 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526618705 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526618705 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526618705 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526618705 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526618705 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526618705 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526618705 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526618705 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526618705 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526618705 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526618705 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526618705 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526618705 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526618705 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526618705 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526618705 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526618705 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526618705 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526618705 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526618705 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526618705 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526618705 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526618705 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526618705 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526618705 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526618705 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526618705 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526618705 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526618705 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526618705 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526618705 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526618705 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526618705 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526618705 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526618705 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526618705 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526618705 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526618705 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526618705 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526618705 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526618705 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526618705 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526618705 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526618705 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526618705 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526618705 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526618705 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526618705 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526618705 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526618705 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526618705 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526618705 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526618705 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526618705 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526618705 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526618705 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526618705 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526618705 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526618705 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526618705 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526618705 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526618705 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526618705 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526618705 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526618705 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526618705 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526618705 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526618705 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526618705 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526618705 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526618705 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526618705 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526618705 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526618705 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526618705 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526618705 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526618705 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526618705 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526618705 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526618705 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526618705 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526618705 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526618705 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526618705 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526618705 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526618705 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526618705 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526618705 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526618705 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526618705 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526618705 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526618705 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526618705 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526618705 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526618705 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526618705 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526618705 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526618705 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526618705 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526618705 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526618705 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526618705 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526618705 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526618705 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526618705 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526618705 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526618705 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526618705 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526618705 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526618705 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526618705 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526618705 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526618705 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526618705 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526618705 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526618705 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526618705 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526618705 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526618705 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526618705 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526618705 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 526618705 ≤ n) (h2 : n < 526798561) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
