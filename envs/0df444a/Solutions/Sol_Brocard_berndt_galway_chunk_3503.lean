-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3503
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:50:48.918679+00:00
-- url     : https://prove2.me/submissions/56cf6d46-6e52-41ef-abd8-9e89178728a8

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 629856115 ≤ n < 630035971 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 629857365 1250 629856115 629856179
    0x2d0603031b0f03030507020c1c1209051f03090206180f040b06070b04021516030905060a0e04020d2903060c18270408181909110d0606020601 62
    0x54042c815002550789440d000c226600d80e890304915101103c0380080d8800d0004059021207078518030005100e6201d001036803d4480324400550f0313485802d01c5070640200c0954200807584030a19807940c0c00104030304000900304044d40104440e504882403d810445103001118154a0414005800c0c0700c2e0845003400480c4514021400b01d020b4158003d1801c0000804901195540c0020300b062919800083d51a1f60491001040c483e005c1e0034140d0210303541c9440031503d0709103074040b59a04d00e01d07600c4014082e5075840920009501c0311151030051540c03099000c400c50000080701c0d5050040446140503508920109070600c0750140089074038400403c02006103908818200c4422641250240c0b803c2040300d00181c20142900b80040360b16440004000412041d00090062442082080049226480284011460059564020031a10300301c104a0034003a038122080907081203a01c1414101c1c9505070f5070a0b100c085d004407000d80c1109005006c00d50480c2c000c03140320000081c0d0322a06039 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 629858615 1250 629857365 629857373
    0x21905071e0213020c071701290603071d120c010e0f090a0903090b0c0a0606050105032703131202040c052718150f0102010608030301092d0603031b 65
    0x30f900e85680048540c0104151800c0c0d00700388840d80041c03c54952191400c4218070b402402401107a1018900003200720742c008201407102176615a07902c0141200d40b650310380300c4055a42280e600042c84c61003801100003125a1545807000201181f40b400604080c0c01c2040050064800314104034020000142d0a062030742c2e5888046410200f1108000f4081e1743d0f5050031a00b81c009504416101c1c01c000400740d110800001d5130b4580c060042004002c142e0300c80c0c00441d0584415262441c1111120760001c80400340c2010100b40c5148446c2180c3c9081c100c00d490b03c413a00d429500a106440c0c260720307501c0039400c00c0d01500300c08040b07510b0418606511300e220112a0105c000c8408043d004007810b4140507110840204000d150803101140345d86815961110752001e0000c0c6c290051300020090002035005008210a4a03003174009181507130308210203070300200013141c20788080c240a1054003411100f4549260300a1200c80e00214905013542005001c40303014070100c48071480307005a200007207 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 629859865 1250 629858615 629858629
    0x903120c0a17040c0801181104152c0c1c09030e0a032001180e0915040c150f0e01030518032b1a090a021905071e02 51
    0xc6151111500e40754860141d0440c1d00080150700059500281c506001c02e1011180d00442103030a002d00911948075201102039111040c200d0040001e440103110303854900d05038000c49241f20802c445108402d544510300f00e085820110504c0403042515030401c1446402144564044001c00c01c040c82c16010b0318a5031000d110a506182c816035813400c03c001054400c102001d10580000c1080b1045901c134103000c8400030202d000e25105060450341030f01994002c40141340317000350000c0900306003031420f175200c1e0742044003c204440602442900c2d942c82c51442c0c00707240c0224000c1740340b07111f050304061110390b00740b03032003000c507400c2c0840d9a0f044020b55501005012b01d0030028078010a181e104d0700c490503840c00c00761080300f0b80781c0008070742e802d840c4c0c0740d4505000c04590040d14a422440d0700c5c108040031034060181154881c1d0352a00054540c0c10040300568011800f10001460945141c210010000098a080d40060400264441032001030b00501d02c1002c0301003e44404844207500240c2c0c2 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 629861115 1250 629859865 629859871
    0xc02150316230f0a0e2e0f050910030905010207030c050f0c0a0b09041523010e0a0608040f050d0305060a05100f0e03100f06050111061302010c2102070501020105090312 74
    0x19011000030810803a610038100c40d0851781020306911402c4100d00c0c40c0c84030352811100d5410001524030400c2d108240300b01403205500c101c640f103103032600c0308183c03d22061020248880c4145505ca4841e140051000d100409542c0c0c020780c1c400641018624100e403c0141d81d00400b1500d9000f00301a601c2d03507903118140e400b210b800f00c01c03203981e9007043d001040c0035040b4034000090160b0741c0000095083ca201c1194403a4001c003501c4a40c40f4800c03540103540c040000700900d070b0070442400d0280040303402991031540041c0100100a4040c02030740ea41d51074040011900e100180c0c40b41c060081034200340c402140542021202d42c4020554400010f1070007600b00c200b04104507000f508801d00d40c030140100c90380c0242c8540300344103a0060301451405403c2c0e07885013a00003060f41d410043d100001248190046e410000c610321071080b1b0740c004507120380c0c013400250f440d81e074804050034803044412201580a030107500a01403180c5814006402c494004080300c0703064104000c0c9600f404246006564 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 629862365 1250 629861115 629861137
    0x30b010e0417071103062509033503010305030d060b0a08040b100f030809030606121203071803050105160e030d180e090303040c05030703020609010c0215031623 71
    0x40c42e0801c84c01c02c1c00307043c04407808107a00f5000701c1d4284280811061100e2131305032106064040840d500400c200da4030b000600c806040302c1401210a04d49034a191442400e02c001c020342a100400c058100d10510350003a401252294000121400c011348540242c50050881d500c1c080d0a00501031000380c20002d000340010520b0402c10300103581c40e403280f542038000d1714a280c005c6507043e8992805209a0b40b040039098802d01c104400071790781d0302d00488030348856070310403024000b9030010040101c441e0300003a2104044c0203550020350100da0341150f03804015401000040b44900300320b4034542c04041041c445a0420041401c1082d036901c000a64450018961811680160007030200304602c1546030000c0500044438814014101000800345008030f001e00c0360000d2040d41d840c2015522035407480b0081d0018014885241b1960049840900380e0313002501c013607400c03440001d1000450380125142c5500d10f004d914510403413517003d14601d403c02050148110280c1040c0307001e02d91802141030790a = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 629863615 1250 629862365 629862367
    0xb09060909061305130512130e0c070f030309150614010509011e0801030c060305040c12050a061b0e03010b03061503031207050403060e0d0c03050d1113030b010e0417 73
    0x703045525280f14406140c64035038410846030500f000e0403081d8500c0c200d0140c40d2481203800010307460309482e04496200b1540c0305000c070028508100b09020f40c100030b1040d210f008080c010701011502008201d4003051081d078000440c50f0f4141351107a0b0803402290080b40d40e40ca001c4050000c45030105030700c461a0000d00784103845500c00c100485520b011400341c0b0b80703154401d582c04e00070140c04c0184941a40d03c14448601c8043d1684422801c640040703801030440240c3d6101001005400b402150034180940103403030044c0003036119002034490003400101a2680c448007011010360187c1d02500c00c010032070080c444156900000303275031100003410184540d440c0110b0741039103940c10011101403c01303a106040042c641000d000c0e1407900248015912181080c0344107081c0c0c4c40115900110769003984482d00d400101c1e4804844a422141000200075078075901c414030601034001901000d031800030300003801811407420341c01c42c210680c091041820070505010016500c84d40c18244100c02508107 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 629864865 1250 629863615 629863621
    0x61a100503130c0b030601030e0f2802040c080702070803121504060503060c030a0f0219081b0d0608011d06181513060e0d120207151b090b09060909 65
    0x4030402c00e0566400422040030810b0014030f5151510140d4403546007600e04115011005020a44a50880b002e84000d0380000414800c01c28560300d10801440701da40c84d031031200d085540820115074815020001090440080200050741000001c2c090200030014508059040b80609180300015010103155085490003250685882c0d20003030081200a044540700c2c1041e00c0002c003e03038000c2d42c10710a040d040c00c211042c030018a0080f14240102c25400d0613400681950880d6982805031140800d20386280c1050381e0410050041c0903902030014000500740d00e06a40d060840e07c04c40c02400c469a001c0124200d00071001c2099a4071021145022184c0c290040401c0c0c03e00c0c0b01d4080e4111b5145690050050100149420000ca60f104020030040c2d250075001a40d944c003600c028007000107840c01001000c4001035004bd00d01c00e481090b80212101c4503800000948055811412100c000000c242c0780e03450740005100018a07440c4002d92071b00f0000f402144083c0305a01c80180210140008 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 629866115 1250 629864865 629864881
    0x90a0821030a180807030e01090e01050f010c020301061409130c0e1b030406060603050a0902031f060f0e1f05130b0f040f02180a0806070315170703061a100503 70
    0xb400440501c0b40240305184203071521390b4590704850425400070b19036150040d6154050010f100540b80c4001046004e6882c01d0108048a03821840b8903041050008070400141c0b001d02071040902482940b01c81003c42e0001884402070000b0540313144071002040300300c00300700603031420001c0e111010880905035540c154542040306c000d04868113408000001c200038024560700100545d81c2d01d80d4148030030f89480402401b51948614080d50540100f90103c43c459585500e018455980303020100304182d58591650f01c0390f8150740186201d80300c81040040c401d002c05141035980111445207209142440007280391589184c1d42903085590360310800e0303482e0780c8224401e8208a0004c0c02805400c0302042c0c0714010b134000440e0f80c034060380d07c01100704e4545001a698400e41c0c40580080c4141d0f41d54038000c0f03002e071080313800c0c03060703d00078807a004110409000c0b040c49490307602600400300c0c14a180750000480e060010500c641920390344103850103560f84140d9585810545ca840d6441c1c1d155041 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 629867365 1250 629866115 629866121
    0x501110703050a210e0a18060e0f070e0d0302070b030a020d020c010605040e01060e06040f1e09020f0d210905270709030803040605040620090a0821030a 67
    0x1c040c000340318886401080202c1e80440311381c0701d0401c50102e400650700362000d5400303c80f440c203483d40c4501a1030060003080444209070780c41801c002d1002c2013840d07031003141903d840000c0e94407120894640d010030070403d40045140e0404182503500481c40216501c0007501c0e5007032400f40b05d0322948000081442405160191070504160f10cd0455444102101060081186100d058001c500f0f1404141d8094010700c00c03201285c030142071000803030b664102040010540030380d5090361b05a640c03100d4644140988034030b0481c140c0c1868000341c0040540100000001c051a003a031080c00d1541808000841a940d0b03004400ca410b01044003c40d00c003541921400f100343c10882e0840b0b000c05104002052941c09946201e44000084045488884044076020940e001c0a01320791002c101080005455034890340d40a8050305000691006000d0628036080c4104100b40404002103200703101f500d0018050401001c2c16001000c84185c0c95002000b10400078041c0d20340f400021000405545580d0 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 629868615 1250 629867365 629867369
    0x16081e03040507172a030c091504050402120604120305060d0309140d060c051309020301380f03150103051909140706090806010e010b1920061503011505011107 70
    0x10982c44c1c070080000c1036804281700641c01c40742c070038812540300c1c620300c0c1400480140140700d1201e0b401c51070008003044c080075240180040760803850145560706520b10503c03006008030301c00c1c0a100b107404203045009050b18005040d191048a2180c040c0c40001e811504030021150140c121a01d01e43c1d480380010304042440c0320141011742045400000581c0c080300a244040a030118079416070344521600d8102e00090150340320072a5001341491943d00003015801d062044041510b0101a40e813000e2202c82d00081c178003c0147c00301005101c030032403440030302600f100340c02e2030704105524000095020071154a8864940a682c920780f160500c81d24203812000c440d40c00d412a44902ea89a0005110800314860b102007030150718004a107a40101c0e00550413120264941070030980c02c800c0098103c004507000702e003440014140000a0070b5031041c1c2d00c2d1090038001c041c255524054040c1c10807400e104155500c42d03450720960004100400141e2400d49100386031404c982507a003480c0c207140c94426 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 629869865 1250 629868615 629868643
    0x140d060609020301080f160303051309020d05060f01081320030303040503130509010303020703061a0d03021c02150f06030708150601021605091b16081e0304050717 72
    0x2240000ca100c0364580c00450481d50000c01b00c8404a140303d074444d40340d00f0410165281403100500410219100d0001b504880c2040398100d5030072551044010100e0b889480720001d41520749003000610300d443c2c00140d52408003802c01901071703e0507c1c180303a0b80741c0003038200030a0f040000410407112001162440c601e010041c080729a01d041a040c507503030303d4011041998141145040100b040d08181c0170760360403242d041d001003940344c0c1503644100c060201c142c0340648440c807140010212341e54500e490826180030741c01030420141c041190880c0103180300c1070030040d94446850000c1a01d460a403c80d03100e6400303083e0307019036120503000906044aa41c005481031003019520609034489079151805042d090b0216940841e110031a10031070951481456404482c86001520355080031a4003040c0d0700c242900f00e4a808101c5207400040030a01c141611002d0002c18908110b142c1400040c0e0b440075201c810780d00b5450155070722a650316490161366007800f040c0c1000d19a94004001400754507400c = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 629871115 1250 629869865 629869871
    0xc120e01021c0618090804030b0408090a031407080316060905030910050d0b030c09060d030c050f01020c07140d03050a12020f1809091b0105190503181501140d06 71
    0x1000c860068901c034083c81061020b41c01208950081c85c3c42030180b0b603640310740e48a0409296886921100304000d0056403951800c0044410341e60b0350098420145218403080e0020840a186c01e5140c0022600900c1c85580b0030482c0441070050003142c58007165103e80082002849072424500758042e0030901c94000b0b0500000920040d01300c000742800e50301c0703598100240e580c84810903554804001303030785401c084094040307007042c18014070b900d03001c0d030084c10040f00ca119240d41d20707441c10301d054100c00060b075030210f0303082e6190340c060001400030002007400700d0340c1110380030004103c0c0705a6480101404000250172a407240a007803040c440515240e011034944004c0005901c0703a034000310f22110003208904410100b0300d4030564050250050400820701c5c00303840c03444600124003045001d410f1000c1404030801603050070000b015000d0701d6540d25a1030b400c0191540c0d8002d80c44501b803517100e402c000c4100300880d948070b0840f41150703008840d140407a110203002c500b030b1000185005c1c1429003 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 629872365 1250 629871115 629871157
    0x4060801020d0b010f0504060f0c1e111815010c05071a30150111011104061e08071805030a110f011d0904030201020909150a0501030c120e0102 63
    0xc0e02d64070080c981c40b020307210800b0b140101441100d8504c01d5029800104211000c0c0e001460712503000303010158450840942c500c074400190500c9120100c10031950100c1c2003552490794104030b0384a084a80c00608284030b181880345c01800e4100762009482c1c108042d03118800107100041100c2002007180c000309002d0400040e4200030302e0342c405400340c0e002078000c8a03c1c14500f041c0c0e588005d00442c41d00b02021050b212000308204600d5002c6450341080140020080001000c0c800c9035900c001c81007019603a18074005003c0c14410303802c50707000d0342c130b0301d43e03228001006400c0000c482e4000b99500d026459a8090050380d0f0802078290007480c0c2600c99601c0071010090762851400c01c2d03070f0080300e20345003a002c810011600b44c1000c5806001502544485c0c40d46070030b007480c115420911031300001d401e008070702d0040340000000701c5040001005400044499041c985d988001a200030300c3e0501140110031405402c0840c17a181c401c02095480910710b90040081d81501d1070000e0002c0c89109500b = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 629873615 1250 629872365 629872387
    0xf010207170a030f08060904020d080d181b0503030d02031b040b07050f06070c06020c0a020d05071503020307092601110c0111120412140f1911070b090406080102 71
    0x2c00c180d03104a010941c0c40b11405203050042030300fa442003a0007080e000b0607540d20f81c01d1101a001c0101c0896845200380440c0d00440b002c0c3c083c14a854000148261000c50383c0d08109070b180a016a9110719504414824800ea03200401103034121030507401c02503a2030719001c0c2c0ca001c1c4400305084031a80044042004a070010150000704103050040c021142c3d040450500c554481005035440400328840c10070100000f042600a010081042c9041d202400266000306401d604002d00803552500300f0441803000e810310669100300540c4a20b000c6040d8501200094400751983c0114a0420a94008608800101e850b2484104040d000030b03c400a60410b284405422480c94180a942888443c40b154500c1e83c003900c035511441c00c50340105854a454844885903900d100da0100038081944440c0c0c034040e040181a0340c031490a44075590005030b11605d82c00d88891030103604100d01d215510744800e00005549007941c0c654a2019540c84920000400802c002e900025540d40041115800b036 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 629874865 1250 629873615 629873623
    0x1090807140d05030109110f0c070f0602012007060b030a0b092811190b030103120c120305130204050a0c020705150a050f1b06010f0816050f01020717 66
    0x26441400015054205180c1c41c0d900d880203121694000346060004000780161900006140c0c40e440782024903100d2900702800044d401342905c840c1561104004001480c402400c440041141d0302c000c02556620305d00d5030744021b40c039172281c00101c00c020680c6001d104c1075512810446070b0060440701210081c0c0b521a021072000c84007440c5501540c22140254507114010442d8400b0800c0b800004480300e13030701e00711210251100c1036004600302c04240000c01e64841c2000c003400464540b2500d0350316501d0403500540b0000d20300c0c170030070440c3c200b20710001c0c10382c1c8080e01c01202c90f81404144c603139a0520a0881e820260006940241001c003408040c080542c4441900758282c1c3c01d41d0401912442030006000904d070711080b071a682042030080551141d4081e00141c404181003034508800010341c060690004440d4500640128004101341c580c8040054002e09142010704004503034000d02640880d0f9500c9914015204030034583c40d035030300c00e00400c0c001e000000d030502403100213040c18a80c0c1e = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 629876115 1250 629874865 629874877
    0xc2b0e010b0402040302090402060d110705070f06110d0f030b0402070b01051002060c0703031509020708030f01050f010e0f0d0b070c060b03030405090105010c210c0c090509060106050705030903010908 88
    0xe529046410074242403a000721800e50390003034030384c070416207455080c0032075a80708003081000c1c20383e0f48020040c160103002c01024214024002403201c9030130a10071035840080da074485014052001203441d110300000c103031544498a03a0070128020b44503d0000d50145c0003190195500c60320000e8140104100710f003106058a509403441210340300840b80984c0e41e481c0584800c3c42059090040c200001e10070303001000e0096000e003c00c0c00581c1e40354550b500303a0f0042901103c00f50801f10030007004051008906004200403a0b004016000c2a00081c2a1001405040d0300400c54414540f040c0c0d16401c1c1c00800300d0342c3c01043c0c8a49072411341703801072000201c143c3c1250b0150421821001c3c900c1e002003a10283d400c02044405c0d01d910f40340055031400f02c24002110711298010008004511480c1e0089040c0034644801c10010301500e02052442490f030090b00c800c62622081c0b00c019480010610f05569440c1017050b9902c1c8242051407540c0100d540c5c3c3c40c0c0c10760901f401441003000303136070291074 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 629877365 1250 629876115 629876141
    0xe0304090e0313121109040b04031706100e0409120320040305030a12180c0f0905090309040207050a052505060903060c030a1401170607090602060c2b 66
    0xc500e25400c507400761280300780d80802121900300d90040c00701c074000d0200e2102007445400081104030609000c640010001c8400b515401c1030380c8200f2041c5504a581c0240c1c4040100d0300341028602100082e0703900c1c90407804142004411590480241c45035488048107a8100342c0000e4003c0900760020090605e0601c60480e00c101d01598901004003402900c00f41d0398810099410000c0414007280e4005902d5200000640c96546d8480c01600c40da40c0341c0b105078050725825000609040346401c480000380c0c4030100b2640b914040008045010040d5104103108507401750303071905103007455031414a40d08070144c010301a001c10071640d1540010001540c2144c0c009001c4941d958904000701d9001d14141a50160050000128a0415440299031000e040740e8002105281c91045043d0401d00742c124076213180ba40c40010070008801c001155000156141c03180c641420810b000b034076007002501041e0880c00c00b081c2c21026200500303d1292200742d118030090920701d039051090207010524000c203 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 629878615 1250 629877365 629877371
    0xa121b1b17030f090112020403021c0302010e030c060a050403110718050115020d0f0516030908010b0402030702150a060b0a050d0b0a1a0f0f0c0f0c0901030c060f020f010e030409 78
    0x28400c00004800d43d4080b008100a03e0f0400c0300c15030040d40e2696100c0c41d051241ea07403c020120059680304843c1007500c549001300c3c0316024203850080c0c00c4400320402c8524a60040c0841d4058220004038250701484480002c03525840f64901179171070103616109844640101c1a0114800c5e2003260030240e2080010000d005590b6240c5100c91040c540c055400b0050f0001c03202135409030701599803403d9034000e611303149241c4890010100e40c0c482c1102c40c00c90005022600401100009019000c51414101c60462070b50504c4440a5a81d1020b0024004101d0b001000520114081d5010500800c0c070462060f681c0c3c80c4105004241c1d03800b0807a0749040a00d0710504a1890400c0c0b810001170f40c1c9000030310ba8400860010448150300f0030800c5a9200400300050180000b090000c1d08207910320200a1400400340440b035800c000c40b01d100e09024902e1880100045041c0341000c00440d0018144401320080c41700c4224145001800001030642c20b2843c5950401c8000000f002180e92480c010 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 629879865 1250 629878615 629878649
    0x8090111120f072003090102120301050d020d030e0a0f051c031209140f0a0c14010503040807082116031a221e06080a121b1b 55
    0x802014054006000c010310722000000e940004240315030350b001040380c1003008114160080381102800082084203850f000811040310340c2d601080017880962481800500b50f606050206800c10f85420001e071207043c02c21165418035016941c0d8038081d2501600360110640c0304c195880c1d000849204190040c603225000e420740000203100e01c540c0c0e541c0f542d1440703031039150514882c3c0913043c01c440c141c848070759081c66071a00c20000c0020003180c14007800034000d00107860811038407400243d031203000641404a2612031a070307800002c80740c1c80b40e800901d0a84800450605d8003803401120000a480d000391000d09000b44240e0368640d1281c54100410031000e11026022401d403102e114045200b05a580c007600c20030700e44001240c000d151002241004ca01c958803040083d5000200d055000c034035405030700151000d4500404010b4070704240203209003501c070303524024403510018000040000e0b50f441616000d00000c14085111742110607082c2c80300c180039400f240001184501801507040c1e001c6 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 629881115 1250 629879865 629879891
    0x80303060f03010b130b01350714160c090e07050f0103020a090509090111040f06030c030207110906150a08160f09150e040e0102091e0d15020415080901 67
    0x58000c607200c011703014000c0100b200341d4001c0a40050740d00181480803d0030018041e038041994006140c400d04412107070034003542400340301c000c030103072122003008206001218001c803014100c4441d043c3c82c0390082c0c2e803920306050071100316000c4e8215900d52170801401d00c43c0e48200060301010b0380c42c00c032402c003e280c450000640807842145009000309052540c10492072030060150380e806038040b0001f28525006412201c103a5004c1c2e0045840f06900000c00c0c44075076898420704074030003c00d040031490410107880c1d036240c52400b4003826100b0b5074980002411383c3c488500e9011015140310460351100f1001c40c0107800346100b02d03820a0b011821a6101800910902103c1c0e0105925150226294104032000024002611040c0e0a100410741610160b4440f0301c520f400000e1040001615000c00204010014030560080d141c1c00c1c3c821501a49a43e4425031250b8015a02074090854158610f0f58040030b8010342c1c0c00940014280d1300181400394101c0701c5039214010a50007040708600c1180 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 629882365 1250 629881115 629881121
    0xa0212030d14150f060d0c0903120212090d0f080d0902011202031006080403110a0f060c0f02032a160302090906070c030305060f03060403050d0c08130b130c080303060f0301 76
    0x2844401d4000444031510403800d001c091210040805001c5d0f500e40502c0711020000c0d10b146482901c00151607500070010303ca103078281c0140e150000d101a00100101802e1040240104030145100340e1020104404200142c58540000c80d8400381254451505c2e901c4040103220341c01e001d0b4003041041003004900340242c401ca80c071070f0240a40c2458038a040040807162804c00602c1202404400f051000440c441044403001a0344650701c528034100300c0f4034080d001d8852180800003841404400c00b4041a00170055a20314012a0080324401090000703048100c1d4000300c01038158001c0d1140c602d40001c40030f01020640703000740c800b000341d034882c00b900c144d0390601242d84400142040754041e00092007134111039004140244211a9007006000007414000b090b42c0440c041500014504a100d9903401644000c54442c109a40c080c1350000c0c49110034181c1810041030540031400154140c0300348110a0714160300f1500c0c0080c05600d41c010b1660341c0c2d00c1640d002c1d20400001ca0107400905e0140 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 629883615 1250 629882365 629882371
    0x1d0306040606050307140904060b13020d0507030c020a2a32090709030222020c1614090a020c150403020a051b13050402010e030109050610080d050a050c0a0212030d14 73
    0x1030031102c02988d80d40c4030034005120442c1626802800402001c008868600141c20112b9541c04006110304181d90090112240f1000c80340075900316082c404042420480d8a9001d00e090441c001e00f03081e21010300b94200d400540107001290900880c81118001c010b5255080405d45485c1003400d082040030840302103800c0b070f0044000b400c000c00030300c01030605291441d8521070800c900c1508034145840b80040c1d0f0031a0307a05540c02d41c48182c0e0692945110301408d001411260212811841048040341c2d00150041440c2c01185e00040e00070294002005000c1c203000c0c04042054850030249030094940d1200481a00d051054002105c031400e41c3d030094043c2c40c207008100780c041240d078601c40d401500340108140d06001c903048510120b91020700400c55068400e0014011518103215103074107403115900582c6150740100c140c181215001400c8450307080d0340742801030b20350610038030181c508214040c0094004d104403070504210403001000d401d16104440c0c0c1886500a92803204074241381c12 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 629884865 1250 629883615 629883619
    0x23010e04120509030a081611060f1602030a02030f0717070e06120a050601090209030f030a050a08280207061a03030409390914101d030604060605030714 67
    0x1007441c0d03880141c040c0d07004042d14034000c2c054a08a104035110165a500312950303041c40005a0202c0c01c0030450507021002200c00103c80f05820803060408440c2c0a0260300503080b81c60380384031208020341d0340410071a82d030582d00400311409140c0035500345440d1003082c130484004984060003200c1c11b50004c21400107441c42e801400e521983e414040160303900291040b0f445901030103c4020100d2003c0c0407141c043c2000ca0000f41c1c1e60320b40002850f1500050410311509a001880f0301d140840c0e100c0f0494020b013001d4900861540c03164041c807284400d0001480c150300000110b50700740b00c00c141d000b40c4000d60150004000d03030183c03070030404441d4032070718030881e40358000304404d22101000c3d0b800050a07011340701303525180c600d14003180040f90312070802c6a443e000102c540050070343d6000c1d0250b40a03140110460295030b01400c0403d009041d0a200841408610f0000b901c800d016030340703940d201c80801801c0b64450304050820341c009141d1800f4185c040d00400c040843c14000380000a9404000 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 629886115 1250 629884865 629884883
    0x702010614010c030302070b0109050108070509090a0201140417060420150d1514031c08010308030406180f060507020f030409051003050706030b01031d0d030515030123010e04 77
    0x445401180c6200c3c0280c01101410340c00e000c0d400200380029003060280985000008155040c001d006140c2015540094810b200490130004000c00204208000c01d50a00b0042884034240c1e03414011801503030400303502c40c3d8912030840c1345403030001480703030103280908107146260200680745800019450886504010b42d6840d003030903407100e04000c0c0200e184071000019a103481c8956804031010395030228139455480400a080b03032500344a102e40c45841000d00c41e006414000c005055001c0500c4042d14150f00840000c00348151a000313520305101e000d01b0250711744182d290000089002840c1030310328916007000144154000202d0742e00d42c0c0404030003107003000d11f02805035018041c000d080d10001191041c000001400c00c020840103820662400719230410b01000040480f144441c88150865480b86040540f6101252907816400103140100e5a99540745144520905075031180e42c040d03180815555841c480311030040d4003001e11030450183c0341d0f42d550402003640400e445c050540d0348 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 629887365 1250 629886115 629886149
    0x5030c03181002190c1502031215012a0210030516021923030406050a020d050a0c0209070c1b090f02030408041e080303012402070b090f0a0314031207020106 69
    0x8509541c20080303115045d80c01c045516628440305042c0c5544c0c9010250384082641181d003540c0001d20b41c0d01100e6000c0c0010000b40440c002000020703502441d45034002c580c1845a03080c1d16044807080e003142c014003003d5081d1f1410a00900900d0205c6282c141c0e4814146a20b14941c030204207400724142c5004404451001a154889096290940c00001c1c000c0d01034803454126050029000618194648070b444280c080000b89c100ba403074190320400c1003020803000415980294a01a00c41d030160740e4583e003580e80d1300050f11104d08175400a042030361400d80420b4241144103081059803a4813000348243c501030b000c0a0240c3c002501c004045080510050010088115000300555080402c0c480919900d0503c0303030550b40281c100084039520300c10301000301d400c010b0f8082d1045013184000e01c155031901200034654003413000742d9842410024030f07a00c51079651044000103550400d034549018561048440e039a540800c0c04404520645400155024010b03c01e440c221b6200d600c09503c00c0f030b = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 629888615 1250 629887365 629887393
    0x2010903021f150e100e060315070e0411090f03120f030402030a06020f21090604110613080102180d120318150608071e0513060305030c03181002 64
    0x8503090480c0b038925510b0034540d04450618810398002c2050142c1d1820301d00380b05c1c031400340700090b030382003100003418a00502200340c60005a2140d505e40461482d40700d0b44400f00c0803241c404e0320a413880ea0007401d05100244080340840240040d07802282c00744483c0c9844414151280242030101845850900250720501011002158020310080590b460048203544000413608101c001302104640442c82d581ca4140030012008680000752182c1c00c0d5250240d69180d4078480103000500803403070303011007140300d880b008181c64000789111184030103c0e8841004600079041007e6010700c40c0c8944141000070300f004c242c040955900500402d4000400807419000f070a102800101078034080030340716011640c4002d1003a00d0008001021440c107103885245890880359130080c01100d012100c03480c0c81d00c0d8000520790112202554041200e00741c410601c9c0052405910142003400000b4112081305000b2000340f0302050342281e40451140700e41c080c803054041c0052a90b000d64003440348032801d5 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 629889865 1250 629888615 629888653
    0x40e063913050d0804090606050405030309130b03030a08041109040f2603040501090c0b030c072d03020304090e150c0d09080d0e01050604051003020108070306080105011202010f0201090302 83
    0x421040703184881c600d41c0d9280400e0403c1ca00140030790b00741300c012a00380180440740c041e2400900840c503100d0304150819001035141d00c16407000c0c078811149010720505440c120707001280c42c003000501ba6910360b400c00d6030185c540101220b0440319546111008031003803903c540c03210f006030f811055280218401303503650000d002c81524000054006202c10803103120201c0000c51280344100d0000c103501500c0d24088000f04503982013448800d00c01e2003044524402c070b07810f955445402c80208200300b60a07031040001c03818080c40300c00100181103204c0052580010050003200d124036010070940d181d1803203468a400351702801c0710b0a030180d2000b0895500e0b0703c401905007864520310005020030307103645049144e03222a01c1216030310344580d54a10b0031002031213159400b03981902e05100750300c0c1071840d1003040d065a000003414040c0801c08078031001e200740e0200d000b40c10b040d00200f0445d611000318040054144104a0001d03001106140e0510b01c113000d01d01c1e0265040d001014070307a071140c2c0e43c403140c = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 629891115 1250 629889865 629889877
    0x11070e16110d0309030e0a0605030c21130b0705040b07030305280c030f0204083a18060c0b0c0f070c0e060a0503150a11040302040e0639 60
    0x4010303141400e41c81e414400d1042d420341075041e40b8000b511111601d006002d40440000103031203140035039820050b680c0c04c842104ea002180d409083d55829085a140180208060642c0003050124081001461424145c42111070003058082100c0e0b4541c042181c4510403402a04006041844a100064001d40189400c00c1c09034000e856200e0007000c80200007100000c0321180c094a44490120180d010722600551180c4600706500c5c05041100d55076882c4984a0041e030300d021030000e5048031207825903030b014090500d86000312010a00c0c100042c00004a80b413180c400080d047c100007519405100340080003030707008a181c00c8940d42e401c00c680301600600c8081218060400a100c00902c0070007a0b08090100b216412030207040c69010f000d000d040343c5c0c0040d400f076404a42e00c1c8580d00e400d4803055612940f512000f049008000345402c0079800303a50700003034206d42040d0300c03d00c2101001c140c031889502e05c02d203421080110340c40c1c0c03140c00c0c0b030a8000c00b11144499200111107990315200400e0 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 629892365 1250 629891115 629891117
    0x30313120c0f0c06090f0b0711190e011a0702010219030509030109060509060604020901050d0c12061d391209030301060e0d020a0b03060d02040612020111070e16 71
    0x74001032103484007803403810150412583c60010b12002d0003003a40080080c0091301c1d0043c8803001300390034103602880350f118800000e8504607000301d20521540d220070070301101ca901c00c0c0c0440036031a9950f0450b10002c1c42030052400d14081503004800d850003200540318000e805034014080c01641d008500c0c0c031660305040c1502041010004007072644c8090040410f132502c01c010004072460720004040c1003003000342405102e1801040182c1507682d014003905c000c0c1204080000360b0504095080d50215103012481c604a41001d100044c0341107003d40c10540300c4184440012140c0c0d0b190311080c0d42c00c0e4400401114010002d003040606036612000150720034801c0c9040381b401c0f0703214081c0036a048040328100b0b01548008018081320f0350002d10003010800c150b4507844400101c0d03000a241c80c909002d0103c91400c04000241e50f0780e01c3c0e01028405580181c01080401c0c2c0f510b55900c0d010700c034011700740d01191a0007102a000c07000040c10208561803c15154420344940e83c1200c001c95402910070 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 629893615 1250 629892365 629892377
    0x4090825050609070501140306010c1407031b0e1005031906020c060a090c06030507080106030c1209030201051509060a120507080f103c060b07060e01060803031312 72
    0x40c00040007000100c1c003414840f0b00802003d40b07807400041911a00c010102081501802803002d84d98000014815042e4000d000070180c98044c0e26251a148940c0d20141500d00c1d5010000051080003840000396249148480c03216610701c00400501c3c071851142070b4140c1c1c820400b6010301d120b140d0707040d03800621503135014aca451840043c0500d04001070702c8000b54640e8038941c49040104004040000f841c0c2e43c1424401894903050141c0510814814a4181a01d42803145001071080c045804501403240c401c201f0b904031420002d00130300d82200e28041504c03800c07025454611f0442071682c452078004101030402800c001a9101c00800703240120b9891081d610003103001d0f081071104d5031101850000800d21083c0001c07800f400d440002100b015100000440a00700030300490005650352003000561185504081c1554020002c9a0004c1c0c100400440c1c2074007004802d400c900c00c0483c08034005d104098642017000d032640301c281d80000380741d00d070502e04000041d00c1401d12285804d680c1440 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 629894865 1250 629893615 629893687
    0x20108100504110c010e0a200d0602070606060e011407020d0c15030905010b0406030f14030408030d020301080d09050d0308060a0e040f020301050f01080c130204120c0311040908 78
    0xb080c2a80d00f01c1000c040c590802080c1e41403c40c400740704203900502102c008181e4500e1f40c2d150b01c6610090001550100c0295034602c0da42c60311a0144034902c5540304008540da8405403e14100400c2030740640b400140031526800300640c42008101c0002e00401600c40c83c156140e030130066400d2081c2d0003102d59014150300090252000311a0301c51103d500d40f00403d03402c5041c60500c2c00c4404084119201f40c0c5045414004214800303203894881e80d01446842000021400c1c80e4951b00407640000c405200004850f204414250051812a070f03051044030032204501c01c09407541c46513400b030544c205540103e0040420320503410141c2098000e00741d451281d8445e800007064180c109c038142d500050340207950003142024403541d0f034881c00c1c00d01c5004055050005c615210301e842000d182c864401a860114082d109a0444004150700c6102c400b040703100d0b18054442c64206c0c0f00985441c0d140d40b016a41c68107082c0114403200e6402603005240503600e04004800800019507a8001ca10b032400c0 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 629896115 1250 629894865 629894869
    0x12150302060a0c0b1e0c1e0301170f060403020c190801140711061b07030201020904091a090309010e1302211f0b0a08040f12170609060d0201081005 65
    0x7850007070b0340d9a90b61003000200e82040305074124041c0081920318100a400c8000c1a070358000aa044900d142900c1d6407a812080501e05c1e803183c42d0354205610100000010722403405209229600040c4001d603500360000401c61a200d0b44110b501602580015010b42e40f146421520903000172120324003401941c0d1a24a100c0c00c507a207441c0440d052b01c0c90072041c08262500030004c41c0040c0d46c80401405549050b40804044d4100308800c9180302c14040f5000d0b0805000390161221000080c0003080310b0075079410301c041401ca40c80000c10440204401213000c424000c4204c07082c00380d040c0c5460025000c0355007403115249000094940ca03d6090111110341c181c0000c810001940540300e001d0b01e42800220055910114080c030302c2400014070040000080d64010f403540b410003414840c11540d50340c00c012410036000030004003c4a06207406035a0150050700250080354485200052a51a9418020a00010303600541e108411540100c0103610030800c56501092907030019110b560703104c1c0 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 629897365 1250 629896115 629896117
    0x60301120309170d030b030c0307091a150306040c1b030804020d1e060f06031509170313050c04180b070e040f020c0f0a15020a02150403030911060405011215030206 72
    0x7401c4a240d4002090a0035800e5250083e001c9440f001c40107000303483c1c80301c0000f0f540c9800072f1040c0041541c0b01d6051500c040056001c614548101600044440d9024041000301b41e00442c2c071907203e5441c014140c55220f1103010542049002c0000b45d01403100c0f1500c095400d294014402c076804108001000b0004091600340440c0074140d1605004c41411407515074140c81500401c0300520345004820008111800d80c4020303c2c2070076180009900e00c05090003078030143c00440c0601610400806c2c02408419032061a9025014030305462590104008100503900340001c000d00321082c1c81c51041c0404d0381c1c101210b401210600b060b0083d40010340200d8181d40c1044120941c203176001c6003018001c44180072860800da0341c41c014001c0d51113140d40c0c00001d001c1d0303c1040147c0340e601086150f100c5000f0003052427991a202c1828940e45014039008001d00340e103020882e03000303400542e0600c250034103006a40c10303588141c641a490103101900e900007801c1800c88180450901c010020240e19040 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 629898615 1250 629897365 629897399
    0xc0601090513032d0224070929030f010e100b2b0c17090601060203030711010b040f1a0d210c0206030a05090d080103031e0210050a0c030f0902060301120309 69
    0x80c010307190303030080d1852040f074811148880c0c6e011201c156080001841e4021001c0c02a00d485210300f070f00e680842034440d605c03605c20942080c6000c4000043c805040c1c4e000b0209070494240c035004102ca66202045400742108610440c0f2020006100c100245412200488140b11410318840001c01000d85441d0036600081a61804540901000c241c501803c240d2654044600c00042055500d4050000e5480c840108854204003424007408490318007034110090710600240148003019a81c0713405002484069242d02442d002c0003401030b001e0500e1858030104541040c0c100c0c0004c0c0c004500d007104c03040c4a0a54000700910030b0365100060b030701c00007d580200d41742000010b0138075010484030302e0022511911014418158010800030398400a10741c095150110000001510300006900c1c04190185216809003800104071f03640b5115809440d895404d0760b024006c45a500180300219091090301a4000c1410030050204121150003105440c3c440d24140ca49981c0e07030070302204160501 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 629899865 1250 629898615 629898617
    0xd03020d0209300c0916170a050105010f080601020c1c0f11090108070308191e02011a0f010c110607021509030606060a0f140f040b0c0601090513032d 66
    0x200c04105100340f940b6100702850001e40c0010030707440c84c0c1070f800282c260f00c0050000c3c01d00c143c1c0c4129407846130300c0782103c00407a41069502c01903a0400d01d10703882c003601013401042d00081c10480702c0d0307000611880314140a2001a00904000d01030f0f0030500c401040c1145c0c1d40c8640d4813214030184c0005100b940c400c840107014040a90030392020f1801c000e000703030341a4080080e0758003840090000c162803600f02d521000c1c50441d03464914a10020648034001551456014187d001ca4065003003a01034000c008090741c0307a8400e4581c09414000c0002030004450480d0002d401c040c582400107000402e2440d80c840001c00c10303410310710250f00003900e17000040c0e0103051402c0c02045108250808001d6290030000841d1007500f4900c0c1600000c242da040c82c2c0c00f03001001401114640348000ea0380c03c66110307524503451103550702e444441180e855849510741c581d1034820300d4000106624580710f441c1c0180d44594204400f1030380781d1400c50350048030000300019a202890007445070401e21159103564146 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 629901115 1250 629899865 629899909
    0x80901320d0e150a020d1413051606050906071406010f09060501080417130b0f13050d0203071503020f191e0219030c060c09180e0d03020d0209 63
    0x91000008103aa030840b02c2004030b6845551a0486525090f0180b03611500034840141c0b5000660080000750088612088601d00540d040c440450026203100d180e0714000d40441c2c1c0e041010801c015031040301840b480000502c20f101c280014a8003000032b09440e03009800041403500c502d0f01c0c00382000c5080c0c4c04101d04510024003001445464000e0100900003400c1c208103628180d03e450a810b15054103610154400007100c0c00e408001c0c6029034060440b008180b0303201c1003040e807102595804818076400c4ca200c003202c001040e01c0e046001c030086075406400340040a1800e00003a42a41e01d0426040515800303020844495404001516150694403c41f17882c60450804c040e0155078105801c80c2c03606240f05401e0310a540000d04000402c0c0b0004c002c413450001c9050413666004815002042d950400300d21151165100040a094411403080030309001042c000c00700c100c40c4048111113107500003115540c0086d010364040c4c115104412009890592040005088045050401c04426074 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 629902365 1250 629901115 629901127
    0x3120503090f010e06010306021b0f0309010e090126031b1501050301090c031106040801050a020903072405030a090203010e061501090b091017101a030408090132 71
    0x8801c21041e4a0004000c00070800010244101030b19403805000c003400545d0005091514042b04c90100c010340b440510aa80303040407031180c044e88a40c0b080341020f000034442c6140d2440b625146d6080c3d4122081c2000010407010f03a28035007017a1301c9442000111501040c400b41c03e5580f40d6002d012468400040502a44481c568059000d0201a0082400b031380c9010f8603040018803180e94401600d030032010400002610a0014a481c403864220304061750900c824445140c24980240c0b6000b10214107540b0f0039a190b062011000c081d01641603941c100c80103596081d14000c0c00115001b02c0c1c61312020524040c6600402e0a44d242d090400c4040d500c050304100d500d1140c503800e0001008240f829140c001d24200e0400d09134007924070458480e00340c0301c4201314541c0c0119a02c004800304029078100525000c0c41c4103003c1d404500c10000d1180e400510906a2641402240e04c07803030740a00c0c3c903030824501a0044031902c40380e52002e45402d0410790307080c8c3c0000c408c0442004130020b40703903410381d0390b8 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 629903615 1250 629902365 629902381
    0xa080609040317070906080c19031116061a0f060313030e0a060215010e1003030e0307030b2a03070c11030c090a1a030721031b08040e090a02010801050d050703120503 73
    0x103480204410b800788d906000c1d88025501740864009191903501e4082681403c0030041c3c001403240b485250b0307039081c283d61210204111a0040104810110105548040e440c01800000311004005035801082003000402d1b00c0319640c11803000d280249000120b4a5810b0b01240720300c03006400040c0560b12a065082d0400c00e074510f020b000d041c40341d910501d3707428514251440011700703000080900c401c4809110442d2010401000290b8100304402c2280c14441c2c0c4400c00050b40c0000786900d03043d07403940240c1c4e46040380d003242d000c1c000641e40c0b881c4d0400d5903280d000902c000400156070500401030b10155a03075403a200c003402002c09803000a080122152218002644404054001d80202c401006151038034550b0a81c3c2da01c03007030580420410f15103001c0b41c1d03914415000c40c0070311400a203130106001500002c0d2059504070458104561124003c0990300c10711020001d0014003040014051414000074030003915114100b1128003075229a50b50251a5030207001e54005a4044100040b003 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 629904865 1250 629903615 629903627
    0x10c080603060a06082d01060303051201060e01170a02070210090609060c02300d0504050418151e0501092a0e0f01090e2a0a080609040317070906 64
    0x2c0311202d1420059940b80117000354940302c40280401c0d009034071a004000c0b180c0c020002c0903048200c00c000b0820702c1d44074038010303019401c010709a041e400fa80900105240b40242030b03002803003030140c541001e4008110038401c200366004203c04020f5400713100020050302c40a41f9129001c0d40d5880e00c118079420244010040e070321a43c008030401c68030442007005038682c10b90001c1c242210860349603054090035a0f107440d42d00d50324103d043c28880d03801c24036151a48040074105951003247d0a10a03003080198031640b98540320409032856081122103110a025030b4848640411209102121150001000022160300741e1100700b40031349075850792461001401c8204d07141d208100c00600120b240940003400c40d09a008041d010301044600004281e02580b0100c0051010f0007030900305140120041d95401d1010142e5884100d14250282c030030341c504000d80f00ba40510743d8a1040595a0300104034124002410035000c0c0120340301405114803081407454452440c9807510805d96280010003000 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 629906115 1250 629904865 629904871
    0x1020a0c26070602030603160305010e210a0e01091a0405040b0301180b1504050403030b01030b120309091902031006080702060412180b130311041401030212070305010c08060306 78
    0xa80d600d080c030010404001c24261500c480d005a00161290340ba803000c42c4c60301503130440055107002640e01c0002081815000340d41c81c54a14815a40401c0a9004c0020507030f00108040e0b151550a0040300c440c1849040305440144052401c608802d6035034201c0f0000701c0d1119072044a1403c0000d080c001400c00c0e0003181001c1006a00800034410500c2080789500101000100b81d583c604001c0349102c402d41d03d0b65119604010420440c030b00b080c1c039000d40100050340c40f007400729007800c12450061900340d100c1c3d1003280b41080610303c1c1c00c964000b008840300000300301100300140700700101c024a46501c0a1072040c150801c03d642c16030309112002e030135484002d09580c01c5500c01c404000000e10340000c11030845d0316500380dc00100c01c0c0d0354000030740113566800c205540b00001c03911107040c200e20350382c5404890003908114100d003640424071082d14581d196030300e07179021880010030050510740b81021201449909403480c160310307a5525401e4480114500340020751040030702100389010302071950 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 629907365 1250 629906115 629906153
    0xa02070e011e12020a050d03020120090324010b0a090b04060507020102120421020303071b15111e03070501060e060108150d080a0203041e03060c0207080604080a05090301020a0c 78
    0x81c0103000c50380010417568003402014042c1d8400800c0c501014000d4200b1b41c5035928196a503090082200003684c15500000c4506200744243d80c02000740d403881c0712003083c8001d10b101c1011042c1e8200001694264400c0c2e04407410408820000103200b85820081c0014150380d940f5680d41c0d024a0000a01e0031005121100140308100801c11099806c00d00c80c40207161a101490603000071800024158013401d2809401c0c0e080d142e18108002c06480b000c1300503684952400700c081c40a1850445943d00b020794607a0455000c015210b05801c48010401544602c01003101d05c1c1061540d01c1c5070031b4540039444a4088143c07281844404d40c0c21101040e440301002c100440b2081c2180d0002c1c2e10f1501442c80605424000901d82c0342191080c4215000780409125001c81c6007540c0308082c440a0041c03100380c1d0032510300b40070003a0007407011810004841c0d14400900c40d68039251641c46459100040c0d14050120030080d20400c1d440c20b00181808842039100c02c804050142886810303e060391418803 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 629908615 1250 629907365 629907389
    0x4031511030c0403020d020a05041b020601090902090f1807090213090c050706050c0903030703020c041107120f0314240402090303070f020406050904050d0f0309170a02070e011e 78
    0x1021800500043d0380449404480103000140240040350442c4142c0d0025900b0508242112219198040660030915020f1742243c1c00c90381e80740180011203c1d1080b000303503c503441c45c001c5007094005a020350b400012070304000c4804c01400845e5450300b0020b52024100e180c0108141c3d0380d100b0401117007401002007000510103000318510042c151f01c15100010449075440b004a18419410029102141c1c4080c013241d5680100d414041d550342031494149108604000c6079007407a180540607106100d030b0004511005016200e405e0356040d030160120810980da40f0005a0050703401c110485c00b0303c941500c0c1c90700c10322090080c564221032100722036000e24010030140b80d50381c07000401c50b0443c070380040d000e032181c0d2050310016010700115400540c1c44072000080c4011710202045180018601c0e4030b60309040c07101c22500b0b0f030981e01c5005020308030048005d1131014a9010100400c821211441580c0240707842d59600500800280c01c081411210464a2121a544240e00c4806807000c104c8803 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 629909865 1250 629908615 629908621
    0x4021b01060b04030f030809282a03080a0203130905010302120604050d050702030f060103082a06040314070b1f2909011e031401120201020604110d080403151103 71
    0x140444d8004108020100301607c4000340740c1034014802c2c4241ea400e0740714811600244086140154448103805541c0da0040d000003c106008080d520542d0086442c1c4824142e881c54a0f00c0406802c00084541540801c020350004005820b00b00c2020344143c550000c0e0f03e504500510414107189203503610759038400411300c0041000060380e08200c0c8a24540940e5803030003407010034184000090038040e1481100008410846d0b220090b010340601600c40b40421034001900601c104010084051182c10040c0403d021900c03c0d0040b800303d42803254024584621551466100702c41140c02104603071003040e0b1083c80c084201d10000080400149103054031070003080c0442c1042c481007100d040f0802c009520a1183d014280602000300c010204851805d811304014016001800e00b4450101206002050f00e00e031800840400e40d0b010b038010031035607540d0f07500c0e071030034003a0b0b6100e882e03002200c000400c002450090040024500c01c20103112845915801282900c654103114401d203d014020 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 629911115 1250 629909865 629909873
    0xb09011a010c0b0a0b030c18091213031104090506070f0f020705090105120a050601060302070201090603140708040503091011070e06060a210507030e0f0c06120c040504021b01060b0403 81
    0x844e40101e80c100000809900030000285400c19503050b05401c424a40083c14840c4c0706460001d00c21203800043c5e4041106000d440090b82c42502d07116580c04580e0b20090010405e2102c0c0c074203a40302c0240c00003410054644800749030040450300c0d04d001501c0501d082c1030303030b84c1d00940700403500d407240c001003407528107000000d910400305014660003442da0041a41c6066010004590b1440e00042901c0c16941c4802004000e940f1040e02603011031804100010031a12034403840c131105520320120001500e40c410b00b00c40303144010f4030030b40d40c500c803d01c40d00c1080e0340d03203140c980e00a400645484e0b018040c040e41c11828484c241d0b211708540340807041000099111181268948925481e00d0441d0384051600150515040002103084600d4502004100317501648072131400991b01c4211b5100f003c0c0900301d00d50311040c504215030000350600541000d507030300140041d08110380498050504c0e441c0c0d008038040347c0201428000c18800d0401d0300c1e040c20420b1091501030b1000202d028905030854403 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 629912365 1250 629911115 629911133
    0x1020703061b020c0f15180604030f0b060105030c04060309020a030602130501080901090309060507140a0b06090a0507020316020d02060d05190e0d0f020109050a08030106021b0f0613030b09011a010c 87
    0x7200c0407058000651f41e00c030706546542400c09114024481621075450b800d10380402c1d82c00880c00c84907030946801040207580114107503481441e030481541c4c645410080300310b0140c0b5003008100d1b08a0128080440021140d00180240c4500185280d9a003440c0800051101d00d02900c184a20303403410349102c0101c0d48c092805010340d191303403c0850303441c0e04529000c40080b07030005850199001c2d804d526020441c42a10b800d00901003150808225115222494115241500e020026a0040011051000f1900d1084040b00c1c00100056003039659500403a00c65445806108003403580c500807c48482e810a14001a04c8242c00301007200312a80306100d50f5a60340c0540e503006003c0b8102e50043c9841c401d4000205070760384903003610700c40d01440c90400002c2e0030a00410016004404001c42c040000301c0e40c90348448801000d081c1e40d80540c03000d000041e4410482940105120000400841d1056025138020007404000290300703403441d1000741805201080a07410000f10480060224003c15 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 629913615 1250 629912365 629912389
    0x50106230d112205130209060603090a17070605010803250c14150d0c020d02010c050301090e1e030405010f0311221e0306050606070305030c030601020703061b020c0f 73
    0x3036101d00c2c50f4110700c0310000c000040c8001c0542900d040c801040603500c200700c4e09410b00c51003950780704035a03242c2e613007001079070300040b1101c0c0c01d5503101200031004158030f00e10680c1c0c0c01c1800400d05147c003615466010507a2801d81010000781e000180000442e030707550070345461401c0c16801c13000264540d80c0d00e41210002c0791203030002035040759a955085903904d54000c00260003e020303480c0e5420301c404000c00a0410110484098001d0f5190100d600f8010300550724401a103550380c1e80355a0a002c12000245100c074200805842031791000088a008411410a04c0d981880116200e030301e860b0005040300d1503a4403010401d41000d0740c0e841500d56075010380c0d07070455001c009a14040203d000c0180c1c185240e90001d0148131014881c6100300c40340b5503c040c10390b8001c64042c800d80c0c0d07030002440b5940c8180c0400600148007000025100901c003409103030420014410390320f8070744e41c80d101d120994900080740100d00720494140a12103404001d51060b94078184d0f1542150307160540040d825210384 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 629914865 1250 629913615 629913619
    0x109050403080c09061c0b011101110901030915060608011802091c240b030c03070e070503090f0303070306080c04361a01050a061815020a050106230d11 67
    0x4924102142e1702d01701500c103244510351030103001c3c490420851000d0142446030302e003c1842d212412071040f0041c0a2101221a2078144502c0c0c50400c0004400801c03400e002551109607134005600000c1440c0240c80081459941c0c00d80254103110300c1c0000448921a003641c003900c10460b0706050b8607030150700c201d10040041c07008004045428441d12410400320000c003a01e0118040100e051042c1e8858248103600350103c60b201c215403805d259541545015034220f8442800000e00e40b00e02c40e100940d07001e4440c20694000c0002041c0940c5107400645003500440d40750314061000742402c006403003440400310740030f00100d6624900b06d050f00100481b40481803458010318184402c1e051482c0390003903480003035600e84e51038401c1c60380c950b040c081c041c20788030f5a10403d000034068071800c0744140c038405210541103a28509034514408410b88541c440650040c0d40115002c02d60a200d800d00515080006d05401c1c6000e206c504110070340f040c4081c0c032410080c0210404a18030146a824004003 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 629916115 1250 629914865 629914867
    0x6061707021f0507200604020402071b0e0f060f01080415060b1c05130b222901050102070305071e1823010b030601031d240109050403080c 61
    0x25410201d0622440d00c5003440007070282031295081015aa003c03e1180d0050750b1042c011000c1010081c94600300c4842c145510b034465030108000d864503a0007403410922500c035a80b0fa041400440792461021a8031101e081c2d40d0310800c200c0101050780c404e617808803040b40c015082c5010140040d014901c058070181502210104401c00d00c0740e103507c8607001e40a0083c030140c8034040b21148074034004020342c011030704909042c0843c1020070151500c20340a9441541904c4c0c541d00d842c024009404010300d0b02d0101104030410201282650000c0c0b0b8001050390301e9030402201c450404009220103030702a82c11940f080d10200302246000c113440e8151303551040b81c4003484503942c4944100300d941d038001c00800141c540508245039144e600c1a0305401000821485001c4611940540e5400901c00d004c5240c1c01000010046d40c13290b8090b5001100355102c40350498481c4194074949140580d18014a00702c110140702421000c1600c0350041035074600500c028a083e42e0010007154001c2d03e00e41c0c00d020 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 629917365 1250 629916115 629916121
    0x12070c060b0a030b0915010f0b0d060f14040b06090f0d111005030f0c040b09090702070f08070503010f0c051e220e0603070e060114070c030804030312060617 69
    0x11290300016681e900040041c181c2c0d5840381845003483c0c4040d01c0e0704e6401c1c46a0320554601188515907141290204007042403c5890842400565402101405281660f4000104001800709107200140c04502150f0b100100c1b0103083c4022220844402c0d482100e0a0000710340c00d41d540994240110b20546100d04200c0795840c21007224048c07822100c2c0c0c01449034070819440d90307001c1e0182d031084003038007002c59850700c1e2500024024484c5004010810504101404040c18008910348e0450007a00c100c0d00744035030b00c60f0650106421504903034145c1c0c000d02410082850b090080da55104544501040252003040024000d4490614002a80d40414460060b16650601a00c88810780b13460401007045101c419000341c082d180c09403040800554003c50703401e040000362402594100d4503d422207813541c0c401540c00d0345030fa00d852280080e08005850001c1c80b50300450f8006c5114901c204d84941c114034018082900c500020004240f602004002d003540c00046602c460f00502d8514003951 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 629918615 1250 629917365 629917373
    0x60c08040231140601090905070c02060f13080706112802010903080c010c08090f0a1407050607060501060f111b0d050307050f0609011e0b0303190207140612070c 71
    0x745288a1211050340b038901604410841040360612492090340c46c45500d50301d9845040c100c3e8010b495070000160000390f4000182401d6006160302860307480828280240915464010039a9070414001500001403c22019810400a450790010600904210405001241200c0c0f0400c1030207042c0d21404aa24015640070354802009103411400785640c92800c102c16034064041d41c0174072000215800300040d42d01001107003081405aa000113401188056142d00f6034903a51901d241c24140034200002459079034a40040c03203480d21900021409600d045005010f1701e1900c0303919002e00c1340d02e100002d81c1540104124156102c4031604440c07186400d004500030891054004101780300000305d04051000c0004e090b08422044822a19540e545080b03d900303170340012240041c2c00144181604040700250454002098050100d0742040418901802c0a4920b4410500581c000710700c14072858019010894201a0075140546002508458a210780d40000d155100f00102d4482c000200 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 629919865 1250 629918615 629918689
    0x32c1c1b061d1804140d0f050a12110a110d020c1011030904050109020c07060f360e190c0801061b02060c0c09060a0503190804030501021303060c080402 67
    0x182040810f00b081da4502860600d26454488408205a20800b003006440e580704000c1403400315569902d090a046000f401618010740c80e0712501d0500f42c40c0d00f28901c0c1d0102c0c07000640140307075541d130300c0400e103e480b401510708100014024004540008104c040b80c1e4403540c5044850003201d1404c440c9400f4240f152034214000c180e00075501c58149400025080c442e60090302c00036a1080a07036140c2c50361402c05444903d041c00180010a5103440e06c03260389049023419040125090403034040c01d0300c0340f080c05010520190403a50080d00748206101c2c0310000021400380c02c1c1d240c0d40081000010080c409458540144105010072908082e51015162030b021188030041d4040c005030384900c00300c40800d0f101c88a801d11903000b440350000080301841c0050703485044400c0a40030b04208128080d100c011721002e0340c016262510200400400100c0900c0104205164503160303000c903904610702031064074040c5c5075003820810540280405030707458201384003030024000400101c440705019040b0b00303 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 629921115 1250 629919865 629919889
    0x30c0c0b030a0c030b010806010e0d030c02030604081e09010507230a12020c0d0209010e06011404090605090a0213090509100911150403032c1c1b061d 66
    0x2440000320500c00b0015558110181d81c0e406501c003400200d003880c004480d034690440303020340011903850785140c89080c0b40540c8500c05010b46000c20b42c3e04c0140d0042031070600c0664040f00c0103080003540d00300c80c7e4040464680300c410701031100da142081e41030000f4210302542c04098a405400b070000083c82c0d5001070361500b244015816602d841e00703135041c2844541084000c0c0b40141c0501e50310030090f4604054403008103a4002e00e440011390a0504800000b08010802414400c040010b00e00c10314031000600010030070800c002c0b43c00c904040a000d100b51703026202030000c90040c0004410500d0103c0948103640450100041c540c4d514000c00d480c000540c07001540d2a80b60102c441c06019210b039001c82c12120179144030b40c20035021551100d80c0d100c0c07840040d00041c10700403041d602495044c030419200d0302824100d11203034058400100e4880180102503229041843d402d02000a032480b140e003049000403421a0076403401a0203440d51791908148480440b4030202100b02d50703100001ca0078 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 629922365 1250 629921115 629921129
    0x40305070605250f1107050a0b030a0b060f0d18030f08040c121b06050403051b04110c0109060b01050307020718092312040f03020d020a0b0d0f05060a060c030c0c 71
    0x5100c51800006080d031030084c0d000c030002417040d2034651907100002030000e0481d10040d04542e0b4103403802800103156000540884001d030f40340d0076a1602d03940e600e40070381245a0b4442185580728128000b100840b144e03240c00c511314282080582d0301084e00818040001341583c20700c040e29644510307104221600c90382102048035404082103060042c44211810f21040d014800c10507180c8400003616103000c0c902c0020f282d136014200300d0b83c000043c403401c05031500006d840031481103c0040c05c1540f0342c2040003650210b0f9501c540580511515010b10b100880007820107524506181600035112461405075040d60082c150380020310004c60341c0501080364108074030302050740160600515030b03d1081d5a0242d40c0c0b0502e0340207a4101521400c440c125898400c1d125010313032a544c203000000781c3c03074002643c0c811030748803000403101c82c0180100707514600013000103010403110581100f21030010b4400c9014000090041c80419040428104200c0d054108560807050303d2500d0103c2c15080d030441c038 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 629923615 1250 629922365 629922421
    0x7021f0c02090c070b0c0c070b070b060316032006070c080606032407030507020c09010303020718050105060417250609060206091c03091a041a040305070605 69
    0x110903a8414150840da034030845001c88540c8402e60080d80718001c807007000c5e0556480801195a4000150091480c29140010b40b0150b5550700103561640c0c2000a003038414904050801000f8a400c0c402a24001c0440c25007004803406d680707814100751b07000500804004039082140c1c88654469040d02d80c85a8082461500e1a0300d441e0b0058a0b00d5041c1ca03040d010744100f90360220141c1003050786a030544120303508440b6540e2400b00c1103014143c0a40000254000d21403030f1103603511007207916806540284c00600d100c61400901182c0b12400703144041d0307410314050052040340d0761031044504a41009510031207248180b001d882c10b09c041d01d071080e07175103018203d2105c2d10441c041c446007040340c101c0d032200c000b07044c4d0f00d40080e030b140d00c412203c0c50300d02d0b000650144070040703080c505000728082c20320b400207128403503546840c5071100c80350125918004c44801c0000f002001500103034100d1155402c01100c0c00c255a001c0d090780900d2000602c0e0755125030000e14050300c0380c140028640010381d944 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 629924865 1250 629923615 629923669
    0x616020915010306050612161103030f060108012315130303030501150507020d0b0a060b0a0e03010c09030506012306040e0709090501120213020408070b120f15060702 73
    0x29403107aa0200500601003400e180d40065203103400070555070303100d41e511520345161380c501c503820001440840c100005d0046034401041c0c010400c1024500c0380303058000400050500c200050041c140591240903e4041c5807401c011601c0820701090110400360f9030036607102e0070100f1481c3c040c083e8201d801600f4244540000515034103400060480c0c690b100c0b8601e103e030151504580074403940c0e001a400c6070007082c541001072100b51950707500c18a900300000f0344a8943c009078034640d01205203100010459601720217185402c2c450342c80011050300b4081549407445d80e0b00ca85642d0148501505405040792858182c80001c03100082c2c4500105415921910752860804021080e42c0c031350b0020300100c8000c900e501c241e03c280d906a4081a20212141c43c1d1a070800c411a030804180c030801ca9001d10000401682c00c000b09005405000d09480e1286041001c502007030100800c491080c261071001d00c8090b4841c5400341684090039102c590780c03404c0c0d9001040000001c00c0400b00c10850384511 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 629926115 1250 629924865 629924881
    0x7082d0a120e0d081014150d09150c17070206010b0a090f0e01210819030f0608070e1e0105060a051c0e010b0a030206030f0402030a0f12270506160209 66
    0x2194802d0090f00303144017034135448000c14190a0b400c0061550402c003041826502213450301c01070100d80070981808140401a555040e0003040038140b5029505e8440c1d0845000300cbd040b407171040a00e04100e2035407490389040103000b03569407410301ca1015000c800261204102c2d02c80ca18500c0604a950003c00c84159100c10709110b440091040c1c40c0741d04508503480303001000038401240000c2c0c0221809062001c40e00c0540c000c4148000c1031818190b64491102c0c4810031406550000c14000c0f002c0d100b41c91070901640c50640d001803201a030a4000e0100e001001d0100401030305481c016a00e640e01d581305420240d41034419414001d0064801c030060800030055134019266540300400240104e820310000d0000c039140c1808002c0d803141c814000922110006100380364403d00060440342000e00b00e0b21016200c450712a41958000398400301c01c480743c0c0c6c01040d40680301844101c441e0440c22500c440c150180418050710344a902c0009082840c107495a0507401c003030790014a55402030070680b003 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 629927365 1250 629926115 629926127
    0x8011103062b05070f090b061309050705070b011d0702030a080103081c0e0c01020d0f020705060d090b1e0f090a03030903110f031c05040206160c030807082d0a120e0d 73
    0x1080c1d0480d47e04201d01380c80343d4104030702942d034000380f440c8020441c40d041c08854400760034001c01039802c2100a008200110303402101c800d00a00c8003903008040b802544031400c05070b40340185610705550041160140c0964020a41811650031140e406d454007614006002e5107440920344500c1213040c413000b4082288041805010f0100903001c0700e00c06c41c180c040a907290f554001c3c010000d600300354000c00590420800600740c00032442c600042da4510f07552440d1030180150752001150448040125070318808038a201d8000000310b602e400c081ca02030390810750741c41000000800300340e02d4a51013010035004091140040e801c0005070355110400e5070326180e59400c407800040524a1401d40100c2042c01480707aa405150041e04062034040c0c0c040b03100703100070176402049461540800b03000012808510280140e0b51241e40526035404d8910040c40c007040b58800c0d1003d43e401c625001d003c02c002c04a0850f1100301c004d050030803001845403401070080a014460250500403036101c0e281c40c6501031 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 629928615 1250 629927365 629927369
    0x602070605041103070e010b0409050402030118030225051302090102070806011203080c0906190e030d090302031b060d0c02120a0f0813030f0e13060f08011103062b05070f 75
    0x24040305d541d41e56860008400c07400a1040c0e148080003000f040c00a039145400083d480750000d800460b045480503404207003e2000780003603006800a04840390909440ca82403440455086010441e03541000c001461410700745880101b540c0d8001055541c5034024480e000007091404284c40007981e480720aa88045039101d001c9000034250070000c0c07410007034441a5680060050412828200342442d02d031417502c54825030005025080340383d2900c9607020040015020203903a00d48003810309d940f05240c41c08521104c0a05141200c4d2040741c1d180d203030704060b40c8074140d40450110300d21001410a90410701019048215220002080352001c0d8204003a580341c20460b40e00c2c41100d030b441c7e24009020b852a25001000604440790b44545103200e0000c0e158800e000604819160078045d5200b0200d408c990b0145441040e00701e02000094020710403006001c00d40740d1990714601e4800009001145015461072199101013034030b44040000c00103a440095001048583e0513407130380010103808505d4 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 629929865 1250 629928615 629928619
    0x1f08060114030f0601051605010608010b120f0a060b040603080d05061207060801091d0d12060f050f0607050f030c0115060e06070321110c012706050406020706050411 73
    0x100480e00c104407004202c0c0d10940c0c40b003101801c5500e40c94011a61030740600d800e00c003901310000d01200880ca0a22038038000f800401c0000035007100c0071041c4180388048291000e0140c0010003503120807603001c0b6400c00141c0d030104000400e4154240000c0040403140c0000d44601004280864001000c0d070250340507003c12142200ca169690304450360303074820b83c040c5c2d8000900c00c3c40100710390f004035000140f5403415150305055084c1d0b8107e06030f01d45400d0071102000141c402590b0f030440049403003014080c00e403040d0415a09400e10001c1104280250341d920300442c0005520000e2040a1140010407005d44044d43d642d01700090741e003806000f0385440118042c1c1c00e4200020101c0c000c01ca00d10411101030182c60a1210640301a6100103c20502002d074030b200400c080d87c0c20f201c521800c1c01103060f0307800e42c9403903078052074120b82103c00e414400310b4040b50006080e98904d500c0940b80c4c3e4600d0f44168049000d58440c50032501070302070004000e250700d00708810300041045420040b6a00242 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 629931115 1250 629929865 629929877
    0x121b1f0309060b0301020a0f4b09080307080c0703060501060c11060901080a182405101406030903160b0123100309081b03030f0703060b030601030b1f080601 69
    0xf004101800c0340b080690040109203a01c1c05140068061030010000d000d9404001001078480314030004102d82000700b50030041d07100c01191320a00e0f81614803c164032102d02c0c00341c42190070701041c00d603a4030501c0130281240c11301150304041c940c010020303440a194003500a00165030342c1d5070007400081c041ca508580e2a00b40c800c0301401e42c2050b00a460305032005944480c07098a0383ea0850004105440030150070449d01031b8034a02082400d680c0c4100903a10201c507441c107030440c5065030700700c030340c060030320322414820180801c0800910030203008284c10440c1c20f181e480c2c1b031302000b15180d40319071032050701a20459a010701c00e215110012070b0480c0d0200880e0000c800c0c8a2510000201000c0d40302580144140840c0507001c2c4a44d110341030543c880c01500d85012030a84c01c10721022103440e1600b01a601c00401c200300b440012101300e400c9522030070203000320303414000382c41180c0c0030003043ca03410035603560303554141d076034810400900300b1040e010310400500c40368200030020b10782142d115001c921 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 629932365 1250 629931115 629931131
    0x303070f05070f0605041a0f190603150510080a030201150b0313120516050a020102190b0a1a132405060706021b0303090a0b06121b1f030906 62
    0x10050040342e100c654449070000c15250380d550313042c009105c040c00540c1e80c6081e96590124203000191800d01440d9480042040c601c2c295891104801c2251070301110a03042a20400c002921036070360000304e42005030041582c0ea50030f01688001d00b030340d52149e40e50b0b01c220503d207001e06806511a0440e0049090312110454880050b003180d44815501482c419000451642c0410180c8442203100300d000d10746035140840e4104803659008207104281c07070039004001604110368041001041c41200c00348802d100100d582c90707116100d0030060402c26440c0c0c403020885200b03c1d45a40f94040114002c0492480450007400c2e90010150354400001c5510a00d011030501d42d0000071190071101c00410003072501c00709590340c0d806500b11484883c8814030b5651405205031050016610a04210000304118203d90030045202075014081078003c100018405500f5170700425031041658071078400b0440072440740302007040c141d01c8151401c0c01d8403e050410042e41d03495048040e070a0701401d0b003440040 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 629933615 1250 629932365 629932367
    0x150102011803050403020a140d02040b0f061809070201051605030402010212160506090303090304210c03150f050601080612070302031f060b04140d08070f0b011e0e0117011d0303070f 80
    0x108c0c0b01124550101840d5442c9006240c550840e100080c000f43c5140d205507800800309020f40c1184825500c80c2040100768103d030309040032480d40c80746440c4000d102c04e00341b002407801c035030400c2c080c007030204440040064103590013041206c43c042d0036500000d54507243c0c0525140c850118040440c1c0130b0181c01e0210f07000280000550340209a0100a5890103141007425880214510000f06442102c00d0300c040228141c0da903042c1c02140200034400e05d980ca01c02c40141129910100100b1141c9003000303000199901000d9264080010703624420361700741c00d9054030701d042000e5200941c07500c646406401542c46208581114141c800d030140003460b21007181020a0140d07000d50030110300c00c482c0c108605c0c03800c882c481100d0f40c0100c40a900e03101c12511046141003c40000741e071918410001001200f000740c500306040e504103420003808500b000d150b40c0c14080c040c82504c0103203401160100d00013000b135003c501054002400082d80003280c015143c4c403030708210381200100e012122400019 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 629934865 1250 629933615 629933639
    0x70b03010e15010914011d0607081308030307091a1605160803070b070f050c0a050703022718011409070609050d030e0105030721090c05030d0206150102011803050403020a 75
    0xe10610380c640001c1c804504011100c035030b0080c001f06005102880015440c0c5c41c0c0134010002d45000c1c00800740e80b000c020040524104065000c003800c0e85c402c004010420f0f50004400042d6988612110044403d05040d92218001e840100c0340480c620702c0844204032001646a040b514244031000c2c0556444130b0aa031640980300000e0014443c1000280c1203e104545c4116512618282942007120b40385c00c00707241c14440d20b41140c880d48580c2c0b081c415481c104103a007550031020281c04140b84001c2c40b0600700003c0203000e050328091682d808400181082d000042c9450750030f030700b0200c0e510f000d05c05030344c1e1000d26210325000b1402d140f01c0492241400e0301000712050300343c0ca0f040c00d01211100116800d900c000c142d1010440302c805ca5007142e060144103900343d00002c18000c11000c500e800d010b120f000c1c031580254071907031040103041e08807500401d0641e440240b80c1c4a0999503202e0400507400740c01c040f540c884c4003d0019494408258100d00030704180c80c003e60f054407075907031600302c40303141 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 629936115 1250 629934865 629934869
    0x31e060f0108220c060203120f01180c02070b0d02040e01050d0c03031b0609050c030d02010605100302030a15030f0510021e0c010f050a09050c100917070b03010e150109 74
    0x7501d0100010700360541c040d0280100f415003210118081841e8032084d40310780c5070b40c10280040c2c20006a00381240030710704a607504450000c040d58a59450301d454103c0d644107a03101207540d91748503001188041e0082c000384004107081c40b0381503a1074450704040c6000398000c0c0142c03001450010008070325414607034001007807a644001000c400500b141c805942c003107080044e03245108201c07034400d00001d02c04d01903034080c0c0c0d100e8001040034121031003c2504103001401210b0031a07140c804d040045a86030740c456a261115400c0044ea01e0b00c0d000980000341c55144000101034403183c00020800814010a40000f8040e1341900c4000d20250303c0d1a050740300e8083d029084c0b500c0240d040e0410341c040001040c45a6030361000044d51181d00c01c0e44d0050f55000c84810b1015543e5041c10f8091010510071346040481c02c0768500d0040300221009884100580070381d81c07240c1d040c031001c1000440d0400000c03014003081481107843e90380d0347c091208200801c0781c107071030b0305030140b2921070807035018800c2e000c2 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 629937365 1250 629936115 629936117
    0x1314151e09040f0f0f030801140108070807030c020a06060f06020706051614100903030c090e0c030a180f0c0303110102070201020c040e010b27100e060d020114031e060f01 75
    0x382c5464658050000030b20400b92000d41401200380d00144c3e0150001c0d0056201e034403402c0040d0300d0200144841c00c0c440390b0300d42c14803028404000c1000c0e8420a81c582c00703105c0303080c0017070110f01541040b480c00070744100c010300035883c0102c00b10b040c9010a01c0da0084030510780c00c079541d0f1034460000701d8050040c18080c1305013283c0f4903107000000b01c80505d4002800850821580144d8004241e42c05484444400307401180d51503d1521400350700ca40000042c050700c00340c00c050f6044c200b91140c42407100905c412103003940d40850800790004840c1100a050304144c4000205045090030203400303c1310302c0f040300822412024440c5001301030085e00d5070b12780c05802401c11048020240406002c0b140b403491182d55a602400500750380354004000400158011440c00f1401105c208044501c060028070005014000030810311a01080040d4000000d6035070154158040c40143c81c54000031f05108042c400210400c0381d1b40c5c21285801c0d12408507400380c0c1c1c00c25100c0c0b0041c490b031151000c1e5014 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 629938615 1250 629937365 629937379
    0x4030f14031603261611030c19050a15050a0b04060302060a03090303020405030102040e2d07050a020304180209011814010c0503040b04030308150319021314151e 71
    0x402280c056503581e0200c42102800e40d044c0d20960f080312540007011515413158440104200d15036580c40400c0b0b046404000c8015480c090404010740c1d0340c1c4603400b0504000c81d9480e4101010400180300e095a50b642c0960040c10744e002640190300a40811500e011040b032920a0501e0302e0b2a0501401080741c1e0040c2400c0d00d4130769181800c8001e001010402d4051580802001940ba102407000340020803040b00c14603807a041844030000b100c891010042e07810640680e00744020000d00c042190000007034105a075451f030000c00140d0a41c081c0360f02584003103001c00c41081810465400a28050100b42d131b903501030100321900b00e01c80d0301e080d014041e00c1001d05240c80602d03500500080900c3e0380a40b00b203e05203551075801014030342c0142c0044001603400c0d030610030160032040d241030101c00300f200a44414030031050f02d4501620703003010180c49030403050b0080d540700809602400c0c0c401000c2e01950600d24141d070442c01e04602c1c0550040c003600c00f5a0028071210508030306802c2081c07000b4100 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 629939865 1250 629938615 629938657
    0x100605030a0e1e03070c120507051e03010507110d0305040c06110c1903170c0c01050721020d120b150a110a210806090c0d090804030f1403 61
    0x381c020314522040501620625140e40001040c60b0b6400b40f50042c6000159540c2001d4a0039900004059002407402070030304140c540052800b00c2c82d01d05680043d11003e91580c0004000c4111401e0741d10100d401d5441d01c0284045154002c204000b02010310702100e0005000758400c804481c402c4402402c402030000f41845014421031421413400c0f45481203a100c005580b0000c0d00c1e20000000307041d2a10210b00e000c00c104625400d001281c5025035200500344014038030341d951120441301400d4108940010f0800c20040c1c03594132070f00040804045031444100c1584003035074072031401661201081c911100b900b11481d4600a25410f514082c0070f007020b0420b85107040d0f42c1e941000304880d041c84100311a008814004009400d0060301892200900701e03402615050110984520401085a590208801c5071103071a8950b40002c44003c950b950341e400043c10400500144000410340b40340082c0c0041444500d90009a10034081c005040c40e0700c405000540ea20b01c10380d11a4030694007910345c6 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 629941115 1250 629939865 629939881
    0x3180f0b0109111804150902030c0a020c01020708060402101103211008070509041703100501090605030601082e0305010b03011a1f050d0f0903020114100e040507030f120810060503 79
    0x450006c03a480140b8502406032220404800e907042140c4040c00e006e400302d106020a81d040106540c5001c00303002400b0703464202204030740c44540042000c0e00510040201d82d8126201c0c0403640d240314602010303280c87c0e510400d606c03407504000070260302e40041000007140003c01607075500d80c219840c201c01484403928010510210b040c0080c015101044040310300150000b4210041d0700c40c01c83c00c130300d00103030750708180000d407a01d007054000408016080c02046640d98204032810342101d0415001c0038803585072414880381a01c2003c001e40741d00d82c3c10b1030010030400150000100240118000d0003440d050703240440c40c0701010308545074030007a0700810034000b00d07400c54650f1001201b03240882c585010130908109465400a40402d031580e5820540281617081c41601607020f82c541400c0c58904018006031031a203040d00a00651502c0940882c04110342080150011035002c2030460041410f0300b001100024005044001300e845403000a0310899850b0507482034501c5034440c0c605684602e03003 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 629942365 1250 629941115 629941121
    0x3030c0b060405062d180f070305041101030506030c0301110421050606061c0903050c10050c0919030c060305061c0f0624290301051003180f0b0109111804 68
    0x8401c251101e0341c81c031700b0803458460360b10b804400c08219025042c2401c181c0312a03401e4800051507241014078000510001450b0101ca4402031a02484d0110f5262a0440007c0c1003884290400340d1540c0b9080b914502d600c0400c0c081c20484501c81003603a00715100c1223503041140320002008102e500424001116403030710314090b0032070902c038181240c022101c4051081c100c0d2540300d01900410008900c0c514000303002c10140f07026076400c0e4030500060800300005032650107902051446040880e54402c8824404803401d4001c5070090034540c4a596074071000b4006007010b45541d805501240c16407400003200c0c04980e441b0325403202c0c41001301210341d22000005c2604000380f4142903200498000e00d140e402030540050000f210340711140017003600d84841800fa09424410f04950300b40010070440c0d8503520a0205200c0500303011650007501c071241002940c0b842401020360381e5260a80061045000002c1d058806541c020407900320403001034840e500444103200300b441c44400700320742c80d07061a0b0 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 629943615 1250 629942365 629942419
    0x21040305040803040b19020c0d080901121113060207081b060729060301090803130828020c0114071709040f0f14100905090c0a03030c0b06040506 64
    0x3140c6582040d8442103801c3c00d640c481e81c0500c0410101141c103044207082c010440c4030602040c00188011a8840302003418000c04844c01b810b100008144000355901a046141228810040400001a00341c1d24900c0c0740d0403590b1843c110000050300843d0407400080c0141c1038449080042814131115000080304070000080560082c0c420300000700050209400c41c0c1d80d400120340d12095810351851042c99210004142c6407080e0705151030a00843e40c98801c680e040281c01c1c0b9005030100c0c407410098628441c01540e55180d850045080e00c20450403207a00c0000d07091582525207128004004548050440d454600002c200304800c9000401e011401c446201c042d80c0034a08041c0d10000090031140d41180d2440c1c09500c482d05100b0078100d42c420350020b8041030200851780d007003001c114522000c090050400c1d481e42c0d840883c0031001c0410524910f00002050341d02100c1d102d203001488040c4c10b001c1215410780f8030000c10542d117020300031030340b00e241e002e8803528a075100007501081c008030803 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 629944865 1250 629943615 629943617
    0x50f010e030f0d0b06070b04020915060409021612050a09080d0503160905150904060f03050a02060d090b100e070806010f0e0d060518070815160e03071701060605210403 74
    0x1800b44204c2c94968001409a95000c1c04080c8418500b90041c0610142c2c02012920044a040c2e611801c568449050381e0580d0901000140c5074500070182c12036804560300b016000d01881442c2700242c580c4040185122860b560354201c07065610b02880d0f80c0c0328052202c1c0c0e000300f04288005002211b544903040303001075041c0f510903215513442012940c1500082051801d1090000b16620a814280914001007074170002c0c0e00300e41e46c40c42d120b20f0346810500000034400c6c1d030000341c252402d000e03a81064282c140c00a202142c00d007425181a04111241d01c28461181000c40010b4a50b9001e02540c621a41060b100c1d5821840250403c545018415461660101c036900c0910041407080c40341e18412140000c601e41c01c0d00080f0b198138070742501580009140d034466020480f60305418140030386c1020b01c1351401c24810440d075500796120070f19454860340503c82c1907800030700509108810043d64a221000308141915454102c80c68403a0451245440100c0001c0140c0e402201d01c450744c0c450b000e = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 629946115 1250 629944865 629944871
    0x10237050d09140601090b1503130c0e01090510120c1502030f0301030c080f0303040c1a0702061606150303090e07033801110a0605090f01060e04050f010e030f0d 71
    0x5155100f0394002a24401c0c002d180c2c2c8240014407140d1060b218840a900c03080716181c1d8040c450480c4c80c02180710040043e01042440300c404010040c07405541009081ca0200080300e641e12196035030000c0c4801c4030282c050b00c01c503e000141c00e0a02c045c0c500c0c101d54005141103079013407e100315a00c001a010440c002148010001c41d4031902c07900c0c028502961003501500c13055490901258981070100801c005d080d00204180000038900c04006021140b03429050303003154800c0c071005141402480c01c060f4020600083e03010420624099040c0100e1050343c0c1008840c810080c00290103040e0300008010035514213080c0320000d800e46020382c0c0911240b0300818203002807420385107a586c90916404040188000e404070b01c503100040c0c600d60810030700c0c00a10001d481061140d880c44940006040b0a94800208e10041414081c0101c21008a4001e0102d9070741c900c50030b21550401c80301981e1500421400c1050f019043c0107041901040000440c1001c426111200180e48240000d0030805e41d = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 629947365 1250 629946115 629946131
    0x5180109051507141507121803080912091008060307050307080601060809010b010e0f040906022209050c0a140c1f0e1c03020a20010237050d 62
    0x514203880036221029402d01544401d658504030024070030302d0759244450f03044410704641808486201681c17011051415031001a2600240320061649035002d030080401204441c2c28540c10940d0103000b07481315021614146500168a4001e005021010740d00051400c4150b40d40d81c0b0628031903801074401020744110326941c60000f03150401c02d500c41c1c01c940c3c000400420200e50441a01c5a0044140000b4449800f104000a04a00c81280b84a1281c0e001c151741908030344a50307004180f003950002c0115a10643c0fa419084021010b06000c0b040300450000811340c0f116502403607010780720b141450b90401c207901c401036844030a83c011200c05200103004c035041c014020007101c0340c0710381903100400c944d0030a40c2e1100281e03031840d03100c1513083d440b001c0d544009030600b60290f49400740504c0c005803100c900714000c42c0c1c074400e00303444842003038203c41c06060040019030090072680080440f4104040c01c203280c3d00d130b8850740740d406080103910f02c00100da8a540108000c12240103444000502c940c = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 629948615 1250 629947365 629947369
    0x1517070e0421080712020708090a03151a1e1302120403110a1a0601230903060f0c0f091507030315080f0c0d020a081902040f0c0518010905 61
    0x20304101d41c1540c800750781030341e10400780540c034400300c0121156103800182480c1890015090f40e0000c03040c90f202c190700003520701c2803109000c20307203036070000051140384016903d00303002001070785213500328080d40d1070441d00c01100030601c10000c040b80b10203400a9030700d44075100c2a2201c1c42c1c519a07080d41220854418216801c058070040c9605242070350b07141c0c2c290a150030000c190b0880c0d50041041a401900d81602140e80e1020711542c0400541041d6100d0351180c00482d0002c000e24040c8032988405010701c440100d07180e000d402c0b220820740031241181c3d00d840c000500400d0569000d21082c404101d9801c0e01311080300245104080034260320841d114402c4400002e5004500a6001a0f0740d04048110000c0d401c4664000301090802401d04040c07200b00940c45842c0340c0d02c054400c0c401c2001080464072000d17032480c0200041e0082e2403031490301046400e08052401c408901c01e5150a0308013900d040d5a12030500d400b1000d54480303007404000d070741d1150301b02c80345281389040c0002c8400004503a = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 629949865 1250 629948615 629948639
    0x403020a0605070605072f07120302011a010201020f04030b0718031103060702011b080912030f1b160b0a091e02040e19021c05030d020a0f03151707 65
    0xc0026079a819910341a50404108a40006c3c0045080240d0b03460b103a0100c180c4a40200c5900b200c81c2034504007519030110b21450301113150b028201043e51031606070b040c590107500400030180300c1c003869241e00d80d44000480c01c0744501200106014024071003030002c5001040015807142d240d040c000441404d07891100690040ca60003110010700300e8213050b0444c14180400d60704150680000e02154a00d081c8000360100581e003460200003502c000242129002c2048100d907203894120a80d503401c022003d800066002c9030001c0c40107110040c0300f540507203000c0445800c0c0a136041c549800d007403d90354819010358040c0800c44d006803902661404640d0814241e010f080d811080c0d19822511413040c481070380e1409480b916103400c02c1c601d2000c47c02012410000e0240e04540a406c410140440b212001607083c101610a2002045401810300702d507005103503106140d21102055a00120102c0960307045e8070701d01d030390f14048440c00c00044204095115210500c3e0b41035803001d58803101ca131524 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 629951115 1250 629949865 629949869
    0xd0c0801022205061b0115180e0a0c1503020f0304060203010f0e0108031c09050d050901020c01050c060f07021014041e030915030204050303030f0a060b0309030301060c06060905070f090611120f0403020a 89
    0x249240080c0492196510a502c1003d03078072700141c400c07183d080c0c65810903481c941c0700350000f8003004041d00c00601d04c603a04541c044107094620b90340360300300340c00c085000b03420074010340d03604402d03204010a5401240901504880c24900214030b045155505201140b804514130030b003007901c418104000500130f12200d60340342d03240da95450f00c85001d8000240303006070300280181408030400400e00442c0e404501198884416025074109407a205000c03172030154101d0380881010302d4280a05641258504894000e500507c07292400311f020803203051005411500c010081b40358003208000101d4100d90320419014903044c01801d1036075440100b401c0d90b0080355142c80c000e003c07000300000c41810344038000c043c05e0780b021070a0039031800000d5940d50b4030042c000c0000340203816481c0d80821640341c01c100e0140c0580c540521003420185006810104180d1143c00031404140010528510920000c5481e0000748010010400c0c25030618116601090502c000a030301044003002503240e4402d5200 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 629952365 1250 629951115 629951129
    0x1e1509060b06070308070f09030512090d020a03061a0405131b1203020c030613020d080d020d0c0c0210030510030209100902030f01080106060302090d0602090d0c0801022205061b0115 80
    0x50146000c00004050481f904c007042c052014021003031020400001c1c40b06890b0081c64a215541d60640c1c2c00a0300c1049582802584008081808420001180c201c600e50012025100d8039010201c3d04100680b5400c841030002c00403103074441000304007200c20b10360b1041030082e06281c9040e102c0708880d11a141111055001d43d0060500000d90f0404005c1664000181e0340c610803002166030006080c1208510041c140030404540303d0000e86035a8101c403580e00b0940c4080007912602440501018204d00045c1e204045610410402ca8001c0c0102d500c295001e1111004245c15507003040b1282d000034001d003070300801212000c02c840046100a5006034010489410103601d03044086084d65110f40140c81058010f100046440d1290f40301d402c07400f80d0144001d40c0721292000811310707810f5240b202034142c660302d0600091149044d0700811101c1c04510070224601401034078082006501d2140d2a0002c00030400300c3d600d11800c502c00c0e13024506401c0042903000c0c4130180c4000b904a641c0000d8 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 629953615 1250 629952365 629952377
    0x12150b06030c0c060c0705070308030c160c030b150a15031b2d1b03030227130b0a0509041e0515011d01090b15161e1509060b060703 58
    0x8903903d41c1040b09940c0b00c26210b014602c1d01d0060390390580c881c0c45d03c0c480200000808000304103038010790006e403891001e07400b00701c80040042d4200460075221512041d04c00041c034001143c0d411003021900d041900c0d001d0701d205402e134074001c08142c88400d000701200405541381913450300c170050b100e80080309009075030310048000c440a00d20150024050351180c2d204181c48640c40c5d000780c110080700d14200e104040b07044a4a09030400b03601910444445208810841341e000c650380c4a100070403065100260b0f4115001c003d0070b44580101d0300c103600c40030ba019000d000100304926001000541c0035110301e180c40d14502103088003d079084220300e0100e031550028100d4003890b01e81c040c001f90041c01c1032040c006401d4180c0010302c0300c58006000d81110641c139000d4130178154680c1011228402e0060706100e035210500040000c09440300d18040b29502e00514124005000c1407400070001c0fa0881c6041e071541c0985d4401800810780d09004403400303911105030030313000d40d2600041c0141034000d031900 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 629954865 1250 629953615 629953627
    0x50a0b01030b0d32061e161b05060405010c0216030305040e071e08150603040210110f03120103021215220204140a06081b06180909160503030412150b06030c 69
    0x1c01e40c240d5001d4241b201080c40400c00000c00ca00000c03034120100d8509100b04000915000c0b01d02040c2c09141c060000c1c4601c0050100b0040150301050b07030810b00d40d00b40c460218140b040c2101c4c400d00d910000d40011014401131213032114941403e0b400c6100b40c285001600012203001001c034801510120120b50442d08104003802052000400b04404840c03180c554034065001030a0400e402228030200010312a1710071700d0040c100540442c00300c8441c100d030749404180200c55407903542400704a0042d4401c1c1194641800c0024604040c140720b02e9640340e2036038688940b0711a140360003000d40500c103620030001d03001da1100d200d20514118496a402000c1c90501c180d10199003295120b403010344c2c850044400618000d640242c0c1e02c0008440c891707601c68402d008001c49035248503c19611090980520200d540006210b001e0340e42c0e41c00c1d0040d501ca42d60000c01da200e0089200da2015800303d114480d00240c07040c0300f48010610001c1000680c0c03040341001c2a10750704211024405004000341c2 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 629956115 1250 629954865 629954881
    0x18060e06130b0307090e0f01120f2001020f01020403170a050405040f02070201031a0a1e1508040201020d02030f03061c060f15080f19022101050a0b01030b0d3206 71
    0x11441c090b1100001d403000da810a1051f802e08110140325100c032540d040c02482c010441445100c00001d5001990502c01008036658202c2c0c20b00c007416101c0c00b500c1102c02200410106009890440b5044140004000000e4540948a601448071002003110401010645503514402d515003420b4001c001a1181d245200140458001c1d0b403110b40c400e81c00a100c18082d6440040081c00d403070490f800807002040d45400556445034a41100c41c01d0310311120b4079285550b0040d515407103103000346d007201d84013540b000090f40c0380c1c42180000c01404004000090305401c2131500360000c424984050f111001c0b130b40e101c2c4011144001102100244c4680900300b10f5000040d1000240c42000d02a091908940820694605c8500200061400692844815503550000c804d40c80081900020000c41c2c041c0200c9000b890100c0d440c500c824030749480c1d1051540301c2d1240b00c040207000f1b04440c0b071201642d15110001450301c005501200705529003c0603100b080030100d075007610300000070402400e04800e = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 629957365 1250 629956115 629956127
    0xc05030408071401030e0a060b040b1206090c010503091504031110060305071502100911030a14101b03090602040b070804090b1519030b0d0308150118060e06130b0307 73
    0x44030781d04240c04c103040001001c6c004201448096031084c40040d51342c0c149000308010340702c030b0443c141d446041000c0d03a41c04210089002c80c40345014070103880c0058441801510680400c1c0c51a465a0703100c4240c200f802001d1804071600315010381003010428984402091910380c05036140800c0e10740301c01c0c0330002c004007040900040c000407050f50402820b070207402965280c0751001c014000343c940280030284241034207000b400100141c00d903584031005042c66810751000c036a62100c0b922a850101c0341030905803003544038101101c9048080101e00321000c80240010b0f43c03046d11039035130030000005c003514050010200d89100703419458540785404141c100720361032407d506000d42c528003402141d503100801180c031100300c400f0202a001d039200c00c0840c0180401b200c8107410107145c0070002c1c14140c20072a5144100680f080807503001081c40011280400c028415007254140c000d0144122405038811280070302010b481541051080c0710b000410490365841110303140c1c4000300703210b0744660001c = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 629958615 1250 629957365 629957399
    0x13080c0a0210050f0d0f1503030810140901051e0a060c0227011e08160510090302090c07030311070807050f070b16060207020901090605120f03040302010f0c0503040807 74
    0x403c0a6041100b9224101c080c0d10807892070f4100c295075203160050080b4607a100d180074a1070000303043c422546a241c00303003209206807403590902c1540d20000030354a4200320070941400e80034200c41c00742c1e407031714017813210001c3c8100100078203901d2003010f0309817621082913800041a9541d40d0328440306a42c01441900c1c0041250070701c81c0b40c513190110805906c3c942d8050f045030041401180c1c402d40c50000c0410b1901950000001800340c01c000041c2c0c900701e04ca85000b80e807001c680c1c40f00d90681e14041078400071150700c402904000900000360404552401070620f0700d0084c100400c803081010310841d0b40f5448000b00f20380c241808540c4000380082000220980d202c040f000f80500f50070b290708200d0750f00901c0503030580d4020f84200b1104003e05901a159101d6026050440da940c4854501003d0900e90141038043d80340c4160700f00c031248000581040300000c0d5005185040d00b5900110703201102e074000e160620003545044000507804100030402410041e0252520506048a083c0411005 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 629959865 1250 629958615 629958617
    0x40e03030402030a110117011206140708010504020f0705010609020a0207060206010e010519270b0406211e05030d0614060d0b040f0e010b0a06140d020313080c0a0210 73
    0x500c10000180c6001805000c0700b60070558082e44890701c800100d603005070940660990000c0f503800003070450500110070301d09601c01c0c81c003800032200014102c10080740c110359010000c3d0030440100b01c1d40c101540182040030818039080c0c0b400405840c0e1909503041d0342c0c480c9a10a600041161400e81e051082001401c0c2034400f0f08100c0d490304e410641d81c03c17010b0040e40e224a625005411010b0340100f5010014100040c88500305102c844200e0310325400c0c000b10240c3e03a4103044100344d00340b60a100352070940c3d1041c41e03280b405030024460320200c0309020b24111000555074812000007054880540a6148600020340c0d072241c003410010280c0d15980e00c1b225000d2090010340c08550303144001d4581c1409100310004220040c540014003901a95174034500e26860009051a41041074121401c603070300654000c1e815a90301c0100b190841401c0e00e20103803080c0140103c0b429003410340c00a50704052030910080d25159607172251203a41c3d00c01e42e0701c0f00c1c03241e1120708203404500701114006441030007 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 629961115 1250 629959865 629959867
    0x90e0601031a070c03141306020a14010507120902040f02072103060e060103020901140a020a0b060a060c08030903040f0f0501110a0b0a090c15051c020c03070305090616030806040e03 80
    0x8079400107081403c138500000e05200070b2034201d4004500d40350956080092200603640c0031030780c0ba940039444444510003900d50a400056400e0410414054140103012942d40e5020600038400050000c0006c0030080740e002c1e454500703002c00420240003910180f80510402c1c1c00040d1030b182d0703203031603c10701036841002d01d418a031041000c01140d1950780e40c0305a0030309000d1f9543c03000800403641011080120400107074041861440c1c02e40c0021102d251030b11440c0b00508039120382c0c081203480c03000b0340f04250020748841202400a40240013460700050b25a086a0074a038482c481d40350492410b400c5142c0a038034034035040000d581d01040301e001b20503200019011280030b5440312203000030001e00700303413800da102c10702802004028014103004107410740444a80388580c89000f0007950004200c16000c0740d40102c1d00c1c0380c0e1502c5108603102103070120021494072544ea5000c3d22181c1044003080e5001c14240109103100409410041990303209650381c0c049403038200b041108440e03511400d42c1d02c6500c = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 629962365 1250 629961115 629961121
    0x62301140301093905030a0219030e0106090b0a03031107090e150a05040b0402060313020d0f060c1b0b10080f010510350a020d030c02152104050106090e0601031a 71
    0x118a501d444c9041168030f0f00550769a500f072144806407103001003510920004036030b10110b1543c96440f8483d0550150000c1c010659111400001e407058000201d60115111400b0030009000e05103200300b204244098506050f41c43d0504011644000c40d002015001b00c007003020480c8212100e154002c811b040100700c1814151200e8050358030003000207004040c000042826034406984210b1040c4e80201042c160403154540500100c03038502c0d003100c1130350034086960711180c001d5441c0c0c0203006004000600308039032a1500104e040c00a445440c0055401c1004a4803c009021255820068000100e46820190107203480354200c2c1d48458280074500d071021202290803074101c04028a41c103a08140806007800300c9080500d08040254080c0c1480621010140c100c40c0e60390720035008488031100310007000181c030f9161060101c0704510780040c1c1171880310018001c810f6900180100c000046040c0c4514070441244c0104000d1195980310100410400c01c40b000c1412007181003074100c405500b = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 629963615 1250 629962365 629962451
    0x31605130522080c0318093301030b0a08010504050c060f040504090c0f08060a050c0f030403080702100f02090306060d051218130b031006230114030109 67
    0x15004910004051003a41910300b44001c0f0340a460400c0b14690941e59111108100781d0b03194904568102e0050700e402c00050010956081003407280c410480105921400b01010a4551260130558505043d6603504460603034032030304500c40140002e031000180509160070f0403441c1014416079140700311410441410922008016203080f0740c800e56008c5000581440c0408025815030024581d4a8030704100050704100060b20300d024130f0310000308014540381c4040041c1c043c4144280c0070900300d03080003c01e000a01c51811141c0c4001c81e8415110900b90b201107010540b240c0003892015980c001c94a4901c80c9401c3c40015000382c81154000080c11450f0ba8550f1910b00440c030075004850085520786611240e01d0710070f04080c5004200741c008000251807e0000e101c088801340c0244600b10414545140c0d600c078003030555810122490140d180c11008507000c01d0441511070403c00f00503003988400c00002c2c051406010b003d4804100d1605025208004803414090308402c0429915038205030 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 629964865 1250 629963615 629963641
    0x8010501121a012105010e06040f021008060a05060703052217060f04140a050a0c142d0409080403200a1503020307050702120705131a0f0f0316051305 66
    0x4c0c240d054400001c030405800c1c05070041c03000604c0041c8900814041000700140c0c034031440e40e4a803080322001e6001521a0f0215107404041f2840c541041d0800c40a020703d240c20806440320302d200789403851030451b0a2007a00c0e40c440c0803604005103041034210620001c4803600d024030890005030001c10461130034900c01b545c407003170140000c0d202e45403a6003000310469045c000781006d190480c0071210040021b1411460382c407038511601e0007000744104042410316000c001c030840912946c0154014851052280780480300390541c4a034007030740d00c0ca420400108070501800c0110f000d8614040f00c40d986000d103446940d060300ca803c1c41104031180c24407065403032035590154040c25142c01a1a55111402030303509102d0f41601039800340b129445c00c0900c400005400c0c00b03613035007680c1079a200f480142211080c0c0c0c10390000340c06041101500e06015081c06110381c100740c90300030302d9007a650600c84042414008941d0b170040e43d2648421091107a0304040314230754600f84d10b0841c00c100034038151480d07480c0 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 629966115 1250 629964865 629964899
    0x3020d0f0b0703023912030f0601031803030b0103061706041218140f041e0e0d090e061309140f0307030e060a0309060204080f01060f0b0301050111030408010501121a01 74
    0x40c04e40200b2101105003c00b521038a0106031740c8046489041300c1d15440b49054004441640c00346460400040030344d4401e010300364099800f0000c002e9a200d240d60709070040e01a0414a9040558a082c0020440b2940e140c16210100340c002400e8141032a003458225074040c03400040511035404070002e502d0810f2442d180c2124202e10f0f496082c0c3c48500002011000402c14007580281080d078000c26410b0903288420000802d554200003d0030810f0309141c585d4241c140d00c1020030052a0108080410080d6040d0300c104c00510188040300c111061600700c4a461000303440000240c0740d00704980100700410340392812084021404c2c40c03001c1e038000f84000701c000d8007580a9a070105a10000c036020740c00200e0b815601404c250b407940e4130b850145680e280072202452066080c1080050600c0714024413006540546052600d941e0a00006442e0b0755030110901f180c40c8010000011250820f02c6002e002c0c180c000c0d10700000f20800e040c411b0801c1c80a0581c091140f4140004002c0c10240580d0120 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 629967365 1250 629966115 629966167
    0xc040302101202030406021b0d1e022b1403010513091401060611070f030b01060c0212030a05120a150311060705160603110a09061803020d0f0b070302 66
    0x29646041d0102115554040c10000c0c00240c004010700041100c20340180c002c0a2205c3d0340b0148612500348010383c0c1d070640c403c804000c22903250101805080d9034003845481d0010340100d440c151000c03a28050841c8126080c203402c4594081e4540722170303910104840800282c600c1c560b007954100800034181002d280f0060b035040d540ca9070b8400400c080c01969402e5000201f00820803107075a4070019054201000c2010241d014402003c03440210b180c0d514004e40b0740013166400141c1c00c00000b0350340a05e803900c003640e002079401d03212003114600304002c00140455548003511a03c000e4000c0c921800301034060b500700e42c00c003100313400f101002e0a01201100d800003062280d210080011419078864038402524034014084031140c03030141000e48504886140da001c01080c80080007100c440e00543c40260700164079027900704083d510a20f020f00d100c0b07a00d60940d4854035500d0b0b0001d00c00030b080030070454140e005610000e090040301c1c485c0315848140390405600d00002c01041406548066580c08 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 629968615 1250 629967365 629967379
    0xa03051909050607080105042a0e132405030a02130204050a0905011703071e05102912030a0c110d081b0c090c341a0c040302 55
    0x36600c004018031014040150060812508155003066901d0702400c4030001d010420381000011942064424503000c020191b01c20f42c0d60307030318415880c03c00000d20700e00307041000341e0500c2100e01540c07141004090407031444000680290968040600c0c9001c5044c40c00c039403480c1210030400381c0c6000c241031800f954115000a43d51f0780c000021030090282e40c200ca60000103007000413035a118198441d40c160355101c440401c4006030b41600968a10031701c02e00518411030709044a004803072400720f2003203441c0301c0c000361071010b1250b1003c03004070b6014807001080e0302d61408104813010446120301a61620948220401101d00880345650f131040c101c4030320401c500d07022000c05024808050518118000340001d510080724200808181c0102c0200350040f8507044115226040000701020500c001500518103603549201c1d800154202c99542c2c07403c1000e904080241c03143c9c07a40108100d001e00641c00080d5401820300d0500202c007031903c3d1000204000a1010740884001520101c80d070443e199 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 629969865 1250 629968615 629968621
    0x40519150f0603080c1f060b0a111213150305040503041512051515030f0105040f020d2c0303010f12020a030609060234020f01230703030605090c0a0305 67
    0x300042c80c00d0f43c0b01500d03605022070340b040508004a041e0003110f0742590304440043c240010b09003111500d105441a0354810010b00015a0144814120390b2240e00142c030a0104813034a0100c0992247c02105d0405401352001c0c001e24409122003c3d11000c6864204100c0c5490340d6526940d10481c01803000c21407024401010581c8210701911b9048540c00c1c007405903092110304a0144107100c80658820321010b8a070080c1000240240ca104d000100d810300060703480e103402e1000501c41c202c04403004079020480c442d00404103000b00c00400b02031128401055003141c00301c85480d4200700c2c1c1d4070340c82d4004200410641c26140c400b4401e8030728001c802d000400e05880080c030044150307440100081c1c1003d44030b1080c01120381c0179040710180941d003025002c0407071490100d540041015907032840c0e0b1215404000d820000c05680c0b42c95810f050240210120a07450089801c0e49000d42c0210440003589204144d81806510010803003034440e8030107800c2c0b101c0d80b801c503401450004d0742010358034800 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 629971115 1250 629969865 629969891
    0x106030506031e15010b0f0301050603040609020303180114130314070e0907090b09062101020c07030b061912080a090f060314013503040302120604051915 68
    0x42440000c0c481c03401c1c00b009070002d5140c2d94072100300d80508800d144c4a0400040d8600c468030848401c07080d0640c1641c41c507800c1404210440c0c10241c0242d810340d03070729410a00103071001c00c01001d2041d00c03036824032000c0350250001030281c55400314100e1855000d12001d28a00c00804440f07040e00d0b0300002e034840a940860240f4508942a03100c102041b6020081c41003401000c00c1010685040007824409100280d05111810105494094021181c81400c1701001c860b00326030604045103d00152500c641552004cac0307000e519410540d22010880d092000c607140107074102068480c040c6803025035925003c20002c40c41d0f501c010240c410302c000681d9112891046c01d400313001c2e1105410240180d900d59034001c000f001c1281000400301580c1c070010890000d01440544c01100b0280800c201800c002c603040e03558090309c2c0a0020910080c0b10200040c0c0d500650180d84500f600c005250611700381c00c00518003284000e01c01240c82980c4500b07004100f0007502c2d018154001c04012903a0346001e64 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 629972365 1250 629971115 629971123
    0x4050f0d15020a08160c0b0601031d010c05090414040f031103120c03040605100503030906090301020f0a050705060a0e28050d020102030a060801020c0a0b1b130e011d010603050603 79
    0x704920300c462000a10700b030001c0d00000c1140c0601c8607921850b0340e060f4240300a0301c510310b900001138070044d0440c2c002842503210703401540c40e40c0c01c2002da401d00e03a801e441c42c080c00d40750641d90503000700b4130100e15212141410300c2807030349040f4800340401d503606054a5020a0381302604010382000900650a2205401082283c62240301c030798400c0304918089080c0f03030b06a0001c0c6e80840d810b43c203000100380340d10083e184035400c1c0e8400a01a61070441198100b180e1381d4000092a6015502882101c141c0f8012401410184440d5212242d440c81c152a219060400007840c0328103591518402d80d5603890b00046506401045081c409100c000b2080042803441000304c0c01800340c0304000d2682c15042d81900514001d41042c40c0c180b0031541c607042d0303003400e0740541d80d440482580510120404940d00c810f241e900703c01165034103005102446501e61960f48a58410110070304d00c1c600402c040c0080c0759003140140015070703002100c0d5000c0141040e040b801131144c0c40070140c40d1004258a0f40c2d042c0 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 629973615 1250 629972365 629972393
    0x604110f0a050906120403120507020606010e1311040e041122020f0706020307020f061003050a26030103060218273324072a03051b010504050f0d 64
    0x2056050700d86c40e081c5030081c203196556040000d140d080c4000320b0030140c0000703150350040c00e0585406114901d0742045c46181c003c4418900710035038a03000692811403034440204090104010280e0030380c6040d041031701c030000780d0354011030003003250b10302d01000039846110000c0c0d041d11092001da994007900d503042100380035030703000070701801c3c800810720007056000205181a105071509440340c83c0e507008005924105c1c80d20006c2e1198000e045201c001030620111082000031503041c461040c1b0f0381d0348072280580c100741c008807140b03580020122034031a00c01d0340700386490808645041c3e0754150841200701c2c00c0710003100303003040d25074250200d40c1c02c00c9202c0c84081091140780c80441e50301200d40350354444c00030041c180b030f00400d0701c00500e0484402e00b80302840e501d043e070740b9494500202c41c0c0d201690721140d1001f281c248140840241c018040025400c00254040c000a02036005003402c9480d03074078443e4800a062101c02c000410854407101000030800c0d44c103c0340e10310382003024202040e6a00c0c0007 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 629974865 1250 629973615 629973637
    0xf010f3204050903091801050303040905040804150c031211071137051203070206180d08030103030831020f040608060709082404020d021005030604110f0a050906 71
    0x2e010814100b10000140c402c9200440d825649440019a924040102805072a805420400041c000340040707400240d0490300c02e01c0c09501d07055490940140c42c26001807100002032300a10542c0525511203002148855020410004500a0301d5040314030b100e01080140141809000581c0340d640d001c18407581c45200c255051034000000001c20680304484000080d504007520010030344d41007210301309104550040c01075140841940030010b03603802c02803c0c908001610550046503884603001001c9192107038604c07035101d504618000c0d1000000800c0c281d8200c801004190003840600c0745c401c25a46841c40180d00341d041400400d0030a9a2030342005d030400d0602c94009241100058080e11a01181c0d0390314036000e031500c0c400c03601c8605040b0022018201950001a40e2a680b00102d40103071000380065003200345540402c05170200c800d500408203001208100e40d504260003860481d074016004be6203048da1a0314400e48900078140a08100480400da02600d600c54104440c0e048000c = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 629976115 1250 629974865 629974871
    0x24010e090405010f0c200118080912033004050c0105180a14010806030613230a0605160509150f2101091a0306070804290f010f3204 58
    0xc44060030700244a030f01140390106d030181c41c4805d840c040c403860350aa4002c02c1c034410783d00c030a03844064050b00105601c0d030380203010300344c40700640e4400c000501a84008e00800070310003244c038008250101c8080302c1d130440000c0900400c40021408500c0c00d4502409003040c58803004005a0301c50041040700445810000404003c209030315034603440e0b90305000984c0c0310b945565445080c552201015030304034008000124110001820780103206155103040e40303000816080096000d071800d00e200200359010303951101401050206508024284009400c0c15442d00383e08002280003040c1c8890303010030380840441e003070703400d8000a0103d50500a9813240319203030080040d503011500000f0b05c6121100c40c900700e1440d80010700b185464035281402005040c80f42d8403c43c05558561004208071007500e0486010700c4c1c0420103011402c1481480300c01c41d41546071180220180c0803041e00301b48001d401110040110101e08071030401100080c00000d0303c100140600e00141c40340044600f0342c0241 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 629977365 1250 629976115 629976131
    0x140d0b0705040f0e0415060e04030309030e100809061b0901030f06050a0b13080c0607060f240e1305070314030426100c0806100c0c0e24010e090405010f 67
    0xb200d903c85001740d00a114008170800c1c42c6440740c3c00c8072210312588100c2d10603180003c001c0b0b0b000e60311041c1000c1c00f074140641e03080c00100028074583c0003400c060000c038032880e041c4840e44400f00312166000596803181d4951001405890440380202c9005504140e01c820368400032003c00d0700910010200544010f8215480c1c4848800c1c40c0c02c80340c0341e038000c0c5107800c0001802840c000349221707402c50007a040e0b5280000c0342c1c0b900b03800b90003408103424006c1d848c3c0e00303000050059120b01000c07099920040d5001c442c1403074003448822a010b8054001c00e0500001c200210380c010135948102c0c0d9004822500040f8401c2d8528114010350744122406001c013200300740301c2c00701c2c0d40360b0364814a03803903003075840300c0c0e004040b11011141c13804c0006002500f00c0b400640307203003840480d1603400125070400020034126075691500c038111a40000d099004140188400c2c0021001c1441c1081750115181c1d01c256507000000b40700850040c0054414004000071030107000c02980070361904020644c00b40039001c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 629978615 1250 629977365 629977379
    0x503131e1101020f0114010905090309120706030608010209130c140a021e0f070e070e06040f080105100305030d09060b0607030305070807050c061504021b0c0a140d0b0705040f 77
    0x90812180c860250003031342c80c20311031400103118501c40214500b400f1442642460710704002494000e001030b00d544010444411035136104510410500b00000c0141200c50034524014240c80c125400340745981c0c0144540c440076528a0304082003011440000902804200400c03140747e0005c11100040311400207040130f4155010889182e0f000d01100e550740b14801e0f00709242c2c3c0e10000008504403540018800b4480b0444907002150441c1462030009221081840040e40030ba00641c090a400707050500c0c1000084801e000e4075501403007580c1010300142c07440d154203031644100c0003800f50660740c17040150b08110703580c0c0c44198500c101900c0d0304c3e1100658900034000300402d44030040854255070020f03510602c140c04480d44513461101418440e192010084a40302004011660041c1c00303010b441c040000d80941104203d00f5039008125141c01d03a028091114141e42011144040ca5085600d1a44504405000315031341f000071150107a4410104507051301031034000c440841c4007000002080 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 629979865 1250 629978615 629978633
    0xc05060409150f0305030304030c1410050405061503030412020607060e030a031b02030901081e04080d0f09080909070c05070b12060901050904080c12030106081501020705010503131e 80
    0xa0881c0d503000c0c82116895500c0b81d06203e0071448014095441000040c001038416107129890764401e000c000440b4507403070012403e0007405281440555a20700c10401404000c012554100e0710030b80000c030382c0e4103038240426160310540c040c0b8440c00c2c00d2600d4078811522098200d40000d5040081003004030950030405480b5403117800028006810611441c01c100b200b1002070301d0344002a0015844d0418140066800f400020b082000ba10420300502025000d20b0300b44031b1186100e070183c0395691a00381c0c1400126444030901d103402a00d420038000006203c0c0c0c040741c0034100e0440315100e00d9a50518222091070031002c0003445801a1000003400c0c032820300c0985219503181c00b0b481d00a1703a070301e000c0c0070880c0f809108140d07000120b0800300c0c02041b02c00c401061950801b00642e005900d000c40e40e00081d91081e0300030800118404100646a030018400c0d0090910034405003084a2034980028582d01000d880380305c0304156901c00804008800c030404c40d030315030340f40079010081000b13003000121 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 629981115 1250 629979865 629979881
    0xd0806181b0d092f1e0301060518011508070504091e0f060810090206040515071202060f06030114010513060305160608011e060f0504031a06030d03020901080c070c05060409 76
    0x18030380c0c00613000c405680e10b400f00250380030016000d8150305000449800e0405149004140c05540e070764000701d0551215030500e024400032030125101540b40a4412198103038035540c0808100a40c424000441d80c0001100c003103c85612001c0f0b8600c40440880740c08007415609500c2003031914000030f441c800d0f03641150302101c890b54141c0383c64005041e03512054950f2982e0095010b40d080000f40071070310b010342200900406d030301c0015045c0b1640307645500681e28601000030269001d10108100c40c50301119042e4041010360090000c0a4142a8520090018041c1c1c6102e030543d0130020b00070729013035400a0000c5420208540c64045c0d120a505051301144c011030b00040c03401400840c080121800d09555003800b980c3e8520003920b03040781241d00120244a100411200300f0000000c01d07644c0841e420148107242c1328000c0c40c2004410186080034481c843c0003454014000c2100e5a070308445525808911800c6c001e60f1001c841c0740440c94000d01e0380209601280c0840c020074111015800862 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 629982365 1250 629981115 629981153
    0x1d13021503100317041d04031b05010f0542220c030605150918160807080915041406011205010c08240a05040c020d0806181b0d09 57
    0x280031245104e0501c49200301d014100100050600c4560280406c0440da07920500901d010403c2500281031108801c03031342d120a0350180e4681440003880002440303107940141c00740301c1030b10f0602c0c14040740804c8000200100034850f1a03449a0320f01c4082d0038402c100b5204401450032854000c21085000c1d072117500c43c2d101410710724014024821500074450f410940d00b00500e07400c014036044510001c560f200e401d68a0b08259100080d07103074030080701d0341c4074040c0c4e20340b1610204610040c1c8005105502c001d0041003003001e55000c0c032803441c0e804562407120207da50440a220341c2ea03410b00200a841030030340055540b14150000500b803810b40350b02e8560724852002884060390401040710600810b468605c00c10381e2503000049400d4801e14050301c003890181515003199a200d001070200c1d6011900358000d40c0140c080e803220301b070b1301100382603200700c0071a41b00401191070a02d03051058070040c048403010035100c100c0c00c3c91018001c2034550650303001005001c1d4204520300701c0d94840c850295a0 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 629983615 1250 629982365 629982383
    0xe0d02030c060c03070507150204050402282a02011106010801091502280318150e03041d071803081201090b010212090d0512040f1d130215031003 64
    0x5141c8039103c4080300e0080d811503495030309040301030f1a0b84042c1303066003030a1880240e08100004050315140003034405074280f00c00307500c03551100840314043c40f4030f20442d101c2006000001040880301010410104188126203001d581c0c0075480141d0701c10b800701e50a0220351051400026103050150044001c4130b1040d10401640031002c0206030070b074091407240703000e498490301c400c1200d200301400c20f288840361442d010500307032902c00d001454448103180544495950f5207020b007030760b084c1b405101e541c44031445c011440d00e0714202086107902c89032142c00e80c00c181e090000c1000c00d88074591009045e0300261044c054035030b4030301d880c401582c00800f440c034400b882e0300c00005011000d40300303905a010060300a06000c5a1300c2d0803010055100707a10786a8046c0d565501800415420080381040480d450300c1503645900b8110310080303c11496101c0980e00d8029180701001c54940468070b030b046016120b454003064014030008031102c84d07800c4100c400d00f070044104080c1285600301b00040324000c207500 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 629984865 1250 629983615 629983621
    0x506010f05100f0c020d020d0c0515091315031202070302090f0403021e07090f0b040b0a03050718020904050f060a05040c050703200703050a140606150d0e0d02030c06 73
    0x48030342d030034804a0792004030b6182c401035441d860040b0700c1a400144024100c0c00002210350000b082414400700c00e075540b001c81041482241070001402118078a0311486904000b41e5038001800e848081d44c0e09115180c40d040b403080c60003d01c0c01c1c210302840d80700c00340015404603524029a41c010030300c01648190400380118400c1c0784424030680c011038066003d000000f0000f80b05003503022a0031150200c034802c1c1308002480c1c800a21031000c3c01d420826011841d0080fa20070842690494035110b03102e00b24202d41000000e0300004c4800440b14a41481c42150070000c0b0450024001c0c1c02145400a04203401c0210070104840e02504c2050111040403850380ca0341d09100483c0c55009000340869000c201c00d40c0880e024080d00c25415000d46103c0001c0b102040040d0b0401c1c00e6079104070f4095103e10050410000345d440c08640c901d0010005002600d480c900050164511540030500220000f4122400201540040002201745c104a0751080d2118030300039541e038400c1030004100e0041da004 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 629986115 1250 629984865 629984869
    0x905150717092205010f0f060518040c0201090c051e120309100504030605090105040506060f0a080f0c090c090109140105160b1603020306030a0b1003050a080d050603060405070e09070e040506010f05 87
    0x642025101004110300c047d50521106440c5503204104000324805a524001e8403030b541c5004408082e0701e00d0f400131451804500e005580601207030000c03489002040004035520f918201d00a403011022200791700d00c1034031f0321003960075071040b000342503000b10000c0030759006641c1150090080700d22540c1d08200307d42d0740b000e00c80e00301c0d081601e0003407040d000040494194684044141d4600100a2441c481a5a183c00b400d28080030354450203199041090444100d150003803ca81d40480d91084a9180035580c40c0028038004041c00340c11541050111841e0341d03a4421015104441d0b80c69103081d02c0300c0c0317482c203122a0501c0c007282c1e10411304c89a141604040da1180c0250780c05014054028a1a249181d8a650312950010f00140c040092600004041038040107100380030b90040700115540c001c1c7c2121002a40c8004005c0e6000798040c10030b00c4000307000000c040c4102c2c1d070303e50072251180d00c0f0700c081c0c02d05040b4581c1c4421b200c2c00c1320409020900401044090417100440f407040300c0c282d503480c1 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 629987365 1250 629986115 629986139
    0x617090c010206070f03020f04090501050f10020705010c0c030b27030711060c160303180f0602030715060b0715060f03020901181805030a090515071709220501 70
    0x4022070068110383c003c0380b441401101c075856001c0b0300742000b5080c246001c6c508103880c0c1056104810084c1c40390010130460900002124081c0c1d0103490038602d2902000340650b82d10b420313128032410000040e141c0c4080c00140700c01c6030080c541c041702c040803a0410405182c01c10022070400c426080f0300d0400d180f0442e50000072030b52425031004a40f02680b103180108480c54001d2802c62510f40030343d090780703110f1022803a40d0314007451103a1110b02c421045008074202080c12600030040312681202c2c203000d82e1740c002040d138048980c0a41c60780f040d0400c58001c440a0040c40d40116420700010490303c04204914002c900100070602040140701e0b030355642030802807510711000c0d411030008801400b01900c04030154481c010ba900022a05540500d0107906030004118191400d8001240b040c4885d640b0082c5c100081504440c490440d441d501d43c404901d12981d0710040c60040304d01c040400e50754250043e0b56140c2002000b0394034a200701205c0220007030019105845a078944000802e02c000058 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 629988615 1250 629987365 629987383
    0x51f11240411040c0e060c19080315100e060306040b041109041401060801060c05030403050709271203020c0a0f0305070b13080a0c02061c0b03010c0c080a03150f061709 74
    0x945c6540344a08900300748516075008111540050250868aa8680510003c10044184129401a52481c0c0200c1c1440318010407402144907242115400b05015070110034120508070840e07003182e694a9200000d40140490100d082d003080c02d2468035940201040094005e280040da428000024121000304a045090007032501041c4450300500805100e10307002104c083c80b07202100c1c90540c503074991030314040003903200703088068542d4140245a0003001c5580d05824a0080805000070903565400318220803034140d0041545c007241003115141c08003d44641d1760341100340304e907420100d0300f40102150302c20503007518041904000302d00e26500c0c080da0128216003101c003003070902603c8001258a03040d80704003680d111100b4003241000e0500b03164030341003200c1d40b05000501e03c4021024582581c03003004001041c4840461520003280d052801c5400b11800da01d400140d0b0080d003010601c0544160700084c3c2c850741c04c1d41000c04c0c43d9800c800d0740c1c00d885d81c44100442d500d40c0e822610650303440d045 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 629989865 1250 629988615 629988617
    0x11e0b0109051f02070b0313020406060201090b0411061c0905010c020a120f09150e100c080405040c032403061a0627060a080a06051f11240411040c 65
    0x240d081c680d0050f403068600d10390711507a10640e03405c296112440200340c2c10564211044400e110180011031030b103881001c0080280380000d0041040c00d4444140d42600200090f083c00905001010117070b440d0f104540c0c18501c401408164600a94418002041d41d110200c680358a0220307512801d500001d0000030140c0c3c0300000e60302c9222042801c9a42640c0e5450540510035441c3c80440c07501d0404511940080444c0e9400556006103001c0058191880d4005000c0c0100541d11402060100003158184c44c010380780454200c040b042c045000b80b4a2012882d0302c9086440601400071414502004690042c4418403480842400d001e464124003410180e000c01c0800180c1042220340b140e04401803201451216001813200104406a00101c1607c00141c14441041500515880790501030f00303040d540300709079528000364820101c0410f44c0d88030610690070301c0c003540c0c00c608102100602880c518100c4150400008801c084070040e0350131101009a031900300c1440c145446549003810213 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 629991115 1250 629989865 629989879
    0xa0b03010912030c030204030c0e070f180b0702060702090103081c0c0e010c1406010807060305150303071e0609060b040e1b10110609031c020f040501080711011e0b010905 75
    0x8264090f002050703010281300c1030607003e10002000c1448403030110020100341104400515044d10010300d00300c003441c2ca40c0b042c04038550b00b41401e05c0c100e00941d41501c45050603d42e03030f4142800021481d0003520f030001e40c0603003170740000f104001c04480034000c522052004e606060b00b519040006030b88043c0e002d100003540c14020703401690700c2003c045203224001d0385001101200c4c0b2000c103050100c00d8120300096440320b0810080e10750326100d08c0e0740c0711840c0052580c981e011500000d450340b098680c0503103091800f45106c0c0700000c1c0c4020200d0525400300703080251810074035001010304030081d4914842c078a0b0044c4c4050450012034400c05560300100e181001c00001820440d030f0307094020109040101400200f004d0000070040301d07009001c0302d001180c07524128070016100002c2a265103034040d00601c005111f6505420a807400c0c0c1d070b402d080102441e5500303031080b80d03600d890900440d5250b00f07001c00ca002c140303812110184c002c0c2a0f40320920070f0301e00344401500d60380260b201c0d550704610 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 629992365 1250 629991115 629991143
    0x90203040803060f040b151801020a0f0b070908010f09061b0903140a0501240b1303060209120a120e01140301091107052e09050c01270e0a0b030109 65
    0x140818070410a43c9004100051b2003c0060100d4040c2401d071144650484000031800f401c07980034240c15011020910040c504083c8541c1d03140c04e41d15241c03400908400c581d0000c500c1c1c66020b0440600070b0803400d0000c020700d0070402c0114001e8010008281c1e64a0300d0704026603407000d2480080b118420b4280c581c070201c1d0f407030b40e5241ca900a5440031044024001e041c03400c00000c00a014468036480307500791400d00c00c0040f0500d040d9064040d03014815000041001200102c0710030b030840d0490350070800050700c0d1a17516020519018508140c0d1681e405506200070421010440625032110705a4032010710310302c2e01c0c1c0155440c403426170000b1002c070001c0c00100403082094101c140d4030219081c540341010303c84e1303072039500e08080900c80c048141c0d04900002c213505000003503805003145561061040e110381e80c95031070712034458a424030b0420441180342041c0618203c6101240d01e11100c8400d04540e41e00300d40f400c0301f881a10100c103005c0c00c21165403860b1805008080c141500500007540d484c0f = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 629993615 1250 629992365 629992369
    0x3060e070f03060e0c1c0b060417060a0b010f050c010908190e040506030709020c0106090212070201112a1c02010b15130b1608071103010b1f12020708180a09020304080306 75
    0x1c40e1b2140d61020039110400580a602c034400a00300814540c0f9032000240600d20f0181e003001d1000b844600002d01d4031001c20810b0ba4086201e01e40c04c03503d0300f40540c2e1500b039a01554054095180f024103030800c00610140d0001500004030702c40070300341c4c4d15038511300041c0c030400041c1c2d0419290f20b079040d4083c20080c44201c50301d60041000410410000505030b07524807000d42070760881030031030703081c40c0c55034003000801c4e9020302881c0d054540b00803c4a00c0d00140070000110100c0c403600d02096088422480002520f0404c94407034072040280711201c000c050b2940080c080c00e8032150560190345110700c01820a6881000d40b42108444520a181e80c0d04004181c9180d422811001d81092a03c51100c1c001c030740c0f298010310710540140b8807510104100303030a240c2980d0100350840e00401004030004101840b52040246a4003186803548122070380c04603040c068040e045004d01408000140c030134008a8001ca54081d81106590300098070745c1e1005407004901040b64050320100081000075118 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 629994865 1250 629993615 629993647
    0x140708060a03030f11250303080901110f25060c0e01090e070305091e0c0a06110a03080901022206020f1203070f120216030305090106060c020d020103060e070f03060e0c 74
    0x3c000706004541c0d0744400c030741412448420450310411903446c41c50003842031561159140b540404418000c0c402440c0c00030038000300d031145c031780724445004000c2607000e01c1c2c40c0010036111094040c981d1610821080342400b100520241310382c0004540d59480c2c0f0002540034002c02c400321842190703000940d903580b42007a8090400104803c00038000c007600c2e40c81d204941c1e8400200c40b204000180742c0542800e05200720b90704103402c20703800e22140410346014143c5c0041c07002c0019038149892801c1703885100c42e031406400f0319480185a41c040c200002a90100d00903107108803021507080300d1600d45580811a219580200120710007441017000038022802014814562001403800c0301040440075003500c102d0f040500001d5603420035030711103c189545402840d804c0045240200103042ca801c9020f800c40f8082d44009018120004010095a000780d01c440d004106039400b07014503152028005180215000c03030b420129181c40c00205141c21304003040c612542d442c1d403420345040e50030078000d814 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 629996115 1250 629994865 629994887
    0x20a080d0b0307120b1803190203040506040b130e09030d09020f0603180105180703020d21050406170f011809060609060603060b0a05040b030910140708060a03030f 72
    0x5401d4950140e100a80c80400c1500000d00152120005450780d03440c080d500c0c03100141904000b40f40c5514412540341010081303c1d107a50101440f003401407250042641180980d9210642c4030101080004448070313010010091600350400c5a40290344074052829041002c0d1148929580705001602c3d0144660f80b0840c0a0303030000f4040394540003a1000151160310850300351070b031211510b0b2043c0040200b40201d6400c85900801841c21203440e4400c01d07602d41445c40047d1096a5451542e81171200e1407840048000c0b108840001076041c0441c050f165501910980e00082c045201c500c1c040c102c1d108030340e8002c00401a164400b40d2034041042d940c0d03211800b091590719503c0b0003010004603070f4800c0400414004801160052808401804a0b032840e40042074090080100740003803513129003154281c81490140e2070312529201c640346d1409568000120300c02d4940380044081c4400100d1107842083d0b26030396201c090740c94005200c04c4810364800140403c034285551745042d0b00400720a01 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 629997365 1250 629996115 629996137
    0x50d240e0c12070306030303150e0a1107020303220b04050303070f05011824050906130c0312210216120203220503010c08011202210a110916020a08 65
    0x4100724002480d00742c20a001d03a4034501199581e1010401c15415009a80c289203081c90039529091078524100380c5048010004200d0b00d90344c51000444090030003d40f010303030b5005030491340c407038030085100b40031840102c282110905a988000400c0704543e0111400d803a40075000c0c60400700180e49194402c05d882004a030a9501c1d550a001c1c80900030a05030b884500811140c01c200c41410020801082d8136070f40001c11500f05000c004080c05c0020b00140c000c0c100c078200381c40b1101141016048421240c0000780201614003072102740c180d00c0400b54030440041201c000b0401043c0c010b01d4124816080c614000002428200d00400c403108056041c80c2160700580f49009001c0c00100e101a42d01c0d80010504440c002c4d041c0101d0a00f4803507040c81c8061410607440c2c07541420200c04034165400c40c024414079140302c0020400d00e2440014034400e61b01c1c02142d80c40d5a0b10726102c085821800076440c00381010030005250001d200c18040c110181c5c9402402c2c203541c8a4444e00055805801d41c00 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 629998615 1250 629997365 629997367
    0xf1603080f0d18210203030609060d0b0a051015170a020f0c060f06030703050601030f0c0308030c09040c2c0301020f031f0806100501051b010c050d240e0c 68
    0x2009403107a8064500c0b80c0c0c0704254080c100283c145400d070003903203010109a408100c0c150351401061340010480c2c0e00004100d1f045407582d500c80000610603848a940208240b002106105002e94560009809074200b000007004c00d98491400018ad08002c100740070009500820103050038403030107103940d0440d80448000d8a0903003804001d0101c6d501541030410b440e072001080000d40c1c80c01d2000190000401c80c0038000c500d03c0d603245c1580c0c9007410f020107440d2500c244e100d82d00300010411040003c42c0d1207590303143c482c07400341c0341d4004981012a05d40d003d207041408102c0c80354466094007009440a80040300c640058520950141076046030a0750150750030419660400a04400307144111040b0f82d9119503100340407104200d0746e003994002d0001d03900030300078810111080b0802c40306175002842d0007622801d0414504502000e44899800c26511342600e00404643c000010840701c81000d2091100e000403011b01c00c01c6a01150035040710400a20041c895150100c0405401007003006d00d0b1 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 629999865 1250 629998615 629998627
    0x20f120d02090d1407030c050a0503030304230d030c1707050d020f0d0204090b1305010f030308060402090d050c15090907140c0d120b0616030f03150f080f1603080f 72
    0x284543c441d0130300001c1219070020030100108031b03248080201420056440700321492801e00402c0d5280006000101a407804042c00b481310682c0100d001000000c1c0d408039007040700c00d10f0010307000b032086a9031900002c1c0140c5150030752494601b10f050240c1c03002e5650780c1c5082e00e61080c0c00000d4110001c0340c0c02041c0108492409140c1c1e42c0068006410700c00c5000a8514089080010352107a071108034403143e05080040010548031100102140d4050a1040300b80e0781d4040014005c0c400c29a035150711036102c281150620100149000590000365050300038100d85c125400304070701803803004a51019240340000d040070701c2100300401b030301c00c945c80071410140791908007810404109607000c0000d001001c3c003100c44d2000d0041b08410101a00e14900c0c1646003c4041c2503502e400034041d091140c20a01d2480f002c1c403d80c0f080743c1008442811008913030300c898072007440b100d40c0d01c11084584100d0400e0711080707a01040b0382494880002d070081003280341d5a034425045e00004d004a00c0f08809101c0 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 630001115 1250 629999865 629999873
    0x10060e1203031f080a0b010902070305070614071107210c0e09030306011701060807030509070807081605040c021903020106090f020a110c0a12020409060219020f120d02090d 76
    0x2c2c40c00784150a01d007012030ba0f1118600c03000d504059000c200c540c3c1c81440300901240c401d9640505442c02d0802c00742c5e130340301d003801c09403040d20510350f000f4815460803a0403540a100c000b2001d0151540d5a070303185c2c600008000859585a290080c15003202c107a011b070590340c000b980400007500d84922075242207a5610140b04548440c1125444016000002000001d6900c802316055011412101ea00c0e59410800000c009a00007080c01061581d5040880c103840c00070840403000349142c904540c5803d03280c8500580300c0090b0f1410711101440b0942c0440c0070300e0140076441e0410030300d900400180740c60a481344404294452b040d400c0d556156004a4060300307074010082c1041000d000581c1d640b40d4034a008207035640c22800c000c10364100ea028030195a03107551480007284c3d0f03041520048030455000041c010702045000505007440000c5540100040d104042c00d004425002d03034884d0b07000e1440341a01c038600395014440300c41007044040c400d2100da40c06060041000350000061021a0f55 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 630002365 1250 630001115 630001117
    0x3070c0902091e130c0207030b060117060d03020c090901020a030b0a0b0a05130302090c0403020306090d02030912190c080d26090c0a03060e0c0a0b07020402160813090e010510060e1203 81
    0x10342c84016042004140b040c2711004203944c1d0880428070f0544901d40d210001c006062001a10700c07071040c075440880c10245403007000065500000180012403905103940f10318001d60040350310790b0105e4100340c040702061401c0345072902100e285032801361515402a400304e4440c0d05c03401c180f1401a0380b03400b0200250711194001ca1054100d24000c035921415401050b14101c8014524021503004080b10b0310180e03070120076039900300001e035420b054440b40700501e035040100a140401d520310301d03800010b0a2081415000d0220b50744201a01c0c1450f05440c0d0842c0c2e4039412100000007028014018026100001066540110b0040980340d0068010000501d504419030050782d00544518a10412280502607414038070300403600544094608500c901050040002c0648a50b5000c1103070600ca8022824803280d042c1e0103403003166a14075103580d10480e10800d001d021541c514092110340401014840c0500408130800b01c0681c0078600700080b11990076403040d180d080540095440704440c8100 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 630003615 1250 630002365 630002381
    0x3020409290708130203070b0a0c17040914070c110402070206180901080c0f1908060a021e041410050c0a05010b0306060303030f1909020a060203070c0902091e13 71
    0xc01807403058148000c00030070301e2a000d05814011900c68091200590f4006215000c0342d40036140c05842d95182001038500207506500500060314601441c040050130100400c01d507591a02d0030014807480304141c007000b000807241240800d202e00d41e200702241c200100090f014800401c09031038504c0300c3d40403c025401c40000c941030140920004c441500c0d10b2140c90f40503004d03500003010341c1c6080030300244041c004840c8090041d0a002c64040030741c00c4140400d009400100d0858105041142c2c8400c000d6001e40c084010360002d000c0c00b800c010786285c04450807034140c0284901009000c004004000090f246401c0038400100100c0000d68014010061514000c04c000545182d0302c1c414142080da00030f01076071182c2c20800400c0392000186581a0300561190943c080240b01c5040c010028241e2000c065840120850006030596000000b000c5892240d1051074509540f0480c02e42a030080d2143c00d94420107031420b02403000e80f00000010396079401030400e84140349844000c0100c4011b8 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 630004865 1250 630003615 630003683
    0x321050c06281e0e06060a03020108130209090d09090204050109090b010315060e030c0d020303191823090615090328020a081219050705010509160b1303020409 70
    0x49800781101500d40d01c42e0009004131100039021a2500c0740001c1d050320420f002c024140450280410f1443d40382c8880404d00700c1d80a02090054200100e445903500f44500b40f107400118210380100d400d20307042c000d0310100d60042c0c440440c42420481d40c0006000407610703071810140c2e15141516000c2a4440f000000c21035a1181c1e184002d085e0181410a031400541ca40102a03030320740c02005880c000b00300c60402020020310746403840b4480084500312107c0c0d80010901606040c0403542914603512682c02e41d0070741c40400c032200350003021302800713a408550792a0700011003c198481000141c00401c84104000c060390201010030145540c0c0000603101c2500d8401203103843c0c411814003559001c0034010500051040c80f50440a0748150700c83c12802a581b00780a00c0c000c413a19005400f030301e880c1c0f40c1c40b00013072000d8030301440119034941007080301e070740007094080e4000f8420841d40120380340d003d0843e440c0032949080d9000d2001078000071100300d0322103e0341c0e01a40f1441403180325142d182c0e440 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 630006115 1250 630004865 630004901
    0x51f020a0e1e01210c020c01080708040533010b0d360611030a0b0f0a03030207290d0c2312040201020f070321050c0628 53
    0xe1000000d10049600c11554050000c040b00420b06006541c140a03284909103040a04c1c405038011220f801114200c0704c200d010b042c103d00c84607003a004038104915202c00e036205c0140e03548403d42104c69030005d0b176000d0100c1d0080c103d042c4140c0408582021001c0300c401c12904075456280d941055550240d115484001001c540740c070b0302c04414003805c00012481c0c130741c0721008100c405400000d40400305092000240c03481d602d0003000039540000380c1c500c0d00040c1050300c80c60300e8110040901006e03840b4511402d4403030b080840a2405503c500b05503505940188050350418410b61000344e100c407001c8101082a0342c1c802c1407800c4040081145180e07055000c07030200c00440001d4182030840420745005244040c0006540f130700701050b50700044001a031404551950700040c0e09200c070441c4030603c0c44c061001e0200c01e01100c090400c4840d500b10011525a0030480811200750143d054a0340a0350494804140c0010120750f0100d04007030000c6c070344a203011000107040e044030400c04680502e80e00c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 630007365 1250 630006115 630006127
    0x40911030708060a060e06010203160c0e040b060a0803040b0f03060d1e0c08030316030c03060e0901092001050a0c050712060e0c01030e0304151709010204051f020705010c051f02 78
    0x200701d01801c0c0040031074403146d00d01800e001d8000b0b51039000b84002c80c109600c41070480c0d81402070900041d0010300048059840d60b04041c1800e000000040350024090104640c0010309501c0000840d01220428100e250401c41c00840032905544003504072544045c4a101a102150054440c10a03008603c111540b0142c0c0d1440d1520001f445d5900c2500c40d9041881000100d8003130403000300f4680c0840c50000b6008400c008198003c212681220380322003801030070010112015404410703901d000c0e420071400300c031803001e0000280d42c02c8082c06000030b03828000c094031b06004142c0c02030054030a5040d94140b0b0381b21603401c2c0000790130316000c0d14080d403948428040c02c40103104400f101c020a11302880f2400b000c06401340d4a201c0c0b0301c21050403124060140131030b00d00c19503100c440d155190645008600344100c00d40e010303402a001d0340e445801c0c1200040100e40781100c041700b4500441d000b502c079003860440103540c0c1403001607007580c0c54001c0c144010201286584200380c0c13100c000c50010f840784 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 630008615 1250 630007365 630007381
    0x60414040e151e06090406020a050c011e060b0304020d0b1015022407090b030a0b04020706020a1b17030c0f03090a050c060f31030803011a090d0204091103070806 71
    0x80c0d6540e51102e40c1503c0105003d0103458041c83d01c0c0d446500403002607a00c0211070400c03146071060504c248019441e207070780503040f807524210036403103810b002c581488601c0e00e032403243e8006d102c20303900258000003a0200c00000ad640a03119030f40408030141e00c09100d0342d82c0d14507981d031482104085005822558032038849201044200484160030682d1001c0c621704950040c002c1c1266008007920150048000f407911249608265040d0030054002e648442c118035014001e50441c80c550708c00704a003c040280c0610080c1c841001c610b0300501000000601c06941c0300003603101400c4000705c0d4804011503605492840011401200c190000300009142e80c1003144c208058498500e10406080064100501c80102915a03c07450401060242c5107101c60000e200c041076540031900200740c1d0400014009550701442c101c0307481140883c000342220308505090f20a161800f60b20604202d01c0c0c4000d41010780c0072441451103030501c0c61850070104006840d180c280c0e440001c5560103001084861 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 630009865 1250 630008615 630008641
    0x1060b1b010c090e040609110a090e0616170403050403020411120a0c09050111071205072d0909060b06040b0c01110901020c060309070b030c03010303020c0906060414040e15 76
    0x21181e685401da1102e801e00d0007103042c0d410017070030142c150368643c4c481009002c2c0c1c0115800c0c1c9100014103408149623030340041c5025205080c4103503064090f040000360040c1d12460710441d0420950781d1350395003d0204201e0038075548041d100b43c0401034107210100051711184540b480c2001212400c585071a100006a003000304000c101455960416032160340c90307608010401d00785c50742401c00450085018100d185089000e83c40b80e8502030400808009000c00802c0035030950302551618815030580d1062007074083c0c1c0c03201d40386402407403080081004102030303808030381c040c1c2c411039000c1034078020755000424039041074002c0500700c4c1c000954071000410900c9588109030110320610b00b0a80315900207900d80c0f40030381086000c0c100020014002031024041000034140e56130100c1d071079042070802c0441a8001f400210302520404171750003400d18001d0111072040d50020505850b29003000c0780c031032507180c9017911243c205840b103010084110003840910030300c2c1e5001603141034510709801e103212a = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 630011115 1250 630009865 630009881
    0x801020304111f0824090c1905070f031b021302030907090b0307050103110c0304091d0115141c1208010e10211a0703060609050f0409020301060b1b01 66
    0x703010180458424250408140c1d035014103000c5c1300303484615a0320005814041e12640c4594001d41c008200040a07401802400c5241901c2c040c955207040656401c0d00c461189101c050f00004101a016000a210b020450020b8665064090158000d5070128003070840c481c006031040c40c1c01000304692402d0403c180c00c005d00d4003040902c6075090400c04a0388860ba280500c03410161580500004c480105086451140c8081d04407962185e0342c10300c8100500d40d10782004111f1038221010603180c00705001e0028105a00e81c152140c0c64030308888d10010b86195807000d9004011500d01c641c183c50303c9400c05004a0089140f0004814001401050340205030840c042404148040c040942c0c2c0140c10b4030142d07040b031183c00340201d242d03414110078050840c800500d04091603610300100c1c006800414065541c80c0c4050003101d40b0303a501035411500320300480b030f080102517030004002c0c9000d811644042d40080c00003d0380a451b800d50300d45640c007484a5422139070303510300c460351429030034424104 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 630012365 1250 630011115 630011149
    0x7060f02070b250c0305030c1c081303210608010c020304060519090906030503090103050906070c0f14010e16050103050c040521030307021608060103030e01120204080102030411 78
    0x28140c0c10505070b403006000740002c10303441c6011074511031080d0540360444904580c0000d1440d41c07003503a0346426603503548007901040c424012003079400d25201c0c480740d101301c10420603220a42c0a03601c90078440141c0000020a808101319110100e40528681c101ca0109011540b00030504604141034142540c0c0f60481c00c0046603c104401c01415900c4001d40b003240d40000f441c1c51750000c84800441f80c0700701c65004140300c5860310000108110000004088141003a01c043c051959150003481d2501e804980d13040121b9048030368000020142814564030520031402c0c0d10701e9a905207082421141c1740070500d816540314480001d41d1201050100d070082000b46014085490094034108040c0514451a800741070301c1d0419a00d001802a444140381c150311003220344074030309004002d40d1154006400040081c00000c0410044400318211741030380d806480303894101c175105d001101c045400c100e014103031fa80c0c00c2c013010500c45000e00045003d2405144007050035076940d41000550445000310036 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 630013615 1250 630012365 630012373
    0x90a080303011d180709090614060a061211131a0a05091203070f0602210c0f0a1101050f04032a02040f061a071214030402040c2007060f02 61
    0x701e4410a41d1458898480055440c81d441d140c0c58031301a007084004034800402d006000000c60130009580c0a21105405010180185a440c1c5805603803950305a685640000380040c052007071070b00541c01c0b0f10111032155000140b5403c084450000c07500140c81601c0c107880c80c0b0340c0401512040c2c010b4440ca01c030b18250080e1510480100140c1036114010099010710300700d0014008114017402a80c00d45500018849500076030781c50100000e510045c200b0b200091305028050201c800044d140f44124400fa488a1900c080b0703908005e00d54100c032480000b0881e0b91140709000e0320081c01024000c02801c00c0f280d005003050324000c0e041e03114101f0b43c90704050305031610f144070f064601ca03590803880d015940040d090500039040d2015042e503402c8101010001002c42c9034800d0400c004100f51805014180300303c0b013800e14100c0700c00c1c005080d038520030cc5003400450058035040d400b2803800c80c581d041c51300f60440402e0b003c01c80c800b1501d030030007200e4001800070032143e900460040101d862902c068 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 630014865 1250 630013615 630013619
    0x1080609070507020411040e0f06010906110a0609020409080a0c030816020c0108040302030d0c2001020301030b0f09010b09070c02010921030503040813080a1103011109091e0705090a08030301 84
    0x81c090700942c070f0041d21540d01c8403020301103810348a04682c00f8003c003107202c001c1d0f4500200300100c4860181e0301c00d80040e00383d02000540604c03c0b00b829082c0b4044101800800c4c4540c0c80d942c01400c2051010303039020765505c204000280f0381c000180130281c059190f5003a101103e00303000d481100024100b403000314191400d00304050b8085540131800900342045d410765200c03030078201d145010b0301072110f1b000c1d46441100403429401c0039a00d00c0821804050318a40c02c4d446c14414240c5c0001c3c44002c00308260781c00400c41d043cac3c100c1d174503550000000c00005529030600d40003400403c01901d0310804280c98081150565a00c5802c4201030942804880b0f0079040b0aa440b40080d507040c0c0c0040c0404c10080041402c0100c24022100d03046001030170142c04940b900d1500380c491030140300032103400f64003107120700203030406009554403980600d1619040a00420038451418001080c0c130501c01c82c6501c015640d421101c05060050f9119070b01d80e5180c8490209000b2000301540240305d45600034801 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 630016115 1250 630014865 630014867
    0x1050607020f0909151005091602030a0c05120a171008070b090103021611240403020d06090f0605100e0105280807091e091a0702070509040b04020108060907 69
    0x110b07000380082594202d10641e80d84201c1ca00780310789220b5a00002c004c0c1c43c02c0c49400c0040007554001d561040390700000540f9180090007032a90011460009a00240031001c0b0260091860080300350040050310700b03d004080b1208000c2d0312074000400400c080c4400c20702c5030701c02501041d900c0100d94152101a0f400e1110103540c0d5803091190b4501d1080000702c00c41e09074441e4058581080c40e060340e01400750250701c0e01032541d41060004a009142c42181c400402d40c02005030200401c10381c00c1ca030f1070241583c003130000c00d425000d415554591108a00700000e0171010392a88c140380918000280d608200e05548445102603022104017a40e0344014005a41d440e140209901c0403210342035803008805014038401a030b154401205805540c030009903d07855504004074000a04102e8840e104004c038a0700d0403100e0b00007014001801468407105440c01c0c1d4880c041d080300e854011203030002d6440c000070b074140b241107030206d490704c5403c4140411960001003042d040741040b00c0710076561429082c = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 630017365 1250 630016115 630016129
    0xf05060f01141e0907050d020712020607051303080a052203050d0509130504050f0a0f0c09140708041103010903030902090109021204110a120506390c1603120201050105060702 77
    0x241d054810044c01c0080380455000e0b030201e6030700902d0700d1425510b501e01421310009442a03441400050b005240c00203c2040c410303400c4800d00710000c0215004a41940ca81c030a40341c00500e40c110a00c6000c01ca420000000c04024240b80e40000142030300490646c40c000d8200380840f803614060040034031403040b082d5152200e5a000e101c0d807103000a40c1e40d54506000d0710380311a503c81904180036000b050410300004117103900080e0702881820301590b13946c240c00030480349000c01c0541200c01c00d00c00310f0101c41c03180496980150050701c00c000740c8020080024211410b691049000c680c1d40c559800c2103045c0034080c1c5005100c8883c0441c2404040515442c5c20400280004c1112540e8124800d140d558824100043c0660f08201c682c1001d462400711768aa405550744581944858010b0007441ea188048441c070003003800a50064080c10008401d05410841c106c44403030050105031200500c040007044011405140c5103000040c111350041d084450680100d4003650040086d00050386440e5 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 630018615 1250 630017365 630017419
    0x16052103150d06090b01080706030b060910030b010201140c070209150603070c080c0610080105090703120c030c0506361b0622090b011b030c0f05060f0114 68
    0x3a0b04088640628a8114010702d40090000d2500d81c10070000b0400100010348a0300351041c40d2010820001004200450750182d0160590302150b01442001028400c1d08000d00354071041c00041080001403941d14140541103c802250b07040c0452240c0c01c1d450102002500600d00719501e00c0003040035408100303d07202c018041000e00c18081e08840800800c001142c031052510f100303450f030b241080c034000403141071a0f204d50000c0e58240000b11326429400f2484404030703644850048400801000700f950099140c0005405000d42e00b03441c040407903401c0c01400c1c8544424000c801c80d001d000d07050880c4a0b0130200c0346019041b6841c0104801602c002444001c1500103119500094404000164207214400b40b442c005000b8544003101346041c144820305036580407900f40440311182c001140e41848212036100c0c0158489003020200b400b400032190100d000703083d0450416010344170b603440c0c9082980c05010410142c0c0040040d2680445a0b8134814400c841040d561030b4050300300f9903038003603031 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 630019865 1250 630018615 630018619
    0x41802310b240f04080102180f3106030b041a0405030a0525032109030903020418140c10050c0d08060a05130905120f0409020304081605210315 63
    0xb00d602d2a0a000040035200d44080d40c6080f290b4030341c2c84101c418042d4110340e103100d0b6030b040e4052812a00c0c0c43d060303104411070b0b0b0001c2c11080d050b130b9041d10000040300d107000c0b03900006220343d103120741e51502a000743c00185000d0b03510300305181420714000080241816100f140c004003d0280700000d90080210b074041d402c94605540c0319042500c04030301d841c0f00c4802d60321001c18581950800c16030482c440246400d188049030554034103002016082c1c54180c400140000c081603401c2c030041c80c1546c021482c1c040060b0030008100042d598500585030000e041c1c1c0482c7d44183c0d140f1425141c146055a90402140381c07260900003056620356407030070450104421701207041c000607120341710007260f03c0042100901810f407001085d0286c40c000d208601e000c1d941c5008030307404004c151401030200c6506c0034a0344005460710f4902000c090081d000680201c41e41c03d0104101e12112511301c010000d10ba014501070400310801d8a032121b070700200c2d280c140d902c00b402401002415948484258019281 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 630021115 1250 630019865 630019909
    0x230f0301060c0516030b0405010c02030a020c0103110903070641091203030c070b162a08030f180c240702030a0809012a02041802310b 59
    0x40b03183c940d003050000500c04155000010000052044030344035940500c0c0680007c009148052204a88910605441c80007580c03103008060f40ca5442a8002d100d948501d40c0200e00b030008003c0000d080c030481d540000006100c0301014000190401c5c1c401088083c12114507114400b0341c0b04481c1c0062601d40314055000010842c3c0cde6894803201c106c26860400e00c01a00d40c0c91030721855074521a0800003080d0b80d00c64503000002c62040c0030302064440003481b0340316040728090100340f0360403450b401d020400c1945200850080000c000801940c084d07070b84580301d000710345000b000f03896551503140600703003c643c03088081c05c01a842d181407a490f098240703540304203402c441c0100c0184d1441f6024009406104820300b41090020480181440c4042643d40d96401c40c00c4007180f00075521084281c49003503929503c9403006160030341c00340c3d52a203104a69002e401040c1c1d00011045030241701118032107100c6440ea138504070030708510300c25103075001e40042040a407040013103041002c014000581c2000 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 630022365 1250 630021115 630021137
    0x504052503020318070302150c030f040807090b032b020307150209090f04171e1201082a10050c10060e010b0309101109040903230f030106 61
    0x352940d280203040000c5245100d400d0390000008000303610884c0c184800700114680075a0300800490b07007104894009001e05807011400c1126021a881203080510920041199841c0400d044019000410b0104040c000032450124000113554500888a119030800301d40003810b188000c142204225036501062140b0504010a038658071803500e01030845010080d8170420701c0c0c00c54005009006066403c1140758984001c0c0b400c0700c0070242e80040c2050709000c0100b9400d071185000c7c0c61200344190300d902c0c03461240d0a980110341e024100400b03813501d0400c01449a14802c21260b103410550b0352085228054007450040500a130315030680c800d030901c80203040000d2103203083e2003240518505545048580720304800080c00c032441244640030140300000752040e0144103603172051b002d80c406003d000070240c1d4014010003d0242c010100c01040c8012580c6032a144150440039120380c9401d0307000e100c445415034610f01000482204c000c000c0080380c0a041e5518140c9044409504003542004 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 630023615 1250 630022365 630022381
    0x20a120c0908011401051201020903030f0d090209090109170406211116111f0809100606031a100906120905030a030b09070914060d0e060115110a020a050405 69
    0x40d10aa00c1181d4660030050a07144c4149241c00482c100d03075003154424041c4124120301401e0340984603407a41d058105000b0a0440b64208004040250382c00d10005495920b50780014520036082c1e411205c1d60703644400312010005001049034012000e014054207061800390014017800e203083e064840c0d656984440036207050160011486451035500aa81b20140c2510308190203042841c1078610303007280e911440107070902050052101d00c0d1494045009103a50f00c0540304400040c1c901459442116400d81c095803651040c280645055a008605112110b0f01c2018013264007280d0392040d00d04500c618203036030b0844840c42c00c40d10346048c030188180070708080000070441c144020380b0b45c2c00000b0722096142c2e455801640095000c41d03492100d5210210700703c4605040e030041c2d5015086c1e00000c0000d44c50240d0151481026030744c4042582c0086020705400c080c0c0030782c881246000192010395845400c002031642124007500107204000054002841c0c0490900c10310f4000ca41d6440030503142 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 630024865 1250 630023615 630023627
    0x1110706030905030c070b13060512040f02030c03150108010c0513060807020a0807241e0209060d061401080601020d0e0405040303090f030c0209090705011d030a020a060807030609020a120c 83
    0x10b0f42140d800e45080d155100c80344c0c24180d00000700c0b03440e840c0b802d050208a850242b4140c0320070b0f000f0a91342500e01d580d0b9903101c095001d60322100340e82c148500e01d00e8000319541082441c060040c03ca0340301c80300d54500b0040c907003541d050044080511134180f00c07041c80101b03142140c500b1903206240103060307900e41003410b1b4108540c60b039018107030078800101c0703000344003240041c40810499190902d60240150010344100c4001c00906070022030900034880c0ca1031501e401a02d0300e1503000f448207103040c05403150082111110340c0070700c10070301216803402420741e00022442d500800070300160105410340240201342004d1020124482d542d00d2011a00b40751081d4042044107a10140c805800000c50070060444901580100d01c00c0c22581c00141d40544041051030840307a040c0c441e021403041c0c507a00c0c50041d00e1442c45161300740c42040d10340c01c056640d60303400ca00240101e032243c83c07081c00c00003070040588403d900a96003084c010461002844c0d0300101080b403c002d005000203003c6d101550403581c1c = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 630026115 1250 630024865 630024877
    0x9040c1e1a160b0103050307031704050316020f040f0b0a061e0c03051605030c0d1d0108150d080d0c180b1b100c02010f05040507031509050a060207030e0111070603090503 75
    0x3c4070703071800402004000002440c0380781c0640c841d01c034800600b0050360000c03c421180140103410611070f016640b00d01507002501c09200401d80409007210b20085012240d10136074441c429600d0300e0303118403030b410480120805040c075803034401c80411403805281000f4820786031036010800880400e43c1494030031402c2c0c400c00d280c03184844402c0030540c14550b40e240c04c4000d5807121030140c0c102034815640100011102c0d401040d4030318019002c0480103494600c00205210600321801d0f01d44c0d5844da841a100008107403090b801c1549440d00c55540c803007219030900142003400490100340c003d02400d00e0000701115001c10100703544065441414010040c00c98041603688941c070b000722084245074002c0010381c000d0794001c110b0303005500c0385801a00c1040d01c0207001070304030402c144041201e4045d61800c4124650010031000010ba440c540b030405141d000761042540458840e0400d6030126554000d1b1a00b4a42281144096074440361250080d00c01c0c6024140e940c0701c602e00300f010078016507003 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 630027365 1250 630026115 630026123
    0x20403081303030f0f02061f08070b041802090a0b070218040b090f0a1104020a020703050604030801210308070806030106080f101d060601120b09040c1e1a16 69
    0x34480c80651030004900090b400200d011903015100c000025100f90144035841c2c200d5070082a03251155090214204000705010314030045000e400b00e03418108001a800410540d000503035654685003054030100c901c015900141c40c01007007040c019540348240002503074515100700e0f94802c0c031781c0700280d070304400344551030390040c003a408200622100041c154072410550003507070140d5060440c11a00c8121a03440281307150f039901c00e50344550505601518292582e0300485034501e0b140c0c0c941d5858000b0417141200000c0b0340c600107124006ea00e8130110203c20303021444200c82d810710b40e00580f111800071301050804c040f01c000160999805d4004000a04032141582c403001480d052031515280c524419003461403e02e220300c01e1140e880340c0814440c808590140201d030b100d0400440d0361304003603803031030802d186c07100b5950050b41ea4801545010f0762041c90711049103803410611184c00304039041380540715102031004000c80c588264070021040c21034120341e0f5a4401005000343c2c911080c0d58064 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 630028615 1250 630027365 630027367
    0x17341101030f0e0c030d03110412050a21020d050405130b1906120b0910030305070812130210090503070b07080c15072a0204020703020f24010e0606091302040308 71
    0x11410808104c039680c00c2820b80aa54071140006800e070180c5010040c24801407c1c10481000320a0524413a208041c0c4124191195a805510380740e080b00d068904c02d1b40c600400c1001c10340707842e0b010082c400ca034240c00e00701075041c07920746030001e2419503001c4001d002c030b03039191050000396540d91034070713180c1000540348210041504c400300201a1041196882c608502e011400c0103c2d16040d900b892140e52000240c01030780d401c603501240d0a4200590446000c2018041c070400f00d4a00d16103203104440001041c01c881940d0300403c2001d030740c00e607500c00a10940c000706005a4402045000540360341280b050340c3c5030051f14010440e403040300114142c500540c2c0c0040000005080000c0c0211411303178858114046042c40504500b1070f2048401c840c0703040d0000400182066005030503914005d0050740d1001d40041d20080c20098540c0703500c040390340c0c201000c0c2000744400c08414050008040b48248038902203021407134503c00c02c21454032564440c8038004009450307070100c40245a0103001c0c2 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 630029865 1250 630028615 630028631
    0x70807080705040f0e0303060607030c060f0c0f03050c031f0504062606010501090e090309040903111e0c01051309060b04030c120b0c1617341101030f 66
    0x241d0725150607004661149003440740c0044078520b14000e100403100c0300c00181d0320716161842005501e0b0310150044040c819444025008105103100f06400d94094103008110045a2000140080b60003082c03c000e151500e414081c5000c040016681c1c0102d0281c4122481c0001d080c1010040720654007165005080c20000700309200046010f04207c4000487c038500c2d4510a0070041e182c00c002d0103400d001071301c40c0b0001c08c207240d03041c0340c000d82010f001c40550746420303030403404681078031445030054000c10030600310b00d980f42d4010031400825201b20f014000c600e940400d01c1c90b8607100f01411080c10018040742640c40303080c047d081c140c01040381100c104980b9079244001e24445e00144401d4500c80042d07400010003110414900102d0740c1d11039a901c1c0e1942d10890b601d59a0b07088001000ca2249848034030702c00056990412102a00c00c984019450340110040303140c007040c10569541c14142c400f45250702c100c040d22203116071154000d070000307000305002c80105c0007002c030081d0f8642c40c20b0801c200 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 630031115 1250 630029865 630029879
    0x80a050601141c05090d17070504120b04021203160b1f2405180904151805010e01060501090e0903120726100302060d02040b1c06120f060c02070807 65
    0x40c841d080c041d1507009000c65900d00c18417035102c0c3c003030300781203008a030a0b405031035240d42442a605a21580c0780c20100d050a45070429107180d9913441e007049403011448414041945407108100554582d440001d614180c18410b401e0100c0907521001080c3c40700400c08900300030200141014101603c082542c1c2c004da44503100c040b0701026001c200d8030045000366030782003188101c00301c030005283d14845034a2502001c09009840d40002c000741c0300b0109940240d80c00428034040e1100c070604010110304002c100307080840c2103440150380400c3c2070307240040810040c1d810440080855240400c0c03c10181d6908038071900394410340c012102d142000341c08220000360004150040c005040f24000d03541e640c00741c115064441c0a0382d65a00700780050504100614088000307101c10300003c035001d8142130740c910715008a03400c840030060220703e00030b0f4801c6c880005442040010003003650401000709a580321401c402c3d1615001500d49031b2030320b402100c6240200800001005070740e08841e09a980c8100c = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 630032365 1250 630031115 630031147
    0x905010f0b0c120324030a031e360b0304020307060c0525080d02060106050d0905070807030b0f0c0304030e0f180a0606020d030506030304050405041515050108070f080a05060114 78
    0x5d035540749060034500c00d2581c10000b50814125034140c9480c041c4180c0c0d904039280c40701440f80d2440401213032005100a02c9244501354100c908085021b0911610068468203025a180c00251492070284100030250b03400084520489038542490000c205003800c0040c1410300e0108003007240e10304442040300b0990302c0c10400f8210b601c0801502c902c401c072290100e81340c103801c5c400ca030300164007403140c901c5018481d88091404c41c410021034401ca9600c805843c00d20010740c1c015a030480180040161410f01c0c03408075640011801c0803180b562405030780152580000c0c03100c243c050408003aa104031511070340c000d92582a5503c1c2055014034241140030042c01440c0104401401080c5800340d0480c0640662802008000d01540c2400d04080620000744402030041d00c2c0020340b94803018030302c0ea0714406c03442032040c80e014a203115401c0100140c5440406019901044090100f80f059154001c40140e023048410300c2c0441c258981c6c0740121104078a00765100820640002d03080b0b10069908 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 630033615 1250 630032365 630032401
    0x1235070515060d0b04020609030a06050903090406121a130609061a15090d0c0509010f081c2f0d02031e0306030d030507090b0c0102030403090905010f0b0c1203 70
    0x804504002e699610a000322010301c06002004028040d0110f401131508902070014400c0103821078242103403d440d00e109940302912580c004e5000020b92005a052600a1230701400d031018032002034504da641c81034603014080d1010900c011100c3c0204041d400c1c43e8440844080d0403110500c91180130741880802441140300c400714282103040030045a041c000300202d80c1c20034021074181401c080c001480300340307074800f1402c44980b440c0d150081030f5a41c4402005011307142c40002844450b09100303280c0d02d4015151007150a04c00380380851600c0c02c1c0e100c940300302da42e00042440c000c0404030001d41461180d001615070b016009003598808484d070700001512002013050940040280d200c41411039074403069400d0750b05500311200c0400c140e40030b5004107801a03280d141000b9203c1d5100c1804640703410028800e64680d4001082c4014103a2103d1480040c028a4a041109516116120081803280d00c42c0540513100810b66407110311040c82000d1404030580525541c0c2c2c40c00962351581d084400e = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 630034865 1250 630033615 630033643
    0x106090c05032e0603050408070c06090806220609020a0302030d0302070c120b0609130c060903063e0708030c1213080a030e1c05031012350705 63
    0x122079642e81d0030f9910a040d2401d030b0303840c828010141c0c1c14801e00324040c190040050f122000c04000402c000b45403440080c0090070035136184001141015111070a006c8050032104007440740f00050844503001e002c0c090640b80d40b1010009000d001840440c00c182030b00e50020b50325005040d50000c1054041d0000d01040e80304103543c415258a076810107000d29036551000e88036130010000904181011607030355030041c9032104a0342c00104103aa6020410045800c41400101c503401c0c1001009854000c10100f2200c40f903240125007030701034481240102d00301d611220960700c0f0b01a00300340c15402d42203030b2215401450036540c0380f4140a0000c802d6001508141020303025200082c44a00c040500b249040c1c1c1c4641d0349468040c401c2ca0480190038500021106400703030030319044881c1d5401e8000010045580c030341d00c0c1ca03454044511418844554001c04101c082032800f82c0004045541c0000e4118410300900c00140c0c03120810006002d20b8000000c02c00000104c5c08244200050a83c4580301c030 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 630035971 1106 630034865 630034891
    0x2d090e2403030705122107020604031d0603090c030f0a111003060e1305010501060e060f0d020f120406060b3c0414120106260106090c0503 61
    0x2240c007010040d100006c07001150b080035043c0354400050038a40c046540b40c40c0130041e403a400d000b800101000010041954504840c80421103030202c0900030b15103e10303065030220340d40d1240c0ea28540c4244034021021070111800128100460340c018041d001c0b000c00310313044c4540e4001030a00201030649504001c1109420f000c0c50f2446a128650240e4018001d410098211901038004004101d541c0311002c429031585421108801c01c5080e41072303600c17400902084001d0162000034034010800188000e074000120301818051750141a01700200d43d520904014507104010100006981550034401c0c080c10312420420200781e042507100a248500e41085820382c03068001644885107240c02c13120b1800e184002c0c0b004020000020032880b810411200000403000000e9144003444036a460106002034012200030400c58105124400c1e1011010744241c0045910562142c0 = true := by decide +kernel

theorem cover : BRFrame.Cov 629856115 630035971 := by
  have h0 := BRFrame.cov_init 629856115
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629856115 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629856115 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629856115 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629856115 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629856115 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629856115 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629856115 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629856115 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629856115 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629856115 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629856115 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629856115 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629856115 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629856115 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629856115 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629856115 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629856115 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629856115 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629856115 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629856115 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629856115 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629856115 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629856115 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629856115 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629856115 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629856115 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629856115 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629856115 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629856115 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629856115 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629856115 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629856115 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629856115 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629856115 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629856115 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629856115 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629856115 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629856115 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629856115 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629856115 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629856115 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629856115 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629856115 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629856115 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629856115 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629856115 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629856115 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629856115 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629856115 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629856115 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629856115 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629856115 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629856115 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629856115 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629856115 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629856115 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629856115 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629856115 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629856115 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629856115 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629856115 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629856115 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629856115 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629856115 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629856115 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629856115 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629856115 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629856115 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629856115 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629856115 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629856115 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629856115 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629856115 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629856115 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629856115 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629856115 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629856115 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629856115 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629856115 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629856115 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629856115 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629856115 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629856115 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629856115 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629856115 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629856115 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629856115 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629856115 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629856115 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629856115 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629856115 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629856115 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629856115 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629856115 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629856115 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629856115 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629856115 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629856115 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629856115 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629856115 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629856115 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629856115 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629856115 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629856115 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629856115 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629856115 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629856115 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629856115 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629856115 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629856115 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629856115 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629856115 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629856115 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629856115 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629856115 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629856115 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629856115 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629856115 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629856115 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629856115 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629856115 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629856115 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629856115 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629856115 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629856115 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629856115 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629856115 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629856115 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629856115 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629856115 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629856115 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629856115 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629856115 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629856115 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629856115 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629856115 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629856115 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629856115 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629856115 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629856115 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629856115 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629856115 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629856115 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 629856115 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 629856115 ≤ n) (h2 : n < 630035971) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
