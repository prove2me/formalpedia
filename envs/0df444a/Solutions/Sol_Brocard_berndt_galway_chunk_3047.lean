-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3047
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:30:14.627607+00:00
-- url     : https://prove2.me/submissions/02604bcd-19f0-407d-86bc-d786830d97b2

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 547841726 ≤ n < 548021582 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 547842976 1250 547841726 547841737
    0xa1506091505030424021c0203150f0a05060904090f05030703081506040302010e04200c070b210925080606010306080d0c081213030813050a0b13050a0503 68
    0x4071003104400c00d03155042c0ca492000742c4002d040d038401c0c1d4501601140d10080300102c042003600002d81030000c0113690350341c2000c0c0711001c002881d4001c4104058102c00785140418680105d9152070054905c0010916080503402014090480050b0402c515103ca80154040540c4004034403180041c608000351281c10005044000034000d00110700c0e1582013aa0b180f040000083c006490301349582e00549480c440000090340207900d410380280170401c52403048803031014403452a40c0c0d85004403161401c1c425103403c402d42644042c80303d0ba0700c0111180441c0380010010b00030b18100c1c0c0340d8845661408003283d1500804100c00218840e40941001e16601114900e00440382c440e01c655006400740c480c3c901035882c040e4808141413400c0c81c4100305100700680281c03145881e1482e40c0c40c3d40fa9042c2c400311114090720900c84080360400d948040e429602000944104d54013041c0c645e600da03126801d00f4800392400703008101240007040d0580c440010f80c0e0b40f0208548141d03009141290b288d4024 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 547844226 1250 547842976 547842989
    0xb030604240204060807110f10021b07031101030b0a0f060309110f18070306090e03130605130519050301180b070e1f02070f03030c05010c11150a150609 67
    0x20150242803044842c000e58054600c2c54070f611600d03a41c1d40d00121030300b004071502c0202038400c01410558070407050142d18085c106c40e81e0050381d18815000f00d07161400c01c11000803880d5100300c40400209d010703008403015008003441e001c1421801c0301c000503040e428541100400f180315810000c1c01c260142e010b10109442240d42181e4840c42d1f000300114554038a040581083d65500d1307100400304c60b00300e4684d00c01010b08000030600d44594450b0101c40001d00829041d0f800001c001507046005c880c0080200414903200c0c0c03428810801907081616244160340c002c9149903200000503140b0352213100a840081e000b04000341648124141081c001c5009541d40042c040200300711a1040442003105640548003109002d02d4036005c81007000d00e00740b20300460080800c0402c00300218400100114080d68030300c4006403060925500316240324113400e00303201c4134580d20b24a0300d20103d205071804450a0304021161b0b647d070a140c010700000d0414069040110801040e4550010f201d101615076 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 547845476 1250 547844226 547844273
    0x10b030f060f010f080a0e010e031c0b030d030b010c021507020f1f080a230a0c020604120c0f0204020c1b041521020d12020d1403190b030604 62
    0x141d001c02e10459102d540c400a002503100400f07002d183e400303002202e40281246900107041c1e002c00d85002d0031511194030300c80c00c1740c10008030310750500c4482d2000b410920344440200040078034540000d0340c40100020440c24551550911100fa80c0030b03005118440e030b00035000c5502e045505050107440da102c0360040f40310b01e03034410003c803480c02c000038044403000e101c461264400d00181000c0d5002d0400070040c078092078481011505006000000704000d0200f55890805820032050090035207080f6901d040071544100c003008040303075580e51607481c160b0250034034807240c60082c2061007031100400c1000c1d40043c0005428a0200000114401140c21042849020070101e5042005480c0041030501500900c404180400f052000d014203a400c40b00424034841c0c001c59011441ca06daa506041c1c480480204112403c1038051000c00c56030b4080c0e182040b800c4d03038030700c0e5200210301000e49508d2182d000c02900c5241800c00e0f42c01801880801030480e042403620b413515034011692a200100da402 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 547846726 1250 547845476 547845481
    0x90501051e0306060402250605060a0e0402030a020d06020c0601060504170313050609130f0c1707080c1608070f1205070c0911090d0308070e190527010b030f 69
    0x2082094000100020301508607601d91004105c0a5004084140001c00d0419500c41c16035802d415018401c40c400c4402251a2811303c08102030301a9035405001001d001c0b074200300042c2d03804210124810f82c126200d1000c9401c0341480301c0240a81103040d00148220000410095040317800b42c011100000442c400d001d800c0b10001d501c900a4000e4001c141190301c00a11652521401800100e10302920404070440d2119400080d1103c0f040310070310240d0303110f2100b0300325540302d9401c01c0510380071280003d06081401340184030384001001c142954001160780d2061800b0f03101c160f40a65046031110b6220030203410f0801100c140b04000311000c0d18410340e01c2c0c009a01690545820b0f40c1c0040c80d050a251a0012500c083c010400482c10b00d01c2040100c4901503a80c00b4032410b48501965803850540303055540540903060072545107200d001c82160029140c8164060101614020f5444d5801ba60340740c00c150107440204c4005a2403585031034004105007105101942c8141d02201c40c0304802d4 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 547847976 1250 547846726 547846759
    0x210020d1b0908240c0f070b0106050706290405090c181e01060c0f050106090f1a0102011104050f0a173301050d02010e03030a050a020f0609150a0608030409050105 72
    0x74904907036104c415200d078000604020b0340c07030003601d50b4038038101c3c6141c42c11215640d0381015440c26000a40400c0001c58208240704840c400c0c84140928002d0f00c40c06800c50003001e9100b40e5200011611464940d0005101210203120454050306c0242040c010f604d0100020300741c0c0710080b9845150b0000703040800a40740c5000507814103c5a0b0f03900c0302c07075950703156460746604c1a1040348140e41664a0346400601500b9510610404c001245000a0101c0b840754a55a00411200e44181160b0610f40c032001d40300c02060440f0100c0e102218000f5183c503854001c80c007101c1059202140c10b81c04000c9400c12a00b001c070340c90809024403614001300141c108280f040e0500002600340500e61401d00600440c14001d00040c005401410f0014841c601040001c5c61940401c3d05180014808216091900d40400010709400c0980c0d026050510b000072009540701c0c400241009004408401b041501c00103502107405400108150707aa60b030340318102c00c03010304002c0c072032103003c1c096284004500 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 547849226 1250 547847976 547848013
    0x50a09030507080f09060d0911011d0f240306010f080f0a0b04020c011515030b062a071d2410020c0405040b0a110a0210020d1b0908 58
    0x805a00d9210300b07007810b0403a210007105401c0350249607000c03a41001100c00c2540c444000d0040092507000200d0003062a240c03c11040c1e410f80c2c412414802d1020b4103c23551030718100e030b910498809580c10491048803c0020300307112990030814524440860031203004164240040d84140c1080e00c50100d209844803044400d940704486502d10324500300040386040c40c568110b00c0e0a20001071025043ca1144808039007194107065034031140342c9410500f00300c410070030342069110031013604080000541c01400308115104005804520801d00641d03442e00e001c03200c42000710108400119030404d5107903180c00d00d119070805805a18032070500001450f1156002d10018000c00485001102409050030b1108010072180d4800650180d4030841420351200d03c14a4440d50241c0c0e00740300326003000d801210886121222030101d5001c20000c10302c03d1500013440c40c60000c80c0700d50040c2e40d070100326601e000801140102e09051024241c02c0104103510508001c00e80d1400c03029100c000c10301c42041d110 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 547850476 1250 547849226 547849241
    0x20405040b060f0f07020103092f0102030703020a0b04170d02030a0f05090a030f0905040903030b09090307020d0f1a01031109090102040f030f02060c030429070c050d14060109020c01050a 82
    0x44248100049125028450045c1c55528410b060100b4604000d94901c070607190980e880c0701030742000550271605810340560f041501c4d402800510b241442c1034600944031320041c200501480001004102040440178041c4102c240300005262500b200121520180d4400c0d541014210309003a40f0309200c404511409000701e80802c018030240f9003580d0240c80701501e49804400340b00e0858400140360700d4501078415103a1085da000a1a107103c1e800f00464107801403c40d00040d030080c803203480140c0340c0c4100a2180c0c0e070070011000400202d481d0800442060381142808042c0c404000010808445090340000c00d04a51000e80c030341e509000c5070700701d025a1042c500003103902c1c10301b0008120100c122080140c0003400f034a02d00426003010a2466202c0c0d44134141100036401200200700101100180841e5220549807030203005441d0401d0070100b90180c948039216510744441017111840341301b44407020090a844403503030350b420310900a4118800e00d40c2c00d5402c00001a8402100784910903 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 547851726 1250 547850476 547850497
    0x120a05060105031f03150b0a0b04030512162319020f0402090f1804140105150103020d09021906030b0a0302100c2303031b1207050d110d020405040b06 66
    0x181159950013980c1144400b0165044210b800014084082095500d028100250401001c200c02c2d0b0464148622459607a006c10328214040c841880043d9001c038503076203c408a50f00040e250012641d500c00604c3d00850000c05034030a81c0b840034288642011499113580000c42603444c0034100000705400700c1d00700f00c0003d41c0f050056840d48075520700303940070b400314a601402c41d0000d400910302088a40c1c00c0c0e502041807c0042104010402c0512800304090840c003500074006418240e42c024000110098180d0503d90080307050000b902d480d80c40740c8901c1c0e8005000c1e80702849400d10003079805456000f110f00003800c100040040742081c4001030304407540039080199401600404a400082e02c00d411192281502100586203100c400d07a0044808520042d6589050608185800902812403003050302002c1c40b00c480145004010f0030381c440d1090500d84c0d52400701c1003880c4c0080c20922090003021901050041803141c2e01d074040d1055800a031400c1000e000702000b0042540913403400340 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 547852976 1250 547851726 547851737
    0x105340303240b0f25050105091903030b0d02042901021203060405180f0f2a101103161101090b030117150a0f1409070b1b01050903120a050601 63
    0x20001e402e480720040401316640308450b4200030030b000194a41e041c2821013500c41030b007400300d10b9003809028803445070070184510042071000c07200107030846c044103151405002e159036502040741c1501d0350f024039809a03500420421071030401020107000d203002c107461550450034081011400d54000140170f00340c60000b44280d4150380d20501040082c00340100010a00c028005607414041420444078182c035182001500680e0340c407004240c41c10440c154100e6028440c0c04885003800012103400000240a03645c0304440b10642c1d00645d82c00207410004882072200182686240b40326141400d90305102c0d08107601a0a004001110b05c412a030044500d00207041004100745c81d1140b0782416983c0da203805864161100100d900f4001d00d085540f4845070343c03144030015101003a03100e079400c616170303000c03a445130f508041c003a440d907458641c000d0716080c0000045c000c2c3c400541d0306008011508040c002c0c0000d00d440454191282c00821148400745c000d24007141d03041083c2d000d41c900c00e01040e9603c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 547854226 1250 547852976 547852979
    0x30309012d0f090f0507090f0b091501180f0501020c030f030f03090703080703030f053d090c0f1103090906150705010501030b090f060114010534030324 67
    0x844010415061400030b03a683c0c4491410001d14441c4000d5480c500a1000e402440d182281c1802a540c180303c44640b11840c10441c452255104a0303242e401c040c0c2052415650201c0f5001a03519118100220b01e007003551510024160703a008849605443d000c1e800d8543c0d010b0f0200500d82c0d51408111404c1d2103800a20a14946066800186521503494021500115644d03240c4c0c6075030350f000b107905074002510f5040705a917080050007a00d40080712100354656a652420041c01c5400f0869080484031784050581d10450322803200c48000303003c2c1504100004402c003040640750303410a0b54021f01064681143c52001c150100550b613141c40301901d84004d0750303601c3c0c0410240c0c1004011303902d0649010312011020803c02d204d8640a1486480341e0b0086040654116160000076192890a0340c4500e00500034400313044c03900c0ca201e220038280036032580701c14000e192080c500960111138001440641c921a08160310718289024000d031001c01480e080e0440b841a80300004031038030701c0050f401c0b80 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 547855476 1250 547854226 547854311
    0x3030907140a09110909060324100b03010807091d0c01180905090a03090b0a020309040e01182f010507151b020304090b060406170603150903030901 65
    0x15000740e1824000e101018564071042c2d140111200800c0d40b5416901c04200403486051a172100b64204004a009004105c5441e54509810480b030800285001141c004120308424070b500c00b0000d040381c1e071012a120f60f1030300381070303565030401748074030300b0064284030101a80036040e4140801000d052000b92140e83c030a8001503815082500030400c0c454034028000401c00c0280c4a810f0241000c1805004098160b050003021050140c0124809110800c0ac101c0c6803600003088551252054a000c2010040100601c0c0182040034500208904140e40c0c00100a0003130542d050a08504c0c12150807001100b882210100e102030712640443c40030040c80e0017203100c0212944015400d610003080000003600c000060748141c050010143c0c0c000b1070144110b000f0303030107800305203501503c0380790504d0714101c0c0c0200f4030b503400c0010750740407010351011401507101844102042c440d1007003d10b0060800c103400340d0340da5004440f45081546412042400c01034a00f112060341c00c0080c0000070325000c20700 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 547856726 1250 547855476 547855499
    0xa030203042405060a06090b0d0b030a02040e30030105300a2105031f0b030f0105130b0915040e1005010321020d0e0f0406080106061103030907 63
    0x30300640c0e952444140201490003240001035405164000c00f10702e07801d05000380001c101451b0009030a022601c1801d02080200c2019a031a42401003008640c0c1400f0380003090400e00307079010194010b42841e64201c0e0b076040024011030090b00100d4500300030200581c1880c03922010240000210030100010801442c0c061074900c00d1140401114000301001540703c007007041490414580c0d030b0001c6902000f4800368a45012100000c450044580c04800741e00400714440100f001d01201e00a07420809445203040741000a080919011070f40c0e070412079034000d60601d007445498414680c6510798003a00c1414082d810254602621094650700d0300c6020617001c2000f14500b5401980d12506100780d0b00d4200542d038500701416000040a50550901d140d0342c0003031108000001c0240c0e40440c4055a0000e44c0e071081c46000d15066080385104800100940780340074150794803d090843c0420004819440442110881e03204c0c01c90103011500e160b5103d0200b10b404c80c50b580c000b06403c000c0c607039890 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 547857976 1250 547856726 547856731
    0xd0203090319060e1f1535010c0504030606080d0801060302181f0e030a032f01051005032a04050601090e04050a060b2d0118060c0b06150a030203 64
    0x100700209a040046454505e03002d2513500e07000c9604050020b03480710140c2e621075107104c14244a6002c030b03071500741300303034074103612000d000303040e01c4040c0d4030261742c40c00f80d1a481580c0c1c2c1c0185100203204c000d1011000a080350002d0200344c80c01e83c60400300281c1c240b0001090300b262641a2240005a80f070908203030000c3d0010b503a086038892101211100c00d82d1410781400701a0200d96a40c4800071301e0030401000384158445040c001e520590034500465000340e034030074001010700352941d007854007000d1400580901c810480025804c10050000d40480f141c4090241d03842603044891072103540100c15004480c03480c55449074a0380081d0882030307080c40c0d0806517002e070301030501c0c0441c103030380d00e91500304000c04a07020382e050707000311292204109450066110814045848261074001150910107140345095103c00c84c00c40000203501076401000301c14801445852221091599071602911000048200715058044840007500c0341ca42000c0b6804c00050942c800380c02c10b01c2040080e0b00a40c4003 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 547859226 1250 547857976 547857983
    0x7030f12060506070606091103010e01140a1d04030807080c07110f0312070c0503070e0f07020708060c040806010902071101050f0d1a24090f010c05030c07080d0203090319 75
    0x1915800b01d516240d03072008201051142c0d800180ca94a442030355805c503503004810100402c41040100030035603401302a241503a003450345580e08119110001003015200380d21114a001e10000c2e1705d8840150502610710903030003a11070780c01c20395480c141103910f080c04603041424014184010404a40540003640c0101006000f41c040301003d00c0000b0b1038001030b400002034038240041c060f8100305603800c220000340815001803d02505240c824403100c04020114036500020800066182e44208822001450850141e40b01c60030600d000303070426803060054504a111f082c00006103030b14244221908550081c1c0d10101ea106200011144c580c003061507501035020a0126103d00070080c4185081c1a010381400100c0f0400c0c1e10a1200824040c90006401e41d4402c00d442d03200041e800c00c0b9050040111425200d0300300a41c01078510b00d10b50724000e492884007103851540c011000840f9070566800300200c55181f5100c1408990340e108140c00a9050781010001440d0241c00d0380190165920 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 547860476 1250 547859226 547859231
    0x1f060906111e071e120b04060f11190801030803040303050720101a092a0f0909060a0303121107150603031206031e030203091c12030207030f12 63
    0x2e0081c1e0088003248601c0085030307103412002d410840840c40742825000384503a00403144186140030080c2403d400c0900025044007110000182080741c50383c49487d19440110080155200820428445070051003820b03000003403003099011505c0c01030b0b9150341283c0d81b200315540b03155600c1d58100c01400740644100140940380c0051312240b90b000f5207860030741d00c4840c0144926856041d80c2c1e025a090903101300c2c1c440d4408541c02540c0d07200c592032942d00400c24000d80741c18003001e0312039940e1a11047c01e81c402100001ca02410103103810700007050562000c4030036040300d0700d4503c204a44008688002000304000700e2500e09524000c0d080400d18015003c11141050000c3c0c681d00f0740e00220284540b507440c2e0744c510038002c16800c40b0315aa40141c20391130802000c0d06503641c030400c4580c4170169542103074011140e070013010301c20800c030759591030003801c81802280d0280419002c3c2c01104000c45085d03955904200e0745c1c0344a482070345d80c0a601941c2c1c0c000c4012a0000903140315100c00212914282c = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 547861726 1250 547860476 547860493
    0x3080a09030c0b21010b091005191206060e06030a05040c120f061109101211070b0103060b060f04090b0a08010c120f020f0f0a170106081f06090611 65
    0x108010b9500c00109501c564003642c0e011120020340309964010003201c000d8005000500082601030203a0304100d106407400244a644440281d440b8011141e41441155034486608035050740300c00e0000300c0c003040b850f0611140d5203030350b010344104004400d603e0f0409810710001d500c1130b94a401c4540c00c40c0c0245509104161a880c090500648001d0280c0b0302da035103000c80c0000c200d068818294180d14401c502420810b175000012040000c0509030820003041c030080c420f05801c168480112940008041641ea0546150503281100c00348402e842c55071070f04580c90400e0030101c4c1110862291046000e281a0a20800e48010203641d050290000708011010071098424403514049040070744034400d4080c22b590808060309c0c51092149004e0b0f005000c4c42030714590b02000e4580341020254800e0f142c1042c5602120442d4541c00c241180342c0354540002506500303d60090b0258250030000c500d08000f46000300316440c15032042100141c0f40c28000c0083c3d0b4070920098110307c041e802a200c052 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 547862976 1250 547861726 547861733
    0x50708040504181e1112031612140301061407050c040f050a06170307080901180605030106030c11100203091213082a090a06030501050f040309080705030703080a0903 73
    0x141c41e01824401c0c403180103840c0380e05020492540510000a0000413408480345568030485205103075402809810120f0715055006018015911305180d281403c9400c03e03043e0030f004030b80004030701040003c10a07078040120141036180850381604e61030703103030050200d0307402030f00c2201a40030f00000d880500030300008400d6076413640920b480d15a0340510215030381c01d2007400c0408480c1558040030342848070603942180307150044159030145800c401c00c0b90715881243c0058034084906951105424070900e404582c6a4202010318113071142580d0800c10400c0301c5506031000a00e002d0b42e0301240c1d100c502200300783e182c0c607001154040e03000c000341d4464111080c10030381b594118016034882d00c07010341d50500c8119403c10080603404180e0090b05c012041004100c20110356440007140a0010100082d010340300541161006641c030500070000340c9042010404840000e440c00c50020300c0e000c6001801204c0002d885065500040c040c1803001d00d16a500c030603a5104141ca030b018040503d1002010 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 547864226 1250 547862976 547862981
    0x9010c0305120a0b1c02090406020c01090c15030b0f060d052d060f090f040611040e01030605090f210d0f0203040804080c0103021306050c10020a110c041b050708040504 74
    0x941e040c118040789018139a8200500e08072400300d6500705181c020358100141c0d8509075800d4002e41c0042c00181e842c0c01c0000190b000d4201d054005e080b0020340742002500e1080902c0500c0038601595040240706268402c01241d07403104910f00358402400d00550130540f115900c81e5800c480413850902902c800d01c2c06494840364451022a442d020803c10000c4a0603e00146000b5500032900c0c00000e00c5c0905816000000150000d07024a564110740c4500c40d0358131040740c02034820450312101c55030b96481e01d44007801d001c0b9000c3d05140100088403442ca1000510350341d912440c1540b68980411084448110b83c1000c00302c1c40440c0d89071101c461501d04a803000714000c0e4058110199143d0504d038549207040d030008409d6040610403c42081c0e0303c1308001d51407043d109289070040da149600485285098811b00500203124070000344400035640003001d40494544a80503140300b0074507003081100b142c22a105200001c6c0551313260420030780c400c500504c80d01c1c1c441c2441c1410952100c010504 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 547865476 1250 547864226 547864231
    0x50a11070806010f0614130b1804020f1902060106120c02011d010b0312120105010c0203010b0307090b01090b040e01140117010e060a15020d21180317070509010c030512 74
    0x444e000700e001d05001095101c2c5e2150700000010030250300e0582e400003072a00da4619880b6010b483c900c0443c0500340880391202842100340000c0080d03484040008600c1c1580d4480d8200b1244200c111209503040e83c008039080d4108c9406803a518110030760032030143c01620610741d034541155a038009119441c2c1c000041e0300344800b41c41c0000641e4810303500a051030100380e41c41800f01c210080c0312902e0841c03d81175440741950400e103031414104160780701090160049105456041c0034004010400c0580d80e80900302d60a026650070316080c2e41d80107060071038407031401840b0000c1440001400340d0b90505114030603a46041c54014600168144050305400f03080c2c105008204c40c1c8420f0003c640382c00c11943c0d02a00320582c0c044125000c2200282d03032445100c5014091160842800d1200086400303544a5071812450a002007400382514180c034002d006011400f090420406000b92400060413130702c20141510b889140980c0600152400c25124200310100f2104001030344002d01600c11450 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 547866726 1250 547865476 547865489
    0x309050319020d0816210e0c030105060402090a2d03080309010606030608030306240a0519020303061507021306060c0311160e130b070203031005040c050a1107080601 73
    0x10700c14600250020304021088986a040010310f4060091400280b10020380f0701c111800c01d08807a03d40200c100ba034000003000980f0280c3c0c035010b42661524400701d804452203504800030403169407141c04001c10ad01428156035000242d541060040c40302241c21b228441d003080c882840e1b503420403144005040c0765500219040d20010082c040f2040007405000050065410103114a6080c0030610b992408010901c1d44212880d200001190b0005102100f903813012400346ea5903002c0880713001c0c14941c020224590240d0800703028482c014800b006480c01344400404208280175000ca81802d9a0001d61060780d00a14001121643c80c0061103000b0040525440314141526035003000390401403040743d0710010b50002c00a01103c250f1041d10641590f600b916400c809840b013515030904074400c103100810356440f10042c403010980000c00b6500c15801c42c0312044071340c1c0d210010b000945448203000c8000c0748003442140b00e0180124032505407a1b10750f104a4140d159201c2640e442c2500c20390005 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 547867976 1250 547866726 547866757
    0x30504030c0e0112110f0307090c0206060904050c240304060504140109080307050a02031603080609010906080703080c0f01090c2904050f0d08040603050f130b061003090503 76
    0x400070002007103401802800704586861456151101c050b04407440000c0080c6070b181d5968864510703542d1300300c0c14a82c00c40050103c0d1003507601c3d200d4100c001e01041a03110058440c0000183c01480d0600100e4811a44007002c0c2c00030038401c02c2031003201e14502d81c49400c5241d01c0c080100c1c000c0202405103100e140120000315150401e07041502e5800d5050f82c0100040e410290040701242c1c4410407641c0200e400d01d00203556500e90f40d02241980549421500d600c07440c28402d41c2031590104110b8041c0340221041c6410784d9072040b41d84121120743c4a500c038960080714041011603a2032016118190324501a0b6640d180290841c5003181d0403400111801d0009400c14041ca0a25400010f256580d143d8191802070240b58032040b00d000314801c4600c120400900d00c03031144c4891141c11a03a550050b0b2603a2101d8584002038082c01d8111413038503c1c0c405410014610f6000c0c488078141d0035400c0920880d43d40c4485041c88802405d180112052544034103060000a03020001026160a4040701 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 547869226 1250 547867976 547867979
    0x121b1603090602010509060417090402070510180b1314060906150a031e0204091520190c0602040807080a0c0e06010f030e1c03230c0708030408070807030504 69
    0x203014481d660300038a00f1a85414100407012030002004c9800a8206608c0600c00984103401c0c0242c3c8101c10086810600209031710040000c009950078144104000a11031b00c102da100304103901c2c03080200076101485000116109683c091411301c8201d010740051103c240b44074013410310f4060305036400040c2d9800f045c200310b0aa1504070070940c0034982224110b582d54507603104c00250720f03c00804030041d5508200004115a501e51044c504554440b40360b102c2501c845518000408500c80c12002c4a0100500600884440c0c0101d5a61024018508401d0003466070100d641c0781c0d14002c07c40e803150b820080400c0d00b400400800008101c1e9070300901c0071020f1445e000c05441c0d156803003210005245800d010a580c3c000000c48040300c814030f00041c1e01c80c000d925040c40c000440c09400c82d036080c8032080300d10181c2d05d90000a64040f042451001c100107e00304542a038070100d903801880641402a0300c005a02d2400541e009801451000e0508245403545201a800010103c010402c0000c0 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 547870476 1250 547869226 547869233
    0x603080a020c031216030e120f0f0d03051b071b0816050a0303230904050106052709011203020c090c0913020a0806060a170711070801050903121b16 65
    0x4e50300030083d4200302c49080404030300342ca0004602c41d200c01418403000c103000640a4031070038440400d07110400d08444200200c03500c0c140e02c4030058850f0100078000c4000740034205019025881c000c04c000b0f2418601d0410045c0201c000b03802c02502294024000c00c40132050405908150b0082c2c02030344040c000c1c04a102000300d20b000b070140d01840c040c1c040c030035041000c41c1e00900c0c24680b12800c00c010803010030880706000c02034800c0c00f46096004d46404000700d03185d544130740645807c00c1003101c040c0d554140001401e080c8000324400980c0800c0d100d00511004103004003401d0b00e01d1080c011207192003d80c00005400035411500282e128038049800141440d103041081c0310703890465411032800380e8416004000200040c999030041c3d0001070f1001c0040c0c440d10510800400310707880d442041c105540010a0941c0c640c021200c54801c10b0320101c0d0004044c0b2519000c2c21582d402185040140700c00c3c242c585200070528450f404400018100c000381d544010000103020110b08042c501d0700d840c = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 547871726 1250 547870476 547870483
    0xa0f0507150c1d0603070302030438090105040f080c030c0f061e0709060305060607060e0c012319140d02040801110a08060f0604080d020303090d1404090b040603080a020c03 76
    0xf045192140c071076248040c10f80b5000100c0360800b88514000d680c2e03a5a074102811f21030b1442011050741003004441091441c01c114850310302079640e8400080035201c0c0d0250301d00361002900c2c058410403140c2c035840001080741d4010842c074046281075900301a14002d099060020040105520360000401c101880c40c8010640c035600f030440344a0502800c0680e0000d108680740d009000a055a0f0740115041d030751a10240d55801c0c0d44500309004410004000a45030080304140c01c6c0403814482e01e0030316030b54000b20508605004104c000b410516485400190215a4410b110a001c40071140e140116001002042c10b00c1c00d007072002d65510f2901d88598210b4005125240d18800f05014040300e180d40b02810a030088422208201a03a1001340010303e05d01c00e55100c42014801d40c80320703c030304a80100242d072081c402d100c00ea07004132103180401e40d84d40c1b01c40001003030859820042489007045a50014440c080041c00c001074603070f00c956400b0003d030700c008144000740e8000780d501c1080349001c1 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 547872976 1250 547871726 547871747
    0x40f06081f140a0e0a0f050a0c0b03061e0f0901030c1805060f010302070215041806050f01021515130207060510050f10020307021903050709020f0a0f0507150c 70
    0x2101d007001540d505905002603240040d0030740390420b8a609290b2203800c4100080e107000c0350000c0074121400d125107001e56890780010f100300c0d85862106000184210403009680c85682c01404000354000c44440c503010414120380d43e030354071044070383c3c05100e55154101030902852144580b240346078100080100d4030402c1200c0305052505000421a0719181e5103070316034000d1000e01300942c851000e84002495510307120310405100d40003050020704e0250701801c4403c0c8240002c001c2040f1512201400740da10100c5a070217001d80d000500c03481c81e100c4c60380c82c0968803849681c43c25107113407016400541d2070b0240360801c900d1290003081ea0014480c0e00d200f0b0329000105031010102240c44c04000c900a030305014600f1388541d00501018804500030710442c0c04590340200142c40c10101d05d041c100c000e90b054001a9142d219005c80451082080c1c0700720f804441e9081e04490800004040466440d0f81e040400710412600340b140310005400c0c0d020b02120103007901030104000c02d10030700080041c0d444 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 547874226 1250 547872976 547873033
    0xc05070b0901020c07270f020a0e03070e06061e03010b190224090c0405090102040f05240904020f03040c0509070507030c0803150307090207061a0f0f040f0608 70
    0x42200c1c01e02811300240c07041c01c8415401c1542c010b188070700e003410919a1a440c500d6211410f10343c0403c000c00071540100118034880d15804000b5a852051560720302c440d000d100c59900d03442c400f1801034a4240068060350b004281c0d04400d210781a50841d0454000b0380c443d0b04140004920309481407103142551040391040e10050071f00c0c0900344101902400c00700101a5042c01a502092845500340320340804558080c00030700241c105134030740e18000d40c4148104c10b510030242c540130400d840d041d0b47c0f880e00e0f1000042c12402c40c01c030007503c0c000164401c0b89a103610039820404022020721801c0070f903100b10301403090391190900e05020700000c0e4100820000c2045020841c0c44002504030b50040c22040d00642c1e000d86070750751020f454107040d4004191507418851018009001580c5400401c5444d00c0745801f030000c21a1408200c0f15900d51462580c0d0101000034440700605202204020b010303001480400d003544420014405c8414640054407107030455000d0002114925240081c612103 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 547875476 1250 547874226 547874231
    0x31a0f1f1805040e0a0f0309080706090503060c0f07030513090606031407050306060a050c15040807030e030604020d02040203064c09030f0c1511010506010c110409020a090c05070b0901 81
    0x1002d0400c82c5d10742a80100c01001c3c8400420741c0024180300d01048000382210804854071140c544801400341c0d005881580d209206120001d40515015025038002c01c4100900c541000900c0e036003945c040c1c0025140c8045009501c400103541440c5025807001030156480000701c070b060a06603004030310402000070303050080800c02e000c00c03500c48000b29407410a0920741142c4600c86100002c4c24000002c0100c295080d641c4e050206210520004018240c407035103480211141c6c54080c951221401c5601035070101c0a0b080c010050b00306030b0001c541c4000010502c00b07010000c18080c00b001410106200310fa00d0241200d070000d21160328064038000780381d2001250550580340014901c2100d800000c01c0500c5809203017040052048039840607001240b114a2000100140101940c00510814a4941c2818040795542d400f903041c2c030194641100451400d4550031080c0800340110540490300800224400201e094552007450101078507690750741d944420508080303803614800381908140f41d1 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 547876726 1250 547875476 547875491
    0x60b18010504020f1e03090f0a020109230901080c030c0102010207020d060b030a0f0602030708070e100f05070213050f060a2114010c080106020d031a0f1f180504 71
    0x516441114115103040710050f80d903503607640c0520124050955040c00300040c2601c080b94015032200614070883c240e200f15445800c410140682c5e605030b000020b404030b040428244220064421507620460a03038a4492541d11440013140181509a200f031100d078202c541480f40e989400e01c1b407110069400d10095081c1289600000d107003440031040201f02d16038410050026890900c41a0904c940002c2c110098142504014001e9801140d04e0000035100d0b5001a064a00410300100d070608080c20032443c4013a0488141e503044142c4090400703200042c004070006981c3c1c100801c5c00c80c1c1461001042d10305098a4901c24610b002d44000c2c17250104075014046801401d41c042c84044c0322200410620301c3d141400c51682280840070f03038030355003403090700361809030440000c070b040764000d5088036103030384400c0c2d011812a090000c608c00c1c4c6e80400e07500480e143c40d08104410900304014001100d80c0210030300c54085030450429540410900f0100e10100c0704292801c02c01000162028082702c0e = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 547877976 1250 547876726 547876759
    0x309060915021e0c100302070210050307080406090c0f0803070c12020112020913020706051608060105040e060a05031e070f0e060118030503030109020903011107050d0c0317070309060b 81
    0x401a407543c6030750310203a1010300120040f00b0482003401c08405000401001c1c2071890050181d4042c0c64144e005500c44810844050f210f0412a446018a55144c22140e04c0e207a8440014042c40e030400d07104266952008182045d440c03a22000815042c1b0003190369201516202e40c0c00b00c13041c1d0000700e04942c40400100580d801184803031031507111007001607417145c044000603105800708805a02c11440031840348100720b603541c4154002e803403e04d11948243c5640307104031821542220039a001640070700003004440108901650011402040607070902d407034501003444c00d842950f1003441791030201c00c42861030a050011002030f014020041a0041c24441041c00d0018041c0c492810000102e91151060000950003400b640d0310100f030325500c0d43d5500d6600c0c0650000344450f442075203822045001440c2d20300450300c0d42035004003e030141100c42c140548044045100541c180603151602110100300110348500c542c1441c0c500040f02038545c14000f04481456001502900c041840f070b2054 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 547879226 1250 547877976 547877983
    0x703171b0106050609090a020f0a0309050c041514010311030708040b07020309010207140f0d0b092a12190614400606030f02011103040b07120c020d030906091502 71
    0x114500b40c130450031b00d403030b1110500001d21070900030075013004c404a111072403554190003001e0300303501031003c840d0b80850f82e178104002c0315041218042050341c0e140080041980d50a05000252014180028120500b06412180741d2003180d0107030014004604210402001c2c407030a58200000b4030056082c9060600041e40d0350610340620788000a02446000860703590069074083c541d000f030049038807202c09103480700c0364807000e64205860f070003190f91a20210341021191045151a01d5404403c802c0800902001924890303810500b400b0300d6008a05c1c605a030594105214400c14000840c000c00700213100780400050005010010b1350100480c20030500341c0e08420000049452040786140c4417030b00b413005211420002d210600700340d800801e00a462210b0b865941c000e0300c803008411151011f9944030f1081d80075245200105100d00c6001c691761040800300882d560030071030b01e04001a00001c062906506041340056003803441808501e80c08036009000780744c030300741100155001810194a = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 547880476 1250 547879226 547879237
    0x90617030c0d3e100b0d1205120103080901031b020c0915030a030206090c01020109120c1502040806061e15130e0f012d050d050703171b01060506 64
    0x4009040c000c0101800350a01c0d0703030b100038030010342c0c00c107407400754460540c102226564040e00f6401040c800101d100a94018045120b200a09040c43e5916944d02c0360700319400400c103041000824801c00c41d40140c03000d41280a940500803c50710b03107110314001025203c1c849032000501d00700f09866544280c0000342074981205c11907120b42c0c683e403400c102d4000100c0e149925a81842010b465106044d00840d04c140902c0514082d81d03542003240005900380c4103801001040c100e0032081c049400c902c00c510142e441481805009800c0b5840841d102c00d0b81c005410040043d0094400c1c00000e03d044006030301149460810540041d21450001f1480c03c9000150740700c10b600041e42c0c0703288060b2510448080e1451040d80c03001410550101044500d09014014483c3e21544820009040205d140d000c0c66441c10704101da49420003060040010092000711064450a1404800903403041c990301019000500a5611034214400c00c4480c904240c040c02c40c81d0745852400d000c9070311030404444 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 547881726 1250 547880476 547880503
    0x1015091b091401140d06081207050d18080d08070f11070b071728140301050411270a05040608030306040506060706060321050a1e0507050106090617030c 67
    0x14400b4500d40700595940100030107014000400142c040310068055000100703072450314048030540009200782c43c0e02c138841c059001c2c05903480301040d03a154606c618182641040d9603100044080d540d0382106141c0b104100f070700700c041490340003000718150f88450050f80d48100b80c0780140199211055554031003407a80030b2521030341800103c41003848611440c0d040a07002d0b94041c0f942d1400044d48000b00040310000c8009003801da4907848070b186100382d9070b84425039a403a0f6003902d10b0340b82404000c02403500300d42000e10707050705100c001c407600701c1b04440d16002c0161010f00030b0450240c1c0100300da8030807141c20561042d031800d4414004c611000041d40c1e0f000d0401c2d82c00003140d850b41000100302e4014228010f101b6420304c0c0000c01080008401c90240500000c41c404584280f070710266258011003a0600005011840903074200070303007440e140310035180b5080062506009032901800d50b01c039030b044030140a44500e0704002c00500040501030105014001d9030507c0c0440c00d1044d100d084111416 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 547882976 1250 547881726 547881749
    0x2503050604060e0408030f0106080f13030c061a010e060c0a0f030e030604050a03020d170403080c130f0f08030705100504060b040929010807171015091b09 68
    0x8203540c45a5001001408107207148000750b14040c50700303002550044400d031072246485070001403550300540b034583c01941140384640080c1e440103940c0c90400104901a020002400808804640a4420a8a481442140342d10300c0c1900700e0014000d1080241101d0050204000d0402001404500392501c00d501010300311142d5030314207088070004284800d040d85805002e0501c81048030003e800c1440a03c642c09a880f40c0001322019554140c0403008021407103401030004000902c100380b4994001203103151203051404c8488036480c28503d0344c0102803106040c50050003043d5001c6d85100080c41a580114030704566960f604ea1034258800c100c08800c1d86031404030701003000c9174100304035120010300100650060307400e1640300c01c3d62034500545aa440e4083c071880e1014a006200d043e104188010603d05240503a50010301d108100c880d84507015007106001d8082c124010703201111070081040c010a41048046004ca50a45200952451040070059074039500405d00f4812140e42e072616 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 547884226 1250 547882976 547882981
    0x30a0308130503040608010914040b133e04091a0c0d15091a0609010c0501240303020d02030c1902010c02030a150c080606071e140a0b250305 62
    0x100c0d03007140c107540c00604034000440d010428962000d0001d04a44515905008075006c080d80d90342c55000503200540b450760350341e00140c40c02e404412f548107454401c008c400c000740703007030140a00c802200c95905070500241d28002d440200c85900700a9100310100c40802c03e550550b038903030b54040e20039840f540f058500c200000b640c202e03402042d00d51008a4050078414019140b8107100311002602a80f448549051402004d880c440003019100003006400d180c9040c8810b8019281c0395440d403011106136403140e4002d0b001c1c041c1503203e100e2202a0303032a040d80007801c511f0081d04103044100e004003158810b204846900100051030046154101d201d00c20b1120640012078039100b0070600039405104503a9050f080002c841010110a128000b0170403000061000031500050b003590481d50008050200c6004141504d6111200307800071405d07206100741c5548ca0003401c00448810050301d40108007600103000440135126407100021001ca001e401905181900c481c80c1040e01e41c01705030b580c000 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 547885476 1250 547884226 547884241
    0xc14090d032312010501260c0f0705030c0102030105032401152703031b0c05090901020421060b0a0b0a20101d010908030a0e0109080a0e0901050f030a0308 68
    0x8410794016141c80126540c540c03a40d01c40c200101e081c821640082d000200ca4140400c3c0451f01c0d102e040e5522040c00f0940d1141881d00040d500001c11100100742e04000240008804000918481b21034000250301c940c50001018104110704038a904001c140703024509005140c04111415203010110b80c0702e0794108a14115408540964581140c076403085840401e070091240354030403a486680c92003c901100c4031042010708428000604e00032220710103010a1522502055012004070b00040c2040d035501000300101d10700c41d01c003440c40e50051640b03000f07014640c007414800741d03030907511101e60510b0102c010581e44160000d250400000d095903640411400045d284050200001c039440c0c50310701d03800c0c04000c103da4000b510724084295413803c12070030706018120160b6003190103182075a80d41c030760307d8002e08000100400655603540c030b2040082c88060141c1038842c0346540700c10020500c002400030b807800681003a072082000000e101f00b190f40002c2c403d100940d061a00d850700b501d4102c3c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 547886726 1250 547885476 547885517
    0x604120e0904060f09020a2711040e06031c121103010b0403080313061508011505090c07050c03030a03050603010515300a060c090906060f050702010203090a08010c14090d03 76
    0xd000941c0003080340d10001e00581c007903d20104100801c09142a0b055000c5148c0044070002052030b1007441c1d05202c03c100303e544000042c0d40c007070f20240980320600000e00c0035140c1b01c0401120400403985aa6070800802450f204440c0b1641c8400255441c0d5410030f0000c01070f5009510009000e8480000042c00812841282c0003002e540070205010b45a905007105c01d9a414500030b81d681da40c6800072110300ca000c1101803e0881c1c4001d0403680786a20380316046c1442d540f0804d0281d44c2d43c460441c038042c1743d450820041141080c103035000178a0b401c0001c100350035620094808051031140c260420109d5503001c103082c0000c0d4070f1421102e200b58440319441d440e8425a5800701c1a030240d01c40755414807038203801c03011611034141e40711006c0d1034031103c06d48101c5182d401054001030b411980f07540114000d80043c2007950050040b0f80c03c0003000c1d0700040450106400107031a40e51292003c500554010101c0c107081e82c00c0e1805242424464800b0684202c2e40480240c20440e00b841119000460342 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 547887976 1250 547886726 547886741
    0x903080f0c130905160903020a120f170d0c0305040302121806071209151e0e0d050f0c030106052b050607020c190503100e19050604120e0904060f 64
    0x840602c0c541d074034188001003804a84000c200d08000103121a42ca1190107072a06581c2d004100d05001400c2c02c0c0e655402c86030303025044400c0c5544102c000c000c5096002d1004a509500307030450f648103030500f6401c0c01d075a030b03042e40d60b0309241c2004180000650085902662498203085894a50b009903400121030b5049440541c4c2201e000a415800c1c00b001c0481002da644694481c00c030150ba6030324050110130202038500740001c80f0485c3c0d07194144111300c2c849028403400e02c0c0210100ca200350026940042c0c42c00e0440341c40c0d0103140c0507900c00360306000d2102d600e0000c400800c202071520020030503460382c0072102460071000d62403500500d01c100d0304a648030b5410500720380f040d141071400039585140d1100f04510403220682c2c15168074114810a00a0380c0002d00580b90300904070700240c01030001c22110300d04c64009c0f04080a560707000703038441200b000e0003000103140d681880d0070005400203c860907001005080302103803e440e1981d18466400540c030160000e0007402e01c10300480227140b003 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 547889226 1250 547887976 547887997
    0xb06180c0a0e01030f1806050c090a03150f0e030c06100b0a0530100801090807020f031c03021216020c090a0204030209040830280204150809010903080f0c 68
    0x241607400c0800c40041c648150b0003842020104401d0312441c209d600740780a883c0e002c1d9070240d042d5600344005a045140e00090b4a03e0384c00124803007480750312140584e68410101d41440d0700200300c80e600c1c1d80c0100616a0040140c0241024281c02e1034541c462510800c91900248400020014441c291800c041d900b001e490403010100b0b1380703d0f03403121411642c059039203140d80040300748081030741c0806100341d16000e980b0041051070840c0690a0040104c811600c04d42c1c14000c0d00034400c0403900c46207040c078100055550044e65525001400c03c0714a8001c0c0030b80e401140d06100041c030070b80c0c0008140c128141c1c200d031851215590145414064400c90b040250001d9001d01413101300b15000000d0301104035054413141c0d42405828a0803800c08110b60070342c10854004011071740800c070141648000071201b100b01c12040070f440613080140d80c004c1d40700b4071241d400c815440015031391143c441500010040024011508142c80041c8161005802c00c8048469200410382d42c1e03441078202c40c1e100c1c52 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 547890476 1250 547889226 547889231
    0x1e010908150103260a140d05090313080c030312040c082b05090904230a0f0303050f16030506010519030903020105011d0406020702030102090d0b06180c0a0e01030f 72
    0x5214a100e2070000a2100b2183c00f40f06408902c1040b0000d007919000c0e0580700c007003d09100c9000030441c0c040210319003600e400042042221482c244134080c080c411402d40c4c1c01155650600da09992000b07165501001c0c05811002c903210107035401004480e50481e80c0016140180c695080409007800b03103078440c003041d2241c11030082c00c00d12851200c0c0b0301004035000209000e031040c00181c84601c1a0075806502443d810005000a44c104030183d007900d040c900c880c20403054030041545002032807030b0182c4e50401038000030f004042d810b0050b07507071100d0204124000c5d0305040242e54040c4c2c1032203803410140b5842e900024a2a4031803801c0d50403403041c81c2e500b0852095004009001404d03c80400d4005500309800414081400501e031401e450560916180039034882d112080250809070080f64595002c0100800c82d81d03604c95a016440d000710f202c030b003071420003500f00f14080c1030580d150183d500700c00c810010080c0015043d60f5107400d442c04c08a44400c44800100d008220001500740004d2 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 547891726 1250 547890476 547890493
    0x1214030c061005100e100c170a03090605060a1508040f0b040803090d020303090703020105160209012606040f0605040f0605012d05030304060c030c1a04120e1e010908 73
    0x2840485142c1c2150b8050754609080801a0070460b01c1d26007071a221a0044115204600114400c040105550740108020400b40010302407024041e8030500c41040060b40f50b050610600c0b4444c0300301ca40140c41201c541c0e851a2500300c415550a60702484401801b4021000402344889007240020042e03101c2d1045004e40b905180c6272050750030690322100706100700d50708185440c3c000001c407802044038500a001051844e4011a06588a40c0f504103040c000c0209503001610341000c01c3c1c1c041e0801d804072040e104020444040c50150b1280180021b40c011014000858502001140f12503000030010070a503440d801d0014818010000041c00c807880c4c540001119a0313104c1083c40703c0961002d1a9610020039505c1019070034090191680c1508200020880c05004103007009005200c0e01700250148655111080c0c00c810b10541035000d8082e2000700001c00c00500f0100c1e0341418a401d0010000840d2004555800705040489041010660f00324001da80261a47c074002c040e4401202e8011 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 547892976 1250 547891726 547891741
    0x3060501170607020f0c04020c07051002030909130c030602090607020306040b060f0612011e12150c03050f04020f03161401080c0414010518060309010605090a061214030c06 76
    0x203000d0009070000d10300450000c03410300c078400b140380c031105001e40005010032500034081000a52110b031503281c9a04c01c007440060544c4500c0da40040065040e0080d648801c0803409000c2c5550740208507a9011726170703903c00070016108440d0300003aa50480c900603100c1c18420b02103000d074443c100d0080d48c036201d240708010401c02214221446180f040e40c0070b00c0264003039024090203000352041c2000300e4060000600c001c2190301c503c9002a500952940c80c603940c1d41c56516114424200700b560244440c200e81040b0640d580100700601e0000d01e0b0030000d030b00d4601c90a184508000d00001d1061400d0f030061000365074100410320342d204c0c00600d1043c0c0155100d480c0725002c07000800301800310f0203001c0011441440007060300d044901c0b04e540d450300c880002c0e00460712544800b6002048400c00d1810403590b07110500510b1060311290000200c03141410100300102c1801031504c441c082c00c04e607086c40b8080c00c80145030081d40e03200b030a6203c0ba031030782e4400034154001c5200b00803a5104d00b10810050 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 547894226 1250 547892976 547892999
    0x61202161b0807050604050d0f030c0c0b030f010b090d0615090213030c0b030709140d23061f14040f151503050f0f100305030a020109150c09030b0c0403060501 70
    0x126242d030021944503d41c0d9a003806018003075032184951213880807200c08041a0b02400348080f0718824a00012407540650341d83c4c14001a98000c142c591401100b08040940884922409013503200805824400300c440025401d44002800038074680e00c910914200c0c00220003440c3c083c00000d9010340d1962503245021014201504c0262802c5a142e02c2c0040e250004000326801215241d64515106040610440038161640001a00041c40310010004141e01031704511a12035452074150f043c610395804240f510300003804210504d554102d0129503125006c0c0ea09040720001c0c003401e043c5805076800580140009516255118101003890302050b0404000106a6403084d51109411240260803400c9840846041e41443c0301c12000c10401180d66000030703441520000c80d075a0003901c0f599610f096800104124002d40c1d19290b501040040220140300025000310040020802d601401419600c5c14800078211b404400c1c045100302d018101150051a0460030901030b030750750380200440 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 547895476 1250 547894226 547894229
    0x180f150f020d0c182624090c01020f2104050d060b090f010b0f16020a06080702070b190507050f0703081c0b030715030b120c19061202161b 61
    0x50110340d1084406050706550005464400688040c040703540b0402883c00441603440b45141e22489070007204005690042c07481001b240e02e1894050b0615203540c1d40f9014501d4103450554015000c5002d0305800041c5068000b02415228400c651002c03148142c5d610654201c0c07900301450b903000034244a6281c020000205003601d860b41180c0d41e607034401a40700c100b13000e2240703983c07020809850740760ba400d400340000c40c81480010006c40c000380d0010f204081558044004540c2080c00c1091045e0180910002080c120720381625080c1601104013800304040114020710801140314030a00004214490030503000c40100c400080c7c42e42030151068004a0804a03004c1040c444520503c490340a000c1880e60080c0081103c20f0501d1411080f072241020f5520400d581c0c1c07401a010f59440140006203007050741d0140c102e4080c04c4c400e002c2c3c0102c800078040703c11415031204000c0260312540d1480c040680c55001a102e809942c090300e401402140c0103414150071081440406045014040 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 547896726 1250 547895476 547895501
    0x3060a0504120c030e090c040b13080709020a1b0819031a061603030506060c030d090b0a180b0405030f0d0b0117010f03060509160e0a180f150f020d 65
    0x40d280c042924201d0f410500181c0060000b03914100303810480c200003460a41200d0300c040c4160400d51180b490003880d070402501c101c08640d180e84200702c410400c0c4900310140180f0340c419071504010b208080c1aa04900c00104503070308038144a6018400800c040e10020b4005e403208184d0240102c00007400317454012840c000481e05481d1507413492401c01d088a2460035490162010485a528158000c00000304a290000780c1000102503c290500041600005040c1d0004003402c481c186621030340001011141e03401d00d000090280b50425800148450740c0c0312842e02c10700d6540c0e2824a05500502d0543c94141341d010030203414180e6190082500701c8001c0c0d81c0c01c001d4004989216410700001e2040ca0650700f490401480032031080c1d0041540601c580084801081034030350742d1559034a00d54805d100c004941d2060181c65030303040c014000070342078416000354096400d440f2401d203000310100040450287c0c01c0c070703000c4072000360704226100135040b41d007191280241c02c040c4026050b0340f0301c1403 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 547897976 1250 547896726 547896743
    0x240a0908150106050a0309121701050904050604080c0309130c17040809060703030209060c061801050f01120221063907020a08030f0d050601031b0f0e03060a0504 71
    0xc00e5200000a114044840c203581500650b440c0840640f01940a00002d00405450742d80d07903030101e058801140b100e480241c2e94828140094070380d0308481941030300514840c160b503070140000f0444c0042c40e990040d0f040075019681e518060401441d5100b581740e0103801522a8030040440d6040342c1c082092880251503d05d824050003a1074079811303074121001000c00718240406c4000f403c05002404607103105c1e007801803403c100d0758005107058004552030340c0c09070300c03031070400403107102c90a00c0d5241d15500354001e0119090400000c0002d1805000703585052059224983c00d65980f8404500c0c880307040e1000b004c14603000005291070392011034a01c2000c609400025041280c000c0811031400040300b82817a0b840c0c540d900d10005e6038005d0000380d901c4a0f40c9003010403410300c1807000b030800b9a04906140d46d51074404e4158801d4840042c8032a05161810904000e4050725030741501c106441490682d0a2002101081e290147c0320503d89170148035050800c03582404642c01a40698080c0141 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 547899226 1250 547897976 547897979
    0x6040b030604020109030b1914160507050c1021090b070215061005040b120405070906080a0f1e06051906080a0308073f020301050105090f240a09 64
    0x626658260a49001340042d0100c48100702290f10082d000e500a55800c826403c1d21070301041000940d003510594580c088100c0301480000307260500704151404180c1001d60510f009500e030701d9122030044030124001c450388906048034030b20442000d4603081240d0b80d04601804004900b030010309040e2802c499040013140410380080c000202c15461089582c41e407006c964034007042c03010741ea0202c202d6805006040c0070204803000040c010703052000900c030011901d8078060426a2038061250301088556285c401c0030300900b100030411004a50b0413105400804d1080c0c64078400600100c040c00300501c6080251400700805601704034044d8a14208039500c4540021030b10f41256040e20910200794805414100040e010b200d020f548005c80d424042030040d5024004016014202c8100c4070030000d0800c0780ba6503502c003244c1d00d07604000100c411415581004006441841950702491180d90044048841075581400e4a0b501c00719000d081032a071009054094044c0d00101c0100c000318107403260 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 547900476 1250 547899226 547899229
    0x10021c09050a14040b0901060f1209080406030506011202032703031e07020f0a08040312081504110d060621050402090705030703180b0a06050301090c0e101d06040b 72
    0x5591081c1d8000a044030b42c400d00d0041d41c0350701d00180310000c5400c1903d83e0315101099980c954854000c0c040c580718540c8610400c00028101a08201c20307820062a005603a8049003d107000d40d41516024140003801f0740b50400143c0d10341407041c0c0c90b50440390001040201c0900e500c0000f58504804100e5902c041c1281000035440303002c21181c00c40035104a82d5440d017080800f81689420417441d005440b900812550f003107062490b050f40c2a1101c0500060410400202449140f40640c0f245828043c508158058400102d501c0303074000c1c4980d498549a00d80d91381400111070940c21036105c20030200d5910301000d42846c0c048048510b180340c09901c0d41486000a0044a00c00c0364020654100d9503a4008107481e01d0300003801c10005c00d0303506c0c207002950316031000100c0c800360701403c82c103001e501e46145500142da02c82d0700414000d07410840c4580004100c00ca0380c070292950320821000d10364424240c000c140720183d0040720003002a1244018800c03589910b02d000300e030240e4082c00340c3c0c2001d00 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 547901726 1250 547900476 547900487
    0x1413051f12080d0902060f070b191505010f03060b03090a02010306080a0302030f071410090c09090305091201020c07091b0302040b09151e0d06120c06120b10021c 71
    0x980c05080d266040055454038203c80d8414802c141c40102420b040225000707a00005030002d50084401700c250364244040325006039541010491080303400d200c4140c54143d280783d451800c1c4549410b2140d44422110054000d030031a0000c1c0005404168403440c200104c01e0780d440283c442640407901e06240030604c020b01283c10000b4035050b80081d4a800310f10b40301144039600484041e11480d01002c80800d09020500c00009801c24080b00814841030300c1c00c01c003410000692080ba1941e1030154101d00294020342554100300085640481024140c2005800380c03059600900340760254603004901d1440c1c50f8401c1c520f1051410001c541400d058a050f4203d110307601540b081000140300c1c5034103034a4034110744a004207480c0c06950034000323503c0c5890060310090380207518000c030208100c48051040d02c80d40303000b404c0e14240da101181c0181c44000e11040d09015803001c0024080f6000443d960b40e41011036407001c05010300e0031401c80000002d440300d01406042c184980c0d106c2010040ca0300c2003 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 547902976 1250 547901726 547901759
    0xb040e0c0f01080106021507090e0106021b0907020a020105090414010e0a0e01140414100213083d11300105010914040609021813090b011413051f 64
    0x1b50014020002c0302202101c7c018001030015081051148010a007503201c90250350080100707400034078140d081d890004008140d075040040c0501940020040440e40c005411030702c0e5502170920702e0380d8082d80c4000c40e003d010084030541861079650000a9100da9070380000d4400c150310302c0c042000005024140b406e0340d0a40310f00c40505260540420301080310030791800c41c2c401c2e1b504c0c1143c100b220120380103016070301b06c40c0740101680c0b0802c00410030200d092050205801001c02905032035449040300204121380e00000d03040043c00403007880c0f5440705aa02c04442d0032140161151500708078481c2078510307040d01881c0c040d0b40b4030700800040854045600d0b94180d45050b10341220803410841c2072408404a00402988a40c0354000024102014070080480ca4421068018a44031400c2800302c0840204c00c1d20288900e001134500c00b00380900c1c0524103541041002e07040128803c400100c036195100c100c4000c2c0d40c500003d005564010020764081001da00d41000d20a543c1c5420011081010 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 547904226 1250 547902976 547902989
    0x61109190f03142515020f03030a05040c0305060a150504050906041403040f0b04090612030516081c060611030a0c121e030207020306060f0d060b03010b040e0c0f010801 74
    0x142581440058034280b000070340c9901c0c640807204152440041e00d61504540c442003200b158130400180305040c50400b441220a8075400201000d4603020382d0700b0b41c0c81c40300610014215a454020401b00b082ea2010000159080400c8803d9400d0004040000305010070400200c203080001c00507960412303002c0d043c41a400030b0060551130b41c460f02e540c003006807180030f560a0341c0010000464900d86000d103e001410031940c5d03282c0c5881c20000e4080c100e40380e07500322a030040d0880c840400000d500804468400f000c039000b0482d0301c091494a5610380c014907038444c1005407050603204046a0785d03802030007103d1650b03a421800610342c81507280c4074800d24042c180020382031212200401e001540d454801c41c0549440345d107030481158500c5002c0805520304000980008500d8150702d4204203c503007001c02210403040c052901c00000d11058002c0b4001080c0c641c6030b401c0700b011aa021b51000c01e1264000c2c03c14401c0101c59400d407500c6d051801221403107111800d64400b01c0c3c3d44a140e4040c1a581c1 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 547905476 1250 547904226 547904249
    0x40605010906090b1c0312091406070305190b010903080f0304060c0e1305130f0804030302100605100e012d030e010209091b07051218040b060a030b0a0306110919 71
    0x11000003902d5056518170903030500c100010141070b880320600c20401c2c100d000d031201401b46120510f03290705060001d0110400c04d802c00c004c1c000e00c0810306074961000c0000f4040020b81d0701e41c1c580140d9403540c03107034000b600b0f164010945005000110004500c00c0c2c0c482c0400300702000860303a0654058000c01700103078110340b041d81c2c082d240e0005540000d8012481403502e08200400341e403409602c13585942c040307502c003002003800c008140c0c0400c154a45910a004280002e0b400e00010450b41c3c084111100d04000d060000710030164012244407203210104030741c3e8000d8010f20110480029072700340414001038604084025003100601c02d490244800401c0d602050300c42504900b20b0705865160005142d100b002020300290080000c0c0305160b00c22448607441d5254a100e03490505c0d140a20113016a082144030303052990340340115150391629050001d01001810082100e010302500000c00f00307441e01040901510717640024080035403048907d500e000b065690414103540079403080c07000851 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 547906726 1250 547905476 547905499
    0xc010c06110a120b0a060f030b1c230105070e22051503151b070c0b03040b0105040e0a05100e01020d09140d170402010509040e03131401050f030c0f12040605010906090b 74
    0x1b40300c9d0300082c84d0110000d00301c1ca11200c800d102d9030352001c0c9080b02110910808078282ca403001014488000390100400201700526002a020f850f040740c8048651248075051032a0b0104094420742246c2506c186030104181d00d40700e15040c480200780015144a0300c5a008a503441c8407000c1489032055440c944000c00e020480c81c114201074000003011039410200440c040340d4400c02e1030146100c1c9010394000340d0903502d8201480101e6290060151036a00100543c0c000310b5000108071414410304100001d0181410034918028000c0305e00c00100c060500050f501407040c0700c40403407107078046202600d5203403900705001d07030300341418031101c00c60300105e040001c0242d80900d014110b0184007504c042244c0904442d070a0940c2c0c8110000082c0c0308241a086c004507102d903108134206942800c0081c548014a2050521800000e0400d0100348000420105100d80d48080d1842054841c000040c242843d2a012010b0702090045a0405287c18400201e913900c500440c0c0000c10090028200720 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 547907976 1250 547906726 547906757
    0xb01090c0c020d0503160b0a0b0a030b0f0402010e030304080a150506031c09050d1a1b1b0304080123090102070305043f0308100501020c010c06110a120b0a06 69
    0x1049800c01c181c0d04e40c0070900c410210403105d02c40c9005001c4c070881c1d1081681c0b40040030582207403c81a00180128900601440018000c040c019000b000c1c82901a185540707520040700c01d1481104000d80500000c1800501c481000881c6905241304507a030090b480b1464100100f1144115010b650540c410b048214451100807008200141c9614000c030b5055101c1c0b0128000710f90701700c13040b520054550a0080446c24003440c0e150850140500c1d00e00504068a13080024000c0b0902000c42e1492101640003200c02002290020b0a0b900c000380481c5a501d80c480903000e0081e50503000400c0340d00c00194200b0f02c18800c40b10038580c1074a401e130401d401e2044040100c03180ca0003021241d5820360003030800802c00d1402844075800101920411440d51070000c00303c042c0035000700740400c03560f0f4051040d40e8002c510a4061302007880c10150400107800c0c00e0740606210b20100c003042d80300203400d013500341c1c3c070044a11500303201394170034407a841c140300610099514034403911002030280340411410 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 547909226 1250 547907976 547907989
    0x15070e01050a03140c0c15070509060a030f050f16110615040b030703060e010c05180d1e050a031b05060f100b130e0105030a030c020f061b0a0b01090c0c02 68
    0x8500300c0c900002d028644001036130307585000341d441d00503070000410030a0180c0c404201d6014404208050399009003049000680103000300d0300d5a034804d4102080e641d032000d01c40da100b0152441c080006001d6420100780501e40321006403000e00569030007001e83e80c00d4a0054501140c0f0468480080c26266600c0405410b4007503000c00d804e0f4480d0300c4d88110615981c08101560146005980003d4401103000415084a241c4485c2e003061040c24000442402a640440d42d41c4600555414105001d40e1a01c400140c0410941302c0c906c0301041801c1040c0f20740081d035911524840e03181e030070588240c042c0c3d000c4c141036003500050041d0321200c0015044000510507075040b2119902c04514203841ea00c81d060603422496049044800d1748000704010703080c40314014010202174006d481050b400340c400601100d520301c0041c0c011b0001030800c0030030741c032040d0403140400c107100440f0301140701c0200c0907a1901042e50040c0c0c4c4443c03410001091541c810b200d8100340c01c41c03035240c031405110950300740205c = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 547910476 1250 547909226 547909237
    0x3020406270513080d05090c0f010909050901240501023f2125230d020f09010216050a210c0803040f0e0f180c03030a030b0315070e0105 60
    0x401803a0100f100d00018000c030058170031080c1e0388201090034074291121910341102e4809031b0740b003102d41c4542d990850f60000c0c2c030305082c0c4d1130b0801c02145a54031070303c1a5025010481c0c08014421400d00c0801519410403030700c0d0180c5000340d090b43c4003292084406c400c2d4182c019628409100c03d22014035030b04400700103602e100d40c1810842070602e407040b00c86a500b515000300d0004409100c00800440c400440354144c0f0700f40050191540307480200304001c00b5150300958040308201141250406840c580040d0343c80701560000656481c0030345d03000380f00c40303800c07022a071400352045102003081c0c0074123060705e10151030300070b04070a604d02d186c16481c8001807030709400a0009011714a2804c00305003000c80c0c880c0540000c4009599551405090040300c0c0b450b0740c0100386004058007404180320380101d01319000300740031881d680d00107a81da1500b4140320000c000c0941c103120008441100c2a00350300f00c1c00d60b041040f000d466485c080105403540d940d00c21240d403c00121520201c4150b58010805000c = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 547911726 1250 547910476 547910491
    0x19120201020c0907020a05010e06042103020d11180a1a0d020c0601081c05043209040501061403030c072601142401090512010e0610030204062705 64
    0x35268440c0b40301007001a8003d03207440d40183c00c8a41941c1c1448400d020381e00e001d0b0070180061840d4a0507850302a1103408882204000c8030034172409588191285d01501c403101410001003220a0300c6c2c8000801c2d544c0310030300d044044c002000c1c24411034504032400780c04903104691224a454109a2000321580c04258060f400d0f9600b80a0264040701c1080302c1e902030300e4154002e00e980768001e41c6090011500d480380c482003040810003030200da14140b0118440280022100e4140c81007d520340c0c4030601c0a0711a81e40024808040005206c0150425400c4510500d0903021f520400340501d52280300f80109070380d065126590401c0410300400310b48010500c00704d00f42e00203149480340c860954002e0301080007803042803010300050781c008a07000200145890301031801000b07441c00180c581841e5118143c4100083c47c5850300c04102034103e031842150480c1034400a00e02142e03c02040d0500380000da000f28034121000c1048605990f01c1c0c0828a08060b41c11240c041c6c071103c00018000007442031 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 547912976 1250 547911726 547911733
    0x40f03030f09140a051c020c0f010e030d0f0305090102090a120c0806090607020c04050403020a0f060609060602030d0b0d020604090515040507020d030c020118021e091f051912020102 80
    0xc0042410140003140c4500c07010042c1c08001c4c050308055180c0006841d20307031411a00300f50a82415500045d1000707541d5030560302109150103600040c0c902e00e0b2140b410a4150085244050102d640108640c002c5c070103940301080551620000c4500701e00034488283d0304005401c900740000700780c1105e0005800d109486001c12541c9034050b5070b060540c290b946000f01d80c00341c410b11000d940c042c0101000b201c0280c40410680c0780c41e4400030744d62034003410050b00780e581410317800060101540159001e080b101c08140b06d11aa146002980c0f0f601141103003034800e190444000251401e0070715285032a80047c0140e0409080860308401003a000d0002a90654034034a1202c0320b458a0060b203200c1c8150b23402400314000b00000150546021140d40700459150a101d401e1080c032640721040c03200d03010780742078018500f20f820708000c1c0f44d0400100da500110031010071070b000700441700f092084400c10402070059581c4d0002e11160b03505039000b10b07541803007007074092000a103040d800703410350307030052046 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 547914226 1250 547912976 547912991
    0xb0403210c0207290c2806180f060b0118150e1807080a0603060f0209090609040c0b07140a050304030311120d0b0f0a17010e0307110603060117090a0b0906040f03030f 73
    0x3204091b03241c1e00c40c0d81c20382c40c00300e1000308180710a070302c90380080f00a005144d034581500e6507100400f08854000c001c1240d0f6441c90b2100319a4410100c01e1423005d004c44083d92145e4460100091003400d10021000080c08001400d485003012540030990030401041e00034240c42c0e021040c0c4032500c0c0102690743d01c1d1346c1c4030800000302d0000d0054241c0e40b0204500141d07150003080034400078a80c010001e0b0300032401c000c02d020000c3d14117415141110144800700f43c503000c075454900081c105460f095503c0c3d04c102c8091005200d000704c0200304403032181e1030b111045c0c03000500b410b4441c032202140c100740d03150510090425106a0304030103004031009003a07420342c0e10070340002140e21580783c000c0f858520040310051100c000911440540c90300e180021800e03c0030ba59120900076600705481802020b000c0041640740e4000e00c1c5624030400700080e18069890102c0305d20307683d115685015104150f080f0007040000300b020580c5400340390040031a004200c00b0382c80075806041d0054000707440c240e03500380 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 547915476 1250 547914226 547914253
    0x20d0305130e0106120c0212130302030105010806152d04140a0603050d0201060b0301090b1207060f08011a310602070302040605060f070b0403210c0207290c 69
    0x70410054000d0556101040d418807000500f0b104107114070f16a203500c0c201c15012032540005140707460701488c04c0c441e07079200354200d0240545616503200940541c288000821254400304502d0720419400c080c4403145c13180300302044014000c1c203c07d40c21441d455070b903180e041481000c03c0d44000c03c0203800800e921751818034800c0c440b48203ca451120583e2010103004102041c1700041041403144001c1c0107940c00c03c1d08407a071901c07040c8078800c00544e0b00c082013241901c4140250b00a041d8880990380007550364030014008102c40c246260000744158000f1880756500d400c40d01c64010310004e0103007400184805030000c031000c2c034800c0309001c06900c1409079800000d8141d0002c3c060319805412205d155105020950b0b80d82d400048c4120014007441d04858051426202031640048c3c01000907180e60030309030340340300b10689098030001d000704c90341810070000e800c4030f65210783c0350b0708130b07240d450b5980e642044041c485501c802000c1700070b140090003540d01700058141c0c80d809406545401e00d0300103 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 547916726 1250 547915476 547915507
    0x4052d2502010b09060301051e0402030f06072d050403200306011401020f01060506340609021201060602031c06150201090c060504050a0902030c070c0810180b04020d0305 75
    0x1490200143c1d11046050b8082c00c00703100c070942281c1c090740240701c203040024000707180340c4003480300b44400350008000400b51740e0100001000c0f10355078011b42e845800c100700c000340032035200c100c00754440100c5034902c00310000103021640440419074170700342407600303507560726585c00201a4100396100c415a050901c1e03907400d00c4281d0003001034001c402000b2015070000fa09201240700d42046603450000100a2501c40703204803a003420303044085034030019001c056405400c06860314a2051820300d6010002c10055034000001c0b81d00880d440468140002401d030300742d070200d00036000140c00a00260700c2d85082c400d54451940f04101010581a884403122502c50301e251500c00300503034540c07489100740100c481c111805441c041c40d04618090411022401458551041c0310a5a60000009500d105218182e038009988880005211a03641504030f9844607650000c03c900303480c06c00381c401e005003075070003030040603622144110103a038540d020000a8070b140710f42581481000c0000345003021401c0c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 547917976 1250 547916726 547916791
    0xc0405191401050f010e0f01050304150216111909020c0a05030f030406180c0302060a0e03010c11190c141c0501050702010c090602210915030604052d 66
    0x2640da40724658985020004110b0396000c2c42414020b04800050345501c8118101c0e80f50802803c1103079580d1074506e0550080204040d00b42c11071840031400724031440d00384000c1c01c0e21500901641e0701002d030090070041c03c65035a075a03460000115041c200704880f16900a844511303014402c0c1e8000f5885511a0707800c640c000446804040b01c004100010810310344122101c1c10410710f880495228582c0d036816102c441800082e20600c2d01081d403804c2c4521542c0440080c05002d4001d1080b03d130b18240143c4001900d10800d152405807030840d0030242d40050514111581081d480c3c8009d81c82c05411030702003185604070300c3c2c00540741c00c07000b4090341d80103180c5a501d5203e440002140c0c940642d000382101d0103280744200b0840c4907031003080aa13500103241e1640c61f841311f074002d091030601e5030460040c1c0f0421012a8102d001e00742084500411080510303c500c00c260380034049640ca614104000040003030180b81011008000108403007042541c2a5206c1e49504e0400c1f040d0701c00c24422501072950 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 547919226 1250 547917976 547918001
    0xb0301030b01080606031002030a0902120a0b0906070507020f131d0d0e0d11010c240b03031608030703060902030a0204180c02100b150c0609070b0c0c040519 69
    0x401001044000d64100d4018040c510160400c1e00b08280040d0300e400300030018618080e00440403a00043c5ca5512451180d503000341402c00c11000b41c15440d0320781150701c005980c41e90035200020310382c0202080c01071241c011941c90924012550382002496001401d03100c1c1c1048040c050011500c8051113603c2003480301041101c0c100b507031070325031524000f403403131310f103010070140308242401da031070f00d85014050541c0800148811403007000100c0d50101c1e4160083e04603c10501c4410400c210007481d0701404044c102c041c030241d0031210074103170707030b4410940400100c5011409407404940c6138000395800c088036183c003050003075031001c8910507604252542440c19a00080400c008411031220208440142d2014400c1046260020352035900201ca641c046540718002c070031066803200008081916200740184d1520301c04105580d07220800c40c0e42c89418861410040303580e001d6602907802101c00c1000820f14035505d041408041c00024040c6146401004040c5108000500030f0100d00d102 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 547920476 1250 547919226 547919249
    0x2010f1803140634050906073008040b0402101707090f0501030c0804060c140c340b0921060a200711180a060302101d090411040204 58
    0x600f82403084001109024200010828044010480702c450407064104c1031503041990302c6039145004202203100d0214010803003003c0003d1400d02c4828501b00f01e50490740c0c02c0d050200c0b445c504c04c055800020655002c3d04034440d9100040062401c68841c0041e82d400e4506880a000a440780d4a8604029282400420500d1a0070f1145950720301c1000010002440c050016040340c1402800340e13036001d800035200e507440308540c040d0300e03029071165070240b000300c10001c1c1e07643d0110000584540781c1c03416a07040008200400850a00d1303504410910004600307030048031070f1521101c1c0360186d00420401d500b00c5401954400b820620018a07030080c01140013524407482c20f0488881200c0d20303200e00e0340d0000781c1103042c0194000c1010039a0242940b24500c44c0c030040b01400080c1000041c141200d541074001d101b0001030f50803c1e0000340031288240d52800345180100d500351005d40c81d9541d41f160490540020000600c2c1401c1d038560428040c1590011012807800401d040c0d82c0240c011803a547c9 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 547921726 1250 547920476 547920481
    0x30b010303170f180304080a03050408060f240102190b250e010509060d0908070b150108060f010c060e01060602060a060819030e09041406060d02010f18031406 70
    0x142c01c0301c490000380d030041c0d5101403a4a85400e80c014248006850500301c4d1950985100ca000c904000f11009040741d8002c40b4a0f100a40c13400820b158082e01070022a402200040b6420248c9100114004c00b492520300d00b24081c80500ca1301180c5200170240d04510442c50728001400751240ba0300806030241d0001c110324903144112081d043e140390401d120319541c41c2100100554811a020803c0c80c0c01d00e030050fa01e14206001440318020848103413542407600104004205a41c0020000940300303031044401940c5859502d10441e08941c8001e01185006001500701d01d403580c0d20b80d45032241410b081c6036a842c6074645004545020501183c20780d0b40b03074410705c07100d40c04000050340900d03420340a10280341010461070700ca48000e040e4144030031640c010b03001094014200d08600220151821886180c01d0a03d88012418101465481d00841000c500142045294a101c07280c040e11000c0c0541e01c8484215001d84805610f10560807030700001000081c4004003002949142c040101003e0 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 547922976 1250 547921726 547921733
    0x1504050f0402030c090601050f0a05190507030215060904021309051203150f1011100c050d05010e103005060601090b18040b0604051306170c01120f060807030b0103 72
    0x480c0c0c4241c001d21a005c14820403510342c1c0e0000032201e07045608446981c03501c1031580c056600b0700807074419a605050496000c1c00b419800406030011600a5084420801c000c100e020300300d05045c0d9074242c00c444c030791000a0260a0100c22400640210680003400007074680790b00c0d052404440300d00406400c004140701046020745a1441d440703004a54064203000010b0002e2908038441c01d00c6424000c050030501c11501060010784049011404244100481c080d402000707680a43c0c0b501c00c0041c0741c24008140790b03e2044280e4818001e40d440e448486080080160440d48030007045138541000210840c0d040d5404800480b1642c80f40000742142c0c00d0020000d0705401d015046222144410b00c0030303601a8445510481c5680001d460000303011281ca0007007140c503c50b51704120b030007401884486092028950040f400c94081115040c0860390101c00345449000b280c900500044070f036103070714011304840e5014500517000501b002031156580c120082c10301100781d00030780303501e11074100401c10b1 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 547924226 1250 547922976 547922983
    0x31b02030109110f040218091e010801050106090603090807331a0102160e090715050d050105040b06220f061e0f0f08070c0605132114031504050f040203 67
    0x484c1c000711001e500b405901d0500d40400c110070285684549100004a420914408401c072445100445030903000c1d07845031100d80c06031900384105030005900010000780c0920910580a50076031024003140f801c0c4141d140d9080d8813400440740d030600b03070480c400c1044c00030341c403043c1808010680340007080e03152490007501007102484000506540041a405046100242c6e96074255402c00c0010054dc0e12032801a44c80d183d10b41d04078265258212142c0410203030420080c0c440d1408506085c84203030703200c2d000d020503100c800d00c0f5103400c000c040c481e8440d000010341c0c0000b00400c0c00e0410b1580c60340e840744100814a0980e0052010406507501c004010300d5818210342e81a0981c10044843d2044003801850098409101002c014443c004509440c3c03042c0050311071650864414040c40c102520251a040d25204086400d920304035001001640080360000c07100e00c0707507242c0e009280989401d080321548004c4c25003480c400340c40079020160b5102d104450045103404022062450640b0601d4507 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 547925476 1250 547924226 547924249
    0xc09090303010e0103080c01060b0d0f0515012c13150605040308040308030c0d0906060f081b04092612010b070b07050d0603020a03210f0804031b0203010911 69
    0x90308100700600141c4121003000d41102d50140f650365036004022075090041c815130300300c107201c10000160761543c02d20301d81100e0048503030b41c1401c220f070b0b40340e0241c25100340070365540507404070b5646148104641c1001103c43c22402c004c41c807001c240b800450004080c5c4590941e045075403555040341c41c140001e51800301c4043e080b903003803081c5030074255200c44400d07002da407100405040d000070000300183d0000003903c000c1d90b590b001c01d00106010340350010151070b2900407504400000b040c002603440340003455850f0f106103a00e08000c120741c5041448041c04206400ba660501c00b11540080440022030718000504013100590701c0301c40da11040f50707400206a2055645407001d01010001caa401d000d266040505401c015945019810300360000d0b0060740c0c0080e5206c101c40c00008103202c001d0030500324850105070b01020120302c0c0d100c1607030040c05103c1c2c20300002d66403100041c006070103690248071408030b801040c0c0c00480541c3c0081c0c2500d035291400c850304094410030016038208012a1070 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 547926726 1250 547925476 547925491
    0x61a0c0609030a12090309030b0f160215011214060903030a0c050901021c12020c0604110a030c0308090301090804090e1b012709020a0804030e010e06070602031509090c09 75
    0x145031404403540102224501c154501200b80d4418245c01010700416804000311f034461000d00c02031500c4e6001c4034404070f0032510f4481540d03500c0c000c1c5c80242c4c40071507240b5a2480c54030708442541d0922102c00004044189c049817003803810301100401002c20040306224500b440011031b500c3c0703088a2482e0030b907a640c1d00340780d050240a00510f2801d80e004101c80480d051b070030310010510176140f041280c10f2012500b407080850720014507070394400404100180304500502c01c41c4040192501405440241c51001030900c075905803040c0000781c0329a000b0424000010000319030102591a04c8280d07503ca90701c05400a41c0d0f4613903859080f0000d010309011001d4441c0c1c40308042400c0c03c000381c190140d04004003480d03156240c070740508006403900400078241e1000115100c00c03410074058904801901c0c29000f04414044220307866108080702065044047e048a0412070b083d61b03620301a4001600ba500c41c02e1800c4541800f03501c8080c8114071407001d807801480e181c0550818007003442000f81008 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 547927976 1250 547926726 547926733
    0x601060f0512071d15040303140708030408070602070219050108070f0f1202040b070302030306091f030b0c0903060702100f0b0d11010504080604151407020d050c01061a0c0609 77
    0x105070000701e100c0c90b0b2044660800451144000051010544d071030403001c0d03444658030b000652680b2040e006001030324400d444401104c1248662041d440c000e00c403000300034000c20000a00000d164030054240c07d4812400542041242da00241a5996020405c070851007903440c100036940c1d001d10400e4104070103041181c00b60300c60300301c020407404170840c1134800c0c014145003c9c0c800303286a41c1200d005020540c1e03e40d498000d03524000b134907540141e81007882003034941c011400700c101d0090120b5280d1002c0c904550b08921710365810040c60b0005015800058051100c28016101840807030300c1410790317a01400390425040c2a00c4101d07060150585001ca00d00f9861000701c1d210110039030007085d0804148116120600c004a0703140c03281e0340140e13140d40a004140010010040846001032910110070701c0701d00c0c5520703a030140e5104204c07464001640501400c0490a000f8001403a40041120002c1103860721560f185403034000c1d044e1603a044a60000382c1a0301c059043c8030094001603618080c = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 547929226 1250 547927976 547927987
    0xc0d05060405061e0f030303010906061808060406090204020c0a060b04110c1506120712060b040504020d060e010204050402120405070f030210050d14070201090201110606061606020702040e0601060f05 88
    0x440d000a0190045952200000d10301e134049a80d2520210b200c0390004040700e03682d684a41100003d07252612415001c2824030303c5000d600c0c00440010f2090f21003149c01880c0c180d855450701c0002d4a020b20050780c02c50f41c20840ca110384042030200d07031240ca0103502c0200f11904458240000c0740c204d08a81701c4642414016491502004540030780036900d01103008056484a0740000c070900c00010300071316188a00f15001074860003051000d59024050074080041e20342d400305000035104111402940f1104100c0f0040c0011100d9014034410030318100018105a1114082012617000408081c00c401045040004200c8104840006021421520341c88640b81da4045612051014100014081c0208144a055403154081c0c80400c80304010140c01d42046a0080d001303108002c41071b40080c90082c6c041d0804400050001d004141c080c4c412031404492800d6a1078400c44407104545058081003244056525801106070b6a07070400050f1425514058020340034800c1c40201c0024403c09014 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 547930476 1250 547929226 547929229
    0x30807030503090d14090108091c0c0318030b0604050a090606080a1506030206030610121103071725110102040e06090f190c021501080d0201110403081605030409050c0d0506040506 79
    0x558203800805e023031403204c0b600d0f451406810550380800c00d2200d030b00070300c00e039007441c940c04813610401600907194a4200b079007440c07203130703003020028080581001440380205101d4145948050341c442c032010000121484256070300801c4c0d40141d40310000c5a8420200041884070075020603020300d180c4201000b4646c91503010400038000102404c1c0314075907640d05075515078000e0700030403001610028100060b035041220400701d50015185400000d051004462511607450201c2d40110348280300b42651980f10200da01c40d00404440d49001c0100104844000c1d00090014102034685c101c0d850001c1d160a0043c0117071010f004010b0302c0b400243d8000d01691803a100d1124644ac529001e0108891802c410281d2030106100c000d1085046000c0000449400c0401c00452410f0320b6402441030302c3c99010b074000c4030b019034040500fa05600304803061024800b81ca06071718103445501900c1c1016030300c41c3d07848200c40341265a4030300001d0001307460300c005d1030301d200d2140c1c021012182080142802d00 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 547931726 1250 547930476 547930517
    0x108160311040504210302040e0f0702060f07090e0109050108012a0c420606170a0e0a030306150309110415080a0807170301081f06030807030503090d 66
    0x801180030b256504042418460806440c001c1d8460307041c1400310b000c046020040082d4024859a1482d107060004035030b0280a036541d0341d0203842607900902c095140c44001030203c0070b0207881d10052020740480001e544171020344003070003010441030000d0340c1d40c1351004c00d90030354241c5200d0103007000b1164034074100a081d04010f02e4840c01a460241200c1c0f2481c03510300ca4804c07825088003080c608041c8410006080390700c031407400d06951a0080301c81071540c140e140548400e405080042210084200200f41d819409144d02c46900d0350701242c02441c581c0c00b2030804c101c000d800e80010b51210f1091016103e8505a074096451394038040095850689541000c2050000d400d4412900c4082031966405500186d20103040031005440c01240f0344c3c070f0b060034280e000380e0080310b1b0f0f01d03048941c0b640743c04045801d0364100e4a42c0d00c050408071003507a0008200e005d02d000d282030843e0740c4540220200341050b01902605100c1d444040d41d07801d05035040b91508605c200a41c08020018054126207245003 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 547932976 1250 547931726 547931753
    0x90109150c090528050a0b12060415080a0c0f0b0307181e081002070b0612070e01031518050c01030902010e12060106090b09010207170a021801081603 66
    0x18440003840071034240044900c080a41e0109034404071040080c030400c085108509000c1c8420689202d1550392401480b03070903840791049181d80e1800303000e000e403100600c0031810703070044000b400010130092100954411a140b60400f180307c0d80001c2c020400c001c4d41361125000340a0179150303556003a25295003524030b403000404210400c00c03c0164080f912000070304c4c280207000381d8070031f03e0032800104403240307a050b13441d10a0003c00d00c07980855202c5000346108031a000340d000300c5508403940d207480c01d00082c1d945101d202e040340d02c524903000410700c1c100760b0020702071031203440c01100740316000400340240e40720407400340b0720400880107140009500095054800c0c10a00380401c18940e9400143e606203000703580c00f6048203c2d00c0c010380b44000040f54aa040e64603035103072045c0b0240c8032001c590b0305004442c0181e000d603000240070702203000b60004040080c002d140c03c075541207840c2c0e8041101040d0b10301d820740e81241c02d900140043c10040c04220903c0206031411030f052032542e00ca0b0001c000c0f00c3e = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 547934226 1250 547932976 547933013
    0x50703080c01021b0f0709050408030127020d0510060305090a0204230a0b1005120c03040c1d06010905060703140a03060b161505040809130b0301150e090109 69
    0x1a00c058202429010b6a01142c0302139400400300e0001c00000d0340b0b030034100741000c445000310040450b04070400d20070b4038000c9422645107800c580c20040c04407015211012050450300b480c00e60070703c040c5902c0c001414001c907a503201141905141c0c403200c2d181c4855410410506050200700f2030080720000c0d002c0a40c2c0d40483d00421031304881100a2182c101c29401244051070000421074185100d400242901200703480702c030119414044121098004c0400c070f00d04041c04400070900ca00c101c82c000d150450b00908c028601965240d03032440e46072640000400c5409401c108025456070400d11080040800b0740702107280c01c181d5a00240110180d6111100c2c05001207102000d00c0d01c6540414050a034002c01140c0c0c412440d5592200c8503402d0004449a90719003030303549104c6025006250049602207402c50410b2030f42410010444024481d140b40503945040721690ba40d002d0040540744502c030300c08414882d003000c288007a00a0014030b0015076a0501d4022342c0080c490415000d000690b = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 547935476 1250 547934226 547934243
    0x2010e01080c19210c0c03140906070f020301050a02031b25030903050c0102010b0d020d0203010b090a09030809031626030703020301080f010605091f180204031e050703 74
    0x403000e44152a5010703440c040d0318070f00c402e06980f91115400550150041681d40761894002141441c0201584d10b515030343e40c005401c5404031400a0701558502001e2220480a1410800d40f4404a402c0f50001780c0c0039100032503103083d4202542000e00c0748a401411022041d0725600d803155860100192100d9840c040344000112f0b002d80d01d0308100c5001412150b2100400c540c002810018001c0342030703000c265003074042c000b81d0606941c014840c480b1241800740180015403495002c002207251a1801680c16540316500800715a90751080540f113800c41d03140014005d03005050082001c3d0006200c2125680100b0540352942a44146049002d83c0700e20440e15090403001c00c000e00d2040d07178503020020117002c020b205d405078040d000f0754180c4410608450342888000c05203402d03100e803841441e0300495514003142812010400e1030341e054200501c111072181c2d0310550100b0380964400840516039002c01c081c01040008080211b400c800100342d100e8007100ca0300c9090302c4c0e0740c05100c002c05280 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 547936726 1250 547935476 547935481
    0x9150e070e1201110c19020a030f08090d12090e0103080f0903031c0912080601080123120706090b130905180312070207050d1a0a02040509010b070309050d02010e0108 73
    0x79500080380ca9144960b00003400010145400071005402851058100b4041d06c454006001900540340004a400901900c859031031525240300280143c10183c403011820000c1c0340068603814030380c1c10050712440111442051090004002070050340018001c14180d00c0100086083d54042e152a420401c041c2da0b03071243c4440002c0d00e54421042d0f10f91110780500000100350180d07038450844a401009492500c07807803900201c5141c1c2048540f1030200b24404014070911601000c81c0003c102c29aa07032031412003d0b48000b4250030030301c03c03001c1d0342c80d4400c00d014048030354004403082c01001a0010341d418101810a10020501c2d01c3c021740c9a0f40d942c0300c1c0000d41001e81c0240740310700788042d1001d8030368501e003e03020722010440403940480544180500010f290500d400388814003500105c0c52500401c8488140481c050b02505c0403026030b8003480b0200e201d540784401d40d8000c20031002910b03580d48007880e018103814595449030b48181c040a840502503604994910096002482c001c241035 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 547937976 1250 547936726 547936729
    0x60825060908103209070608221704170111030103050a0305090121021206121009150c092102010f050706150b1e04080d050d020c011509150e070e 64
    0x50120811104c001e9185030143c4950358070f40000600072a50201038034260364542e00b064071805800e4036010f089881e0280c19a4011b01d80b030501c10023440c801c501c00c4906080405543d0310b990025084104c1083c003065008410480905c0788545089905880b01e045614544901c0d48400e14448040c0a00c40002040c003503580c49200880140c0340d40015501140a070780c0200e074001e400c2990114002403603280814070a03d4058201c085001e07014004108140c2c0f070154000c09080c03a042c0454103030401c505051040e801174007500c1c180982070703500c0c115203620b04000542c9481c011500d54a0101c0041520340160340d101030444101b40c010b0030b015035034140d51301c0c0400c0184081c16410f000b070094000045070240754080146400200f074059550201c442c0d4680603424410785c425030961340d001c0300300b0000c0e43e4040c8003e401020003800c40103003000d45080b00d180c2990310303034890a40c010349507407000d01201c16944200b0021001081600c40308904100c5021260340d0042c1c5100c041c0403010f14134003002d = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 547939226 1250 547937976 547938011
    0x20309090c0d15030213021606020a030e120306130b0102030c07060224010b0a0305040201110105040f14012d0609020f040509160215070306082506090810 68
    0x81090142100d8050700d00000070307240070340210380c0358040e540c01c0034a0210b209004900303880c2501e0700240340b8090004010104402548690303400c01524100d18108008104148080d14140b0b00e00d44000c5180c0681142c11401e1060100e0022140e032420300600010740c88110041191070f100c41000142c01c0c44020043c2d1a40c041ca039000107042c4211140407030400c0c1c1c04502e8200255843c1d222618600d0070a0581c502c0c40424094091030300c205010006895209030401900f1a0040c1400e44140300a906e5003820b42e401102c00303540c00c141b0700d4426010011a455615141103190008200e41d52613100c0000f000b5a60b03a5401d0103a0f40100080090505950700c410006c069031801107640703004000b03c2c0001c0382c20512940b0b1081c401080003500c10035403d2201d03004409330707034040c00900b003810410a0100c03801a00001c01c0581d124400703c0e0004081004040e2481902d100e1610040882045030030300f4901d42088007001006c1c14100401c8030005110160b004140700b01040380a221000100c0 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 547940476 1250 547939226 547939237
    0xf0303090206031e011a0702040f1e1506050304021f0203210114010509100c030c0804030f050d02030915030417040e0907061718010b130f060906080a0209070203 71
    0x42c401c10020920500041d002c6550400714103524110010340e07a14000b004404003840e645000c14803040041c2d000502e015801030300102034484000a01c5e401440b0210520200907500344a020307910109007580c0180001144000c010ba403030901e142d4509680031031090001c686c240c0c00d03044a040c0440301c00c14024400c0d01c1c03000186c0c1040280f0120f80c603686020400c0300784a0043c614603084908003030b40d4801c80171509080e9010b000e00c840c3c080d0861040300d01c45a85da80a504220302c0c400c40c1000502010010001180506111446c002d442d0401909100011011f502554820000040191205055000c688203007020194403585d0318202800c1030807843c001c181d1071640c000f4010a5100c174010b50140990b0703280040b80d40d003e4855006030f501400440d911300c40c00b01308000088a400d40071b8440c804415044001040507001d00700410b0f00350a080031904030560700d8000c41ca41c0036045104030030050020090601155203480081c42d114041c2d0178020b805900c0300c0000520703c0303008104450 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 547941726 1250 547940476 547940479
    0x1003080d0b0901050d0201080106180306090606210203101d070e0106080109050903190c15021c05101511070f0303030e010c0e12070807030807020f01090e040f03030902 74
    0x1655a03480c4145000100700700441184030303410060001c0b50509160b1442c0a507982d06850b0a28140d0030310605541c2844071340360405443e900c8007004400105a4083c80e04980d00c141800703c0c030b0b40e0a0103040c006010256602d1030700400407445100141e0381c0029030244061180c0c20003d0440d103410b020645200c0750340b840050601c5030b1031000078494a0441014101c502d1582d507003d0030f9803202c03006001c0c0d41059949009590080c85074646e45010150349100001c5103080c5902c1e1401c03969102c2c1c482140d451405d24015502103150b002504980182904c10803d059041009180c030281548881400b406101651010720b808104501e001e9044034661403206002c640074996101100c0322807403c2c6010890019041c08062056810f05015481031100c864480115010400c0140f04501107414040841031003801c10010b00ca2909210300b030003030742c002d9000719600e01c0c09005014400e044c02000c58100b009a000400002034140301680e081a4091800c20000546042c00c502070400e964019 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 547942976 1250 547941726 547941743
    0x50706030b0f0a1d250818060a050a0b0f03100f0b09040c080c0a0608041b15020106080706090f0308070c090507020606031005090c0d05031315020f0c15031003 70
    0x480d80c4200d80e6440710504200c3c42c8413034640e564442012000d003243d088800b860803003413940c500130540600c042560003181803a03580b5409801c18095031400d1810740710750700380680d50340c14800c215216000303580000d00300780c840e814529030305804a03a0b03032101d50301490f8601e980c4010500700d035801070f0846404a48010404600c904041c10030071311602284c400c1e0041c91045054a8906050045c080011110107440d141021f07940e68964a4000d0f0141c03c06c00811000c40380040b4010820b240c2c3d80c00541e0703176a80006000750a0503521441c0c501c1d0740d04400184003585a0410104400c1d0180c4010340790f2001c401525000300d840d20f02440350840e00094000c600b0402048200c941c00147c032441800104c00301c1d42100c0c81c90030f03840c0840d903080d1020400e0390004200050a404d251002c14811841482207910f000d4900c0029586441690080b00050b01540d002c03000d00e9030304010b0f1022090018028001c400d1001d030000f070180e10181e041004485000c400200110302507003000d0011074000300308 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 547944226 1250 547942976 547942979
    0x21e2d060f040603050a140610030f0e0706080603030c061801020c0304090f150e0a0c0c021008040302070f0803032e06050d061a0f03250201090c080307050706030b0f0a 74
    0x4400303038202d8042c1000091601000451003070640c003810100d80c0101d00030048907222101030182e0482e00301c0c400c1c4141a02c41043d2203280810b40b04000d240440ca6010303003503c50601c2d50092003030b034000d407081e4445d03841803029000c408400706545400440c270050340f00c11f03485a02031140c00780c014002419510301001c107000520307820682010001c0c2071501c408120a88007200c05008215043c0554201050395900003100c10210354842e007c50f00e001e007030182a800490340050074411084071104001001c00003804101138040040030054641441d2051130a4100300300ca03035503804010001c000480200507450039605005c8040e006800000006c500405d07207450024019034400d0003004100d81c94500006100b44568004800350400c10495a2030700345880c612405a03000a0018280d8641180441c0e404510111020b2110301c009c0d0000b044841e11402c0190035240a50301104154004104100020b8004a030301303820b86a140c140040c1d82c405250100701044260650a500100090390 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 547945476 1250 547944226 547944247
    0x3010c051309052d0a0f09200a0803370804030507060f0c08060a0b0c1b0303090d0b22080a18091a1002070b0d050c0d05040807021e2d06 60
    0x24130b0704c104041e035400d100040c54640c0d4202162042100a00b82d10140b44a510a4402000d004000040300402d840380203611601c20705d085510624941003000280420001800e035215603000100100285c2502c000480c00d10180c04502c0050005040260000c1c0807000c20020f40c0c0541102107018a04000702521410081d003030310025580c0b01d00c54440710900241a0101204450584c0c200c030000e4100700c45081685420b440000400a0341400b051000702516112240c4540d1071074000d4050707000f0b070304000c1494010440349002c4101302499024110340400d03601c6c0e040703d0020300030303203804400540c5003050202034425a03007107165550f0512034020b08980018408500c1c0309021542d002030801450826681d8907814411015207075400d0000c21501c0041d90312159000004ca280c00d464902d00704515011180d04507001c60380d1005c045a03c0066003441c2450f50f031130000300c0d407040c00d00b1030b0980d00040600e150080b503080004d5600c40f000170070804010000c218804003400d03903600c50071804c0c07 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 547946726 1250 547945476 547945561
    0x4271403120103050d110d0504060305060d05030f0319060f030b1015020304050306150108010b0a170f0906090105220201030605150a020f071206020c0a0209040c0503010c05130905 79
    0x40d4a000021741d0a00314083c0346e5004aa11050040c4940f581ba18040c40c1440c140c001e00310061880303138040302c11228800498414001010710b4407010781c02075aa4076110440d1841d9281000700444410710704001403224600151054042e80e81141425400c1d560300042c0010f0100150803214240c000c0d0303800c0e00741442d000809042650310440c103950f041d5881c50140003185c4001c14140d80012a0b41c001004103418600044c403403241c80b4030380141500c00000b500e404c1c0d01c1c002c0c2e80060f61108024104a0448002e000107a08900c452000b070080d4240000c031070f01028200000b191161080c40c40303c00840e070007544050300034072026180700114484000058080e4010140c404050301a03800b40302c00d14a000710f15542960004050100c4541094540d03a00a40168118030014800d210b85c0e800940c0c2c41c0c1d80d0309441240702d07080d980300142c2090305140c256a00711900078280305c0300f40503007654100078601c000180d9440040c0041c1c0342da02c503561100003c10308016000303249040030700030410a0400 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 547947976 1250 547946726 547946743
    0x50a0b040603051e01020309120703020a140a0201140c0c0121051501030c080c2b0f06060216060c020d020414040302010e150115080a110c0a020427140312010305 71
    0xc01c0644110322084c0006030a17440304079a0040300340c101d04260920007201001501489011341b04a0741303186075641e00c04c558040c0c501800c076600d0f8040300284045685c46595400450000c1c50304034100034907000c3c0300395154264034130349040c0515000c440032880c414a4207070454907203540303050045040c010390f4140300c00d03800d0f445940041c0c144480010280d00070b20000d40901000f0480c9481c102c221030000c007540c6130000c0c1203925001d0504a45030821103501420011600c564800075002d45070400c0a81703014000100d2052081441404100c1c26810100300c40080d0f4040d43c2c2c00e0800d4085200080c010041d203140803181c014444240014158154030845410380048115144040c014004004403042413203080c12520700c100c603c0c0041882402301c40e4005100a1011031000001a032481840e00084905e6000c0e600101c0c00c3c500f9072503e801521405c0201c00d07400300210513009005074200201020140184c541c0645801310f0716010802c42d04c03002c0c03103950902c080303584900c0c119403140c811 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 547949226 1250 547947976 547948003
    0x20f0a06030f18021008040606030b01030305030f01090c20190b0f0a1a01110703120210060e041109040c0302042c0f030412050703081812120706050a0b04060305 71
    0x10200d0520504810a03e42c05442d0b07002440c00022540b00e00049419540c0140100ca0140e150071b40000010750700c2038070501851003030b19115140c1c9001c5400c9155600305902c910040350419411943e51358000b40d101c03100104003825414810200c2030f00070302d40100011010a8203883d0b20402050041c0c0c100118041d1742104078118140c1c69241148003034039003450b251300119034a0346042e55998021051050240303241c40640d0703503080d41c07038860110340c11108000c840941c00c030040ea00b0313a20b090341c412100900350b10301040c071603400c094803044901030010074464007548010002c43c06000b5641c0600b8005d40e0300510034008110f942c3c1e00001141030314a40d0f090080d02d03640601c1500d0078045000d50b45040c20300c1c011030400386080396072610070b90031040c20ba901d40074944002c404a00400001d0405c040000c0da852914440d0344140498255110324406103904140c03030000070030343d90108441596402c12004221510f40344035002c0100707841031060364010328009001003001300c0862081d410506 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 547950476 1250 547949226 547949231
    0x203220302030d020705010f030203060f030a210c050d0c140604031d0105072f0622050303040e15040225030905041e020f07120315051813020f0a06030f 67
    0x80c0c0d07003040c0e17a140c6480c041c507408174042d0324558408501c40d86c05943c0c04040180448004c01c0080e01080c1420244002524140400a5038800c1c4800500304c4215039145440d02109010341d64481507269091042014108017411710300d04180240d555554900c400d011055403030300e040501c1e010f052681600f0f1f048001f40002070805810b580560141c604458001010340300a240003031350141c407266040d007000052841c0110580c40c2d0f8a480c1d000d450f10b00c00c1010050703160b1294011841c0095115880144130b9401084180700a0000c3e04035a038000003030f001e03520f03800490b460000f4068091003085120b40e100014070b181203c0c1c034003090500300502070340354200382c04c0e2a0390038401918605002c0800c42400c1042e1466240301c40d070300500c81c0340040c0741d03200e042145a0361034400c103411590810000070344991245404030900c40c3c40304018041243c1d941d01e17160342180700d40c000382c80007410742d10501c0421040406646551040e4090010020002c41c462522904050028126098656072040c0b = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 547951726 1250 547950476 547950493
    0xe0f150f0f130602040815010f0806060114130317070b09030c031806040b030408041a0304120f090e100e100e060d0611120106021603170a020322030203 67
    0x180c2806809004445458a41150350354119209000c030040e910201e460b290f082100056401c0c06005801c40c803e03100388004095454803e03c40728401d0641c101d01b82540041c001c0c410705030381040c40e140070340c210318a0003511580400ca10014100513580040c0c41070700d90300c064120000c0500000c1c48a1413180802ca541529414100f558a00030801e441c4250351041010040788040f222180b0742d01c5100400044c542622100350030765680056604844150002c242801590810701c4c024036600400d414a905501c2c09807111081d070f004481d82c070346c203000c846001c1000091084007900090300d40013000e411641001c200342d400d000b550f0300c0b0709520b03150780101041441003115110022031700102080d6101e0b072a00020400c030588041000c8a00980c0d03420270703c0e608900d0b40054000007026401f5000d9a6142110103400d00a0310314464220300e442141c1400007800c03210700c030b02640e03030b0895805440700070362070b8264030718407410101042500078100e020580e10803000c0f400b410303644298184e0701c006 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 547952976 1250 547951726 547951741
    0x6091315300503090411271f0e15160302032709010e061903120e0d02030706050d020909010f0f0519061b060203070e04110c15040302010e0f15 63
    0x4048040001d06540007008013080900c1c140d040f00301c0a0102411052600d00007120f100b0104d401c00b074444c1c51a10030075841480398500f140000da5540e9840081c40c601036914140100016244c1112900c140160305903142d9103001d14080d00c28203011060490980c82c0c0724100a5aa9000340304114034059400301108200012004900034882c1c014040342143d9090100200340150000c001c150002d80e00b00c20403541c440c030914008000d6014000030003c07014100340c01000821901c03150360081101c255078900607100020a4011170381180341154880000c01503d0010b4400c3d002e803650700041c02400400c002110b41090f030100c41e08110241a00d031365840c00e0101800060f03441440360b20440b202000030501403a90801d45071000c452000c646141680c0d07030000c0341c00c1602c0180014541310201400d03401d2034404c03400d40b401c0410010f1f081680c040302d45983c0d400243c01207449503822102080406000350042c00c00031507008250fa090700b0410814550710036040383da0101800c131403000314026 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 547954226 1250 547952976 547953059
    0x2102041d011a0d0f1a071205010605040b1206010912060e0106080115060e1306180507050f1e0903011803020c09070c24020315030c030c06091315 64
    0x2c410014100046010590315980e541840184095440d18a54403544c00840041e4001c98032401c1c0d941c0b9502c00c0a50341444440455034140c00c90400d01c4001c0105100c6007030030383d007643c4024603110720f44005640c0306001284c02c9019070340306c84641c81c000c41a010810500341c004060001140c0000c00c4681e655844c4035003655070140021919107610300701840358520580000c1420388000d0241c00e4000000c903e80401c540d2194007c900c40c2020340c0c0c052081b001e140c028160801024505607007814540c03040140d5511850b41d06441000b09840070105102c0c950065a8003814010000c10220481d0790150220500c0207800310018040d00c0e01118080c50302e045024013500307030707136560800f03c0009a850721090031002c1400750388200a0300a05411000784d000442c46803175041d001441409c03811040c903261030a071a403114840d804c0001290404e480755000d680003844112107950201046000b04030003400c1c07100305c036240c041c5920710100b9200944000c0c000c0d000301c45110305c29400d6000c54603154 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 547955476 1250 547954226 547954271
    0x703060e0f041106071115030403021903050301261006030512040b0d0e16060908150f070513080109050a200d060b0f18100602030307092102041d01 65
    0x2c07803d15a07070328881c0c10070b20007030130700c26100d81c6185c0c644036460b000041c0c40e060b82022000040e000002004101641880a850500840690526404c581d580c1c0649036000500402000c40001904030010800000d903140c488401c9000303841030704070030f20480b0300549040d010070746091081c166440420010007084404441d01d10f2a5a401c08052558083c0034100c02c0800200500c121190040c8042004100030b000340180e48400c0c0060303150031821030828682c402c210f039410075400c0400116000b01d0303110075400b4031719107480c59442d2001d0031055100c40d659003102101e0341c80e15094070704101e40018071050b02405040d0743c1c002900400102910341d03401078091500b088a50a070080007402d03075002880410030091a01075010504008200c0804942280103040e185100a002a89030340c803054401400d91031002c1e41c03451074819005008001c1c01d100d40e80d2104010f014800051154114800040d0303402003060010b400008507160340c4030b9502c0780141c415440e20a40b91180340710f8010401 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 547956726 1250 547955476 547955483
    0x1401020a0912120c082a10020f03010519080a06020406140f0d2c0a0605060d210203190c1505090d0c080c031b06060a050a0306020a03140703060e0f04 66
    0x1000c007020b4600b20344003a002c083c203c1e4202c000f403080d1458043d506c0072114036041221450602d61a13030f0401c10349004602040c8540191040000302c1d00c0300340c1c6c1d03801c036815140183c030f09000820104034068408100703a44194914002c1141180030084180c00800072600e81e41d882d1180c1c0e00300188503869620949410548000b010014403051900c150000c0c990940456124000080210046a04241040f00401580c2c000d154500100000c0d842420340204090341c203840f0035900b640d281c007000d00040740110059002c54810070b03105072081003144c0888415034540120403554590140004603c2881154012a00201184008464825980b0030100e0b0001011040900700e03090301c0480d612041030342e050317204100c104600e04042000301154281d40510a0008e20720b00b14260034103a0242c129485800652420030169913404e11701c02c2600d8000d1b40040c0d44616000b0141c0003011807110348050803105004200ca05905980020121694502e484110b90360b403001d203002020003214001c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 547957976 1250 547956726 547956743
    0x6030b10080103060f0b060f0a1b0c060503040f1b0e06221a06070b0415050402030d141204080307030e0325020a0f0b09150a0806090a091401020a0912 66
    0x410200c2e030319800038000d17001d040c0000200d480048000c0380702075100b80e01c100d1201d42c001034031486075036001181204031000d80c0c603c20038003000f55540620400782441144e0030400080045003e000425003503401d815448000b0300c0b80e000c010070480500d40b8861041d40c01204e80b030000130740c0302e0410300403418425203c600038003019498411601300174840c42032100e0043c1c1d10072070034464544070f4600501c035850190714a20100d20b854600000e8804000d00128a078a040c80140001624000390321035804e81c4034103102c06000102104480c80c0d02684030b060380d10400b004140006d01400c500214040d20032a54140480c50418242950b0391043d00c1c0550301d4074a5565107107025146400c0642c13003880c40200607540071b0356140c41c0323641180308a070130040340c2c0314000510450518190814154142174403e00c035051030a200000742c07810030b00403c200d004200480000b050f0358100d40c043c160720343e070080701d0b5280312519010240c001e4105481c0c0da4003240b51140040b40a400300f20902030600c2d80f11080 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 547959226 1250 547957976 547957979
    0x506061f17070c020a0807050415030309061b05061323120a0c0c150f0f020d03050c090301020f09031e06132d11040c0c1407081606030b100801 63
    0x602040700c50080c0800b0420507001d0601006070b8a80d801c0070010420440202041d5081c40104422903000042d02c2e082088211000c0000075001920340d400c0703071a50b007080314403041c15007424000b4480701403000742103001e00c10810038580c0081c00043d161501a1605042c10103500317018100404440c4103401003136025203662000303140343c0d10050000d0100381c90000d584101c50358a50800c808241c000c1981c103001c0002550680d075005d89001141542c9103030442000c05a100007035200c66910080400705622900000e0480c81d81d40121500420090b00855880f0301440301500d840e0441c108540c0b103801920302c01c20b01d1202d551140c005544004002e084103032035010410b0010841144200d03203200d03d8074140e441d00c402e003050340c3d40350340f40000003421102420303d003032400500d58480240c85980707004640075145501175642c1f800e0b260f00c030070301c188208400480c45161050075444486140302e0389084451180310805040110b65880d101401340c407035114200118968480702d10340000d50b24600 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 547960476 1250 547959226 547959257
    0x2070605041202090910141b12010501050d0b0303180108010f060207050d0519030507021201110d11090d06021e093607180608010308160510090506061f 67
    0x1d40c5070805c06071400c03980c0c111050461041a40e124031510000e804100041007650880f1040309000308200c1c40c1c1084c680242030f58001c2401606000c0e17241000387c0402d03048840c0000d50300030120304c5c8004040340d498080064030b15900010800c206800201e502c400041e0034035103c101e100c00c4d00d50640240c07182504160034802d503000600b02c107403014803400c5450f29441440e480f010714050300a940d0940d0780c0203035006214000303c00c06011a141c0c0c0c5019181c6140080c000181c4200d4510407002098220700c80d031041625024030300f15a588615040400010003295038028069070b11a030b00344201010985503100000d00500d9000358008540d445220964080c0c180b1075894819481540c804000001c208a80b500c00102c80080100b200f4a0a006281902c004038074020020381c9006040c0b07604660301e003021070040f4920b40e0089240403031184100802481014011680c81108004401c1c080c28420342c0d07075400382c54240c0101404181410030f00b0001d04d088034451050303111401d120300c0004 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 547961726 1250 547960476 547960489
    0x50307081903170115140307080412090305010f020901020f06010b0f09041415010306090c05040b07031b0615060e0d02090406111605070501020f0706051c0c02060702070605041202 79
    0x280120104183c0204021450030f40f509264003030451800300000082c00c1c6903011b0020114007000700e5803160140308100c0c80684c80b0344207075070060740010410074a0110085c280e690b0b01440e00010450f50034074800a084100c680c1c09400000000d074211a04010b80f00b502588070383d401e00071b40000c002c04100c0382010062303c5c00144542407019100244028003ca00380c1040c1c00c00340c41c003074068000c00565601a6901d402800098240302504001081d210800500a4411071144007503102003c034188040c58002c9509102c040326000d442d54407640c480c40c0110080c2164106500180040c1c0004206907100f0010180e444c50054007402a11080703400b01b11066200030400c071880ea44814174080c00d0080240680341e5030004007400703c6000103a14040f418242103800c4181154030140740081e41d0308000807048110355050408581e507101525401128450710300c04555110f003400d00521072a5070010fa00c501c110744990983d08100c1d1550030465503032290307200710222a4030b4110100058034228 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 547962976 1250 547961726 547961773
    0xc150d0b0102030f031e151c0c0e010b030f0709060509060c01090510020c010e0f1c14161101090303050f0a0201230f09010903200c0406150905030708 66
    0x140120b1303040c901c000c903255a10f64030441e52007603851120903000d01c9441c0c890b21a076070060303104070300b1425a10f00310001c2000b8600b403881d511011400154060309012000246c180901080314000c0e1103982c440510402030340c81558400300c5401e5210008488520031454030301554010b5551034903216002040051300c3e00104000710980d5a12804c0c1800076a0800c80e0340581c12b02e0f6140503843d482c03520b032402e00319410803600c01100d40211544104802011900031044110880c9141c10800e0984e000c07944002481d20354500707100c0c0020f130844c0000c054005a295248500b029003102c025400c0110b81a803810710006000c102e0520050001ca00c00202a2400e02007600c000140d248404003400c48440010314003a40c000068000c5c04107422030009507aa00221190091200000e107503401400d88945a02c1003c0c054003a8400800e5503806020078451110018410704c00302d130b261041c0101d41601c001004003c20008880020b1605010070880b044602101c094400302c48907200209410110 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 547964226 1250 547962976 547962979
    0x1805060a14040e010e100605030303090604240905100b040b010f050a050f070f030206010b13030204020a0c021201050a15030f150b1e0103060609231c140c150d0b 71
    0x15051040c5890342d003407145d034000c00c1c00040180031500110072014200d4045030001030003504101300b0400c010400258164100e85d0102c000c000d400120a511025004880e20a10380582801064014044d00045103850104410010006042d08100b048211640380c885c031800705c0d0400c030710540200c1c000e01c0079003400b0788241021803400d6400d01120750240c1c000302c8212881203441010320b0500d0b50400c145e0780544603820401d440c4c007204034120b480640b928800241700fa600014400e801600c01c007001414258003070a4011340782a8644114040c02007259811040b038a448500c6074450380005100c82160b800800002c104030241c3c6440e114581d0b40d40b80c41504944a240800558490380340b503000250300203549a040c04481c0d400107040e2031141e482a0200104200c0500c0080050b0029800d040855114a0310300191403010801e04541580311291070442825000300784100071080c0c0c0c40c2c00e8151010350302a40c65070b10400c1140140c098580384040400d200030002c083c4194041d0000700d00 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 547965476 1250 547964226 547964231
    0x905060306151309260406021002070515180d05090d02090a0603050d0f0909060b120a06030209010f050f10050a0818100e0d020a080d09021c08041805060a1404 70
    0xd8000380e44050700c000382e2080707481c0e1185a175110740750120038207415107114028038030914080c03030000300a544544003442c3c8402c2310f0740000c00d6002c0007020001c8441e520800913100d82507241c00c1c3d202a440421400040000e0b020315404084164890070484d00d2030400100080d800444640030f000020b4002860700503502d0341c444010001c10f100f000039103038060311961001400003000740e0003084a0066800000490b090207000d00c0682040d41c00c3c0c5001d103a092601200940d02d40701140060301c0315500194101c038070040080ba240c8400d11000c0e00740c07641900c041c4440707041801800340001219000d600000d41c1840b04180d050310541445801410107440201500014603010f800c1c0350100d00d4009680b5500c5c585661041c20520501a8000449c0080c0040c0a260b8650007500d10074048607078060f580c1c0f214468110b690301282d50000c0c100c0d108505407a4000c51424068a61040c0103442000c0c8010500308841c01d0540103180c81031601604840c40f003840e0005109501c681010076581c040c1c1c = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 547966726 1250 547965476 547965499
    0x1d16090305060c1303050a05160608010302090103080d0219031a0a0b09040504051c0f091d010e0601020109051b04181e02210105011a31030c03030905010306090506030615 75
    0x186c0800650300c2c9140110042c04804603038112001c008121507020b013050007507441c010005a0b480c0002c15044940055415996424040d8000028820842ca0400c1d9043c6240c02a241c590f06d41e0020359241c4a0050600ca220500410041c90031100c2c0b00b400c03080202008008000d05281c0c105540082c460411034016480007414030907514440748444002694042c0e2580400b644098100c00030070881e011300081190f542d82c11341540005026058203216503101040c500c0c2d200750300c855030094014007030b1a046021489225004100700d003a440c412030a08651f0a01003940715288085180e00241c00da08166000003285055240020182da00c00084820345000c4c06038100704018050628000207050340c1003c0c11a030403102d03402e100c11884003083c0000c50481c0030300d2607d21140c0c40501e400c4200105900c1c0c101c88640d003150001010f052044900100709500f1041840940d0030988051010326120106074044480c1113034505d60680c040c1c00801c010a07402c50310341041c200b000c0c28a201c044d = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 547967976 1250 547966726 547966733
    0x1503010e070603090210051602090405120f0c070e06100e01020114010b0a021b0d0b19020c0706030b2e2024060f13061d16090305060c1303 61
    0x21907107501440120741c555400c2001c515002d03002020000303d40c28020305094201514801ca041d149800074040c041c1c58000c28144442000383d02505071a00045603901e012000d004819500403542c04001031146120104403015212001441140098080d68002c000c1010844151101c10921415556107880300c4c01843c0c0d080c8a0a400b800d000004590703240d8034000001c1c42c150140d503150078a194150701c80d00340303640d40b50030700c00d51943c008405080e140c6954120b0810f030070907a080c44844910016411501c0030012410348100c440e103071810000704070300c0001e00c9292400032250105a480d1030f252406c401c044a600000305c08001e2401c0c4207045070f5030492401c048071528802e005503019200c010049002200c0103102d024102801c0c1d40e10382840c8011814101c52000c0440c42a13043c040c1e400080e5201e54012401400d840440f2850b051101e0000c2030365420985901080f11001241d2084a500803000d2000316a80900240345507581c83d400c0c941185c200440c1c0f02503030783c103541000010 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 547969226 1250 547967976 547967983
    0xd4a0106060e030f0d050d020708120916080705030d0f051c0e01180b0a180501091109060405040b060603190626070608040303020f0403120e030706020f061503010e 72
    0x2404068076000c840c01c510724101460003000b01c44158490317101240c168000c640c048241e40d2000380c50100981c44040601d41185d203805600500c000a008603020070001a800045d007510b8060903182c00001161917060250b214030441c01907079010303403000c10564092845520b4900c00e164891404505241030500340038162154103101e1070072951515012100310f4801c0c890020300c500140310100c2c1181c800d60361a0403038074005040180c05a5904200e45d4101c1031122070040b140d038804d00800c921641d501d4805c803100c41100e0000c0c0030303e0790040089c103903041621415010f81d800181c95a030654904080218540c402000244400d100010b80090101d09020745e201078410800c801180c6a09404c2a00850303110703100080669109190822410f17821070301480e0800d805203009079035071144501f181c00506c655880202110418035005541c55404a1110b08a5400318207030b07070b081541c03030070100e0713442c407a41d8a104201d030400c1d0040b5403411141c81c551090000b01400218040c0103e5031301606 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 547970476 1250 547969226 547969229
    0x7080f1911030a0509101e0c02070e040b04030e040e1903050c0106060e091b0d05041707050102120c0c070e06040912080405160b1204110303040b0d4a0106 68
    0xc440e144d40900a02c1c0c41d06100c0c140701e99010b4801000741c8401030641000101c48a0030342142e00c2d623a5804012680d10a01400c1e02908007806001c1c05420705c0d1030528880101141e081c0d0016180b80518240e43c6400c0c003407241c9403080d0310024010b11580c280e4445001e03102480031030a11004111100d80550203000e00e40080c41151244094103101209000d65104e0050042800e500091003201c00c40c08400c00ba601102070380c0700e00003541e03a101d24000fa458441a0301e0240702050100e00381040100540050404081e64550402c1a4503040702440c2e103801051410383d040c0e085650144400c02820220a0340300c40b0080c4082680c0c036060304c6511001c002240740c0400241410200002e010381048207914884510580200d042c2c586000c40c00c0600a078420b105460307000c2804181070140b011001c030b030b4000000341502d42e101d50328414030100b6400414080101c50400034001c01403e415000c0c3c20320640c0c40c0d03110241e840d40b01c0c00c1d1048101148050315850702c0b07540c601e0000d0080e00b44113200 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 547971726 1250 547970476 547970491
    0x3090c0918010b180417040b13090f0506060d09020102010b0405010312080f04050c09090a0c060e24090f0d0c030b0421090306020903030702040f050f07080f191103 72
    0x410508a00280d5094454004401380212411804201c1d61803440010913485a008a00c00b030601001d5220700c032aa10403030b4001c01c15000c000c21b030f40e14801c00700f2240380101d41c505901001a046a9400d0744192071084818a602c030500303110345154126181c00c9801c01a01c14800004e0a401d0b83c40020300700e030400c1c0c105071180890309800a41c0d91360000702464000907400803c12540c80c0c65900c0035660010446814010700213440410141c444c1081101e104aa2110640c861607441d030f940100180702860400707111f840620f1444902240c0b0121880c00181d0081c9803520740003541c0140240b00c4100f074800703a00400c8072400d88000c160b040302080042c40c802c1d0002000da0505041402a00c0034920031301c58142404444207248075080340c15241101e501c00b00258541104600083c1180611440a5007140c1843d00c0800700101c240c1c04244134280d0000b9a110740e0303e44c50f00c2115510b500b291085910940b00f004a0119000403000c0e04c00700030300082c04260b880c5084c800e030010341c0050b9444d2 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 547972976 1250 547971726 547971751
    0x21161d040f020d0f1d06160c020301020304110301060506070812040c050d0b06130501150c0302030c0304080313060305070203030411130e0c010815060d0e010b0a030302030d05011e0b03090c09 84
    0x848000c03118010711008080c0c02c500e01c5e4042100c1000d5544490002d04250044503190403040c00040c021102608501e400030021502d030310705810046050180061424480e500c4c0000115031480d240b0143d0b00c05682003130030f260a000b01c41e8086040c00300094015a41250312a00018043d90344180c00d1001c1442a200100755090980074841b00d811216100d04400b820300c80103010700c1c0d88078078000340b081d140c138544080e01030383c00d08099003944a01c0381c41c40124040014045004807001008091450110903005401580c0301422030898001f031b54404010303001080881c0104050f28030584d2440401000c01203a40b8041c110320088170035141c144a1590031000240c1850360b00145069484112201203215420030000010340b42d1040e581c0c003a0245a455201015512007540300c616075410291111076901c1e101d05000e56a9041454900d9101d400c0130300114541400340328039010200c0d081d84882c50716081c00c4810605d0741005002c09454400d99141050541d01c41c01098010324081c040d1 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 547974226 1250 547972976 547972991
    0x90712080c012319110c0a020310020a0509131514010810030c060507060209090408090a06030209100507030e031605030f0102070f14070b21161d040f020d 68
    0x2003820748070705182688084140741c540c401040003e003c040d44c400000320841d444084d50603148001040464011040203101060324074140d0000500c9501c058000c4080b545001c280c02c070f0203820380c81041036290018200384901190b07402d100c90840c0a0075042d500116081151240902d0b083d849a40702c25440f2848a0f1862203e50708140f54582144059050b0540103007903448035548421244221805c004c0f0014811061106c1c660580340815002081b03450b07107090504120005800c98894984940c02000c40055400d000740300301e804c14407001e0000c41c3e02d0380c6815402d0720107410400064040c8592848042c025039030920110300a0107074102a4480d01f41020240340c5004c40c200540b520340da204002c1070022401000311000c00e181e021840d11070b41480890910b00702502079009013903040c0041000240ce0406100d107060302c6414410000d89550f0300300341949481d82070242c020205010380d01d28a00551600c005e041c1140d0003420210b4241071a4590108a0b8032041841040d50f507140d16 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 547975476 1250 547974226 547974247
    0x10f0f05090c03150c040f12030e01020a0b0c030613021303121b06021e07050c010305060a060e0405041b03080705010e06010506030c28020105090c090702120309071208 74
    0x34094001000704000e20304400d0b00d10100c0c0d41c80010038404000c4100103000254001204411a0301030108460b2585035684d560311403c0302210b0119003200440e00454611002e9440000c00201c03641d00401031080d5911006001030056001a2038070b604013214011b6840010018001040100454950f0310a1a441c504000a00c01d00c40b034080c808100003007615242d481c2c2ca045031000140d4110348016a02c0c2c10025041c441d80641d0410001c9a0b00b002c90341c881400f074082000d0182c20820b89040c1714a94405003000407801c80c42c001c02d408100c4a1011a59908095124a500078442c40015010407114032207518a1013107030307104440001c0c0015040d42040000e024a10248621030003e003103d50402d80007030b00c5400700800d8800041c2020440e8080d1040d41d40444007800c180440c281e126550529000b0b028000c01c440c0d0082500c00c0c6104543d090614407282d0b8416043d030707806010198030103144002d465102a1102daa18070a6100c0410043c2c490030707406d0310141c404d0011a507907403007448 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 547976726 1250 547975476 547975481
    0x3090a020a0611120319140a061a0a030e0f07080c18060102120c0102040b27010908100b0f1f090f030201020c0405070507150b011b050c21010f0f 64
    0x41080d41000580031083e9000c00c000580b0300b80f4009134019042d1603a88031341856019100548403050103e05003500c1c030b015a490428010300440040d80140030355922900e10140c41d20f5419285140000c0400012071014401c3d40440c00c0034200320180c0d04015100350300b0070b2800629410588554110440659040c501080720413242000c01200500741e01e00030f40041d4031140e00074243e405502c0001340101100c1c100b94111030241c000c010119132198405007a4070f162214210b0031600c1080302102c0d6001d99802403100c1c0044490f03580003400706814424840b0042c22640b550345411401c800c49681140d6601d143c20791420503661840d03158400000c07401000014103070301c0080f40b0010250b080c00581d03070115150cd0a11030030740740030689072100003040ba40d9100e00000504170108241e044400d0401715002142a2407003641d0350107000008617044c01032040556002442c0341c0c4800120545801c01011800c00140c0743c05c0841c9440700411880303800d40305480321502000b0ba03554681480602c0f1407 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 547977976 1250 547976726 547976729
    0x1050c0f030a021515100203190302030114180c090402130314010c1e050307120e010b1f05041205030c0a03020f0d0e01120f060b0c060a0c180e0402040b0603090a020a 73
    0x4900318075807401c2c4030212003180c400c070300e10141c010074111b40318400c1540200125100d00001da00c01103100d66039140014001d410a014158030714030780603186801407a0911000350041818201400e254684500c500060340c44600d4035500075800303012403070900007400000c100441c058070b191910f1001101c0001d007110701c1000607009101d07542070780c09440ca035a942d00030407461040c02e0240c0d032a25001c4c0143d900c4c101210550384400e04151a05c01580d03419008514030400540c2c1c0c240b5895844005155000e00c00051000040d00c240401c1195030540461003251034002c0003920700c1c0c840d400e403d050621508440642c0583e101d000c42001042c0100070392040d600ca90300e010403a400c00d500009050201c01c0380b402c2c0085841c2c030420880e208565000300c0040ca5200401039640800100090f20b600f4201c401a00c85842c10905c1c09c411801842059141c00c11407628203651803c1c807010b5074003403d0142050341c00617958155000240c0300e88004600941ca00001001042100e20400440c100c05 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 547979226 1250 547977976 547978003
    0xb0f0909070303050304030c020907020c040e030405060a052203030c200603060105280906090f08030403121b0b09010c021f0902011106280603031d01050c0f030a02 72
    0x245010400030110115880090782c0d810314180342d6035199030504441c0040e4012020354801e1440307042c40074031b540000707414180c0001039405000744002500c1e05070b1a80900d10589800220800188915901c188001c2c00c03a8035810704210200c0184041c80707102204190000c802043d003e0b03481d001448404403c0c2c503000092281324102c0c814503500410381c00e00011305201e041c4003000c60400c40b101c5144444811a10103c0e50701811040041001410796030140710f14030101f010414003003041621229040c1c1541c2c1c0c544001c0d4601842c42d41e40d00e10402c050200a020010003401410501e00154440040700d80075090305921414600403030b5003140c1f061110841998001c0300754480002030000ea43c1164a010040000c10075294001603a081401205041e181c0c018101040003c6154016000e0900c050051080c0c08040800c800c0040380c84900010f070100700000204031154840900501e08108103241481c20608410031161070701d90380045004c81a040401c0c10135290b0783c10807080314140e22 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 547980476 1250 547979226 547979239
    0x606090e0102130806060d0b090a0b0a0b0a0603050f0103080f04080105070e0f0102011e0507051615052208030a09291b03160c020901062d02100b0a05060d0b0f 70
    0x1002800100047c40b02c48001b08540c400000295200e60f0500c441c41c1c00603001070103615136251298401e03006001d01c1c803c07144522440f003800f14034640304e48a201e2244446804240c0345900790f48941004c1d030405c0e01c000b07200040400020031803a10a02506000c0c951903201da2042e503040c4010048a046a076400c0d42c110381c94103185000c0d818094551036410b0300c04240004e096182c14008071800d120314441c2d0f42070385c080c0703e4401c001c02038651145040300403071103010017482d2112600301c400c545003030f4200c0e603e0465170914030000c194894000c580120003044002407410580d6120160400030481901600b00448240c601644030903031318a501c941080030300b40207140c0b60200001280409040140403401100a000550b4001e071481c0180940041480d0300d550f0751510014219825080c5070004050b90441354031000200c10030089040b90700e900030b48000e24010300722400502021410035803149600400140310f884074401859200060400410300d59005402e1181138903202e407446020b0705 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 547981726 1250 547980476 547980481
    0x51c02030f160905060a050904110301060f1d09040605190b1e030322060207060f0503280c02071e060203030619030c17060a06060e06070606090e0102130806 69
    0x1d1041000c5500055240c0450a41c901d40e480440f0303c0c181a42207950002000aa040400d80c0c01102400c244c500890381400400e0174003010480c103000a00c161000f04503403031340001115005210740789032581c00c0f4055082d4140614002410408103940aa4003241d6420501200f0540d10409444030011402c0030302103524150081101c030880c00100c400e08210f100242400c0e981e00b40111540c00c0e0444188481d0101c0c07031144801e000010f407050394058412480005a02405401c0301d80c201c002503102d00f41550340700c0b0b481110f00030a4410082d0440007100001307841c800c80d4403c807481200700303600401d0b10900707108106042c12449241c402d202d2114420800c04140c2c00000c403a805401074801070707072043c480f0400311103000d401d400003006a0111100814000081c454580c0c13006000011580039480b0300440404441d010300076540041c0000c851f851460070014010b00071b40c1e124600c00603080d6521076000301201c100d12440f1405035000109c2c1c80718441c5030740500003c5e050300310141c101c90 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 547982976 1250 547981726 547981741
    0x2090307091a0f03030d0e0f0102280201270203010207020d03020304080106050105090a060e1c0b10050609210a02030a0c0e07080108070e061305040b0a0e070608060405180d051c0203 80
    0x80c01080c0d149240c0315107d40e03404c074515206200e44003e00c903407000299100d818141580720b40c084001072410401d01b01c140d035640183d2050160202e0021400c6205121102600c19851000c070300100681c0c0641d000c01c1aa001030300c2d0308000c143d03000c0c025030140d0f480c1d6081414050955605602c0f0b107041240078411007010707a444204020071980c7c3d609064040c10380b8440030588080300022002518620752180310203102c00404140d12a0241e0f00807440b00c0c4c0ccd100c0003004424000c500d07860742c0014000700b5260003c5026160514000300d0302c0100c1d403840309140c0c00079280c00c0024808444041c0c1c408004c100d09010701510507044000381c10700301c0c0c5542c18414202c0d9228498410141c0d0f0b1790401c030110700b10b911410f01e094251050410240030394506404d21105000d0117541d03031101d0628094401212200101d1100184e44c0c65985a66442d11080104005018094219520481c00103041c0580920801440c8424030094440b00d0300c403150030300354200722010301c1d02c0030503500d00410401204 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 547984226 1250 547982976 547982983
    0xe100507021e04060e040c0e07050a02031819141509012312010e070905010203040b040e0a06080106170d2a1a1f120302070308070602090307091a0f03 66
    0x9091410511841c03602d90100082c01a0056500101e145040320003032000744984800038a0681d203518082e00150344412400302c0d494810140184010303041440003410503403061074482e90b440c03801420503040300c0c14804402c418607181d80c030840061407001060441418001c03150103c55880001d454100aa2400041c001e60480101c0138004451020868028200001915488407025050304920760f103e102e01c13443e03514150703602c5000c9080e8400000303d540c03000003245c00303445241001130300b03140c50110a00441c000182c203071020f40e44c45500c0410701c030f1000d00c5a5001030400c510705c4020308003500c3e01d02d82800c1900c1001c504205c581e282c54011a01c1c1c01070001c3c2007607000840c81d070902c88541080815040000480c101003880c2505011101042007011088109041212030416550300304440c80e070f8000100c02005030304140700400c040780c0300c400a040d50078041c600140c0340110500000c0d0401c441600140e804650382c4022440482c40c824058103501010b4030101c840d6602200069075 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 547985476 1250 547984226 547984249
    0x3030314040c0e04031215090b03062401050c0d0e0a1d0f0408090310050712090c05010819140f0105060903120319141806010e060607020a03050d0e10050702 69
    0xc82c500f48402003000c15100b90344480254503859401c0118402d80a02c2e410804114414480c40340d091644d038401918001c540c0c2c40c0100058506c030480d5581030f1a81c5c40c06041040d0f40281480030903c14411000000d100c8001c050301c50b076a9084581c0d50304810804006155000080d00e180ad404503045c18003d071683c41e50308202d1581249840d40e0325440d211300c052040300c00a5806005040000307154031599048207010346490344a002710306c0141528482154000c910241000710049030401807540910001c0d500b02010092131050440c10300b800d603040c0c0700e00300d40c50441d1400c490100500f00040d41465400340400b242c8561400b0007075400aa0b846106511400c808100000458424003441303c440b143c8105c00e4030280300720a007640b00c11078200412074000c03442c01000c5094400103040814024144ca00d80c4541c128981c175101e080c040d65402545080741c101101308800b001140d02000307100880c50495039508412031029080c055141d400c0d0340341c282840b100f03000c91001691282e14121 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 547986726 1250 547985476 547985489
    0x110604080f1602131a060702030c0d03050f0c0f010b040e03091e1002010b03010c03020901081801110301080a0201020c01022e09020d03050a020c0306070c0f031205010b0403030314040c 81
    0x1611048805100c0600e8041100000d610007140701c0080c620581981085c20b5441c0802603084007100328074184034081c81140c600035403682090029259624101411000c03042c06440d20fa42840340107580031540758403801428100343d00045448103e841c2c24012212013002c107407024000c11407800c904507901c1c0540d10302ca6100d00e0034120400b05003078144400c17010805005001340101021180c02078003c06015941602a500340b205d40d10240780603008035070034444180d5540700c290361000140710031454a60844002035484c0c15a2140341c0816402841c0600300f0400600800c0005200181ca003800d000c0040341950080f280e05c0c0740809e151144005d08070003007200001d0745580d62217540000c19601d60000d40c000c15803007111041c964450301407c03561116070212203c0c25000000c140d9102012102c20300001c02e4031801e140001c00114009028a02c21b0408001e070040104580f0700f0b6413403d80080c1d081001c042010014075030706005408200008410407802401d054132005a015528003c10 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 547987976 1250 547986726 547986757
    0x3090603181712060906030a0b0406090c06030501060f0201090809010e0111070902030609090622030512090303070210110a0c03050d090b060906010e0f01080709030c031211060408 79
    0x81c014014400400344140e0380030402c00c0850075110325218a0750015955200200c1850002428a041c414000d600400c0000c0040240b082a542d5503015400b0060044a103a40c580080b0000504810b050b200a0989501e001c103a540c1080c2c0014120422503920000310382c10a2002070100b00103d08403608a0020701e0214829800e0800694035808111560070051080401c00120700c0c02c00d1b40914001c40c4200e4858415403104001c007a41e40c40c00769484603154641411840300781484030075941c6404c1c4281005400c0c6607040c4404108000111000e50031508000100400300c1d9050109850240300444100007504a0301d804040070301441040030b0034041100341900c14540660182c880856403d9028001f0300341b545040f070304542c400d894003405001c850b00495015030041c0380e821104503015018a040081500046800f101d01405003002d00807001c42c0803010480b00200300c40a58051400d006075400031840c010038103d0f42c2259860340c0d0b0048010b020015800720102e070323070b10122030401 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 547989226 1250 547987976 547987991
    0x30b0105090a15051e03100f0e0307050c06071a1602010e0723062502030106061e271403060f070c080c100204081f0204061202030a0e06070504140a0303090603 70
    0x17900c032250303510700406605118800032880600615040600c020380c03c0c078000e00031019203002495a9001e1410002c046030800d2480d80400e0600030080c2490758014004100c8541c489507401403082000c0e01d01001c0d460400c2101c420a540901410308180d40744801020b440c0c1c6440752900042586420304510180e0405425515603900c50942e2240788120100c0040716440d0071002d0301480b034090049001c0d5007401400940240241007024034071700b0000200103124201c0c0c500301e40b58071201c100c1920820406210384440200e500e100b0340078000101c501e1b40791554410806142c04030041500c0c042c0c039400030801c44034035400501600c0c030503440041d090319400c0b03c0300414202081140604006031010078001005040001c000e51092080301d120740c0403140703040c090000d9100340d024450219a1010515a0510aa42c015607200041c24800941250300004482c02c288050b15603100250001c64240300394050700e2a44140e06e213007100d0301d0b0506451640c02038481402da03c5010180b50b0303036200 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 547990476 1250 547989226 547989259
    0x2100f0905011e0e0303070204060e161706040b040e010c020709150803040323061312030b1e0a0f0303031409010209090f04020d05070608070e011110020903030f04030b0105090a1505 80
    0xf47d4004c1036008100344405503c1e2252400d038050704607001035044104142d1740301d2603800703421200070740001002c00d441c4a503103030f4003448080d1514611071a0800c0e514410318026000a1090504c42e400740d40c050601c46140000c0042a160207400c40d83d0780c80c500c00780800c1aa20000f0407101180d40c0001c610003540780130001341092005400380701c4101c1c01564104107940c524142c2e480e4031103109544a420055441c0001c03011509848002034100540c1c8800c0380b00d00260400114507054000d000400c0795803942103041400303005034801c4000c42d07184c0c1035100c003040400d401d0030761241e4554001c608000060000500050002c2d00040c592442c900110342552201c400805091380c001c81100d03622a9600d00041550380c04480d03c4000a502c80f5030812150300c211602c0c1e02e000986001000e042c0b81c1e20403118000c1d07004441050f8980f104000c0f920080c99414054401140280c2e1a1200b41d071418081c000191b00041513240850302d0004010a80c83c00036561000380d410594005458595000 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 547991726 1250 547990476 547990483
    0x31104080a05030304031d090718091a18150904150903020c0a15091e08100b031207030c0b06060f070c15020303010b030117070302100f0905011e0e03 66
    0xc0090368580103145484003800000402140a188a55a41145007000380d40c00b804480c001e59049901c090a5804140b01e2803091400b8003100700a40400c0744030b00d0384e69174003800300d603c0600044526800c405c2a0b202d00c4c40d01da100f5640204105111040901e844414035481e152100000ca118a04210105090200c0d0b0f070381c01d9900101e04001040070304081e0401a40d14400c03180440d100d0754544802051075501c2d0042800e207036109884100c03800e410700c1111a540d0804401d0041491003107080000d000c5420449100505c0c11200300080e40c114420270f05041c80b51501c52807491a00030404200006d511000082c1055003280c207840d415101c20001550174410100d403076980020104003071092024141500e411182482d920540107403050101307903200d000900c600c0440240500c010410030103980384071008c5a030390000b5210256100d41c0010f05035180114a100006c4503008107000707440c0c201804102801c800d080a01400c1c10401c0c203602601c400e0b1707140b08104500c02c40242c0c8161400c0 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 547992976 1250 547991726 547991729
    0x307030b10050310170d030e010b030105010b03010806250f020a0506010b2503080708040c0803130303020f0a0c05011407020901080c21030405270103060614010e0d03031104 76
    0x501c00700d01c070031281ca070080107038100791120411000766401c001984184601080034040380e51005d4200c002c1c580b01c2c15030007464203046684440d520703840d041503a95030a10465001e0720450000d03d85a50600710b05510703041c4c00402c10540300b504003407a801c02c02030402114540402c1031400b00200007080400700d003045102c074030041c20f0b0300c202ca0011a9840400001c2c2110380d8000e8040d003841e610144164a14140b041400b9000c02d608402113600a48200d1070385074004d01403040c1c103900756580c204461031039009400da2415801d2112081c001c143d0f0500c001f9420705280c0b8020030b0b84201c1b584500146051a10490b0306126009c20140780068140050326400b039001420420720b50394480140d51645c014881051207500d18281c0c1c10280b900c2d02ca8100c40d1581c6c3c24000f1410701c0e0400341400b10440202142c0c80c1c4111902031001e0039011800d0b4014061441607001050203450141c00744070b10120241d00e603041c0b0107060900c4083c0e031111846980d0740b40d0986004107542030054060b03007062095 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 547994226 1250 547992976 547992979
    0xc5f210906070e010c1713030b15040c02010515130b04060b22120204050703021c0c0e0307050603040605060a03050708010606080f19090203031b011a04200307030b 72
    0x1110100160360801150440c0b09203015118001072400c200c00444410407218401800b080c800702020001d0a5460064a6a001034000d80780c4000e17100c2d100c5c000a90411100c2800951520f00d034404c50342420300602403130491600091040d410b125002d44c3c00c10362980030b2076004403001902000c00c038007940c01031180e001028008001d400c3d102c8045003502e500190f1281a07500300700d031100b9452101c00318880c044404ca43c0041442c42115802c00018101c0940200700309602845601907032201c420b00201101d0000400013020380340c981000d4041170003100030601c66000290104203c0e11110112540720341d000000041a80d0f607040041c00a400c150000751117886004801b042807201503200005a0b40d082d180c40480d96a000681c4d20300c00000c40c1d80c20702c2c2501c03c51440c040781c0d9090b00104201880282540d051010b42c0d048080806a03450f14001300369100c1d078580300c01c0120014403042000c401c0e1420f1002e1440d0391003011801e0316a1020301403101000001800952290f40840b0301c2000 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 547995476 1250 547994226 547994287
    0x7020405061f0c0204230403031820120d021509120313060b0f010f0f09050415180b01050316110109060219020c0906040c5f 55
    0x45960005107000100c0900305d00691405c481481041c1e000540c1d0208500d004e10000c51660316135404502510f0000c2140040c00640e002d9440000d0014070b031300e1300600c4409840c01d0319001c00d80410078440201d02e00000203810105241180503400b01c1d100414170107400d91400301c2c1c1c039004000d5103418039402800090034008000d01c0400101d0360440d078401402084240304105030b010400240008100351680498121118818020b00481d0700c0ca084d10200d0510070801c80d6100046801d8810603140283c5c0c41c1c0c05424284a03600240303c104117070a81c84c1104020181d00000060290b100103054920341880d5040000d410500c0745000c0c1c540340400710000d20110f4072030f113050300194100c0d0211008c04120003280d00c1e0f4991000034203e503007010040404c00a5228003051000411240d04444100300744407449400380413408500c51903145403490311079550004032650f81c04c1059482800060000d403000003040c030100c0341011100384100c0c4080140d8551003184130303140001b01c00f42002e030b2901 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 547996726 1250 547995476 547995529
    0x1103220e01080c0a081c0f0509130c02010c03090f060e071703030f010e13170706060f03020f15092214010501080105060c150705071a1e06060702040506 67
    0x8201090684003c60300307480c215600780d20307000250345609055402e03212564034460400e090710b01c100d020120701281414042d1910099502203803280100306001441b0640340c5034061081c80d42485849100c012302c0c60100840c2409a8400c4204402c00c03174050005500d8241081804034248503140090140014001403040d0702c3e0800b0780c80741c100304c41c403070303080c001040000440400d4290320700e00c10b1490081075107071031516a4a03041e070003c51404810050340d090141c040002e01a20074a400307007080e400c0d061001881c51040044400c0380c4c02c2458007070160b825449408c803d6840c01d441d000802211204d60304100c2030048040c0600d02544443d2007814a182d139030012950f1400079060751000e0740e0f4115181c0c0c0320420b0120328410702c02c0d080341daa40105d1101b01e0604000b0795454002d152440c015203000300a856070a80c455980c2c20f941d800701425028441e041541074001d0280f881c080741d1a4540f07141030000500a8042c0c0740c8080c4c01030361200c000841565030304e41c041030b410300705d040130502c2003 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 547997976 1250 547996726 547996739
    0x409240e0103120c05031204031103070302030c0712050a0303020a0302130b03060406150203180a0e0c04062a060f06090c02010e0c0301050f0402010f0504210201020d1103220e01 78
    0x200030b10050303850500d24001c41d200144902d804202d443d400c10300030b42c6042c100d0303000380f540700038000d00075410400804581c420a00040c001004528004e60095441d41d60b04585c0740d00748035041d441810440e840580c550001407000c2250002580c260034010380b542071000c0306901920402c900c00074452007020001c15484000c030301442c003034041a202008002d440d0211556411814189400076910034445414501c510503804900b40201030090703108540d8440e2120801842540c59485903400401e09100c410f40c040710028070341d2411719111103512944160302040301340070340300900311035220f80304102c03007541a800c11070040c43c0c28a41086080c2c02050300030b00a0a81900b00c1449002d101001040e61605000b041e01402c0100a00021134a43d9401587c1402ea40c520a00c140a0140400903050505c901007401c0c9007011501b92407044610701c002400c0034070b54440002400940070480d011080004182d40e0422070b25420140266000f28050010144544c04501035044040010658 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 547999226 1250 547997976 547997999
    0x70906090c020c01090308090d1e081b030901050d0c1e0f020c150a032003040f0c0b070c050609030304030b090102041703040608060603070c020418051002040605040924 74
    0x50007680c0c20750700d010390381c000111405505407201402d6060306000741503280c50500002d16003184540051048011610710074001848110310903140170300003041807840316520350010700304500520091464050750800103407460003442c801c2006c807550740340001c00003030003491890501c5404615903480e48408450040c001201210110014002c059070046a4140341800038440030b400400355007003100401c02140104401da20103801561049100800081c0c0040250300840c02885041b00d40807807810100c0c0740c4070083e0b10202544004020581c0440c040071803283c19220100e40f9650f8800403038000a10303500980d0005443c1c1c44501040c4012003070154010002c03203844490041c80481d1001c00551a03014511031600400c040c1d600080452a0217401982e102c40c80d401c1c088902001d03038011404a400d4058034020786010620300f4014010108144804203168507029461315061800041160050740300da900c21640303902c0e040a48000c40040a07840e00c80c18981103041c2c2d5695040c8840 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 548000476 1250 547999226 547999241
    0x20a0e0d050d0e0f06041403030403080c0609060c030603060a20040b04050f0a061e1407060b120d0e010c05010207050d081005030307020607030c1704080c04050a1a0105030907090609 80
    0xb180e0b01000f1000d60f41020b24081416004c0100642e0034a80b40903000d000300c00c1ca4100940d49804100b01c0880010000c9018000360142a0000c04892400b0484c03c1d00e0030340301070045412110113000b006055070300001da4a40c8090380d00310101e42982e18003061f84c06007403400e1040301145008500410100c480e0b0024008503035084506a40123a03104080c881e00c04142c3c05110300040702d41209015092090300c1c0c0200340c000da8a80085550740020103070401c0d0f007240201300c0c4c20a03100c0301403844034649041c8100d40c544100010300381d00d00c0314181c05000c4902d4490054144021a043c5005010013941511182e03a017040984120884940c00285150b01c101c6007200401d82805001c205828000103075010365501622852500800703071016074603d101d10104035103030b0500d0320340b003003030000145c0c05000100010380c010f00c40303070171014104070a0b00d03c0145461045490300d0f005a02100000308402c800d55020300b4510341d6034959010141c02c080c030907004071000ca814800000f0748020594000e04 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 548001726 1250 548000476 548000503
    0x2030a03110705120319020d0c0f0e09270610180204150e060903070308042306090d080c0105090d110d0c1103010b0301090b010f0501020a1203020a0e0d05 68
    0x1070004415100714140103281000e41683c1c00300e8004002c03840d0380c01c02503030404209078084000c00042e00c0e011042e40d200d1560f510401d500d4400348440b09403ca5007a1a000c265420000004401c8c2404a1085c1c0c10050045001d01040d0078201503202030002940c1c40c2c40c1d060425a401881e00310300141d8420814419210198040c0031038801d0407030244280e4040d5140c0b403620412903040c100044482c0c3c2d65500c43c0ca41e010804010380c801558041042d000203510070441d283d104e502d4a07a40065000034104041d42d0600d4942000d660303135540208507061340c1421202c50301c03d00d1013420b01004a0060050f003003125071800d03040c0079030190001a5100300c0b4060703541c1c03002c0140e9020162a2550710848144022950181d06280020041c00d0050f00c100d401400000340308003040002806d4404c4000140c41b0407001b140144032081c5440c00c0900509003c2c001400e0450041d0b480c09400b022201c1c810080641c003082c500700251003207200510f070410081401d444007845003003164503413400b5040c41 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 548002976 1250 548001726 548001731
    0x1e0c0312010503030705030409270b010501030507020c0d020603150604090e0c0a0501020606220606031a010806011d0a05150d0b04060b1204060e010203010609080706090f15020a02030d02030a03 85
    0x2003070f140001c11a200258010061414646840e03003402c080d103064104925a8105030000c1e61001c40e441d864503031014000e10911580d945044005801c480d000381860045401081001d075840e00c41003c05400300e07606448640d665a5000642401280d004e0012540030f06c0019000558002c00d41004401c426074005403100ca503c0c540401c48004498070945003d600010300091191402483c2c681e1741c2105607072428074901d624100801119159001080825600c1840e8403a19412112440354031801303083c002000e00742a00045c0110000081201c0c2d42e04180d40310349510340303482d0360b008014400644920b210b44074900389840f0582090401006e03191074090114034901d8a4003a440071902203d03843da24001c00e0201010450000500c00d1343d02d107480703031505003499800b440258020310640e510a4101c030705003e45c09081000342d901c40300801854882c2480080300382c66600c0c00b03c41040c400000b01010101e800d9060541c1c10002a40c9801600a15480d072034002c00141480780032503504 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 548004226 1250 548002976 548002979
    0xf020c010306030f03110a05060a0e0717190816030e0103050a0c090b070303090c1413020c0714010e03010c050921060403111606031a031902061e0c031201 68
    0x4404442d030310311019180300680c07135814010034001c001451040f1116000d83d1071120560300c420345004001ea4002c03125583ea045003100c1c9000500600303000c0c044554040700102112107031030755281001031903d014030180c02c02600c100658481160308604155241848001b032030b0030080d201809040515010034102400108551550720540c11070041603269400700c80e0402c0303a008101e400500086091654800300140030800034101003004180e25107640f50030509200502080e0518185051711030303401480403040700000850b581d800d55004904254501006d2001250645a8022102e0b015441c0c10050101c41d54014010907203844140e9840c0089203090342c445a07030450b81640e0000307070f0300b0000100700020320030413810080d0b83c40401201c2541001200b01902501103030701900100c0e82d1030318040d101c1300d00c1d29541c901c40403003103025091a00004140c3d940303800c3e11490091080c000040c1003aa14901200089089080071462540f104c01e4104040d60700d5000b000742c0728071410346a00 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 548005476 1250 548004226 548004229
    0x9050f220c0308090a09141513050109020d0b1008010b09060f0d050406061208040b070c0b120f0f0610140d0614040609060303210605090703050f06030d050a1119030f020c 75
    0x7c031012044200c1c1a4a141e40c0c0b1941d840b050381405201140d40306030300407c1601e071250a405014080c1002440c01a55000051b0510381218070401865000b0b10005000710031040c0c000e46014119401161401e90f20122900010035a03c15800500104680401c0920f28001154071141c4110b104a01c100409078440da8200842c0c1240304005080400400080c840051100d02410080d84105102030b030091b01c074240c0140c50381010b88034038551240f503010004400030740710295800c00d074841ca0307156042c1010b01c003040384000180074000034008825500e280c0d020300c0300110b480340207100c00100580354071800350f0b000717100d1130312007d520882c03d010340865100d81e0b82c8158030880f60b041e180c1d0030f4521104400c156960041c079035148020750f615400080c40791103421351144200155034000803d0314281c0e002000c148006801a80030394030881482403010707000006c6580c1d001c0c1c1030501108622085041c0da141c015005890114903201921780010140c00031300e5a42c805003507800352030f5011501c00 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 548006726 1250 548005476 548005481
    0x180c060305181b01031a0402040329130318030203010c020f010f02040e220209100905130b0a020c01060b0403030c23030412050a0c0e01080709050f220c0308090a09 72
    0x3800f180c0f5091046640c1c03281507000f54000c030000c10308a940100000c803244001400c0341c205501c16200d030038400060907441100203010100640c0c610980800c2410142102c040c01042424024144880d035401d114a5401c145201c40040d68010000c1c4600c0140910080d1a00d9101c1c03d0f0801c2036091201ca04100c0d9903d000350b806444c0e030500c00e10007564503490035424100814004600486400e8190000760325810712485c403d41451030a09116880c103012803044401c0204a243d500034120b40090008407803030001c40c1c00c8404020050b8a41c1101d10001d030040c4260743c44440d12000c00903001013056001142080b0540c014010401e040c07000c0d4500c1aa08101c1201e1025242c000304001e0082c544071402c1d0304034043c0901c1c2140c035116101d43c0d032090003074681e820050002410b000100300400c410080704000c7c040415017401541816031a071400340714013030311100700c500803036607041d0301c1c80441186900042d400c01c000000940d030b06d00b00b10383d40e03034044005103000302c68103640403d04800c00d0 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 548007976 1250 548006726 548006743
    0x120209030d0c0213020a020703021c0f0b0c090d0f02010206280914030d0b100201271e0f02031501081b0f0d0309050906120a06180c06030518 62
    0x540580264a001c95084460000101040740d010752071218803c884c03c40c910242071030000382e4008104250a5004000d80c0801d0000c001c24600b840f18822800607101030b595464860b48801c10441944881e101408a030051174080f540019454032000c052003203850307040030458000c1c0c00b40c0c6c0f600e80b82c11625101c03880002c5c0741c150359080c0c034085070001080140e000e02c17102c5010310381c03914405441c580703003900f1030b4002000030380700725213880c1420003900c1e26aa03a00520042030008101c0520000d990340405032000b0052802c007503095030a00f007405404000e400b040f00d16030800c07207400340a52911070310240851030240d0007880342206400c0c2074140503440c58160740185000b040e4030514000d1a4040c60041c201507500164000000c54040d1601c441c0110401c1c4262950594241000188150180c004241501c940a02c081d503103100e42c400325a45c00042e0b0000710116500001c4105042c0760f0054400040451b141c5080000709240d041c0c0c480d0703000f814400c0c890f150401281c002665541d114 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 548009226 1250 548007976 548007979
    0xa0807030818040606050a0212132c010e09120711040b011103040801020a031104050a060f0c021c03020d0215071d0a030605010509010f060203030402151902010c120209 74
    0x265200340040354111024010929060703500e8601c8018082c041026940f5035400000824000307d0b0300751191f42c0500c010510038429035021424052580c400000c1036030302c5e228070f040240d500c1510001000c08200e043c600601d00303925041d0256918400221031410817500540c10f8010f044c5a05421a011804c40d110f2640012101d0394815054042200a1030030302205814000810300f080d510f03480c140003400c010034000e400103840e90360b2800050203990180c1d04c12000c440c1c041006008950710803c2c2001581d0841c6032888a01d42d403083d050701d242441e030101a40c807415056a19850a540b6001c1c014014469802e584841e90b82050036179440034140e5104071076411920015032031900c2801c080c40d800840706d002250300d016003404120791101e142c1080d0307486c649441c01030016082010315a401801c2c8680031340c410740c0c07800c1e60080d2280400f801c000e10590309040c0e2095411100b00c1520300d03020902c029801c4200780303160041d00070030b050140c410104400a810802c01c0d851032003514003e040 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 548010476 1250 548009226 548009233
    0x200a0b030702210a0903080c0a0210021605030705060d020304141c030609020a080c092407030809030f071e021002070501020d05070c0b0307020109080d05040213050702030a0c020105091c110a08 85
    0xc50f601c00145811115000c123651040f6480d00d40940d94059050007910015009400d03050035042460300000643c1d001680642d00c80101001183c4814044540b801220000180c1300c1e05c0c0c40c40d08145240200300002101c0c85a15292030f4011203030400e01801700082d41b002c000460369011680c099000320072052020421440020304820810b030014051000014861501284001501c2c2401520081d269a0415022829404254100180c00d40105c0303c40010340c01d200341c0d00c040c160640f081c0400100302c0803409038030300041d07100200314809540d401861080d038400301d0340009541c0c80003442090300501c503a0f034014082034000c20031200003d0700a00703021809400c107100004aa400a4040d000f1503503283c0381500171030700200181c80300a000c50341c00f00361810180108000703400703071200f010381c441c3c6000140020705400100f00e40003080c0c02c0c18a02504240c0b0300040e681805001286900407580c0034100c41c181000d010401440c0d032003134100c000e400445805110340910303903010340b0b4042d07030 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 548011726 1250 548010476 548010479
    0x50309010f08071e11070902070b01211104060b0c100507080105030c0d111c05060606130e090c06040f05041b091a07020604140418200a0b030702210a09 67
    0x40182401075000c44217030902455192000b01031074589102548001103060340420003d00700b000e040d850a0041900070607450141c011b0040403048103072504001081c042168114800588480d0007200003445804940e6072624082e078403582e01c07203001081da80c0980e481d05001405150040d05190b0503507002400078020403040c0c000380f14000324004000c0d11041d59841c2c090701e044d60b0b100d040304400e124600100c4d1558009141c02440e00d5070103009144292420300450b0b10b040003070380c0355200712850741040203600e444104c1e589091400c98640d01e41c0000b0005404160300805200c140c0c201c42d010b603010007086100c1c1550003c00302c2da0450f10400680707030600401c40310596416040002040c144d88a14001c02640024501c1d030095005100201c0c10400b0121280b52611940e01140860461844150265503a04692054820303480d08656021101802c90f1303203d48101d0000f5040440d0f00c240e590614274400795449007004112800a035009540100481411099600c4202e192300e4440919 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 548012976 1250 548011726 548011757
    0x11209030203040504020717040602070305060a09150b060d0510050109060e09010b09120a12030605010302030415050a0b12061b0c0c091308070f060b03010b0108130816050309010f0807 81
    0x9600c1140240c420b94080850f00c1c0b458030b440c2c23000300020405900140f11b40c600c2c0d480c0080c205080140344c03454203841c01c481600800e40703444101d0f0101c41038a0001605641510003d5424003407840d817112900d1074002007202e03003690340c44408280e0b14241ca81c129180d03031300e1204550f5072a01400c140c0d00305010030010008124542e01400111400910709030103000b002c0c403540c0c40d01d6144001680d00341e50240807480102e8040c07080a02403d820f1a0941c0341d071415803507000c40d41482000d14500c00c2e1743c41c80020940417456204261a080c01066000145a00850150359080980f205245909125600c01505824004680c00101280e01901035480d000c001c110030380c01e00405059818010030101400503040e40020045148200200ca01800301401d04204841c55080c203180668509a000c80c41c583c1c009401543c0000701c64100d00c0031950902d4006624010407054259080408100c0f40401c40040003800c0c0700c41003aa01d807075510091700000c03111a80203481d0000490411010318100 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 548014226 1250 548012976 548012981
    0x102030f0a02070e0702010c030b010504050f2412040605130f0618021206070e010306060212030612060103080a030e0105060a060503040f0b09031e120c0d060905010603020702011209030203040504 86
    0x1070406005640825541d00c0400c8010a000c440c0140180d40d03c00301517805981610510183d4402031801c03509081c1072131b0204645000c1540c00c60310641c05401c41c64032090f07480c40c1d000f03400701d1060003803a124083e150050b00d04480948049602a0030000068103608441d90300001d010b4016190a0001805454120003000d000465a110700152580c01d400b41c0c031640361015100c0b050000408042c941200028100f01c400800e890425041120411015500041000740c41d00f44008682e0b0340d80325079000a02e04002040c03c0b04050150b407000009001030a8081d004210702a10103100c001004480c150807580c00b101c0c00c541c0b2074242002840954411009103912512410790062019a55100c01c0c01c50306085901151903071002807200f1414134a0f2011400c034580744c000c054181142184130380e041943c001c20010381c9010125090040e1602030304018000d10003160704001b6940c440320001c000c1c3d440198243e001c1424161084901d4800d44507000260390142e014505040c200f07400c0102 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 548015476 1250 548014226 548014237
    0x304030e0603131e0305180a031b0305160803070320060f060a0b0c0705040c0512040f060b180408130e090a05061b030703022113020411090102030f 65
    0x3004890240c6514a8540d10002c41c051001c4006030801c000c190f01d000d0203400381c4044c00c04038040c8808041000240c000055440540300c0c400c3c9000c0380384189000c04c1c28605268002b134445d00c403039140e20700d40941032036260007920301071400d1ba80608840c071140700702c4030007a104000c2e00b1b45c420041880403910868070040e054040110ae0796100b6240c0c40c03d24030344541510340340080d60350700c02400050b28240e507074980280342c0101103500740f8a03d007141646540007403191502980d12070380c0900001c1d10541c01c468019001200340310b058241820a41c1c00741c034054408450851901030000000e03d00448484910707400000120b06954450340c0f243c0b6207810244001d03111300b0342c6e80c40104251001e01511881507032094000d10055640d404c22074035041d0050a182150650f05c021003d00f003121030101c9901415900700941d0700c091004d541907000d08800f80c142c00300c0702018107111002e079400c09041101402200d0030300c03003d03800e107110314031038419003042d00d000da4010080040c00540300b401602 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 548016726 1250 548015476 548015483
    0x20a0807060c05040b0d0b0a060201090b1302010c02030f0114060a051c0c0503240a0506010903030c0f06050a090c080303061c0f08031f120b01090e071e090e03070807080304 76
    0xa00309566624500029080086c510740d4860301d40080c026242001072441000340414402441300201989070007a00c450098042091866212000310640e401000b40d004000e03030140450310f601401c01e00d180e00920036400342614080a03600894004d141c000360714802c3e00c800402c0300354680d840c4691900307400c140c10001c4441d48604080081c07144d60600400d400c40340b00b000b00c0d00321800c0002219040c0c10004001c10101c0c0d00c1e181c20301901d40d81c000705c048283c9a0500717000f42c403403140e82041c00c0840303d8170b47c0c0203007030b02e040c1800c11402c01500d030001d6800b18070814031a2282519452000d880f400121401c1e80c010007001e02d550342500404034040030160094001500d84805034580c1a21507201712814100d90071244d080c842016854000d401c020954408296800c1e045d9666030f0309094030600c42c0c1c07507106484103c80300f4094130a00c18000100403100703071801e4034107101503a0189507105228450004d4a800c4040d0942e500200c220b980c02a44030100d00e00d00744480e03030340901d29000900243c = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 548017976 1250 548016726 548016737
    0xf0309091a0105122a0403020f0a0b071203020c030721020601060219080d09060c1101110f0a021c02070f08060c0405060c0f0a03050301030b07020f1005061504030c15020a0807060c 79
    0x1034004c0031071082c1400b4600b501c00480c9581c6c1e4110f0040c0403241030f40300d1440380602086582000054183e0083e2219075602540200005120303441c110068040c100503034900703010016030101080480c803505090000388441841e00c2d01d08643c0141e0b15100300340700d15000b5801100b9000c2e0301e45c00d500d46c488811441400b5850905040300d2800040310200b00080341e00580c1c4041c4402d880e6048038141c604181210005d1000001c250031040c05801420100c216000000c80c42d450b11500a108030000454009201e42c58a9a030000080da111614440c1e44041c0031034103408540c042c1d0204440d84100314400a5034a01031401c1d003072000942c4058244c80701409588180141540c050115441c0346000e40d0350b19841c0c0d41103060071146028064648425580704400050707505030301180544401c517414000148558803440483c03038041c03102c1d45400c140c0100280120070003034070300218015104080d030082400f10390035800707a0b560f191942025161403428810700e00021407031b8000303100800e010f2920 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 548019226 1250 548017976 548018011
    0x8010e100c140f0c12190507022d090702030a02071404021207020604030f050909040b0a0b03100e060912040902030c09060d0902030f0102160f0f0f0309091a010512 72
    0x316141c1c014400354030b00d040f80003408030165101001904414002c00c000e042c6419100c04510640b01d1010030f4900912101040c0b0f40300b52340e501030500103000790101012800710b04c0440003820031103041e008076100318a02404252094400000d0740c1071030200d030b00184542400d1a20003401c8141d0704c082c0aa00540030072140d5041041c1d400c5a070b000b4100c0c1c5e00180010704041c5000b4040c0300b070f01242c1c170301004400d01210202c2d5907a900410381194005061841540f2144070b110081d0098566039a054882c103001200180002d40c001041191801e0580e00301e511000c404503166540514641c404c0c0100b4001480705035400d0f40111b40112a040e0101c2c41c1851410100300c13181c1040c82d02c034020555442040007541828840e150811800000862404241c5140d080c1180402e10000e01001960f540800030001d0b038460805d41ca035040280d8030704c082c00e54603008144031158064000d90038102070400c4010000400e00980c4620140c69580c140790340321104a0341c1e084001c140d02242c0000000 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 548020476 1250 548019226 548019257
    0x5120c0a060804110d0c051002070b0a05040611070803120a02070f03210605060a03090609061401051905090c2506020a0e012604170c0109020a08010e100c 68
    0x1400c03801801c041e02d071031440e4500303400d00d0000084008000c4e40101e2110041c41d0004c0c00c50a0120161602128a8810742149240c00c070f180001d00e4100c0c20403410005030b0103001942240141c800c66140e50368240400500002c07094a400d054861030761a54402d00c2a04403035071107605090f07804a4030400050900c074094507560701640c038500d41036004c80c0c0811983c2c51110741d003840c101c2e62035000090510141d441e00d00414040e02c10b012402040540d03900341401000915008510503d030001401d0100e00c01040a5405800c028450315100b0a0211071000b03140b5455510344c422141c004000d2090b0f40c1e81c10240c0441507001c058015400d4803081964103440c1c1001c03040c0030189006201c01a1118143d00c0301424040d408007015042c010303a242c420540d104000c440c0d031420010310a20307400580715460100f01a6070801d00f00c507134199002c1003904a40c041540503801c5507000311480c4000a50f104202c9088482441d15820700d500a0801c40d080d04420760000c0308206954900050101d08650 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 548021582 1106 548020476 548020489
    0x60f0906030708060a06060207050312041a0d050a0e0f210f13120215070f0b04080f0a17071403040605130f06020306030d03110405120c 60
    0x66001e031400d214100051081e4000c4819608007854240e010f07004500610b4010b205103e00000c240c6000524001260f00c1c0d2034100703107454140744a03800001001020b1042c102810040100521200e2244601c500f01c0780d10001440a81c540603141482c42e00070b00d20392140c0c0720000c811200d103421448142c0c40c8824042c49c690b1600041502c0060b4000e02540420210a007440020040e1001c12880e000d45c0c800c8a445514084015041c0f1050250402c080c10000c20002400c0014640000b4650440d014250003400e111144581c10707410b90052703581000042c28554000c0a02c06d900d9a41d9802c03503101d04107500d00c807280782c8807a071032400014405442551144049a80f01c0881710b100440c503600540c2d5540c0c00030f07040c20080e012354010b03221140240b1840300000743c000e12901c10b9080002d05655040d00d0142750a042002d141c00c8514048254020841c00340702568542 = true := by decide +kernel

theorem cover : BRFrame.Cov 547841726 548021582 := by
  have h0 := BRFrame.cov_init 547841726
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547841726 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547841726 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547841726 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547841726 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547841726 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547841726 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547841726 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547841726 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547841726 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547841726 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547841726 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547841726 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547841726 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547841726 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547841726 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547841726 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547841726 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547841726 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547841726 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547841726 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547841726 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547841726 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547841726 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547841726 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547841726 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547841726 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547841726 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547841726 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547841726 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547841726 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547841726 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547841726 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547841726 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547841726 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547841726 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547841726 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547841726 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547841726 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547841726 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547841726 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547841726 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547841726 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547841726 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547841726 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547841726 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547841726 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547841726 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547841726 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547841726 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547841726 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547841726 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547841726 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547841726 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547841726 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547841726 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547841726 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547841726 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547841726 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547841726 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547841726 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547841726 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547841726 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547841726 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547841726 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547841726 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547841726 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547841726 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547841726 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547841726 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547841726 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547841726 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547841726 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547841726 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547841726 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547841726 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547841726 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547841726 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547841726 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547841726 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547841726 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547841726 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547841726 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547841726 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547841726 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547841726 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547841726 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547841726 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547841726 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547841726 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547841726 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547841726 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547841726 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547841726 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547841726 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547841726 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547841726 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547841726 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547841726 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547841726 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547841726 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547841726 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547841726 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547841726 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547841726 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547841726 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547841726 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547841726 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547841726 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547841726 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547841726 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547841726 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547841726 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547841726 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547841726 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547841726 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547841726 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547841726 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547841726 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547841726 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547841726 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547841726 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547841726 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547841726 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547841726 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547841726 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547841726 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547841726 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547841726 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547841726 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547841726 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547841726 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547841726 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547841726 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547841726 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547841726 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547841726 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547841726 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547841726 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547841726 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547841726 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547841726 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547841726 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547841726 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547841726 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 547841726 ≤ n) (h2 : n < 548021582) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
