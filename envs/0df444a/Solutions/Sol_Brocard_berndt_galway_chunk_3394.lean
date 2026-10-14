-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3394
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:32:27.32291+00:00
-- url     : https://prove2.me/submissions/d7d42012-b909-4214-89c1-694cbad86cba

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 610251798 ≤ n < 610431654 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 610253048 1250 610251798 610251821
    0x26040906081c020d0e15070203010f0506030d020a1101030225061b0e0a090203092404020a1d0601030c0e030703140d0504030210030b0a05040603061d0c030d21020a12 73
    0xd200714540c8080c000d10454129100502c03c41b0170390140310019403031000716459a82c0c00b6000340010b0058681c480020142100d56078000c0c0140324040094030700c040f6502c1841030b441000c0c480b1407050b47c001100203400c2002194a030a00c0c1143c0102200c130b82600010311a88a0340c008200c26202001c181c2808011920400900411002070040c580d0b5420031001607444500c030040c0c0725030307403412100d1420440104c00711514134030380010310901114104030b41c803481c001d8948444081c0d0380c031482c40803e48000c24840844000f10080740b0a58070941012074070010f641f5000390340d4000d550009007810303825482100c842d103084e020300e03a01c90b030144400e0f04100303a24101681014907540100751807809a00f84d200425613144400300c2155a551070945c084e03d03001e0001c004843d00d910f0290020085103504845003103440c1c00e202080c8800042210030348001402030001401103040940d0100d1008100140880482d04400000040c0788043c18800e0040d80c0e81c5020864140d042008888864495 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 610254298 1250 610253048 610253053
    0xd0203071d0f2704150501051005041e0806070e04110f030c0c0102070f0303050613050907050d140102131e030506160e1f0e0301020726040906081c02 66
    0x14540355981d44252520400c2090343c110811007541d09180031030005900c0b0800b01d000c290402d000a2184e4000c0c868064414040100002e0b40c03503404105645440c402904000340040100f4014040003c1170f460440005038030200345591100c00981c28a0f40813a00c8500250400c50740c1c03410341c50705010f410700c500e8548003451301d410050410240180300041508155050014088102d48000d5041322030450700828280b400d4001c0b468001c000e4203007a248140f00380c194084030302e0341e0540384c8a03c074050201c4900600200307242106110002140081c2a941d00e484440c1680301140280001c12203601d40d003802d02035590030a0b070010104c00a00c1d2690441c0e20040b0b0003800066030004c1e03415002400e00303d66107602000d000c0100c4200c0d00f02c050a51b013003907100001003500d2101480d05041041103485244201500c4410f141c200e02500340051b008424050030040012503940311444042c000e200303040d281a0302e070380e00001641d0181e40310b0981a8403455588082c07040c078100c0c100b041c00040c0702 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 610255548 1250 610254298 610254347
    0x203070c060e040c0905090c07020d12020303150f0d15022101050109060807090e040f02060a08010906170a02040c030e2b0318020f03070f12060b06040b04031b0306020d020307 77
    0x800e880307c1c001003402e10702480015400c001d5644266140e10f010760702c503094006070401ea500094030383d042900d4000000c80f02000300d100320f2404c041e400748a0f140141c0420310070000d03a128081c01c445001c890000c1140c0c01c00c210b01a04440d090004440c804208000c004d42d4500000104080c40366840202002011010300c01d90950050701c40040301c044c118503004a40b6503040c0403546001c1200d009501c070308001380700c02d801d68101c41c041d41240c41e01e0808000340352781c1e60900000821850105051500b18410650051405920400c150345051400040562000f5981c40ca031040e1881101e0840340308a8151800f209504020a1041600d143c00d001e003442c8101e55aa0351216003a000740301d0848440040f803a5201049104000c00c96800c4403004995113083c21066010b00d060140e400b182131614812882c00d1800445003102e01c0c40c000c2c02d117400c0c50f41d25040c000242c00e102600d80310b2000307d000004601980080d140c1c04c02c41400c01650380c02c1062004d0603a81038800c480281c03016800 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 610256798 1250 610255548 610255559
    0x1f12230c070b0a0e01020d020c0a0b0105062a0a0204060605031b070803180c0a1401021911060f0c06040602180405060102190303150303080118020405030604120203070c060e040c09 79
    0x1402c0d29045070030b40c00d003c01c01d2513540c1c0e10390380640103106000c0c0040e84041190450701000140400384a40101e20300851a62503000f4081c0038410048000100c01545109d4004510441c041c1e003544c44040050300d01c58103940d40040c082d25026403180c00003034400b0042c014103c0034035856400b40031311490ba552620480d0303942c40215001c020320740c85e4a02c550f503010100c1e250040c8800e8a01c200001c101004068948100110788500c04800500511410b01c14120719100b645c0c50802c6079402040f902c141011400070443c031617000702801c0001c200700344540c1714000d004006e194002c80c459180580c8520441c1020380c244410070340000d10450400c410300500780d0b0007081103c0154031503000f4185a4401d400d0546c040c00c28a03520284121030240000181075202e01901d0607119a0130541090f2042c80c50300f40160b0180c5d00030154160001d002140004004070402d041c03032000c50042da81011644d480d02c05070503030a43e01170030119200300404c501c0d6103498490600a40c06500b01383c4006403e28 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 610258048 1250 610256798 610256813
    0x1202010e100225090b060306030703022e03020a081509010303030213050303070f03030e060702060c090114030a05010609080a05070b0f0405060f0a021b1f12230c07 72
    0x806409000c0d5807034501a500d2540b0a02820028400c64020103464450035444150301000310f01c030740302007189407a1503150300d403070b00c81c040701d0082000a000b824001d0840e000c03c0400124200101e2490a02c0b454035101c10704014184c0b0105d400c00c1e100141c9401c00441c0140040800610116868000d900340c50300d507685440189041d80e40600c0d00507143d00300e603070b88001c41048503040158548800b04241003000760407150305246030700c40c0d541070104081e5800e10a5941070240e94980c0540c00c03c80008113140f0343d0102606640c081450108460440b003c40c80c1d1581c0e2003039035030b101565109c0300140700e441c3d00414000c0040141000034120980161661030300c61542d401414011280065a421414441d0341928080e1100030001640c0d01e00001b00e410b5644e109690140150107501d05080034810303640c0000801d84406070141016501114115403440c8025213a941884100300701007180075564802c40e04001036108018200d0440d0504070705590000901040c818903080101c2800074460 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 610259298 1250 610258048 610258067
    0x71701050f0d0311011e020c12031e0604090204020d09020f011d130b060a2c0108010b03040c03050d020f01110f2a0a06021902070803091e0315010303020601120201 72
    0x15140ca03a4454210f13441e0300703024200d03043e182c8030fa103280d101e00f42116007101e80c010b203012014174003110b00400700345044040749e000803130786501d50260035100d030b485005114241c4c81d80803400500001d0400c0d00c0c0d0380010100c0e004803210341310786d031350751007411046040c05249945044424246183c1d030400032601702050400305102c15001d403038882e8010050801030b0b0440e01c0c4540c0d00800035910740b10ba204000300402c071001c0840c240c80384194090584004402c0e641140c104069440509680c20b000e10242541d001030800c549a40d0512000030104e0400e10040e11044181d5002e8606441103030002800c2d222000714440c06000200500c003100d52014040702e20010040440303181942c4d0f0b4000600c1c583e541098101d1080c000d06103407000b000010f40c01881c1101401c04003044594074075104030794a00d101d006514540c0c0c410412a4101c1c0381a04074160b0761040c00c50b40402c40c0c43d240000c0381c10094500d4508145401b0040180101901800300d1030141900184101500d111900020242001c = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 610260548 1250 610259298 610259303
    0x70501061d0f070216270501090c090909030509040203070e2d0301050907051203130605040312020f0c150702180402010305181c0306210c06140409020f070506071701050f0d 76
    0x2154070380b42c0b442c49640402c2941085030b0003010080fa40e5607120780c46c068022b0400c82400a014940302056000701071055890854066403a541070810b2101070200951000d0080000c0c424110458280c0d80d40e80c01c00d200c400c1004800c03001c0031010700103c600702590200703986031007a4140410020036440000360441203c404450b95044086a10b00301d5003940700e4248148058101c03403201084050300b01d4001c4c8116480390f842241e2031441d9200072602d6400f500012259600002c5904d06140340456100200d0943c80c0c0001d4135001c0c61340d000504d108078100c0103e241d81010f20401c810366800d84501a0720a4007030070b81020310013001c03415907211809108083d5410b0840c0803a41492817017988094013402c0c00718240703400901480000340c034509100d0f0003180c003917030404404121644220310307503000c20113100b0141b0300b080d0410024601940100d0008400319405000d1203010880030010383c2d01945242e00d500d101403400c84400c081418058200d9070080e4414040031030242c89034140d04400c2c0340c = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 610261798 1250 610260548 610260569
    0xe0c0f12031602010c02101119150e0c06070c090b06030103050d141b0a061a10050903031218010b0114070b100f0914010e0403090605070501061d0f070216 68
    0x2c1e00c0180c031101c03210400a034000d00881c011250b40703504003ca242d025800f010403101c0c0d60381c0fa21100c149600b074120307000b001c05c400070100c030340110710b550040c052020f078004c251242100400041000d9820600c02620900100c6400300040c600500c22101c07007a0040c0d461501d10760654807895641c01410a9902c10002030b400e014500e000320301c0030703a00340404c8035910915003100c0450080c0e4234031710550250b8031549030100350407000c05441d100c2d890320030000d0400e00c103034440c2d040142c0e40d0390041078260390140030400100d6880e210b899407641c411640710864160098500e010a421a12800c00d40c9042c4691401c4580301c21000034151241c503030b80a072120507256a0340c080641c03000b002e030f80320f040100341c10300f00411225465001041c40741a507510000d4641c2e03072002c12500c040c05c2510041c0c08149444003d002d480c1c4214001c056240c01880085201070781c612280105131600c0c8412107444208006100c2558002c40d8030981200c4c15100400390608880ea60440f0341d8002d100700350305030 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 610263048 1250 610261798 610261837
    0x2180d080304021009080304090e0114040c180e07081c020d09030f1a0a0219140904021e0a0302040f290c210408060c1227010e0c0f1203 60
    0x600c038600c00000703095081b040e00d46455842445401620b8030512804155082c800c04000c2c20252005403403240342c0ac02c03c0190100c1c90000104280c5550b481d5200d10745840c2c0306032018060302081802c0c01031005500500d80b41040d4940f03400040c159a662a0843d0050032040303269680c408a024145d0b5000024650b159440d0719186803111111400b09a10194030360402c82c40300d10700e6000d0005416802064003412421400407070700000300644030b070308440062080c80e00070f00f05540a4480c0045c408289480c040039103500143c2d41c2c1203007500b00001380d0006000d21401008120001c014207070800151410440000d400d131500ca940700340b800c1502000301d695005184200b0511342045120000c200981400292401c10340d40b140c000d1130090702c00c5101081c00d00c42a0022207244400b20900805291541c040c404030041c411042800d06512031010401009801e100340b038480348241c0010407031480c60f54140000f0100800c44140b1460074000c1d1020700e1480802111940c03003040c0c4420131003 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 610264298 1250 610263048 610263079
    0xe010804150c0306090509060105190e040b0a0e0a1407090506090a0e010f0c030203010f0501050301031e0c051c0317010803040e0604020d050115120b06070b060d06020a020102180d08030402 83
    0x40429600024125040c4801d00410b00800708108e4160f0343c00740c500070741901000c060424a440e4902c6111070020003030002070b0126010780003180d041200510082541e401c0c0e14290303032030304d4803050054a528100080984001d070040040b1802000300f880d00340000d1901400048035020014040c2c1099900d6800c4000700303a5080d4010903001504101c01c0220f030a9903c0d0042c001c0d00700f40541c08500302a06030116140d0b014000356412264410030420310500f000c0c14090320010030001c210340c400070791100400ca039910234003881d1640781034140e102100d000504004000000e403000644120440c0c100500c0b5810021045800395142c0317108010b82600e603a00810024880e400d14080b15034540000482e010a049010901c6515241d56600c283c1b504603540004550580610660002c801c0042c000084c5500900c03590105000b0f01c1140c03000b01ca602c0e44002d99100c03801420050758009004140000c0c0c001e4602002e80d0250380d40601191560381d004850301c0081d201900c05e00c0c0000c00e0303005 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 610265548 1250 610264298 610264301
    0x1e060103140a0903031401050922020405070c0b150f1509060d060302100203090f0d060b090a020a090f082d0318090a0b03060114040213150e010804150c03 68
    0x3980344040d9035001042c681002c100006014021080300000e08003298040000c1c07a15084070b050703440c01401e5541c96240d504031410f00d0389044045080c084004a502ca000d603607948201c0380709040710345440803041030701c0c500301e65042d00c001d0803000c81140c180e44a400549070b41c1914100c0d01426a2042c003c010b500800100c180201c8040c41d900203030014400720b5115460300540122031080d1510f99115006038816070b144d01a1a1041e82c104200d000d0312901031900ba2075480c200341c040c843c0001c8000c600c1c0003003100c80c00c0c01c646a4a019400181d00d240c1c4580c040017210090290f42540031010b81400e004544403201200c1c0c203400c441c08070350340c50f4142c0d8081740f0600c22040d0790300840340e48505103544221018480500c8500c00c5080e08002113070b1954034000d1280c100b0009001e403481d07a00704081c0c400511881d120040d0819424401051018004075104001e03011a40036441c0504183c040105110241020907041003d0a02840700007041512012805c05040202180305800c0030400c40 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 610266798 1250 610265548 610265561
    0x14010201060e04050c091e041205070b13050c0d0503090405061507320307240e0c030d0513150c060c121104050f15040504090c0e0a051e060103 63
    0xc00442e0300e2800c2c4003c204000a15464001050702c203220a035507090001c02d440c40040c100c0c0300002c03440c032002500142e640d003407408907810b09080c0300f400c0a4903500c5118110702c0440721000c1080382c1c18006018444208000d106210048509103c502c01d25610350740c0324005c240f00b85000391385131000b19800c0c0c0c0e50000801c0c0840c1d00c204c02d05482e44024100310060220104000005040c610b0031500322144d00d0750400d541d038080d0301c010352500d110b559402d0190a4200c28141103012103c100c4480d03045180a0955580301200061041400541c1010f09054464040d0014003104205840b1f0301d00300080b00008072448001c890000000b6490300b615810a86900141014034104180da1596000304039074205441900c3c00700030700c507081b0340075900b140b0481c0121903015440b1419401d4030b1400000d030320407554040f02c0883c241541d601c0400d080d40c020b01c0b0200d6840011100503c8800c840b48040c5a102940e4141400b10741018501100d542002000b80001030b812a000203615034001e805c0b82 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 610268048 1250 610266798 610266809
    0x80c1201020f25060915050a0504020a120302010e1f05010e0f0402240706020307020c0d0b18010609020d0621080306010c020f09040501050702100501032d0b01030302072d1401020106 80
    0x174032038000c4c0d500d40003004030900500300e402030f450f2030041603d101d4284a02c0d0312699015140324042400e00c00820017809031000c3c2242159202c1219080c4001c051102a0035003940700c85c5007038400c03032481c1710005441c4140c011b165280d504004118005d00c0420501d60040d405450b09500300717400744240c0c40e010080c5501c119118a000550b41c0801c01036500440c0b10b426a0750030b80e040c00400c042040300c0c02c841070308054464007400000c900d9000c40401c283c0e018503800307000054005c0d640c1d0104000c0c0d81044407901070701c0340d485004010b1150640b2007000340036120541849401c000e6034074a82e0300d001c0582a28100002e0000400854944000226100740000c00070000380c0781034602140607103400c84540006003c3c6030012070440c2154012035040e04d030300caa007000124032031200d0300380001e005004000750031017078426200108031000c215038041d6010754043c04229003041275900d10303208400480c04500ba40c4000301c40f1500032404141096540b41c00c0026585085480100d0140c002034014 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 610269298 1250 610268048 610268051
    0x90b1f020a08070f0606240e21071401020f0a030e1810170a0302151314030c06070528120f0f1103070f0e0102070f080c1201020f2506 59
    0xa60611808081040013544210014012952180303125820852640840103502c2d5500e0740038031003140201040008088040c1030040ca5040b0910a031108204000012106070000c00d0240b00f4101d04031400040c4010a00040040c210707110101a5208503022019080000d803149010443e82c461060b02a80070f0342c908154031505044005c040c0b0004248500c10605001c03000b2980d0709180410f032580c0c02c0b07815070050f11550645a0800c00003503002062000182ca00c404603000080d4000e0540482d10540c40c000c540f1050a052414a48040901904180607083c030020510454201880d171182030004c100045140112400b6a82d07004c10a804802aa0600c0300917480840503a000c00a103058006060010072a03242c4288942c1c4001c0c0e650000250045003000c06242c0a0106402c001c00e040c4100c440b0a50342d0b90040000d040641c0180312140c02c00d004041e854075102e1132031041c01c2e8030403000714904030000d5500c0e219807084405d422040b074131070405e08020244981707103113030703400d402800 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 610270548 1250 610269298 610269307
    0x825090308130e09100e0c180a0f020a020a14060112060b12100e071e060c080c0a140d080f1302030a08070b06010801090c1b06020c01110c07090b1f020a08 68
    0x40580300c51200503011100e6180600e002c0c24100e00040c01c0400c142c010305500c0040c070f0038110141603008c0082c203140d105038031400442081a650320003008104400e6014045070300d61460300e846481440c2031340e4684d51340b0100043c00a40e0f0740c485201c5009600c4200003680c60740d1040807840d60f0701a91840c0d40e40b40200c4034101001880b941000503c160b1020036107410513100c5000c0c103c242e1440c01440e01d90f41c44140700740600760180041c1035605000d4058242041d020560262809144410803100340c030804a04200d008410003100300701c2002824195a50700d04421395003004100105480d062500b40400a020754030103000e800311003504011a155180b1050400484040c020741c2c1d05030006002c07100004250800d0b225801c00000c95a03200200020040700544840d1040013090343c1581d820001c2d001080424803035048000e1811008a4403250094078243c1043d0a076840402140e0030150702c5402603031441e0711004040f42d0200420030000120380102c1c5410400040280482d50004 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 610271798 1250 610270548 610270561
    0x15030501050a06080604170f1c0207060e011b031d010219021c0806040903030b040213060e061305060a0513090204090605060a0c03030b120703030825090308130e 71
    0x401142c8900368160050180990310880e40c0e60b40c480869000c1c11080d40342e906e28100b41c1c0307080002c02c00c0018004005080941c0014034001107003c098a1946883e40015620100280c40c020480b20500d140020040020701c201d188110300c0d1100450380415a94020001c0e02005126404580c91a01d500071516600f400c51386404c402002007190016210340d0304113924a8400c4517200c500b00b50a51f85040d100c0d299a414003000d0101e0300011810701da01d500381d0300504d460b0380c40a2715a4074042e8500b00b5001e80f030400c0151019021619241c0582c0c1d0800c04662104240c803032085c11a0019906250f42d800d11200864080c0140c2c0b031200c000f60800310300090745002030b801403c02e490030440204240d6944a040240d248210030003400070404811120f0b001c64001e0340030044000c0040c09002c0d01400d9140d40e03506054460300218080317215181071103084500c40e11031881d02e008000700d8999030b100300c45c4040d00c030303564603c0003c00b407030300c00101002d00b446039005150042909080d2102d540c14440e = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 610273048 1250 610271798 610271801
    0x7121202070312110310060516021c15060b1c020702090405070608070c121b05070605180303040302010c12021c09030b1b040b09030a150b090a061d04050115030501 72
    0x1200c160b0849802c00c00c01001460a00381103d0140a404520021191038013070140c60315002031411130326012170341c09c000300981c491800030700504045c89400320408030385140a69001c01d0392034602118501e0f018042c0010100383c8110b4001c6030303007000c9a540d541c1c1155188006841040c1d030003500900c070751051000704400005ca15007921101d880d13420299945800481d014204048080c18060440302d00e1003805000760013129109081c9049807000803910744503035291118a0303100d040020000a6030008840005040204c1c00c0e900701c0c06549080c0c5540c0000305526004c0030081e00d004184103501c4001402040f03640107000640020b00c120745682e20010b0f250782554441a108400c1000c0042d652400c158040004500c50005a90038a410043c003000030f90800c410868043c441c0c107180c0300215600d043c1d5156290038001002ca0f41600c003070280004050054400ca111509100c0c00780708155419401c8149403c003600552203540d50340c1005409040ca0484c00d08115014510200600c20107 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 610274298 1250 610273048 610273067
    0x60405040912170f040209151009090b06070506010605090a030b090616081b13080f01061a030906060f0a1212091703040e0411060301080d0314040206071212020703 72
    0x1552180b140016403283c980f050000c045600580003611000010010718140440c0358000002d1802a01c081c03ca0002248440030405903050106586003810040070030740d0700960719841c2e4180c038058102040d9030784e11039540c081070080c0300074400041f0fa13008003a200e0310003800007140c0188400140342403e1b02da2a0700d903503040d82d83c070020b0240169650070340c500421031603000c0d4070000301c4548544402c1c51840007035041241c0102c1c0000e01c1c603000040316102000f6180c4414182400042c40700c0c07070004c1c01301011201c01c6907050610700c28010081040b8000c513080b81d009606803000d103900c280f0840003402854031900002c411002c041a8002070101c042d6000741c07141c400d030b11003c0e20306454607c80500380444840e94009640104000d00c000c600d20ba200329002881503420300f101081400010f883e40e0400d80150135070f9400503480d0105c8680c03500840d0305075585040520076508064020403168031031080702519810001e0b018000b95031003104906070300c00d0124021034403040a441c00402c0c5101 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 610275548 1250 610274298 610274333
    0x90f070303050409060f05060304060507142b050705030c0c0a0b070302070b1807030f0c080708060906010b1305040b030c06030703060302030c1e09090c03031908090a0804060e0604050409 82
    0x6405c0020411800080f5424261680200042c4c11555240e480c60040e1030000d150781c1c10404c00000c00c420b007010311006000318008203020520008459040010b00c0220620700303040c00341c2000240b20000b60880c0803281c010081d0078405640c0c03481044c1c003030300d04150018021300c3c44c0614000c01110070b60681c060080244501d0008140340c42d20031094041c0118107141000ea038002c02c0e402c00c0041c030741c030484540840c0b0601c1807072031560382c0d00501c0d804d0a90036030048000f0741201080000c00c0806006081c050b00d2078503091420030480d290171003401e030110700400c0d009a41d1039640901c00d507002c0113690805100200101d41c2c07860203403c014003828161004a0092044044a151030701d05280c001d840d01140c4035a8045100c1c8007000c000d05da000c00f610200756400b402500d810240ca06100510110b04000c4003036003c0c10509400500c000ea00908150050704081c1d503040008144404582c00c8420a10341098514200e60008445101d00d1303210030340c8646041c0d01030f8200090b100401d181040c = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 610276798 1250 610275548 610275551
    0x31e1e0c051c03060803120103031e0e010f03020706060b090a081504020118080102031509180619021308151308030118020706090507031b030c090203090f070303050409 74
    0x101005000d60304000c040c240140315802021107003003411104241c082c0308410300d00d40861620f1307984003418255400074900880700e6000d0030062042c550070521a4034092044d4212400c005820640200311030387d2100098104585050840d19591298064800c03558100300200125661003140c20240da0001c22900c0c0030b21140030380080ca001c80810b22070b003682c4103440140d009540e04c0e401101da075140d051107840d803034442c4100480c3c0c000d404d02c00345108802c1850240d140c9076410301002400f6800a1010891400c0881c0c1074030910303000300d2103540041403922a42d400b00d42510300da802900843c0401e942c40c06400000085100c0c0000303407001e42800003030300c640d8151210410b0308000c0800b03001c081d1051004200401407010a0b5903042c2040d10f61180050601080f40d8070b460564204900c1a605a448100305009200344c0303a079081562044041241c0c11245965500001e042c1c071441034985055001c00001d030141418414400c00042c9403040e80c2c4035644030b250103402e80d0002d025202109 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 610278048 1250 610276798 610276847
    0x2040e0d022803020304090b06070c03050c04140105010c0b101a091519050f1204060510050103050115051303050d11010f0c09090b0a05062d03100e04031e 68
    0x106100c02c26061842d0141e014524080c00d111220700a412800da01a400c842d04010350780100b0001c04071079005e94441c20142001c180c0f01010030080d540c030003c0c81862620403100401943c1c0c1c100700e11a9032182e00480c0703400a03541e4041e1000f118074141c0d00401c0311500a288000d145d00320dd600414911348211040440c11040c4184600f0031302035007004032845001c0e0360880c04064060009410f0b50b250200c40603240840a00b0011a0341d40107580845030552134006010056980311044005032100b8a0100103541c50b108044085801e20400c400900c04001501414440c1d00590940503542040c201d413181c01e01d8107001000410000e00086240d480c2c008840700b2095240201d103c011440c6d581e91a045040504d41d5000742649801c13103070310001c0d103140050581c032814003800b5036107419800803801c01ca80c21589070400394800c4442028803420005c10040103030b460000d000b42c85105803841a180c0d0f40e89000d440c0359101c80305010303010003940940140342d5446811070382050415030321007400 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 610279298 1250 610278048 610278103
    0xc0f0204110d1a030c010813060c0c121103040605070609020918070909030e040f14070915030b06160206040801021c060b03040209040618061404052b03050402040e0d02 74
    0x84905100701d01d134550800303406040d156102da1505504070800c04004c4c2c00c410000d0f0380d23100c200d4241d020040041510020501c040c01285503185001d00c405040071001c4058a00005482c1e103e940264030a00901242c04414000c1c02e0b4041d84d002c4c0d0340680043c020f41410050662482c207000c020a06500c40c1c0f00c4045801c1e180c5000d0202e00c03c0d03040d01d4508824111008201c0545040054400040da54107031a40c02d1003070411030319024000b10785420310490300300710084440306554682e00b004d06040c040c0824941c0c85120886103884d13249042e02c028840e41c0e200060f683d20071a070081160f5070010691600d130345c1001d01601055582c0c8a01084883e030b0341d200905450008541c081e50110040000130082489608544407107010004143d100c0211a91202c00310741d03401c40642c41d00c070022410442003100401020240d140d81c1984c14040440c1c441c041c0116022990b8804100340d22600801c04548658003c5083c001301241903c2c1e000584c1407000755920140d0419892014115540305103 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 610280548 1250 610279298 610279331
    0xc0509033406090605250b040b160509130b1e0f043e0a11150603102f030402010f0e0609150c03120114040614010c0f0204110d 56
    0x84615586030480010704d03054058400750400c2050300d58001181c00c804000106d803078114032002e0b11030703201c01c2d803d41410700348440800f400400494103540060001d40e4640d8224003560b041c0d00302211070025075080c0071903076809019a07108854100d006100040259100585052100310017030300c2c80d08030300c0660000c0006440b191500d80314504010341720320f2500a1900030340c03c141400d86082c20203000d031003500344050358021109040052a0400d0242041c241131181366041101c94080c0ae00d6401e0840020340c403540300d04c809040c9942d4a002144000480a80c41149540c0c1c2000c0040c8541442d5102003041d802210128009020281303c07540560045203460034500f4003910150809500b0030910002b94100b103e400700c1c4101c1844181c802160410061411002021b0010300c5540350100700605003100000d0144a1401c0c143c0600110040c0c4048180b281d50910f04189030b9803440c00e01e00e81200c2c0700c49001c0c0d00582000381d8036072900c80a90050054116200d0100148900e1205024 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 610281798 1250 610280548 610280653
    0x170106060507230d170108070806010e09070f12020112060303080a270606061d090408250308160c0f02010c02221e1e0c050903 56
    0xc80d005104820104010f4045109184061802550440c0703500c10711918010314400d07a00f0024050007058651240861505801400b0050090118504081d0300c0d0351941d10502900c0303c1c03032542100140b0603000402c1950006d1040710a11081580c8400d100da03a0424000303003d074003090044038000409222031241a040f01d8040e921140f0743e0301c80d012040090020b000c1484500c001f0047e4070450300c6541c040c01c000d9035205403000114280340c104090300c8038200241c070000c140b251914221207603c030400910742c0182d0003060385a4034009403041d42e25105240d0000184080030300300e8103040580101d00207000b27504541340c450035512080d50440300402d92181c0203010130707102c8003154019402001510403d5100600802c49828160201380404010041d074944042d19005c0d403090b1407906101c01c01d503101008109000710059440511600c418a41e90004110340e03480c44448203a00c24001d6540710400181600d4003003405e400703845500c1c0c03201d00c0c42c2d20390208500304120f075101d0000c9455 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 610283048 1250 610281798 610281809
    0x90806090604030f0507290f010b07080a030603050609100f0c0909020901020a140d0e12060f0702070f060806040605040204051e0a05090a02030f071d061c021201170106 74
    0x304220b50b035654044a407180c1104440307050050034040000020300d11480020b00ea100310880444e04d101c080c1c440c88100e0030141140d00910b02d02c1c00140f00348030550b000c43e82200e13000a82c46540d03010940040f03000300426070000e41300780110b506015500308081003048a0404001041c40741d2000b1441e1101201c046440344000300c0d041090402207240550040d01d84800c0500503200f41c0643c030f03142c800800d243c4110018643d04800c2c42d03202c659401c0040034103c85002c4e40ca00c0001080d802442e9a9640c0181002d0a196034100014080320b100304031180207030001c038001c03206855075003c001d8103551058075824415030800d00c0200e89410980b0a4904984d0000c01c4403540101d1540140070030340319044a260402040040032800c0c0d154803c9a5029072001d00d00141d49140c0030150081c0428082d0841c010880c0d50486144640c0038410261401d03003048801380d5440340e0700d00d59100035950703041075040c0035400400d6041703030a811030f01c40318100c50055a00c0c2e011101184000c0b0f00301c0e809400351 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 610284298 1250 610283048 610283053
    0x1f0b0d020f0d090b10091a010818120c060c0403020105040314010b060a0201140f040b010e0c130608010311010c02030d12020705061806010f0810020a052115031207060207020d0b10030309080609 85
    0x1400d41e50b1007140041c0c1c00ae80d1070507100024103003c031019410720888045614a0040004500018610410545500072598003101c0c4c141400c550000f007240c459888090a070288680e40074070441429400810000c9005028503620713050ba86012b80a014600c10041c48424100006842d51076101540e92140d90f1180000543da030820701314015002e409407804000301c009100750049002e9009030400500010380b40d03844258958134160044001c0d07440c01c1810081c241c0103034001a14006455881e54070707241084a800780e2903928030030081c0112003010700340b407113032505012880183c0301d1000f0780301c900e2406941107a80c880704000034826151080c0086070f400f0080c01140380c44107901919200300180313012894141c076581e0f20a500340e000d101084824010364184400c41d030072400c01c5d4003288001e03005030490742554004c9002d039010f40080a0002900000e400c403c640c3c3e101120703038010364040d0700c8039a80e080180a002c275084c200d01084000c0703111448049040600010b05a03c2070800c0e400 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 610285548 1250 610284298 610284341
    0x3032a010e210a1803030c151e020c0c0a03060e0118050319050c01050a05150d02010207030807110d050d081005370e1f0b0d020f0d090b1009 62
    0x260408540d21020f40c410070403038420740440c01e03c2d040303d1128004501035030345c028121255013012100214400382c1c1c44100b601d0400554403401e00b40383c201e40e42e03600e80c4400503124204e207050a4249030f42d488010303038041440c01000c001c0050781e0b4011b10001d070406000300020504030300707404601c03a001c42025100d94418480c3e080b81d02c1000042c01e9001c00285021800c040071003401d64299142920240c1c855500d640030407440481c4142c07161031040b400c41c0c91a00d15142c0e5000030751200d9480c0405040241c001030f01109228221644003403d22010b01400b1401005d4249241ca494880c804d0200081d058000306d41090802803100b02603c01c0101001d5010b00180d000324201d41c46001184801a07021030001c3d501d081d0702a82100901d49403003016841d180c07001b04202504402403949074523820450041c4032031180039040e034129816550005aa940d46210b040102c0e0296500800300b450404000301c0c2045811040706025190001c0b203c801e032502c40908a068903448078000003445411103 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 610286798 1250 610285548 610285603
    0x60d15140d1101051b010e0d020303060a170f1f0605061c2c2d120d061206060e130312020904061a0408100506010507060b03032a010e 59
    0x3200b81075003800504040b4500b81c65951511707012501ca14032042d65956618a02405075420302040d401050385101a519500d4000300280b400d20b124041c0c040080c00328041000c45003401c004c60b11074907102804031441e14031100520564034242d4003203211440e003440c1000aaa08001d0240c440401e003001109240139150f4003000000c04100f008034541038011003101045020a0084c08520031081010b05044465041840e02001c0d001c03d0a403068020350591b0196440046021450080c1540c00c1560355240d090690010340060b81000c6032040100c0300a204000311540104200ca00c0000d480016036502403190303030310324050840603000c0b81000c1d03200000e00300290300070004080c00400004489456074095580c8002c80003040643e107400103030501c981c0c0010401d14174503941c1c000041c001c40c42c0c507000007401c600030a500240849d44600c3c0c081601c0e640cc0c025900d59450600700e445c540355114001c03d401d86064000418a5440c00c6100c00c2400c0001ca40846103070400340000484c20400c0 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 610288048 1250 610286798 610286813
    0x390b09010e03010f0504080c070e0402090106030908130e0f13030903032f0312061e060901140c060a0b03070509060d0501060b0414040c03091e05010605060d15140d 72
    0x90740745505540c1c40c040890100042d01c2a2130055029502c017680380e00e03849044a2901025401c858101c032400d0040000690321150603e064030801d16020031001c2e02842c1107031f21801180d5000750346075401a40491400500454607202c0d12000b2028a01901e40145242d02a00c201d04050009101054140301007070181c9400030303003500011130f07018401411002c00300700808000c007402240e801c00104406140b4180c2c01b0307207030040c40480e04820702c41c0c05400b00c00c0a41d41a0000d150180c04086400c0304160300800540303c1262300380004a568034507141b40340303889440894040c00e451340342501c0000c0c03c5c10006411020b0f100081c14000c09a2128020072106564540d0219025900d6040c0442c2c40b8401030050402800c00002c1410f501300c0d15010001595086a048800c0500d010b2419002c079080320746100449044c1c0c2506039050180d0300305280540503a4101d10b403c0382e0b000450322000140780d40400700a0409100c0c503002c40751079008580030140c80091031644010fa00341101d0100360b42 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 610289298 1250 610288048 610288067
    0x110d150c0e040903080402182202040f05090f2e0207080906070b040308130309170a140304030212070509060111010b090c09040f06030803070f0309390b0901 69
    0xa07814000d0709640d0500000d41a1091154100e0000d03065600b0300c0118106540070a403514044070728a0003e140044101803000f82d000d481c00781f00455400d01c10103540342d9a00c0281c01d40303510704060020346496110a65140c010710907000c050b00c900c1150301140b0307401002081021000b030486400707000a40c0d0340c05021303400100b015940d00c0c0080008900d0b41d07a4100007481c0d407500c9410407281078a8541009030044100900c8075400d802c080c4518000641d0108a00b001d458401e1400c10112191002251503c4504140207103541400c4502409a040c0000a001228421a980c19800080100f841e840d40500c0c0314007500107510707001045a66000740c010f510f20100c180b00000c2c280764204002811036000356690f4007000310000e091409406d0a008002e104100c44009000380b40c51075581108500c0010400030401c0304421390104560f01c2500484105500242d1814140703400b18017030200c5a540c5800300180701c0300607541115403110010000300701c0f040508a2402d026003000103603034500a = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 610290548 1250 610289298 610289321
    0x304031e1b0c03030f141812030c1608030a08071d0306190e01060807050108090a08031302011d030c090a09050609030a090608010e0f0406061212020607020a0c050402090a050913110d15 81
    0x201005001c230141c03c10070280004140d00001030986000e1422003544484480c4c200d084140c100304240007075960420429a0043c080389449008180d06d0200c000784100250780b2180d05003e00e8086c41003000c0d402c004032084420350300e0200511510200e1040c202d403054030a055243d0001c00c420001580a0401c207a40001080c00740e900700c4d61240d441c5e00303260303004440c000c0f040c0b917000103080155640211034101e04003035210308078001c0700860300081d0344001c02806030f0b12420344d810000760701180344e170081241198401c040740e0303050400c951101e40360380001e0003481c0001c081c2040050304e54481c0290f5812646500b2411015440b4003044120740e0760000c2099900c0b944039980080d15180c07410760307169424000c5002d1070303184090043c000e04260029143c501158000d1148002080344e8200e01421504121001603842103141c000c200316500c140d000350390000707200e8104990311440c43c0036003d050788203248841c0071840c1c0408108040849a401a000c01ca440a250220325413560180c4220318 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 610291798 1250 610290548 610290559
    0x70b0402093c0106090303080f1f030803040b1e040311010204030c0e07080a0b220902060417010b06180603070c0507060908010e01020304031e1b0c03030f1418 70
    0x500541102014418844118107065486000c000b003581815038028003600301480c04034001459a28006c0001c2000381034100c1c003c0c0d0a20102d1844401c4501100b0814034a10550101950b03e04100c6040d030412942641c840ca58440000c810103014900400c03006204094100541c40d540c5040b10308401b03454a5460f01d41d8204004400f04141042020003801c1c000489507051602d11402420b150018000500e00742c2840070701005030383d5100117000c0c0c0d1f14001d0360114011a4102c85000500f0010344044d4020500040100c5c0c18029240500c00c4001010005d0040049602c144801c0d440340e841086110030350101d40c00d140f40382c16401580c0080c041d24210a00b08a5501c0c0c003400d051050f405080411400c41c1e003004a10003c0c02030380c42160b0494000c50642c601034a02038200144106034880e1307139200142000005006000d2115400044401034501d0b42c01403401c0400d07400640419004940300c518a5000f0078420490811510a065101800e10320400740710080d03040d0000b400d96205 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 610293048 1250 610291798 610291831
    0x1d030a0c080715110901030c030b010f0f0512070e0a0806061005030603031c1a1509041d0d02030928090b0f1807080c0309070e0606280207050402070b040209 69
    0x10340282c014204d15603c03424041c0c0e610081e040002d42140c501002c1d407c1030506140005020382c0c1c000c562043c12101504010108203055001180c2c24821200c1a600c0c0c0740a103406d10805a07070114100c8200082a121200119200d01c200d13551007108480c4903500104a80d50140306600c80d0740031715086080541100d041003c0502844170812a001001e9080c5540d0b00722000555100e160a94103010b00703540c007003c10344c0001050400362284280d101c0c080e5450f6070000e4551510822041088941c40094034030040c4404e030025203035800482d12900c20300001281c511103464808465085143c08404c4c0c06030b031494000c0c031102034445441e640c2d5000307250070080100b80d21058445800e001404080224030300d0910806425414080c04a81d007a200a0081207100000000c41740d00b50f980100c250f03001a510f080c00500180300d5070a002d074031001c02200b4030f0400320001c801d00c13110f501260280e812464481007808124007600030043c10b030220442c0801c0250410540541e00807110840d012442d = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 610294298 1250 610293048 610293083
    0x1e11010c080f0304050a210c060c020717030304151a1201200c060a020708070b0405120a0f2a030302030a06050d0f06060e0c030115020c030708011d030a0c0807 70
    0xd0b0308201c805481d030f07800c0000c0702c0e41082021300511f840c1500182d00750714803580b401d00042041111980080400c0d68a030075449805d802049880010440c0101c2094410030b0401402e441e50400c0d82d00b01d030000700d2890940c0c07094940d80100c148141c0b40380d40e14070107112030b0070400055000c2030409003a039550f2800b809c0d009550207620300201016007541a035441e040140c04070b00d0850000c0009501e2071041c4005400a09c81c082203400d0180c10900003030454981c0d00b001401d003124540c503c001d0000c001166083c0503000107482c80484001d49817001c800d03c0081c54200e000c80c1c0303022201e02c2d100c0d5141a0307100003130095002e107402c110101e03400902181ca890110304000d4007000295450514480e11200b000042d00a880240c4080501c5442500f0080c6081c60a80418060700f10b40310801c58130302515610030458245c05900041c00c07070308040c2c0e80d210400e000f000c2d000070441031044100040560a070300042180c0c108042542c070a29102510380395607400b83c000ca803044543c0312440d8102da00 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 610295548 1250 610294298 610294327
    0x110c01082d09010e07050f2101060b180108090a0b1303050f0a02160911041202060904050c0c010e0316140a12020c101704021e0406121e11010c08 64
    0x700d2002d00d00002080400c0200f504d18282107940024401c0344045c8041c051a11005035240403115404500007101c12601001c90240009410090580d040400c0c10394644201a1000304844030a80341d101c12911201803035034842c0c44c6444042c015071020404504c0c01c1960441100c081800303803910f2030600100300080016035015107201c40050380040100604d0015a00c40e140c0100041c42d0104111001420851000e00440c4141d804a080e45211032055446141c2100c0e50300d18001c00070016450700f1741a0580e16004400c21044662800b02400b40102c000400c4075075020700398661900c40400b41e512903a5040030301400d05028010301010100041c6101501c44600340300390094540e1801e10f005100c110481c4003007000411440754802c0080c201e0240d02e0315007054040d20100341044403d043c00d40d21412003d0001d82113490403000244d00c0030001540900300d0320503250282c4a10b01200508400c48103904094030307211001c64400300c0d0b58050340440c00c24503c038000f024100a0380461411 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 610296798 1250 610295548 610295551
    0x307140105040f12170a020703060903050403150614060c031603090806090604120e0d030f020c06070f0209160503070c0507030c0312030b010516031d090c0a110c01082d 74
    0x2a00c1e925901090040186201003101a01c17440021682800700c1c0010082d9644401d10002e0a4103907184405024940315100701c80c003458000d100403000700074008000380200042d10440a1815808003045124034248085910580340c0d400103604182c5c400d2840115045410412000e00060040000e94441c05010440c880c1580c0d074080c0c4024501820558a0214120301c12401c0001c9952401c0e4540e036201043c504240e09880c0c00d075400c00c80d8400507450427691210032644200041400c40410a400c80140c1c0000e02c01e4030b000266859103418070701c05000c05400000419002d000042e0f800d032041c3c0b1a81941ca000d0340449030803a6a9407079480307241903680c0090b0750a10500d040400829014090034840c10420f00e0f00038541001200c40c01c88510742800014200061340140c0d0706d503403101020640114400908a04a509241000c080c403035200301c0030000462030482c54201e00740d4000c203203540c0820040c0c481244030758a00e20925000301a120354286806030f031940c44007643c290700c030721207 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 610298048 1250 610296798 610296809
    0x409020d06090c050304150c05040902071506080a02040b040b060f0a0210110a030c090305060a0f1b03020c16080706140d1a0307170706050906040b13060e0f0307140105040f 76
    0x5d6603810720303007000314511201210041c500c030708040c00c03005c07500e90080031502103c828120068441429182c4141003803c01c507414454242000008501c8950100d15072010b140701b151300304500328590b81070005603104503140540c807103404d200c50101d0007503490040a1480c25441034580030540f41841c0b400301c414800c88007140310300226003005815010320894100825608050b1005491a50703030603941c00c802400000410348951000400302555002030206084800c1300c040c071003208210040007034014a21643c204d1181c614100c96104080050f542941c4030740c1c0240c003807141070a0050700e044148611580c04444201b00301da007903107110700c1036079804039946002c1c008580e2131508240c178003541c903013110084075110441000d00c0d400000d200c42c1141c505003405515651030030006400b501480e40170f410358050001e80242c00585642103030003520241d4035018600d030382c8903050010100d0040019078050703004030014820400ea5030300140f416103051420600d81500e9015000152580c0e5008 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 610299298 1250 610298048 610298057
    0x3030c01111206010c050d030f0617030c060c040b07020114070605040f0b010614220e04030e1c03022d121b060405070b090a090e0607090602060c0409020d06090c 71
    0x210403a40a01400c0c035802030401d180c05000d901d0680c803141c1c7c45020403040c1c04149690740e000c0690301d002c5904040700410b5040c030010724510522501070f03220b80c403d032a000304034098440000c5210086805460980c1c505c0c40100303080080d5039005613401060713031100111641080c800140080c1c42c6000d064482c92051341085200d10062401601c03044040e040030003071014451000240c2030180d0107031401c034844e8040158a243d1000d0514090b029940c20421101741d9910800041c16082803903000d504000313683c9107480da4200d0810041d1542003003001801a04641c0b40031001c020f9003140411200a01220344080c007242c02d00a91520003612185c0603105004038801c40c840c010198907c060041e944003400251030b041d541d50b034451929004d10380c030800340480c11000b6600c0300a08600642904902040f00381840144182d8540741249d45100080300d55001058003440810880e00603948210701a0600741000543e01c084c5d040b0341c101c0100c4684d102da001946100c0f030701800c0c02c42c40d240e0300c5 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 610300548 1250 610299298 610299307
    0x302011e02070c05040c1b08070b16090b1c20160c0b0c0c010c05011401060e09161b02010e04060e0609090303130f031b03090f0e0f04030e03030c0111 66
    0xf00159030800c0b80d03004500c185d150444900406030040e0b20801840045048101d0444245c64102601d019441000d81440c50315070401407143c080e5100e160000d0440d0301c4202803199100d4880d1000c1c4199802a002802110703400c5c21140b01e50740059100d5070302d68841c04a650500c1c00d40b1405500402c2d0b00304040d5204900703c00600c0311900440c0040d100f24035a140c9031404840c1c22503582d00d100c1d039000d030400c00c07e0400c0d20140603080d0b00c0030040d0600605080e913103595030400204201405000a4030400d80c40010468480c03d0a9445041540e90f0701c6110403080e030400c80d80d60848104006906001c48070440465943e16486910060b0261001c1524141031000902101c4a002480002c1d0395008109001140300e00740303048010b00c0e42c0b05840035140d4241d0725040b19000103013500300402003500519a0700305904608080192030350680782040d100da4512020f82c032000c007900c20811003540d041c041270200e842000c03840140780c00901141d1400001c070080c582103030310034800421b690303d0104 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 610301798 1250 610300548 610300553
    0x90d21090501030506061204150207080301090e0a150c0e0303313206031003021e092a040f030326190f020c06060307080601080a030503040302011e0207 67
    0x21032503015203400c1c039080025142c201c022609038444c051070400f0b43d046020000e8100100a040100ca00000520640d100e4885180c800e01c5d07a0001c0c00740c60001c0b414580020865400083d0003903255400880b0819240103100b00302c4001e100524000041005801980710203490400040540001d0341500428214803a044040c810200350402d103003182c882c107020849201c048030032504d020300f080031841c90442c100b07018880b440d07602d2140320f0300900c022081040c0c01420f02da2100c2101d000b035441d00314412180f500011001c507010f41695100440700046401400751080c00300c450642e401d40ca0426a100001c0181d103600141c0c030041400078885424000c0540c08003074000544600c60400c1e0808440d8031240441440040240402e100340c00000b08440302c80b60001c5c0010034084908650302d503007566425032100411507409009102e82e110020307441360005410390480e400c3d000580007010065804680aa001a01c02c0d405c40d0348904d003946540c002c4c0d21501c1c01e8105540001a6241c2003031 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 610303048 1250 610301798 610301807
    0x503070b06030a0c0e060a030204060e15090910050603032a0f030f0d020306010201090c06020109110901080a0305071a0c2106010801181b030b180714090d21 69
    0x7440c89000f6004028a10006840b80b0740da0010785100004041d5150743d50030100e20000195480030b0742c010701b40280002d0000396511141d01034012864240703621841d0006010380810161000041d55101807981c00c07004003180d0025030080d80c004d003a00d29260080210b001102841400703504041c5107580803d26000040140b8441c09011101035410507150600e03074440c9000e202c0854030138540010000c0c042e03038401c0d03100a09282c3d01038001600741d81c851800a00904080030100c3e10555520308240031850045885c9040b030704003034010240ca20341540c040f038864114017001c039482c40d0000b0355a0700118407845240c0c0700d803000b00c0c015a121038500a0807004c031501c03061400d100e01058018040d0760b0742d101d118141920784001c20b100a0b40364041002000303240c030703101c50b1000001f0991507803980b9034103401c45403d2110840d80078070390018001040c034203c841a20443c02040c032542202405004000182c503075520002d02c03009803c01e56407250003543c60005840008880c03c4800800d03003d811 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 610304298 1250 610303048 610303051
    0xb1305090d02011104030303090f02030a142104030f0f2001080601180611150a0606090609080a15060b070302010b010f1b0609140f010b010207150509100e04090503070b 74
    0xd02c002e01125003046800e882c50710850101508040e20349a0701d2081c4540016448030181d070103400c5071202142e60405040c0602c42458011710b034090710400e04d43c034140312241c4110851610740110f1500b0714550b150a0810800c02c0200c407440d80a500050204920156074401c660180c0021550020000c0004143e03080050100b810300980c411011141c04140600c58151000c50070080c0c604d2600207005890003450032045000c441000003044a05909038004a0032111640c9030581c14545078030068420074001d001c0c10105a11085629000c078001a060407100c280003000003a140d83c4071000a00340c0c0e03202c0b03902500940e440c2d00c00c1c801c15503401b0b05c07000c0000c03499150003c1c841088039011150203000242c05004a80c481071203009118203000d4001c251a045c0781218003102c1040703d101d01a042d90300089015024075100001c445006200001d40c0003156940d82e0b01d030010100400411074907421340c0c04d0070441c9481100640c2d494600c910b0701094002d00c0216110041440d040c03085080 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 610305548 1250 610304298 610304323
    0xb121b04051003050615040e071211010507150b060715090212030405060f0d0b030703030207081018060f0906150e09030c0a2603010f060e0406050102071205010b130509 74
    0x142c0010004035502180c201d070040884450300440200c240006005095080c00c1801c96003e8140d0009144800e40500c0421612454041c1a0030801400645032401010b4025180c2d000d0b010a0044c1003519074000310b45544001c14050a0000d15200d46001e070248002a04400780d031901414190300c0c20b5401c3c2d1010940c000c00640c606414000450780300d0280000580c0c41034004110859202e400b41c120b2651500d015089590725076480c28029a20a614403c00c005805002d0011031385c001c05014035103400100030b034050300c050110760744c820081c030030000a118510703515404440041d140d402407001c1d81915035181030500741403407403a00122b00c0290698070954020007602d011000c011454522441e0000702c040c806120a05c42169000ca00120a1620580000000c6403031138054a030b080940c2c050b40d85221840c41d074072080c0411a5118003c00d409603214060070003403a0400c003601042c01d40f00d1000490150215000b280c0200305a04001c01403645410030407039071845c1085500b40000 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 610306798 1250 610305548 610305571
    0x30f01060506090105090604120303060321020c090402061207050a020d0c0b060906130603050a03030606110c040507030e06040609030e09070e09040f14060609010b0705030301090b121b0405 83
    0x40c07428000407868440c0c5115181800300205003040b0341d6035080c00340c800601c080550030800c4d00c818a002802400540411650f4210340c910f58481034101d000c03610255451a0004c0c1003000240701005403c4c480100b040343c0c040313803c00c04151a1441958847d0080015031903094441c50140b1010342403503155001681003009120008000c0303040c04d20300c0d540000c0140d9807440251a8080451002c0c0465030003e034006003003403400801c1000000f1074894050090780c01300440f03500c50f03c0480d40305004100b001902d9000070205019807400c5d520458004426040012f0070440d1000c1c82c074140341e41250103a59051341c41100f60305160304286903c100729411078200c80d05107018000908030000302016180288100400034041080c2d2001401d5415001100b000e00618801d00c419640e0108644050040c50b80f4000024030752400030541c0d80c00d5038011301860440e824804180c00618901c00c101c0c1d030040d01c415005014003400d20200b8040c07001c8040303110049600d00c042c0015504007a100d0910359 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 610308048 1250 610306798 610306811
    0x150501030e031606141513060806061e03120d060e0609011514040e0912160204020c28260901030c0212030a0207030e120a140a05120405030f01 63
    0x8000401240d8040c103060240c01120078203030522500070107180c050b117504004003001307200c401c8001c89804c1014000844070704856500d0003d412084d0f9050784035002156000c800071039400d00d00840b0080b100c1240d055802200244607000034603065402e6410240050000340c8400021500d008080141420100e41d5080382800d00100303403441c405110340c9908030b005c0720212140300e1061007044409641d0000383ea403540d446800d440c04c0e03004166000d145501c0f824061034141006201514110040f240c1340b111070950903003c0c00042c0d80940c55102e0705004603540c0603040e5280a8910100c403012200301c10040a051600e45c1c3d4030566035102d04403006404031040303071038120300040768100d640030710f80410820a14601645040000c011094407510007004100140605501411690b0301030350b100d00301c20b26000c3c288a010401c6c0c003078080b540e403c10921035000c15005d941200404404808440728801c42c0d0b200c09003410324074001003014400005041240d4607040040a000301782c000000c1044 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 610309298 1250 610308048 610308071
    0x13080f27030a0807150c0302031f0e3103050304050709050907031713031b060302030c030105060a022103061e03100f0612080d06060c0b1506070203030a020115050103 73
    0x440710302c90401000d002c07000a40c0c82c00c105440c1641ca07052a070844041c095180c0310345000d0007039041202c9543c501100d09010004500244201c4000c5800c80d030220000c40d1030340ca1031564440110403402c3c075441300b0b100e041040c84051a10007050540251794560300c80c2810300d00079042031016400150200d050100380000c1c08000701e4290100c80e0f01c41402d02c03c0d41e0824801c8841d501130528450108583c009000080c081d0346000040108c074010b0034031031201c1d11100c05408030700090311052040d01041c0010301c05170070410010440c00c0c10b0703401116101c441c0310030180101140280c480c5035819000c402c4c8290343c104022940d80d40f80110001c0d810148410001c42d5540c520010b000303420039241c46034009000340692018001e406da0803040100c071a094100f210056104441000b8032078502280022003500c5162241c0609034094402c030740b552107031200f000c5810380003813a503a07001804000d42c1c80144d070b0410080c80100130540000c00c513034100364180c580768075455001505050401002021 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 610310548 1250 610309298 610309303
    0x60a110304180b03061e060d020315070908191b0b160606052b020a080d0206010e0f0402030d080406021b1006231504030f0305030123090f13080f2703 66
    0x19030310b2801c1c44145142d483c1000101a8488c208010750580901110440104010350407148900c2c515120000c8169803a0101ea0366102030110880c5d604e440400c40c400014141120307240c920807a016401034003503c0c0d19560709940c5c010300c4a0038140c001c038038840d0700b001000c0c001c03c00180320403541207034a5583c0c200d040034040030f250313060004102e05104010455a4034410100039003804021500c43d8404103401075030300d000030301544910201c0c000001b0681e207412480305110340d501030003424a17925180401d51740404094401c4401c0c0c1d4003403090155640e8245c01c07105003400d10317400030400c210000e20007904840c02e5811101700c0ba06018925445000c401c24000c000f6034045d11250702504071015404294000c54100402080c1410309120605500c50003450603602c1c0d440400c450301090200c400c843c3c001094405800980740030008d0302c0201c1d801c0081c1d52150b10030600390303050420380d50390030220346c4445240050500080307260380158131480c00412050006c2d490060b010300c04140008d5 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 610311798 1250 610310548 610310581
    0xe180621071d06012001110301080d030518150403110a0f02040506011403150a2411070614090301021903150e0408070b090a060504061b031505060a110304180b0306 72
    0x1081185d110040c40b052400358000d40c0c8003481c0b07046258a950710740c07040340d480301000a405000241014040382c050501400d03503070208d0400c2c1004110071140d000d0841d20080d001070040e002d004104d1070014112030b051003e1522144904591130844969104000c202c80c005400141080003040c00b91001850000403070303030045940c200310000ea4400900207104c1c03013000e0b000303000d2450350703001007000c411925140314200340c8150b01c0c0c001e400b4040b404845d603900d400c0e00c103000000719a0260950760030700120060001400190016281c402d020425a070104201d10300840026038820b000d042c80201207100c03c000d003106501406190509850740e141c540103440300039003500310000c080b9511400400907070300043c1c0e0049052102c2c3c43d0a0600d4030081c801c00542039503041105040c811700d980709108241119140d02c400c0c40000381450241325180d0000d0b0030fa00706100d01170080c000010002c001a1009021504000d05200408000441550340e000d43c4a40242e100205100c0c3d81c409500100 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 610313048 1250 610311798 610311827
    0xe090d050f040b070804050a0b07170918040b01080f0a111306030b0a090c0501030207260904060b0c0111120109020f040b0705060906070e180621071d0601 68
    0x10307521000c4031040400144107540c04810702040001c0c51404101101d00a002100e4045848560b86542c4903a075003042e210308039000341002000c08281000c00b0084000d0417500c08042c01406440b0404000c100007003d0a450585881040a00400401404000b06041c0d02d0041c0003609041301150740c0c02040280c149885032048114040301408120540d1201c0c0c000c0d90041074a07111800c0c45046034004003080481506c800a41c0d071720200d05940031303000700c0348019813280300c06c0402800c0e0b000302846d165540003190781c00d141c1000700d04c0c900d030360301c1c01a10007821060125550398070907802c3c042d084840c5400c00e055000b00c28050111448850f41241c1e0441e0a504d80c0960742d04243c2c240b100582c419a000380c580c034000880d15409212000405510801d041011200b00e0b45401e5015103441d815840c941c1d44c410f654200010702d02282583d9507410440c00781000f440304001c4c20480c1030103265455010120b9101e06400c0205400d030307407140c600701c1e88902e001c2c901500341840024070151031390424 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 610314298 1250 610313048 610313057
    0xd110d1d031e0f13090b010509010e040b030a060f0b09010f0506030f09010603080403030f021e0303010504021b240a05040507060c0206070f0c2d0317040905040308040c0e090d 77
    0x41101e41e40c802d08030340900d030b4860300310303580c0c0e000b50ba9024404281c039024610065252002c92456940540d0403114540016105c14280800a000300800b5000480b2815051f00a1034000700c00240540121070402062000109014003540e0910940860591003440d0032220368100f0400368544004685c1c0020301d250076450103940d41031025000d0b1807603a000608404001400005065100041d0840c80d1010703800d5892015543c00100c0d4004989503080060390403c0004204a19040e8001d047c22805015401e2156001c0c1c074842e03041000d550344141034a8034055030086c281202d10b5a107640b100b50020300700464146500d03016601c507001e0180805100c660b41d03808066540761000d54560300da1080316a550394036517140541d042696031065500c07200551440320070002c50f424448d45940e0701c514440c40040c1c510748450b081c529140d501103281c00700c10080410003078103074040c0030301c114000d40700d2020030b080600d41814010b030030342d00c52200c4d4020b8000b03010f0300703086c0400e0292140205261 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 610315548 1250 610314298 610314337
    0x40809060a0c050a08030a06140a150309060f0c080108060f0708060d0204051801050907081c0c12032a1d011806120e0105090706050706020d110d1d03 66
    0x5442020b610203010300188983d00b04007040203039000c001c500c40c5440784010b0000d96660500e100985c54107611a545c070007d0b000080c4070800c040300211111294030314020900324026120071080b600c02560101095440380010760815810014103401000001c0080c001845c05662a03c3d00b00000b5140008100c140e9000c01c2041d030700c0341e004050864000f0820420350402c44200024000c51401d0b811080d420700e4000340c2024000b01e4040c08441c100c501814180e01c160558145d609080980340c024030030051661310114034111049038440000d61800a054400c1070940c0c2c0b4044e541d24101c1d260040c01a003176180e070a9128289003140a440e0700300c030307025905040040e60407000103000a840b50381072010000301e20390b1142512a585111074020419000c082c0301c401d00b80d50048451907060b601044041111912503402842070307601414006042500d83c3e078021094494140e010940c0000c003113108e111407a000e00c1000381d0b205003091484842c032400b29510b610b0b400341c85c0001844842921 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 610316798 1250 610315548 610315567
    0x9150f0a1d01020304140609250f080312010906051e0102011407020d090801061d04110405130201112a0f0d05070f090218040903030b0915040b0904080906 68
    0x20454041d0702508079500c8003800e0003442060003900100c40070340318401241ca008480b05404901d05001d65055409402c40c0007688170200c0090900c0010b140c0c21960300700d000234402d40c402800030040c04005001d103a40c1e01035040c42c42810441a04541004e6291400800583e5034260881031902d45042100c0c00304100c540050707004100003400702852081303420400200c185d01107000018429591600026181c41c1c440190803140c09018a200303070200c0c4408000da034070b040300e101b40d4414801c4070b24812400c0020702183c00e0307400a554043d0101c2e1340c8413103941190307002071084081c2c0c55400c00424406481e5021052000011080031041800d6079000d0303040741e1581e80118007543c1016022442000c114904203a80d01c95511030031030362a2a495000c14012018000c440883d40f5001560b60642902800c10001303088284c0f0031403e00d6585d841144a54035400c181c14441c40d0000903503950311800d102444199100c1c80c91980c4078170059410007000a10100964000140540700d850701c0e03e0402 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 610318048 1250 610316798 610316801
    0x82505090a090609060e010614031e120a05090909030c0a02040203071803050304140d03080402090c0c0d1d150706052809061503030503060d0c050a0605090909150f0a 73
    0x2060182070319041000b200b040c400b10381c01591b8440d181c0c0008001c0d083ea01e09a106004402e44c0700700b581070f0040680041d41c00368800d650700b001c1603000c040c0c504a10b2407088a080030303480b82d07042001290001c5104001460103040341a8808020300103589044000b80c0415283c48081070002d01c210350100210b401e251240d0001615480c1d0f41c0c0390000704d50303160b0401c555a604544110a2543c0e20074203040c070b880c10580303ca803103460391541f81d900c5a41c0b555820050300080c000d008480854061118540d40c11b0104004005600281c907814140c0c3c0d10551609002c010000340e2500035842070707001c030085041020480c0c42d05600040000781540b680c0c0110340390910312403071081d00140c0716540c0c0c050000075588203e211500c0340b0f41c2001510040e2261107034822251001030085070043c00040d860782400d101e943c903142d2080c018180c40d203407110005410b40312903400c1000040c0000c01d0302080da062450b00b0700e400900c1400202161002c1403401c0c0f45000005010f0200030f800040404d0461825 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 610319298 1250 610318048 610318061
    0x6050910120f060803040f0f05210a080d0b120d050f130305150f0f060109030308060a031202150906160c030e1c1b0b0315030c1009082505090a 63
    0x40d03082400050360b2074009a642ea00703e4050087e0080320810005040700c00403071500121070000e00070410000818401440014030f00241038054010040302c0f40006802c20002c1040c40d425a0001a007a844281800204620342d150180f040d031081480d03030305540d000802d4a400446054400760341e11444002c080b0102d4090740010802e00c01d09030180e100913503d003c03c521482540314203480c1a0349210400091034029606940400c01006050001c41d101d0091240d2024000e032540500c03030354966424900701c0081c5080c400503040350a41d2505001607850003904005244000c1c4120305000601248040701c2c0309008003404052001c0500f09405441c0707004034614010300e81e480700783c08a0511505004205000c46990f400c8500380b071941003054680e202030b6010405505d040d5900d07000c00942c4030700340008996052044222217211961800125541c2d41d4055132586070482c64580302ea4500380f08201c4844031044800542904030718801040401c88a04640d4000d0301e4071072004c200002c102 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 610320548 1250 610319298 610319321
    0xd020411030105091e0c03071b03020309010f021c0806030f030d0207020a090507120b060c1c080112030509101b030c03110307110d080c03160c0605091012 68
    0x81600a00c0e00403000c03405141200e0301920402810340c3c581d10391504066a854200000350742d280c011501e049540d030055607001e0f9540c1000025090100411104002c03641801c030700681c0001207c03941541c0c45140540e0360344c5c07640003e000c1c41d0350000c90164042e4502003210200220000029041d580070054140203503000400d8a68a075094030010300030794401d0105902840804100003445892885840d104d80a1566000c04c1c03500082041c4010702a440e103069031128052180d44007806c03090080c2005656011061441580400350103402203005910103030394030060100300404680c10204031000314008072192491480c6411003660200f1001001c60074800c1c1c4121070303c0c01c242d0020700702584030380681c5500d41c1c01c0c41c008a02c81d44c0ca02c00e4100c0246448148504504036091101d41c4001540c07003450020f0400000141283c0b864101554a201594060008209003d65490721201804451824501d000b80c0c0c4000b0808801c0e10411003006c00000c80d00d541e84444590340070054030348 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 610321798 1250 610320548 610320551
    0x307030f0f0c030f030923090c040b0a081009180605070224040606080c01120911060f0301030c141c0302120a020106240221041e06021b060d09020d0204 67
    0x180c0f02d04010003102d884203011004105426000704044045224084007a1840720b0151000403c2e0f10078030001c81c10281c04075580f01014840407031340c52203e0303014084000542d07652122500c0c0900d4000708020309503000e684403601c1c0004030341e0307000d1901c404000381a80089000c98070f40c94214040303280821200300c1d54622400000031180d220709030030b0601d0149020b00d03000c1c065517803101c1001d501e8414241842d40840c50706900a00d444060360403044410b40211a8244517401100c045403d0380c0c89030245444520000006100300008040c6007006402c01040340002041020041050410b00d10122150302d601d101440d07003018400c10045c29035814910070306032106900c04010307010704038034021150500c00840ca021860007080201900d0500740354000d01c50b10a0300345200c0701510044181518400003000049400c20000a04018202040101200240c64650b0013810602c00025180e031151095081c0312035941d03110291003a2451890001131483c00510003d040c4081040b402908036 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 610323048 1250 610321798 610321823
    0xc07020d0303091103010c09180609021614010603020102150a0f060311040b01020105101502030c161409040c030215120f041a10060e0d0615050109060e0307030f0f 72
    0x103906821143c01584900c0c0c03450000c054104c205401d85402e4000c000c0010304500d001c100c05030b0209480c0e49030345c520140024540b42c0b20420041a6032021901c100452503400048080201d034a12040c2c50f4001140200700c440e0560380001d41398035003030144211818690b03003c40c2030000154400e40f0b4289101078200720040d900e01e0310201c441d01c2490502c1c4110700e00a4190010350040c050305108515003015030ba100303030a01044030004811817510340708600c000c0c03200c0150300384200300b409018036001030540c0f08580340c080d500903542e0014000302d014814100500001802c510020030a0700d41c112451010b4100f510f80603010b0340a80300078240c01c484030805010305003a00c00c0d281390146000301440e052459076036101214501d0142e4950a00a034031401c00c1003810700c920b10703910038420b00034460800859151200400d95140225000014103410703002c1200350f0300082c803c0020906420100c005520790750000b91942205d210107000c01555200c032004124200315a4040b0790340c84040020722 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 610324298 1250 610323048 610323053
    0x301050f06090d2d0807061a0d08191d011116120c05030a0506070305070309080708120a060b090103050a02130b030106020609010203161b210206150303030f0c07020d 73
    0x22500310366140105200584414061340103922114100181c101c80700754607145203a514a00242103543c1400e042d41d04400300b1008a99803148190311190203648000d031208a50a0361a1400500d124901e00b030202080c04100300040401203610766000900700078070f174502d22240c2103044c00031107424081c0b061200c1c20082010500a0441c0ca07450b401107143d01c55403500d500505503134003880b50000e865a800340001544451181d001035034403884030724010482002c1959100402e4010329000c84005501103075008074000416880d80d40007482000a0103000d06d40042c0c5420b41c8103002e8460b041640300c00016015901a804445030040392a5260140c25668004500c040e042801420010700510f00802c001c05014001d680c015902c0d40f03075440d0b010800705400c0c2c0350401d2141c149035a0f01104946007011588083c500810b0901213100c1e1311442d420318100034100f502c010050301d03109002020305a00d0340c400206480d17010007402d04c42401600c03440c036100d060f40111000207501402c81c0180e01c04 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 610325548 1250 610324298 610324313
    0x304020310020a0216090e070e04050c10120b040506150a0203040b0a0905031203190915090c061b12140c0d020c1305130204020a030f020408010902120307080301050f06090d 76
    0xb00c0700c50f00340c10f480b038650300d66103020161128006181c206a006c0d0341d0270712244031a0380c021500144034004036820a90f6001c042500401c494a011010401c41d000024030591240039080c0c50a208070750070402481c10b4400035100311800c200180c82d0040208600c150301d0300800888001d007422841c107a03100c9140c0c0300c0040000d134180c05190f00a00400c21002450000c40c0292070140158010380c001c0d4900c001a100014064070005a41a203002640c090080c00ba82c450a030b1304600884c14403d2080c10518040c100180c0300540955480f106408440490907403080710752141d40c10302e4210310b0481107000c6845203004611924040e0302417425407194580d00003907080301c4024242c401c0e102c00001604c10700b04444084500c01002d24103038041d0401450710f680200414001420001011080c40c05a00c2c03c03038020741c0000c1d9030380e9034070040c1000354503040910200e42480e00c00158948031403580e03100c086000621031103000e420300406a4505a07509800d0b10b40c800c4000d0710b403038a5103c09042110 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 610326798 1250 610325548 610325563
    0x601090905010311240910031b0903110a0503120a02011b020d0f050306010c060e071a07020f060c070923160806040e0a031206080610060206060406050a0b0304020310020a02 76
    0x43c8103035030700300b0320210300c8205c2c2100414185030381e41010b0803c0d520005018840e68400001420107a607441d110460039020b07980b90700391412595401c5030f085e04603e014001e030900468000d01c580200e4601f007200e9500000c003c0380d154400326600d6150005040d0981c098811480c0c2d0304940d580f2135110b18100303a40007492031420744444ea10413403458000d1500f80d500f44020744540f40003480a4051202260b0190010031003010b20408440d081503030355154032921145c0460039501c506000424100b9450000c003403e01410044542c070f46060103000400741e0310460341c45000800c40d1204688488410280c0141030b4000700c1190020705460100d07091868418010f000c0c402081c00a000703d07030300d424640f082e02260324614004082c045801c2d20103a500d400c0700c6510001458a42d8000b0410803400c1c45003078000c82a9611200c1c8107810204043d0400c0300040c5828003e907e07000c402c00527aa58501003808541c1414800c1740e80303842ea030010900704650300c81448081c9000168212820342d0016509 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 610328048 1250 610326798 610326833
    0x120304033003090b131a150f03010606090e0c0f0a030203070f021f0f06170105040210080408090d0f020334081002031f0305010609060e100e06010909050103 69
    0x1003450710740040150200c035045071018010031a84400944200041e1601e00315850080c0d08613196240c4804600401c1d031401c4400d444c01c0d5030094118200780c10600500000c60350100e000784441400d284001f0300c0740003588a080724038401c4102140000c3d0340341c0111611006400c1110350f0b120200d90003d4040d500c01d0701c9607000910060344c5d00d078001d4804250012414468540c03890759080340039001c009040d00c81c020344250755583c0d40c0002c03044842e5072201c1c404d1030b61800101e058540b500402080000507246030050000c28020000042c100318200d41c410481107a500c0c190300d400d4245104165401d600c000d4240c40f950a403d04015001410701c1d0314146188580d00703e0303403007298110384407545620a480c06544102c00d08400c818060b0080c43d40030010403101c11f0350460891300e00003240c140750700070f0360665503440e014065804540a581c025042c11402196207040c441e40c00c409510407441210320521240c404034009070700c155841d40050600d100180f0055131a414200525210308031030 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 610329298 1250 610328048 610328123
    0x10903090f0512060f0603160f030c080304061e0e1309051011070f02011b06050f070507050d080415090b0105030c121b031c0f09050a1412030403 64
    0x42c80c0c500040e102c445a01088050001c90320f070041001c544590142a40368940234040040d280c0710740d5208040c004010308900003c0740361850803c0d950041c102d8200d120035810801092110300e400c07030758001498003480f400c240000c01048044070107200664400360702ca42c2c081c1c52058003407070680250b0745241c007480940e5800722900c0513081c110b500c0450000d03500c0400f4007607031000c10070a4000c00c1c006030060500740c180140d456155911410003110032a0300076a030b0300c14070555030a403400a07940007200782400e13840d04c081034880e40d42e02d514404a82d03003003291000000b01000400b45038041003d44c035800601050440b407508180c040000d000791402881824402c01552801001200408003e04003900c0003420106160440d101580c881c550035100c0c0b41c070746040c002d004e2058042da07076000356641d1350b00c007003140801414214554002c1e03200f81c41201c010301000d40c0030b14130714842140450342040802041e1408504600596001400615521041404001c1790107110a0b0112040b1403 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 610330548 1250 610329298 610329329
    0x621060e0103061e05011a0306120319030c0836070902090114090f010f03090b0412020c090705160c09020301030b041502072d0c06020321090d0c02011101090309 71
    0x102c03030f044600c24407841c500315801002d00f031141f0102000440d08100054114140356003804811495944403403034400e5000c0c2c41011692015626220388241c00700f4038940b1404609000c5192051407070f12401519a00b4020044114012007113004000c0d5200e0b140140c0304055503c2d000030000390450380d8a140032881c244030282410107414102c50100000a2810301c15144240044404600044003d000d06035640440000704415480003403080e4403500303100f9000c3c041442c0003803c0800900c0024009c00f1814144010250001c2c02e4480d484400300c0298501000384c2030000034200035901082600d48008000720511030552400361040b40034410440f17100002c404c8010481c03240301742c080d1501c5003087c6042200003000c0200e20380d08a510b031940d20039440b240c55040561303102c0d50044016900005629055581d5601014882800c1c110f44101034a0804800703915010000c0340c0104000e4800500d034110381c010440a503a40c0180d00081081285510b0081c000e500c0c0750103204141c414000 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 610331798 1250 610330548 610330601
    0x140c150406200310061110060e0115110a0b0705070215030708070207080a020913062306040b010e060f2208190302150a0609020703080f0106090621060e010306 70
    0x108980c0182081d00d00720f06664608036040316120031050f008601400794a01c05487c401c034601454010342201e000311010341d45018401c3d00b01550903011001032107480b0442405607a008500401d48581110b0079050b5692074101c1164180300c3c80c40300075800984655112555041140078600c1101075484c4d4443c80e44400c4416603a4803c41d00c501d0480c3d9002c500721360014241242c0058014514103064803000c411507480200380c9140310950380d030b0f11649582180c502c1c4900f40110303403c0403082e1401c01a00120f000001c10014400c2e0903140156400036820b85500c500c20112842d62142580d000c8203100041103d104c0e894291007000080e01c1039840d030b10021000b01d402c25002c0c5605400910394450f00d1002d61a2080009080042e481d40c2c822001482d4a0709000601c02240b0960fa21042850f00d1010f00c1c5440a041e0080301c104401d080c402d200c00e0307400034030101c0604c40b4881e209802240c1c00303a126001e441035421558025507400d0000080101942012302c008442205100c41d40d803c80 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 610333048 1250 610331798 610331861
    0xa020a0b060609030d0e0307090f05060f04200714030c0706020f060106050d05040204060b18093603041a0d140705040b0912011d060106080403140c150406 68
    0x1c0640d503034503030031241c585011540185840d031b0401d9800b03003d642c04a555021024102d9894500c02c100007070310b0b4410000180381ca40c586518111003118200001c4420b08054074105400404a2015480000d09a0103100010b0f1607202240000c0341200d41e01c00703502c4103540d02c0e00d03118807030311015102d143c00d000c1c60010b000c100503068980c1503407501e00301843d514550001e464050020b9030090380d124000304509107194000c111808500f00d24550503886031049c0801e07500000c10424100950928810050400704910020206181e0640c1603480c002295075040d440745600800200024268001e44180d542c409002c106004600c01c0021942548103156040021184103001800800003408107084010140400f400f0241964001c40311000c1d540d400c588041ea040ca007508a2a0301c14410030000300001d501403c3c0c18a41943c450800b6903000c0e28244617100b59104401c001b00d4911500d000c200f000070700444054028035604d040c1414420010304200001480440c2d081104030060441d0 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 610334298 1250 610333048 610333057
    0x50904020c0a2603071d0901060806130e061f0803120613020a081b040e011205010e160506030a0b0d030f03050603280c0f0306021201060905091302150a020a0b0606 72
    0x1403c59a51450b03883c0d40086a00244075210507040850500c00b211080c2c82d480801c601801141e1129844c0307040c10b20810031a00c08034460490f0450900341e8140407504c02103a8183c20850316070340d0161480c0411000c0303400c1c1c0b10741d4201503443c0c4004540000706280d890829030045a041e18814140f100030910310050307108240780c01000c90f440c800422075200009031841c40101e118880282042c0d111414887c030b0380800e0b40110341e00c14202c90030a05010003072051603154120003005050001d41c10000f195105014481c03903103e80800310022f10b10030140d401011004000030441740e24034542e864082d20902e0b080e258540040c0ca0480022001d007400101c901500e868040e800b0004019804101180245110f0842e0702d035030480000151919200f0540018510907000580c0743e00d000000c801040030141d015104009040c0d03010402512001500c617000b40c1c551041003000483c0c1d0001c02c51501414003480306244002580318203490740800c0703043d40e092083c100810261211001c01005004 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 610335548 1250 610334298 610334363
    0x619030917090f0904140703050a0506060402120f04060b041e0531020a0306050103080304030230070606150e040501080304030218070207080607081e0702070b0703050904020c0a 78
    0x38950f0220014a4070041080c0d129124641910040103040480f9050141d664021526607003c6049001008401e03c01c03d80c3c004000e480c11800c0074241404561003240c007505240360b03202404c0105082c032070070b03400c501840319001c2c00c2071189a50403080710403a1503850461840c1c840c0340c1000306030901480c00c1c1100306030041c4081c002c803400c03e140c0c2c1020418104041242e01c6100003100000180881c0102c03030003580104000b544a00e000d04021b801c1007440c8440c00541e101c000300382c0950042c205007061038005450001c80d1200500c2ca0b000c80200865040008510700c00011101c0d5203a000342e0700400c003001078806010076683c541c0c0b055501e004a0200960002c1040100c01e145012810002d511881c43e10407500000c1e41c1e0b02109041107410b40760040010b02d54001c2001490002c902c0d400c280d0140c40514916141c007840c000d4840a080c0a14a0704510004401041c140b280c801d951030160001c000710340d030b840b00858180e55484090340882d000c41c021100080f400400070008031888a = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 610336798 1250 610335548 610335559
    0x6010c0c14060705070e1b09030601060c0326100603060b0f0f13080a020a06020c010906030e0c09090a0201020705010203120402130204080316050f030406120b061903091709 76
    0x1030901c81451501c150444000d07410400a010507000f18800308602001031041c00c52850980c10500001e1426072164401000894000c100c0030f00e072601d0004030141118140e107881c01c0e4071401443c04944440540d507a039056090301850008494088004040c000c3c10030354000d03c030b45a45d46a040e000d171483c6101e062343e0348100b07110311801000c3c070340000c0c05c24040d0310210301c1c0b4200288107044529606600440203e0703000303007910307011810012240030180c40c140c0001c010400700074000070031114040c01000101622002d4035106110100320881383c11800811124041c0740c11107945540340c1803030170181d005120340360300000c80d94008411142e801820038440c80056230b40da024420500c0c03640080500c042c3d0b01b0000020440e20600142441c04e940b200340120760707005070074064540704a4000d0618150020042000f4040e000340c510380c0201c4420701c0124445030050009034803402501c071100c5000c15106501c00456a165010844842c895548981c0c0b2030441c120300743c1503010f09007d298008 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 610338048 1250 610336798 610336823
    0x705030d0e130615120609020702030c010e031603110901142b02060a030e010b03010c0c020906040624020706081b031302060c0717010c0c030c110306010e0f06010c 72
    0x1030030020042d182541d0740b00b001080d82d96940307a490b411490311480c00c0c400110003102071581c080f924040d000080c018485c0950408505400194940002d42e001e54144004034203801643d4a0a20100f055409221a42d005080d903900384045020a184000c0384200806000411140a4000400705246c0064014000350318074400c59549004040c11036101102c08440138001030303035082c0081501c550940e402064400403400c42d20b094507051041076200b40d0606815648a40d40103090f41d04840d01180c42c0007007915440f012500400307003504001a030450502c174004020111201340041a01a9403c46080e56a185412188050301340c2d400c00032600241070710074408411030059900b1182d06a066051078026600107010ba90028401c1c0409070004801000303d0f02c01c4662036035041100c1402400420000740009021881502d001414044181d051600303004200c40c1940d02c2031790103021202c81c0c2d6101c1d2100010030310100c03450000c40500c5c1002501651240c2d20048160340c0c40076011151 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 610339298 1250 610338048 610338077
    0x10b09091f0f02030c071101020708060703241d0a0501060e0d080c01060807050a210b130b090c09090f0601060302090f1305010305060c07050607050d020706020c010e0705030d 77
    0x1e5405110460040c1c50715240340c00c40c80420380c4019402683e640d0425580ca6006207004c140701e00401446d10f05540088408220041002c0313441c0d603118000b03243c005010603c030640440e040241c84403056440d214400045180e1001400e0a030b500c1d00121070345149640ca6000c0902516000d0040d84001a10307031940103414140345042085081c4180c04250421180004280c212070040d840002d80c0d510102c0100700c281410110b400240c000300c0c11140c0010584801e00010701c00c0760300018607202840700080d1220300880d00c4200f980da48800043d11608020304066039501014613072034802e504010104034021000a604c5403030065281c05014982e00c0d040080c0c00940214001c150070066103941006d0710b5039105c542080340c00301004001415415400c18a18142c401070500341001c0782040b07404045000000c035182e20020514056948809080b05440a40994903005190700d00104400b407040703006402c8402103ca91000320b548495543d4101a0b81e100d980c2c070300c000030900350b058840343c = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 610340548 1250 610339298 610339333
    0x20a02060d0f1b11030a0e06162a21030807030e0d080f01050d0503071407050d0609050606060f04060e03150f07091505040506070c050603070c0203010b0909 69
    0x414450000010a07074034280301201910424092015030708403011441190b44e0b0024440d0081081050045050002003800036020780c2291502034812000800e9050414100a07021140664045d052500351001d031a010903402120341c000040c00c0c22603100100c1d00c0703482801c0308020501038210070050021503850648450f480a00104100350300d48800c0548054200084a500c000032ba40300c0e41985805600c0310528601a0007491051245143c2036011490000075164a950822104402c0f0b520424506142c048254005a0091024030210040c0409540000115402001500c03107540d103100c00c0054910030200e03013032400c00b42880103000341c5124196107155801d0180803214030300481c82030030740c40020496022401120f48000c110303803251301581e8280100380c40302c110917001e980f0300c5028126000d94042d940c094180414a101404501680100241b6010b00083d80c0c030b041c422002000e507401414181c0c042d6080c0244c0b04d1079401d00200300ca11030b00625000c0d2980200107403082c071 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 610341798 1250 610340548 610340557
    0x31509020d060b041e0515042304090c0503240c07030203040302090f07170907060516141b15030412140408160803031603020a140c06070915020a0206 66
    0x7a026600d07107001c501001090010300203817501d8000104032a8100f03034035808600c8160001c40c012403c8140440c503803214041614155503401500e00000d40c035801c2c08840048206190036405401e2040c840f092105915561003540d03800d80031380d81c0a0b40407549500304085c1c00b41101000380080c034000b40c2c2601041e00030f44441d52080c07043d01d1a1540e290009000580180c460200d020121003d0081494205a05218a62104207031020500e0308001450b03e40c4060311500c8240040042e62020350401d055441a010351700c00746200034400d00c01481643c0c2c11341b80340f812104940032000092180390403200c1d01500304101e9440d030b14554890761a46c000e003103695045424402520042800e500e18940544003400780b0000600c082c008504e1032200c444a036500c2010b950b00100280309220314059140c5403006614240581c0e07500700303014201c41e14000c89202003604d080100b04110448400318450740908a20703590483c609440c0c0700040708e135240804d00540541c0c0a04110001410b0000140 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 610343048 1250 610341798 610341817
    0x10e1203070b0a0506031603170a030605030f1606021f2d0e0c100e010e010e0d05150105060c0d030c0c0606060c200109060c02041b02071503150902 65
    0x407410305000c1e903540c07107181c102911040700580e1104100302040c18108140320102c0701c1100e90510301131a588135107248440102076100140d2000400c0000c0c1d50003030300198004c00f0045c0840305480110750710a5100c00b4508200d10b03510050010000e1424400650b020151520b260300c481c4401c000384160740103004081080e100e071090004841242030044c02c0ba440f010701e803c54041031404080c7e00c82ca0810421440107842038002ea404088129803010200388045c4c000e00b021740340e42d01800d0040ea00140c1123070106030700125800040b0100003010038004010204058145103591b20f400400c407040c000e110400c00ea992103986040d50591198120195651541c20460200600f6495207000d44015070420808a20388490040400104510350f920700c0c008000c0254a80c51480002080300800d40b00340d1081017114040841550340b503a0100d901219014050b680d0421030940117034480a5602c20500c601c03440d44c100006040c000d02031107405c20b8200203060b040505218040d00217421100c0503 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 610344298 1250 610343048 610343053
    0x1b060512100e0112060507032c0f060901060302150a021f020702031c080a06081b0f030a320705041109030a05010f0f060506251209031a06010e12 64
    0x51107082c003140c2501030080b200140c202000d8508100c010303140040c059000301441d004a815105843c80e00c81914101c01007107629040c0400320341c49103024003625400c0d50b5402000e046c8200d02c07805600c044100e07482074880340031010b584010940e8601802c800c01025030801c1051800030700c035100e4552040a403141d001405d203211070700442e1030301c1c3c07a0b4014082d654490101030944160882c0c451036202001202c00e0051501384032405850f043c070003000c1c02107244410791810140e9100c420350001140302400b00c0c0c1c2a03030300904028100f0405d000000c0da02c0e0764000d4a403c0400809200040800112002031a82c0b6160106120081019503015048510f0510422805075410b00580140f240244008588a10080c4601040702e00c180e00c04060b20346802030821040e00c030402500c02e000c0c00c5c1d060b48061010600001004188400f000400c504510704200c01080e40040c401d50070340703001c2e0040924550740c000a00388018015543d10380802c50320b180c94109171a14801c48820000e28105 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 610345548 1250 610344298 610344331
    0x4060e0a0c060f08011203020c091306090606030b0105101b021804050f0105180709090303110a0206190c08131704090b040c17010e0a020702060c0a1b060512 69
    0x707070004840000e81200d00001c1da440c0c000c00c6010b52025409016203940910844103182540d8065034075103414440d540521141303000145080c3c08500520710282d000b50091081c56410301e8100020f098a00044030300450000000c551428000e01c0e0309903180310750f140c2c0322003582c10402214541102000072a0b2040c15210900421188460800c0c0118801e01c002c00c0f0021031401d0322429107000800001030341d41900041c0d800120009920740403204208800a405009070900318003404a294121034040400034a6144c41540054090300c07c03a804c003420354131740d07a841500300192229000a400054070308070101d001d04c001c1d98103210406104451400c4144c00c407105803001c5801030340c003000d45a903640040d0131090616002d41a48011540b03801d1213000c18071243d24048500600910114201610001e42503054550455403080d400810709900c1d001c0c817401107903440c40011b00c100c030b40c110000d5441d00e034141c5d14070b040c005407407640d141c40303007440c0c90240c00d41c048180040c00c4840c0c80316200c5 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 610346798 1250 610345548 610345553
    0xc0f010c08130204021903050a0608031306030506040b030106030309030302060a1803050a1808160b04031a091f02210609060d03022a100f0801050d050f01060b030a150e04060e0a 78
    0x1041b0015056807503d010a0508d08401c09004070b83d4107a0001409e03800070440710b04c0c080d0072240d40c032040e01c066080000d265100c3d200410020001c0441e1940c0561801c4008801c6c103030024040d4007144d1081c0e0071241140c2e99428040c090340c0a03d07807050780b0341c0c840c400700800007030148000d04003180061070a00d946181d6600c04200301140381d84446201c4c0c002002400c4100005080341c4058040100114030706880c6554109110f001c221495400c80c0030000851081c000c288141050300c4540c019500d1403414250440d80294881122444242c008101d130403111400b41d100c251144a000b00320220f00d68490f810b20003825840e4004400714000c020303845100c07001b03016030521000914400e13400c41044420902010402d88960b080600c4801c1108504041c2d01515850542d44155003014801d8010710300701e0320300812203002c240f255007002008110480c04e81c002d0340c171406000c0c805002c0c04480521a01e00c1c04128080c85865495800014000c180103411080740210f1520403514481d5958 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 610348048 1250 610346798 610346827
    0x1608070f0209011e091406040513120f0905011b021507080d062d030f081c09110105040308040311061c020a0201060509130609080d0f020c0f010c0813020402 69
    0x240c10450425021455a9904c16008030072500a000108410010326070901720a01c54100c00615a600c255102c4002646080304000e4000300c4603400440e02d24070b11020700b4040c03c51180c8081e00800603516110000f07166105010007410181800500c6131141c84c01c1d024442c0d03035840d116424480c960200040b030009940e04006001a080b00751000400b2420007041c0c40c080b0750300142d40180c54005000710310321500c600d5031f11800c072580918080e05201e890314258060740100e2030418802843c007091902c1d1344500340c005021843c4540702840300c000c4914010b48083c040c40c0400b4010080502040c0001981204003032250ba100400d01400d04000c112a6444403d00c003440340d100c0b0740c000c80c10031180c60302401508007400085901301c205192888150b40c120302000400f0348500c3c1c83d24008418407500038101c400358070303401070244070000344000c4140281d0b00504c0c980e0482d120714082c6103110b00e0706104480c00144140c3c0c540c807950303e520310480ba0150b05100e09a81c00350342008a0550009007 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 610349298 1250 610348048 610348051
    0x5060616330506040b04020c100b1507060902031c0e01050c0111160b01080c091f0906060513090c1407110301060e160c0b06060a020a02030601090e060702031608070f0209 75
    0x144030100b11480c068042c082517880d40075003c1d02560040c000605104001b240c0203854246d1071000040401240000030380e03038003400300302d542d519900040742400c0c040c2d1a000725646038025012655400000754103100b00e540b1094001c0000f5a072000759500c030b036114500030461111a04004980d01c20110340c6007540b070f844403070b5502c80002b40c43e0b803410030410f0010704203006044400c0500001a0207074042103041400920780584400150b00304514031502d8041000600282d01d0104000f903110b20028100f40d1107405081c1030f4288030a00040c19404500403000c03400924ad940131896084102020700a4022090403501084030805050598070f0900c40c82c2c0040150198412082c20b001c0d225012100307142050108200301e00c1c4210001c1900840740c2030b000042a15107035591080403004904051450000961502902d07000250300c4007660022980b501e424400e8032007903141c1e030780705036a40d1081061111400103d00701c8400840c00700f03405014014090b60017813007090515400074924840 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 610350548 1250 610349298 610349393
    0x20301050115110328051201290702030703020f01091d070914010923090f07171504020a030f020a0c050609010204030305040314010902060c010501050405060616 71
    0x1559104081900e9014240030000c3d90264003452910421054020600d0031036000c035000080095540c181243c030490469450003d801d090340f013556140d0b43d0341c043c10680019070050f900140f00e22285e400c242c080803505081da008008140b803c0c510340c2030000c0f1041c7c074046d2506000c96041d00240181d00701c900350403240e441060340c5646140034007000d03107111169003200340d0301102d1540e05c21081e40c12058010548507000d5890820b074019210705d10070791900e58400d5030000b82c500107022445403e045450301034003282d1141c0d0b090414140340b03030207144000c48076401861481038840c00941403a500a0400c2c0c0481e203008121258129880c6051b64410300a00300040c0c030505480d41480700c1030140507001b144501c000c1d40351928549004060303004900004c0c1615008502a04502800350b0102c08d500f40c1c00307132803282c13100345d280280c0380200713401d128950260381004005106443c0c44009c0719291a4040c605460060180c3c0f5110078400c1001c0c000c50b00181980210413824924030003c614800 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 610351798 1250 610350548 610350569
    0x1e0f130905060703060803030a051803040902070c050612162c041a0f0609040204081609050a1b0c03030902060c030c16030f0f0501020717070209130503040501110a0203010501 77
    0x20031403500600d0b0080c0201154201441c01405016029000c01203e0700901f0f840c002007180c4c0c80d038026000080031001d610901c0362100060008a104140d00502001800740300ca105441350340d5002d01040344610300e202901d00013048000303001c03810f1400c40300d0159505071034007040d1215042c003010592001c259141040c01c2d130120340d05d091460280103e0011410055040342c070b058101c3e0101c1c40e0043c2d481c82e014855000403c8500310340d2940d50558004209c030304100d80b02d00344241c088090f80f013800d000d2181100c0c02d01c03000800c429042c0c02030301420241d5680c1040008920203088030024a002401c400301902c1d0031220000d617032100060441c0902d0403010b15038807140d5070748191030040340080700c121181c03d0042c10000b140c1191403202c070072508400c2c945c60829075450400e00900c42c090000b401005070703907410411507086401505059100b0b61704040380d516000500e4110348070030030005000d03600c200300600140d4860300d4042040c60880e000c80d18010040d80c0040c1c00e403071098000390540d5 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 610353048 1250 610351798 610351811
    0xf060c0c030213020d24060c081c0902010f03090803010e060d14010c11070b0301060f050f210a150504020f040503190606320f030f0c090c091e0f13 65
    0x4072913901c6001b030010901644020141080d0f1401035689034644101030030700c0000145042407045020840381280000b0348685090641142408024540b83e0810307070006010703a0403000d03002d0013803082108031500002900e0850f03107050b800003005840207200540008640380880300003080c8030701940e8a880500e00101c1e040281d9400204a50300b5040d513040f240e0b1047c0b00030031003501001d04a0b410349080d40703042841c1c601c1156041d2010301c1000344001d010003000502400540c900c180d00c8406050310000581d07035850380c4044100381c882003c0505800034482c1410400c81c901030b4024620b0390300c00043d06d810300d981d134400241084207540460314010b0b1508400d00402c10306108001c0a401220304400d0210320010748545064101400c0c5040708060a4103544a640c640c021a804800001c0454480840c00038006440e11590f400160241e4242c0e000304910030260002e0f522581409016404c00440e00185403800b6141414100d0b04038803402030b0220152126032000143c0c90f182800030a41 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 610354298 1250 610353048 610353067
    0x3020a06050916140105091203091816120623040f05040305190c0b1602060609010503150a180516080307020f0120010614010212040f060c0c03021302 66
    0x990750700400c01800d6401110214000b44903490159040ea900300348110601c030640c00040c1da03148501110f10380d203c0b129111451a58200200428540ca0282c842a0141ca003404c0410701800b0140c1c3c11042c031181c80300000303031002d20541e102154a01c807071038003281d91940c1d40c902513511000440f01c0302d011403600c1450402070601c1d00030f488581030f000100300301c01d10b0983c40c004c01902800c40c034080c900c0c6150100b015010300c1880405c4c07441c0d400400003c0c485c00c0c84101d80c5400840000180301600030400020018506808070504a4001901910020000c900c440740c120a0052011252903030300c10185ca1803204403460040201e01c90002002c100c91540211740c0401c02580c001581e07540300700035040050700d4115101e242a00b00307003050342a603a1034440030030040401191980181d03280c213000141505840c04402d0402e4800c0c0c007a10b80c00c2c41009511006407003180600c50100c4c21600d8200b146c14030603080301c01114090310341d846005480780d0010340094101d02540a040c0e4020420001c03 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 610355548 1250 610354298 610354301
    0x12020a0b01060f0914090408131a03040506060f370f030c0905010612050a0f110d110f03041b08010906020409060e0402031c020c032a010203360d03020a06 68
    0x85c01c110804501201e51100010358030b0b101c014070003407044501107580750b21704040c40c0300e5034040e0040c034406404440c00d6114541c0140c1007220282c4e075610803000450218142084d000488000140c007440c2d07100c4410140008100000d54003491666004200c10629055282c052019040d10124031040e246142005000306d012504100c080781d142000402c000b68000d10780350003d03455100003103034590b1241b0300f20000300604041401d0084c18110500441091400103200c1800022410001d85146003118203450090545000d0004d004202140104d850716070241c109004400e040f4000c1b40d11140303100e09460340e1210480d8010340205080c040f041d401e00031813000d40780c0d0b1081484645025000282d90b10082100141c000710700c20b4032250b21901c2404006031862f0081c0844440c9001c140010541c0816100d0207070750708140d2481408550700c003100319103604420030200c412201a10140400224156820f600c0032030302401e4550071038613207001d0740c0c1486d80281c016261014540c2410170 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 610356798 1250 610355548 610355567
    0x6060b0a0507020d140109150e01090302030d05060a051906030f0c020d0309060b040e0a0203012409050c1605030c0709110706050408070209010f1508040c0312020a0b01060f 76
    0x10900000d00010241a51110958040b190100c80340301c0000d4130380c100241c108611039910b0055508080c03000c0144007807441680c0e80080c3c0107000b04803000700e14012500f01c421400c8000d0050304204020b003500c000c02e40059403c244003d000c4440e503a45d9400190f5103640e240380d50b10400102c030301c003004003a400d80b147c0c15407011510300c00e001c21450000001d48a440c07040901084c140e4610b03c1c401480b4580d0300190280101404c100805548000c00550303c0c42e840d64124440c0d030030110207010487c5056540140701c040c40c620040b90f24142021030016090040030030103050310900c414802084034880c00c8010720b0242016680d104090034442d42001850b4208042090501d095070186c0507128007100d04054000000117a2a1200d1a00d54401d02c03841d00040e50100c0d8140011a0b900d00c001c9006007110a01c08001521000410040da1604030440707000d040c1c1414100704201290601c0c0a0108440c25841522041581d40c0d480950303218080c0c100a001803140314803022015044030050 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 610358048 1250 610356798 610356809
    0xf09060412060c021506010305091c02070f09021608030c0c1207050d14030c0d29092503181a15061c090203190605041a061f0509090907030606 63
    0x41803515403c0001c0100160094211030402d540d0342c0000781d852105015000780701d0340143c030b00c040485160000370350741c6078030b4040d80414a042007000904510070344200c4400c03180c5054a03100ca500103895036142a04002d00aa001ea081005540700c10f40702840f80c140c000c1d00004116456498900b425854058403100600a2200b0412003000314a070b04c9040d0303580a10030048541d542e03180603c041024200034440b800301c0303006c50000714880600315081d00c58905c505980881d0703280d560387d034500642c1d410000c4594440c03050030034a0200c03910a4200404680c40500103680e0088255107418540c01c3c0e10b003c889181840c101030110b0140c90b160540e007401f00842d90b1358101300e01d000001140c0c00075120241d8008d0f6481c1c2c007000864038148404d001011860002408146c03080c1003050141c4021101181e010719400141d14a030f0b51485620b41c01a100034121644c412581c1d42e00e01140050103040c10b0500c00c0c07d00468102d035448109040c072650066010307045a600c1e40c500741050b02ca15400c031 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 610359298 1250 610358048 610358053
    0x1a0f190503041104140c0c07030212010e010e0a110105070204180f0303060b0a093003110709110a080c19121119180b030109091b05030d050f09060412060c02 69
    0x5d078034800c00c0c2020030b280c114140c00a042e55a200150700c25141500d99400207402c40148803111041c940c040d813004905d034619200a01906000840e010380b42c0742d4401000303103441c2e0402a0000c031365200d80064080c052001d4000202090210244010500d60038811101d5140d8103200c40c0070558580904130040220b4201306040c0050004040d02c01500d5024181c0030b051543e0345103a0700d402454504002c0031100403041c5041d4018100140107201013003016050b031081c010000b48036511803144080c2140381e5048281000101c4008442b0840003030b210395061141440b80c0c03541c07494450840703c01d1030b0076070301c4640c1c4901052000700d0540e0b4142d2008609a04140001400501242c0c403000d8184040e10b007610059141a0110032070f81019009450a140c02100100d03c011459000b6120301b0b006000c080521041d02101503030402c2240070300c40d019003042500e0b500440c0210081c10200382d02c0c424017030070411030401044085d0400e9010100d0324180c05428400e01c80d591080300c600140d517201 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 610360548 1250 610359298 610359311
    0x109020424030602030402180906040507120b01090513021002250f050d03050c0712050f010603120507020d06050c120a0b010801031101120e071e1a0f190503041104 72
    0x1941c0304481251001405298000000404658428014000d05c403ca4a1170701040d05106442c95a6a01c04071800c40b1a885400404291403440f02904650181c2c000c0b10103034140c0c2041080c1c006404c1c00f401486012410002803801683c510301a030742035205650081c102107080100da41e1044030350720601c0c410180c02c001c007401000b56181040051750310a0320001c8803410a0f02d0f00715034611030b26502942a004406005c1100c8080d40100700900780100201c0e903401c3c0f0068615422913403244002401c807001c441291401134015405040014001026000204a030741c4400050354011611004040400204106202e9046400680042c40c0c0941005400c15080c00a05022418000903210b520000714a000c183e22600c0c14640422240a05200141c14203011541c1c0307010301c0c0150b04016031455030302171044c10400c2c028070444008007189221000f01c0340b46016141d01c0101220700c021f0302000301c40d0303455041d02c4600710600e82c5a5183c903a24a1b0a0804507845904101d03460b205c1d46c20140d = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 610361798 1250 610360548 610360601
    0x1a011103070206090109031a0f24090702120d05092a09100909231914031b070f0b1206192310080705040b07170c01090204 54
    0x42510a81035060300c40c070750f85070038420050350881b14a5100400c011703a242420301905550b0071009002c1c40e00141e014455440e0280340240f0450040c1c0c01d03146440c60801d0303d00f4940b500c00e1109401822500554618488a00c03100d5859800400c410820790348580034003050b03044c00c01c000e2840304914001d540c00f00001600e1300f0403550b1203141d440e214541035000700c0e05a2680c280720500502003028104452101441c000301c9541c403013202044c0341c1914001c5010102c02c0402d0302c0a51800b4404954501e8602c2e07039880b402140545006d626611050000c0059800513014440c035601c1000c2c000c040040c6090014150344206800004140790103000c10059188001e51103500002c040703c00f0091000c28000e036035039800295200c460311f0001070a580c3c2c40760711018010712071064207851507400c0002603241592010015a10346c0e0024404100030883c0c22041030242c00d0591007400d4850a6010110381481c4c06e42141496005076503403003128008500d018840c0940c080b48020b101c001c20901107 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 610363048 1250 610361798 610361803
    0x709290c0123070f08181e0a0605010902030114060c120c061603060b1902010b03030307030b0103050a0e030403020d03030f1d011d06060127030803160305011203301a0111 75
    0x50f00702c4600000c00406c83c001140c050050711042c2100b81038100d5824000c90641d40e0392144c0c07107002d440c828a040e0000c5440142d07802100d040c1c0d40c4c0c10300e81a0190020205001045d4080368102116005410483c0380c001c058000402e182800340c4001d0600b4140440311400c40c4202d0314842c1c040c5860310b601041149818015034440c0302d001c039aa1000f10030030780da0a07405446100d0380340387e06000000170810b540b60194008099100203030f808010725600d9000c00c000303c81c2c000e01c40d0461a8010320040005262902300e224036944240b40105d03508408000503010b4070f91700382103d410b08039003070740460a20209100c0c0e40c0d100308816490108603a443c06115880b98000b0745414104a0000d00e4640c1d80141d81c1401f203245c81c2840003500d2210341c4d030308101003103400542d034003106440001d00c1d00c5100e52090103428103881e56210400c0c2207444690f41a11121081203030400ca190280303119520f8499141080950b00c01541d502017800a050880941c0d19130400c1c41c200c3c10301240704601e20b0a40c000 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 610364298 1250 610363048 610363051
    0xb0114010e040c051207021b010207030b1303120204030b071b0b0f0615041203030c21180605070c06050601180e100e0a0902010201050709290c0123070f08 68
    0x90320300242c411210f1608880c0b520418142903010180d000500420660010740a40a0404810000200032407907004a803548858030003e0140c1c034020020403010021304000c110001d109041011029400903098000d981065009442c2d4181e420200f050b21500002c010004907018024581045903039500c074403440342d0160084030806000400030700c407520b0300007160101007a8150036503201ca42e901903c0c130031303800741d41d0084000900740091070380e40d80c0c0144210030a03418041c0d040d041c20004c010000c0005c00c10100340b0180f9000380328101012030300d184600742c01100c80780d890044e10502400e008080c1c54014200504000c451f8000c0d9801c04101209101500c524151545079078544070b0710041d030302c54181c0040810340c0284c01071001d0242c482e84841040340c401c0c0c000b8445541c502e0b02c140c07481c1d0020b00c119007010b550180e85c10352044049850111892031440030303d040c01d060314481400c641462903142d580e1126240c00d01005109020034990125207850b00d8403a4006421005020030310 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 610365548 1250 610364298 610364327
    0x2030c060709082d16140a080607030e1c03021b0303090312190c02030a1805060910020708030301090b0a05030102090d0312060513061508060303190201090602030f040b011401 77
    0x101c044c46685001c003c102c50103903800e504003103640c06240d5907034201c4024624420340c20840340c501c0d2004c0c524100400c850341100d9494014180b180e44000342500076040c00703071120715180214001c280c9800c0001c1c40303904440c00c060340c0068441321282c800d40c1c80b00b0060134908210740d206000b008483c0f08004111005c40c0c41640c60400300d501c4256060f00207a540c1044080c15506146001807070f0756001018104140d010b550700a020040b220b400004d4a59074062145c0103c01005041a681007048040c5a400801c0c4110b030003140e80c4a580604540080c2c0004040d26150a200c1c116803501c2c034a440080c0408400840c40d208030306000490080301150020700344500c048000c03003002c8840d440003004010181880b01e51501008100340103260f0b600031004202c001c6172145030800e00c5a15103a1080d440500114070304840d0b09410052682c82154520441d900c0b050300100040c2d060029600410700e4142c482c03440e0405c0d107000c8128050581041d00d620303409505501203683c0c0a840c640d0b890f030 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 610366798 1250 610365548 610365583
    0x40e1e06010f120207060509060a09030906080718060816080114010e0607050d080a0501150e012f010e1510050904170a090302011d03030d0e0f070602030c06070908 72
    0x42e001c009071060010540f601040d54804600c82c0180021600294843c68005054030b0050381e441e14204122402c680d0040c0024181c00d80c00d11000740540c1440d5040302d41401d01a062890700c0b100c1c00c0300c1c640300303802035000141580184082442d0b14031f4200340103003280c1044981c2c1c1d0f04000d4903112500f040c07038010f410004003221143e0700391109030071500d55503004001c0c0d075081928180c000e04203800070384002103110f18180c00090f212003298010841158580e448003a075000044c0111075560f6031100c0c070074048145085030030034030781440350b0041c100c482c91001040e80c801218203030342040406270011100c904100104205248600c03100026500210381c00c804c0c07600d0b0307408c044100c100c840d0480b541c190390026219030307a00e80104408027103034403d0341d4400d1040500000c0031000d01205a0050301f41d40140b020000342c03041c507000490000d6180b800c413011a03c2c508043c07031401410f40d100c24050307080081d05900300c1c84244900c13540051350b0b091081c5418034004605664010180706804400b = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 610368048 1250 610366798 610366817
    0x3090b0a15030b0f07090b04030206090f030102090d110a06020304052b06090b06041505010507060f09020d0812060103110a030e0709050a020d0e0607020312041511040e1e0601 77
    0x924101614007450304900f07002c580b464003c08503042c04500b51503050200e10000d400007010104401124140d03503002c3d0542d400c00542c40240203501c881c06103080c0d4155002e000e1000143c540c014070304c1d0024000c148040e0b01c541000107200c4014402d030820703000c5410800044c80141c4555141040c50200482d17840300e04400300c5a0b081c0c800359444401010a41403e120b0340500c8a04030026000d03c030102c1e000c00804000e44030407050403d107885028007080c0309004100c04200540e1209850030318540c0d0104d0b40d0030555000902c0300940d034070700303d900d410003160020111a00c0703000303980d00917400c0c2010403150141c1c1c54074160358002d02d0f1400302099110030441128000c103003ca00c0092032241744c1400b07581010785080b03000c0d4024508240805183c201d00440341d920000c0c00c2c1d030044c03803260040d42c9001ca1043d20440d4000c00200203032880d150990106816540b14800c3c1d075a658025003070706441d1070504a0f4000d6442002d0304540751940c0320b120815003000240c4030250065024240312012 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 610369298 1250 610368048 610368071
    0x7050a12080c070f15080103030f031503020901080d1b0201020a0f060f0e07090b06120a0c05070b1501080c033102030307060204030b0c0c1209040b100c030f03090b0a 73
    0x10700c03880302d4411240c0100b440004001c110340360950141c0d0707800b418103880080041002c6812400034440038001508080594a225009074095081842c00c020403400b000e460f0740220b4400d000130390003225a94004200c003c43c00e40d02c40740401003200403240b0307154164580c2d00000e42d0740741c850f14090000801c6d1104e006c10400141d105e40b2004060b013409101282450143c691166114440c0c51925802d15a00150603c0c00b1400c07207560011a02103101c003034960358041707002002c1042c044d501f407040c1004801d0200b0242c54040f40720381140f18602050400703650005104e00c1c00600107603215007040c403d001d5280c001181c0010582c80c0d0f14200c1206001550554a28150445010350507001c001414801d01505800074002e480c015006c21000f61654420400c107442490b0a04525802a51000740068030303000040642070b000410102d56180d0101c009061040b60241001c040707104c030240141003540003200c00c0e68441580c281000780922a841e07410a0280040410002d0f643d01c03241e8062 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 610370548 1250 610369298 610369313
    0x3011503050a06091b020f01020f071104020c0a2a08030901030c020c060f0c0c0603100308031003020915010314070e0d02120a0302060f150a03060b010306090e07140307050a12 77
    0x5000c4100705005c1c81c4a800710044504260310440c400500504c01e1400700381e132050080341c1c110160550b005190140586602990310603444956911680030018984100b4080248484050280c440c3e0104c0c106040d0b401c00c0306070782d600388081c1c0c20042c40030200800200402900c012041c00e09001c0340b0500840003c0341040030300404c2d668081c42c0851001c0070014460050102d00c18140700301c030b06080e141c508122003400b08840c4d061503244048802d10001d00340e480a15080207440c181039001603180e50002d2210741c1e00302c48540e5801041c086c048140d40c0d15000c0d141031044440c04040c5581007070000202514072a009680c040c0c214445481c04544500c4040301d8100780070030590b1412905c03490020348500080d5a074001c440c91800100e08440c1708a0101d5030220001090039614500c0d59550300003034590101c845041c1030380d030100012290540e0103441d000c490624050315010b800c06580007206500758101a0190340003010500c00e6899080000c0140c1c2c000e04201c0035064190314003541c = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 610371798 1250 610370548 610370561
    0x1f1806051806070f020c032806022503170c0f071a0a050105011d0d060e1e010e2107141903020106030209011508060f190806011a03011503050a 63
    0x9041e480b5140800101d07981c4105015003480281e820398058480c00303410190784146010003070018144c0d803041c210304107000407810000da512501025003003c0c440d100e400b450500158000000b0005640b580080650000303441604415561510304103040009150501d800303820500c0025030000945901808002c0407150007101d6110300d4201c1034500000000061300082c4075443c08070781028000500195a104071307910490002e82210030300300c0203032603074405484000766801c842d024000b40301d1100d07445084100010305080c000443c2042070303403400900e405d0800c440c1508403007444151800107203191003100c1d0915000460021900707854220207062020101030640c40d50340a410000402d5019007041b0101ea0084564100d01d80e84c0e018500e000480704521540081d4468001991901d0446880284840040c02880d01d61542010306900496540c10810301548184d00420803040c100c03103140001440a0109421941341001204000c110f64601c00305164a540c000b42c5440807036840712 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 610373048 1250 610371798 610371841
    0x81501091e0504060204090b09041101200307030801170d05070f0201140c071d060603061504090e061008010c0813111f02011103010f030320030c1f180605 68
    0x1000b241c242864144020741c090300c500610310b4103144800f400c9117420340c2e10310321940d040402d1061074240100111140183c200148001c402c0b014558420b001c8100043c2c01014403980301d11a00f9414003060307948925194010f83c06c0c69100c69070a86030103030302c4802d4450b40c640c058103000046070300d4801a903180c501d004a212031040080b40170f0000b400c0000e400c4045030403012502d81d0107007514550110310042101c00300d03080305082010030b905050071202030311021107461740a81806c0d2244e0000059034003001e40480194003040501c842c288060300d40030300070800072008010448203100e0181400c2d80081003d56000c2003810302c0400c0c0214208440d4408c0c4004010381030380781258820f80101a19000f0100040d131030b00c00162505141c0030102c0b41a1040d001c0880c5d001c5146076012910380c070503403c1c142c0c1c000d856000071580b60a020000b6240c0101a40c0240007400b10324012a40b204407035400d004010742c108120361b402c016071244100d05141d080880480c895a89011080c010000c00300c09 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 610374298 1250 610373048 610373051
    0x150408040e1009052d0a1b02030a0216050d03050a0201180803090d1d04020f0f130510030623010c020a0608100803030f0c130e010b090a081501091e 65
    0x2c00554000b6070541005950480c8401c00050f240e82d5468111030480b0102d12100503001014600d21703064000c55164031108071503010403d6103251322500c100003c3c9a501402691011031460421038042c0080380302e012100204000c0c1c1b1f464600001c680810b201809018401c00040206000d0304c00c1d0860b4075052401208845490071900c3d1203129030b40215200c440c0e43c041e010884011790301c03e04001000d0035400d102e041241109c402004000e600942aa20320540100310380300503040d104016148800e11080b001d00c0b03c80c680820301c102400301013905001c05180080522048000036101036075810400303009045034403d9001a64001d42854020394402c01c903008c0052040c0e480305440c2e21a8203002c441080c1c0d03070355480296a45c2c2c04141c42780d2041034038010001c0d804188050140c07018103c0c0410031105103035205083d10a10400303803c11700d040403000802c4121410b000404070000e28810008010403e007405101d00c03071140600400903450307125208680344018140c0314401000c00741d0390 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 610375548 1250 610374298 610374301
    0x1b0f070602030a17060d1401090b01030b01050f0d0b07080c07150b010318050c0f04060b030106090303030c0504150c02121002090f030d09060528020d020c0a08150408040e 75
    0xa020355607420030208400040d00c00c0082c4006001130300b0001d03014450141042c0c1150000b40d44000000c0c00d01c81d1400300030341d078458000020540704002c00e802140182402c40b00380d4100320620030308140b030b1042e441c01405c803184000000755000103502e620800c1840d10001ca0b8580b0740c0e00341410710500001500c6020320131950640d4200e0f0742c1c4460088842601c4c2040041000e1030020318071007080001500542180440c210541800034021500d0a4000c00000e0174a840c0c242401e1181c01c2a00808009421030005004250b010320402840c8200360a0843c14a45002030002c4031a0f03801e00c5076070420540350754101c21134481300110007500c009036060340d0f4a00090030a880094011840840c41014001c01ca04c40ca030a0200e0318100c94407869480e001618100300e01922298011000302180388900390803410010060103960b40d0800307503540034080340164802d000340b400307401c4a0301c01e01c11001850100706a4400060304810541d00850701401541e950910104a0203940d2042030300c24142c40 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 610376798 1250 610375548 610375559
    0xa050d05010c020c030c030a06200f070c06050405090121020301230c31030b0109090308060301110409092a08070602010c0203180301020d1e0f020f1b0f07 68
    0x40291802c940c05034201e80542c03500342d04040e500c4901c1c030581034068102480150100d6002c0e04a4a10303000d0a4492140e8511200203e0001364003006c0c2c80c01542c0c20200f0103208001d035850042d00100700c1072400908240c01c100008000c46d8061007541120100c8030b046c603210b6440621507040312a0020020808512200038590441402070842c08920b855200010481c0c0040000d03508075680711b000790f250181c100550008110080c810b450041100304800200042614030000d01800c00301501285031421840d01410031034015065174826418003008400c03900a5030281c1d02183c0c010240840c40c030040d070a0805203040c0146111064003802d01c509028000110003220854412070308442c1c00c580e070350300c0c01c0382224801d60360f0200580080005440078007138644d00420012004000500e005d401c10010400c5900c4d5600c20400c003d10744c00899075005171740c4074a41d109120340809510307142580d0b031003010910411004003c01c10008601c02c42c9400304110180f600d007690421a2603064640 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 610378048 1250 610376798 610376801
    0x203091e010e01061a041e0e090c0f0f0d03051e040b0c12130b090105211f03030206010504050a090812060307090606083d0e0a0507050304110a050d0501 67
    0x803110b080030b82d800e207640000d80c44004400f080515003a4000301c4c1c201401d02e4850a0481003a811140075800ca4010104807000d99854050149441d40d008103001c1d031240e81031202d90034640c01d500780b04800300e240885090311403540301c540d8154585011940d8580500722015000d01e100d140540c1c0d18800320700892a50420740040004010700d00c204d900754820034901071114071130780540840702c42005008001c0000700c00c0143c1210340050400d41d042c0f1012602c0b448103512100110300d000c00c0c040d0306001e600482c41941a0700340c203940e814a171a035408d64501035510075041c4101401681d8440020f030300300b40580e11a400065000302c59994030f10010704942082c003000c2c0c0c0c03154828001c07400c00041029003441010104d13108c5880f025219a2811244c1001c04484a1499640c0a45c0346450b840d241e4200c00741e048004005901080241c2045e62187c4141001801e015442d0b2912061264858006050b00c1d4041d51240c204074036001c0c080c000c10001485580120b0304926180040c40400006 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 610379298 1250 610378048 610378061
    0x901021e03100b090303040b0d020f0a170108061b0d1b020d080a020a0f0e0a05100c14160b0a120f0504022e030902031e01060e0c0f0d0203091e01 64
    0x642d42c1d200da46464443c0c24520a60b200668145c0c0100001c00c40c000010015043d03410381030300018104881c800c26920282d0115038114001507001c3c0c140700e514485440118050400c03c40106403034a000f260ba101700140c44a800c83c0204d13004104000380545c0794220b0206090403a9041c01000d2948030301969650482c0342d0007001c10070100c0040c1401c00e6501c2500c180f0b421507940c4000031107490000741d41c403010302d0301603a070810381600010840361034070030103000108074a56941d42d40149508061601200860180c000740d0000c1d03100f40e194118070703042003080d1a0543c1107950b17030303d0b1400c034207442201f41c411b0801000c50034250040303542d100a07408280306d28000e54400403032038080e145031104a070600f482c01f03003250a038903104454540303c2c1e44051101440582190310340104059074000c04007007004029000da4551100b4020ba00f440c80030301e40c01044421100341889103440d0801e23920b01440c1346100e882c503030100000780d10394020081506152003014021442580f211103580c040c005 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 610380548 1250 610379298 610379311
    0xa1a1203120903090901050108040609050f030d0b1e060f12011203090801020a080a180f0807030207050108070503040b040c0504051f05030c011e0c02030d030203012306030f0901021e03 81
    0x8050300091040d4101000b11130040000402c1e4003026800d010040d14007940140050310038a54441d003580011f0010404041c4442e6440011619400301030074203010340d40b00102c0b8a002d8070308041c659180300460602c5401480741280d1040d25103405221200700c03030203051080030f5030343c203c3d0000150303005e002038005041601070364468003110b4031003221900340c2c4074400d4014002455103000070322102c42a8030400140454501c1050b071039810361280b49000f00d518100380e0300c89000044400c109601001984000c24003828082150314041b200a0094000240090072030200700000408019030811024003030413000b0020402414580140007503d00d5243c0d90030700e40d1801c040d01150078a80080e0450255005956444092410301241514440205800018410481260320060f6014840d2140c88030b02035800685a6240c10450640c0000c0c91a20200d0710a9440011780030ba10f512049070b902c8560741c400c0c20004d4541114650080c070074a100300381807503c00c01582c001c661000c80107501925 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 610381798 1250 610380548 610380577
    0x6131a12310c050310050c160c0b0705071e0303090306020307090f0b1209070f0603091e08120c0906030f100308030c0a02060f01140d0804180902040c0c020303030a1a1203 75
    0x8849003011803c40d40305452000c03010f84240003580c81c1c041c403202c5811902740b040201e46c00480d520140b00c0302d82d401c2100221031940113480180311428200445580460791404001d00a500e56140500300a041c1e01024002a800100151240d800b9050040041c0641900e400d6111350721740c07c0c050f19030040d1009001c4e0106106c0800c0282c100010b014094a140f0901a1a4140791a60580c001d04000301c0481c1c0c1c000101d4a081c600500d112a005850350045030300544c3c40b604100d00010702d10b4000c001c43c12114044c028000c0351f0300c4803416203078001e02d000080345d0141c907032202d1041480d03820352009254800000800c803480001002a20710260306800715403054448001d852541d220034040c00c031a285545808048900c0c280c0e041400306030095500c5440c1c1502c41d00c0c1842d42d1014000001039550b00c0f2418032045041270b1180020014462501c403803001081c1d40040c2d100d20006d003040c02e40b141c80741113000d90440016810740d020b4800414803a54250144c1600380c0b25084a0388088484 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 610383048 1250 610381798 610381813
    0x801090f0c020607120603082803060e06060705010b12010b0406050108090a081e07060b1005090904120306240e090106050d0507050906131a12310c0503 67
    0x1514007491a401c401c035005000260764100c1c045508a03500c040c1d0201c1c0c1511904000080b50210f001044003240180c2d2027600e04a07008090140601d00c400038600b01031805c402040a02402d94005811010031a920f0b0781e201d241c4d003400c501502d1010941544890784070115400b01d035055128100c138800aa90500070f40c2d0340c61006450040307040303608003001e4110901900005130070a00501c46880700c0900d00d0164191000c0d2060213030020031017103030b0403503031035000142914185128140b00c054a141092400040c0320218040c2d01e006000105504052039840043c28000d400030720103028a0513000308140d10389050b030a5000c0710140d6040200d981c1e240408400d040090a541c169221510303940d02d4615841d40b80c0c0010000141031074100001030040e0083c980e074020050800380c000c454124002030401003220001c4c041402d1880c4280d03400c000751020300100810240d03000903441c04140500107500e18500700c08a0484509030783d02c201e940560100948120b40344c00391801682250b840 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 610384298 1250 610383048 610383071
    0x1050f0a050c0a0203090d030201090c150306090506222909090a021806190603020711040506032e020f1312021c111e0f0a050d1719080109 61
    0x218401c3e1500c1c0350058004101030b00d41404c0a9089030b004030301c01e10002955603016242c5440748030f103a030000c0c60114440300601141e1545030003144d001d08008002085981442000113410145581600140100364401000c080b0603a511070301440c40044504003988003010400301603210b4420380c86100303010340c0d00803c10300500001d4000c900e071b60190501d111007200240042406600910155000004078030041c0800076424800380140f103151000358a0310440d142011104540e41c000307a02070782c0740900f00010350707900090742e140c40d8051208584214a031410702c4141070b29100c61445449000144143e02d4070390700c00c004c0c8181d140c10a0941e04203900c0fa00100c648440c503803400703540702c51002e48401501215500f140da03814401c07281c1413500000038000c525075503116510f4605150060010600c6400c062030203040c074640c121a480013450401000441680b005078000e05003059645061800c0036510040741d5540d08802000e0501303000b446e42c0140030301c1090042495580c10060701008 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 610385548 1250 610384298 610384321
    0x102070e0103020d08070f020a170f0105040b01060c0c0803071407060302030f15030c120f011104050603071817060109180b0106081e04060b090f070504050d08090301050f0a05 77
    0x16030f0360003050345413010110388903003105800c4454107568888801000170300680da5210080300400c2c56200e40444039808a182c2070801c0500d46189040e030b4105000c000028444c00c03100e506541d4903041c07800340402242080310140712070b81c011803103500c000a0346a00344001e9400842c42001d40504403608144c4818086099020503109070403801070b440089010118644450303c540700e006022660800701600003e008107140d44401d08503500050b0740410411000c0c0070310310418036640d09846c40e040c0380c900800e816210051620b000c01c41000c500c0e081031800702521781c00400940555640028030008080c1d00d44100b0f12540082600d051340343d15601104000444c003040c2c0007080d0082c981e00c0e01310181c0340d6807001483d4070075441c005910044040814407205000314001d1100281c2e015240041c022800c0001d400e10003600701e84001c101005a100c0200d03000d892040d41e00180d01c4101e450003007510b001c1c0300c1c2c0743d0768594200390412407510406c010300703445030011080610507510340200042 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 610386798 1250 610385548 610385551
    0x70605090d020c0105090d150608060105010201020a02100c020f0d0801080c040908090409110604080f0c010206131415010801050610050a020a03030515031c02100c090e0703060b0307050403020102070e 88
    0x1c00350f08040020b0a442d801840039003112880501655900030066603108003107500b64060207a5281d4954085c80000020000701340501402c0c0000c51526602c240040d584500380c94038008030b280c5410080301c01510a0000c154104801d40495a101e500303800050300c0700c03000340528234152194000a510500d068000c80003859008010286030001c00824030014016440042d5401040e40301015803549a14000740000d0400c0c1c005400c60100032081a03061143c402d81c1c3c40c2c1190f005000380049410f5202c0d0007614117501960800b100126491054180310905070030b004403a1200c0c0001a040f00103420180c403454089490700a4550804010f0b00d0b580108603280006070301056024002a010b9030050390001012041d00410480310f10000e458024441502078000c00c02d140c2c1005025010424100365001c402c0c810710410100b000d004105083c0b40c880c10700301da4451008104514000c2c0c3c03040303000e48100c2400503074903c1c2240001c1d00c1a4024031040740144182800081c10014040019 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 610388048 1250 610386798 610386823
    0x8030f060306070816090b0408011a060a08010b030415050c09040510030507151b08130608010518070c0f032610050607290601080a090312110d090807060509 69
    0x144c0031525a00640f41c1e01121030301501c414011502c4000c50a603406401900040466000200c0c60307004071003c0302c50304140941284d002e00d0040c8090009550007102840c19260443e110607180e60b2541041d0320f40403803000d0344414007803030882032060048004004007083c0300d003600e0910150315070400d4545e031594148005045e070b82000200748850030191015045200d001e180c0b5a16036840307800000385124900c1c2e070442d01c1000015400790111544041200108042d080c0740900c0d43c07405012990702480392248100071708680d0b0019401030f0250f1002c4600030b4004980d0072107a0300301d1038090701d02500070200301040050b0052007030025411001d524405d1170241c812040c030303500d00703000e11641c1d8019000448211501403000e09a010315902c10713500307081c40808490350318200340d00050440c010191941800a0824041101180e0410ba8054009a06120000304900c15a688078424000c00c1c41c4551002e040803805414840450041c2111501801342003040b40c44005c0c2e025a981c02803a5003 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 610389298 1250 610388048 610388057
    0x1e0609150c051e030901060803030a14010b0703020a08160605040605060406050409020d12110a11090601030e030a08060f12010f0f02040501090605070501060f08010c02010b0618040b03070f0308030f06030607 91
    0x2080101c03400d40556041045c090020070504d0721380107400c1c11908226030700000c269a80c10488a100134000c0700600400180800c14a846511f4a009480300380d0004041d101f01d400166034034a00307100c00006440349801c588100003030f040c01c0c980740024003001e80301140f145042403000f041910f070a10408076142c1d8020801480c0c40c02c01d6807448a40707410003001409205016506c1030002c2e41c18400015542e200321402190050010301300182100060b010604162500101c1c4000c5a4004211104e0318424100070a4507941c1000154600e5801809542c0104043c00d20a612034015001204140345c80070f01840301030766802c2603c049004510880c0d0006510140809c40355014000800803140100008a030454951803a100014a5035010109d07582d0f4400c01200c94550a110340b0b0310a400c22520391b442d0200c046110140c0c2103402800703030700c00c50b56509030740d6641d03404100c0000201040c0c1c152100540d580d0405120580045803c1c03807941030100c002804618000c16000d01c100d185440c0d = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 610390548 1250 610389298 610389337
    0x1209050a0c1a0d0b0a050315180706090306200c3a1d030a030905010f030e060126190c09020a120c030e1b030d050909041e0609150c05 59
    0x42e074402411300c4010b207076048842a134020030301d5141400030048108034100d5080290420001d80000e6015402e14104680c2080383d0038000c0f141d2000350034040381d03040500803800744211500030950309212825001480f0740048d5900e14428080740250031542d41809019103480041c205552300d01147c040b080c020301c600c45132038410600545d40356005c181415801e01800349014003181ca00350303144200f6804201c840004000030742e40400240100071031440d040c00407044034503180742e4808046c0030f50b1140f000e0a0704d40310b500802c0e0030340582c410744522044811040703005088110f1141c41850584045000f0000810325200034000caa526404a40d9048a0f80345084030100017455158000c504040d118400195100d904000d451b0005807103a40480d81081144201403820241e1503000060110601c8030451580d148111983e03c02d80200c0070034103040c929240644a4a40390304014560fa292038204070512030f51045180b00c2da9070a00c01040101602041036038036000302101a40fa0855084 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 610391798 1250 610390548 610390567
    0xc03010b030d081b040803070209060d0f110303090303211006020703030f0e10020705010201320901060b19090e060603041b0b04080a020f010c050304151209050a0c1a 73
    0x20300c40d901160064907013086180034250740c2510b0344142d1245040d40e10100c1c5d10025880e01900c1c41d500040304039030b20540054296920400400910400b502c1d9000303080300c1d03400c5a10284101e8840040007010b40381d139030080400c1e03810144450796030a062140440000f9901c8200401c1c4542500c115800030300c02c0600e0340c1e030300f00e03032000000b01000c04101d0a400400615224048401d02c1c2e1f00c1c007600540039250403d0300081c219000701503440d100580300307410a06441810213191000e40700060b0303100c8003035071062110760140ca5190f0140b0640c2c14001107070900100914180076060100c2d54070307400c0503a13a4071440244910280c0c0c003a9800003080000c0b40010b6015017208016242580164051903902c80ca002e91941050f80104015000110218114a88401452603841c802d080840d0541d60b60349589903280528000c401058041011500f181e900901c094101d0000390f0005200700c01540c58065254070100100721101030103d01c000c40d10100091440c0f0b030105d00400540d04140450 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 610393048 1250 610391798 610391807
    0x303031609050d0605090c06090d03030e0c060307020703140604120f170702070302151e0f0706060f18110a030b0a0909081b0307020d111f0f020c03010b030d 69
    0x840c150600004030000245610b81000c40f0b036003e8040c03c8001410301e00140024241207006103003a02c00c903000c01c80d4540668805210b020620703018540090400141c1c81d05910f084402640c0c030754090404801c0100c61036000030204103891007000003007005071000010555070071041e2401080c90120f00d40c0d203224188a0ba8074245007241ea407411031020003204410f0004c0c84000e483e100f0043c2c0101c8800d106604203004000c0c980421091003518000c40410300030102100285c0c0b8110b500c00000e840300c406220041903034181d54103d82d08104a60703483c070300041410704900c51540050381c030025501d085030b02c41c440d4000c1000d8510301c00d4038141200d82c00f20000c07c080d0410560100b0b120740b02003004407081c4282d085007031050003034503903581814181d01d003010b00301441d1103102e9004004030340068071441c1c402e008490340140711599800101000035080c0307000c060701e02d10390041560302040c1c9580c405140312004943d5002e694844080c10141800da44441d11351a40690000700e89102c1d05209 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 610394298 1250 610393048 610393081
    0xb0913080712080907050f0f040b061209031801020f0a02011b0b0f091c1d060d0912030c020f1e0c1002011505042309070b1b010e0606030303 62
    0x9a080c689404902d0b5030312400b40741d4901100000507240c03030410844180801034900a440d08403241c039044013120300000c001e0b180210000740159118a000551512030b1800d0300c13110915103160030442e280000c4410390fa50060214860030600000482c00c00394004603810900d2003044018120030610340c1c00560301c51205144605903004400b130b0810200312401c2e4a540541000040d2284900786000202c0c902400c0080807407603240100d4401c5507960700110310084d00c4421041940c00114420002100360080d0410304516900303110200f01008105585500c41500a843c01c00000300444000c0f40e58a415a04208150b8040d02c2c41442078206079500c40c050010540444801c80c1e4190b010410540d00b222048015039101c4240c0c1000220b00301141c03010302015034081218440c3c201c0502080005242d0010384c1608041c003044102c64184524400341c0b44c500451507450b161160008200c2070101c040c010154642040040c1221020074480d002c1d0f00000c00860440c1c403a01030740240c1c02407 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 610395548 1250 610394298 610394303
    0x16080d030f021204020904231f020c03040905130c08060712290301022b0c170402060a0207030c1814090d050a0314010603240302010207140a030b0f0414010b0913 71
    0x41441c014072400760402c0d480892500c0e524041c001d520380c15151041d46030327900f1f01a120320310300611040101000000980d8200d4040010109960b15601080d550f903800409000c0d1070460110404200d1620004150380503400e1aa0341220120031000c404040b1200041a454450544020308210b03008450390006a420001d0005240801c46200700c05035180655048200c86944010f18011828a20841c0c00407817850410b0f240078414101c0790f80105400400c024841c200100750080864800c108100203907a000049031106600ca862041d02c6c164dc2d00c1c10a468142000c99610320300d12500b0019026480900081c50740c070f4004441946d640c0c0140000c0b0f400c141d40d4411a024900165800301e0013842c070f94400044070040e207403840441c0044110010001c050103c01000140d90000d103010446001805020b50a41c004000030070110b040d41c0080c26202414040c03103a02c060b280005c03130041d4420000390945030103d01c1c400d4203a4481695903980000210000f4031203a00b02007000d08941d1 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 610396798 1250 610395548 610395563
    0x305090909150c2104060b03060903030f061c171306110a0b09030d0203040f12020a03020c01030f0e120c01060f060903020405070306080a0308010e0c04030f1416080d030f021204020904 81
    0x42a00c00d195140d0081218203031206d680b102e0841070b56080c140400c54200441d02d019614502c0c0078030080c912184043c1605004407408011900c0017850040740310f42e115402010101c2d01c03146500507000580003907890705840e0b003410b040060070354014240c03201203500d1030020340000900c0e92202c03074a00d00c0003000110b0750300007040140301c0800d051004600c900d1044a00d0b4100d48032a081c030a2503903014808070b41c1990701401079440406d03000102c1c0b000062003460007203850070f11407a4400103800c04161034203180c4103032400d0022140403200500352441144000b0403c0715503e000900e400d40c40c40c444c070780100d45503d00c00d0015040c01d41009078010308504011503041d55460b88175260110048d41900001d0300840140503c2c0007501c44141c2280c2c041c00e066052a0840d11403081c0354982240041580390701c1c04108e210103c040c0030081240d20340b42e0600e801309659041e0305807601009082e0b407000a03e85502e1040c11740b014400e49158048400881065945a03030a00180c8000030b0026107028 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 610398048 1250 610396798 610396837
    0x3080606071e0b04060b04020a0e1e03010c110d080c07080d06031a040c0b094c030c03060f0632090109141f090801090305090909150c 59
    0x281c504000c40d070600c0380f05041c8580c0d5840d090030314800b22201c103180c0511840c010406030302090b61025905640c1e0030210348100101d0f003081c00c06003c00740445107698240d420a0400721482d9040b401501100580c4030544400c4940000c040380c08120443c1c402c40160000e205090204410304080d1050400f114000141d242d105d40b41c41c011007400203901045640030b0400c01c001c01004060802c020016182c080b4241204000090074820484000d100b100c44e43d034041071002401480a1803910400c03d071550740031014840040faa4007042001800030030b0400c6c4440356114882c1c1708031002c852140c02c01d8001942090011506011442c0d00306a43c032881d250040224442003091064181c8000c0c1c2c4180d844e902d8a00142107056240c0c01141c010780000381d00e105640701e214003070314004003281d04114801e210700015100c240151304141c5581d8079010705241055001001401c0c0e000382206c8841b00e640d541e1f06500d81d603d034011800c00941045030085110107800074040c1c18081001301c049a000c = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 610399298 1250 610398048 610398083
    0x460b0301090b040b040525091802060429040b0712140a050f12101404151202010504120318050603060a030b090307082d040b040b1c0c0c0b010501020a0308060607 71
    0x110f01e695451028180404010823413801944920001c8040035112141458501d800045185c00307644110001c810326900c014034612070740d4420641b507032051201c43d9210360300c0f10030040860700811011200c50148035010a01d183c090241840b001c040182017074a0010484c0089440c0c3c0c00c43c102460f216a418000041d44c4204640094820f164012008050500d0702d9600040400400c007024040c80c50310b90b03611300200f41c2d00d040a0580d090515450340100b994070040740c00c0d00c116404010b0000500e40036100701903100070590512070080c0a626032850b2100b04014003031005584441d400000104100005140712042c1035000300c0c184107407402d1000944800207598040d024012a14083c144148464045110000c00c4602e46564050900742004c1c80052580300700d02441650341c2e804191400194010020041007018885045c0400040030202405540400000b1980d04c0b00e554004140ca520000b0b035a6103a030b801d43d89100050f01e60300b081c03000e2644000320548200c07550142c0c2a80 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 610400548 1250 610399298 610399333
    0x71e0b0a090f0b13150204050901090c14030a060807050618040504051f02030a140714030c0d02070f0506070809210c030a1d03010c08460b0301090b040b0405 69
    0x1040028502600c404200340c03920107541130031700000ca050244144424800f41d281c43c55458152541c0e00c50000e80d2042c0403505455001c8548030400d200300c80002000601e840a40101d002c03a98650102c88510791200c003042014001c404105c0d44d20304001c1800340d0585440c1d0401e80c1c006014030309407100310ba4a0014940d44a5000302d000b03030042d4001051004c0e000003132050340c040d901840d000c489a0b00305200c00400b9001e41e103410310701403080800443d00c039590041c100c2d20b00c410026411580c4000f54a0903468045005609840c1805803900003040c482c02011006d02c0b07942c0d001c01520041c2180e82811621045407000c01c2c0b030002041c000e858286204000500c0041d14030340b16103014030900c101c5c020049080c1c04a980c041d90503c401c00a00c40c1e0400041c0f03030044e10040c464441000700048048100c1031560b03e0710a010920b82d410950320a071003e0000841d803258806000000c100e03030a00d420380b00b01110003481d030600f0b000020042041344e20100d030464800c0041e5011040b4022440380d = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 610401798 1250 610400548 610400551
    0x1b021f030c0e0f010c0b1b0304140c030c060d021c150e09030a1d0402070c0f05040b040204030b010b2116080618011e0503060c071e0b0a090f0b 63
    0x2000c66628401e00c0c05003900880c4000e20300104580f144003460300700c07000909a899180c2c0042c1b4220803840450314032100040005400c00b0320b210384940300d150500300115142c41a0b01c1e0070703681340254040003900d07050101d0704450010018020740d10742091409041c1c0258070220070315402c45903514000409041c580180c1d10602030490100c003481e41401c0c0c0301086c003a409001080164800c002e01d03481141c00041806040c0c202042081d001d95140340490064400d00c00024100c20304144003084603030290f40c90740180c407826581048000c03030b01002d0008910490001500302c0001000401490200c003009007060345026503103484c001002400209041c1041e18482c61b480001c905007001143d124441c0c651002080756042c04280985010b07010401040c01100c0356141070000d004880041c10321a00b004017405002c0f90210f10380282d0301d030700c0c54100c100b00300e0b02800d0b10ba018582404c0754140d58201250070080c1c0075500d4a54103406001007685400443c0d80000421030300010035119003845 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 610403048 1250 610401798 610401859
    0x80102040b03100e0103050c0d02010c12080a0b0a0b070807080f03010b03090607031b031d030c1507020705012a060509010f0b19030201050f040305011506030e0d1b02 73
    0x540c4030304104400c220301c0c0f40b00342c1201e01c1a007290001000030890020308a401c80740d0682c0c521011030b0712070004071558001000c000d0b114041c80e81e603011409900018049c480ea10b03a090030407816280904100c207042c014403800d6181c500a03c420004603020341e0080c0b011500c04c11010f8580800c0d5413203409180c00c03d0740074507a102000300400503400320601c081e1354010000d250400100018100802401100e0820201016a9011a8040c0d9480107920441c40e0140780100e03500c95415141c0c480d55411000c007010021000c01000c181d80c0b42c000100441610303030503164021014224448642001030a002015051010b0104140815824031985024008000c00031908958100e03041d0700382c500c503400f15800b0b2840c4030302c4001c4030503600c5400c1c81a03030760910308555170321103120804816001d00e4001900365441c0ca022621526003264888040b41c403681c605002070500c886855480d011402500c001140e200030022700c1c08081e03951418074551000b0956000b02d80e844820400148282d010f1 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 610404298 1250 610403048 610403069
    0x170f010513030807090e15030a060f0902041a0109060813080a0306030218100b070212070f0e0901090c091d0109051e0304140103020703021e030304021302090a030809040608010204 79
    0x707010602d9441155560b201020b418450016032070030810700740a040060603450000ba03e841142801d5a042c02510001c0b504007506021000c0d100415000818520300100e105a10348002c2e8280c25809000c82c04840a05840b03c4003640e18002065480d0380300202813005807414040007034006542c1001034a187d80203035900160860541c414407000580c08511070300c40e5500101005000520440810240e800c6000525101c00345032010a24039000402450254010184003081082c1652141d90032186424400e6a0641301e070641d032400c0343d8950f00040c00c0d10000703d00034021050650004d01c82d0100001600c100140ca98031b00b60b007110f25141084035242c001d8240c0c1c40d0302009001354201d03024140c0b0091441d042c40e00492409100c00f40c0e801d10b05242d00821a2001e040c02481542000312256240703601c1e1030250021582c483d4000c5a04910a02c0310f4070844071504510b1090341c158640203401c02c0381c0c80c0d086403075000d03a40c1c12280b4540d0f8055142e1101040800b4280083c00041001040 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 610405548 1250 610404298 610404331
    0x3050c060702122b020a05120d110c0609011103090601090b01090914011422090c0317040302090a02180d26091309020604060c0c1502061e010b04170f0105 68
    0x5413007041102007450b002158010816000410b10219101000c5d544640310300d5503550307000d15108e0191007401e00c0b900c249040401d000c03030700e02400706619119a80c144000c07c84824105840d891900054810f0b01d0190f01c000c006206075010f40d88440fa600c0414140000540d0707444c1045070569000f41c06900d442482d2100401c0031903103000080c0f8411100711905803c01c0f6010411b0f2600d04075500c001c0c0405031301c0f1002d000a00c400005071501035504011f2002042d540301c00500129805440128001c0d1400130018514032418400e4403040c1580784e200c404030034039010412520322500f9009507a0071030ac01c1c0d0000c0070305d0903a003082e43e03400a000d0f561a48440c2c110b0108042c0090441c021041c540c1007024000050395a40100c0302503a103a81842500364889007040c0425020341d800102d0915000700300d1110251b00083d1052245104d124801448048030b4810503000c031080c40fa03400003903400c0c801844a64110040c0080302c0300040704680e40c14000ba2405401d441041d214080d4035404485c = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 610406798 1250 610405548 610405603
    0x6190206010821030604060f0f030506010605041a0c16060c1502040311091308130e160819020c0607080402120d09030f0201020c090a0b0307060903050c06070212 71
    0x4480e60040040a010b804000001520150f40d0a91031000c10301c48580000081e14550342d5a00000241182c00a01a1465107800c400000d000c0d03270b400203680314404c100c00010528494421141511400c40b5222140104408420016005006980203c0c090a401a03130149015420900104007640c1e550504540c24201100030b18591241c07801710500412050001c00d4000942c1e45c1011400e4903980c490350f031035407114001a030462a00404902c0d00203405031544090301201c8045c4c1e4400500c5001940b80d51030700340d9000f451200c841d800729029800048842034059801240c1d20000000545042c10303c4080c0c604010080343d04a01003400300050000b50708100342d80d414a40c044100400d25071007135810140c511912488018005128440003408592080c440111403e5002d4020851420b00824010280a805020600900c19880c0c0064030601c104c00030780440b50480d0181034070800f400180003c550060700f00342d811403d410070b0450000d600b0000a0001310f088240800400c4184 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 610408048 1250 610406798 610406803
    0x52107030b04020f19050d050405010605010806010302120c030c0903030304060e0c060c06150d0816030e04020f041e030f0609021003091a0405010b1203040305010c08190507030b061902 81
    0x7101c0c54080d62061282000400d490320840f002c03000c416240c0c0390180f150500440355441105004007260b8140343c14082006015000300303040e0386098950f078156a072450011800c81c0907040c0300112118010010402d080c1c0480300840e04a083c98045900d23182c0780714042403859100780c5084640ca9640e46072211709200900c6402d100510495200703260100e2090069954030000e008250f0b401800541181c0f41d5075050900703c0050360100c82c0540751800001050458000d054007900450710803c131500d440d1400d40b088601401c4003442d01da04142c01d1503510301144000101070713204400300c0740003c000b00701e143c0c0342e10311400d2040c080802c00d80210720500c2888074040601d5000d05080a074a1400900c86000d1001c8030a85244a0380e51a0354030f06001b400741c5110007480d50045000440d92602c003402100900c103803801017000b070040348041031040f5040e6200300d5240605802108140f400350340345030426a049942483c0114040c00c070708002461a51198407603254401581c841e0000e0035806 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 610409298 1250 610408048 610408061
    0x213170c040501030f0303020a0309060c0e0901060503091e07050616060f060303080a0f0b0a080a2a0b07082505010c0905010219050f07030f20010509040c05210703 72
    0x1a01c081c007081d45945d450030201c141c821002000e0540105012902e5803282d486a1740e15904980c084c0b04d8002c000002400c44040e411039180170f2a43c4c0400850b8841c01202128018111030005001c4020042d1a1501c902101d40124406000d12940082c1c207130346840182c4004038200d01c03141c3c0d0303111103440d00d80e080702d0110503040300c00303402c0a004002180c0c0014849900030303000840403c4d081e21f01c8910b00010302c08a05040c1c1d0081010700f0106101070000f46c44e4640030f01c1010708044100ea092120044a500c120300c60395903003410343c010b000c0c0001d07a0024006061082d40340e1405c0040750465891440035499144103d8401480e245090060034060603501c00040c0c10a220428100790000313481716100401d603450340323449034500000c210080025940c22464982582c4800340c981c038020708070301c09422041d00c40031901c007050004540ba8039120606204140c44113441c0060101c00e01016141c00c00c510000d100c001d04c80f500a40c0c213058414141540f507044e00c0b2907986040200642120306 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 610410548 1250 610409298 610409323
    0x3070510091e0501020a0b0703090203010c0e180103020f01140c0f100b3a0b15122815020c010b040609060605030c0f250b0609060d0b06010201021317 66
    0x202c0c1c510402032641c001c074a074032225410403044400c5542e00300c2300b900a8101c242000b0b4041d0702e4202c0e000080d5501800c1400d00c0d01c4101c2d4401d040c04012543d80c1d0300043c0c2808041c5d40300d0900c80601c0e100e0742c019180c401110b0641d045480c10704032125240c030b0600c00c410b855401103410401003488101c8081c441c4542481085410a009015800c0c1001441c020b9100254240290040d20760501d1040b682c00001030f80d000c840144c403880c01402050303011050141640c02590040d071200c002c6800030506082001e54003501200c000084940021820f80f4114160b454202902d180751024401d40000c00f14204a0310011a00710146001c0c00f0440e079007a8041c03240f440ca042001c0c4851944002103070b8001e41040a029182c040381c80034800a882044542c420403c46500382c080104070014021040f0390141c45410070310783d07982060084451040301d1455000000d12411f000180451282540100040c4001414100f00107050004034010b5004107104083d00941178800725420043e1004414 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 610411798 1250 610410548 610410599
    0x304060b060706050105090f010b180301060f23030106061211070210020d11010501050a0909170301031407080c0603071115131e030e010f051e030f1b0a0e0307051009 73
    0x10700d840b80300e0380b0b9404bd5a04003a020b40914140d44510758094000c40080d0041681284140e5540c2e5021681c0d14030030000c0000c03071604644010801d18043c0301c0c9500700e0364a078a13a050001d00c0200c2c640300a03d00380207008800718050101e94056115042998115885900202219003089a004e0812003890752008690380c10714005111903164081014210b0f40d0024000c540074140f403500511800d003800c1603e042c000003000000511030100030010301017081c00d0540e40307c0c070384490b01d540c0c540d03080590741c5411510800c04a0b080030b00c0340410416818225054516003849180b0003100a501034a40105480c0074171003032014013200c480c1c1290020a03242260100c00480e40d070203040361150000440c10300180c8201011803900038021140305000711400410141c4910071040700940080d1114001c0d00c0200c800202c5407412040c001c002800440c55250629402c1281182c3c1400303010705190300340c040e009001401e070302d82030380da03141d4109180c444407041400c050101c84005825181103a406 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 610413048 1250 610411798 610411801
    0x1205010501090b0c070e0a0b1e03031e090405010b0901020f0f06040803071107030807060e0102130b03190e0601060f020d080f07050702100206160e0609060304060b060706050105090f 80
    0x20380e00880d9140880d003d0424041e2150903061025040242e036502200c8030800307000800001c04126404110742007021580e900c00d0543c51000b0341c55416603086001e030554810400710b600c0690b10b90010810350380f076111052a0204036400b00d025039400f84e0180f80c0d1007001145400a40d81c041c4074000e100ca04400c001d040c0c5016482c003150360307190b000d0805040000c0000c0800d151622401c08840241c05850844001e07599074079040d469503007e04010354801d4903222402d0712000d012b000315030405140c01c0f40802c40904040910b425944041c002c0c109100c007901c0011204111800b95011208000300688103561601801030000b041c0c4020581c115005920401140c542000c004d1b0f40003100940315010366500c401003075a00e40314000c0d01275031112410700385c420080c0d03002901601c1503070080002c00d41c0a001070001d4540c20544000e40d0f0b400081031010481a040c03040285034094011400440d00103a40408108203034003104040d038010f91900018480c508080300c1e000d800042603001d00a07103 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 610414298 1250 610413048 610413059
    0x60702060412080405030d09030c0b16031119030302090a09061d04060b211005090705060f070b0108060f0708040b060d110604150201051305060f10030b0c0703120501 73
    0x5114900404507811482c0081400b480b0004040c1d801401d005400c036410100740500c003900b0005244002c1311426007844022561001c84025104c21030a05541484800c0c034aa5059030070541d01200c0302e2140c070540800a2071100d6112096181a000b40c60050340c0b4000300b4180002c260154100c41406420088100512038402c2d0310f03d4440c5e4400c241d48400da440780d2a206014080c81f80949030302c210301c041c00c5107804243d01e007903a04039011201120000441032462005580044a0080540d0041e180800450501900511130040c079005000c1c600505581c0d4090318038001c0c1c011454540c4a081008040301480c0a069000b401c24201040c40b85095603c1e00521200207040d1800b400c03036140e810041158541d8020b0303500900801e05074480b91203a144000c1a405030341282c0040d8241000b0440c0c501d5000324103003129070060050705266075034803080a5400005000b11000441290b00003000c261070804450052000d6140c195450440d414010024101c804015401c985440010440b = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 610415548 1250 610414298 610414309
    0x714010509090a0b030a0b0a140903030c0c1606030c080903070206030105040f0207140c031603080307140f161a091b04021b0c090c0f0409050c160c14060702 69
    0x4540108070340316012035959400703020180507161001900b612031000401b00304119a20341c3c91003611450010884900e00705110404d014080d1503440007600708002040d2564000c03402040c45188190880340301c0c1245001032000c1b50302550044001942d10007000d40754552154a107a0001d4410f8019800c004a03900050406d11042c45181c1c440c9944046040c10300c005901580e0b20240c01c030120f00d40380c0880c09040d5494000c4151003903c42c0c0138145a0f03525449200c041202960b07040940c0074103580d1881c0b425030f6520003549800d603480d001070115103800d00c41500108500380140755078260f01c7d2418076083c00f010300000c0c0c03100d00204802c02000903880002540b0050a411180b01d01c1c0401720480101d00248a10100d0765000810701c00400c114550000d002c0000c600e0603101d2002c141d544903041e102074021820700c0718160808002c10001c0f0340868101079001085240201c2c50440034000300714000150300000c0b02c21810b0404208060040c0c125408940c0b1000d035107040c80d09006900180 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 610416798 1250 610415548 610415557
    0x3030601120f020a11060108010c14030a1506020a05060112020303070b0408040906080c0a06181413050405151501120f06030c03210c120507051c090807140105 70
    0x5040100c007001d02001604075070041d20344503086120031565404204401404442c80c1c2d00344040c18440c1d00000162903d05101d00500004650b40d103940313202c045070034100d40d42e0029004c124080d03200e01c030b071203003081302d412940008100680040100c8002c034503000d418100c050303100342440d40d030444101015032008000c490009610640c00201ca0b9207a18106545000d50307003244200c0d600c0e04402140000002a02ca082291b04a81d130203906551003004540c2944003e0f154010500d508208100103d02da405e001300241c002410100f00c21541a03200702242d030b00300d809550b6544528603480300740d041040826001450520a00c182059010018205041440510100542d18a003e40b40f03003c9940c41071000e980d1124071f40b10690364a09114402002076454040c10100000c1780000c16070240000c210141c0d40180030903d81d80d00c440095405d40c000c103a05503031500070380d20f07034921541d8001c05401030300d04c5580f5255980c0342042623080c40d02903948c100105076410120b0303030280e90b0b0b000410784 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 610418048 1250 610416798 610416811
    0x809011b0c02041e06060c05100c091721040302040c0801030203120903030f0c03030609130c050f0103230117030720031005010b07032a03111912021606020303 70
    0xc07810400348408130502c41d20207031304004101d10300200802d035250b002001852840c00b072001c9405080f1800740040495803504850750118000070380400110f608190b400850301480030540d52042c0a6039990008a200d0072411043c41c00d00040c1802180b515224a40f920302032860700030311a60559010aa03038602d5050495503090380803603400c2060390308004941d84090015005d98440a56107190743c1c1d02e8205481135441001201c0001c2e4551400a00340074000f904115444541486c000a1292656450b02d015040540701c0852002e4201031a5140c60681341d649841d200561508940c10115015140c01c803400350010001d07140810207484180404841011b902d5444600d00300c0000d00c1c00d0120003403a0003060405000141c51030116000c0c2c04210b0081e15a400c200076024510320359003000c000b4012407a2841e90101c80031902c107501030350500c001c003811646004801c00c4010744408403500c003105e0300290001040507040d418400d00d4403911801c0c805075050f5042c03503006501d901000f003c5 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 610419298 1250 610418048 610418051
    0x162a06030f0609020309060c0c011d0d1b20060d0203130b221b0e07080a050601030e1b121603060b0604050d080c0a080c0c01180b040b160b070809011b0c0204 69
    0x504041c160701f98800c1e205130014602f0a1001c0500c2c401c1c0d591141441100074010510030410b101c080c0240910340343c880d96201154038003401c41d03801d00e00704000c0032120310303a005801807200884070394652008601800c8080340400703140585203007180440d83d00070b001e0300c00c401007481a151245a086498810f0300c1e4401104000c0602c1e01d4041008090543e100744142c2801c0418001055040b5401d140100b00403202481b895440100540031740701065a07040681d0b100d40741e810300048240302030305e003c001e0050800e003001040407007032880d2100c00d49a00d2a88485007030100200801e61090500e05d640c1511f05a0410f480c013800500039044440d40500710850001b4481c0c0c0d4008280203844074194009601c548410200c5242ca941d40031801240340132031002d4440c0420001c0012100d800c03141d02d941e500e4901070600c4406000354200d141002d0101c0c00e0500120300044d12a802903100d100c255654040c9031500803010740c02d581314180580c1000c41140c80701d8000b81d600c8a160f0242c150143c40 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 610420548 1250 610419298 610419307
    0x3020703050909134d0415080d09030b0403050a12020408030903060604091a13150e06060103060e060f0109150f0917030a08090a020d051c05162a06030f0609020309060c 74
    0x1282e010901c000217403c0e0b803152409104005945600c5900300680b00810700325031103845c05020980720416180005004200501d00240001e0700c14001410705081d140f4003c00035035181c102c030380c1c00c0e60460741003580c0030b030004075494403281001c00c8855030115044a052003008003940b04c503c0100c1540c0354103c8860502ca00050601c0380d2000800b1300a070f8008050414000842c10715001407440661615040c091038011400540c42402401c05440c6000b01945481e203441c0100300603c220080e180313041c4010700900080307131640c0e4401000880116114510900380240e030084c01ca1f1100d8010018090003802d4034504a00c00000351002030503981011a040e40f9110381880c81c28030080301c029806405945404204800171540d8ac1030302e02c01c404043d184d45440e60042d541170040d40703000d0345821496940300b004285c54142d098005010300307401d03003150300391142810184071442d0449404651034100382c14a2240511401c070082001d25021030070750410b402c440343c07600c0d0080c0864501020200b07 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 610421798 1250 610420548 610420673
    0x3b0702120304050105100909150b0a0b1201050405060d0807150b03010e010c1e0804020f0612010f0f0509010e24180609090a050d0302070305090913 65
    0x480000400300c40042581c4030300d440e24006000c1c21044a10b80802c61040500141c4501c01e80915440a03601c00c1505c40d56a180c050b40e0002000c00814040d40b222600600188241c00c0400504500d03589200140c0305604040901080d03803c0644064003a8030240103202c00701c0d4640007951141c5510202442e103000c038250180c0007500d0010702c40c561652070f00901e52b20b000c0b015030204003040c02c40c4e00c822880c500c0511001c10b24520b0b1045110110b00f048000600504c0c100d0305e80b48083c02c00030111410000001c8860f10b000000b60481081082028018030004101c94443c20041c00c041f18089403a604198100e02070440251007a440c1150500030f031252541412006030381450041c1100c0d241d22000c1c03070389003240102034405600a500000115000a4001c02e100c60040cae0041c1c024900f40040d400210000e50202d40291304202c0140064849a43d5045000e4020120b8008801c140d100f90f0520540e1400d86a00c168401d60351083e01d41d03c0c09401004804021010a541a4680d003104 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 610423048 1250 610421798 610421803
    0xf11190e06010509041404050706482004051b1602041122031101110c0a1203020f01061401030f0b040903030509060906151003090203060406063b0702 66
    0x13182a5038400e044c14040c404e80403909030218459802182190384c699a100c0040d161722025014090821803800307039a40c0c030000c000c400440100e000c03021013070f94004194071030b2700b400703000b00c0d01100c070203030040c010b5041080690482c0204100c200c504100e1820070307a194186d240c042d444a440c110402189840c003090f140d4051208281d000351062100b030038411620402a403000050260102c21016411007040485403181c0030b030381d07002c015866460200d00054480c4404035480301e04610919000740b865407900d00d2884010110080aa08818a41d207006420442081a8181d06038940301d400c008080c104c46882c5090013007800c0016505410008031030207000380c1810301d46c0190a2516007000c0561540c0414401d0b00c3e01400c1c2c03040340d191309046a4944005070f80802e1400c46010700310400d4501944032810740e090764200003a02d00080c1d80480d0400400300e030159040b0741e45030010442c80040b04108920000d803040c03001c1549981d490792100840c0c400202c8051000000b0000d0050b0703008 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 610424298 1250 610423048 610423057
    0xc09150c021e031b0604050103111603050d1a10050a02150c1b1605090c070501051f050a050916021f06180504020f1201180f11190e060105 61
    0x90406500008002001001c0d0b24022601e280680302c2c2a0b0208201d01603040c801212280042c852442c0a00c1c0c00c004402520003804490f108100400120707021000c89103412641c54480c1e02e409848016441044049450141c800e040701d4013221004042c990f295008480c4d0900715082c000e464083c210b0049291203c0b0391607628100441400380901a21035202401f050034600c040101000021020241c450b00030b180901d00e21340c8409820301481ca04460440d038003400ca07007041414800e050301c0d1303e802d44805480d030404180002e0540f4403000030108024010303000a440b200c604600c1c10001c1804107500500c2240340c001e04191203040c451007032113100066402110144888104d00c038026008121600c247d02d6031500c01c0708506080c041c2806650710a94000b061984040c800304280010b0150007044a503455586843d03c81101d03204d10900207402d070041ca112010802e50380fa000d003120701c050701454481d00c052240c5e25900703669120741509948240d0034512040d05c5090041c0c800b40107 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 610425548 1250 610424298 610424303
    0xa080702100903020c0f0414010e150a1805160e04020304020f18090d09240210020f040f0b09100f1803060207030206240f06070c08070609090c09150c 66
    0x80c00c549000f495800184211540d400301d64410400700a00100022104000700800c00018440010030940450010f031135440841e0401e46c032050795041000036110910342d08010300d01070320682e102e0000c6001e4400e1551001a0f01c4154101100001001d0040c0080e000b441d4466900000040c0464030740f61845031495801415007601c01c5454050904d1080c4111030201d400e114842c1450300301403103801c2c80390480d00e074031807a50304900800c4681100540b40c03400b10710030f512401c9840e108420040c130050801214840380c1035225410400300c03609001070383e0710487c0c14250511039018580e80e03000c1280000c0c041c80c100070900100d0400309450300010402410940030b0002c20020622049800030107000c0e200b41d0940310300383da4041d4001d00c56101440180320907221407500c0350581c14214403c0c0c810b01e0b8001c10250070401c2541c1e640884c844982c0003006076030840c0350104600c641010b00e52000c0c00101e6000d11111060040c024004403007842004461403505942141440c0680b81003080580c = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 610426798 1250 610425548 610425551
    0x10e0d0f080a440a0e15091b100516050a0f0b13050a060c0909050903040f08030f0913091505041b2301030e1905010b0a08030a08070210 60
    0xe85040a0010662150403598a0240c401c0407050783c6406040a0250720807603031903203000b41615104200056000707143c6a80d4503503d0303800c0d01e040e0708100844042d020341c48100310f2207450076036006030511000300c1440500c1400c40b6801e445590740d0282403001500c9514115850310403540c0090031508001001400742c1c0601d000641c203002c5a40085a023150050b05d4001e00b0746c598180c0c941d424942c194014200e40c20410745800083d03440d401c000c000009500e010090140c8501070101298010ba40010541d40000340400c0400c2c241070555000b040c0c1c0d50040c50500d86112040c91603482084242841082080482c0703054030100e50144000c55044000540c80e0b0490714400c1000300001d5605541071420307600c0b07140b862400d201150301510781c0030b666588480c2240d018803e1030348480030a00e040c152201c82034020650708101d440400c3c80d200415417058002820000d08544244c81441c1c05401240010f0100c032000004817102a0024a480b88035a91174160803030411848070340d901c01c2107 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 610428048 1250 610426798 610426807
    0xd0503160b0601090f120b042102031207050301150e130c030b090105040b0d060509120c1507020a020d080a090b0c030c0717060402100507021005030901150302010e0d0f08 75
    0x1141040d400d110b600d00782ca0300c1c143c491701d68020100c074201500c00e00c0f00d08400074150100180903008800c4c1c0080c85030410200000c08007060410100500c241100160b0000c03900709900c004003c0a40d41000342c42c00c00030300e594102800ca15202e010040c08000307000800044000a4440a103d11903103090600104940f88070b0700300050160440100349403240c140315001003071a02d01840340b5240900000d01c02ca1402220341e4541020703000042c8168400e01410346284a482d12000080485241c59000b4100c00100f0801a010364036010300004110352018402c0001a20f4451703110b00700a4109841980725100c11400329031291f201d40107000b4091011504c2250088004040c2c0b0030004004160b0f110326844903002000300c00700076501381c90790b40840045405030038000c1584128030280c0c50f14615200e8680c011521200e04030100200046000003044030b44c990a2054070b11003050507094641052035a00000c09078074003240300e9807280031031030000c0c0c08024204420340c00142d8441e03481a141e = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 610429298 1250 610428048 610428053
    0x70308181c053106030f020c01060605070218070804170c07170c03060402130236090105010503061014040815070f090f031104091a061513050d050316 66
    0x719000f508101d40494000814500590002000c4041405034426501c41892900500b2000b0703001070b120a58a030743e400c004903200b00b1000e00940001e0030b0103455803030340d8031840d106210306005010b030003c5a50507503d0500900da6800886a600603030800980c05484500f2510302da200c0c492000707615000d205074000018441d880888106440444030140c4600d00355080c00e05448920441e0000d5002070156010445035945034060080303281a40d481d0b69030200401d08110340b070511090b600c2403c0700d001d100d1050030301c7c0c80200b00e40506405c4c070f820341c118101100032030115945045000e00740101003402210a0300d075602039400402040c400c80c0e1041c1001401408844000d03500d1500240640d03800000040c0503aa58808444031842c0081005140d82c40d042d0700d002602000c80c1c2d003d500c403540c0d403000c02c50032010000c0000fa6146c0040e003a050040401c40180c0c0d501d41c00224102c0306103e400d500710070003034008c0200c1d030701a01c060244c002309142041c114841c6407200c2c4050003a0844c0c4000703 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 610430548 1250 610429298 610429307
    0x31c1d070f080309030c1216030303050a0b10121d07030c031101080412080403021501140a06020607050702010e03070902070812060d080d0b0d0b090a030212070308181c 74
    0x321500011941007154039090419142d00c200044141c1550151900000c0c80c18100300601440700f045045e90812519850521400b02881d4000d40001c1e40f00d000344030300c2d040c00340324501d480103084600008210074400050048510561403071001955142c24038268005030b01e0030200940000c1c1641d80701a00e910340303e203081089000c1554800d4039155290b0071940540d14281c066030f08031281d90070000c5088403ca46c15100244210300b14060f2082c18684e0010040ca014042c1542840d01c0c4481c00510050000242c0d0a070300040455001500f0b0103491a005800ca80ca02502840d0515440f160311340840d1400e0b550740d014003600703440007590340c1c10301c0380d0325014082c4125402c0a4140d103803199002c114080100080242c14240c00b00b0500c030044d85241d10402e5103010140c41c000500301c0c180c81e1701c65014800c0340c10f0421904a50f04e2442010b80c14421040c809016910103400d0580340d407001004a0340040c1501c2d80c0c030810340c0d56500011020804100c23030f000d6940311060481c0d42c0000003030 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 610431654 1106 610430548 610430563
    0x40b0a02090d0309050f010801030b271603031d0306010b2503050309100608070501030e10060602010b0907020615091005090c12011502031c1d 63
    0x4054442c618401c9010f070003501c078020410700e45010700003a030000440c3c842c104000040188005111145116040507143d56031240e84065a01841006c245200c0f01032810710410031154200b1205104140c1a81d100740e8801c10040c900c0100120240c40c482d0400d0340c5908a18014070100341c0000140140803860403c41401600603050003c01501011050380007a40010030440741c41400c00c522003406895180411900345411403281d10b5030306a005107030400da2502c2c5100050b0508008040f008100040100f011555814010b4024241c1c43e46441c0200445000295000d0011640c0ca1007071420b0210701076810b9140f401c100e01010014a0141101182c01c070101e40394403a855400d00c03900d1441401503030f4031402c00c0c540007032140507480750005082103090081c4090b40401603811202c3c0e03154040707045842e2449103c001d040e0006106580140b1100e40c0b100c07602000581c1b1 = true := by decide +kernel

theorem cover : BRFrame.Cov 610251798 610431654 := by
  have h0 := BRFrame.cov_init 610251798
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610251798 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610251798 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610251798 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610251798 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610251798 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610251798 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610251798 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610251798 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610251798 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610251798 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610251798 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610251798 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610251798 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610251798 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610251798 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610251798 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610251798 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610251798 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610251798 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610251798 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610251798 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610251798 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610251798 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610251798 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610251798 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610251798 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610251798 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610251798 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610251798 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610251798 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610251798 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610251798 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610251798 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610251798 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610251798 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610251798 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610251798 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610251798 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610251798 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610251798 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610251798 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610251798 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610251798 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610251798 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610251798 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610251798 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610251798 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610251798 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610251798 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610251798 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610251798 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610251798 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610251798 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610251798 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610251798 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610251798 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610251798 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610251798 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610251798 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610251798 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610251798 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610251798 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610251798 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610251798 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610251798 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610251798 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610251798 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610251798 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610251798 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610251798 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610251798 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610251798 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610251798 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610251798 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610251798 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610251798 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610251798 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610251798 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610251798 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610251798 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610251798 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610251798 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610251798 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610251798 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610251798 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610251798 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610251798 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610251798 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610251798 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610251798 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610251798 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610251798 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610251798 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610251798 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610251798 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610251798 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610251798 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610251798 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610251798 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610251798 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610251798 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610251798 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610251798 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610251798 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610251798 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610251798 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610251798 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610251798 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610251798 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610251798 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610251798 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610251798 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610251798 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610251798 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610251798 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610251798 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610251798 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610251798 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610251798 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610251798 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610251798 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610251798 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610251798 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610251798 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610251798 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610251798 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610251798 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610251798 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610251798 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610251798 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610251798 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610251798 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610251798 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610251798 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610251798 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610251798 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610251798 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610251798 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610251798 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610251798 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610251798 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610251798 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610251798 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610251798 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 610251798 ≤ n) (h2 : n < 610431654) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
