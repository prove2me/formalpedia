-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4567
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T13:02:09.641983+00:00
-- url     : https://prove2.me/submissions/d8c28154-1e47-4426-836e-a75e09914a1d

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 821223021 ≤ n < 821402877 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 821224271 1250 821223021 821223031
    0x3041115041e09050f091203130b040c050a0b0d06050604051c1b09050717150d03090915080f06040206070605090102070f06021b28031e030605090a05 66
    0x50000e010902100042c20121011910342c40d044140040d510120101078074001d540c528494800a424040848001e200703c2d404094a00601c501d181860302c031140b001d02c01943c0c050080714a000c00300c0c0030031000b101c600c0010880181004100f03601d4455030040d5038000c1121440d01440c3c01d17400141e90a0100a440032200e0040c504034003070038100c46800c840643d0f840d00326104095103106500c0381c60003084107400707892015000107891400c54405000140701d4600041172007803103403c1005584244d401050200d6050362040104d02a5281c2503880c0d216580006405a080c82104a48860507a03075450480e116001260b520f03540303400340d40e0788800c82a0b4020350050303c104408000701d500ba412060b0400d0342000018a0701c03003d604d41040c050b80c0050b0480e60f01c0c0d000281e44500803032207400b45038104401006000150401c032800074448442c414442d01903010014428249806940030901244800d440b00d0185076a00c20001c3c010003140c080c1c14491444100401c560803614422180f00d9 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 821225521 1250 821224271 821224309
    0x20307110609070b09031009050606010909140c0d1103040b090d090609150507050a03080f1501080114040b10050c0d0905091807050a1403010f02030f040f02180705030411 75
    0x225041001c080c500b54045c444050b018170912210082048552003180203040c05035001e09028100000010f1001c19242d000680050514108642c9010f0720b02e00b06800926080445690350110000348000c3c001c1c6845549002102004000900c15860165440340065909a40d0340300302401c13058807651014040d0000052104c50f040c0210350544503080322803000c42c1802c03820107089545061402911210803000110b00f8414400c00040c40d50b034860304072240e80040310408140f000024851901403007010010040302c030300c01c0241e80f034545c002152410058064052040c0c0c0c14005845a440000070711003a20880500400141c1310703041c1d031010340344020105130182c1c40d2880800e11144100c5081700d403c0c05400400100b075652000712400030302440c400500030001c1c450402d400c49014403403200d0740b02d00400810800304910701c0c03855401540070f01c232001021482c1c0040b980d10708903080d952a040c00e540040c040001e030020040e510441c0319040c00d43d006010b800c184a50103080002c20158 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 821226771 1250 821225521 821225533
    0xc03050f15010215070e01031a01022a04060b030118020a0c02130e032a060714031801050a0e0115061b062a0206010f1202061809070201020307110609 66
    0x462030001c0500c2900810500c101c030064912604650b0f9655400d50f44400881c4420b900b1200035601402841d03140800511807881d420300e400300107174840d448940c1e07410f40c000070300210074144074030050f04000300b54003d081081810740f5007485011ba03038428010f085d98407a00454920614841d4001c440c0c001c9116565450f4206040e424030044c01c4d044483c0f50101a19403a200300c01210400141002100542c3c402c003100c0b100301800b09440365241d59411141d0081010060001c1c3c102540e898072403c50002141c0c2da54074a0540200300d0003c0d1805038181d420708003400204103050b042503908400900003000704c45050b94402c049040548112004502c14506441500e2188100f1119141c050f400120310351150700501111580c842c842d0641e402482e20900c01a01d504114083c00340c207440107a9041c0504103039a0281c8000e500700024032800c8000b076516844614024210181203015200540c43c0c24107050280c081d400440342000024121007078002c420000103441d41c0241400c2c006054 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 821228021 1250 821226771 821226781
    0x3070302161a090d0f0b1501020708030a2a0f210807180e0c0703080c120114040608010f0905010509030711120c10020303070801050604080c04050718090e010c03050f 73
    0x8150300311103d03d59100440400355800329200340868a1664401d10008049260903d600610f410420f68030754115404804144240ca0780001250081501402c102c1001c2700035425021103104201000e600754030100f010102040702031511002c44501c5104414114205030b03444c5e07103a040d040110100000c0c590004140082e02442004954190807940700124a880d0314240a000740107460420a1715000640502071590000c40541c204010b08582c51034852102c1d8070200f4800103001c1c9450300740c1c0c0b400c02c905081c0d03560390200e402412104001e0014030003503800d180051a41c00710586155081c0b05c00a07030505c2d0080129903000e980300c01d591400b20b8000341441b4042441400511003842424400380c80c1780c0d603205596003071964940c003c5a4914100f00000c2c06402d042e48110f000364800e100610114134085004c0f802d0f80c038180d4000560765034404084402c1c0e1050781c80c0c09240d08100101140740c1d482c54120807039044401000303011241041d18210704540e422aa0783e10a010713942c001ca0 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 821229271 1250 821228021 821228069
    0x8060103050606130305030910030209011403091c0305072d111207080703110105331302090a1e0b0706060915061e1e090909050307030216 61
    0x80e001280905404d00340701020456010116254206403075641c1701040c03100c0e1078546298201d02e180d4007460103500300740759070001a2062402500850742c000c2e0110000e00390440401c2800c0b00300e80d9041c03c903075040982e10300103001050207848107000500c1013141810440041d45031108004450454140d0700d41c1c201e40c086400f8080003400c50101d001e032240e40d10b00c0c606042d0151900500501c0c0c180c1c1d032a1142e140c00342500703501140b501e4859041c142085107140184054000f40154032403000000c102c8015511031f03003084c080c0701c40da1006002c804000c8004503a400380000450689a810b01c458a50032b1020f4968500007024031007580c02d01003400000038003806003411601c03d200128280b174469042009540e01038000041e40d107880039013000041c0c0d001e0400021500700361000701d080d00d00000001d040d064141141004181d43e0030000f140d8a200785c000800510030b160b0200078648442ca007081d00c1e507110003000e80051242888641e0300c02c511443c5102201d40d0b00d01e06e1204444450104 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 821230521 1250 821229271 821229281
    0x9010c050307020d05030a0909060e040f02040e07030b01080708010b030709020a020a0507060e04051602120a020708100606140c0c0405040618050f0f010209060403020f0f061210050d0308060103 85
    0x215103a000500c840c90040c1c0302c6200905496220f0b20141d6203515107400c0c005c1010307842c0e5202d401110f05205040180c0000d00c281345400c941c00070400702d0020f0f40d50002c9400b5214040503c030091081090000c14048414000c5c2c0c103a946001c240c0d95855600c038007a6090344c1300c101d03895501d600050805c00124415034000c0018807294015a0764103119a120241400601e83c407500214a500b000000c4070b00d402d10031245c0c031481d1082c10a1480d10140c10082d951864410914001d950006109610340c1c001c01102004054a804551074001e9400315100503025511817000860350f4801044440403130f000c00d8540f9075603c000204501c907001020000503100190060300c10550394004411208c581c5468190480c0c000d10003050041034030380d0344501d4100300f001c82c56950392041c040e03007520b90b031141c040383c0869804990810402051031700040c00080c4002242d40d00030000200e9480342c0d0032520782503114800c40c0c05522441c0359260706120281c226514000c0c0068000703c005980366000f6405 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 821231771 1250 821230521 821230523
    0x4050913030c050607020105040515010b0d050c1605161401020d05210727120b090c0415170c01050316030b130e100905060103021203280806030f0309010c 68
    0xc0b030031074242c943e10b42a060503c05e41e20b07800140d44803000c20090200c00c1140b240c080d0703002101c1030559850510009180e019441015001a440b480440c02200c40442684d40c5040c4483e05d000380803403145000c0d0f030340e120501039042403201080400107102260140440d11040103070003a0090320321440c2c0468007503000d030700114094641e95020400d03000303c05102510489003034680001c110b140c0100400212801e8000b03490403010135606114860242030380b000078651286e040c480030384a030001d20f81030117044507145070020320b003076494011020303048214403c81e084186080c103101600b00ca0941c5480303404c545035000c95030400102d00c0070358030003840501c0006549030000e22060440d0014080d00645103d010041e919074030568030044c1c0506c900c2060404801e000c0040440ca030360303100c2c1c4900c03052101911400b81c0c030909101c80b29061003140e00042c40005640020740e590092072071070500ea082903c00144d048070010b8101e00b00002c80040515008008504208420b001100d415504441c = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 821233021 1250 821231771 821231777
    0x406181208040e0c390f0d1803020d06052a0318240919050a06110f0d0c0905030a02010c12141309150e01031712151003020405091303 59
    0x20b1036008171034030081081030910010702210249001000105001c05880c6a00345c2d0441801aa4813110000300d01210102905100e0070b1100e080606035185410303030303001a4201025010620070005540c0c05144102c16403102030050f0391052608102c04402101d411150710400c2011840710003040240e00740940c400422241c070b2310071900110a1841510450383c60b00207140b01400f460747e50a00c450181200305e02681050301e5000c0e114169503a059600140000f0f607141000303607606055000f287c58459000054607950007032055460020424003082c800000d4000c40c020440d4035011881095481c1c05940d29110b0b100a901c07102d61040002c1001014880013240700300180407003001074482da00d00c1854000850345071802c84420350b4501d001c030756141420344a003800194400203086040da900b01e442c0824280e0308c07440700e1170180305001c0c02c1c0c0e42c2540e0f00c004004018040844042c480041950540d103442d0f1010410340a9010b14000c203907020b800e0000141c0c0c1002e41d20069080d0714068a = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 821234271 1250 821233021 821233027
    0x11030f06011b0203030c060f071407060e0f0303150118050121061508011a120106030b03030702040204030605090d03110a031e151e150c05120406181208040e0c 70
    0x3d400030f4a03550020f400881140c2082040040c5c0b002e9802615500001e00e080c64945140f1907a80d4070b409125070300009140070fa50300e094020005041062003e01c00b00b00044070390303074240b503403501745081400c84507940080c841418102000440b0342503081203500c1a1076402c0044c10b110201d064030000004428020b5580d00710028044002040c0748441e0203468613030079540d504140800002c05000c031348543d1070103130030010284101c0400c02c1150444030145000519940104002030541c40b81c02d0019610070f001160200a000580c0c0c0418054000c01d41200c81c4100b079920254203460148070304c0d107030703110060240d075154501035003103811500140b030f120880072600c85140501302c1d02c11000d21040050504030070b105804c000442012444580820006014a001d0101110302e0000301c00c441000091800307035040140c01c000c3c1c02d0600d8006251151a50707204e103030041c45403175241d180c0c10019948210005140d0151416920801d4100c910740d071601d03007800c0088c240d000d800350802d90804020 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 821235521 1250 821234271 821234273
    0x207061103010f050913030c0816020a03210f0207140f1203040f14060301060c0f0209070e03100b0f0d0f06060801050114040b01020a0201141308030c0111030f06011b 73
    0x29000560180c843d00c4110714450741084288600c00b4001000d0810b80c100d140c0c0c0000100341c11080d0764003029840100c1c40e6880b210001d81080114030074100035044902d0140110811520340a11038661070f41111041100309403100440e44c49502e401214056000070100b80300401c80680712180782c030700103058000d04c012640007140d050301102007694051f41004c507007407014481c050410030040049440880382d0084003400686648018421901848442d50001080010164503464a00d4000f06200c00364a000e0700080c0c43d0361210b4410070b01c13074040d10312500181e006902c40c1010b240d070007408030101714900005000f2000d0750186c0031340d0390382d8446102c2c43c0000c0660080030060b00517040080384952410358859059912041c81e18400c504069410707500766030019840c14001d0302442c18646030034401903600b85d03d21a0310401508000001d40200c0d014000000400e0000000f50080040346484105010607000684000e001c56440b040403070115071041e00f006500e85482d60280e40780200ca = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 821236771 1250 821235521 821235551
    0x120201020909040c030201031407050301150905030d0c170f0304060e03090d030201020903150903072a09050402090924070302040b03041b0f05010f110a0f1a1b0d020706 74
    0xb040b00e04440100e9131000510455170b0601828a141c1040c032145c3c0014184240f010f01103000500460203c244041ea81003051482828aca000621014080e1510882d40c0c400080c5103107250b0364203880c200302c18844404005180c0c4119100ca80712440084d00316129580d41102038090b200005409100c10b1204440c5943c0c1c0c2d03103031140414880c0d000140c0d030302e000c0c5081c9420544c803c50400140c059040400540e00d82c040b048480941d03100c004000091110300003c190400d001c150751003043d05100002c10404055030115000394003c070b03a280c0c450360710703c285240d0350904031420f00b80402100f01180c6034001ca1025107600010a0304025041a84442006030340c0d0b08110b4082e1511440e0141844122104180c100080e145190951001d2801d00c030000c4c1c0140b00804004003000400b01d002d0300c066000b031110140195000c160a2600101c80c20201d9046601d203010f2003c01170310102281c110040d5400c2c0007000b80100d81c5990810b5100c0082d17000a401400040c0d48040c5c8071b0b0121210100 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 821238021 1250 821236771 821236789
    0x31b040b10080f1501050904050a091712130822030b04060b04200a0518060c010b150c0a0f02060d0615030c14040e1b120618040c031202010209 63
    0x307000da4441480340340c41c503090b0000010140c640c0d0740302c40208540c409543d85c481c04a43c0b400342c058802080c83d84504201074000e1820340c4002c0c0082c5018802035800c0600c0200400e00054051140103064487c400908a1054542e10013000c60710b04002c1a8032041d500c1401e28482d02da41235954408503031340d44465019070b40848040742c01540e03c041c03031003440c07034240700d00d26146464400c200c2e000f2010b103000b0308c2c0e40d110342140b00c2d0900c42c011805500504d42480410400e41001d014140c9524a170b031455406004005005882001c5608585030000f2800c01517a61040040700105451b00341c1d511900c0d0f502080500998004408011401800d44903010301001800350782c281c03020b0141c25040040494108124101c1005a80c0182e80d0488000406407000d90341d9400a90304540c640340d054480303000901055030080d03172001c2915040e0610090341ca61140c1c074196040d0380c0c50042c04160015940c8100c5006002c0c4040c00b0301480441c0c400660f22803100c00b58000103184c0f10601d80002c02c000 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 821239271 1250 821238021 821238049
    0x30103140f0a0f20180a0b03010e0c091e040807030c02030a0b04050c0312180d1b03020a09050412030e0106170703020406060921060f320105031b040b 66
    0x2500301800c00041000381344c1c5902c0c04140c42c2141d01c00040a01c00000c0c54260b041c1e03c0b044403800984086400940c1e150700194840c4801002000042038414a02ea2140e1004480d1031254000034001520030050001e200c2105d090040324003005d503034582d01e01c20150024075068003049a0801c0c18001a1010031040c0000381c01030b00c1c4071501c1d21302464041c2c644164107107898040d4000300386d01d140b40b41041c0155050702c501134160805141d1704d10040388201404c8031006c2c10345514032170700040c804541581801a00c0c000d0390844905038580181900b92102514010143c0508000c5102d40e14400e60000e4044030100b0004921540d407032403091656405421111480d410101c02002140340602ca0138000f04940c0c02d000c40560700d4513640b076100380c0306100700a110070b908421800030444642d0101844001f0f440702080908200c00d404c10380710710b040a0104a8074001a84d8100c4400345024590484400800a01c4980700c0040115469111459100e07003144e11030006450b10350f200d5498400c0c82c = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 821240521 1250 821239271 821239283
    0x40506040e04060506120a0321020307210212040303200f0c10050405120a0908060f150a050303161a010b091009050d03050c150a060513050c030103140f0a 68
    0x140c20142015001c0300c2010b480e5920400c6c40c505c0180c1402c0011504210b5190903043c492018808416564a841d940b10f0f00c0403007251000080041e019006144104c07000b41b40d003e1102e10a102161120403031103a00755105c244611080042c1c00a8400d81250040341c50582d00c004030100c21046d051043e030403060000070040c102165408080004000107005011042c0d420302c0942081d884080d01c0b01c14420014400800004250551030f002c1c151080080001c502116428a000483c0e2081008141c40c1041d40072110180841646406055001a500d0050240d803420794182d0000f5100006058203d80351a80d190700603004200300c0600e1802041e406581c1035494013001700308a007140f00207034040107200d04148184603e840e888400d5100c203038141044d65650705d4455090749065004d19941d144100003004102081c9416000700040310001d44000e40203c079a0035034082518170855900c030059005000400110701c503c68015494507142c02aa40c04000b0010440d080c10b102c2d240a80301 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 821241771 1250 821240521 821240549
    0x510060911031909080c0d091d09100c1b0506270703080904061e03020112020f180114040303030506031009021f020c0a030b09010c03090c060c050304050604 69
    0x2100d82540160a90700418200031403951500003042c03ea15015041204001a51040b55804100d161400c0345c9005048030219200e03000051001802c44c030741400b880500c84a50f0303d0300080032841034135460180d034080c0060140c940c0b4040e5050300401e00900e90008110b6441c0c041011000326012069809010f10041d021610b8000281018520f80030300c0080b00c0c030a4200d07105e0036602e002c00c8a005490b88120f4844e5135084800010b030251103a0741000210085a40402d80f6110f00c00a540b42202c2c0b0030780720710306080c0c00c00340001c080380165110184108001c00000c040d00803030400b19217036aa014181641e030b41c04100c1c00c8031a5900320b60002c4012a556005000c0189800c1100003011113481005002d5140c0680c046281182000030110802ca00d10298840740c3c0c3c001e1013005440034025280a092513a20b04100d00020310a9406000d15440e14400e1140c50384130340206120581c000020001c01c0d890030a04441c3c0442480b002d0303605010510000c00d06588a0f00208000d116810314028 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 821243021 1250 821241771 821241779
    0x14010c0201080727170c03070306050406090206040e0402041a0a0608090307050133120f020f061602040f0e06040209040314040f14040510090c1101020a02061609061218051006 77
    0x1000320030483c804186d114400210b01540c0c00602e40054076070201010482da1140c0c0303800c5000d8000c0b001d00a50280011502203048008181910b204034021241841900803056900d2600c4a0481001d5001513083d9003d100e07460190f031985030000030b030b0701c1100c2c6800b9442c2c558608444c101400c040c540c00540100106100c40a81d1800203459a2060060660700c1c0842011414a100c4001420207409804403829036890304036290108a020b81a00d540301c1c24244e004130107801c444412440717240381c1003600718901c5643c86a4848001e002e002821aa02e0799000c0080e11280104110200324290050700c041030195000f030001001a00313000502c2c00d042c1500ca844042201e4483c0d4040d601c1c001c1000071100300407009508a40400000241c10700142200721902601c003112400c5541c00041c409607826030000d04c0b01d1003007200325000d40e40403883c0c2d6400c0760f6450181c410700740000c0c01e2a1418800310766551100e2038490118250000c0007503c1c0d5521401c2068200b00207441e84c1d03540500f08 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 821244271 1250 821243021 821243039
    0x904060603030906020f0d0305070324061b0f03051b0a0807032607050c0c04060b21041104151508010618080a0f020a05130605010914010c0201080727 66
    0x10143c04035002811101085010a036500c1e441c0d8a264410185c4074404a1035843c00380e4000f07400b03808240c080704008080b0540d40902153303681700f81c1d4001580303030601801c000400c20403142f1841d409190446003040548040f511a000881d4100342080c0100860500540421285251901c180c2006403250b1042c140606002c0303c0e0903c040b0312240d04140901e413414103c1c10755a2007001818030a0725146c0000c80c0601e0103081c45500380d0014500800401d441d1400e0300540b0810b1300505000c3d650004548100d511000c00751001002c6040c18030413038820b85480c0c0c210344d160300a40680500c00a548895421043d007000490a01182260005200b0765601c8110440c410b202d00000c520901c0c64001c0003590745060b050081e040d400f407005050210b60b41e038100900100301c01042e1540c2408660326400040441d48120342c0403032001500001d1480d12198031a038040d105842d00980c01074182c00644511100510381400c02c6440c1d0780500d08101d5900c0b07071000030407620440902407030420082c4 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 821245521 1250 821244271 821244287
    0x31701080708120a0c1434050f01091403030d233d05060708181c0b040203070e150301050105122109060d05060102060a0b0609011d090406060303 64
    0x988010010450b1403501a0041c16009080d41e0280d2070306c0c1c07010401750001c0c4c02d0202074080c560450440070440032824165068160391b440140c07a43d0220180d4982c1007000c4481265621408582c030303010100100342d401c2c05040d002d00702c00340990749401ca02d04500c1c0211554070300c1201204a5845490088114421003554020301800101845c0034540a6404019189402d21500500c3c0b49542090400318511150001c04016101c1034403024249058070f00f0b500514a0681c19100408100550f890010100096400039450101040c039254a41c1c41954000030403d907003602c203901c00002c41d070700040d42113407059500070310316605c07685510201400e40d00183d100a205480030105050a04408900b55041c54251400703a00e04d8811948e00c42080d0082002c640c1d0b00c07590200d018400d440d2542c002d83c0c4200000d0382036030308a64895042c0000c40e14a0001d00d6000035050200b451654094010021801040031640c404a020f540004e40480700c122400c5403615216941081016000705c15 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 821246771 1250 821245521 821245543
    0x302030403110114060f0303070b0108030415140f2d0301180221090a1502040e3301020703060615030c0507050c090c040b03090d180f05040207031701080708 69
    0x81c404c590301e5900b040356a5001408482c4280490744401380e50365020000c5a44a81c1d2201400002d90b940349400d503100d4102d40700b1803402da80e240340106413942c803030403034002501094035003d13040c43e006845240d2035400c070b402d1039103100a40d0104280c41c10003440319400d1169512040c503541c4e41c1404130940d0020003517000c5a03a0706005010400a01c40d0740c0d0031128913281d10b184110515a640d1b14110300c1d102e04080f000d0204400c8022424603280180c00030815603200100c0f6030802d40300c0c07034401c180760740c1c0705000d0358001c0324a91001203900800c244c030312608510510403070740c00f01d4030303515040100c0300c1942c005107018801101c00c070801c03901405140758041d03450506e2070801405484060f21440e050311340501c00c05022000696200558040d41c004d418141d400a840e440d00044843e6180c01d00360881006c119102000d0f41c0c502d0f030800c0c1d100709803400c03c90404103062500051101035084031204600380040341d802c41c20351301e800c00c0f040f60080050720010300140f0b2512303944a05004240f48 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 821248021 1250 821246771 821246773
    0x1140c160602010b090a1503081c0c0c020112050a06090c02100506030607080408030a0908030406230112080c0a050a080d05060402180f031f06030b160806060c03040f06030203040311 80
    0x100c0c2c0007640d03410300b81076104014040c089041111213441f1450032001c2c0e04020124030010640c81041515414000c0d00703020944010401d1201001c8282c60b1800030500c02400100b019a00c243c80341d40e0382c4c10494202e0032071240032400035215516081541d541d54040e800583c0880d61080c880030b040c2c010160400b10550103010310b402e00c2a00180070718030062014040e0000000803500c0c0c40590790210100300c4d00500803a0700c0f81468609080902213407414003640a4941b48664071a0724800500c0e8101ca4140b045c07034091402c20340d150b00300c0c0c0c2c02101d001110b5000b96502003000c0384003480490081842503000541e1045120094002c0310400307080380340160300c140b00c19401c0c403a20341074012600800715a040040c0c001003000a2a04181018864100455220480f000d04154104400b9039108a2603a1019640c1c46200e1210300c0d8128400d50000f04801c0202e0100e09260340100030744803441c01920715294176580c424010f800598402d13000240c0c000200002c1c554010740d00201d080b69a0 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 821249271 1250 821248021 821248031
    0x1009150225050109060c170f040e06041a1306080a0503040e0a0209010c060e2b0e22050414030c10050901021e13050a0f031403121501140c16060201 65
    0x800203243c0c14917800b43c8414800201090801c0c0708010a40d019043d050038225690342c4001014205030350042e104440c116060040894410300e05409010300354860400d00d410180203000412035074000045030944619612a4007090901050241c80700075406240215a111b180900034403c07100e0003003800800c544148080f6000380e82c400600b01d425600031401003007110480010a09200c0440841e00c1d681074401149055040d183c2502020360388541c6a02c440001440180010029202000e64030201082c03103400713103008258084c54005d40078205107612805038040d940e02c4c41d445007211f4022940810360300d9110300028041d4a80c0403500c1e0f0025410004c541c5110b41c506021103040c4550000007182a84180c0388802000c802800000c0c0640c15465440d15280030320704040c042541c03030b466451000c0031060000011100c0c070a00001c000301076a034402c003030350340078200d030003551b0b410050031060b070710351074000c400141814101c104080c002d03100010030a0700c501200b5038090801e69040c0 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 821250521 1250 821249271 821249279
    0x21010f0209120a03050a032018030d0203040e04080a05211f0602030723011802030c0402090901120204020706240e160c050109020306090d1214061009150225 69
    0x1900350b81c018092814041261341c504000e02100d9180b1000c441d180c04000b08071280703000c8011109c18218001a0709440070030042c04002c0b6182d00c504d01a010750320010780045400500020020f101081c40d514020381042030011400311120b501190344100b10182d03074144040c0c3c1d11801c0e0007000c5031301c441d100f02e6503c515150000c0d480b80038803c005031a030650f02c007041c13a03516107103120b20f0040d01140c0000c00110341c404100210418404000364003e105a09000c103180c2068401c841d030716a03000342081d2040e0b1902c034403805842c10300c2508136001034017440710100050041c000c0221404400141240800c14403d404550040c69403142907901301c094280082882034048203941003080c0e00c1d0041030f031000381c204980948a02d20b4000c1d0144980710401640b02000300d144451402d00d55103504d508816800300406407045500c28104100c45000400c0301c40c500800f02d1521817202e4104090382c00e03541c4020126074103078004400e01580009401ca503900f0800282c40700b03401c020880450b001420 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 821251771 1250 821250521 821250527
    0x4060905281b20100c1e0905060a0201020405210c01081519080a1208070509010e090415092006133602190305040f0221010f0209120a03 60
    0x2042c51540034041004014801000083c904030940081c1d003003210322084000c1c2e009402400603000450006004282c1c0f60340b000046020391100724080c0da40c043d0310900306410088c05a000c4084202559400c2000188030707211070f00c82080ca101000c0031504483c5482000380d042002d0741c0c0d01281000b900408101032010691100d00f0030f0b0105460540f02803401c4046c400c07008006800000a52003150040001c209141829412045d000ea8842075582c507642010786d610300804c81081d01051a05080c00e9490810029075039101d0301030075201c0e41d00303920400c4180454014850075120301041c61000aa80c202c0100860180c040903a0070310f1406050710001206c07112240a404191140b0140104c1d0011544410070702280030400b440c01040ca00c408100001d501900f0f1540c402c11a07003d41041240c0070340320780d52060703400c650542d8580d03c2e1503081000d03000c02400c08000b0711100c401d84000f5000244115116203c0380100140d4900d00402001a000c4090300c0009060380282c500400007a8 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 821253021 1250 821251771 821251811
    0x103090b011a0d0f0608010b03030c0d051303120e2403040809030309030712031704030f1101060b040b0d05090a0203190305040312050a030c0206060a12020406090528 73
    0x10700d01d02e4440100b602c40c0c02020451007007082c008a41c1d4100704160701d000640e50300c4101244c0c0018000c100c40b898046c107068481c050b40c0c20386030894001050340788925000d0300042c80c9a00c12101c1d0390100d25120307600c0f101d03020842d030800f10014007240c0c809105410b0080c141c0c012110800c05005010610344005611840000c00041c00c071540131982210340d44081041c0d50003003900405a03461261140c00024091070510010f5002030301501c4520711040e104401c0138002c0784c041e6030f103502d140800d01003035503022014484992150b60b030390000262546440041c02c058200c00d21722a0740c84e1400c5001c1429204003600815441d00500e25040041c0c4d4002030842c00090b101d4016540c2100e02c2c141981c66018561000d44111803c40c0b400550990203070007001c4003251602c0401026287e00c2007241d0301e03102114443e400c03140215050200d00103024007a041d0703e00c01400411800d4691410005941003074030420b04500c40b86269080c110320240000704e40e02500082001000c142441e8210440303 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 821254271 1250 821253021 821253029
    0x20f030414030304030f1a070f050403060b0a0e07020705042a081902030c0301060f020a020901060e120d05072a050913050a0503030610031a01051b0a0f0606050103090b01 75
    0x48110512003000b924207005071401035030482c1c281c100c0c1e8095404d080c1881031264030011519000031001801c01405511186507921059448505260071652100b00401480510035404dd40c0001c3c0007501019403215184611078990150899070310b03003000e0005035040c07100007100784201801b170704200d5100d400700c500030100d29141c8010591200720701d07890501d100b64200405580000200030000f82082c0045040300d407281e4500038026070440b02280c845000d9000298001091001088660311842c21340b1401c00d0001c00c1c4421071603005c24400c3c80d0106106030b007404114049900d0051000010945000c103240f0162050a00ca4040e00342c000650079014491040e81e190b0b0120303205004030000a910035078000304560303010341541000c1d40c1c4d941048800318800c82c00d51746c008000314441c0c080c0043e1080a481d40e442684212401580c00f60426101c21440c1200f06100c5020b5000c10449090101e029075081c0700704100c1418000280c030f5140d04554189800c00420400066076003d03518119 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 821255521 1250 821254271 821254289
    0x706020309181b0c071409450d090614161e0b0402041a03120a2a05011a1e120706080f090a0b0a05220b09070501020f0304 54
    0x42c3da40c442121401074441644003000f2000807840514800000441d5000d44040d00700945a61402c0020015809011640c16901101900320860a40300c88102c5442c039120700c1090000e09560301d4608400400d80c6d070b031005000c0c0e00140d00c41d00902e07040200800686010700e00351040f21b80128100e0b040e44610380a804408102807203820600400f50320074017024044526208440b200c42c00e20120307140060750140e10903460482902007548414442c011100c6003e4042c0070280860324180815030003800e804001e0003807000028182c880c0c200160f601c000001c5140d80052151404e00301d00310750704c2104c01d00e02e00f08101624111561043d480100e42203040c4404400c100003900072610305040b142040d6090300c20b294010828030340080d0b20911401110300b0201007030780c4400c203e66680103284409418102e401000c1110340c0002d8000d154000081e8114443c0681c102404a400ea42c00200503203801d41540140201c0040500054005010905c010840d511100d45410317241e100b144188400303 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 821256771 1250 821255521 821255569
    0x305090d0e031204091a0103020a0c0f08090312071b0303080c070515012705040f08030c040e040f032007090903030e03030a1409150a0b0102010f050c0c0706020309 72
    0x1076650100311040034014402030440d143d541e0703041c410340a400b1801c40c210060070f0300141804254424801e40740c1005680e81ca00c211443c554884d000100003540c410348083d1010481101c0700d031010800440b4905040b40c60315512992070414000c00591400c1300c1c4061382c2400401c201280d44844070b5900904000205503a038601131a10625181c0108510726120180800010303151070b6440c142454946030100a0601c10812940c1808882040f1001001241039082040110301c80c1d101450f44880d8aa000a1500c2d450301c010201002040700c0442d03402101d1440c09080642c4481e48075082c4e01c5030301414000c2140c02e00300d070352a90a01d00601010071341c2c440442050601c250081c2c002070440340c00707403030352400d0105074040903010360b14040900d003c101002c603070340483c00203034609900c00c0d4904c0b1404035142e241094011f0b10480211504546d02c5001c00024103030709100300360080454900389581e6006045005007400120791001c0c1c15900f09104101c19500c0d0310010700355001c242e00503030304 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 821258021 1250 821256771 821256797
    0x1b06041401021603050c0f04060e1f08060118140f04080903010609050903040611030f0a05090114131503060b030a0c030603080304030804051c020a060b010909091b060305090d 77
    0x1241c000d43c2401d00580401c907080c00010301c1404103a44404110a840302c8501e0b078185001d000a07076134184160209694003d0014600c0000e8821001e403116100951000c002e64541c810740c41c02c60f080c1c00c040382545445012030010a40362141d00603003c0481700d903414034a46031003944441c07040148050700761000050941c08030b640a500c048040c107a40c030010042d60910322401c0380d481d04507011b034102061a50555145041000064130600c010707603036030240380c074035511811101a0003501f4010305002070079484502c00304251016290007a00c04d4403d000c01c030b14040d0246154952410130b00d040c10320f0030f030090144d410760004880d80184000c0010400c4010214124003c11003584043c050110210900c810140d00a504501642c0110308607003214212030149a00c5061150196000da0b11200c1403d0014903150082e240b9120141044c10b80e40343d40342c20342c1d001e42d0041242141e248645c20107924071142901c00200240a2920b410841403400d03e001c03e070781d66500c800e5a024081403050ba44 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 821259271 1250 821258021 821258023
    0x509060d11041107110d020a14040f05010915050907020723091e070e0a0e10090213090f050c1b010216060204030506090d0816050d0c0207081b0604140102 68
    0x803000c1070280040110040201e00c050941e0800b4100301c0e041400803103c0c204901d07040c2000074600340c0042401c104075140100f010035059210341c01076041a05c034541d0b1000080c042c0304460081180840c0440c044004c5403013000e030200190081403040c0384540034480f0480d4000340d07020903100c21042c480c26078800451200c1100c105449034a5129007800104440c51181007440c6c441c600489404469075224001d050301d00c410000c4415801644000c004c00400c2c40b0310300c48540100046d001a40e81035111088001070760302a0750b2001c41540c0340c8204000c00d441ca440f407600705280d200300820050804909601882c4100500302c0b512903400504041070803020350480725030403545020101d80450034030701000a50000d00c41643c1500410f0005100c8220104a4940340c8116566144071541c44621310b001448030223290a00304035080c8150181c900c041c0c803505013080c4240e0002c0485504e0512484d15108449400810014040100e100d0580314013040d903090f51004000c2c100c60a460800403 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 821260521 1250 821259271 821259293
    0x6072a02030a120f081819061503080c0f01141f0b04030303050612060402010e01030c021e0a110a031a130b0a0c03050106030209061e0c03040b0408070603060509060d 73
    0x2d850400d080f50401c05050300003940c0404020107071900512565140c2807580240c61241503202c0390380100103000d8443c4c5001c0082488548101e8001400c0c0c505500200b0b10010a908100c408001c0000d481190400410041c01c04a40120081c410066015040c0300701c00b1001d400e0384984405a040e801c111500c3c40360700e40140c40407042840d155a40e90030002c000d040d0540d2020301869950b483d0a0f0702d25004100b092040d0303010303140e40e501d103c0c0c5c0100440050400010034421030141c4d40e40c250403901205044200ca9403000c00400158a0303500b0151035110ba20f01000e48100c0c003403881000056120300720318048138014010810659160001c0600c0144070143c0180f039000010b042003c1c840d01c0b0b51001e08501115901000329a0300c44d04154101e104071094643c0c4064184901411801111408404071000e003c02c2070403d2910396409203181c00a402031000400e01003800e01501d141001000c0048c25180780502140703140c00e012030741640025040900402801d001c0d202440b0305c1c5154 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 821261771 1250 821260521 821260523
    0x601110a021e0303121003031713173a060806070f0e1302070501051f0b07050a0803090304060f020d050708090307152708060c0c10020a09050306072a02030a 69
    0xc04603c6d15000301c2d102452080e500080700030a03401100700f6149200c607010b0740d219a240401e09440b103841c0352100500304262800ca80011a8104100346030300030788038200a41032811300e0300b4203411040305c00800302c425845441080a50701e842c604203c1050001041c0d60405080d06002603015000007046070790513070002941e6041640c50603191440340c0d559004146d110301078002000903072103e0500103d264550880e468000c40725840c1401420703045401410358620503012a2241e008566400c4c0c01c4d0b4000311201c0400d40c02c00716080011a401412091a007522880541500507544130040c02d170b40612031000d0040300d00810000c4072a201004802c02030b05040e60f0324801d88440b030400038032105246c1c00108012400a100082500ba419140020345031098081d08aa075129401500d00d5000460103007054820b030300402140f103505200a003403103881071307031010383c420704002c01e151911501a001c0020480100241d003810040e1007c07665a0b02d41d10400c0368000503450000a15001c80400c2c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 821263021 1250 821261771 821261797
    0x71b140f060a022a04140a2910020a120507020312031b210c0d1a031b01051303060c0e01050a020606012610090b060c070303050a03061d0601110a021e0303 68
    0x4001c0c50f42c2c002c841007070f8887d010707031601400501e00c1c0840240300b8180c40c0101035540c0200c5010084686001410307840260503031320480c2d00d003000c1758031404805440e4101c2c40011801c00140b00c019400d0610902c0140410300c2401ea203181072a01e184030041000059102a440300851102c14802840c00c030300c944441e02050030383c254106442c2900155110b0070582c0030b52403a00c0c4680f15040b140c510046210780004003d0012a00039250320180030304e040c0c079024104a020040000464481d00000c00035502440700080c9180001d0301c05400d007001d0701c01113410b125051045036541a400074030039900280070301e0510004401c20140c4008100b0a90b422040c1450810410000404c010380060880d142480d05100800042c03003444190311030090031407000d0b0841c40c0e0600c0824000c1d07000b0041d01405e46030020742d156a4640241c02c07100000b081907000075204007403240700e69014031032000700b540010103414a001a03030f0000385060401c0240c481400c201c1c00044d0055130781403046d51001d4102c0a = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 821264271 1250 821263021 821263031
    0xf030f180d0b0f150f0d2604081920130e0c0a0b070308152106070f08010510110c04020c0d09060201060b090105071b140f060a022a04 59
    0x40b07455070380100c08440307210701400c0540000b42a844002d40a5070300200103060903030102c1e095011b11014070928a420303181d1452043c0c1c0380c140034002d944020200d540404d101d0b5119400e01d50018280f0202450b8022a031441e603c1c4c25011945c82ca11003006a0400928610900c0b1f001e40800c144071007200b803000c00c41d40f4010041c4408540131607100f0060000316000440582c5500451002d40990040034001981c2040007c02c09802001e8a2104600003804183c44129a00a0849140000306148040c1e0010000c0c011600d400041400704000c050a04165540c10007010030f83c89002c00c9450350030043c12100381100c0c202c041c89081c6910001038015541c418461300b40a90f282030300c400c1e00c0b000400041c00000e07070318418410300040e24444803869140c0040301004464a8019100540702e2102c0360309800300309100b03001344034018280226a4600d8406c80b00402000700080e8040c1e902402e42084000007260b400710304c2c807044100e01175500c841480940441c407500c5010032500c80d0072520380 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 821265521 1250 821264271 821264273
    0xc07180906060503030a020607050a031107060f05060405070e0d03030f11030105120d090e150316060201180b010909171201091a0306040305030711060f040c080f030f180d 75
    0x9801502403140102000e200712079503042815900d00c5003480100042c1c0002000c51440c0e8400d50050405184034035000c9501c48242c040300090b903005c840c08a44841d80e500321149668070501403103500c0780048808010916040601030030081019030294402c0c4100300c41502054000c0c2d01400d611088407500700910003ca22003111903600a001e6544a408a04180401001d00040240007280c0640d2000305851800d0602c005242014018055030b0710700c4903244400303483c2000100d6008184001c207250b90380c81e20794040e084030640c4000b50046070005001c0c00100f55075007020f9045030b41e02c3c400003403004544d04149814009030107991203c01c0002515400c881c40d101c12081c180d40310001c0801454001810b01880c070215421026003640140d400100401d0003580034540c424800d0400d01521100c60300ea8604100c0100d600141c148000001c0c84107001030000c900d0082c110f004010420100300c203180607640c0c01001e1000c1400f140c002030710301c60554035a60008060901030402a44a101c0d = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 821266771 1250 821265521 821265569
    0xb030a0606091a2706031003030e032d0a1a04052b0804050c040213081501180507020a020a090c030b041a040908090d030903060501080c0112020c07 65
    0x140d8414100062284400032412070940000403807a600c803020050f1a208222525581c0c0300c0750f1441c1c00c101c908114900f1a0b1503154800110700c90010103d00701800b501390300d07014010441d41c000d80e0b40241c0c4810301c03400140c1c0342007808400c40b50500d43c1842c0322043d035100d160f203407103950b143c002c1000c0f07064400080c2e41d512015480303000b1481141034480c0d505107960b50390f051403802c40760b00d1004540216020103080c040e03882c0a030440d000c1d1050312181408900450181d90016189054582c881101080000402d1040704000e0340c02c01d01020265243c40d248d42106031840c001125070035515008110310034000c014020142ea030140550f260140c0d14085080108014107001e0042410600c6115180c6410300c074844540c00070704828914043c1d41000d10006010150f8101c60b0314104102c1c4045d41d960325010a00000d102c5d030384040e055811850207805554043e0700c0313504a40c0c1300040c0020719a820a140030740c0d08040034401601e80840c010040c0c40d2032441e0340f00c41075001c05d0f1002d40e081545 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 821268021 1250 821266771 821266781
    0x15320708091f05130e1303030c020c092a0a02071a091e10020a0b07050a0903140d0f0e220207151b0801030c090e0a080a080f011d0604150b030a 63
    0x44100704c4966a502d50307022208040854106e032102d00112032400009001e81e0000000b00410b1048661103451580441c200c4001038541070440100e04032680c01400e40072103a28021007900b1207030360030302c54101d40183d980c802c03d01410004e007800180c044104140f000503518626801880e0b2070804250780820780c280c49590403101d00510201030b80382405030000403c0e1540c2a0f01c8000c0480c240d84044088406802c92541300c4d0800407413001c0040070646508080001428520140850200c00440a442c02c001608890705002c00f0710b000018541d0798030301d42c1000341c04000160842c0c0b084107685000030f1280c1c0304001c1002c41e464541d01c11783c0c84194890124400e420b40c55510781c281d030034000d590700350b0244002040e12041d0b40c01031002c1c0740305401c8210300f62800012501116510f90780c60741280c01004280c00012410000c20000c0c103448045a8010541194a084c221641140800355414003d10550040d0780303c80c2558507500d003042201005104010340c81c6e8a9060110740c50307010340 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 821269271 1250 821268021 821268037
    0x50d0306060318050a030503060102010f0617010b010c05070e0403030e100e0c03071a07050f070303050d050105040e060a0b06042c0a180312020415320708091f05 71
    0xd1810315001c1800f20801007007030849400000428182002c0d44d0708035800d03840105468115502c484071880d0005580c000c002c050180c421200003d035407001151401c44200c2c6070940e0400072304c0e90018010440102c1d804041e41e0b540500c80f1030555590a098010b010040c402400d20301c540081a0514031199000300c5202d800d1800703442001e50300b0002c065507102e450240402c51024001d040301c03410954801050002d01c25403c0c0d8540c0c40752300e00d1182c28503200c0d0f80240e002c20700009203840f034508948101e502500e4101c50801080ca800b0701020380e99070340201540401075455203401d007680d83d460107590040202c0c0a148607940c2c03010014004081610b00207a401000703120203d03901080600031a8900d0041c24048041c6a000303071070480389900c0003000036140700c0d82004003260032030010160a0b6600c0f00340d00c84112103407480c40c04100c034440b0401c101d00381c00c950706803d4409403091001c0f2194a50002c01aa0325540f44100081d0051000e1444030b18480e003080c50b6a040c80d400c8001f5003244 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 821270521 1250 821269271 821269277
    0x5150705011a1c1b0e191406010c02010908010501170f0109240f0f09050f060906070e04060503010603030c1211030d09061e06050f15030103080313050d030606 70
    0x21602d801210b488501c8004a500c0d80304001c1e00140740804244002010443c0c0120303151007600d20301008440801c00c5070b4000d1643c0380c190000708a9011405600a0070984c985c800401010316095007420006c2409424141040b1000200e4800e5a115038032140c041d0400700001c20003541c0da00940e0602c45c008101c002043d001e0341081da10100340621854464a070403086890040c840c50600884200380d800f9400c2000755245000c403030315003480c859800740400ca91000200d110080c00c246140c000000140031165004a00304890850045406138101c40a1300380790402c00c0c8900002000703000c1a400864066103450800000c2c5a803118000114074060f0342032034861801c81c2030440704603000302c1d9044a1940f0070041d02400700140d5000410302070280c4000070315410600361450241080700e02100700340780c458105004a00d4102e1b425042c440c0c0c115014818901c5035913030001d00b4001440003500700d000c08000606c20380103600c00000c1d070a60007026220103d8811a0180c0105036a010321400 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 821271771 1250 821270521 821270531
    0x80c0309032116051305011103070c0602010504111f0e03070e0a0b0f0d030507200907170a0612020d02030c06070b10060306120b0a061802070614010b0d0e070515070501 74
    0x381d81e02131000c9401480c90f0f03403d508216030a1000540e003503e008804103680d84802c00555010805900420000d465240d0010480e801c09040c01c1e4041244007002030320419289910b422075642000403c0810750755400d142c2e640051040000707040442c00e5002641072804074040014010b00c940c0308034082c107001c44169040164403402d200122501407001000b00e00d00f0400c440100303441c120819400c200e14a040f000030344907400030400c00d4106881c117002040c001040324101d6030383c460446034440e100c100100b00701d616108000d030000080d8400a4081d00034620200150b441c1030150711410b1001900c42a40d405617413804000750441116400c0380d4074012900070a03098840e0103100308441c4c0c15806540703504616255100c00344809030070ba20341c8541c0d401c00000d45200c4a041100015103000b00140c413030441d42401000e40e556224010781d0305485800502c00d6030b0222054603000c0410344800180304825200c800e141c08425081698040900b071400404003c0d80030003400240e125800a00c1 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 821273021 1250 821271771 821271811
    0x12c060c07260307020d06020d0b0406181b1709160f0303030e03040302090c160c09020a0210060b0406112b02210d090c091812090303080c03090321 65
    0x240321300900380d009620081c101028400700380103170003401e02c0242d0404001042101000090200c90065010000804510703240004045c02480384000c0c9994400911800c01030349030009000300d005980c00e8181c0080342000c80e02d43c0e0400c12102442c06500c604041c44c003078440c0c1105203003440d80d22007100068100001042d00b22804810350303040701d9018146050075110001d04044a070841c1030b0604415a8003002003012584103000d41008140c0d8500050341c9441c2000f000341061800d000c3c41d0581402d101d800c211807601d0700201da0858401e89048801030a49103026414081c02c11269a1602e45c0b00c41415030710800d003807103100070b5440340c0c003150050400a5001d40584603024103a0141000c280712040fa40d0300c0507001140994482c04840fa00151203241a00c11503c00049980100715112041c404010001003440038818140c00d0441c2800d256907030048c074411008000e003680c0600400440d003035880400c10b9a22901100303418508800d4600041058210210b69020310483c004c41014 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 821274271 1250 821273021 821273023
    0x19090b07180906031a040f060614040b0307081c020a0501150611010b0109060302090103020d06090f0c02030c06430e0a0b090603040302150a0603020906012c060c0726 73
    0x1001c807a4440121541305480c00e14411713070000020401d035982e8500d0301d250b00000b21076103e614050a070764021000c030180c045041c80704840488030720740d009600400081c0706c24400015400c05a082540d13a400c3c030200e220104905103035000000400d1903081021640080282c5110802070b941d4907038500c0e00508210300c1d41400c3c3c400c1209400d0109180c0c1c3c00600ca11842a0001c00d441c903010f05001d0315004494403100b045032000d03480402199941c0054035030109460268403000400b80c8011400c0c19001d844083c2c035080c020304281c1034640c401e1089542c03600c0840600422100c03d041d07814900e0103000900e03031844821140000083d0b4940821081746c503189a0a0041d19141d84260f8200040750092002c1070348003500542c1544030706403603100c40d45100000640704d0300e40180702180a501e144180050803602602081c14020150400503200c550520b1b80000103880481d0074040321008400703c0c01d43d10440c168100c1d0fa0242c01000308008009420b0701c92400c4401d812500c1042146d42c4903 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 821275521 1250 821274271 821274281
    0x7030311180108040203123105010206070302031009090f0c050109080c130b09010f0311010305012111101736011b0e03010506010305010302030619090b071809 70
    0x118103202030049400d589944540d2403ea840b0348050100d40b01c20300890f0a015075500420907040050401d02d00c091200003188032000303241c100c62050350304803505000003c2e40b2140000e024008056010000548018070940d034107004007548401041082140d045c04060107159840c15078821005c5000080c00d0351140c02ca0070b048604000241c44401031004c100700805081c10b03c071001c69516040c0c00d2545079944a000c0d8000c24668440c00b842525501d07101c000b030200501b52905141c41c02d401000315007181c00c1c1c6050010034035101900500c2040c03411400d1110300c213540700d800c81e01c80c10300001e91640014070440041c00158255880e655509248d400c5050104103a030360080207810480e00e181c0e1010f81031541034070700c0310000c50b07654003c00380300002c0740d4000503080000e4003802d02101d0740d080c00c2c40780e190031a801b0300e801d01a660451f00070070354520001e09406004500e281581c0016411079002c110110350280103030081c0e05007114028a9042c406810720384030000c280000071f5104482c456 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 821276771 1250 821275521 821275537
    0x2041707051e120d1107090209030d0e1206070503090c060f090f0a0b0c0115081c08060d0605090a020117070903170405030123100e06041a0d03030207030311 69
    0x1090200b5a20b02d600c40c1c000000c1c0c0928542000f4684903050f0100424001418049010b0744c0c1c1c1140841d984107914036080706a03015030403291040102070f50344e40340030032000942c0300303a4100a08510b9860b80400c1d8488403020f0241030790b0250034148401260700c41e00440c0540340800459203440005003c000441c8140304480da034503501003021070b040382040c40c86001040d900602008400e9a00d8480c0c400c0c2e540408141007807655505865020310310070712142805800514010100c0b0340300e2107252207041d10090181d60902c0b5007580004c2896981d0340c60707940500d500190030b21441c28032601c8a56203070b001c024201d0101d521940c11806000c0c45e0480503101d0306480d65280e041e0761440e11080400090300101d0048040104030100e0f080e00d090161944900040090402c621078420700d075103c0e198094082d40b6480c000d41e404100e40c010032840590003403000c603000104d80c9610f4800c2420400d0710b801243e041408080710200303054140d8042c240150094a05000c2040c0d480311165480c861910 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 821278021 1250 821276771 821276779
    0xa1202010c0c06050a021209060618010e0708100504110c0f0a03170c09060f0a0914031f06051504031703011d040203010e061003030e06030121080702060a030204170705 74
    0xb14080401d0860300102c1c0c012915207001807a25040041404040c0c808407403a03002d0b40e011806201280c1000b590409501c0e0024500064a5050402d100d1a1280103001c2c401080481c0021942817603162840d18001c06004108001412046083c0b500c240c00800c051001c81c0101c1c3c00d8201003050100740034240b81d0b40740d61007001d5011000013110b4208005084400820402c0c003200700640c50307640080122715000800252180350915000b010202a90131100d800300c1c0c0c1d02203105403034600240315101034035214040c503030210383c140609009104540c86658000c10400d070901419810000034015240603190000250f80701c04c108021034030082c4200e241e0b50700078814905000140c06c1d0910f801500c000c0002c280d04401c080a2851f20505844d0800c0c10b04590104004268203c00306156a00d019034240d421985072116490100c00d500031000460691589144d042000d420304841c80300d91300804e490744aa040800060081d00302c0e00860510308072100d10000381420000c0d4020403100018 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 821279271 1250 821278021 821278037
    0x370906030f030309060f1508240c0f04080106120b060409030206070c1113150f080307020103020a0c1a220804211208060a090b032509050109050609101211010c140a1202010c 76
    0x50300c410800e901c586046038072f0030000d2001040880302030280800a240d6038401043c1007082d400e1454a0314000b0b040240305614000005000a40100f030495100d1180e0070007000301c4103203051420315031407105052544101030100420741020b460b0b001d0ba00003e075241d15207590039115158a842c00304507029920080c1d1042c010000150311a80040c180c4040d136282581700c0c800c0c942c2d16a45a612035002000e11325292000300490100488880100002903075400d0f161803807242c40e0140544518003960001c04450700710600c03a21000c5207009500b550004507008071060913a0014410582520241d10440c0e42c000700042d0300405014450030040003e0281c18041840c20040d0004141c1a03500070514864400020f03956075a44101c900801001002044500d0048100829010300401b808608040810203105560f02c40440590565100e80300000d0b070040c21005070b07962120640000d20400303112482e840100408540c05403858800e8050a030b2007210800300360700b69070380b5106160020b00e940d = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 821280521 1250 821279271 821279281
    0x3030608060408030c03041103030a03060501260118020f18010e010e03030a0f1e110706030608070b21090c0a050a14010806370906030f030309060f150824 68
    0x100d004640007445410101007002300000071904607080015401c0110790781e00020003031541c2008200c001c03962007104642e40d144070194211a6003a041c090b404414104041d81299080e25504485e41c010340040b005131110941101513014203900c0030118002a21503a040d21194054502003440020003005181001b855100c1107601c140004040700c2041008108080741c618491080d92540000c1c0d070380c020800c2c00399840306141041076440501010720b0f08404025450000c0707000030646d41c8850b070071aa240011083c5801170b400b40060b0803004c481d0348017071000d1136000003034082c0e0450096036042a031307a50303840402c00c1c10110b9114811b11109100040706072076200c1c9001680c070050041c0003409a030940300d10b5280350030051820713541c0c030002100303015a8640b06103200002030075114024001d850071a61541121083c40310018141611481c000c02048203507003100e000210b4409081150400242040e110014a03101d5070100d03010b008406245041c004842c1441800149000c981c59182c0c = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 821281771 1250 821280521 821280541
    0xa051509100e0309041e1a1e0d1509060608160302090a06051509030d0206070504170f01151a1c0203041a10051305010f1a1c020409060605030906040605090703050105040b040303060806040803 84
    0x20b4821426440440d520321300c0c0025442662b0440010200c000015070682c00349400c0080301c0107900074080c0c650001ca44400c10546400d034200959070b05455011064989501140142c0041e4000c1c5500060f2200c100c00e0000e00d080241c83c03211401c50444100382d14802082c3d0316004250380c10000194108418032450580138680c01b01c0b48003c03000c5402c80f2240108207800c54010440c0076a101c1051802000000e0800369030500001d200702001d0b02e411604032007903012280e9040000c000b140c012002074203016030903021020a500218a01d01680307481c4220007a424441d0003902c1c8120a480b045410f0f03c403d911615060354960010b200c00f170750800c8850340c54507005008a0b840000d04120011002a052148808824048001507203c43c00d040440c1705903043e5820220070030105008204244200144480c0c0280d00700d040001c3c0c41e125026403908201d00d581014005608280910003001105001684254001d039810400503490b01402d076140c0c030040d100034104042c1480842c4d00011 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 821283021 1250 821281771 821281819
    0x14120a0b06091306060305090607270513060e070507170d0b0a0f080c0411030708060a1a040f1208030c0901030612050a051509100e0309041e1a 63
    0x2000410761410314501e10006a0242c41080c20b2100d1644c0300c2c0c0c410010705415004a80d0044d207020003500d540e10b81703220014001003810512007460030b0301020542491449240590150801034040e1200c10104450b10020308024425100c81086810000d03100300c0c400c0c0c0549006617809038051a0083c900d100c21a019084044d030340c0c0c04ca541d56028030030f0954840e001c200041420034071903802e59181603c014205149122a6030046003464000e43c0c400c04410204c83e801217041c01c1c03c01d9140c85060203e6103003640d5420000080d040d103800d02d202c0c5460342c0040c00440d022880c903c0d03800e50b00c1d46e2101c0c95290309841b0040a50701c0030710109040c5007061000c3d269a940c1803400084080e03940c65241501127444d04141d5030b50300882103800c180001400a0f00029800d5603d011160034032940d400c0d603407120000111989030791020070440b0000244120303440010300174428001e03c440c6040c1c0a03a0301804504410f07030540b8050002c6120703104c0c0000382146e8200140500600c11030041003e40e504 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 821284271 1250 821283021 821283041
    0xb0a09030e0636040e060702210a0f11060106030605040e190b0c160c03060b0301200c0a05011a01020f0d0e010e04020d0c020c0f0117131a01080a020114120a 69
    0x25080760340741050b19244681803000092000034151ba041540f400780c1441c00c0b00660007040c502c85030b10700804003185012994215000d00e4500c481342900907040740c401e43c190038020800c0c0102c100009140c1e40c160171820540701c0c2142e041119040450005659038804a090301003500d0f0380002002040c21294030507407000c03006040c145042d903072446502c81c0340361034481200e008252590a00a00c0882c2c4076044140505600806c5140d80041e1890000011204222801500020065081601404926400b55201c4001d2081a050b5a402c10142503803030700300d0f070040c4520000a9444080066500b8001c0e20365280c5408414044004482110303010b2140398100d80c00b0001005100d070300c1c0c8642c4030252107507400b4000c00d00885081200d082d400001060400c5105100a0300001000c1500c0d5000360403a84540c64403441442c010b8415a0900200910140e04034000038006802050003066903200360385558880c0c000100d00c0500c2c0c0a0104590f00d500c08441c0000c4207003080e41d006036450 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 821285521 1250 821284271 821284357
    0x90305070902130f03031214090a0b15060d0b0913030801090209040912020a110d05030301091515120f0203090a11062709060109150513030b0a09030e06 67
    0x2d68503481c02c0b00b034070100340d17104a0002c1d81d5488901c5400126100e10b95041c4070340e144034480ca0603c40d1100d80e9444c400c00014042500280225101e003443c81c0013140b00190291006848a02c5211604c0c000d05000310f41134098446c8000151808000300098040a030f45525005010307400d01c6400c1c4025082043e00c142c1242d554002d42c00440d1101c0e0403410f81d090070b94020110705042d403820702d4165507103986450080f00f8405084001401c0401a0303819030343d0516001900e000701c0102078034441c0d081c0d071000d009104030700341c4c501c01c0300d03130040d540b05d804850b0480074041040001c043e40d00328482160450210713044000740710700040c0c0014504a05040051149003091981d9130342d007860f50802042d4049003e40900311a0490400b115480c2d4041024203140103014034002400c0c0140070303400096030401a000444034462002d5101c58000740d070704403800d0103c40c504508050014411840b0070307401325031380820350503207440c0c2402159000341e034039010301403946081c090503041d92200b1001c00900d = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 821286771 1250 821285521 821285557
    0x3003110307200f031209040f230703050f070f05030709030b0114210a0212011806050a0b0409030f030c022505010f020a030504140319080c0d090305070902 68
    0x11405201c0c40940c2c89501440d0040c46005000411000c402c080081c14069004030000501045103502500d19521041c1c80120b620141c0184900090006d00c05440c01510030302d034480380c441205148244901a03540f41009107490309140f003d8246000c035403080000301003801c0300c80300d03c3c85a0003654001c1101c3c2030528145440360b94034103011800742c01a2450221401030078825142c840003002050340c103484461842c15018200355124006100e01034001c81402c05610890030f001d4bc0106800280001c001100035890300d0000080c10058440200c500d0400039600342030f1500d44502400c2c598540c035000c041980d1018107402800030f0200c88803d500501480d90311034804d1160f10142d07841004010350856050500250441420b18204d4046601411001001a0f0072204580581d948032a42903600155440060f140c42d088100040d100c0b0401d041100400c240d0002400b0002a28000e07503240c0c8001c1c05048401121a01c0003030401d078001001040891030710750041010002c005000c070781c = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 821288021 1250 821286771 821286773
    0xb060d06061107090501030503030601080603070b0d0203070324051c020d1b08031227030a03051603110f0903011103011d01090c020a11012001063003110307 69
    0x4122082580241c020840003405018002c1d420b01c60035000d00410801040554115244d0560740c0c0001041c3e28140185600450280d5408100c9400140950050980c2c0c402603a0080806504160340680c040ba061082400320100e00e000714810082c0c9100b2020350452034902000034490b0070007080c0c1418201c8015000140c0c690252105050f8080c410010940c0030944030020540c02e19071140f039442e0000d0016248004c0c1c600c1902c3d40043c543c005407030324a421920b520201c8000680841014400051850242e603055005148600e1015820305007100ac400c0e815400c0c4c801c4c8604001030800200400188122079a000e001c0080c070280001415036140441402c2590081e003290780322a410160190300658880b004034058400c41d0070a2140c1d550302e0301d000c2d5aa6080b440002c2204801c00c46445107a4810483e40c806000039070400c5400d03d13a02c8030941d000300b00c180140e0840911986500003200b01c040713000038040c20891400940152140c070104c50a500c42742d0007a880707000800240c4 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 821289271 1250 821288021 821288047
    0xc022a040e0705030d0306232707020d03050606040512010b10080a060f051807030b0603070e0a08060606031f090c08011403070501120209060d0608030301030b0c1c0b06 74
    0x181c480ea20801c0280346807800c0c202010b140100100ea00c00c101414140180700ca1500040601103c464403c110f5500b0940440000d00854216041030120b1088003202208124007240f0b150048101790240e40300303426540800c07820b446040354003d800c01c404200400c03c5040003a40380304460301d40000042c655441c1c1c8005003100792405000c000054000080c003522082510811000305045040e1199140c5043c000c5010042e4000010000c1c00411002410f031074000d4001a0402000402081d0359141030701000c1c08007040264031a0040010300e40102d1003800002c1c08038000c4400408190859803000ea003401c40444000031885081200d00000404011901614090a02c143c640e25060b41c10025130001030544000c800384280d10007c0308204e036980100315610f03202c400c0203016a46481c0e80001c588944110030905100e1843c00000040c20380e404000b031340c141c1e0300c40d02100526885820501c0c400340200c50350710410310301401c1c4031101901d40e42e00500041c400600207a04109142c4014 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 821290521 1250 821289271 821289281
    0x304090204080106210218091507020607030e1504021903080703080a05251b022e080405190f02120a06050c1204141207050f100c022a04 60
    0x510b001d0391038070401d00205441c025201c2540e806503034800b0800d60340d0b4000603000d407003e140c180d0030005084007040862030300788401e121161000400c4840c5040c8120000c0d510007085504800291401035120845031001c40e4003a664503c00103400d01588903a003c00c1185001100d804290300f02800e0700000040c043d90180602502039100c86080c0c0c6800042901500c400400c04180c805e1140103000300c48002c0340c1825114a180e1030002c0703804440c8401900000c10303603c0003035844000100f00341c03000b01c98040426560072015842c000010000c0f00c059400c080195002400c98110300d81c00c8903c0d000c1141c0f12208640070711852290880b1607004604690030440c0200882d0708840b003008144003090051540020409000038a040e002c481d10b80c4400f00c000d04014510f017110300e0b2020000c1d0301008008190031060748215521b44262500707903990440b18104142c1c030b01903803456413803100c1c7c40d105e0883c00352185d40160040340d41561108521100300e6142c00e11002d0580b45e00c0145854511407 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 821291771 1250 821290521 821290529
    0x8060f07180f050a06050702090a09140f0a1a0705030a0c05040e04110a0f0f051509060a12050903043008130302040609090f020d140303041a0916060e030304090204 72
    0x803080d4030341c200824403801e09040d4001d03509100041107d200181c1711501c0c0640c0c003182000000031400014070302501284542c1640420303d1081188006052401003943d040907403048500824109014000d001c00702d20448070035012845c14800505904202d41009910504500d000b5140030785038001050b000800f6642600c0c070002d4000603070b8050505122100c0680140c11250404600d00100381445480750b00405004048481c1c0541342c482c003080c2a60b68202c4024161511940e0174680280141880b5101880d0701c0c2c24040400c2c0000000300c119415070f0580c0320701c00304124500c0b004008040c09414090505200b07058050041448040039021000b010142454001c2c03071401044240d601a40241090515000ba850300207003c800480036400d50554000c0100101810f0264010000f203480f5082c0740000000c110821160030741c400c22844a080744001c55480e1740025568950703d0304080c81241c13401c0c1d034050140301d018503c11004008002d044900e0641c440202405903085540 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 821293021 1250 821291771 821291789
    0x4603080901020f0606060d0e031e27100c02010c05070f0f0f050d1212020f0a03110705073506090708030a0e09070908011409060a0608060f0718 63
    0x4106055682c10b002c4082d245100e100109030906000b000544140b1a5030402c41040fa514445100f803100c0900a407501810814148040f41c0e181140e6441c1c1988a4454000c41076400e04140e602e114100074112112800034251081c4442140c00541d4251956001a41400302c15040c0078000b45040010341c1c00352070003516900215247c4041c010602e0074a4000180004024100b40b00a03111001c0c41c0c4002d5810041541010180c5030003502c0c075509000704442c03405d0000403007458400c98030f0014818120303960750801400102207018003040c05012002000341d000403004000940b83c0100105021070003000d002c0180b910b00c40508901c040300d14082070703190051000c001c0d036001c060101c0c030001c01c404d101851416aa41000601e0b0401c0040038500c101210808078099a00c00c4100402a00395030008000f074410701300c51100e06e40780846959809118900c0000e04000c500d00a442c101d60307040001f060b0ba40c82700c880c400341c001c000501060810640300149605900d580c00040018000c0035 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 821294271 1250 821293021 821293027
    0xd1b0206070f022a1c0b060a03020f04110c03120a1109010c0615180f0606090b0706090f0203161401030507080f0a0b130f0b460308 58
    0x41019080000007800e141c00d10260b40c2c0d10036802ca4001c10096011003000c040d248940545124030700f4010f02d52540c05801c580e0319407100441001144840e03c80900070920004ea80d5a0702c81040020a49408000c1d044804c0400a1040d41840e4004501c00d04070030324003a0030288036201851458110155159030b0040070360900c511855240b15001c0340f008100122071400d648940040c104d614031480c001c0c0907d03070711000d9400d045a82421880074201e0a4100d100c00c100100340400545090000c4600a40c9010400a0000d0141652404681401c0ac181d810180360342c42c1c44000700181e81e0142c84c4078a0003407107600182c1d818401c0d0001c02c00c9481c2248015420280760208000d11141d00728181481d080c180840c0c02d41194046500c191600b00f011295a07603000c041c07001e41846180d1942282c0291058600c03514990441401d8141007803080000f182004200034011f01c40d80002e04012100d685042c0d401445407110070140b2591391100c100c0840c005d12210030752066a4800d407644071002c = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 821295521 1250 821294271 821294321
    0x61b0512070c0504140c0a0216150e010f09091e050a0603150c05091e032a0f0d0f0f08070507030b09010506030601060f0309200a21030309080d 63
    0x80210b0018107400d56042040c8070410000c1178060300301a00d40c05050310f010810810140c8204480380c00700700341100c4852001d075070358080344450756022441c501052103040220015486041140b540c4d032495694080440e01e4140d2002c010080b4203800444610b502070b00310300da00c0c818080ca034020385c941d00300021104d02d1410500c0f0980a1018031070f04e181e040203081c01c0303001d0f804415107040040c01c84604440c0c804105600c039001c2c500c2910b0382c1e0103005034030000920504990441d45c0b049181c12070110414155000c01100c00c0c00102c0140e03201d00d00e83c41101c0801c0700c100b80c0004440c0720b506100c5020160707450303c1e01641c0118401301c8185c2e215110074010000c410300110713001400c080007404681400d1740003d86600e414004c90007001030141c0c40b080d0030f911981149043d0b0713821456542c011030100121628510030f010031607004034107207200091400d02980c0c0c455000041844041150025584e0403409001c007401d043e10352803414030803000b090007544140300c9510f082e880103401c01210303 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 821296771 1250 821295521 821295533
    0x90314130b070c080c060a090911070f060606021e0714030a08040803180a080606130b0a0e01050a0617010b070c0b0c0102030f0a050108071206180b07020f0d0504061b051207 76
    0x11750b0301c4040c000c03c424010003200ba6017204180c004e0f00c007041000700d12013002211601941c040e400d40074000c4a0316001d0341050040070b5010005991282c1d0960b044605416040c20114141c1442402c0c2948810b50400c02c5414103006c418902c0c4004054a142040c16101c50465800c940c00081f001d800004d00c10703403001d414081c2510403c40550750f80c0e41d9640742c82c507100d45415008245500034000651851700c080c0059010110200e030081c00b120503140c84c2e0101283c103080c01d000d070900030840d001c00481c5113402180419200c2e8070034160303002e450303081160580385030300224801c0f140c1c8200c8a0700400c0085142c405030070418030704800107031a0b00c0d00c0c602e040801c64000d0840c0780e03218030b000d0050100c1000410303814103942000d5080e0a01c003200b03280600c000d040100042c41d9400000c50080d040200514407a03000301030f107500b2100d00c802107185041d180c42000910f02d0128104000c2006128001c5080c0c94414064100c03003205010301d600c981c1e003440c06812044503020700010f0454100701e1 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 821298021 1250 821296771 821296783
    0x60718090b01050a1b061b0e091326030c0c0d090303020d0f050d0203040602030619050a03020d0510111c05040b0a11040f0605090112090314130b070c08 67
    0xd4018051000992400001e8520b200c2d801d186010021000082c680544092036070b148031542c403540c100055080100b0581005030f49500c9540065801495160945032400050303019290007a040c50f10400c059032081d81e942d0450141228401c0349200403500c0c0d03018078014612030010b1000c03c982d5440e40c0c3e042541041120503c00042c02480101400840d03800540101e1842843c20101c44811b40007038107846500a0540b81c08042e400002040100052500a18080d88054034908060707100410303a840b003000c4501030f45400204201081026161002d0611001e0b03014000340c8050241002100003a515407880030142c40c05c0c00580400101790703031b10492000c200c40284c1006039040942d51840c0075035019094030817881e181d450b10400c00444200f03c07001070540700c071100c4006a41d00000380c076940120310560701180d803d101d550700000e401c2c0981202d01d41d01d070380c1e416080d44e01c499a1417820b801100354510180c2c215000412500602e90051502501412181040038603040d40145402 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 821299271 1250 821298021 821298029
    0x61b1603030e01050c060109021806040f090c0804150515190303120c08060415050310090b0105040e031b010e16090c09080a150f020f070c080304081905010608060718 73
    0x100402c07081705070340c10101c4d805054032250000540d17115001c200d51108400c1c0111920360080e030019001880c0302c5000c03104000c8071414002401400044c00342520f20034011280902142400e0041185130f1456030702c001d901008580008410240b01c9012070100d5030741c2681140b880171810f209000b4585c00080f2101400c0215006022a09068100512854001e05001c1c050390303e600341c401102c54070400200c06484043e00b15420025941400405444502019242c1201610001c00c45080c14050000303000c3c400d40c011890b18004048110580b691809516115503a4000c492090802808480719522031100d02d10303660390a041540c5d0845a20800c05001d00070b00a10400c10701c0740c04602c191a00b40c00c051030b01a90190514400c020b000707584000c8160f1880001c4c00380701210100098504a8014605000d046843c0c1504680c1c0344541d00905400381d001c401515030402d9480d0300104030522400000c2501d0380e9801c070a40c6048010b44410000c00c4150071041c1192620400c000024 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 821300521 1250 821299271 821299277
    0x180b0a02060919030305060a0b0708031008011107081308030c010207031b0203060601050d0204080118060c03052e050607210c0803060127030501020d0e070b0405061b1603030e01 78
    0x25041203510f03079181c90a440000f070a00d502c602c0068082d41d1044c0c40b4400504a689030030790b49420b286001110b643c02101d03104802c03100040081210032051050111182e50f0400140c58212943c40f100899040141d43d030b200000d1488001c14064000c0c0080e10ba2056010000340c0c070fa04a030300d4060700b46141444405201d0400d80305880c096580025500d030000400e080035903640b0100340003440a442290007442241d800e0040b40701d61070120620380400c081c020f41003003008601882c0228295031003542c42d000400e40010810340c0c610142840341c8401160700040e00e801950354004195160094141550081d6000c007101045042094500b04c14811602d00580c0e039141c82d560f400b03094080600f03414100101480800b0350617030740c035000504550350014482d240503640d01d4818041d60010f04426043c03070410308040805440095034200b6030340080c8030309081a090105000d45604460f003401d00035209544e811340d0100050150b01721107184d202a40701d0702c03401c0d0309000e06a401108207640c10 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 821301771 1250 821300521 821300533
    0x5100c08160f020f060709030b07050c07150c0b0c070c050913030f0306090513050115050a03020f04140403050d1b051602040e07090f05013201180b0a020609 69
    0x6403141c0c680300c504424041c00c22186224020b04103d10b0b0202c00d41e030560542c410b0340309020181c1d0b000010201102d04c140c0c05580140e41d401802c48481c012140c80707a48a51000005000b4007403c540a8619215980340114861120740c45d08100c110055640c1c40810b0300c0024104103200d10f00501c000548826545074050342014560210250000000681080144440c0c0340c0c1c494480c0e00504010803800b00c05100c0d41c20a030b40d55001c40d10000404891070b6180440348000703562007420742003c0b0f4400130b1041d5082461038007071240c01e20034a20001e5010b95590354041c070042c142040707180124001d544180d203544042403000308072801141c54444911200d250480f0b00756210040742e512405038402d42c42a8151440440c01a00c07060710810051b000340d407008141c20407207034011200b8500891046c09140d03a140199048500c2429a142126841800910141a040458503a040741c18502a0349420218541c06c4041e0019002104c440c031001407000300b955810000c00d42c004000c1005031071 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 821303021 1250 821301771 821301781
    0x90c0a093309050a0f090305091002060919171603030c03061a2b0c08100e070c05070509010902190f0503150315070e03071410050d09050a05100c08 65
    0xc01d542a0b4411010b0080d190030005070002500e400504100014100c18015500709180c050100d82100340300c64050400c0965840c0c40b50320008045010300c403010f0281092072242000d0108252041c0801d54180011400c80698508400003c0181404100907908516520b25000f016607488080c06000c060800134203208003900c50b09101b03085c244501c07a09a4032244100c68020400e0b0340f58990344d0351403035100550280c410980081010001540c0c40d100b10340d07542d03840d40c4d06184c940d00803020003501c43c10001d9141340c0100c1040c2c0000340548121040b0340e5950002a40f0342c1c00907007151890319000300b80420a8080b8035040c417149090f82c00c144824207042e52008101303000042c212a50301c8004000420507850912502000700ba0100c0c0c82d0410303161010029100070f040f00b49c2c0c0d500a11440600141001360251160600c0c0c0e0000c0c00040350f02d80080c2d044405412001c10183c80d030f60344800000004004224510050f80300358082d0185210310119142100c10a00448081c0400341c01001 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 821304271 1250 821303021 821303111
    0x5300705030412050c040c080601110102030c0f03060d060603030e01090803181c06020313050610060f080403090e280902240405090117062d090c0a09 66
    0xb0141c0b50840c8440d1030f41034590a00d40e14120f0340600007500607281c0040814035a50000300c01d8821482a25483c4685800b084010700300d101c02c07150307005a85428414683c8141448000319000384005105029000c89602da01044980550040b00420380903143e01c40a541c101d104000200205805181030100e1844048107180c2c00c0c1031060303c81c1041c43c1d04201c040b0f02e0450030014003600300b242152207107050002c0c4c2280084004064900744030b84030008064044189c46881582d002e540c1d07840701c3c45410751003a140d16202030812000d1002901020410103a13000030140700c1d40d160b12083d017003081d034083c110045000e5680032060103402d200161000da2140007681c14484041800083c12580100001105028507044554080304d600000074034a540c00039900f0300480ca0809854407600c0d1844400c29143c192114075141c5000c4500c040703960401c400030103912850200581e40c244440303000241841080c4d402c03032102240e48401841c0304041c0740c5400851424110b10048054080007580 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 821305521 1250 821304271 821304277
    0x10905060a0e060f010908030c160906081002030604110304120305180c13060f0605070c05061e0a030f0c03020a08090c0a0314101407032003010b07020d0530070503 72
    0x624018800400462685d911500c814001403807030805903a20780009040c00c1c2c0c0c940510b00e501141e034100000022448008612403441150424801008207107110078104019400017401c45a10996030036910403902e660000540c456445084a82e031a0200c022014044410160074890300031403010f9400a040400281c0b0581e4000885404400041000300324002d481681c22940086585000000b030301a006000341c48128860900c2a440a85401c1480341601804010301c20003c1c11010301d400007500c4138020702608600d40380105440341c4048070390056948811482d40025030000c1c1000410307500060350358200e450309020307000a4014000092084100d4007014002070b5603c0e070903049821003044015034146d0110424400c3d1401d03054011440581140c401011034185242c2900400c1d560000500b07242c25220703040d0859007050b8001581d9005044d041380c100e2000100d01000c144100300494840da0b0f680c402412400d245102c242807040c14850350000390109200000021b0004000d07 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 821306771 1250 821305521 821305531
    0x140906011707050d050303101d040f020d0203150603010c0201140a0e1c02100b01030516180b13090e03130302010f14190806010c0201020304050405040303140f010905060a0e 76
    0x20107840d6129850040d00304011a40038a038080321340340c1d1400800001001442c0b1643c030940e01d200c0000d41c0d442e404607940050481030709102d0329500c00200004c05652a00c24258000f8181c030304d080000345d01092414454410031403240342143c003000410b01c0c0074040c1440644d590f1000b4001c44240e8202409101e001810701030704d040e00c03801407101400d420051040802e801855201030b5084a150103500c0e09440d2490121603801e225184003030354040d006181c000c48854802c1c0341244142c20048030242c14564003002e1003542000c00103048000000540002c84840b42d890304400d1401c0c611904485000c4444002a0420301c6442102c5103101840381c00c480d0203092202280341ea02904941c00d0500380f00c120941d58020442408140031000b01c1c0702030001c543c0701c61049031a65801522042104540240141e000708070078411400c06030003d0b034102c3d2180c100403412403014140510300e0481180c041540c400b41100401070417132103016040d0812810348002e2403090a202011460090083c4 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 821308021 1250 821306771 821306789
    0x180706300e010e0d0509240a0c0309060804081902031c1b0c0b150a05040509102d0b040e0106030813350c04020a110c090c27090f010914090601 63
    0x80c1040007a030401007204114461110890b175103003c8c030703040500403a091040c01e800140c0c0c003480114200d03000b280002c0c01160808003860601c81c4510f41100000c01c260700d01000c602061040040400c40e4501c922031003034441101140142103a4107030082d0a03c001e6180702002003003045000458000700d00107402c00310720349659030042140c00110729680303669402183c1041c0b6240800c035101344080713000200c0103140c140501c12904503044079224551014586a0304105a504600110446178044140210090400b03d41081801c3c0b6003421640c1d00d9100341c42d01e050010f950003080b0252140c8034041d04800c0078203c90208140d25045003407503810b040850b4018260604400008200303d020b80300440140706643d80c400307030304008001c4551902c1e14002880b13010a00203a40c80c180203030718400c0e03024104c8181004090300e44040d4410344068505941102111311121640b150312416100b0074414124200c254541303041c00b02258154084c0700d600d400314030300f0f101c0417550100d0107904591b0211 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 821309271 1250 821308021 821308039
    0x10f030f0314030408030114040603081b011d070e011502070b03040816050d0201110c0a0605250e010806010f09030b1b030406060e180706300e010e0d0509 68
    0x1c5070a5a10010100c11240207210202c108000c0000410055040c0d610491500381141d070740b80b080c80181c5010340002000c0110a000c891142101403101c5030080e0711034000814252002c94400401c41c20011a10102d9000380006000001e110640079004003060010101400c0080d14000e4545025020b081415031002000c101030007461400d82d5520340c600d151200010300180340140d41e5004d81d54684025508041e03200780015134520a850702415140f001e09020039169460800030a4000e000b200c01584801c0317944040560039600045140440e140d52011025500c005004d940c802000c80d41040b24100000304030650003800707042142d9115068280544484030540540380224048803a000c1000c000c1005104031a0808421070346613200682ea5034a507040c11208541c490190b00c40260700040d0100441071080d40031010b4003145c00d010305c425104081103000340d240e94012440c0c0d110384640404030703840d00a200382c00072100d00e10001c0203c00105d01000e0242e018900d502071084d0400c03 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 821310521 1250 821309271 821309273
    0xa02030a240b03190c030b0316120f1a0a0504020307320a090c020106180b060a0f0507020a03030f020c040c2f03070f030e060f0301050402070224071a010f030f 70
    0x3d801c2c0c01411034139a1001d01c8201c4182c00c0c0280101f203210342d8a4428407541c60b4002c02c0161001c400c40c292166580c030380d603200c00aa100c4420f01c00480a0031211000d00030300401c503078202c81000f54001c00c5181000f180c5410103004243c64040a43c02c51800120380039841352420000300010501c80e650300e0303540d0080400703540018440203100d5002c50483c5082981e0350016a03810350191007550064210345103c0c2c0c034410306c450300300c030070503081c86400a0b010072800e44841e000d02c00c4101c8920b69854664541012680429200360f004c2d0700841c0411030368070720100d10540501001034580c005030b40800c143e03000610024a01c10522900c1c890b04d078404852040c414040603c0395510090280480e56510100e15003803070584e003405425030005010211600e1203107030000c11550440a080c01032411030f405d00f42000300950282e03008903800385410406c4000c0d0900c100d07098008510441405441e400c403420441064012085012801000344005000500403101c80c00180da80200c281130351380410f = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 821311771 1250 821310521 821310541
    0xb0412030f031d01090c0b0a0512100306110c061f210204110408061602030406082a18030f072601020301080307141c030e0a0b0a02030a240b03 63
    0x30401c0c0000d07000c5003c40c1e2120502c0054010700c900c244030300e41030301c40c50341e642441c4180c601a20143d034001410404c81e00e03200911480499400031100b040c0314060341c1d03032551039104031540040010042d00c0301080e207443c6108180095588850380c412000324000d1004600004446907002e45c91011000303124400c1401c00001c034403550268003410400520342007081010b61038004e48944011849410006854a09540802c3e503a01c00560021801c150400806550b5010700622010002c107200b5407243c105d5105412511071000701805071343c2e0f9584070300602c210820681d1451406903001403401d0114850000f04842202c40700080050309240580d198000b0107220b40c89800c40358004400401c0cac0c108080700604d40284a10b00612100c03145480d070310748601c00301b24420a004090f4118203466400380d001582010092020b550f00040f20b9690007000c2c1d00c05448a40303800b0340c08420000c003104148184000185903448624141c1650030704c1041c0d43d00f043c040c004802c680400400c001040c = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 821313021 1250 821311771 821311781
    0x130204020a05300702070b03010311010c0218060f0a03020d0b060301150f06082d04080f0c0a0605061804030302070303060f0e0f0f091207020a05030102030c130b0412030f03 76
    0x1040c0c1c44141101060322039a02c44100c0078084480400f814440400c211500004a00782110880c80205003560318585034810044c1818841c2c42c1440b406000180042c0d0341e0200a40d242208240000b1040c2804001e001300d8201680e08940149078024003270000da607911100843c1d590340315421600c10ba41c6c5e4004640900600d894824220603070007004100c0303101c0440790406480c1d8036030341c505990740d5004e40031030100c40d4500b02000361607080d40800d03440240c88884541c0140200081c034a4040e00060b10291a48140324400054000c451030b50b08200d11805100d40040d801c407020401601d182a05441c0b80c04040c00090901d07500090b0f040415029800013001840b03284160400d0036642e0f000c200300b41030102c4403560b4071342d041000030311341115401c41c090161a200c0700034508051800c80701c6100391302c418020b9a2080020344c001403d590240000d521820f08681e50715207455805100c0b6005d4030f01038014030030f101024841480a41860501c2c0c001c2e560b05490001000c0009040070f0307000300 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 821314271 1250 821313021 821313037
    0x3070803100b03010305150a021312170c100e0c01091e050301021b010f0c0e15070501020f070c06050304020306061c05010525020c030a02300a1a130204020a05 70
    0x42d10210001091020118150303001c550b1440780340709643e0343c140b40d420480c1b02d620500a05003901c0b48040c03000022443e00c20070701d24807401c0c0b01141070b841c90b202074450b0341050070220741c99400308803880358040540c0100410046d040c0e00810001108e2000a008c1d8201c40c0141c03860002e68074403a01d80794442080000051101a00856950725558200118011802ca900000b903003003800c546603080c164458181c600b055a61211448103111081107005109071440100c6ca14003440b1100109000f0b00c0141030110641103407a0f0307106098a031001c80e02042b03600c04814000f040c402c10026880c0821100c2e48140200c0b020b503c1141e844009001c0100d02000280143d840c0000700405807080c050f1400b0740000710008510702c001199001c03030340d801d0103091050701500024450401420580c52881c56500c40e12505009a607003440f075007080e000380017a10350803640701c10491028003074240b820122882e0384188070070403413a180004680d0305108800090055500060b0144a41e03c214140c80c940 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 821315521 1250 821314271 821314289
    0x3100510060c2a1703071a1014030f070e1e010303050d09140d090302010e0613030f0203030702030a0b011a04062304050a0603060302270f100b0d140a050105030307080310 75
    0x12100380c401c00e1794035040010111400c1007009031240c84002510006481951151030841e0041d041581b10418001d4180229816102d040d9222014140078801000900881260280545050080816242c401c0264200001c08481c01800070a27030260440300da00841d104045154034103850011248404012001103a000e040020124640d2207010038049a00036661022940c41c0c039410070050f4407800c807c114400d039000e01c0c00c0000034007403a40340782d416000030152820002590086801c1c0a4249401ca0307100308100c005111513030074401126040000d07680200e04184c141040030704441035a50321410344803a0b5039000c0300c0991b800002c40740640700c06001e0f125055030f03e01001c0d0203411103000481c4030fa03100025901c1f818540a4595401103801ea510b4060340d1280c20034000d418201404941da402e041c0341000c14420a854010480c07400607450001b0185d40d950107002c4150805400100c0e030340c1c14480108107558000040e40d05442e041441665a40c48104d420320010741c0c2a400201c00c = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 821316771 1250 821315521 821315549
    0x2010507020d20040b0a061209050313060f0507031d1201020d091709030d111c0c0203010b180c131206060f1e090203070e03100510060c2a 61
    0x1044445a042d5903c01040b001540c3c2a42450b81000190b0b200242c25a800615013a403c0128130300c2040403501d140c1d102480000e2000385501e420381907601441d40c006052801c03900804c2030310b034041c245c00e8404015107041400d08581e030b540103201d108100c101090800b014100c80c50f00d03944086215490452082c000c5540f508032508100141c03513034440580b0000180e4172602c4e4001c5407001200c4104400502520882100c14000c0d6113602000000702418400c1e0340314400c080c035806076406042031480d00c603003424882e2441090300355018094614000da002c501a031921080212a454026640484094036681000303040c100c02420b6038800c200004281d941c00c0184805540701d001a81c0c07001251024103510b0b02d81c21500110b00c08529000f641e04031a0401000a00b940659000710282c548407a9541c45180001c2c40d00c00c40c601c1e1740646980d1041400150441030b01d03144000e0803035041c442407000d11a2a5040f1420008a40903500030100500c0903010500c0400e0304017900c1107202c9224 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 821318021 1250 821316771 821316773
    0xb03091501030b101a090411040305031201030b2d070e1801060f080108070b090f21010f0e0303190e0f01051506280302040b040b1213020d0b0402010507020d 69
    0xf02c28102035034060801540c0060100d211160130050682c10805401094074008000044c0001010030203000128184207000c0407000410510090045480000c0d424900d541181081e22240c400a824002e03581081c0070341711b030000e40000749004c81703026032303004c000303840d500ca5030709540803848010115031001c0401079501d04180181c0046059a000d50740d0569051030344102660048002e010341c0100d603100307135005c01c040307640b500c0104450031f0007505c0418a402c5040100740e9043c1004030f84a000c0b0b02d460f1078240688400d10480c0160b014428003800502d0844440c552a440081d1190590f140310000b88080240d607074001210400d0404112203040011400180c000c2c1001c6d91840d5000000340d100075140d2030a039081c0c0794181c10344001c4040980c0e0540d041f07010406603200580505070240700008080026801a200601404598a81d1740042071101c810034040140561640e02c0c400380800003507211032002e000e42e0340c1d0054682c6101d440b50300040c0c07424000d1880c029440301415480368 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 821319271 1250 821318021 821318033
    0x6050d140d020607140c120307020d0e010f200f07030b100524070528030210140f070e040f091e02010f051e04080601081002130b0309150103 62
    0x45003032040c410549041003400e9100300d0326000d003540e5000c0011042c40d10616102c8000c4018030a200070030381220780c1b8442c1a0050745403600210341c1c141c00f42e0410206c48030302540110702c14820110920b8500c0740890588030207080790b500344d02e0fa0401c900302c24031940b41105080140b003256080c01c408841840350780e07141040c007403001210f00184030010001c002505082021400740c2c40840c0401c408840e0b2610a11280d60303400509054450b03114205202c3c000903e00b00084900442c0c1119000d8480c103d0f09004e0315190604140f1660546000801c20f0202c03025115507030881d001c120340d034a4546074000304441044040d980366501902d011441c008a05540d40312000a0344260140c200d419621003440320010101e90011b4003003040415040b00b000d10944c001c2c1a06000a8414144803003002c408030601e80082d00400b203141d10144c014880711104202100c10a224003006600e005000c03100c0e403c0038211403044000d0200d021011440b504004d02551110284601110710150ba482c1468 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 821320521 1250 821319271 821319293
    0x305120d0921170103080a1d04140a060f230112050a050a060b09030a060b15030406050906010b16060504020f040905160506090303120403050405032e140f060406050d 73
    0x5000894400181e00f0910720707500d070125040366001200181003010260055902d0382e00c0020b204c1c010341c0035090007041c2d035440c0d1094184981310820580028036044503d03208a03559500f19020102e400c030020403101040510611007074021824290b0b0960b4403200681d00040042d040001c1581804100203030640290700091142c0c50581d81440050380e144480a41441100c1500d6016000035081401045580c1c11154508101500c481c030080c03400540c60340c0e00d805c1135901b01c54454607a03082c004034030800c010081c0908a4107403020700d0807403183c00c08803400d0040c41e0020b001d1601c80300000c0655907164954400c030000540207000700c2600e860400d48440c031000481c000220f0401d0049161308100054450041d4090025480d10589401440000390018401c03810004100004102a1014007680150420488000d8222203800052190740000e07810000e111501e85000c4c60000d00030210095040f050318003800300369031210740108002e0800c03904840d40161a01d024482008128111 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 821321771 1250 821320521 821320583
    0x1110403021e041d0c0112142a0d050f07090803030f0411150c011406010e060702030f0f0d170610121b020a050610050d02092203031a010305010305120d09 68
    0x2d0082040c040031161044552132101e0704504440400020145e4000170303104e200200d270b2540310340150950004400c3c0f2550202d01d8111807a40ca800602820300c1040140780d8101221341414125030f404e040c4465aa40401459286080d544070003050500c0360410645030283d5018218000383ca080310000011540302c440b901000f5032800c04c0c0c0700f50315410805420701942c4141c1d900e2004018903c00c201d41500401c1c01a603160080e0305444c03c100c1010000c0d004250845d0000e003141c1101484041e0598450152010022200da420407203596202d811905001402d03003095031044500800c1c0d640100842c8480001c1010121010000650001501e10540d8400c808603002e9540c0d412000711094542d20890740c024400e8107500c0010300d461501e6a51190700c00360580000001102c900100010105081e4082a0b850b001200c03008040da40e081c0310402d080c2024001545565902d40d51a4504181980c481d5000304105001c0c1d61250020040c040e0400c1504c80e8010132906620030742d030035801c1 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 821323021 1250 821321771 821321777
    0x80f1215180c2b0c080f07020d020d2d030f2912030d06090b01090518041202100f020d0501050102070311270403020f01110403021e041d0c01 62
    0x22810410040285482e00c64981d00400908010f480c0c1546440c0c042480c4201c1000c103078255a00d101000e051040741d0411029a4a840103402c040c05070182c40c05010786064110340084416000703040d0005a50b0708091002d10307024010f1911a940544010303c043c4061030f4064540f44451074642d416006a0140c7e03c400408000401c0351042c00000c09100341c1c0080a0108000fa102625281030301d44030701c0514a5409a03450001d00504000480b00c00e50801e40b4402d03070315400010743d542e0100f4154054031080c0d8840000700c40c81000e0000c50f4900420007040380c1c3c102c104240400b4403d02010b44a07996035402400610002c160300400303504040c541e204080d15100002a0720b600c005121001c907900000c0400c6c52180b103000344029601440320300011440040b42d109003180e08292420b104600950140c00b4502410302010b00b0742c1d65101c50b40000100c18031080c40075913640c61456004014210105502e104a0b40c0440c000c0c0c0071038812420007812850048012034070104040d40300741c000341c1e = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 821324271 1250 821323021 821323039
    0xf0316080c100e070f2706150f020c010c020618040b150910080f0703020c03070206160c1a04120f0b071709070b0a031e06090207020a140d080f1215 65
    0x81781d80e4411a9880c030442c40060418510b0426581c0d0040a02d0f40b02c0080701004101c3c40d880d010040700e5a076800418200041000004c3c4400c55810712030714820130800d190589281d5580d0b00003584038090b80c0d41240002c1c05d2000059000d50391030f48070440c8030764040e2a18101c84442c0542c00e40c160441d03a001c1e401224111f00c0b070080188030340603541c802e8000c0f0107200200c0e20b13070105c114000e400c03242c45d6052622003080071401580d00e4038040e05484100c0c916011110f0068a8008401200350740412014026014000d05040351501070f94191405007014000ca42040d04043d00e442c1694400500841409001c0c40009503010001c3e9081c030030304000c6601203840340440b403503488146200e0b84081002c180411403c1700c1c0319401068003034030014500d503928020700c03810204841e003d0340301c054896030000746142141004100a00281031101d4200880e0316010003061044d808408001d000d88000900802c0e40c0200c08192010111100c03000c01c0c203480c15504c031045010309094058407400d401 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 821325521 1250 821324271 821324279
    0x903020901091d06070512100b0f0301140a08030a030b180f040203060f090a021c200a0f0302090606030709080111030a11210601210f0b01020f0316080c100e07 70
    0x18405d0103001c0d00d5482c54035007040840b08155040c8040d100000700a1511000641030f980d490191000325100181c20340d03603514007a060032603806400000c03805150384800c00c218106000c000d9030003003403132400d021a0041c00341001074005a000b88010742c80c0c045450520000c7c10701710b9040d1b07200f10710990031105252201600e408a00100320340081c45a40007a103110010308042c10409068a10150880c5c0b00207200c0c1c1e81d01080d81024075a20303940807400300c1c0101d01468800000c030003c041902d882c88880e4290f8000c40d43d1501c00410481c0251000008a025176108035002402000050020410f500c1004590080b56009944c02803c850420f02187e00b0f14281004417000d4000c50340421008421905000303242d5800108001d040c00340100c07001e030030310024504403038030803008400001d10450014180b00417645016003103411948814041d0740c501200000b25446e8000c102c01c0c6142e03a8449141154441c45200d0001c519030050070a580c0090340183c200520f400c0054050b55503050326 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 821326771 1250 821325521 821325523
    0x405040f1a011a0a0311220b070804030803090c030d0306030b0114060d090312060608010f06051318020f07030c02040e0619020306040906090507240f0e010903020901091d 75
    0x2c0c02007241120043c403205210311040f800411808a50b810f01003012410400e1024540e00a4100d906800f5600141078488001e0038030160041e001c80c0e0b0b40340d8100f41c2c00d134403802994052400014682c220000225811500412184000100040c102c1d80070f1146c424009001d07010b54881186d844107031500100c0d4500509003501060600500300e6400c0400410050000d800134010a50a010740d400e007480d0b84030440e004050103010a074031121800d5141c1070001442c1446a8051001c0140c01d101094100d031080e00c41030102d404940c0700d043d0320705a000014009100d049500c00c4000c80c0048d0003800c050308511200780c42ca008403802c0107881e41c1c203e820b60715108100c58414003000c0e000210b145d03d120540c040c41e04410090320001da260071a560380f00450380300c084152403075803200e0780400c504040005103640034007038407140381a4003c00101c090901d1490302c800c801404889103210395542d103e505a140119002010140d47e569900c50101c010f1500c508c20f0003c0e0040c1c92218400c03088 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 821328021 1250 821326771 821326823
    0x6020a0c060e1e040f0e0a2a0501202406010f020c0105162915150c1f050115090f050d0f050d0f080a0e070509090c0405040f 55
    0x4060301c88810f1224201d070080c00c0c0b41c3d00f000e03000c2d032259031005410a02001e501c903612011806800074280c1e600581090040410f01114400e4850a030034032801004500c2c07110030049850a0801910554400c100c8684e56070000700f071442c4521800500a00b910750030f00180d0503418030500300340d116231a07680044071000075a40c0d25002507030100002d100341e03500c60f00c010440000101d103034092580d113556425940c1321403040c9240805081c1c05d108000c118002c040c140e000482000920640c04150021461803080294035411400c0042280b030f200304024414005000200a40800d40c602c01640c4403000704000c2c001c450707802c01b0f48102e401c41a40645181c2080c3c1d018900c4685015181104208900c2094041198030102503441c00000901c104205801d000158032008400300c2030303034002000440d0007842d01403560b00345020421003403401702e103650070307104269a1160b1581c0e40302211440d00c5000c2c400c81d80c2142c036100070041400017031a0841c12403849014143d695a41c1020003241d804 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 821329271 1250 821328021 821328047
    0x91b030c0203160803150d06060915120605040213020c071403030a0905210a03030b19060f030f02090d0b040203060714030c07050c040c080f010f141e030706020a0c06 73
    0x8440900c3c00d0004c1601c9078059940111900c1030804032907500d00c00326414040c1c80704215400ca4517403106100001d003034020b410003034a885c030155041601d003880c0c2c0510305150b070314040d040342d540740080303070a5441c3e09032040500300e01d00105642e50821042c9059560400d449050301c0c0c0200d480350400d01e4079004c0708403501f410b141d17502c8400031400c00f0104848115402d0b181d509500c645441c8810131017081c008241080e009490000b0005c070300304240080028020a6451240322411051114a8201d0600030400300b49160000301ca03095422058001c0c032503140c8180d8072409070088401004200d20010784558802d5007620440d480d83c0e001516102c03403030000b514111109000003000200c011000e00f40143c014422144089000404282142c4072110541c0000e83c1400c13c00080d00404508980107040301808440201c0c42e018240c40c40b19502081c052183d454488685105000c80781407007100c0c01c00405540700d082d07031880c0182d80c84804200803036140711501000074401e0702400c41c00d941c0c1 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 821330521 1250 821329271 821329297
    0x1504110f07030e0a091d0115150807030603230c1008040803040611042301090303050d0e0309060a030b120f0709020307030f0e031b0c060706090804091b030c0203 71
    0x4070070035540c10f503002e64101100d5034010300c5510000071222614020264034401906490b182c1094422500d07003551518202012000e403d018100714029080003c010650a5450954000c2d12285c078114054181a0306c00303441400609080300c0c00d404454a0020101e01101c00c55000440c1c44051000402603238441c44040391184002801143d1510001e6a200d441284005059100c6410040c41c3760000d03040012120f80091541c0d24030440d60030050741c151401d09258140034034540d4010300c0e62088610000b4895169542010445410810303900a00030003481291911440c0e003004000b4552101d00c01e00c240c9280c0c03440d090502e17020698074651144400074001c6241070600315006544094140410941e80344031440c4140c2d5503101d0005644542c1006d95584c07070b0b95110340c0250110b00c0303d48203200c6d0484480b10600c1c2d52190111200c0302d91068010800c40110304108402d4025a440054118208440b1200380c1004207076070104030102e40c07810820040d4103103089950f03005204c1840d400c = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 821331771 1250 821330521 821330527
    0x50903030402010807110f0109151a13140a0203040c1d06100912050703050601080304050906040b0609030709140109090f15270c060e010c060e151504110f 68
    0x954410760490760f05c0091410203007510300c1b00b0f8000b1031518844080c0000300781d6586424504024900e0343c1021000883c0c903052001d40d504114098007032500010b06489a18006040c03180301809811603000d0068103417843c0094507000d40e410340079500841c1d00711007045a4400129542c1070f8158500d02c66025803601203481c1e9503070b00a00018960b69280305040c005120310001b0600500c003081c2c810356101700c1c00362003450b14500d0164504a010b2f04058800d0704107001c03c2c480d544030301071300c20750002044a02041c15820400420345606c03440903990b800d8000c2090204240d04a81c010050200d4142040003550b0780e41d00d40d050131921600f100501c4511020689404204196148007041180c0e600c0042d29208481c090104d40f6450185010314145027141c40c4203000410041000400040c2004145410b0020008152419155000782901e60703442a00f1002e41d01002003d502c01c2242c0315400c1c85003040c404560800801400b282c0c821400c2850400444070b441003514038150000c20100c0c1 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 821333021 1250 821331771 821331773
    0x14030f0405151e0f0d1b110d0e060f1e03160507120305042d02031b0a150203040f0906081c12020a141305151c0c0c210906030509030304 60
    0x5a0f2062039416040b1301c060102d418600301500c075080d038001d00c0e590501c003442404000a00600d140003488106500f100c0340403d051074101c01000d078400000c40d1066555006d1800c200760070301640f92031418003134000301c0c0345007001c03a500011030086000701d403a210042d88000003242c051007204002072000c8840d0f144410158005d40100350824441d0304420002c1c041c0240300d2100340651000403c040030240010025070401340540101c2000030070051585c0040b46c402300d80c1000780303403282e852842d0400241c550700314800d0040e034004d004001c00740c10040340c2d583c07400805020980102031007800350403c482c2450004019100510f905920b494110341c1c0543c0c42000290444d22403003040c0207400c0302803402ca0768600004c2c41d0840725901d08403a801d090009000000f48201d8502501c0c000400520000422845002d0b4440e0107101010640c20000748048501d51003c07000281100c122003e0345800102055100c107a2518694403424500d5075000220185c0b101956981c480350002c00c0410 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 821334271 1250 821333021 821333077
    0x801060f090e0c01110a0212030a0e03150103030e13050106020a02090a02090d11060f12150904050a06050711060f01060e0a12020d020120010b031203060102100914030f040515 77
    0x550421617003400e6540050b03403078012070080c583c50041003c603900002035034405550041d1002c550300c1c00990050401001005000345402070602018050001c00e07440803025554260b0341d01d8032204140c8091169583d18103000e035503241c1042c000c0748650344d14400204400c103a40b00f60740e6104002840d2174031124803515401040d161403c00316030040c0040154100c0c00700241d00506401c0420303c54034880c0e141c100c420307048440049500c14468420300d414403001c15400200e0025541c0c01000c00601c5440f1207405640e000b07107107440a00030380101d60070840c91000902c1e1840c1216034a45681450040701e50400112030ba807401040d0103c840940080050305140508680c024418142654200340742c601000c0c0e48900510310803140d0703440e1244015a03007800d00c292800140312205440c00e42c1071a40000c0d4541c0c03c441d14001724203a031905c50b441404500140910304030b500e102a00ea80d82130b0613005500f00c3d03000b03024290095007629160100c3c821010126412582c6e00d0700c111002041050041e = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 821335521 1250 821334271 821334287
    0x11d19030302040f1707080c1e180f0619060c06150b030412120b060313330e07030b191512021c051209190801060f090e0c01 55
    0x3541059824080031602c10602000000600082e8221881446049820a2030000d0580115056070031884a8140c6921650b4001c025018502c03581d180075005600481c20751012520881c9591b0940024002d05c0a0315804007406010107480041c600841092145580c102d0342c4613010001d0166040c1001243c05640000c10144036a04090103142d960000148942c0003030302d0903203901c29062070a10f00d664010f148800e010f046498107008181c240d1000403102e010040c0844140411440c0070010400d10038545522810f20601007051403400d140607042000c08400078502903803401c84600c6034424001040700440b0f600c001c2880199440c180000c038442140c4401059042c0c45000d02e00325096500300010151500c400c030b12032221624010001d02c100c040700d418281004180c5014045000828590742101140c0c1206a8a52100e40480c0c01120a8800c0515240e1007110100744050190084030403215018400c042d01c6403034501e680c0484500103896401507010f40302565003135000d84070f8 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 821336771 1250 821335521 821335523
    0x81008060a1d0f0d0801080d1b0203031e0405100503040b181e010507030b100210151e0503071505190507150507230306090a0e0a05010b03011d19 64
    0x1c90000059a02c1e41a854560041c000d6095500180d03000d00c0450350000007503004048540013044c1c05040007401420b28400080083c0c40010300701241c40546d01d00700115850344182290003803600e92240d29020a0b504a4054144141c4406100e041c00314030500130b8a002e281c200c000060306d519000e000540c0442e105401c0b505a000f0240c0c81e042d4840d1250002030580c0f000000812a0714040000800b202d4217400300900c00e402000f4a1071800d80d00141203200b48020410008000021180b5410343c8589584580c801eaa400c50840c45000140c07a034540c110340b03090301110ba0080c4c80f240211015a4072002c000c00060040c009903141641c00c00700c0300064040c40c146a4a001d09503110424010100440c166900341c0343c901380489503074480030581800445000070b2403d4030040c000891544005003140c0d20a0708060b000c1140d404456210706480388010b000c50701c500b0818a0042e019003444030740e4074442d5103043c1e0344031094032160140200f00909203016118040344080201c400d00340d00d070300c = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 821338021 1250 821336771 821336801
    0x302060c09121516030c0e04050901060b0c0a0618020612130210230306031e2508012007030c03032c061006051e0f0415081008060a 58
    0x1800c002c40240300c0e011010401c80015078552819603807a5107103044440c1c04900701450000b02079100c0e07a001c0c211f12022501110040f5054403a08401c1c0c3c0500300f10b400c0344582c00360000d00031049850000d100343c000c038400d510900c10150f003010081d44041c51800080c0d0025410807400300081c0300503000c00d61100d10408003007400102d1780c01142601490126000108100c3c400c0b030354824001e0183da40300110304d20152455880d08034040f9032650030805000c004403000301c4610031029803c0c02071802c200e8408a1070011a000c0590392680e04035540b090b403203d946400d02808002e503007080e0382c0096030301c2c400003546041c80c02e40d001c440003090704038243c0805a07035040e800307c0f4040d031594901020381440f100e203025a145048103030409101908012402c080d40008010058124060340e42d040c0d216252405420030100d0030b155140300c1c4555a013030032280000c011801d41d1a51031003017035520940d91201d0b41e03a510140500c2c0004514001c8401030380c041d10024400c00b0103900b11141080ca100 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 821339271 1250 821338021 821338039
    0x60c01090501090317280e2515020705060415020a02120d0f020a3908030a090b0705060a020d02040801060e01060e180c070602120907030309080a0302060c09 69
    0x1454440c00c4582044085000417802840c2402e06a106942d0a40103c4895402d000545800050092100074a00c0c480d00e030a40345c3c417039050304c0741c804d000b0050004101c0c2c0c0c201c80410a00302440a01c007200380a00e0104506402c014410140300144004c2a80c401811452a00d0f0070010000d8105c0f080c50000360851082454410041e02c80c1c069006031040d00710018402e030400707140c3c00303000b85017000000f402b194400c0800002003080c5190013003088481418406055980c44000301c2e45550701003005030351048080000036119400401000701005070381e602e40703440f0303101c024844031b91044d078101604980c010004180e03103842c182e0081a400260000051400e41c2d02c024850070344444d9407056080d80c10480042002030b07000306404a413040210744042842100b07282a00da00325020b05041c00c0014049103090400845504481d0440c001007038031030b881d24205a192f690f40007980000c800103440084e0000d220b9a0018440ba003896154014006070b07a100d1056041c140c01a03081d45a11943e80 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 821340521 1250 821339271 821339273
    0x3f0d0c0903140c090a020703110d090e060a061e030b0a0b0306031e0a0303050408070b0112050f07140603040807060501030803010306060515090609030708061302090a0501050906060c0109 82
    0x244198912a0056168a040e241ca507041c4454060a2480a6000c68000556500441d40c0b104280c55200c0e10300000103868000908040700d201a510f0400103240c802c0c4c1b00f041ca9070580144090b0102d41160441e481166104018041058014852540415940c08000010040c8510031400d011014a800200c11110300c002545a0781308da400000d401c4400000d00031642810b00082840340c2810b1401084442250501ca03503d03001c1c0c107070250406544001042c01c03c00640200c8a044d034000c005c900340c40d40c45000018259100e0201162103204800303040503e85404100b0908071048042d1000c030840c1c45c001404081e51004108440d4000100012030020300c161061034040c50044011680303035070541ca040380442c2d4490f04280d2049490005910701300380740000b16941c1a50039900c843d02c0d0020340c03001c2440c10419408c4603130180a60b03000c00c01e43c1c45500c802300f100c0c98000c444a0482d83c817076905c00d130101c880a000d1542c21a9110000030700500f4048010800300a04400025800c000c3d = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 821341771 1250 821340521 821340547
    0x120a050601181d120a0918050121020102101a0909030408070f080604061812020c03011d190f0b160f0f09180f1a033f 52
    0x981210b06a0060082041600348282c801d040300c0b094070a03140000c2c120540c46960b03489007a0a400c2c100d86800156641030b6900c900203100062000050b441c079001d0740c243c942c80c007400003400b404078600e007080801d009003668018034180540d01038000d807822070070104144c000f800c1d1031700614450440c40120107002c0d44440701e401c0e00c9801010042c54170755003400b100a01f0700d60217070b0010403000b85840701840564004100e4540155001c0e50004800b281842c4070701038514541c80240010000703180450182c2e4020483c0c11101500301d00811100c90460003040d038030f811086407091713241d00c01e8004042c00c40a0500c22241540119407a103044001686c80003a02c4004646091960000f200d000340e11035009011980810300e642000071141001b200020a0314546215080c1c510100500004035020180e004500b912a100300501140d200100340381a134a8510501c039010f8800c0001c0351021042c1c02ea680344076882200716212046105084d00c0816030f15145000002c00c104200b10068910 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 821343021 1250 821341771 821341783
    0x9040b28150f030b0708331309050c04020c0a051c0219050c0d020f041103100509010602120a0e10020a1a09030f0f130f030c051e120a05 60
    0x40c0e908400726011407641000801c402041d404680038202d040c10910005498603005903002c00c05207002007495898072454202005c4641c40140d1075035a24000d2102c16200382c400c0c110b060b400b50b9020084030201c3d00d580c0b0071035582d5900030741550012100000780f803415070000c2081031080400c5904c00340058039028180050081c5988065828a074207018458052004000c14020b514110f000d81030180c603000d40725481303000c2d0648030b854030490210865541c040c5c0038a0412001e041041000c059110080301580700382c94840c50800c0e4000006014a4915800d606860895000e422021441c802000c4990400f451711014040500782401c49600c2c2d5400c044081c148590041815a119040100014045401004003426407608111000d200002101e245e4084240710993f100022003200b04a40134410f038508030a102c040300040d901b03a98803802800e0340d0040781d101d03002035a68810841c0108404240c401d0203220458058464030b410407009074981000020380b1440100c0d60f0310320741410 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 821344271 1250 821343021 821343091
    0xb010e0109060c0c030c0e0f06031c180e070207080c060c07030201050711040f050f1e0106050f0403140102090a060201060e1518040302100b18060409210c0209060402070209040b 78
    0x5040f071401c205d80c00388e80041741500020140c001d003049410a242041c80c442d03080e52108140a940c6400301100c02c402c003000c0006105440c41c50a0a00703001d0f0700203403100580d124a01a9100340f44000d07007207250050899035240c80c030b400100409403840e401581c02d90000702095a4000d440c007001d80481c0c456010b900000304841c5d400007120f1a150b500190515005400c80c52a804160340800e407822007981442d06442032800c110f03840d0595000ea100d075620031500000c2c404a03035210001d550b10030540140c1400c10080364106040c54032007004900300c50386032165842c00001c980202e1858411068540354a80014200f15840c0c1503240d4281e0b00030100b0b03541100180e222400703158440c403240c464100030101c01c881894150349017503800380c000c1c00050714541c400c550354034064081000001440030000709860300c2181d0000641d03c007a16000041d18113030f004064120015441c2c0c9001e100f11010240d000313002c0c1144c0d4445444801c42540000c04604600b821001c2002d480348000d40100004 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 821345521 1250 821344271 821344289
    0x181e0e06041208131106070c090b2103040501050a090b130e0604060311100306030f0803040204060b090603180723030c030106081513080d0f0b010e0109060c0c030c 72
    0x3034141450410805040c10450030100b004000601c240c0802d0300c04654940b90300305144034920b008840000f40c052290b40802488452620b80004881c0c0e140d4003c10345d1880e046401d194000c0c0c43d00c2c013000c10800808240ba400382c01c00c1106100070341c0507001801540f00945001180c043d2520908001540a071159001c44540031004004078a64003540c01d40c000e005560500a00380785548141c0d260041002d400d20521400401003007440c440d601440095800c44100780355480390b4108940d1690058074164051414040c000c10030700e20150840c0c3c2d40c0d10700903081910319515049002c50038946011104100e020704c100005040d0051030581c019041402c4403081c400b0074941c20985010040c40c07009020382d0400b4020000c6507408143e2a642c1201106205840e0361030458881c0a8440c40310000c0c0000c0005c9806020740110307600c0242e41d2030036500100b004000c0da50040d681461051030481c00101180b00500416108848030700c0c140e80b04181769100350381c982d601d04001016a41140b420 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 821346771 1250 821345521 821345533
    0x12030405011401140a05090a0207080a11060f01050d0210120c090f0f032f0a06050c010f1104181104090905060705270d0203010507030501170601181e0e 67
    0x14148000495401007410303e5480d5135910881010803c0c04001b07114403441401144001400340b08150101e400340d650040e8240d0340c4020f9000050400e2022140008142c801c0d0800a0503a505c0b4001b030a0699000810703030002c09203d030382000fa0f24449c802800080103c4c15001001c103240600030314002042e5a2504410305040c8030f800900e407901603100c0480d641603040c3c1000442d05c2a43e00118840f4200131503c3c401c662408401203146180780c0c150303004003405100017941c581c0f060140c101c65503807800034070440460604900507200f107076100c070140c02070402c0b0400104500e02c0300004101202c14020800c1c2c00c92114440311070704168031102c000b41c0c50b00d64440030441c0c20f02c00164440500e04169042422004142c607100d01da080144842c1c5440c80c110b030300035070fa07000740003884030340c0c010005d0290340340516009001d4102032081c4c403031002c0d00001e40c42d010500401c5143c1a6030b520240d034040c011800301c90402811507030414038a1540446007001c44460303140a80c401603070051000b810 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 821348021 1250 821346771 821346791
    0x40806101211040e101d011506030504030522090501080a150b040b0301051503070b130b0f07020d03030f0f11190c05030406020708100509150441060708010303030e1203040501 77
    0xa8604082d010351724141d1401900b523010b4110a4213890544907580307000907942c0da8920b0107403101d219032240f184400b201c001140451291140307212041d500d66200138400d07641d030381680b6035540d41c0aa00c002e040c581821003184801d4090350110210805c01000441d000b080c5a0200707085400175030b00c400344002212801481401d040180e43d0040c20541c407624030b400b42511500380000c40070302825400700710014816008950000603541d01ea82c00400b9200304110510703010780100310940408401383d042a9500385418844e101e0380c40c00c0301c09210021700d09140000103815804503682c425003440022400d51001c958100068000782c03041d50020300c0e8460a00f04001d20b0120307021f600050003410002040343d075640104048003800141b400948051b00c8a1610707400344141b01d021507054000611905594228030080021120323507000080401d0a01e60326003d4580e10220f5a5101160b1054010000039110350b05c00034a03120320000343d0b4504070340030b0302d01c4045034400d40f020b54243e915000c100c8 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 821349271 1250 821348021 821348051
    0xa030902101818140f04060f02040b090d05011d06180d091205010f1b09120b0f13061b020607020f1c0c020d08040806101211040e10 58
    0x18050020790070000806020700c0b28030052422a801583c219203507014124096511503001894a0980140d03c00658906864551640030301100c041d140d4604103400654810903a05c02c035400d0b6000c24004920308403c82c0140708050400010440d0159038030038a54401c411034010203038540c0c601d41c02400c0142004c101c0412100c0304c802c40d0951a4102c01d500ba00c1890700002c041c0e040390070304044548142d410b82000b50041c58074400c1c4407031290401060300e143e03010540b5003c408038140c1d144c1c09650742c1c0f2203c01040703116000c21700a10111010300130800283c078101065600017074903001d8a811200795540d81099880740d0b10090603c46d001421402c5064040c04110303403100312440142602da4200052903620404481080101c0d070f40340001c19000d42c420640240000c0d009080180031000071314203900c1650242c8034004040c02100d011643c82c01d03d10070708800b15228500204500191a240c002000c0c90b01ca0066a22594400150814038000d201e540700440c81c00b4000202840503417400 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 821350521 1250 821349271 821349289
    0x3060901050106170f150f04060b041e1505161209050901050d0f150e030304051501050118060338030d020111070f0f08031f060f1719020a030902 64
    0x6201d802c00500c4c2000091460020000e500c65040c0782c0703082101460380040f03881c860002c81c01d40c2d0041c4c242400402c6008030000240112014100071210355001460303034010141c010300404600303900c40c242150a0b148280d028145102840220b042031068036a19203a441007194403001c042001110200814501003c0d0b080c010802641e001d00f0346a616070340d0001040540364002c111030740c003200780201940315510182961a007541101d079a4281070030301e1607565644040d50040d840a031000410030b0351044000000c0545030490035070105081460642c040c10080b40141c2050340d143d0f5100c6465000c40940c18951203480003081e10308410542850304000708640c0c01c0c000c6d681020021050000010119010302d0b80001c000c10504000703182440102c1c0380030102070003441010052103d4102032009102c0d107018040d488412260351800f041e150484c5180b0242c0100b400d00303004030350342003480e241c0039441102040c519140210340034184040360000803040d400a81e9850040701142080381c44 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 821351771 1250 821350521 821350547
    0xf04090615030c051b070f0e150f010203030c0f161103010c0203031b030a06050909070e011508070e030c190608010f120222020d2705030f0a09030203060901050106 72
    0xc2840500210382010b0a5480782d5801d035090005000e000c204195400d01141b8054036020b0040d1800550f510220702c48900150380c0c070858810751007815145490b115600140c0c0070b6040e000381d400c50380c0d40d000d03420081e0844111b03602204e1081111480a00c3c610503104800c0e4802c0d54000c0000342548123050858034071506d00070070341d4401c200744681c0420700d1031840740703401765011502e90703c0d43ca1a42e094081c0100380e00031500a4032240500800c0d01010840109491080c43c16000036a6030313005211003402240201e50105400d070000ca41e40038824441700382c0705600541260341c00b081d800d0204615042c40301e28020030038030222707041c014564003014090041c4049a0380500d014107181c41300d00102e4602e90028441c10f800e1540105202d00c0c03071569a00c400804008640b1401d6016198020b44004030032841e400000041003898072103060a03081480d50032800441c104100c92800e2801640901025811700c4007100c00000141d45c108004c51041250400216540d403500201400403004829 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 821353021 1250 821351771 821351777
    0x90b0f160e060405040906090b040f021c110d110a0f080f1f020c070e0f06090708040c140a0305060c0a0e0607030f03090809060c070303020c0d050705090c0f04090615 73
    0x2000514a0382c9800c00c1c3c1e0282c41c000c850000d1200d081d8a010401800010313402031014403080d0402c0f09014000420303588a50081d1109108000601c000c500803080311100140b10b01c40f220051046400d1000c40c00340076501c030f60302148092885000158056415903c028458590240c00384440c0390b0520451060020341001000b50400018010302c072000450b92034416140d012819440700c0f032080000000904240d20001d0301030402c0c3d0f03000d100c20107007140c08a02502000010a604034460311b5007500c40c6802c040621101da05082c1c4400c0400200d21215a000d0602d00740440400c0d0306000003401a1001202139940f803100c0d481c080d0441c004c211116100b08030a00031580070035048007042040403003925000882018a03c1d200312140145040141c02c002c0100d03c1c040c242c031300081c0f55000c0c0e03806a0221895580032004124035280103201c028004d812040e400c21550600305a201e4000e4031408010303080c016100c0404120f83c00039440803d61315120b640030081c81541030311031410f89280345 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 821354271 1250 821353021 821353037
    0x70b07080325030906150308030f0a0209060a030f0501060e03070608060301020403060e0c090f0c04050103020304080c010203042a030c121b08101401080705010c06090b0f16 76
    0x44100068014450094403040c000070002e40d11140c1d084034202c00d401c214042c0c120040c1107007001030092401c3c1c03800301c86452400c0010b0211340c5909005100320380d8050320103855681c40341903148440e80058410b114003034007800a0340d070076580c00c0060f0501451030303580012060750140510040e01c8042c0d00080c00e11818404014243d2408181c501c1900c4050504070718503128200401d009114030f500280c099842c190480c002c044020442c44590311040710030b105952116218108035101c2078480310744401041004001d5940a500a960310a000d40000b604020381d00207054207a0340f0840d41210340d85002517071403d4030503103002c2185585105c040050f00d254155039562070035444900a12011048420265040203203407000c83c1d441c5d8112542c0864003c0d500c01c4260766032102c0480c4039100600301008542031a10b10343d0701c9412140820b00525900f881c0000540f010392041c2019a6016214045c050125582a0140707005040e946050b60719881d1103503006d404905402c281100300b007006 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 821355521 1250 821354271 821354279
    0x10c14340b0909130b0a090b072109020303090a0e07270504050411040603060209030c0402160f0312090b0106080906040209043306060306050a0f0b09220902100207 72
    0x1000b80d0704041415680149151108860b0142000c926140106024500000c0003100003468000945070b5102d25030701c00b80b070340351070009072380040d40c000400b10800302000e1081c41d00d540da070f001100d590b400074050341d1408081c18045021048183c1059000c3d01da90414845015403103170b084600c50034150800340407c00c1504503043c1e8818076214039445151034001103000d02211140d5121008001001040300c5940c1e4600b0f000030790040ca092074840d008242792009503042900072101c02c0c02400d15081d4000020742c1e5090150318400314240c0c100f02d520035120321003110522030560b0060181904c0c910f5580f50180060001d400200f0120064000c101403100503144c484000d40c00c40d500170401c1905884909403000c0b60000f210f48034001c082c0c00da00350003c000351540100159141c85d40c00340412a114024054032071080d114420214020f0141040049440c03405040a081c00810b03c05400c07642c40d0780c41c05161003588038000c0751a540d069800440c81c1a981c0707160b522f80e140c0040c0c80e0442c030b0 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 821356771 1250 821355521 821355539
    0x314121e1605160212100506010905010c020a260d08100b040e13031101140603121213060f02120a1b0905010e060d060b0712020601050609010c1434 65
    0x1e9240c500c00c4980e43d4000303c0003103645041c4448091401003081350b085e09031110886010307020583d12180458044403006c251548680a00060f640d00a4003030000b15180c48411a00448500002c091207407118a80e84201a018030555208030b6255440b403415040c140ca502040d0f02d001c0d84200145001000700301301000000c6e005591081e484006500105002d08040c0d9925140100d4904154a02000c02d086d04070044101da000d45030640447c0d10074406001c000e4050320034600e00301c030b14a0b451800940b032412182500d0010502c205400701d80a000032039020183d810502420b039001c1e502000b0003404401034030403803440b090100e14441d524403062201800100e064000e10741000079620001b486500c0351001c030703164900c6e00007041005658411100803203800a05046808050400107030004034070003c2e06d107040c2c0f01c0040c0080d103481d205100558200503030150440e124900c14520300d000000034401d18040460090f02e01d840406101c18039904058800c082c1c1c9400c1c06049801e01030009 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 821358021 1250 821356771 821356777
    0x4150f0504030915020709110c150423030705060f060102010b0102010b0a0b0f07121e05040311091f0b0c1608071707120f0b060108040f0314121e1605 66
    0x401404e003000440703008200c0c10505c5940281070aa42040d01c1d003000d01c1840d4005080304e042c41e400740c030311352245040d01c07011107001690050048225000420300784410700c810043ca00103a03d080700d250040c03503542c450400c801159444007003042401000401c1d60280a81c40c0086030034402084070480c2c100018031024450702400c101d560021603209802002c403011604100d8001074000d110240009000b001b2509110b002040080040c261103c01c0b4000c405540c2901c1c1c0c0b08100440c820b02410074400404001010802c100390411a100709110118076078a0181180c4982e16075a00c02d01400340f4a061b15118030a540e0443c2e1020801450901160000c1512112100c1c04100500014982d14002a5820144601140d4610f00c03007000400344120107180c2c800c00b00c0e42503c1d912000103503200f0000300d40107881e244030500c42c0f50020344260403012812001c40142410f1001302c0c0381c544401f04085403044607111500002c0400c07010004216640306845400c00d40b880501c02c00c0040c0180 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 821359271 1250 821358021 821358029
    0xa0501140a0303030b0102010e030f3006040216140c0907180e04030c1505010501080109050405100504140d0c140601080307060b01030204270c260406090b04150f05040309 75
    0x542d01d19203016175038805e42043c034000110304112901d402640030030030440d601141c0c1010000c40c200001c84040103c240040b0418407035408182030507540d02c000d01c4040e60003484218841c00402d80b2a200089940306030240410000005125503240201800501200034049100380b000035120644c895a00503400800c1d19407174400c0c4200f40e1103e240540d185036103590014007500b2503902c010740c403c085030b0009041701e20990b0707000210390380c40500c00c00f1140c007910302510039080195045c0010b4441e422458200c0c0c811800010141038417010a82400711280300540000c500d8103004051140340001c1031000c10f4000c0280c40f06500d491040f079030b030f480b50030700c01021191625080380c2c0d00d0b030003039042e40c00600780752805a9201000386061a00001c3d030306c03081600d640c0340c2000d03800ea0f184503174240c02a1000c01c8001c0340b0080388400040d607032180b004004880d855252411880007650326000540143d20440032580c4401d5121245000d4804482c03c041001c1d117014200008680c0c4a800c1300111 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 821360521 1250 821359271 821359277
    0x2328030e06090a1701060b070b0c13030b010810050a021206221a130506150d020c3c06040201032712110129010903050f060a0501140a0303 61
    0x404010004901d19000384210582e1040f40a000000c071140001000c4c2e5405242600801c4003949407a036202103400f0341400074111215510014805005d42d10090910303600021030002002c2c0c0c2e81d41e508807140403d0f0000c0f00ea175005920b003a4006000d50044c1908015183c04c154149601e81d060030b203005000405007071050010002d81c1c4245080c00340c0c4007000041c00320040c0f251044813a09240000d081c45200c500480c0300c08905035050b00c041c407849002d140006d000501a404891926030740350081d1106614240d42044002036484040210040e81201c082c505d1840e0040380c868079001880841c0d035a010144003010b6504404004500300d40d1040c0d0900b00040c81d01c0d22020024865100ca01c94500384120940b4990140310081e241c480c4c0384042582c80404500d10410800e0a8500f224040c400003040d40c0101e82c0001c1d10442e00302c2004c0418948809803e0360382e00d50a141605039007001030036403c4070091011030352190182c00d01400d000000d000601c0074000202c1d45103041c41c0700140130 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 821361771 1250 821360521 821360537
    0x3090a022b060603032d0e0301020409020705010504030e0a0f030807030e030f0c0301150e0a0f0b1804061a060307180815010806010503010c021209030a232803 70
    0x86000000711148941c64092110140c41c4040c640103009080c10701003075000c85c040c07000b0340c20550031980c21010800a00800f54581c002e481d4401e5403c545140c0c011641550240008a07003104244007415106006900114071070170182405081c00c40001380540c050b45c6400f505214000308802d03c002100d602480321603441d80682802c803042110f100c90690715015102c0c030759510860000b140d000c4410210001c20400d0fa000e0101d400240c040d01c121005140c480c400984040f113540d10580703180c2c1040b4404200c00c6e4401c000100c0c00d01d03074040802c1c50038019409000c1030041d9031050507194803803206070000e10f520850002d0204c1c01700518903020080c0202c0a2103040e0f01c034944e14802040c00c0c2c0220740c64500082580c41c48918240290116485102d0000482c1d00d4140920701e000c0c05580c02401c44840807800d02e06159001031180b90700341c813a041503600090791149a007120950041102d0030608146108142060b80d5644a528800510b6103c148400c001e002d1141100e0351505000034 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 821363021 1250 821361771 821361799
    0x11a060405090c0d140a02190e010906080a020712020a0312020304020d1b030206030106020a0b060a150f11160905070e060d02070f0b0a150e090307032a0302030c1203090a02 76
    0x102828980c100c49440c90b00c00410701c90000c1c6c00b60041d018a4130681422035038642c80060403900700101422032030001e025101d0811031180202c4000d5045a5044405840c090f40c0c0c0d16551031400d0740740c20040041e40b01d4480c500c20f03d40e01c00c540c0402c6009028003585103041507000140c0d00c2e080880d02401c407100110074800c04110241d058001103034098007403a129030751940701940b2604600c40690f09082c810000444500c0c20b800c240041d50201941c03003a40703c2445804940075001001c800d000e200040c00080c0c90184104280c40194083c0b0403000180f500f818003240a82d0000341454003817000414100740955151003e442d4212542c3c040142c0380d0345c643c204896101d61b6910064001e111340d6050104480d9140c105181c41d10140c080c0d1031400303607105e541200003070003241e60444640040c060100005e00c10401012548103040300f00b520b60a013a4444c0d200c1d400c5400c000c50141c2d0000544000c1c00b14140708580d00c0c841407610745411440c140000c243c8030071101c0b400074860850341d10030302 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 821364271 1250 821363021 821363047
    0xa1a0f0a0e0a060801140a031203020a050409050c090a210210090905010e09010e060106170403031119020f03071a041a0c07020915010f1107080a05011a060405090c 72
    0x100785403402030051500aa8810028101d000c00f80101d15105207900c0c000c0c2828208681c41070100c940c0f05e00c410604c0c41d590901100250420104841044410070000400420600409008072200b080c0a07a075900003008120ba40043e640c04640c040e41030820450590000e061206c9001d501510310340c2c000d001c41881200c902c4004d03005040198509400442d64400e0020883e02c05c070207080c02042103e035070b4000c40740d54030004d1243c030000a8054410f0713211245901140c0c0d400034800c0c10b011403c0241040c1f94503103504904150100d803a4050b00b18450661b04101d1050030200c080c0c003451625105840d004204415074a2608512001e08045001c01c81c2000c150306413090624071804003428008140c032000d91000760103a1062098401203800803801c801e1031010743c0416160070748120740b008019982c0c0c80100382000258041c44a00089003113050040010680c81440005185402912100d41e401004001e00f405604144420b002c1c984849a615800c0710b45082099141c0404c7c1c0021 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 821365521 1250 821364271 821364287
    0x30f2101090501062a14011b0201061e0503100b1309061e05010f0302040515030a030f12151707090c0207030302010e0601030f0b1005040207140105060d230102070c12020a1a0f0a 78
    0x2614042c9285c23804d2a03c840d9040d031011055420813102900986200038101c2681503080c000c5680c10b4102841842e212107055020382e52200000d0504511400c0b400700c60011244c109405032030164880b08220020b94008401c26041036542c4170070411355042400740c8032142d4190200034051a69400032494182003d901e01003d00c50080450384002000c2c0780003040503c4003d100c4006c1640b9000c041400e82882c080c00800100c4490710007400c5240849217402c0a4607030a1681032400303030310300c04110240e450003014618045500100300c0070b403452030000e0071034186c1002c01007150803002c010300004030b0038a40002d43e82d401044181850b125020400c03104199a40101e03480783c4005111001c00c007110080985140110f4000c010540e00c450a018603030516410042154400900c076041c0302141c2d0200e05180d20724440014185a202e0b508c101e090f1340705400819070b1462484007041107240c603091038400780000d01540d0b203420300c410b541c00915019403250200c00940100d40c0ca220544a1002 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 821366771 1250 821365521 821365541
    0xb0405091b090d141b0a0b0a0804021507050607200a050607110f0607020106030c0608131e0c030807050f120301120305210105130c02030f2101090501062a1401 70
    0x252401d00e00d4a200703031508070400074102e41c0507107480c01000034141c01c02800d80b0362982380c17a10b640a8a0f84c0d0381c0c1c01c020a50050480245a4140510400c000303c0c1080000c18401d4ad51030700c41c0d504042044201c101d1700708041c2102440395101925840024070089801c2c0e030028024245010f030a00349190309801d2a8942900ca0b58a20565080000159054000400301e030701072039644000d1529498126002403084070700203464200c1703c00c4c2000040715502000c2507031188030708035071845225503110b44500e4580da009803902c44020a88200340a0706005600c44460741c1c030010116005034204001e050300051141c804d880041c15040e00516000d002100e54901c25803140c6500c5040d90600480703540c100f070003214001d258404075034441c1e0443e44a03104000c51103800540c28240c51140180d4158000505400750003120314040c00940d044048090190800c00408a015030414600400010341c00c0d0803d2085c18207002000d8126030414240f007061a00194150b81322010146540d004d081d4182c4 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 821368021 1250 821366771 821366773
    0xd0203071415090309090f0c0306010c030e0a0602010f0c0e01082805250203040b18030115080f06070503150402071b08010b13090302250b040b0405091b090d14 70
    0xc20002042c1004c401050b4010044580a09541396030100d140f13174941c110b40e10300400e082000818819030060405500c2103109140010a640d03440d00400d006140030390000300503030b4449240c3c1c0c1480d011402040303138142207031410341c1003e41003800003040d00c0f4015210f00c492041c587d1404100c400c4002a0200ea1403100b1720a105908116100c0418004004c006080c1c041624101320701c500c4c80803045404441110007514140f4585c4d0004006c1e0142c18100746925641c0c43c048010b0300b0b000052004000c100300c00250143c1d0007840360301c50500d50002d0581d01001801c200300004001c102c2030302440444c081d900181c4542451500c2c88082003010091032942301601c400003420041500107402007042507075140e0810700407075809000d1313800070310b002400f40c0c0100e502c241e41d061074810b03055640c8031541502000c1a0f40c60454907002d500c03070b404ca207101c0400014140719504003a4003490300000130502c0230000e60306034410f4580a0240700e441d28801d041030070b42142840900c030410280d40a01e0304c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 821369271 1250 821368021 821368063
    0x80912030c0f0f16141f2f0307080f0105150c10110306030118020a1403070b0706020d0612030206040b060a0302190602010c09120326190e0d02030714 66
    0x92024030307107850520801c69100d001645142c500b524003182c0c00070300307840c01c14000c401016260a90401f03411008040c1c8a0318440b1540a121a2040104a440441e044420503074906204c540100344071f000501c20241c00c0690790041000c0d450b001500c48600b00c45100351510f5802c800442800c00d1183d5a000e06014140200540002c00c420000d5001c1c03201203000700320444401411080c000c4418601944c0043c0190041010a0310290b03001901e20006040c1e8140a0319000000c580d600315460646041e40e001c0b4006600100a1280b04c0c0503240c49058003007400d5040c4c0c0c0080d42c549004100400d0503008401040320f5407a88040f080c0070b90382c0282440c40b0300c0c1041160801c540031602c034420066007030401128096008041040036610000d06e00f443e414140d80707064451110600010040700403814208180c0c8250b104000d0103800c285114182400c86200703000700303803920155055810381140515200b210740001c21904080c1d4008140c24804440100d800c0c200110401e10344c05180e082 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 821370521 1250 821369271 821369287
    0xc0303070e0102011802130b03070b03090601030c1202030d030b0609100804060f02070503031503030d050703051509090312060409020a181a1c050a0c15080912030c0f0f 74
    0x1020010510900070383c001c1140310592000d548001c5c4442d80e0294210064034201404d075003443e00000c403600e001504941c60b2070360718401480c283d802110f010810707030020b40c014002c20080340d04030303002008641440350b008420b60700084e0f20f4984040f10402819076070711052145071280380944181c100700901c14020380d11501400360158408450403183c0614103415559802c01c0e41c82907469241e041001035040d0750319811448000c0e010228840e07414441804944100c0001d80255440b8454955000c5814204064000d82c400c1c00d0021035480780b035001041118480002040e00e0716144002c0701d1607040d8803000e000c500203041200c0080d42114507000080780c4d640507040302c28262000e042040050500c906081c0001e9a0340c2440306038440c881d20800c41c003002020a8694982d4045d8042c0c2c0c0e22030030280d44103e33002c4144e030f004140c03006081100400c0c403a00301c500194800360f0100034148580c5070518800c101e01c07006200800100d80030034401400c8038031500781d45030003052090140e542c0c444 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 821371771 1250 821370521 821370527
    0x6030c1d01090213030803100e04110907020109031e051b010b03100b0901050103091a010e06120f070308031009021c18052d030403080a0e090f06060f0c030307 70
    0x10108488203920a110001401e0140340c401c42d0607501507a4100c07040d4a05550f200c0032190f001500320407500381c500302d0200d080d40954000c070f80a544503a01c1000d40030096002c3c001c116100800c58070039a4540342550300420740100c01c1842008200c0c0c9020a50700a0300001e0f1198042c480d1210300c850f0002640d00c284001c154049081d00e5804c074101c80348050305450260599400d4001640c015403590300400072540690840303d0b00c103100e16400101d5200224800008540903803201410701e100006203d100c1c10201c3c4402c08402128001d020b101c041155200d5641d410307448000c0003414000700107103010309500040740150182e08020b40d85c65040307500c03034095014400d04490183e40340c80f281c02075180d04030884044050b8440050300745030070480b650800000c4c082d0301500f10440403500020901c03a05000400103503120340641520740c0d450542c006d04400d04240c0030f03030207114000240716034510004442640400221a0aa621085402c0d280a240a4406501030f20300c0040107100717210750 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 821373021 1250 821371771 821371799
    0x1230306030a15051b07080a030f0e01020703090f060905060906310509010e04050d080702010b060a1d040c05181306080a020102010e120703032f040315050705030c030a06030c 77
    0x304110b118002254420030b036030506ca9014001c1c0540c20411807415842d000b03800c00b410306070410b0000505004d4003002075003680d202c154214006180c00a0034416062491440c0e805050240340c100310302814000451035a00ca00000b10b0720401001ca4080080c04100c402084802c40100b884e40941705c0500028a85440a00900748607000c4500081204c44003040301c41d2296130400d00a100e121641503050320b841502501d514110754a84030200007a4803810002c200d2140d182d81e500d480c0c1c249811a0f0480310440d01640c5105504103640003c09641c008152802c84661141101c1c0d1210b801d4002403d104c5040100e910003418080b000490b00004180d00e01071a0003038000f404500384a403466900c80d46021410624070318107101d8000031078840e5000c00c00c101000c0c004041d92014540d0182c030303c2640010079041c0340d81c1c005020b0082002c08070062030403050b5031320281300504044001800d140030062001d01c402e81e0200005100448640021000395000480d414885843d80c6030012003034 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 821374271 1250 821373021 821373031
    0xb19020c0f0603061e09090c0109051c020108191109040c0f091806170d120606050304030e060d1b030c020f060406020a090806090307060b01230306030a1505 69
    0x4010001001501d0810740004004034000602c40c0c0c1c40e55560800f0172840c0401c4145200c1d00c48039103c1c08410315111b241c040341c011101c40005190020000c000100a04210342115000780208001c1c1100d0252803920340310300319424200440e003961284415110708041100058085007418074540c2152141e400802030080251004e04c03801900d0042640c0c0d030340040541c140010481042040381c480c030700c0c60301d13820300301e01c8007010070301c02e03654004400304000710850884540c002c00c12840705103401c0039a40f4140c460a00c001e00025203082c00141c649e000050001e414004a5007032050156106001c44100e110940400c102c2c544860051401c0c44010642d034001080c900003d00703030807500001e50030060307000b440018074403541c6990741d0b1006500300d11088414030254580c08074040c08280b00940c07090190b0001035446000c03505041007920001c0148038140f01c5900100d0784107005400d80b00d250491907502e00d1b940c94480303d000ca86040380c1e55002800c0180161340d50401c810140c2c000d00c1c022 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 821375521 1250 821374271 821374273
    0x6032f0a1b020906060c03090a080d0f090b09061c1401050f120606040902040204051002030d050f09030313110303121803040518100b04120506010603020405030a02190b1902 76
    0x1020050049a800040c18501a5010b030003600062403c0c90702c9001060301c6c003001c00c260390500c000800420198425908400c0203500300d4002c410803983d02c4030315031444030020b280802c0d601c1d1421030940460b00c520300c2d00310b001d0400060340e0310141c01600304103100032141c100201700c030f918000b00d01c2289007020300a5a101c0c4c514007042040d02d140c1483c10500054018004d4145a280c803810400281510b50302241c100d030f001d000001e22552541c60540180e0000d4020310b0360340c481445d001d000c4600051013103103103600003001d0010092001055903401000d07030380240c200343e07020b007000c2c0e4000501480455240c40300189285160510f000c226020b80e040d4603c0c00b04c40078849543d15140c0c0207078000c2c00d4000d61030700c484000311103040f411607800c6041a100c1c09401c1e030b1981000d0400b507001f600300100e0100d020004104014080021500500c1603240844c01c0c1801c01001030b07220703071041d01c010b485400262510943d212849500000520700f001055503102c106034040e034414061f400308a805 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 821376771 1250 821375521 821375537
    0x403200f07060302040609180b03070303020d030f141611031305010207120f0308041a040308041a0403021905280b0f060d0602072604150504030c06032f0a 68
    0x283c042e0094070256019030b12222001400c2c0300a20304129000115001d003a611054501d0090720280310810103140a41c0c040c1072450b02c90340003d82620702c8060341d0b4030f0403450141070140141c03440303401d030b904060b0305600c0c06860b00c0c820008a55509031011500054000040c2c000d01c071542c03100070041100c0082e0252120310303503510310b134004200e070394900503142c2182d0800040000b4806c00c03540d503000d44502070704c10013510008055601c0c240c0413a41100490081c406002c244001a00d0a15115841040e50500352a1541d4020340f00c4170300c803900e00d11650002e0400c0e0104001400f412900d81303c6034a0b035101c2c1a41e812a8460b00300d81804003910400540d2001c16914011090304900c00d041c0a4110503240d141c0d40e8074000258000081540c4511010600400000000c040310b08000c3c4042582070311281081c01c00e2020300c1040b042841400f004010400c0080c02c1586178a0880e070440c01e000038200b02030351184034110903641034031408501c0c1c0344103610044004405400b8034012a62480c070 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 821378021 1250 821376771 821376779
    0x7080102030408040b0307091e031e050d050d06080604050601240503041502090904150b0d0201140a0306080304060309151a0d240e12130e0403200f07 66
    0x100300d00c01501c000d41058420841808484011002035030000704626005600c1a6904100b207120410422a6a016003c0b101c00300240503180c03240013258041003050610718211550381542d120101c0d201d5100f40f06011a0001c41a01207a04c400011315140041c0c450b20300d081e05d4020384520090007050300c05e1084d1600071407060404034800244001da901c40502c2c544441d125483c0b56010460380c210940d4003080b0845494550910072402148641c00149000ac1c50320705400075142e929003910300644a203901d400150707a02a40c0445054941c981031a51104813600c110080c00e03281c1c100100c548170000c2d00241d416415800903221034001d01c41e2001060318203200c801a81d440030842c0388e8902844281614501c0c019a0700c2032241d10940c50039580503a04030a81080080c0b840c2c0c2000000c0d5244030b1a564640c0500c504403a075611007607030f00d00d000300300701041481440501800c080940a00700140c1014080c0c211b0007901c0800d84c074000c02c20300d1620070050b80c61340c50288042d40b500842030001 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 821379271 1250 821378021 821378023
    0x7030b01110d02011b0503040b01030308040f0606170c100c0f0609060903020f0d020d051209010e07080a0b0603120415230301080d0c0b012702040b090117040b0601080601021c0305090708 82
    0x90141b070f40044049e500d40d01e5038804940402015000340e07100c644100541002811a01c07800c0000e015400040c010825080d84050402c1e19a6a072a406a188541c400d11f48503444021a000907501c8107259101000a00704a002099000300c01041249084c400000345500000c4040030a07244070700310b8085405c0300808a81f681d60500c414404118240407005c03502c0601100c1c6c2e035110040303000000b0814801c10140d480c1c8440347d806000c1c540c01c008514402e0240b00074106501500503001009130341010061014070384030354070600b400c0c4001e1341518860f1510030754200c04c10b444c0c0210346910384110300882c0e00c01c0740d000784100312403442904401d440c0d0902900b4595026504010701c45000d03842c1048961119440e5640f001c0406c0d01644100c0b000001440948041c1c600044a10b071600c040350000744c20300705100300000c00710342c2c06020080011002590654003500030b1030503154035110000140d150910030440040355041898005103569030680c4824071410403282228040fa84d00c95160f = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 821380521 1250 821379271 821379277
    0xf170c121f18020d031806050c010c0206102922050405040b190e100507030506030a1e06020405060c0d0f0f0e09061212030a0614010807030b01110d02011b05 69
    0x855042080c2c0d440b040c000d0310301002400d203680e00a01701107090590b03c4c00942445902604124041000030071038180c95042403082e45001540c0307000a282c80d00f450713035940b10492401d12440720b0307558211001596141103000317400c080400c03e601c640c0c0c4500c111b04050440c140c80701ca4400024492440028007403074280692030065401900202507901c07649074400780030741a82040e6160350f0b11084261582d11003080044400080500c0000e090705140344c0c01005e5982c05000c1d284603038081d505640104503484032001d00004200094154840706252440103409668041c1e5803000b408200d01d620004046800d0326541510365485100f100c40f90420b030b4100070443c1208000800311068800e042c01d10340c0985820042c001c0445160003104c80542d46405203001003145a00c00210521000b44101d02640000d00340708140d600840c03402c000024641305000341000209500c50300300d011164001c0340c03600702c94081030060300c840d00011200a40a00049025200550b01c00c4410f040381620803425 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 821381771 1250 821380521 821380541
    0x160b0d0c0c0221070506070b040212060402150a030605090108100e03040605091c0209040c030c0e0c03070819020c03090108010b07080a0f11030a21060f170c121f 71
    0x550341d21202c0c1d401800034880c030703c10034003640e20903000d000c1899a40d1101030841c4a214203440070070b510705441848420036420080701c0c02030303218605110040ea0789100715090803030600e44a0b92980203070301044028000c00d0b440070b44c10040715000031036814408144400341c1d0018000502a880c14031401d41c0d500d20a901c50b05002490a00c9040708501e00b000c0c0071540c1c2d14a0300c41c0201c001c04036400240b901c0c4030503030342283c01c0d4414050400400545c840350000904214107c0c007007514001c80b00e46110322005103032a0810403141e0000340f84514008406503644001b450454540503401e0324155254000134031580445ca1100c000150000c2c01c0f011189003584c0108194144229110241c945d001489102020301800240346131149a04001820a820032951000c1020345c040d40c4203001c040880802c50361140c00d0030000d204a01c5005804400c440c80e0004000403003090528050501034070000d411b83c06400702d01e2090f981100054512440c0e10540fa69031246504010940d04440361032607 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 821383021 1250 821381771 821381779
    0x11060912030705070c0b160b090a030807030b0121290d020d0c0e0408070b0105060c06040b0726010f0f18090201031404030201091704121103160b0d0c0c02 68
    0x50801d840760000c1c0070b209201d05604421151921030b106a0b03501f01040d40d541c3c082010b060324090180a000640c0c001100d00094103060711552802480800003c01c12010302d1f450b0403050b00143d01c03c5181c100c3d01640f205049401132030084103900030f4040c4040c0c0204e40c80110040001c290146040200e0002d401406620408915400e0200001d10241d05030b40640032103c3c0003030b00039006500300e03100750f2240010a955804602d04002044010382000e4001c0005100810032568001081908243c00c41e031031542a6454030700807102c0c250462407031898281103444d005400c581c42226641a10b000b2140050083c1d12140008454503041c8204030030503885208181d40c540496101020885c010326020844841100400e2140d41c015a01107005039960f0f140c03101405040c0764040c280c9815041c0641c541407903d13001c44a64072300b0420180690043d842c1035407017070741d0401c0301100703401403408105101071b40d9407080342031900b1802e003017094141418800003c0a114181000c4400d0b4014 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 821384271 1250 821383021 821383027
    0x607031116050c030604080903060c0f0702190503010e03131d15040603020a030b06031015090509030903012409060b040e06010207181d03130509090102160311060912 73
    0x440d155400d400d07040815034090180001c1c0200070b88042c000d8910840c05001c41c1c41d80c0e4059042418944403000340828806903043c811040402d400380d084491043e0120340c80c0c41c8140001115018006d100d0380700e56850341ca00244d82c0c100c0240880606030b401c2503006a84c2c4030a80d58211154204428800155107003501d40014651401d550220019640098400901d07203031a6408100005455003040e90781c0e00085041010750320702040a003245a118000030f0102088200c103d01e2814400c2c05210325464a940004427044010419a008070400600074088462940b00c4901400c4851892001c00c940c4201c010584032414000c110071511009640c0340b0742483d04640648262001e416641140540000040c15a46d481c10751026824104c8002404401005880203040b200090705443c80d0018401051051801c08c5803c04480003643d04a03a41d50b1888061340c02031040144400910044502c0001031540c404c0c05407003006c0c450030465416403201042e140d507440c100c529100b002a010 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 821385521 1250 821384271 821384287
    0x3131e08030f0406060509041a13050705010f0210060b03041505070e09220308060a06140d270b0105040b032d0a05031c11040806070e130f0e06070311 66
    0x424003c2c0d010340542800244142c650001070a0100f060382d080d80c00716041c0b035030b00c005640100074180e00308800711404807000c0407d68880352224514840d09041c44100c815440000d0f00030f0042085508854008001050701e4800a545a4000b6a015289264481c00e91400312580c0d204e014001c0c24980c444210400c2400c0400400d0900100314414010b6002c012844403c0b8101303e41d0310a600c29241c0440e14030380041444900035160b0300035810483e10b040035907002d80d11101100e05046620001040000380b01e43c04803012910f070b01d145007071401c00500321424007403840031080c1030f9002128180110355030401099039410070100750420b40380d02280c02400070450f02c800000030f900b88005891116820343c9886041d41c0249038203040300d40f4028101c5590310140d20444c03d4002900701240d00b020b0508000b5561001e0060000040c06038a00560070541d8541034001c003101c8402100740090851000184060005c00e011042c09209540c0070802c014000d0040038024240c0703100d41410316840c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 821386771 1250 821385521 821385541
    0xa0828050402060d09050705152802010605030a0b010801050c040311010e120d031b0201050405060711070906060201020a09091b08060a0f03140f07050a03022403131e0803 75
    0x1014000703c0e48054104404450004a4010419101c1c058405000c082e0324150601c0030180036010303030a8901800b0004900f039801050300c44042c60101982c2021a0030318248140d0041c0740c3c68102c070364103110b031790031440401000c4c92030281030b551340c18020f100319140c4d4503003803c5500507808010300505590302c000501d548500c0e082e00003040000c14000c0905c8410107030604003050810750100280d1540202c0d445450b00001c10216040284020404c82c905910351645510380546274a081041d45010004005402c000184c0a0000030004005d42940d880c2d01034000c1d80032121030000705415210000d46100e0300d01c034400032003590001044089000005c1116005d0000708a541d100e42440d0340456984984410236020714072541085907004425010185000b0f0f0312070800089034440c0c4001c1c410368550144032002c0f0f9506a58940c060341100c1800421100340780320b00a1019808020440d044917441e0700c801815008241d0ba442c0040c100700f20500c0717414907000242150303034200701080010384 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 821388021 1250 821386771 821386781
    0x2101051e030709020301080d0e060c0a0b0c0403021302040e090c0303030601050a270303140c070e06211e01020f03070513120609020f03010504020a09021308060a020a0828 75
    0xc0060940328555100d9040c2000c0780c2007a009070f078550f40100440410705400082614280600316001030070304c1c0306244056600c0345103100080181c4121000714101c2c00610064602070355000381a980d00300e0107600303460b00941291007482038139000440811008400810341c030117400005400766184d981c48a005482a511064491081000039030000c4441c000014424922010301380b0003203070261031805e0040600d413030400c9103a1a0740040000907102070300091940f0031503082c41b4044406036581e038000b400e01e100f44072000c09001c00e0084030b101c5080010a920300c0f60301400305e02040c1850189c1005080b40500c0c40b80c40c110cc4401c00c08940c645003c1c0c4098440bd19895440340c240a444021510780c440c051241112070b6510348011340c04620b00741110388014001a0001c0103186425000100352445a108207a1115800030300c070ba46c80c16500d500301e805031201e20126407250802c1c010800096000c0340d0000001140351002c03c0700050081c46441c209080c0c810800b020307030030104480e00204 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 821389271 1250 821388021 821388079
    0x3201032409050303040c06052503110a0615120506010e0907080706051305040c02061308192006101a091509040e0f10240b210105 57
    0x4044014032085002032802094803180c481c81c0a1616405d0502e805e0300704038929001502408000c0c02100401ca41694446400303852003a9404000a4035090035215224048140841c5003d011070583c140302c201d0304000b9880b08100345160001c0e40d0b4003e0b000102c00d55800045c2031303401180041040e0f01c2444074040d00f00000724161001e82d5074030400c50380382181951000300800c0d030210707000390303c80e940801c568000c0c6010307101444040701c81d90380252613400080c03091070403201130420042402a6001503908040070003c015150600c80c2d2030150041e100e11250314502c407030284038580101d034082485030064120b0700c2c58400032070400803e004401d1070500d4806002100740042201650303507034943c450b81d0f520030f0011981e4284180512090718603c001e4801c065200c2c10109003c0c4000240c0a00150f81c0040b0000d07000080c8480c040d03002c10944110b8821032464840400c0c45d86018008000746039007031641591703c0790759000000403400d0034451182c1c880d40e071020710f9081c05020344007420340e1 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 821390521 1250 821389271 821389313
    0x270b0f04090503091f1803110603130b0a0f181101050d0908040e0403120606050f09030312040308160f0e09090c040906060611010605060706020912060406320103 71
    0xc1909400810308171620040c0e00c0c400c150040c01032040098025000d100010b0001c2d0522581d01d055407a50480c510f0f1071080540520000800521240d4410f00f10120142d84044aa00d107410b0000810028042040305105a146050074860100082d0b10110310f10f00e50107031400001c50600001520b1681144001125007601e54100d00300160614000704003900010081c0d020504050a009180740b04c0801c0107554185417031800d010312a00a015642c460790180c4a05940e41807083c04241540140103400d1703001802201840109034120b00d025101d100300011011001c0c00e41801250488900b80c3d54201003500300b5000b030742c50b0070100c0b42c1c0b9070f100080f402110041c141a5000c2802c403451070718159652035958000f489410b612014121521504e80000d10455003080c0003d00325101d0818003c0603940e0001d9180d03081d454503a07880180c40c0d09101035400b6071401e824444d029010100b410110110b0540039140003888104001c0c41c80f01d0f0f00d00c0c04c020182e0859803815040a0902940307100 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 821391771 1250 821390521 821390527
    0xd0c06020d26130b13140303091b0105090a0e070305130803011a0928090b0f192303060105120a060e01110706200304080a0f0e0a270b0f04090503 64
    0x4961a1359100c2d018550f946041c138078808140c03c20a407495a1141083c82c507070000c00c00d1000088000a5101d91114400c17591103207422144016240341c03050b4a900d81c1c200b40503c4000840300e200d07282c0d2512500d05900c06104d030303039102e40807540070284801000342024010300c0144030354480f285000f4a008580c0703240c2450311341c03407800050109544202c00844103400010620b01342005220300c1004208100c0240840341805001515040071550002d00585003440d41068803e50b81301d002c4000c09941c0440503010942d0700416181c080c0400c1e41c0c0f8003a224500002030386003030080401c1a14004000a88903030030099031050003030f00040c0383d14802507490700aa06414441c210042c8103880c441d0200240300c0d6840c01200700d160316048440344a0f250140100004242d45030115000800c8610304980320b01c21500c1e06490b080a810126900301c90955400f00d1550940e07520728400420300c40c49a000c09444951610603100035004040c2c0204d02e0540c42d8405041980202a50034428010303642 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 821393021 1250 821391771 821391773
    0xe01051509030a033506030c0406051c02180705042102280f0b0a03061509062307060905162114030f0a140406080714090d0c06020d2613 60
    0x1003101c0700704c4140517200042c00d20159140802210320008025103040c03010341d20b450001100d03c0c010221890703449107207404000c215640c101003200002c81da034114200a041110700100150030500813100d4640110000a84041c0c24010784886030358020720300e4103060140c0d8074809540a00c05084140441c2c2d040b40418250700d0200b80300d001c0e1031306d44032060b152040700c0e80003000d8540c5d07903000a4901c125210100c1c191588607002e80c050f140c44d41452443c1c0c5e260440c3d007409190410040e00b8620340041544c0d010011160481c054843c0281c0440d100c6501c00c4410003c41d100c03034400c02c1c034003034100c9208644181400c0074940c5228001c034580b14081080e08083d40c00e41c0e11a40070002e00860004400b00c4041d0866611500e2905020109080c0760400001409004d00542110207000c080c0d810420703044089000c68003072080c007820b0403031409481d251030402801107000c1c41000d4010002c407100198460000102c114981d602014120030b01100c1c40080070f00090302c071904250807043d40710 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 821394271 1250 821393021 821393087
    0x706050106030c171e0403022406102d0c05010204031518110616050d030c080703021303290103080a14071a090c0a0e01051509030a03 59
    0x40c0200440d44000c07400b00f40d86a0002c1541c0002074803540c1a0300c00100f407010b9900c100c403c03d500d50200c1c03083d00800740c48a040507490807407400c0ba110ba483c1500c035400c0c0b03906400c2c980000d004402c160340a1100d01103251003901c0700f0340c42c4003130000e1151840f6034606404030b4181340c0c206c00407030a050402d18014a17407100c3d401e990003500203545d141c0c0b08008482c5074071510b1040f0030100131000d180c01c12110090740c4041c90081c1094401d0f104003004110500e21820705a80a18025400304c03c8402d01400500081d001e840e60844940101d140c40d00040c041c540a4000c0b141c0301140c0b00e82802c0818110340e145100900315244614200340c40c0d290441140c014a061903020f140690b0080f41c40e490311460042000b80d0071082010b00b41c00c02e01004000030401403204120540317101141a43c2d6a8001486103820241c001082d44040040300000c2d620510301442070580340b058803244e480b059001c00040e1144684007500341c16902244605d802329100349a0801c299480049500101d50110591 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 821395521 1250 821394271 821394281
    0x50a1205030124050d1d19050d0e030c1215010501140d0914010e03180102070f090b0f04020d1d0c0603040b2823010e0a020c0f07120b09030c030f0c030706 68
    0x5006c400c4c010001a1460b00d01000000300f010a4145400410521640c5103600c845c8001c10000a00007960b00d0307004503a606203c4010f860342e02810f01c4a8501101c280c82d41d4070303600e0314120006045034000100b00c9500c40c0c0c1e000d4001741d50341402d80307142c10306a644640c02881024402c0d40c1d00c04011a550b0104130003030160550014a00c0002d6856400d01d40300d0191480039100601e043d544181810008185100f00220480e90b074080001070f40d480100100e00c2c024011058541d20a100003108004400c00d9485415441c9083d0749004c0aa074542010340d9403440075842513030740b00609000080c00603904086595102c2030401040300741540c0d500d1403038180c3d203031403d401003141d44075903190948110201c148200c0724401c0d10503884c29407501c0511070381044060108000690002032845102000300310314290114030604684a10f07561785172034202100400c0c000c481541c4100d0105014102c000b06803850079125030041c514003140342404400f1a8405260700100740814000d84000c20024412 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 821396771 1250 821395521 821395541
    0x6070503270a08070513020c100c18050111060c2101090501090c0c2f0904050f07080a0c061808060a1508030c03070b040201050c0a050a1205030124050d 67
    0x568140780d9001c01048814401500a0300c440ea100e420108103c5e51405210360440c100000c0c01a1f8500280040c0e0342010741108010552034102007000030b01951044988070307584102890b071826142c03500011620f034007080301040721035480280800c268000c000020a0310742c51801a144034102c840d1801c0c0d6141d0b009a022108140c3d40707600401041c000e034000d036040c00b0201c1c90544000104c2d6650814050a000101d0140700390450002542c038419880c481090b44000380203008510b080d01c0c1c040d98500c3c206c40b030400300d4014900001060b100006400c02c420303500c0300d003c0d0340782420a03100300d441c0d044010991a005c045038000103145142070019074040c128040b03002c42c0030780c207503068012102d5003030340070941940c42000300c013480c00408415982c0496003c0b0001c042915036000481d05030080c0d600903215402018800710401c20002468101540f280395035030f102d000f0b541002e50f00e82c0801d05c5180e8a031008003003900002e10075202030444000450400e141402d40550201084500d0020 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 821398021 1250 821396771 821396827
    0x7030209010e06241204030201180c0f150c0605070201020f0703020a0506070503010510050d0b0301060f0e100b090f130608012301060516050a1a0402040f0e0c06070503 74
    0x1083c0042410f143c0000d00101d6109100341c4140b9101c820600f100b4480c2084001c69558100040fa04052003074200360004000000300803054501406c2820441000b84112061080d00200005220301006100c00c40d00043e6110305101c6562070f00c1b11006000000c000383e04556080001d5494031100c60080c1c031045000b40d005141502561070454a0041c0160080050000c144010041355407800450380c1a00041d06e8196210348145203800d02402001c1062903265003440e80100b00125034260580484840c1d82603990319440e05865000036840e140034291407550100300b500610305098011680c5400050841c000c1c401c045005642280c8141e0032184550751252000c46d0060403852114010350f0145c0c000d080254500300c0d02505a11407600c19542c0b50004000101c01e001090099041b000d4000c0c02021421308015105c402c05401110104e225a14281408030345115a1050201c0c80070040010f1540100e42c008102e82134005802c2120284010040c02459008004100c9045a9010 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 821399271 1250 821398021 821398049
    0x60b0f160c24030b090a2a2102030105010c02060c0a060e100f0219031d01050108061b0c0c36180f0a08030c0d02130602070503121b0703020901 63
    0x90001c50702084000342d030003c15050019601c1d050351051207103500704602c0701c000543d0780305400200c0220042034920070901803904480701e01d09600401c41d2140300b82240c03494803440568510b02ea040740401c0c001c0c02d00040310b070368861006060120041510640150844805a0f62981d8410940301c11905c0d00c1c01540100f5058420a4603900900513400306039481581012a20101f2915040d800481d071420941c071141c400c20b0802c108101c0c21b4801c140c5000900076036844412140d41c3c4d850543d404000c1015080e440075960040c10107a80c42514400090803109120800700f204003144c80b981034400364103124459000140181315200b61a028020300320552611410358481800301304542410b581003004140d80c640d00c0407850350a2305902c040450303140e454050001206002c2c17440090b0156100140800328070145c90007c50490300d030350342110304071620384c000e00d80c9562800d02c0003c4545001e01c940f00114003050007886503018800100c4074203641d00c0d00024040d071002c0c2e1100030300742c84035 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 821400521 1250 821399271 821399309
    0xb0f071205190f2004050904060203060a120b07090f2303070803070501090b060409050703080a02010b0409030c0b01060f090605030c13180609050402010903030804060608061513060b0f160c 83
    0x4d11105588184481000c905040c80c240c00f2032050034000303000810940d40040051441d6480610b4540038050f4803101000341101440c0581119005807003200103c2d40035400090805200c1c040c2c0000c2c0d0301d09010b4035080003a908a03003040a0f000c0c483d0190300d4055054040350b000010030203048064040c900200b100d21103410310000b00500600603a01441c2010b51010120340005000d01c01c60f6400158180d90f144100030480c0180041540580d2003403d0250603030078164032080041d4201e002d041e0604150342c2c0c8241c2503c1803a07559901202007072202604004c541c0c09003000d903521041d05114545401201c001c42d102d9941e01d904003500385d10508101050b590490711908004d089410303010007441c2000e0300040d11240d01e61200400b0025080009010082540c110a0050015004a8109080c500454010740129000d1180940300e4130b0346403184002a40521400c035620b601900e07241a00c0084400e225900403031052000300428580ba200040341040036100900600640c003a990b106 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 821401771 1250 821400521 821400551
    0x2515021e03070f18030f14060a05060f011d13061e081906150b09040b0315060d051f020304020f0f01080117070f0b03040b0f071205190f 60
    0x2100301035030600314050003088000c5800c081e800711030060600f051402c41c0d211501c0e00703507010416000180550f42c50780482040110002d4000c060080d15070545026079200d60515003220411108103910590501024080794010703240c0c1803e002c159503502c0c024002c4140030032a1399220f0f040580226559004c01c100303080c119500d8891a19803203840300d00c0c061810441c19580d0b41092080c0101201140800c1d0800506501000207030004046510783e0079038844407002c0315084030300100d020f0740c1061880c191518000c14003594080045c022141e00740c81d007030240b00e0f00b000d942000304c82c54400d4070740f50355000d4403807659000c0c00c2c80a200090780d20b01e007910512034030700c4404011901458451010003150307a001040f0301d040d00c40368580610b003001c10402c450325103c41c5501035480e140d00788030041203543da107400851044d030080c00704a080d0b40301d070301200c841803004580500005021043c0c0440b01940c0b900280e40040b40110380000076403d1552240489900c5808500700725551445d640c80118 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 821402877 1106 821401771 821401807
    0x8010c030902030c0d0510050406110403321f060f03060506180103080a0c08070605090a030305090d020d0e03010f0221010506030c251502 61
    0x6500440a00149240e100a034024000c2d00b8429200c0d040c420f8044c1e288641c484014104150303210261001420040d000b2604252904000b150785280d28010704040c41c06403010810010a03e428030140144400388102c3e0701150207100c1703200031008101c444540300c9084604c02d070022188041001030500d40c01240720207128240100c02d03c40707a503010f80d204030416038080780191005456409000401d100c01400000b04200301c80c2a5841102450540d5120b03001180c00c0c8501580d414080d0b0740700315000c0005501800c848014554580034554000c00d00c840a025000c2459100a454098a18291041c800c03006143d048a807025400410560381e800d108540715010305410400d130044030080040c032045014004196450180f040303a01032640801035914020480b180c030307400b1414006401c00006d540b00024401b01f10059402502c0c030611800040c0c3e54a00c4c0340e2064a188 = true := by decide +kernel

theorem cover : BRFrame.Cov 821223021 821402877 := by
  have h0 := BRFrame.cov_init 821223021
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821223021 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821223021 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821223021 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821223021 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821223021 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821223021 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821223021 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821223021 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821223021 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821223021 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821223021 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821223021 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821223021 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821223021 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821223021 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821223021 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821223021 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821223021 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821223021 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821223021 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821223021 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821223021 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821223021 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821223021 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821223021 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821223021 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821223021 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821223021 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821223021 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821223021 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821223021 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821223021 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821223021 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821223021 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821223021 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821223021 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821223021 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821223021 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821223021 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821223021 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821223021 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821223021 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821223021 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821223021 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821223021 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821223021 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821223021 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821223021 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821223021 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821223021 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821223021 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821223021 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821223021 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821223021 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821223021 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821223021 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821223021 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821223021 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821223021 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821223021 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821223021 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821223021 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821223021 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821223021 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821223021 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821223021 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821223021 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821223021 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821223021 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821223021 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821223021 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821223021 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821223021 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821223021 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821223021 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821223021 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821223021 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821223021 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821223021 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821223021 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821223021 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821223021 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821223021 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821223021 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821223021 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821223021 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821223021 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821223021 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821223021 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821223021 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821223021 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821223021 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821223021 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821223021 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821223021 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821223021 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821223021 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821223021 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821223021 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821223021 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821223021 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821223021 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821223021 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821223021 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821223021 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821223021 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821223021 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821223021 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821223021 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821223021 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821223021 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821223021 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821223021 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821223021 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821223021 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821223021 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821223021 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821223021 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821223021 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821223021 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821223021 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821223021 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821223021 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821223021 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821223021 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821223021 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821223021 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821223021 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821223021 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821223021 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821223021 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821223021 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821223021 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821223021 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821223021 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821223021 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821223021 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821223021 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821223021 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821223021 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821223021 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821223021 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821223021 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821223021 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 821223021 ≤ n) (h2 : n < 821402877) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
