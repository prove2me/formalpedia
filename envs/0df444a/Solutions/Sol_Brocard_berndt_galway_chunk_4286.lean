-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4286
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T12:07:26.449428+00:00
-- url     : https://prove2.me/submissions/07a59ca6-407b-4c82-84f8-bd01737f8e62

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 770683453 ≤ n < 770863309 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 770684703 1250 770683453 770683481
    0x100807030915091e080d09020a050316140d0503070204090501020910020607121b0c0c050414061c03081f1a03150a1d04080d090c0611031206091504 65
    0x8400404e202196461803210444503280010b0100b02c1d071191700c02801100d5003050350079140c403880000c54442c4010340c4014a4060200e41600741600010007020301c0500032150b0500d0130340c0907100c5510304000154645900b0101552401d2035075000c1c400540049003056400390b40030040c0c400140c540e840308015081c4194060501400c1100e001807030070102042c200e10150801035400c2c034581c1544128440e03107031141041034011200389440c40c0380c03034078503880158001d1404598685d440d001e6003500d48607601c200c599145100c0c00220f0710020903c1c1141c05400100020000351943c0c00c08000302064040c0c1c9002058281d43d10022b003200c00640c14a002c1010101000b4000310200f46500740c1014002290120061401e05102540080c41d426031090745102034000b103018440c0041c110369015204490a12034003816003000b0b03e8400b020311032040051302c8141200566003010051360360061800c031201076103171034603400c1089041001d0400b03891000c030000c00c0c0c00c40390340d00d21039014845518 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 770685953 1250 770684703 770684711
    0x30c16080705010b0a05010e0d020103140c0a03060b0a090e0406090b0403031a041a011202090301060f0509070305131403521b0f0303050706050a0209100807030915 72
    0xa01e07202e800d4a1200f41304134021000302805108685c0c0051803404030700d5040e51121445011800100c0c00b03030600301c09640d01e201d0345105020500c5411402411080100e440a0026a558802c51200380c070440c80900c0008400d10018440c48184001c040e400c18000c140104450300180c03580e5401c458103840c2140030aa851810040d03a0f04100032001010304115020801c0e10720514141071a2002d030000350f81000b21b40c100b41c61726035010f94140e0f40c00f40c501070002c00915440ea8402808441d03a0b01400d48140182d400081c0314910074042c0a1058080039481100d2912940d00d07200f014034200a1400d4030302040c01050018040660001240c03041e0718442805001200d124000c0c02007440b01c010480070306810a0885880700a036404604da41c8a1f0010000f9045014219042c0c105070304281851804c0c000b000045c50362000103007110314001c2c001000540c46017812881248145070134140c0100089019410300c0c1d0107100c0c05a4081c807a41008160003500b40c0c2d40000d202540a020243d603955 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 770687203 1250 770685953 770685967
    0x110111030a0509061515160c03170c0c010e0a03020301020a1e111510120b07090906030221011806022125051209011b0e0105040308030c1608 62
    0xa01070710780c10141c1c41c1d0103000d05041000c100380b0f111710b605001d1070041c150343c1d0190103096101c5040320f00c052010002a840361030a803800440017501c85c44150f83c248200121413001100c034408940b000d410a03402011010004d1b4010340391250380040c2d066024040e82c50020250f28280001c0003080001d0b030300e44040b20a4a51007040c0c0c00d48100c03802e810050a01d04004d1412000119403480c0100c00c20094841c0e6149213842e000700c4120780091f000409035080c0034042080080580d8044d440540700d0198058407240d400d8120f403a9440040c0d440b0700c601c14484460031500e11001c2d0340000541c00859221249500305011044510044070019800140304540c0c003c1e4005c11480c0d01d0050399503028604103d45204c40c198001903019217241e21382d5603100c40980c021001c4441c0740d2a40a140d06481c0760030100d10380203004d40003c0140100e4100c45290100b48070741d0103590308180c1611042c0c105411a1100001904014803100c0100c104010100106200000781c0c2e04151245058940d9181 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 770688453 1250 770687203 770687221
    0x1103120a1b0e03070302060915070b04030f0e130f0b030d1112030708180a060c050d2f1312121214010b031e0f06030c09010f1511011103 60
    0x852881c040c0c20410301c50a1604155008103c0c2000c8940466000342c444c44258001810740d422140210007403840080c07060100b0200c90a500c0c030a1380a600d44210580c8486425508001400b10b52079000703840703102440204615038000100d10f00b01c400005495541840403902d400d0124801d0404182c3c0c558507070002d81010020340d002c600b13405041231305505018101078506c480c0078000d6944100300c01074a0701d84d40da0822100c400e00790005e80c207203c40409094050540c2d8170403000c0d100c0840c2440d030075040346407034103074004000300740d01e0880307441c03410072401b0b03580c0303a801c107095501014102c10000107683c0034120441503c1d5000c1e2410030030321583c03018054000c04036480d13055816400d02d9400340f44c000464a58504403914110310f0750383c80c1d42e051014820b09030b45085100001d043d5500b48042c10b4180c1007840d20441c0140c045071500707180310040004002c424420070040c0045100f0602400a507100d4050314450309080c000c1019081000860948460110311550a1404010454034203 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 770689703 1250 770688453 770688491
    0x30b0115021906020c12071505070c1502090a05130c02060f070f0813020d06050403140f1603020f030a03050a0b100c0327061d0603161103120a 63
    0x5140020000700c103000c0e00480c190080503802911144e40402d0400c003052040c00a004520f0607504101c0d070320a024a007808035421452120381980340392000080c3c44502502d8070841280d00114440c0c1c9034403090100002950140491a0b0003240c0c0703400003d001d445504086191140820001c80d215000cac2c200285000c100622000f865030068091180c0d190300a00c41c83c1c0304d44641e1901c81c0c030642e00c420556401c040024002900004600c07811428443d241c0d20441c0641d20a070b0310341c504840451510a2140201d80c01449a5202003000800300392581f003054020500c24015180d06c0070003182d800c0e08603000b2076452004240c0722803c020b0848003600c00e0303080c254421148103940c081040c030010100a28240c008051251400c9030183c100268405820070070000a43d909810782c03640030081906c0c2c02102c6032100c12055006100c480c0c50440e0590740f1072100031030300d50010758500c0c404861240444c0050f0301c0c507000400a9204500074920240d105807004480810021340c5c0c000d40000300c0c = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 770690953 1250 770689703 770689739
    0x1119080a0f050c0f01050f180603091608390402070b2508070f0921030e0901050906091509070c1209032003030405060408010b150f0a0c110307030b01 66
    0x2628126148110345d0383c0003001c0e0b6484c844503001142d100c1c1907141040c039805c2d80d0b01c20f10300d80c040808010800e00d220006404074484880d400300314007a540c0c44011030f944198040556008504540a16110b042000344140d1454804a040600480101f02160884c1d100c3e038401d495000240d002c000003071001b00701883c4058901c4032150b00c89100d49400410145000d884442040807511801031b40b42d100b002d40388040d14a64103c00c191100c0d0800014482411200c2140030910880178124149031442105041b250050703c10003040c2c2c1d80d102040b4040c9001002e00703104e20300d070300c02980241d16000205403050201d034031117000c20940c5003810b52105400028407800c001ca11202840022200388000100c6021200c003c3c4821865000190031800380f0b0b00016000f0301d0105000174106015044071790440d4040d10b481c0503a005042e0300384094172404000d0680e040040021407183c038401e6004103034890003107007032940801016002a080140c0307680b040d1010a1200018800e60458010604d94 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 770692203 1250 770690953 770690959
    0x180203150603031c090215041a04030f02040c0c0f0b1023090705071505100b070b04020607082701030c0306050136080a1106071119080a0f050c 63
    0xc24079001002030360764401e100640320035004807840041030140350b4012100d070039802800030b0304402074000d8210094100e48035818850f58940e600c0f02410900104440c00c6da07070049841750b0103212540910020340315600313148081140260302c40010130b020510712425144255424403680c20880034002d141c840c2d94000f96000e038040100e60720102580d0220003044217041c1c5444505a44904081d9550300420602810071f0200907c21a0100f0700303540554481d414071240e200003181c5420444009000c6e004000b480c49103144003007409850010041c08601c0c0c400c196840c581925109a8502050b21a41400009101500007421036030140642441d0300541d203010800c440c58440000d000d004800900e8000301c41e00300d116980c4210b0304050140780c002c00704211904a55454107256030b15411030050310041c1c0020841e00d41da103050000c0710903882c2c0003c01c0821301064842044407d484601000d884910740c0c50300040c118009001d600701c1e040c082d20700c90501d01400d040c0306040644145034588 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 770693453 1250 770692203 770692243
    0x3090f03050a0c0b121302032d0118030f0809070302210721150b2119030e0907020c030d020d140a08040b0702070305120316090f0501140904180203 65
    0x1a05054840b44958846c2d20300d030b203550400c1a10b002080c02c041c200700c40e6945501c180d00440d00c1185141704c01081606550008108000038040711300b40e850749508004000031104441d8070019480b50607010b070060f0b0b1380019182070030344da40e0000380a06020f1344100756201c042d5005206ca0903003444105c0040031001c40224403407891011403002c500d10340c000107100031501d189501030300050b58001d0501940c0609142c0040071020600c450f000e613201e40e1250540300e4000d45c5c502d032032030b000c0c8132650b0290b06071128210b00305500100841300074028052001c52081c030004e1551075504000b0780070300c024190054a201110050000c0c0610601c03020006100e20411400307206581c04039186030720541088459003180c81d403040880c10440503034400384c610b00c145540381412588400041d80100701d480e9030a00d1032208054251540d0b000c1c7d10403400d8821803030208101c954003551160000029046909280c8207544000604a4440c10300481031407101102400440c102003051844a07070607000080 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 770694703 1250 770693453 770693467
    0x18100b01050f0a090f080c10021b0904030e100f030b1c1b0b0310170c01020d050d0f050a15080609071a070f06150914040f03090f03050a0c0b 62
    0x6401c601c00d4007880e4007889400641040c0d83c920860f0f0138401740c0329000c0d06000c1e03540d079640b100769034419546489120351015100b82010600002d2441400941c11450348400c0c80c0400410010034002802039007442071180e034480c4030340d4940d0204900b460b8581c880c0041c5520402004003110309035202c1314040c5c3e02c100c6d5440c007601d04040542c035059902c45002e42c041490703401101c028005030760000c0c0c0d401c0b00101c24000b8030400208000c05542c080340324040f80c445001111550b4016050080b400360f0041805406914450300042c07949001c80403012421010300b941e04422217104403000130711701c0d80d1a81c1c40166044891101c00c001d160a10042c200c0d410640c41c1c55440710311511501022801002d414500055401d05480c0c1c10358021001070500c00e82400c060303000d40350b02010041210f880d6440450820003621030100080388941c1d03525819611680c4c0c01344030145080d030550030300140c6200090960a088400809580305401800410b545480c0a40f800c0c18284c00949201400744084 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 770695953 1250 770694703 770694707
    0x8060d0b0a020f04080703150c0306050906131503030206090d0302040315020306240703090f080d0e060c0105040311070e0c090f1302360d0b07030b03030318100b01 72
    0x290303420101d540c074010703559070080142d41e00301d126580c0041d03010b02640b0400424000140000300e884a02c442003842a17004125040b801c6880d1342c000c059014103400f0100c1d030300f424080e00149008080f0035000a54080c80309100810014079401100168006010070400c44014411610b210b1703da0b040540c246800d40d640d0031030710b00c40d20314040241a030120000d00560340d415100d11400c0611070141f0709924140780c003440f850380404016004103400400014a288401403020200c60b5403070060b02a000642c601100c201480700042c0d80d000d14144551202d0039000c1c824280030724445e4880c0f03280b011030b81e1a03003800d00c011079105241c1209040200030852161408407000c041044640180d5030003024001108a000e85d2580303802c003403010802c2c0354021216014182c1c403800c0884220018100e1101003440c64180449207500007180e5010480061141c400385a00000d0764200803c6811607880441d01d1a001101c0052a0600f034008403180000140540710244410741c0e010301c455842d079000 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 770697203 1250 770695953 770695973
    0x30a0e0717030a141204060209032415010c0b070c05100203070906050a020a051006081e10090218270c03150a1409010606030b09010f030b07121401030308060d 70
    0x501003400b00c1040c4d1841110801d50844002d04075070b4070708500340e041c5410960025048074490354000c1c440d040d400121b603801da070701d180d0300e0310071204092101e6658600e0f084404426441d0250511030584000f400103443d00481c0381c4981950768030310b0141c0006041081c034140e0b840061040e0b00e2320410520209503402540c0c0c1007a148541445076480f600c110f400c9190009848000e000d5008241c0a800c1582550300700c2000c88181d2001c550f448150088031075080c506203c00e640d520303407001d03104080389801500701c01c0e042da00003030141102085070003c1031220070044a2100410b0745034000d9031540041c100c03500b00714201100c010310803d06503001113036544800c0c852000c0c00c48100000179000340b03a40e40100751803035a6104071900c02d00341040c290307000e000c2c58083d0401080c1848500d805a081414029048560030852100c24a107180c50305506854060032000c20130218540c04031700700c60b65015001c00524012084c2c9465855410001d004001c0070300254030a90745082c1e444c01040400d95 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 770698453 1250 770697203 770697217
    0x1507090f05220905060709050406060e04050c04050a0308070201260a09061b090f0b09060304060b030a060929070e01032c07030b060316090b0411030a0e071703 70
    0x2030710244251a40803504640740142c600100b0990a028020b010054042035442c05001152120000e56403104104025180c16010b20300004465400d4080c480c40c0a030081ca401c25075065000d8601394039200481ca810141d80c00c00c0c0c0d90400c0000c1c8410840d40d0185503070400050202e8001c0c0b500c40c051690840074403020b480112956207444c0c50100b80310300781d40101c3c120310725031001e140d4524200001416280c5913200d020f4090385c2169000442011290031200814002010146990f4465458500604282c05141e40503c075444081d000644103108031b0700742c1e9004861018500039404050001e0710490024075507600382c50300500800340e80142c020900103c090a021850349400e545a14400700c001411401d05212088501f4070020041182d6003600d0080170080381d56a030384e6051554580c031007507501e18400b080361010018400c0c41e0340030340c1c12000000c001245940100b450918181c0003078611410581e507520400d481e9000c1040f90100038480032090141c0c6458010903a40c413405645 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 770699703 1250 770698453 770698459
    0xc06070909091a1b041d060a0f0b03040f320a2013090614180a0201050d150f140d08030f0c121f21060b04020702030f1507090f05 57
    0xa4049140f000c1305a006100340b03200704031000d80316940d40340d4044007079018440c1c00103200d40c0031006c84c046040141c80300c01640e625560a41e03e06140039841d00d513030b9000800030350300350000642c1c0c1e00001c0c05403403a41010a0000600600c12030070160140006060340003182c0c4590b010b1041c06d0005a17071507100b9110360b0f5020320031001503503144d00442e00180704280c104546901c0d01e81000c08200180e803003034440b01c180400c6403281c0e6645c90380554100c0910280c0a010764041081e50340150700c07803c01440200030800010070090145110321070b15990079000304090066031442030040355003440003590040822545401c81c1151a1600d2043e0703c000b400380d103010030994001442e50a10b10084400302da0502030130007000e14100c0c1c1002c1c0c5803621001803114000420000064a01800b884520343d00d0750340d21088540710700f42c1e45800040070107941650300143c00b03100b01c40140e6011f01092540c000c806d0054840500310917035100141d04020007000c02d00403c03150901007160300c8070b8550252113003a = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 770700953 1250 770699703 770699753
    0x15050108130203030d09170412080f090d03020c010f031e020d06030f0b10121e0c05060a030501030c0f1a07050c04050405010b030705010807020c01140705030c0607090909 75
    0x9240e00030000311601941510000517030300d04506140e40030043d02c038002c6129410514040541500300c0c402c1c0d1003000d00c981c0341c52983c600807030051001084406100e1210624144018021071950f100c1c021054000d40c001e03154450f003e580140100520b101d00c0e140030405910340d011341c3c1184c00ca890101c854081d43c04111411516a00d0f482385024580080788041e850f41149082d10304d40c402120b107074030601d505000004403054281c594a400c16030000e141c00348a00100300141d80d00c0e1255000b81c903258442030300014103484a900501c4800ca0554005c60a9030550510546070281a80b1509a104001c1010000144178120f076150300d00711183d805980c0e031140e040081c0b418054036071165000345424148010454158001c03800008180c05a421561345c1c1d50041d1400c4500300e41900140e003003500c050665600c62198030390480d402200850910900d81c41d06417a680000e600103072141d10980038840300750f42246841c070041181c00418440c90040ea0388403400e9071030781640c61030481c042d = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 770702203 1250 770700953 770700961
    0xd05062b1a0123060435060606040e040f060f0b03060603062208090901091a0a0608010b0a022401260a080307120f0c0306090b030c0d0510020a0305010e0a15050108 72
    0x881c005c40d0001c003401041c4982560380700703e001070074001c4c641d00740c1001002802c00c0c502c071030000306199120354030046c01c2d0390030b0918040c1c40031422a0014400c50750003800100c2080001c5491003100d4a10102d20f01c00034200d103280302814900200034018510030703408201007182c030402180e45020554010440e100c0c0b051a00d00c0d2429040c054070400d160301c8002e0400100d80e40209920066030301c000d07114003241d0074a5200600000c0c0c2410300880c0c000405020060080c00301c4c020040080509500c1103030491010000b40c030402c504601d603c60105626440100100b030050780f418060201c5601200c00214007421650360b0780c541c40c4400901c411004000540c0b414080c8510002d940718000d01441003c0d07000c02070308014888185800d01081c64414003043c1400944a082c106079000350041801c8404201084019401498200e42c1881549442c0400d500c0900207403a03000c2454a0100c3c0d0365050211010800074020180d1071400c2c41c1030083c0b40840b0403040741104072582800d0418031615 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 770703453 1250 770702203 770702209
    0x60d0f020d05070617010b1914130e010e010b04060e040c0905090403020106031e0327170102040801061a090f060c12030115020c060d05062b1a0123 65
    0x1e528440500940039a2900240749a00322500b2101c40c02215002d8002d0780e02d65410210300d015903000310300c1d100007500800c03400030b0080c1508070031075518403240c42c00d004d1100f440d4482030910790042c01c40710860760010070001a000031454058140420898101801c00034000c0040c0c0c96035030901d1150351113050502e030351401015980081c000103050700070071746001d04020713000e0140c0b031000316004d10040014842c50040f00140c0c075013180d03255448170024454090110154cc554070540c04424120400c001455000b10b45420401052035002585482ca805101802c44085034058117800c00803051441d0711911030000c03075180004c00c503220b00c410030909011620901401829100d24031480e64030302c10f000e1142c2c010f07604a40e5854600d160080c440101261a440c0110450350000d109022124603078106400640e8844400340003000c3d0301070104c099084c00980300c0b842c1c4002d8401818110103000310500b0b080030a0a82c900c1d101c0079945010b4500c1c0000d0802e0204440581c4403400800c0c0b0b0392307 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 770704703 1250 770703453 770703469
    0x20301051e0f040203090105040506090708030904200a1205070207030f06020703020f031605011b024222170915220602010905071503020d140618060d0f02 68
    0xc0c2c01034030444d2039240c003240450090405841c1030303507075206400000b06120700009a000950b0022009507050114900a203c0074040706c0c1404c140c01110311a425800d41d0f07200002c2c181c0303043c2643c2c035404003156440502d400ca400107401d200c119000b0301c800b400800c02c24190701242a0b40b1079001039031054942401c1b803d18a003002d202200c0c0c080001d07071300a41c5140c00c40c0d0207003403405500208031007000c00d01c4170100380c4109032a60015030007060400d18025841504940e022640d0340b04500c030790400400156400c12090381d9550081c1c0780700c0034400040013143e103441c007040000c2090886142c07640c036103000455604c00c11004030000064030b0061500c800f020b03070b4044000ba40300d041d1142200221a2400c0c844803105480303e000084000840c50320500442d800c081d040742c0900310700c40c1401c05014500a0309852801895002c1100300700c045058852581e1100c00080d0566a50919104000d50306020700c0d0410510f200c03d00c10b00509545980401010b0760b80285544c6113408148082103000c = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 770705953 1250 770704703 770704729
    0x40308070615230f09060f1203041e090c0905090a0908120f130804030b0c07051506040c020d02370c030b0a0203071d031002041413020301051e 63
    0x210722410000a44491150b16920301c072001115541034002d000720601c4158110030000583c005590008a06c180c2808030044007000005040104d2120a8000c21459540168003c0900c2c500203500b401888510b9144003001d0300d510b05091041e880084401490040315000d4241718401100104402c00030542c042808030b41d20118854170340f54604240c0d00c02120880d00d88070b030300c0c410100103008002e0310460303031041c658000e4002d810a415601d501c0c0c0030000c001c00d5045221420007021002c00c4080102c0680e2810481c050381c1d0b10301d0003205100c180c40105880c0d8041d07500c40300521900940100342c12070015410110ac101425003000d1000d039110f6050440c0100c24500c000d00b8041c840f1042000098a0040b0140c811a4454130108801c0782b004882150001c0d0a030f0700141c000006c41d000103640581c00404035420030203c0850b0748100da00550100300c19406641c0d078091241032014085100c5c0e40d410b0707421400c66160a011840c2051200070700b07012141c11070340c600090b55035031002c0d10039 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 770707203 1250 770705953 770705981
    0x9030d060801150b03130f05012003060102010b100c0602130902070b07091d06010c110a0801060521060f0405161d0a0b010f0e0a080114010302010f02120403080706 72
    0x240d107030340d065080d00900d1000d400c0300054034015008510078100c01d040705c2c0190680c06075204800e8568590581e40120b020044909549035078098120440f0580203084640e481c4c441c003552400c00360000380c02c41e4100403005001c1e269401d41420210b400c000074044007504558007580d5500c40d45070703c3c6605000d5410800e4445e1000c00c1c03800a2100100300c5508c10003040e20703003004d42901d1380510301117842d60442c1c03018550200c0000422a5120321030844002d8481d00301400b060507400300040c802e91076030f0440941c0381e6503035504000030310b8904410307440c428148820740e030040c131aa0a0140c880b14000c0c0900e80380b0b1020b4010504100d8200207440c50007030222000120300392905042a0341c800708085e0500b05592403408590100101d2040341140c103416101d8442d00345074010103940303582c1d003003c01591020f03000d04001400301003070058103c0a900941c014080d51704500c0090804508601414115403200c6490500c040c3c04804807020b481c0c00c0612140c07a403086141440141101c80003e0304 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 770708453 1250 770707203 770707211
    0x803040807030b0106140414010e1216060806090f0405120307021005061c021504030804140102010e030c1203101e0f17100b24090f090112060509030d 66
    0x140206000ca40503042e02e1149040b1a100e036079599003164008000d142090f65014208000c002c01e04205d0040a0124010f060020280d035008000030061184d40c084d00507580c10289140003164214030085000d404141081d40c4181005400b0a01c6240000d040c60000081c103408207060080401819258201c44c0201950360301c2d001c68002d44410301d100c0100700c0c0300e0070310001c51590700d06044442254044002c00201c041034030b400700700c0d000345008200719414000f084040b02003404a001403000d846011240d80f0401c150030002070840e51400404003031a0024040360514010105081c0e0b20740c52120382582d240d44480b511000c007606554450120645034032400c0c40e03445c8405401a040700c0490520140c0b5940d80d048990320f2010840482e00311fa00b10605e078608800c1d0b95440f00daa40c1c00c02034010258804040c0e0381c00d240142d440c150001c200c0c0e010441a0355850b1440e80e480c5041c2d001d0f11404d441c2c1d4505180c402c058020340710010480754aa02c00181021010020b130391203c0e0306a44140 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 770709703 1250 770708453 770708459
    0x5040509120a17101d0720010e070b040b0f070501140108160f08030f1c0606180f0e0118150f081005011410110604140f0604020108061207080304 64
    0xd010340d0f00032034103084004900b000049410f00b40f021020201c1d400041000159101042421442480100280103001121040301d0902003da0220003800120800000d045258208200d00d0800130703070301036111898100018004400700b14107580c0900841d29030143c581400f85000b034050000508080c199002c0140001200d040000d2400104200500031541107034540b00000420143c60280e0a082d41c0100306103c003a1a1060046c803181c0407002c5a00030702c20075910b03180f05981d01a070148000480906099a0186803189444010000203000915443c500481541083c0051141d4118909804201604103031036400420443e21200600d98545440e10205040342100c1d01a1100300c0c840d00c4160020b0041d603204441c141c6554000c1c1302520366030401004018082c03203031145c082000207450a00c65107410440f0314004c91042c1840322100804220252624440e007451010039802030040c080540d811200b000e410a00c182c078106c448060301d5400e00d180c40c01030361001c056480005400 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 770710953 1250 770709703 770709707
    0xf0203010e060306061c0309120b0105010216060f031d1e190c050f0d170d0e01051509130b010b1801020f070504021305211006060905040509120a 64
    0x2581030301c0c465210100349441e55803e05503201030444001d600310500307a020403060030010000702c41d018442e160260040e5240d60042d03542124840701207900d008280010300096030180b110400d43c0c40c89101c0c0107111494980c0c0280520152003a4206155450112007902d09940c451070140030420000c4400303030b9104a504811044401c46c0d840303014080c070f5403d0140804020340b0801c01603007142601c0c1c54941094208100300c41c1d10100c0e0f5521481112540001400071109045a1480721081d80d45801340c2141180550304110400000382e4503010070810212050100c280340240c3c1a507905403195102d85082000c00e0a142002c0c1040c0b104000000b0203e036007000a16030300b401d50003001d00b041b003654016642d40420500100e0641c00c01602807106013460307406001c0c440d441c0c0842c92500341e56074010810044e00b50903104201802d420009410040c20801c8c09c101c081c85040c20003281d0314107200102400c03101d000d03035880f9907210b1000c5000c0e103800f0810711001c0280350f039119032350740141140 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 770712203 1250 770710953 770710957
    0xc1c110d080402041d060a02090d0506090105010315020301060f0e2403012102010903060906020706140f072c04020910170a0b100e0a0b1b0106090506060714100f02 72
    0xc074030130ba08010400722400b0600e2190800003403644010300c03042d25160300e40c1c0060b41001801d1a0408200000b51001c1581045828024850b00c000014107504500700489042000040f0f50005401040100a1203900c04400f810b0700a451510301a00c0e401d40c00002d0120350610146045521a4402003072513401810041d03040380c041a2286114015004410341002d520002c00790104501b64010000700c1c000390492014184925001441d0802944d211b10455240c0100030743d2491900041290b00001c441c4401d030071142508200103a206404c0305801805000039128650b03074455841c0e201070351615010390f07001b50b0000380383c2d08010040035001040704a03134440840f6402440303000704241e00303002e12500403401c1d00a011000e51441041d02612904502240c458001d01d055400050350b40120001e401018000c00c600072006200300341d00c0303007520242e40210322a00d240006000281e5980000c640d1801d82c804506041c0c00341003110f41c4e0501c3e0191030a8000d407400d00c1c86a0313a40850760380c0 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 770713453 1250 770712203 770712211
    0x1308030a020c010b0307050607080d0f0507050901020609061b07081e071a010b040303052208062707260a12080702032d0c1207030201110c1c110d08 65
    0xc11122031300108040d524481481207903048030003003040c0740210750348900410280070400c50100d004120540b40ca412680220b0b40c2c1c0d40029130101d100c42481da41400b413150450000360042105d0708140c00c801e190603810f0000c200c8485000280201000300c0c00e82070b1402410300c01655800f40e0400d4081074803580c0445030440e030100303103038420000c070b10003041105050f168103807c494105401e43e83d060307401e0f9014480841034440140c40c25035084120100c0702001d4101e2002401c0b0303504086800710a079a21100b0012001c0350550031100f9015000910001240c1c2c48000390b00740c00c0c2c00c1e44800c0707510b0b001e0040301610300d00a820301e80f014006101d01e04c000700d90700ca40ea07510f0296110300c01262240601c10740e0b00d80f181c00e05c01d5401408603640c0080e035604140d15072620b140800138482d00d480c0000d09152040740940c00300301c0405240c1c0a100700b980e00c0600f00c00b620310f000414141c294403070b4030141d42d0b185003040100c42d005250f84143d5804103038408241c203c3e0510000e0303a5016084071000c407 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 770714703 1250 770713453 770713477
    0x7090c0c1e021c0305030703020714010f290105120c120f07020d08010e07030c02100612020f030c01080f0901060f060c060e0304080703030305040510090c03150b01171308030a02 78
    0xc444080440e40c0c400300d814500d0b1305590313558115140e1040c2100698800c41c030a4a01f03c20505490141000c20321440070803a030200b00020320b0040344c40204880004801c04465640388281e454403503660840101c40d10306020703a8484445c1e42d40c4541c5075a5a005800481e441d070780311a410000100f1400700d600d8000c5105030219200010080021a900002405440c1c16000ca007004110014003c2e08280342c444c40c64015101d03a2840704082c441228903a9109440400002c04440c0550504c0c40101003000002c0d030141220b000c55170300203005104060300c0010000c62050014610000a5100c0009080c0380094490160340c0d9100c02041000503402c240c420600d00b03032060f402003000004860480c0c08100c013030500d0514644058001f004010001d8902d802405e60740c1404400307030b1040450f828400c60543c66854111704083d50b00d80d25140d51001d403207190020748184e9030380022109458250b4105505802c0d034940100b0005d080380800010320003c40031062210030851500504580c031104 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 770715953 1250 770714703 770714719
    0x120f0905030a1d09250201110f0a0e0303041a07080702041e0b010207030b180309040c030219050a05070609020d050609010f11073f020106060e1207090c0c1e02 70
    0x4402c0040c1c5590170b48a03400fa13203003403000c2c03da80c952079402d0091894200303000004103080c100a003041c4641c406407401d03290380ca0020f043e02a1075001941c50030955400e0f001036050a0400700500003110782e541e0100448000816a4410006070000703c032038941d405441400441c031001011021710000e52070905e031745414012030712440d505c00a04442229008500d07580152150b07a00d08100364603840d003106003808204003580f41e83d201d50041003d00084c0d036030016a0340030600c00301c0101d000e400b8180d600b040010050807007201c0d1300100765001c03141c02017000100d40900d031001030b1005078142d000412502808080106545043d403103005140403520b8284403941d42000c2d0bd1290744a00780c0018803803101062400e4400b01c008204c0c200d0144c00d15000035019084441100d922070b42944a100141e440d02c00c107001e44c590020258400201c2901d030484003440031100d85881740ea250080c12501540c87d040c3c2d40f030062103036510303102050304544800030001102440b40031005481605a020310f1754 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 770717203 1250 770715953 770716007
    0xf01090303320603070306060b0406020d1b020f0a18060806090706050f1b030c06190204080309040c0e13060e07022a0a0f0e0a06050a06120f0905030a 66
    0x205100c0d0b40755021145502c51111808052100710000c0c05000e0302d40601c2048008000510144903050141c0700d0700d0241500e452a0080c02454101c0007a44142040555904082d00007404519110220390440c0e580d4017240414001c1000401168004540069010500d042c003480039881442034580c08000d451042c0d1b21102169a1080544206000240104a0b01d880c0c000020044e105125800d04241280750380b5075085491500300022411654015106203c01c3d884100c6503941e42031203080c419400c05282c4180c103038603802080005800f4035212502c96100520a909e2000fa03510000c180e10f426218071800a00140f806003e403c082030040c80c08959140c0c000105038042103100c1d05900d60740d07031805107074078a10320022030010b03046a00803401007031001e151207010014205808242a00d4502003840805681180e400b1034002c0b029a80144402039005604c0340d0164031045000c14a2000386e40c180d0000e00504401421600000c42e00c030b00b11741d034024801507802a54005c8900c040c08 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 770718453 1250 770717203 770717231
    0xd020705010212090a0510020615011d040c090f0603141536040f1209080d031a040903050403150510090507021608060105100c1101140c0f01090303 65
    0x401030194501503480100107403111654180100710081010744040680c84e0303500041022aa020700d614000340e006881040308040303500102144541d070928104034451300c802403405842182103c4140103a440358100b00545004540d40c1c8020a144121f15000c0c540e0b512001b401001d03000d018800151020011400490020070805c8c818040149080c20007005080c1b408041541c40c188507088036010050f2600c1c004c00503071018410b0307000b8010301030342d10601e282442101e00074200f402c040c0200120180100e1700c000503c0140c158842c00c0000d10035290070708a0b0307030f4076116031040c50f40107090652404c10541e00402800849105aa98224586a491800f400d8440865005036101e0b0581000c1010300b181d904070325002001da0040d660090054110401d2910168020711000d5001c0f2004101c41d00f03200d00d868500000c50310b801051191903558811b81041101821810040e850000384880c04001048a4194a80350100da02d8800e010301103502a0110342d1050300482c1c50940b003980011 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 770719703 1250 770718453 770718463
    0xe010f05090a050d02130606080a0b0402070506061306030b010f03050c121203060109171e012c070e01180f0b030a0b0c1b0309090a06050901030b06042702030d02 71
    0x100006240380805400e00707084c40380c44070540300142c0e07020010060300300c40c514140c4203071b034023600d002c4c2c1d500d205034940030119130b056940860b5500d00441c4100a40030214001156141d0003000c2228044820390007103070100042c04468001503c501d241100020b07000d500036820900702d07441001610300c881c0402e0304000d9641c24404904046810400e00350b05d15124440003075500c00014145000381584400d5240e1b0700c5601110240031a81c0040c5800c8100d00d580da42c0d041501c1c1441000f0b00015005440420411252820300f5650280c050082c1e08120000d010070000360100c00031000136036075034000007860320702c006004080c1145003104410703082d4090300810b0b00c582c401900030401340d02c2d60790316607084d6100100341e01071440c414045030351051240320340d0141030400b460041d900d03504c40b0020441d080c2c00107021906079070715015003000180c54811500381140d8100c40010440c4d511a008a80545411625000d0000383d8112080c0740880d40103030701c10035030300035030817216071052000040c0e0341c1d4 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 770720953 1250 770719703 770719717
    0x31c0f0e01110316121802040b031b06030903073002030f03070813060e0a29010e0c070b04030801180509030409021308010e0d12060b0f07020319030e010f05 69
    0x11601080010403c4d10300361070346001c0d10079a02d080c0c00d20949a00315001243c851a441c401508100c1e9007030415031509005903850701c203007280034000c2d0303190030102c20442d862901c441a02408010001500c0c0860601c00d03911640d0b0804409001c0d1a6581c95940b420314414803904018280000490b2009200006580c50070032008842440e41c0c03200041034a14000040a4140d4801410000c20000d210303802501c0d81c401d40030700100b04441c420b18110310440f03200d000e64030504162107072101c03191850450b00c0d4110b4202031000440d54641030121140c0d8031640340702a15400125050108150340564400e04030780105407045d15030b40601600c44151801954244603980c802d10080c03204074a00d038010050b40e0300004002ca4103e41da05080c50039107a2001c2213031002d80140e00324804580e080710034a840c1300020b0f0800c00485041c480c0d10702e030364000c154084440110201d000700c1152002c206955500d605881e645212034a589001005101088800c1c0d0000d031700c0e906803202c458000c6042c0c40d09 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 770722203 1250 770720953 770720981
    0x91d070f0506090d06150902040807051203070f0503070b0108071410020a02090606131e06020a05152e06030b010c1703041b09150f031e0203031c0f0e01 67
    0x43c0201e000c0c100588540b480b1803c0c1c50f032640d26100c060049410418030f030014681c0b210096142d9103840f0200381001e0103684080d01075180c410b090250a10040112040e640d03002100d6101002076050452541c014050002c10403014400041594100040c0180882c2d903200307901440c0c80c08620900081401469120016902c2800000c006191101069178002c00c0544110300308000d054091364281e030b240d030040c94039481030800740400a2082d005032015280074001000901142d581c0c0f103075110200c0b00749810f0311a00341e000c1052016607800316070482c0400082201c010380b4003030100708038010341d01c00c1d50046490100d00700055401582e0800300e0941102000c2040a400c02c040d50390741c0d00081c0b00300d0340180100c0d081c603541c4402d01d01c030402500400d0000600d51600ca640f10442c4d10740ca40140c02030f00510641000021041d030f55400c6040c00e00300501d10411a2480800e145002c3c24076034420b5482ca404200e01130803100c0d8000c0e45001c000c10410700803452645181801c9542607504999 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 770723453 1250 770722203 770722207
    0x5060c0c151c0204270e0307080c0c0307030312051012111305100506070519051c23070201090812270108010501140403331505010f020106091d070f0506 67
    0xb05e180303000940c08101d040002c40422500c40310350805c5c0c1160312002c1c007101c29640100721040782e85402c00c0500c22901c0140c00070108070341141ca000d00234000b028100c95450340c1703540010b8040450403c5c1c140042c09010000a0404120b18100102001a811080c0111021a407410843c6000d028a5000d0301c211004040c019040500b48100c40d482414195114802c50800080d520300d2601151055806100588804417100358041414502d00c1109000c02524010b000207915002070013881d04140007415980c3c0d8682c51005940c44135491340107240764010300d480d2a040d42c10f0000100500645030b02c403902d10346403044001c514001c44403e118001001c0c3c00062010f94016402c5128003c4803041c8141440d9607030395850041c0040c184a0b12150b580f4601200105806264541c81151032420900c400d80b05e50f071648043c10b056100300c504020003821b41e0f407541c40c000e40c030940207090701000911400c3e0802030b810701701e110002c201114038030400c140090106104800390060340c20080c1628 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 770724703 1250 770723453 770723489
    0x4051005011209020a080a0312021305010318021302030a0c050f0301030828120c0f1d0103060b0f190f02060c03040212061305190201020705060c0c151c0204 69
    0x1500305803200d240c0305049070740d00351590150b174882c04407000030310050340100320494052400030a0420204c2241d0802401440040a05080c12502006840b028a400288801c0740d203070741100d9409040010790001c0c1c0001700b58640c0d80a40d0002c501c06c10601c0c50034031043d540301004175030b184126180300d0042c070230034030042c8005003640ac01403418061808000c1e4000c0341d041664030b800d807040d44460010419801e69124180355501030801c07081c1c0c45007440e008440c00030101615040100b20304100002c0c0b400c0c03584405038042e80c0a50080c1488000641c0c076075410300c4282504d94001c40e50060b0721100c681021030942e20505200030311a00d113034054021074407000e03245801a0000383c001c992212100903400460b002c20090907115044803189542600b505007060350030f10743c0c8485800400b40440e103c003000340c0d8002a150088400a54003d6030b50fa00c00107041e0304100344540c0f06540101d41400420043d10504050012025440e0309502207030b80f0289032504910580c811014500c18101c149 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 770725953 1250 770724703 770724707
    0x5031206030304080d090305070e1302221a21030f0d11071b090e03040605090a0e0708010602010f0506100507061b110c030f060c0304110306240405100501 68
    0x40d40006001d0222414075840e40816402e10f840403000000050441b1000c0003800003c02030b01c00242010407015060f41440c8184844800188402134021080b200358800100010a213050929410000c200010286140a122203118000c409032044001341c1c40c072068001c1600401002503180c400a51400e94800000d408642220a03140341c407070f944a01404811071034200401c0740d1441050800017511010181c00010310355500304071a194601121262005400002c923015504603043c00f988410b401800120020040e40105070140f00282c14480c070650094065410f85080703070005c2c008400a088118101e4038101c8405e80d02c01c1c044008080601c0c001c03130040842a002e201c6c045031007441007010840050040c140400001d40d03074211700204030014008400d81600807805040e40f032480304121603940300003511941c4001d000001040800c019510100000c9802500350703041458681e00031101c00d800350340120141000e42e0540070f2546054880c0354800c005100102d060720381041c1c01 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 770727203 1250 770725953 770725987
    0x60d0f1406091b04050301020316031a06030127020703030b0310050601020a1502130806180601080606010503091e0c0405011221020c0409080901030b030a0f061a090f0f130503 77
    0xb02d010f4400100004101a1020b000071445191070300c4610248100e070360002411a600c03170300540362040400c1a1108a95504412281107a1042c101070524450101d039045140200c0b000501000c0d2000904404154064001101c202d8040f41507859000754400640d0584504a40c102c0c010b03009006507000003108801103000100c01c0e040c0050804408603e841d40c504941d40040390181e001d8010481004c040d121011001c0302c501c40603000e9949445000f070b5603082c0c09441d46062100110001d00f04803010080c215602120115821038a03c0b110403094841c01880c8402d030066080c54000f1914034000c6118025a40d48068a080b0541000d412450006a11180740d400c50141a51001146c0d81d94000c2c641c0c01405400d4513a81c0c0c44243c00050103c41d00c41000c0c44c080d400c01c800d2100030034003003030344480101c2d048000400d42588064058280f1008440b5103035010000806115501d640c45000e184504c48480086040d45c40380328601340e06002e02ca10040a96208000c0c406c00040c000d03071 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 770728453 1250 770727203 770727241
    0x510120816020907031a101b1106040308090f06030708060906210304180e030d0e030f0319050a061208220303080f15012c060d0f140609 60
    0x600c0700c18003425900003410400161480c000207601c0c0c1342001c0d04020804698451b130107080354034500c400b03000e0102400e40e681098410b041c2e404400251400d0280034020810300d503030700524903030f41c82c0d490740307001e5046800000041c1d02032681b101c00e035451810460101e90060350b040c5c8890100b50345681c10440d07c44030080042d44c20001c000b04205d000c4111b00308204c240081e12010755119414004101c400200300c038000c01401741017407001d0222880101c225404141000000b00c0c4001d8490591481d500c1052050804400300008210390070300410720003104142c90650621180e114071001c5408d4860034003424810881c081640c20000d090359004040240c00c0c000701c9810f14004110a01c00e1140c0b941c000e5000c20034000c01c0000c4c0040390f091141c5d11010054541d040300c4a9200000c0c881001d1070000884191240c41c0519040c81c0000a50501d0308001c091a999040d50094003001d42a100d0b0000601703410204e02984000302d124000d44621005000f0740c031503554404400c0905c10400d1 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 770729703 1250 770728453 770728477
    0x90b040f03230303010f0303080901050114010c0303020403150207020f010201271506141014120718080c010f0c1109071205040c0f122a091b020105101208 68
    0x1440b91061640140090750003000c4040d01600c0a600d1400d01600c1c1c0d440007054075400f40d2508005011000c1d042a55000e031000a2800e480200301030f140035402482141c10180c0419007101058901e2003c0307030010840c083c03094036008840481880164282c49004010306800030268801b14010840c060140008030b0017000f6031102c0b08002458403040707914542201c0700118100d407a800d41c43c18190f90030101d00c90103140038480100300c5405806503001d260780401143c4000e0300890000c2e07105a216a50f5160340500c40e164050f40c5d034454650710013440c00280e002c501c41c80110012980501c400800310b030782000007804100080b504100365520014050b40500615010743c3d0445031b02403040500c614812201e40e003546040c210305c02b07203011665000b480801020310300200090014003030000803601c1c11801e0402c940d5055802035901c84240c0020780e10b03526001c4000060300903003554004491082c0c008001988581e181001408280e01440c0c0c0600e600d2440305001941841c01070101c04645 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 770730953 1250 770729703 770729753
    0x10c120c0311161106030c03061908010c0f031a09010519180b090105041a043c0b010305010302011b032606090c180f0d0c0305030a090b040f03 63
    0x204009005800219168906443c141c0c001070030000202e0b1500395850f000c94620b030443c500349110764131a01c03005104034000d614841030352003040c1911741e0300000381c80c84c0b1000b48200041864010100c4030400107d000003800c03c0001812a03200c80340c50700301000d0107082400260f0900b01440043c1441c11341c4181d600c0000400014810404200c45451007101c801c08a1800e00c08c8081010144060f00410710443c54060000a81c2000241200160205803408911140c1e990728043ca41e6160124018844990f0091940c0d0303800c0344000d00c02c1e00712100070200b007424000801182215401d00000b0f001c0341c1d01c0110010001100c07142109020b22914018007801441c220f02d00d07640c2c880f41841c03c030149140080c03000510780342500030b80c03100060380c0d0b1504028840d60301d45500080400041e020b084001a1070b103032525040264580a50480140415282d0303034680b4607602c3d881040361100250740caa074085200340541046a048901c0c003140d4010042c11915900b41c1040e100c9180310f500482 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 770732203 1250 770730953 770730971
    0x206240f030f061303030b01020d080105010815060d090c0e06010806060304052505041404170a090314061b0a210f1406130605060d2723010c120c03 65
    0x2c016184c0714020513241ca03541c904041c500601a5525840c00781c0c1903400450403040c0082d48800a01c1c111582441c00030301c81d40f00c1610706280c41100b022200d40007440000c07416944056908081007ca2003072002500481d618146412032100a8038030302d00055440d400304010307180c410061034005004105032000c0c0810500200104000c3c000e0580510141d1074041280e803800d4480c0f42c420512060f0b4002c0d40c0d1034695680e40b036407106010341498540c004511007101c640700700c050a0246601c40100344804c645c16002980d11402125003080c2c0e42d85400f20402080744500a590a011b29502c50840c0c82c40b040d100c000c041d0b511040301641c01a910130004c0c05132a41400740d1007042c43c40c003e019106003010410702c20140d0b40fa01420000d2400d000e82040603454010481b40051144800060513030500d08000c04c01810200d44103881100c0d5000d40814040980120301c041c400c0d00050105c003623a1a000306080c1c40d062019080407074142c0550070b81e0110907030400035282207145400942c81c40 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 770733453 1250 770732203 770732233
    0xa0201031d06090d09090b130c020c041d06070f0507060b0d0803040c090e030c120d09020d0c260a140c180906390f190206240f03 57
    0x641250950b44039400728000fa02e84d141c0004080703001e44007441040c03200c01849008500ba04690480d540c01c003556425020b5907491091049040030720b0b0040003070100c80e041c86248845604040c81c0c101d4180540350125845900803890000054500e49990b03040144980f40c9600174a000c808103500440b400d85100c1c00500110000d41c0720b80c0c4129013010005042c11141d908481000e00c14102e164401c0041251000c00000c4001000c008074982656484100034204082c210075200290011205140b420420941e4071018055803e071084408062454203e07840da1010b044a18030420f4110881d00e0000c18035981c04078001144020481e4240003c03000428026410b07044460071285555051010044044c041e55030054002600c10b00808904d80b0720155a440d4840050f11040c080801e40e96a59025001e940281418098464860790141c94201e02010461060382c0103000e0440002c440c0700200302080c0e02d00c915020480c47d03d00c0c0e1202404090440a00c0f503550510520f148946800 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 770734703 1250 770733453 770733463
    0xa0602031015110f0f150a0e0f2a011b060e06090c0901080d0f11100c0302180109031707020d02030f0106030302070b0f03070807030e06150a09020c0a0201031d 70
    0x5040e9a1041e00b90741441e843c0904119800b10381001a810a01d050031407135400050301c2c04a180e55054400301c40c1ca40c1c3d06c0c03601c001d19014a01800c94040e101c20600a0000400d0380c25100010310b804002084418140b81d18207c0c200064a0101d001070941d01441500d03046000d500c1392003520f00080c028819030f841454404222004c524541c41580d000c0c20038240301d0724641c0109642d4004042e18081340e54050802c01c44c9030820010495614002000c0b0365040103400d22a03880b0080403c254042840000c0103035102603903140d803030181040426100d5200b51003500850b42c0002400d0905883c1580c01d081a82c805903007680d110365502e1031480940c0d81030000507481040500001041803862030701038200103040c0d2000140030301c00d000310700301840010304a030380c061010728042c0c24580d10b0f0030051300100249100a9080d1081c4410011250b80103c400b600408045400103c881c0d920540601a84070300080040160081c80c03c1c14015400307038011460f6500c0c1242440e40c04a170b172020061400c = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 770735953 1250 770734703 770734739
    0xa02030a060509010b0603190e15240303074205090606180a15080102130f080a0f061107021905210a152007060c02010209030a06020310 60
    0x40d60303540c041c41007806091065985c18041a626241545804480c40e190350290441410210340c48150070740c00c042c03050043c0881d5149450b140c9495041c0550700c400f0307401c10002c0c410400d050250103096949000000c0d00c510301d134400103007404c030190f107501c900d5900f02080c4501e45481c01c94400149003400c030030385040c0039201040002900c0c50407220031407501c800901414042c0d02c4090b003000c2880c1401900907403001103854046540748502880c0c0c0210111644411925440400d11101d9503030940d211804440300c0c0407040a402307883e25440d5031101e81c5100001c0c04400385103003100c00564640c02212202c208921500d003880560307000306045c0742c00c007000f0889400c0002c40500c0030b0320744800d240c0281d000120400c0e080711844080b840c0d0328410110f0241210b098090141c541e040c0742d81010003404040340c004546403c200e45402510b410404049442e14104407819030170030301c14420b4443d501e20044c020310f4440700e01d84520b4002d41c4054910342c050340307a802c0046000100700481c4012 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 770737203 1250 770735953 770735963
    0x6051e0a09090b040b040c0b3009030703120b031e07090515040b1201020c0106051203030c0a0f090b04030c090b030c01080c180307120203121611030a02030a 69
    0x141410004000d2035011680000701220300d8040c01c4000704614060041d40554404c10a03d49034440d4107040c02050314546c0f0203040041e000420040c030b1003580c0f1406500482d060080c3c102c8410b001040a1540411200f030706c6e00713600522134100405d10941c01009014070f01d4100189068500340072a0401c05d0b0a0720030410751822081e02d015540f8100240300040203441010009400c08180303844218854482d610301c200e881d006680055520312103e0340d1181c12000007103543d40c0c0300942c0d140c041c1c1070f1381c800c40d403062039049900030012502004a81c030407070601c2079035071402080050507a4900c0440305682d08120342d00d20013181511500c0f00a101650081103a035880c2898107000c0d400745d40c124044203000ea0015007c1e201a03981110140d6048440c00007029128088604519580205941e44560500c1545800610404c3e03003040300410b80c2c000d0b400c0e10514101070f207a000c8140304581250420000000d42d10000c85c02205012103800c10040681c1c002d101c035a0002881d08050030400d8907 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 770738453 1250 770737203 770737249
    0x60d020c10090210030b0102100501030b0610020c0d0f05100510140402120a0b0f0d081e070308010e071202030708060f030c0d0206250302010507030b0f0f01030f0605 73
    0x24000800241410141c010814050590030307502190a103116040c58005050f00c40c19031162580c003d1103425a94444004100119a543e09100d590100166441c41c02081400399020800b4030100d024044d8800180510841c4c00e1941e48221454000301800e641324001ca4140c44a000c421f4040c160140f04a4942c7c0c00d5194248220f08512403014039181380716502c104140183c1c2d00000b140300d0383c0490110303000500100c00c240461a41036281b02410b901c001101e403040104414075010b060a403055400074414107282d04080f803c540310310140600031a82c9a80100b08102a0340922030b4070066a140c024205054681c548060b0b800c2680d04c80d001c02d400343e00300009828440480419000200c000f0510064800c0204841c04011500079001d0b580000319500c501c544003c105603a05a4501c40840907074050400900902003035580030001fa00780810000c030381c0780182e170f4500b0551004005483d0008000d0043d801040c2c0e26950500329503e9a01c00a8203665244d5506010031000303c3e541 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 770739703 1250 770738453 770738467
    0x1222200907050702090411040b031608101503062a110f06071d030f0d02030a09081f02070510061e09050c0403021903020d060f2f130302060d02 63
    0x6031004004088004000c42441aa0096178556941c140c0290b001509242c80c4940f160104024286031507520f07415101d5020f40203210003c2c20a000b040711030043c1602c2d07041c1e03d80c4116500b0b0325a900d00039046012514801c3c40455603507400644040d4100380480b045900e48400c9514030100a15104003180c000c03116001940c505008030308880c00c140b0040c00c2c06161140010300301a00b1090075501d03a00c403007071042c40151030410074000740f003858504030f6005140300704000b9501d80c05000050006000504000f6180b0000501d541c4038107600741d54000121140002007009412806054440344200502040307540920b210325009003180c0e140c2204203501c40d05210003004041d50007a010a845c042c108096000c01c40e02360307002d40340d04503042e21070b045c445110140c02500c140c01c06540302c1842c415142c01c11510f0751081558618801c014000d0006410700042074510050716440c8816120b000d0607510100107004102152024914648051b16a004102c0c5074115000491503543d00003603d0b = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 770740953 1250 770739703 770739709
    0x70b070501201e1c0c0f1827060807080f011b1d041b0f0206012d032a0b03090a021c05030f0c070f0b0f0318030703090614122220 57
    0x21085841c00760401188081c481f000380e00c02184c3c0c9100d401080251218282ca540198410300501c00c0c0e02c216003844401d0722450340f140c540c40c1e00e00c6030040910921018071017001d41030080a0012009000c424199540800c0c10340c0c041100400058200c552580c00e401540e2b550307c07840e4907140d45a20785a20004024801030b007514041d43c4803806550200c4010000800c00b64030708110100880508001c203401840602540000c0340c10007813800f0040c0100301441000701000241142e098034600003400e0780c44014000520042c0c0390700c410768200001200c00350034440c0750206008290600300c3c04844403511424196013281c205d000481e40c00099110b40c4803802c0003560064800c0410342c6a9032403400481458501c254a010403081a010001403401c0007601e00b2a007400b40c9407015299505103034035000700440f01900072200440d12003050061604160b00c00d031101034031860300c10141511400211014104494842074140e00303013012402c000780c0307071440240107010000441d8030340ca4841c0c1c00b0 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 770742203 1250 770740953 770740967
    0x30b0c25140c0618060708070b0a09050601050402070803060910080a0303021b120703030b0303120403120c0801051c080702030717070b03040f080705010e070b070501201e1c0c 77
    0xd544240c90900006569840e1456400420881207810954807025454007d04d14001c090700542820302c0d50041200c05200d940214940920074002c0c2c0d42c040c0c1e01e60007040201d0007181401f0b8649501400000c03118202003a226800000c0150f00d01c2e0f00c0c40da190011880c0207d80e03c4200c0010703801045030000c0101400c40000080a0701000d03107e034286103504542c032409440000341c201070b00d501e142e41c007988050044544003040752048440c6231500e4200904100070000d81100361f070b8030340200b2411030307441030720501c1c1030311340c024005100c81c0b0040f1100c200280341c3d030300c0a0716160700c20803081c00140c0c0c1c20003064009003904110b401c02144810070700c3c2d0030a41503902850384610304004004c009002d903901c01c10800d41c0b1030700c0caa03251051424824014064002d14100510607040c0100720030783e408015120140c41034000380310340b0740304803883c0071004c88a41214262402c01d01190442c01100f60048a2000d01804003a0800b0008801200d20410052901e0280c43d42d59584400840d0304c411 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 770743453 1250 770742203 770742223
    0x50c06040906051201020405150a171e06010e011b0c081006061713032106082a13020318120a080a09030903060b040204180b030610030b0c2514 63
    0x4004c40c10680723008041640707296400d42000315200c0004000105500079405209403205010540c409032a001c44100304407081210369003110540c1d140002c420358483e81000e03441d40c43c1a51820010b29040301a800314456540c000c4800d8100d40102203203090701080141030700700c0390306000308a0f24070b05040540400b0218000464220840c001c100c0c0311504444400754855252600b900e042d01d0344529207590080446070611050700384400000c0052002031038507a40c80170158a86070780303c00041c0c010176862646409503040100000a00c002175000d40c040d6600c504a001c0000408034680240c034140000b01e440b009210b400401c049442a03446072105500942814042010071030325140600900e81030300c80240110b4840c4501c43d0303e0385540e01030724010410183d40184146000340308801400c0c0d103880310b900a00c1100001f50b150b80311080b00c001140d40094070392200b6103030a100d403581b5030301c1105012a000b4040e03541c0c40c03032090425107800b0b050340549001500c102c15000c2c42414001945 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 770744703 1250 770743453 770743489
    0x4050a1e081812061e2701091110090e07111e010510060e0d020102030d0f06051f12020c0c090a020a0306050604050f0919110c060901020f030f04050c0604090605 71
    0x3005c122030080c805852a400e11034000f8049401d0761000d030080380d0701c5140c204040e14082d6004c048030383c15005412000032580300d240914100c0010f00c0510540e85803942c00480090f0290504000c10000f13224540e030400041d00d042800802d82c0175500c1c1c50840d88203d00d40003225101c0c00002155000c0c85080e0f04070100d00c3e13030090007a03d00712004000c2200c86203090700c102d407500359202c1107a00800403100c3c8580750901c180810201803a0385001815a441901d005400c200240074600c000b03050309824206294a8080c44503584040000094109020020251180368038078500b0f543d07080e407120b2061b10b80c20390150740c2d200c17002c0008003912083d0f80000d008030018001400260744d015010041c01c00196810300907541c89809546000342035419040c40c1529012818401a10240040000b040b04100301e81190711040c140500301e2080804405508000b230000c146900c0e02494502d400030301540481d100c42c034402d8001031103580243d0000d1f880541e200010006420241e0200201d18185 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 770745953 1250 770744703 770744713
    0xd080a02030a110a03350a0b040e0601030b04150f1a010e0d05030f0c03130803041d04020a030b06220e0c01170c0306010516060606090e04050a1e081812 67
    0xc0d60054000310025003441b0003110307000d078075803400c4c40e965641c0034140301c5a8405003424140304a8410042141c00c40319030107079040104c0d4110000e0005a054122544190020040e994940316558085510403021494036107800c50090091294005e01546070607401084005e00c1d80b920014101000100281d401081c40b1860343e00400c1003c416100c0750070400c04079030b81c0c81d24001c01250451090400034403a1212402c030106410030008060070564080c9850350200c0c032011410130022010445000f948034803800400d10026980c2c268280d000304c0080d00d40d19801c04051078043e0030392400b5414107180c65984070300b00c41c054410014100108420300f001106500e40c82030400c1d50950041c0400c400100010104407264400c0f811260320103d401041700c8110303000d1405201616143c403809002486d280004108546854100ca010740e6101c00104400d0202e0360300e14500711064032051404640c44e10054006c14510302c0140300085442d050103034094409000c008214121480702e08443d440 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 770747203 1250 770745953 770745973
    0x30d0506270403050f121602071706040f0602090d030816050c0a1e02090a020a140306060a0c030e0613030b0c120114130c08190b1c020d080a02030a11 66
    0x12480c1d00320340040e01403030400e540c0c0000c824641283e00c03070203885250400001007008a1110081c2c0541004010365007540e00c0b0994031010100040c0b4160046c414a41003400801e000035039010201140900c240340150414103210001040108001810740c003041031718003000808000010b45140d100000d060103030034200c0907040d9980e02d400c008001454a80000c00030000c20340c800e860040000d9009004960524080e0f02c03101c081d400144e114004a250a00c041403182c8803041524495440034000506058001d00121350ba03010002d0194280210303880c0300c1c4c64686403040145080152100424480381c618038000700281c900408018024606212802d00070380b071281d11504469140c040803131064441400100060384015a011120b403401403824030b080c0c2c010703e00034800d02c66001b4043c566620800002e0548252010315580019260b01d122403541a0b031040541c0d42d8000317481d06072548007950f01c002c081d41c4980ca003070307001d640301061030000030b580700c0400c60403903006001a0503507840c = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 770748453 1250 770747203 770747269
    0x71e02031806030414010509030d05060a03020603040f030e060301090207050c0603010506031807120c03030e0a26011503080310061b060902120d0801080c0102011e0c050c030d0506 79
    0x28120107002d12031031000002c1030070300c5a820303045621300103468020030090403c02c104543e00d034804001d8208070360820002900d03514110301001c2c1141d40207000c0e585581e9031959224a16070620314220144002c0360810381c2c607521a070018601070300c0f245200580d43c000c1c80c20440c2c0340001040d4468030800b0200014016a03c2e540252a0001d011046600c1200d807050103050400b00660000c1c0c2020300310022a80600066420860807240a0b4458584c1600c5007014401c6403515070107100710200941d4951040d108607901c2c0321181c1483c010000a000310810324105d0700c19040e900c01e8545050110038080d1100007030041400134051410300d9400044500c0080069034850f86000d44484da0713610840701903440e180002c0581c005010f0940b40d554500a001408030103081c002c040f450b1050740710045d015401403040e40b0400f4848125540340d0700e6040310190140c403039000b035201000001e0109070059541040034001d40000b081d004a0355103004414840d100178140108985e02500c1050121a22 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 770749703 1250 770748453 770748487
    0x41704080c1c2a090506101b1502190305090a0b1003050f07080105070c0507060c1119030c05040c05070204050907030803040302033006010c020111030708040e1f060e040f05071e0203 80
    0x40751820000c040c00c0c0c548c0c0140200403038a9001410018103200407003682c015603030003800e03d0404000312420040610b60102d08840381103c403140540e1187c03e0040c08140a81d004941c411911041941030a49035a80d2605000c07002c0341d9030b041640000801d210f050000c0c01926400003151810040b02c0519131107003640c800c0a0302c62001485692807020050010011042c120b260740648000940408809070089030889071005a40055400902184d02e24060040c0c143d2422142d1381e81d428003050b40c01300700007010050400d440d14460100000005654507000d94446ca00940107951103060302c40e40d8010b1610a61841040c00e01d5a160941c00e00002100c02500b1081c28030f09045540c40c076100603502444a2169000340344004030b8402c0401444000074010340e404001111903030384400540c0c08e43c0030352400103210900344110b003d004a034132071503022103000d6004102044070640c6080c01c0c01100c40541d0a400054902084140311140c200c40070310300d40007240b00440c50800581d2001440c0 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 770750953 1250 770749703 770749729
    0x60804060f111603050f070f0203010509030f0702041119120e0303060d030503090c06160201030605060702032a0a03030309050d08041707080904050f041704080c1c2a090506 76
    0x1071004241c1903c1814462015540d4190031420010b0752040203043c10f400030740c01504e04912941c00c0030001040e40c3c0011055500310b5604c201702504002096003040003402042840d050841401d000d520a610481d2018242071042510355119400160b8040720039a100f150010310305920410900005840b01201c0c12040c0303401d40340258894039202c0105040005210405074040c0b000f04007100d0116010841d1116903100f62000c114169442043c41035078043c00201a505400c1940000c1d07940d10603082510074419050070400480340c2180000c0c41070000e0703810070f800180d40c5000e81000c100c402c00401000507494140600740345010364845103400c3c40001c41c0114040e001c28600f0400c00c190046e08d00350758000740103010a2074641d881020101d01141e080d507121201500c2507900d12800d00c111010f940c1c0c034501030054000c40c0c0d003e0001e4407507c032030742d203000c400e88002c24800f081881e40169a00e044a0921078020341a5046010340c2811a80218408074545001c0c403400c1d0351031051200103 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 770752203 1250 770750953 770750977
    0x70b0a08061e0a080d09080f28290604050411100908030304050c010e100203160305040305031c0b0315040b07270f0e04020334060804060f11 62
    0x4080031102c4412982c1000c60150b90088071410001c1020580810b0518080705642e4074200115594007480340e544030f2403805010342d90800c2c003181d2404511000c80620180320a90900150380c0182c2d02c070440f4841c0309008090700032340710f04848038281020140c1c03504984125800d124a0500d600ca444010203118480781c801c0c000c03c007814075858000c8515a004103600c2d8152030b04c070700d050704016483c4c5140b1646640010070080b01e09165291a1000600c4030314194000c500f4035401c80b41040302203046000c2982072004c113110001c00224200b0040110003958080c66401c1150030310712605403a801d1000c24403a07088614002e4038042c4c0300c440c283e40b054000c0c0c1001440c1e280d0850944072044040a48901e52001e440700e1002054040e0701107040b034a0300c00e19071605640d60083d142212009650096054101d9030054020f250440c0c0d241c03031207900204000a0b107025400c68907000c00f425030700003408108024104014010148207256000060500602c51320704c0c2c0d401c502c0d24501ca04000444 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 770753453 1250 770752203 770752219
    0x31303051510050f100311070620030c030c0d020f210a11160f1407060e03030f12040218091501080304080a0b090123010e2a0d09150608070b0a0806 65
    0x60110f03c80d800c8001d56070322841f1103e50b5102e090a2507000fa200c90340d41d41c0426452402100341112114007200d00c0340c2140c150380e07811034841c04003940030b030792103044401c48a5409100e9486801d044500821540040541030182800050b60007140001d00501c4814580e20f001c00201c000340d0954103c0d10001501403407100480f4a0b4540389504000c204006064040f0710020300941d6000060510f099a01c181c840d103500b400600200366a9120b280000403a2907400c0c44925102e404000c82d9507003042c40100440e2100558075a82d400c5008210341480c0e81c0c5d440105c40107a007205254440d80500040d00207541707014180340285a0751a880c660041c04299481c1c0002d40489080d408002951041d0103070106284510080f19013414080c0104010010300c40d010410042281c3c4a4000724545c40c080ca650314201d4071285921a007001488201082d1202e4040e400107580115042175013842d004002100c0d820202400c0c940700c0707140c01c00050b44400300050a003403034220144550051088036800 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 770754703 1250 770753453 770753479
    0x3030406050901051c021e070203071202010c0b0c0301090605040605180403120501030302030a0806030d0c1211060a060f2c0604020c061509070c030504090e031303051510050f 77
    0x4c4440c850a1608140c0a00c145404103c4a0b601e030001c11410030303905050641180f1001800c00b013440340c414003e515500082d420001d46441e2001c5a0f0b000303005050215034070180381c83d4040c0c55102102d050403610000001400103036054031443d40588029101000308608140c0880c0c0405490405804030000c60340018080501c01c8609072a04e211b01c400602441d65a460065038a07048640c818020595040024115050020b90600700700041c0e034640c80340c1015070300d40d4850f0b003000c1d8040a007000369010241c0c008900030003070f05004041000c40000c02c1450050107008005031900007a602c8007500312058000d00414008044d004034500da1390219450301400500203226240201901d40a901c080000c0500c01c400710940c01003081d512078000356100c4004481000b84164001d02248080c070052051030700c6540301c41a01c3c2e04040441e440c1c121050340030030300305a00b58800c5540c2d41c41440e004a1150341c265826400040d00c524540307000b130409000802031000300072618001c118601c100 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 770755953 1250 770754703 770754707
    0x905060f160f11040b010e03032a030403110909010603200d0210180503010509120d230709080718230c040302040605030706020309100324060305070c0203030406050901 74
    0x28001c0303522100d802490980c9190409482074200065803107185880652044c41d40035051003101132000030080c61529040000e012040c103d2036454400c00c4400100603403400b00304000a06c09540201040ca20880260040001490300144545480d904003541000000c00450720910f80c6501e5140887c8440559800714500000408010394000c10881180075038031f401140311048e039012125600f2400f038554041c142603502c29a00140382d07503c20100100464080c01c0940b211103064000401c140204030007035174101954491100c0040003190920800b036404c1840b5000030811078001d01019807501072150756080030240504440c5803160008030300068041c0b245684000408420412030800148040d242c0d0881e00080740100d00d0300401240620b00003400c0021034220f94011880c00303070910b041c0301000c0b000030145418180c903003581d088020403c2d00001c14070210104050715251070198002e040d41c0014041c841071042c282908409610007004171003d403141c0f800e05694a82c400703401 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 770757203 1250 770755953 770755987
    0xe0c040f080c0a060f0e040c03050105030105062409040f0609060509091c140c100204090e0118020f0310050703090308150d02091e0901060303021c120b0a180603120905060f 76
    0x341b65202d4581081c10250743c1e016400103060b9402a00200300a075640e01c248407600c5010f03d070040c64050510360702c500c0498010020080e4281c09400400c5044503500c542c3d05448158100800190f101d12003401581403541c3c00c15030240c2c0c1c0000801203420003100720f8800340d00000ca11070400c000701c58030783d4240348000215070301464268100c071054104c0608140c000e40283c02004044da0070b1409292220505016148100e0505603a0342203481c50b981c01c00202c02c2c072000b2056010701a400071685030342d50a11842e0f01c07505864a000c01ca00e0b000f4903000304880f10003070a007580c1406c0280784098507240e905022901a074140c8030200692511018400c0e015014100000d80b0200041001810141900001c0449101c0e800b04d5481218404403061242c0010010720005181140c014810301d9447c1c0206009010151040c102141c88951014000b81d0f03800140c0c84030390b2100030820400c0254207090002910340e28000c25401d0900f00083e001d4810764640e002007420200c1d909200300c500841d = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 770758453 1250 770757203 770757227
    0x7080c091e060310030c060306060219020f0a080a060b0607080306040f0b031915020c060c0d020409090303231326070308010e060303031b03040c0e0c040f080c0a060f 73
    0x11032512407604000303418202d41140000c40703060301c2860002030075501a009e40d2040e50b205401034800380c1042e44401046400c0704205903841a984603640d03010752500d01c002409401d0039005010700318040d0401c1f505481030210114018081000081c2c04501000c05072600080110340101e01c4030b1407001110060100050042d5044c040c940c0280359503500c0300c00e81d40e10540316540080700c52000047c910308030300900200340340503082040090b401a468000801d03085001540c01810251107040c0001200c088030000c07404a903403108400c59030210100104d0a4110650880c032844c070b400180720202c80e2085000074034146200b08403154450403074400f82003200360f1049440e290000344c200241359100c280318414002c50070201142403410040122441a0440c02c2d62040d204400041280d040c0e00040007611400c180e02004540b09650340045400340302500c2015031101d0230072908034080e003000d0340200c8080d4007401580e16683c581a0051701165460f04111903010041d41050b078101e802c2c0c139 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 770759703 1250 770758453 770758459
    0x7060c0c0c0611060a1a06030a020423040f050601120e1507030b1f05030103030f020f010e010c02072102060a110609011b0203130902031801020708090907080c091e 72
    0x202011802d55403000005140080640440b8000d8440f05003860031038040c88080156032540504072a11810030500460701b00c80f0100006140c680c1d00c0840c01411019a840c03450301034608000c0041500d0540107075010100844800c00a40c2880c00010b0300c440120780e10320101546589800c07021900a0003c107080c11404041c800703003480c113208010020034501a0302d40c800c0b119441c001540740d011074140c60740041f1581369103107540d0854809031410000884102e045215072940c01c40071610030301680e04c0c5100080b0011130380740700440010781400a80c1c0c0103907003c0d0031001502e8607005c00b03400d0050000d0360159200c903980c0c009400e0403182e0703102076070154800d88926000c2c4040c4940550285c10100f084d1528124018a860012600c1e0300c1100d6600508071b400381800d2004da03100d68002c40d004010604004aa841c0100794142a0f0f00043c60907110214041003050503400d00c01c50a41e48110585087e05d9540713460740546c3e095024285042d0b0013141510340038500119404c05000e4040801 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 770760953 1250 770759703 770759723
    0x1002010603020d0b0103020111061003020f06210901060803131715071218121101060503070e01172103100905180c0906130e0c06030c1312020607060c0c 67
    0xd003813208490400303100403070000310613541c61070100502007429801200743d140110126451a020080480700da0320010f81d01840420659450003c4030b1038003003101000116141c0c9610740600800d0031070f0042c2c1c0c0008404d800c10403941c00482411441d400075100c101c600e208090400d801604e20b01f07000a80781c10780f0705401e10f05211049400950281c88483d0001d0180601d482050000031100b04a5000800000c0c1841d000d0307501900031091220424540000000c51540d40c1c0d000038a80350b034903405000c11500c558018041d80c03603820307400030701c07414680700030000c0d80c1142032103210049032011710000108021002c54607192582013808002d0245810501481c18100203042079a461101541031a100e105489801c43c2010b400262291400500c14080c0f9162003034000094000118503d0182c0110280200907a407584040c1d4003038592243c00603241c400791581e011403030006402241c031140000403000d005075036060450300c140b45d11440203d245181c1d03d105980b2051000ea000381032a00c8 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 770762203 1250 770760953 770760979
    0x807060513050c0109030b0c0705011401140f030d0801050607050c06030c0c06090a0c090902030c060a020c01180b04090e010b0d080d0f021606020702060c03180a23100201060302 78
    0x45144401c1c4540214255548104101c0065414191500c07004140f002d81740002000c5803541c1e009004181d00410000c1110794110100500040003604240080d10341c51030b2403200c2c2e0411212842541d1020790003412900d0320a6400f174101134051180324810704d000551442008810300955405043c06040b998480c200500b0203220f64000e403e01120900c00c20000920803000000e500c40c142e03810a046c0b0402a00b00f00130301c0301803e40300d402641c15109040f01d80000381c80d04801070001100c80c0c3e0142c00c4903043d0b42c00050107001d6800980b00142d070140701c01e100c0110070070115022191074601c00039900c0040c00c40a4090003000754840d600c0310b503122050081c400b2110042200e42c0000c03004001110040020170201e01901c0c868258954201c0340000005215600400160303000034001828950000229851341e030010095400100700d48140715207504016200b20045c00b0804428a1083c4d400c1c404840107140c0d64030124807070071881d48204c52032030013940308201864014004405c003031a = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 770763453 1250 770762203 770762221
    0x30606070f03020d03290f0301060e0a061d070534052508071701060b041403010c030203071725110f010b010804080901051204050d0f0e011b08070605 66
    0x44083c0c0c0080110b41040c80c83d6081c4c003000b148120b1120100501c0303010205683c024811f41a4040000315090f41da80c0001003144c410140c00e0621412003140045021424103003060166081e40340094802c104007400d2011841d041000c9d0f8100129040240311300e0241000307200c0000e01840b031159100d03000c4074121014840081840d80440d409440c001a210240ca411034540480521800343c040c1c208410512108810140a01c60f486840700082441e507124080d9804540c0a5805200c4902192840101500b03081c021402c940c0000d040841c110b14003502c020386500b40100c5000004071080c0000b40802c0c1000311b417161200b1500c02170401c1307018950809810310311440048091403168001003407001405008228142c4d506a44403485519141d0380c4500540106400314184003003030040c00c88107004910074600c100d001d00014105007903025005010311508691000801c82c6610410850ba44c019103880d403090486428640a00c005080101c0d03e80104100101b0f403504140902185036 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 770764703 1250 770763453 770763463
    0x8070503040b0445020c030d060f0317071106070501140a0c110307030f0f0507050a0c05181605070f06090b0f010f082e110d1103060d08030606070f0302 67
    0x43c01c5000020005410703203165805000455070410841080444e1031004290300d8000c0c020043e0003500301c0341441840c0c4901c40c1070b1003564200f083c01d2419034000f0824401a01048030b414244c0010071841d0241a884041140b00c02411035800740d1030000380d6100704803095101820302010303a410301c0c02a0422407150381c040c00c00642c4a900243d0041c000091502e80401240d04c280c0d0705889080103000e047c1e03401d070785034400103c0000611509100d2400800c9043c85094210f91051030348403941428081004090102c1408075400042200100000601a90751216210100341403c9451764210f2910f40d20000c1e008000402c06401c040b0310b801044030200c0a10b0003441c80c25000d4155a0326100c4003015610a84191000d41c1c5c007901c03524190a62100d1007440b40405900580042001481a2000d80d0280c0703000029500001401116203100c500c11fa81e000005000340c5481e40c103007180084e06400481401501e98880040402c1407a0342e500c1c01c645c125a07001411f855100c0c22403c001c2c0d168 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 770765953 1250 770764703 770764739
    0x9040204091a040318271515020a030f02010203070e01030b0f0d150e060c0919080609060702060108011e0b06041706040302010c09080a0b040c09060f1a0a050708070503040b04 77
    0x241c0c5d2036040c0400c0300c1c0c1d29000f070b0301c204402040071030303281c5801001c0c2c02c0c0141c030300242401e091025041d40403414004c0340c61007501031320681d00181448001458010000b201d100044011a48180b081c44242075000c01303000c52245091034040350703030b400c0c50000802c1c03440301c10241a0b208054040c00c404201c4185e01454005640d041e042004500182c105030310350404480c0c8440440081050304501e1070300c0084801541c00306298141d0458036260030030b180c100c042d40c0c2407400d9445002007084040d4100021805401404001d01141e101110710394140600c076150781e0080c544a00030100301e500c0344070035a0002d0030a880c10100c14032a10341c000781c41342000e8509800650a00300702c00715150060806204076403240c030040801e1010f0b6261070640210240c021200300c42c00e640c0010303120b100f900814028003030700340104c1c1004d4a000d102d10030806c1210b03070203414440e0501003111855008010307124078a41001c4401d58136030b91481e0032070a502c1644c100c0a0803042c00306010407000d110903030190300 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 770767203 1250 770765953 770765987
    0x70810082d010c1e090f0e1023041a0a06030f15030b011d040f030522060e18101a04090609050711010603240605150307090f0509040204091a0403 64
    0x10484e2064401c980780b24050080c0000c0c02e031950002c002070a03100d00007560024801c41c2d8540740c0e40e01c0715042c440c0d054081e202032880d12152002c042ca249414429203480586000351110544026000f082c0c06c1407040c0701d1601032543e80d01005054509070380107490228032126228070a0354072440e211040000c01e0050100070b1480400f9000d2a10308a51014022a00300303c0750400c0e05c0c1c003507070125001d500501000700d0b07003000c05240d03403060082543d0200c0606150380341e02c100540c1e2907043c8004c85540024440946c5240010f01010340020704552040d6040a44410280c03d41c40c448a15903121719170007001c001c1d01e041e40000b8000425032000d40100002c0e0799101210842881803800e03a011404042d106140800e24490603003500c43d204212954409408903980c0da80d440025490b10014070240325225000042020300c6500c110b14102802a2881c500708060a04010950102c80108000c0c000c0c1d95941e405820f0248885200c030069800c0826891207140501e0001d1807407200c4074240300 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 770768453 1250 770767203 770767247
    0x260103060e1e100c180306050106020c03120403020f06210610030209011d010905030109060203070215100e07050d1d0714010c150b030d08070810082d010c 68
    0x1001c440d907205000b110b88501d00400e00101c0c82562140101140007009062040a0035a045407081c8034a0200003503004032400900c640c074114020341440c07000090707948039402c8002d689024811190a42e4156601560407021519541012800034070a4418081c0700f040e041d02001154802e014000707100d0307001038920314040c83c1217580941c2a800b441d481540031800880c1c0500d8890340e110084103100c001498580c5083c1d0b66030003c00d0071540624400c3e1026030b00003013082019a01003080032003c1c400703803c40c0c2c061854000500d0103803104601580f50651084808250000e00c01c0040d03911401c1c0e00501089411505c071038000340b8a03005550110700f4094400001400c008401c0348855845041c1c4a01410716403a1b9554204101820700e0410026664444180c150b03d080000300e01000740d80e142d56410b414500300241421a0082854554510012040c0110480030174000700340c0351305c658036201070398080780340383c4980140c2c0d0701c13a030402e40ca484080d440140e80f2412005030281c404040c1030f = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 770769703 1250 770768453 770768473
    0xb221404050d17060603040b07030f0e0c1903050712112107060504080309090604111c050f15131b020709110a0203070f050309150c010507110d260103060e 68
    0x1c140c850040b10004d85c050400d000040107d585004e50303a5214070903250001d042c000110b141c0084481c03070113803201203511660841059082c4481a5900c0503e2481a881380502d5940c506956071002d0003070058020072a68000304202c0c41a500004880c1c00a00b42c0007000400f00030740d40c07a071401c0c43c052407240c440c034600010050300510407141500c1304200550300e00a654810b01a003000060f05484e00140e445100b030760742d00100c2c4094026101000c51003070500304030b03c42c0c3d0390598002420222400e44680300340810120003a40c030706640041030300c824400761400c3c60030310010180d9401e48151075000b2141403035140d40c0403c000c42508c2c4500700810848612510482060180c01c00d1035025a20401c500c50100e800d8dc103035110317410701c80c2084034039181031a4045002c0c08070ba031264811605003c1260450500280a03103039104030b1318640f03609074144580d5074a54a401003a0900c09201c03412000803641c010301240e0f0044504082c002c00794950b0341c4d10340036005000503176040d5400d0003452a02 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 770770953 1250 770769703 770769737
    0x308070501051e01170f01090b0105130e0601060309022409100203040302151b0f0304060f030b03280b130c060c11101209051f0b221404050d 62
    0x50b0f800600d00d14408103642c0c03c0c0700610401c41e510000007a0680700d0302c0302c010440c0c1024022031505500c50b681c44501545018180281d0f0901502c12404132400d12030040d119440000d8920704481d280e14012500300110b001164a52590720285072140900303801000c3c000a10344000d001031401a12115000003685a040b80c880c0070b0703804020b50240540c0802307135111b401107014181091080c7c540c00302c0201c2c11282145001030358a200741a40e000810b04009603504103111002034440c60409000e4451784500083d2200c204d4440003200e002c04c50210301c00e20b0b16413404944802c3e4028001041c5d810920035440204d002d9560441d96142d6840d804a0445e10441544050316804003810380403007105d1082043c40c480d203951200411104a28480281c0c0e0640142d4010702c0c021405040d40a807a04035002414810301c0c00d1941850030002e4140c0c0d1902e6040d0740c000d4010300d03035101214112040e940701e405000005404d02000044400b0311045c80340100d541c1c840030030765031035403450b0500c07005070 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 770772203 1250 770770953 770770981
    0x402090d06140c090303030f06030f0d091404060e070c110d050c090a0b090f040204021215011107061b1403040f0806010608010302010f0f020111040605040801050a020f0708070507030c030807050105 87
    0x81340c0d01a0403c2c408038015038452500e0a410035802070596040d2810640e00c0703440c1642001c01100002c010800801042c01c3c400610b4218500640c0d05000c2e89003400500c010030480581044200042d1891103810f00681c6103200c200340c94001e040c0440003006040c425a1600c50000082c8102c0c0a8030100d2031856052182e20000d000c0540486076503a07130382e00c8074802140014020307038009030208084000c004000603101e102c0d9251510740c1c22900380c0c8400050012010f0710340e04615510101091203102d8012852140b41510500140c200115500c1c00e0250b20b140d10042e40401c0c44042400b0441070702c681041c80c1a19014401c03515507a80e603140444400d5402e20010740030500048618001c40d101c0c0c00140c0d00501280000308080442980741c4020364401e61000c40010000300d03081c0a0b00c0020302480d9004407100c40154100091264000788601c2810303001007283e100010782c54100102030200d00300031504090781d0050300d60b482c280b00043c2d0344000070440b4207510344000545556000c5003 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 770773453 1250 770772203 770772217
    0x111522090606022d0a0317070903110d03050408030a0c05210f0c011d030c0f0a0b0708040c0902040803040306060501081302040b0d020316030605061507110402090d06140c 75
    0x100402624135050b0852260315150300190a1600104007030003010744040065641c9a440390350348000c9120030300c2d00180f0303040b4040d0200c020000380000c20000f103520b080000034200022186a040c0b401d191809880c2481141d0107103119000204000350400c1c0c0043d80c1640d03107806402519240e55044440d114240941072900b2000d4205001010f240255180030307145921502c1c0001640d42c404a221009841100b4200c00f540e83c800204481c03040018001031020050681c01849105240e5560345040c0703000900e2401044000320009040c4000c000e1818010b0180b1402195660744804500d82c50303903c58003003034030014141400040e055110710784d124815800110105503105055003004044c280002c601ca50004072080c021016070b4052101e5030000700fa18544980c0b0f10725500d8040241e91000709000c1c4120f54800c010119226078804807a4080e90110650301103540355000034000780501c0d0f21142c2c001d00441c520b00208000d56200c000c112149a04600715503a5007524881e031841242 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 770774703 1250 770773453 770773457
    0x10c090506070312091103030c01240b160f0b0c0a021209091506040f0b0306030610180c02150f0403020609070503031206030a08220e060d111522090606 67
    0x1000e42d04071410554441c5c14041c1c49207040c645680100d0000901d150031001c000c014507552103050800214041445c0e024100c0d0500b40e202e8824034042d01c8480d1801606c40e04d11070250a80c1010301040024141c042800360302032002c0826040003030302c00d4030a03001080b2101c0544944d01c3d0409014002109403207001e0740040515147ea5504810701003181c0c10400ea05400c0a82400301250450151402c003001d4080050366585914085082500e8080b024000c11280d07045100180700402d042d8100c01c030074449114021401d103110705001c0346000d6040320001c5003080d542c4240002c1c00a4180d003640074501139802c072501521362036030a9450f505503114156140e4000c0043c10040140c0500990f41710300002d06442580d4816141c2d000c0d20782c000c1c0301d00004c10b19081e9050b84400c3c059941c20016200355003030501940f5000001c03c440380311001c400383c21412000c0d501c0b90180e03a100c016103803c4c08052203207a11420f51148180b5100e00e00822800154440c00002c504496548943c1d4122081c5d5 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 770775953 1250 770774703 770774717
    0xa020409212105160e030a240b09040506060105030c250201020f0d09150203040b0d0c090b121821040609081606052d04050a0b070f03030b030309040e010c0905060703 73
    0x900c0103869609100d00c0d541e405004042100000c43d00c0624144544001005030385524a41d9900c04012074015040c1c4600c102b40c4c200501002c210b0000c0c031141d010300c0a007011640ca4540c4903400d1500d00a4604400440105d030302121000c4107040184207406100b0b0f021501d11485030242d542e01c03008480b02490000788007003410441c142020408606005260040ea0714198854405000310340c0703c60364980d440c0342c0b240e0640d41107940c8011900003c1408441c1c1c2400e00b505940c0402c140d400c00f038503160045596400c907034ada0180c02c0c41003203422000304580c6001c0c66661403d410254001e03108800100b0300125000a0107200400c03150701c8050706c0131045401030304000c0300b41c0f11600310b801c59844001d1001c03104080a80328240ea8003240c0207001e00b090300c480ca0308081010000d031341c2d081a580c2c01c1042c0170010000d4021402c000059074513003404104d4407a00000b013403a502900d03c009034864102900391506540640c09401403a0455680c043c000b52118180107a41c4500c002c014006840 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 770777203 1250 770775953 770775991
    0xe0708102021191a03060106020f062404051510110604150608030a05041e0315051504090f0b07030b0108070807120501031b06110a020409212105 64
    0x4030000260f4409900c900315640309070451514011221000d00300d41c180400e4119900c80c40c45d00304040f40c014103003440240b06400207003010544030940a403458258034a06440c00700001c448280d0302c0c0781c3d180050420440c1e8a0301c51003c0b11000d500f828183d015005550395824820b00c14000700300c04100680042044d902c950303903842c1c0741000b44c41c6990b011541ea010007003400030050006201c00c030b900340c2d9481d45850522550044100000708160284407003002c1c1040040c090030100803e0600001000410780c2c0c0e030340360305201e2030600081184e0143c40d1040364000c104c1c2402c0d00d02d403100d01800081020750740301c0c5015800c0b03516140300035010031036140000d49103900c1141070b50b522100c50714040da20400d02c1001c54041d90303400c0c1c004641c84414048104050140c6160840051040b85030079074000440c80413458940905100c040d00503903c5245890034000b00c0c41034000c410001d040b85d849074040c803403801080355440c280a1445003600b04c020010f041002e004240c0982001d690041d04658 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 770778453 1250 770777203 770777257
    0x60c090609060e120604050d181401121d010c020c04020a2003160b0103030f090b030c0d06030212070303020714030d030c110604050d090503011e0e07081020 69
    0x16000180380d022100c21160768031181e0500000f80140d100d00000e11123000da010000e806a0b110b801e5040b03032002e50180411480c205614078200f503813007e080813202540c41004041c05881d03210145440d1411041c010720307450005501001c50f0303401c03035400c3c5d130010740050040106a01c04c81810200142c3d038040d5a00780042d81d41c1c0c103091417aa14000702c904e01590707100d039152814001c00d400e803014182d40004005040e049000c80c00c50001038548004a01d040c10981032480c04084c01100e14404040350020a00301c0c180e100c140a15001010710324a909042c004983d284c1150204400500a440f0005800342c01540313140804d001c020040d040e490300c4054224028902200b4403420010704807554078990409100306405a4081c00c0602004040144064080b480641c01240a030f1f140410001140302c0b0301c411003c003174042c00d1010a0114600b50214a4100c00e600040300f64011032811141c041926402070400100054111460303000d00340c140320041c060720300f06013030104205a051320301d08 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 770779703 1250 770778453 770778467
    0x4031101090812070c06020d0815030f160617150108060105070b0a0603262d030106030c0801050d1e1b060921030903082a0a060c09060906 61
    0x90061500105103a902c114540c43c10010400c00786400c01e0000311300040c0b1915040303800141031203000501d07120f0140c040042810100030441c14862050400c08a038640d01401548182c81400341111441281c030300510075500700303178803074040440c0001c40e0540b05040c1440e03078a4812a51800e040584404200055540fa4002010541003000800c075003070000341e42c500c100e4041c1400450000d4114198035020034541c0e46242009502c100d1001d001c107440404a04841c2003100c24103445480c021051481010059002d030003100101c404030020980c681d150f44040072281c0d003561007005070390740c5105011700f0034a6043c001e011503018580700e4040401c1d5441207190303203114450580c43c01d2000d5013001000320182e080400010015001041b4803884150300c48596003000412540c6050503a074003030001c0202d440001e0100d000418508240000c8a540d0003440040e079001d500c0301c950100780e8640f81c0c003c5103c112411440d0110341c911061265a5140035980c05031564a10141000e009560f00 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 770780953 1250 770779703 770779733
    0x601140a11100e0307060b011b0807080705010507051207080103032c0307120303110c0303010521010203071e08070203032707080c1503060d140a06150f0f05060403 72
    0xa44a980031140b1950114401e4000d4261010095900d8209a142803025106001000c0e41086401c030010790600440027a07429819074465881c60361a40c0c030385400d610038004c841e0064115443c00007000314040d0424000c00c100780e0314040c01c00c910f0782c1e88441518001700078000900010100c0500c00b50b10108000480b01c10764101c081613400000c19030000789410200e40081034541900301c80c9804268150007100086ca120640c210700700307520a4921540da010510a45116044800c406c580050100c10303209966010b15000350350386d1518140140007034000c06000400810004205050148100031352400307804640e01170361849e12a110040e51010881d11640761030390480b6803940c00c400c42004088010718100024240395002c0e0410807018000c52010b10710480390400030004250760368641e0140341036016182440502e80c40e10740c64a0610007a1006100c1c0d4a0840704003a0055046c9810045450881c4808581902c4058606d440180e52041d990402d10610040c80091501c600340030301 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 770782203 1250 770780953 770780987
    0xd030603150f0e102016080f1605031c05040c03060e0708010e0d09150504090c1106040323090a0e0a1e020a0201061205100e10020c03120601140a 64
    0x1410f4882c22000303003803072950102400515500c0d0030511000001405005d00300c5900c3c1c03005820402071894980300c42007203050062114a001644594200c617150a44440d588003c80642d41e03520380707107800d503a00d52048050b441c481210000f0b8080340126030084520035a80188241101071945e0340c1c0744041c0c43c0030860a81d46020301c941c0802e80d13150034450407028010940081043c1d00004901404001450f0070081c08203090720000029590048202d0301100e80b4144005100c2000781401c4450030b84032610580710b80a5101400107159124020741c0785101e4024141da2001c0c02d440c0c1c800103d1040909c1143c100074028000c105410200241980c40700d0a441d002c60812020310451039001d44611340d00c0030741c95004c1103000102c0d0742446101d024110700c2a440755115104c0c1ca0b41036030f80500f000c0302c140c0991100d6010310400f4090000c5010814001000e549454510701030503101c1d0040381072024880c500e100000c034207602c40c000c407c02902924004515100c400c2c40215440c20b400a84050 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 770783453 1250 770782203 770782211
    0x131806050c04050409050c0a061b14120a050c070b0c19080c06090601080609060c030a0b0102160603060e0a23070e0a0f06030507030b0105030a0b13090b0103050d030603150f 76
    0x10161135074000c4c0501c240c031035405421500000c01c1044000c10340c5810074001c00c116078202c00d44e0400d80c0115101c05603001075450300540c03001c021052420030544000002824086441000e95130414050010440600141c40150352208501507860103125100e0007d0f0b40003ca820f40701d030140c030b40440c08050003051039610301030329000c0c8603180c51020703207010240d0b5000e2001003084c403000f44140c4e50409010f101034482424800403013130b9140005402c10050310f6403240300711266030080040e124000500f03811303011100e5544c08090000d11300c91241d40326010f0301c1c1002464001c00d5106080c0c2442c0c016014200340360001d8541280c03190004d02034024080c48060110741c0344e4602000780014442c0e00b40030800d2505018006080d180040c000c24181428040440002d030303040030913680c1c040010030300054000b00c81c0c0c0000e02d042000c820f503c00d0b41440c5c484040706200c3c8002611341a00d00440071140c014255000407030464a1500c000380c82c104540078458034408098104007410300c1e0481c801300d = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 770784703 1250 770783453 770783459
    0x30e03041413050c0c0d02010c020d080603030c011e181e140a0501050a0c0f0905010f181e05150403060917031f06090503060c07080c0304080c131806050c04 69
    0x14211441944c421000400c0880c1e00b01c5143e800300042c080e170f40403a100a0100c40ea01c180007039503c039900030294003400010400a4410f44040040d40c00c100031110007400184461140d00003180400181c17003183e1800c000c515179a883e40054412042984428480e007603600040d920924440006401c03140c0d007030407500c0c424003071004210b412314030fa00a0300002420b080552034003017158110700701601030061281c402d280e0160084601800c40e00c080c03d0001001c0c1964000300d581000749503c9500306920f00401003440118000905141120312088184681d110340400040e20172412441b201e81e00c040200f0300014803e41c04c403e2242d4400d0510300d4054a660000d00c1d0380f50022621380340640420300c0d100b0442c3c0320312507004004141500300140c11900303001c0480d4803030000a0000e01e02400008003b0108801207044625912652054a441c1d5444416280d21035801300c4078184209030408850541b071040c0d205032094840c180400901e003414503503500c805043c0c002c00118030548180400 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 770785953 1250 770784703 770784739
    0x1020f1f200f0a0f030614090901020c0f0a0b0106110709090503070b040803060906240f07020d080c0607020615040c120c0e18060904020112110a0c12030e030414 71
    0x58030840b26814002a1100d5a0340d1005004440c03000e4180c04140c01e00300d0820402c0c0b51404009640702c0259001d031615511040354501a104003242441c007032142c1c0708000f12294010500003007041c071030660845640d99030003049401f04280c00b644042074000d1541005901c0b40b0341d00105201c1c0c4104142c90506885499172484030508680c103460207000001084240e10709448880d521040c111018000d481d1001c000320b1442e10740e20030540622100042020b007411600b401d0780e90103980101009290319080c0f52000c040e4204c50341524040c0328020201e0074650010a20702d1141e51600d410a04445a40b01040702401110f4141000c0c0000c5607154840301d0218002c0c1d0308060600e0712100300c1c40c000e40e0180840c24500741100c04a094001047c03101c0390780c4d214603d07a000354092034403620303642213252110020400355500300c1000c08000b40c0034004c2ca41000c20b465103980940400101400c0c651030540c1900c501c00c145910540081005014580d0050b0740b500940c07402521582984691042e1 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 770787203 1250 770785953 770785957
    0x31218070e010b0c0c031c14070f320a020d2603070207050f03070509060627010305010806130b0c04090e0a060b0303040e0a091a0a05040201020f1f20 66
    0x100b05103d460005010840c80c41c100011406400280d000342000c40b1a0b007039400790250240103410410450034100700750300d00d81505440c4a150080d0140e9660245443c0c040701084c1203402401000341111900380603850945a00017501c001c0c1d001a04075103e25a0130891484000340d03045510040800d00d01020f10445150381e100c20100b9042c9070750724100720402900e07103481039210520408c01080c510b040f9840215003001200c90581d4036081a45032980000c21500500c00046104049000d40282107007802449104c152403c0c1c03010499130362036040c2c02d904c0340400c540c44609004048108000980c030841200c0e44400c01ca4400c6040c9030320352407440181e1b900c0d00650314031b40d4040b02d89201448004c1c400c580e2000c0c0e044000b5403500f1301d0310a00402c0c0341402407542000c2561002c41a0138482d01070b0007450800360340c2203035140d241383c005c03d00c0d4000d000a40f000da0041c490805007000300e4000290800d2000c0c0070300700010f18031140508010140006640201c08840c40f0110b40d101070b00c0c1400 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 770788453 1250 770787203 770787209
    0x40b04090b15010e10271d01030c0509041a0403091d100b1e0d060b0f13140f0904050109080c06040b0702030405010e0f0a0512030c010e031218070e01 66
    0x207102c205244100c03000601030000c854120748654200100403455a400a0f001386040010340b942d1000d0983c09031801d4040c443d264000f85160b50300c1c44184a1001c0c240c241281078901c41e064031500c1507150401e016515004885c0140107541e1380f4030304140c070320802c9006a8802d20a01c5d000249544604e814864041c40c041d400c2071908142050102c1034a138408510003074424400841d0034941c41e25180c0c15400441d0300a07019110000610840028079500328070003802c001c8920342d5541c0d0107401072000c241e01c018901c0415a84064000c00c140ca140381200501e10b4ac01010418240380c0801041800c24002d4000c41e2207650b9802107400052000001e02010110080a017035685014200f070120058000d0521085400400080c00682e8011a1000880c03009030384aa00c03040892021844441d915041581c2c0081004551a042c007000001440b001c60240000c0c480340f0181d0000a90f00c0c01215420303185c0c40d50320000129242e0706a8225980c00d500c5d601140d0b01140c2e50141d11031420002e030 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 770789703 1250 770788453 770788471
    0xf021908010902010212070f02090c0d0216060e060106090618050a03050c090f040b0406090615090f0b090118020306010c1e020a05091b09030f01060b0c0c011805040b04090b 76
    0x101002c4190341e0103208880c1c241c1a4400303000d14194180d5102d00c020070030840004d109824000109001801590a544c586c40c40744c0d50441d03951041c0b41c000f18100d94413917021100b80e030402c1e11480d04e4041c08601207040381d4242d2144000c081c1010000d850100160742c9a5181c0e41070894002180d035140d40c201e400440c095005840031103c0346081c8041d582d4010960900d2042850038440010001e10245a00c00e803c03585c0018881e42618000c1d010f8801491580d0040c511840082100c41e2554000061420841c40401100c0c5801d4140200b660007442803590700300c22403031400301d450074030307002580d0040052525040c842415600c841316003409140a0b40400c012a00c48001c5042518407040680b00483d849400781c5080d500400c10005509248166010041205265a20200803101100c8160030003440000d448400c1c2d900035400041e9981c8141c41060040303a00d0b0b50064102110b0754a880189181c01c6007050140005003000460280d0800c2d42c1b103881801049045004078010740e01e41c = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 770790953 1250 770789703 770789711
    0xa02030c130f1d01080712030509030a0308070906020f0a110a050d060207060c14031f170105040c121e050a0b1e010803090f0103050c040905010b120109060b070f02190801 75
    0x1042d1000051030350603800d034200c0c091072001400741c840d000035146e0481d4403005503040c01e403540d85411142405841159600340c803d09100208054000e80034600c9070b440c5d50b850000c004d541d1036080703a407007540604140a43c7c0000c0b40c41408142c000c51031158501c8064489a40703196108049100444900e1041c0c0d016076010410030304008040c040c0c070b40444040d103011400d02e44102148000e500c00500090a60343d40f5503040d5141542c030200c520003c0c81c0502c0451050b240d45030500707002e40400c44080b05e04003103060700401c1d030b00c0e10162080205a0016a450902e0000c20302c0e5002c1c0801d0100c0c155200d1190b8428003002442543c0d4281c07003004d501503100148908a84a440301e41e0041e00561166007090000174002c0c1c80f90b05520328109024071300404d9513210301143d10580d1190741c008011041c144400484d601042c031005009500046951681c03580e0386034210000c0721a41d001c0c0001502082020f2804120200020f404040c0020050142410402d440c00298012031380050896519 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 770792203 1250 770790953 770790959
    0x1b03030403030b0922020d1403090103150602060705030915150907081b160b070804020a0b04051f120c1e0c0f121103030f1005040e060a02030c130f 65
    0x12500a83c1c080101c161403500d00d5080c02c0030780ca044e11185580c01113011484101e04010b5590311f020a14009822a0080350106090308d96070380c50b90701072400385000c00e050280c9407020691003240001180d0300395000e0449502c0b02c40f4110350079880079211904600c43c60b4030580058881c1d1b010240101c104021400110032510203102e411400182000140445202045500c040314500142248000403006503140526404003070a000c4110300500290f01041c104644107402640203401140200d1382503119036551202c040c0c05104034003800d41c100c480c0203800c40211141c0048000090b10301d007401c1c107140c2c1250000d901150f0104102c200010341d26080f40003404540c8292140029152600003410681034850f048080800c100040080065000e84500039109842d042c1c0260718980a81e42e40b82048802e03103881c42000d482111940c00300c0107002a0034a4a48540f1028040c004081c1c1070507901e42e03203000000d40005010b4801038908015017103480c04460302900107462000d10340700000f82 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 770793453 1250 770792203 770792207
    0x606150d0c020a0b0a051b0a11060a0f0e0319050d0603080a080f090f1f0b09010f0608070c1a0c220f080a0305120709030c030b0601020c0301022d1b03030403 69
    0x10094010905c1620307200510901a81c551410b501903c008400c8039600e403e00311040368410359041c428111030007142c040c0000c421040d040003a1640403060113201c1d0602201050782c80e0310030164480f905c0a605940c4180310fa0242c0040e00d01d40b02c1003c00001c01aa0b01c1d10f0318030050740500e26200c0002c80203410011045201c628850b0008041402000107011903410199201800f00b60020f4590f01444888000d901c02d4003e072810040203002e4200340e5a40f01c10002c0d03540e095000e2040400d03035030000503060a00c5032031445241d640140503038681401100000b1801240544081000e1008210750b48943e880c03244e8900c8602d03d0141d42101c00c03403502014010101e0247c114807000d4010340000e50110f94441c0c04d8a03803074162203080d08002d46400c0b8055802030200c1e40000c1c98100403107000014080c041645500c075003404e07005c0e1490740800c84205401c03407041b80f086400040c490345003459804801c004c505200e0410800e820310340440342000070301c1040e6402181c80268000401c0008043e = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 770794703 1250 770793453 770793473
    0xc0901030c08100506030a06050307170d050901081909060e150603212203080a0e01080402090106030b0105090910150504030b15031906060906050306090606150d0c020a 74
    0x4001c91926210906003c801409401c0345441124400c040210120b143c00709658014030081100038100e98200f036403400e00889441d50400c84a145000c0c2070b050311a414019400c50795030500c160b481e0043c80c1d40315018100142d4a207040c07841d1555446444400050091042503406040c02d0000d0240d00b007038840410b12070100a040030f0180d000b0300c0201444c2d040801d90080a60000010581c0f035091001c400000d56030303c0002111081c004201c00818080000001d03c544005031b5038150544074600019030364880c00381c8000350010507940c010050588247d00c4044d20040500d00302d0f150240c25000a07002140070342d090003810302440d804000071145000c206050580c941400350402d4595100c0003001d01004043d00798204080500a81540e4140101c4000742010320340110701800381c3c100310004258a005868100c2d00c0c01c84e0100d428980024441e01c43c110040082141e40e4501c1e0a014680b66940ca0300344620200b03214440e986102401541ca000c9800d50051101c0901c03824040128 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 770795953 1250 770794703 770794721
    0xc1809061502030f0a03020c0f0607050d110901090506160f05030901080108150609101805241c02010c0210080405010c050a271d010f090203090604140c090c090103 72
    0x5035004106201d26061640145e40d205002400c0c01a02d039840b00503024145402202c58005501a201c00c01c03a1003078000f40540b8014800a10411000b01c5540000c2d065200348581140441c040401c2001940f82c258024480e800c81c2090400c26510703503640307251440e61803010482d41508041980c800c42d5900c9411035005042240040501c1840ca07102c1d070802000207014240a40038400000b140f519071565154014110141c00c071940d10902c0041c14024807094600c04a55039460005060030503a40c080200d1241000300500480b40080c5200c0d00040310b1232000301e060000500c9000c015a4901134000b07403928090301da5609510b8145030141c21210a89903070300600030184509240030758442c10403144038001b05d41c1c5103050085210038039801c0c041da5111600420000910070a203000b40300c40103048414440c0108000d6854104603c1a0700084a20300000d074003100c0010701007880c11f00c2000071b0682100503169000748000100d2203525088035205130074800040d10f9000c550385480707402d5070 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 770797203 1250 770795953 770795957
    0x4050f010504050a0b0307020106030b07180e06010f05181c06050606030412110f0712050c0303030702030901080705040f0e0717010f330801030309081f0c18090615 72
    0x6418282400144135110a000b010034188010000071003050003513120002854200c0210042440c2c4036800410100d8270485c21801d84045601c00101c032920701404602442050f100c00410041380c06c0d0490b441e400002c025080d4441c0300e803810b01c441c5c842080c0902400c00c003254980110905091031800d03604003034182402094204204404101c0e03a284201543c1e541d485c081c0042c040c680c80844c503140c1c1350a1000c46034094032600040b400d6144199600441c8281e0594400c03041030700415440b40030072654800580c000304504100c640c07182004031784c41004c40c1411820140c03030b4003450b45004180e4000050b102d015000f40101c180d04540c1d0040c0b1984400365204181d81800c070146480702c0544603100400038107070781c4003610240030060400d000a106601c0d40891106d100000e103141420f21003540800e131a5000031400700f801280490103410038008400c401c80415010000600d0402d1b022003c020948040040c9401100d046034001c0a20000102d007c50901e001e200d0260020380b00482 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 770798453 1250 770797203 770797207
    0x13021908070815070e01050903011e020306014e0e01020a0e041a010f0311070807020108060907020d0e1518010f0201060303120f09021305070306060311160302030c030a02010204050f0105 82
    0xb07107290b1000c40d00c0c1c0c201001f0301e8125180ca007150046800342c08040f90240c2c01c1c0ca0703208005c050900745076025610a410907070750303201940050b003c1c8800c4020120080d1502d00f0980090301003d0300341801c220b2002d0400104001c11007800c40d545411900c6950040d44e5603500000c242035007550040e04549030742e9084404200d0100e01104c207000040750554050b0500030107040c05401d180c040d41c8140c911044001c0c2c0c29668a5052401101550140300c040b40450300740000300e016030500c3d00499202c1c215980080408107908442510140020031f40180c5c0962224104241c28180354041d01c210000c5804840200c29110005003c1005906c0e0000441e0303d400e10400220f13610800080320b102c043d1300000f803180c1c80800d000f000f500da9000301075001a80c420b03800301d80c0c0d0f1203a4400b5101e80d855a40421655031940c004801b074410680040c01c03a24414480642a5005201c0642e0010301ca401124903010b080c4c1030702e03400d54214413613402c00750750f0219080041c1d05062408000c580d01c02d01e002c0b4 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 770799703 1250 770798453 770798461
    0x50d020601050f060715060b12160302040803041a160b09060601051801110a0f0f0c0906030b04060513050f0c21030f0c03120a020c011406030613021908070815 70
    0x1c00354005c00901805140d2145607080400485922181c007404103403400c5a03840c044005414580b500580d1000b994800524114952a21074070988041d510201c01461030030785092042040404944018100341c0c0b420010701d030341c0b03064036040160033034400d5042244600d410f52100c5e01b000b4000b0300d40c1e810300808200c10200000d6a075441c0c0c020440900b8040d07184004603040618112404400404540020840c2d40900107801c1e170341d0240d103115820445034070740c5a0003484151070440c80018121101c0401250000d0707070581055030321040f2007810307110400351a148d2a24149900c081c4500640003404040d0703250a11549041c1c146400f80c0f18812091044100c031a03407031181030b042c1e459120000c01d0f8041900f8003803003240e18403031040c030480d4692b003040311102c00294840b40444086611380080311180c00300521096209010003006050701c0c0c0d5a040c5a49100040c84070103e0b80212030409030307a001000125100003a0058000034503407182066186854840728009142102080c41c00304 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 770800953 1250 770799703 770799709
    0x20c0a33021009030c060c050c061b03010501050928090b06041a0a050f0301060801171c0302090a0b270d0804030210090512101b08010905090f0a050d020601050f 71
    0x640003007846100d00080e4141c040c102120b04111700d0f800102103505012040c0d164581c0400a019124a0032003541c0e00d54031401541000304004a120740070358070081c401000f00c0d40c083c8014020380e003006440e0002d40e00054117140801c540c007004103451070980784410301c1010b01c28420b06946403025140c00f841c05040c0382e074030009c02c45075101c0351030603000c0001c05440d030340d1003442074566150146442035120f50711070802034500c2c0c00901464921840345032044800b40030000c0c8005400519002d8950301d42d2991300d044010b54804545260010940e650001c0c4000090300203160384605c5000c82083c61040306542a0501040144644618121024600450f040030b04450841c0d07811507400300410000f040a40700c0090b20703446035900000326230442285010200c1c07009584502910204405944008035883c415804004440000c080d94014084003c9503803105420403084800c440c03400140d034400501d8804020f0782154a508a501030386801e0303404004580c09494211240000140c5182c04 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 770802203 1250 770800953 770800963
    0x1b030c0b0702060d0216020a090c17011d070905030714091008060f0a0b1002100e1204170f060c12070203030130050f01021b01020c07050d03020c0a3302 67
    0x1d01c00c00c845d40020140209400365a030042c034290701074424200c0d5a9160f0500000700480c0c0701000100d848480381100709a0b9000c0d9050682d08580a0349842c503145402e8001c002000608100520046d00400315040d0380030869003005001c08444000c0a41101d030500801043c0604103400350088031506002c0c10401160360795100c40c08141942040d900c249800b0301404014085035041060105c0001ca104d5000c558400714268045060091804003003645595850003915000503100c24041072050030300c0303030a102002440d014108d601c1503000f5826035041801c20740d642c1c840068001254014074075682e05240d8032014500207141551f1411a0012826006110311441d600c20841c80000b00e090701c1841c2c00c803464003c411907170680550034285000b0750150003039071500701411000c450041414005c039641c100c40c4102900095180c0814890351214401049056008804962103551030388200800208008000406200e050003c00c0c0f0701c0b030400c800041d800740e00c002d213404c00d02d640000f8 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 770803453 1250 770802203 770802217
    0x52a07020306010333020912070e060d0203010e0111040f060f0c0305031914070e030c030d210218130227010512040501020304020913050a1209031b030c0b070206 71
    0x1084141c90f034140e20000c11880603003443d0245507841c403045c054041c0482d601401182d02c0546036030101001c21102c0300d90340c010a00c5220001c8085100142540c14402d105001d958800390001c5400101036002c0340c00d4a0610120310480680420200034003103114810301d00030181070408240030305c6812401465400201d4011342802000804110540b80030888903000d9083c6c0302c010031500403600701c0350b8070386030056030150001108030b81c1141c942d10780811184200c9a00500504c00f04c0e0300701a06641c0320306881c00f6180d0001008008a14203c528001092b0151f004038074040c204440b0001c00107408000700e50503070200c1c810300c400f1005202c402030301c5103805654000540da5100d6100100c2e80c6109848104006032500c40a10080003015009140928030803541011660745194502c003200c40ca05001a025900203019000410340b4036515402e0b500c8140341c80c60b807882c0c8a44500300d03004801091640300521080c8100140105640082c002d0910341500d82e152003d40d40004005020b020 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 770804703 1250 770803453 770803463
    0x40806060d02010c060203130c0510020a120203070218011e080a1b0902040306150510080f0406090b010608070306061409060d06030b04080304120c021003091401052a070203060103 79
    0x10001c007041d6030281d521000440c0d405101903580e450035190148881c1052541103510b80030510000c9018134003103440000701050365000302054003c60b159110000c217005075170001d60208221030b02c0581c1741c0301e8541030348501011900f01554036050803062006180000c030480300b5903114007404121008034080d0300b107603009190f050161085e5110000381030342640c061609a840040c00100300403441d000702848541d4071600b01081d50781c0381c007400000c01f0040b401c440000c0030200080c039402d42c41803040e9000380c003400002503500a2617484039400382003a0441360100d4114010403c105505000b9603018000a241c0440c0c007040141d4600260700030382c0e00c914130444000c28448541c00c1c650b44800011a04040840c4060400741003c03040c1c1e6005460a48084884501e81004903020308100014241e020300203641d01005148120010090070030120b581c0c0d00c88011080205000740500d5000b505840d401c050064541e0441c3d26001c412480d0001400b28140501c2d4050307900480c070941100d03084 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 770805953 1250 770804703 770804719
    0x90a1b050d1212020a030b030c1e01140906181e032d010f320f0705070b0702010e0d0e06030a0507050f0a08071b0203060403030b060d06120b060604080606 68
    0x6a14103440c0c200420f0803a4480300d10104a6054065154020300c2d03040c81c0070317410b4644407200c0109203c0a403540d212186408220001d001504d5449210b160231210002a1558240444000042e51650100d00722075481c1d0040c1c01c510310646030104d002d28020b4004030f4048882d0850700c0c0030940f81c40d2080f44038240310409031101248113074500c03604114055040001c000910400c01840f0081041120003d80001402104c018040a00e003000c41e0b403606808842d00c15580b218101341c6c400070000c040754100642400001c00003503074020b20702d001d4000b6030000710b503901000400d9441d01a040e40f056041012915540d412a01e42030201c94000ca041200880d59035a9a2070a0f00c0794410195440c2c0855400200140c0303069224107024004d0440741e890840c00403540d1740e80b03a1003070118a8003a5054202c607000c140068000d91220300310f0b040c05400b050414031601d500b10f04613852741c0c0c801d200f850b114150540c01c00001d4503166034056003c55681b42420f0410344100d6030390304000c24040c007e0341c4c4 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 770807203 1250 770805953 770805983
    0xa060b1c050a060e0c030106080106022b1101180b0603030702131505030d08010f150e1e120106180c1b050705041b09080d1d0402070b090a1b050d 64
    0x1d0358110310044c0c210708080d40c440d420529032000c00360b4024400e51001039684000400e1851001c82d13900c000101603101c0d55005510064240000501903443c01300f4422651040201e070794083c0580c02440c000075213450340c000c0f00350400d00e00324a0300801991103074104014400050b510b04003064501c0c2500f40001503900a82c4c141c10b1551502c0350402a414410306c0740b44402191721410550580310a190401300e06c0d5580c0720351102d680040c09240780881e11066a41c03038103040200700c03001d004517811031200240a035800400c148403400e014002031651170f00310600151151845d101c212500819041040400b2044000e08501c0d040580a400076115141041488000c100305070252400400400031540d82e8240543d40701c008003407890114504140000d802c2e1404101d00903030181e0f54584820350401200d06c03900c8032401c02c0c0016400b50382403080c600415440326175148114003d0740207014082d0241019910740b0715516040080320031881003030002c6e0311410110004a070380886017000d6042 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 770808453 1250 770807203 770807221
    0x7210c02030d0b0a24230a050a0212040b0703080c040e041202101407030c0206010521120d020a1205060604120218040c050f060310050d020a09020d050a060b1c05 71
    0x70b203584002040c0ea917880e410501214554580f4490b203102d61100d89049412490b9440c08010042d004c10707120105004da450f103a0700580003065801d8030741c415100c00c4455002c3c156456001034100d0780307548101141c9841095042107406800c140c0d0041c1040c2002d207890145080c0c40402000204070b102d540c00c0c1308030114001c2007920640980600c05200d620b20342030201214020031503550f800242045aa5003500d0700210b4140e0580e080a003003104000e0100708590f1a15103107040368003035403044038214460000080c0180011001c20300740035035071364013110004086074240301c2c13401c0c8654a0001840041e6a440003160200e84a000d42551040300700d00015010301c070382801802c0c00450540400c01002551032044041c3d0344101d81c50746c0400030140c2806924081103501a1408140c0101400036103005807804502c5840144130014540d1100201c43c00d070f03084214800d10715030700c610601c040340a981c0107100c090802c841d480340c01d1040b517840c0c00e4504500d00240c0302000c0d64a60200350051 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 770809703 1250 770808453 770808469
    0x14101706010323040602130e071d120724080106020a031206120b010503060112020f0d050c1201020307021c0e040b06090d0c170102120c0a03060e07210c02030d0b 71
    0xf040d1080c3e0105910302801d088002e98032a001054a80248200110300e40180500403400b44120b5540c4003c802c4c01c041e502c02d6400803804805500c468110901940720604118410151074030500c0070101390070030f800302c03844901c1041112051000e01070051003020341c0000e618404c0b60309442c0031a01a040d280000c0c000b020282c0000a0340241d00703200c68203004440b2002812241c0030b80494009070798820054074400803e800003940700d2083c16a014017460250003a01a09010380180c2c1e00b072908500004419850700400d81c01c1d680d401004021003990144003c104007100c03106980941c80c0e0400008110126000010b07110360f0307650242091039146d030810384403501d00180c03d248002c049414041e0700392840d441803c80c1326100700c4415144401c180255907507506020343c5444c29880e116915410740c0c000c1c2c0015400c0540d50000058685444001c980c0190110b895a01300c00d5205440603a01c11b4a4440e20400319040c000504d00c8a42e0000c2101d00368112540c00050001c0003000084400e = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 770810953 1250 770809703 770809751
    0x30a0908040e0a0c02060f06150d06091805060610090b1803010e0106050310111b1014040203060601170c090612041101080a0b060a050904090c141017060103 69
    0x42c1c21407008100f10720989500c80c2c1da200c01c4070f800300c51a550310001864a50442250310680003001c2826190100700d07028058200c20342d603103c0105000ba12280360508680da81d0b04c140c80c1c10454003480205220302409841e801510503903440b51003884415016140c9126481020029200040c204101003070f040d450108000008000f4820251407401179406070000c0d0060f070740309008802d00150820041c0c4030710a10801004019401c01c2c400000f80740d000040100000c1c518001c0c2072802c402031546100362420040c617812440e0360350030540145451b2000040030a4180188190600c41c68002e00300395a1380003980c20007560381e6072500c038040394440c01142080d81c401920320381800b00b00114031001c2d49140c00d00703a9034444140d650201c624162042c0c0e0000c0ca170400703c200a1070300030520800c010305074100c0143c004545c54400b540c1315084140590300c4217040f000300800150241c60b00d0061001001d0840c07500000000700610302c0002610050f20603410325584105040031460281e0b10380d441 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 770812203 1250 770810953 770810969
    0x106080f07111f2d050c1309050a0605010f020a110a030b09030a08100b0403300e01080603070302030618011104060f120c080a09021903060905060a050903030a090804 73
    0x30480c0481d0060b050345104058609265060800d1091800c51000700c42828503a002c1d0007020480076a200c8000404024028061b0b500c0b04200c280807041c046201c40c03009000b5004001418904483c100040b10200e800c114100401e0312802c0c02c501d940050803401140d04103201c3c10011050318001019515941d000810146080302000042784c4007001401c003003072840d1507010b543c0e035603149041c2e840303220b50144000d609000d00043c4080b43c84004105c02400b030741d00c0c0c00555200040e10000076040c0072100d036800507000e102800e00c1075a00400042c6c1160050740280b41032411540025144c490007010b00a920704d15405601428200750840f20100c075031040c40960359500da1100400030380d9002e01c02c1c000b090a422103920451803d2064464414059880364020348504080c54054210110705a90200700d64003110300e182140318400009511905002030903250a240c66410a80010305200c03005103010104101c2c032002104aa0b13014901c44070000740300c045482d04001c41e024903082189 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 770813453 1250 770812203 770812213
    0x30f0a1d060a0b0105070f0b1308042312030708070203030706181a190b01121109040509070305120310091802130608100c0905060d0b180106080f0711 66
    0x103080101060540c080d402041c410300c54050014015640c61003a56401015800583c1250780400c400104640c0c002440e500c003c51460807039250200b907908141c002c48203000f03c828403015046400721844111520a0340c46524441d1109034541d2030340a20384002d0250780002071840215a01401100c0f10640d01540401402005007000070b08059242c4003100da100e1030500c0940c09216070b03101c4a20440b0075543c0030080c074040c1404100503002d07280d02c29044c80240303880c2111f0003090340034065480c0d4a08810a0322a90341d0070411040c3e46025180040a802018007440428404903602a141105882d0a0741e25103500c6255428100c0590001c81d00c14541002d8051a07a074002da034254041c001c4801c04170305089081c0100c1211941d1060566652200c88001e40760010758204030700c128190300380480320b40e6440010580603030041d03800c0411a9650440346403945000303004040404c0040d442c00001e9818010302600c0c844020300b1000e1103610080004491071302c03e880092100610005443c = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 770814703 1250 770813453 770813501
    0xf0c0602091305160e090a0b06070204060603020316091415040e160311130611210d0e0d08010e060a030501020a020d020d1107030204020310050d0804080c06040506030f0a 75
    0xc0b005100a4400710011803114800a0b106445210044036640300182460521b85600f6040c1c1c0c018104540b034240c00007001d01c0030402503900d51003a40000c01490301c0160b034a1605491441040c072018900009208182c0e40500002030401c40001208205480007002c01008504c14a450700495009900130005042005a4400078413040329600072640c40500c20401104480002c50250f803005030b20888085c0410007426125042c140518407018090b1082000741c0c1400415200414406004180c00000d201404450600c07901a4001c3c130300015080c04410118000c042c2c0c00188a1701800980b81004100142d8a00810b04002c6900900840d40e54101c1c107000307500c2d2006031140c2d0015018000300403c1ca180100c401c403485a590b20083c0c002d660641d0b003044020f400c060030241c400103100001188a80750a00d0100c0402d000d00c102e039496510f8000c1142c507021070300110500a8609220802c900d44694003500c0e04800c1c0c007903c0c1841596120156801055030208192010002000c08 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 770815953 1250 770814703 770814739
    0xc0903030c03091509092a070b150d05100c26041403182215090606031413020d060510090506030304050907051e0a0329010f0c060209 59
    0x2814043c10035a1440596820310f5403072401d600174218003c0d00f102c5014001050a92201c120220f004000e041c40d26a4a80f0b4800d00e03155030700014000c40d08240c1300f03001d0210040b5018020304804008071580a441030041d6510341d00c0d110310f403100310319103a1181c154200c0d05000ba1a4004041494800308000d208200d100d803c144038241c0c2c058440f03502c8100389101c2c840340031089038030072400d80030b81024100c2d02c0803e0112246240304611464146414002d00c1d040b140d00a4403080b1032441301d540030860234868481d00b150601d074840024580340c416a07494144084210a074020b02e00700c403455941e1520300101d40546040d0200522a9103040200b001c081700c0c8040880aa403203201041029031b4848062658911031401450382c402c0c40040001c038802d00c1000207080041c42000d0404a2148610207541e603900301d105000c02007500d4030f29401c43d144c03041a1482c88a452602d6001500c805000042c040342080701926007005040c2540d5020311104d0780455049100280540e48400d0000c90a = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 770817203 1250 770815953 770815957
    0x9100302090103050604060b041e05090112021906080f0601050d050906090d020708070308090d0c0b0715180b070908100c08070c350a030f0501050109030503120c0903030c03 76
    0x2041d40804c3c9840701180d4107042c0751048100350b4522002503803400b81003a03105038040301031031440107110600c03420104a588a24102c03500a05260f0001c0302040781a2040290b0030423a010424552550030500308441c80e403014031290800005100442183c9415004842901c640e90034001100d0500c018405003980020309188210310600a4a08046018a00700d803186d42c14170641d0810381c0100010b00104410384010607440d9001000f106081c699079640007581d0206601000c1000380100b4040c0900002c89100d041301e040d03210003040702000c415005040c00606003070241c0f12540940000e000c85016071340a1010f8a081000c4500c0c0000000d41d65000e030400360543d0b0300203003040c4013150b2040d0050030030240c481d6210704515041400849152445900603d03400241c05802140d903680d11384070001044a41c42964012540e2142181503805489060384000c0c10802001010804030300d01006680502034040600c080075150242c0001581c090004075581c58040025180c00e18240000 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 770818453 1250 770817203 770817217
    0x9060c0705032416021f090c0504020a0503070809010204050d0b10150f0c0203010b04090f0b0108071a1b07080a0b010b040b04050d0609063909030b07020309100302 72
    0x800c56201c00c803c07801e81103a40001211080c1c1044040001c00c0d4500024015082105250301c1101c80964880040340803001c140b0406483c1c1d2903603026100240105c4280c4071020345401c0e501545070543c4942c0050035403000400c0c81040080c54008201418802e404860048c500105400840c08031030500c03044001c4203617403000301a100e0b05400914484419507051420502d921884098842180159074044407000105e0745556203c0800040d5601c86c495111990301400b1409e130000580d00d0002c217000c6043c1c0000465a0103010100440b0f01e030b2044038080d00310401c444039250900410390311110b01c0c540000341340d1401045404148072100140035081c00c0d01510600c91a80d07607070070490407507101314010590b00c0300301000b041c842400d06a4501c00c00ca071044400140764012a1140f10440b040c101c6440944041c00f030345071000c05040c1514030402a01c214400920514010010b46150090f120042010180600085009000b40b05581440d0340141262504c1841048010000d500082c = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 770819703 1250 770818453 770818459
    0xd0e06060913080a09030c0b040302040f11030c0c030405041d06010e09120a0e040f020a09050306060d1101090905130303055a07080f0405030a0c0809060c0705 70
    0x10005030140c41c0c4004054020140c1d82d00160060507151038020050740310800103002e00542c0c000c00800a480e600601e4024100c2140703040c1c0f181d05601c1000306030703106225a24a003504041891a8041150742142c0d008010903440c95a00c0c85091101030960181c1c2c0d11595015140141881480c180281035002004224090714096a01e03a498201c2040055a203c1169840714170440b0701542074000821141d000f5081260405040d04000303001d4405648010340519004500120780c0798012030b1600113401d084000e00028500302c40410044485400b000c2e0410b034500903c0e075200d074050748441000d0007144205200610f01b1510b52440d4201c16001200001d00e09000500100039591f46000350074000d904682d00c03944c5220700c4c014880780d6904010f411100304100c0c0f000146040d045410346a160400c4021145880e8074080c0000700002c0140310381080e403074100000103001104550300380120741404082e481490501c000e85010b215110b075001600060074900f2100b0006a00084902c12 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 770820953 1250 770819703 770819713
    0x9150c01140f1303050a0903021906020d0f05072604120210030c0f0e400b03101a060d0218060910110307080a09080f03180913080d0e 59
    0x46110b1006a280c00c40f140720100400c503041000082c458402001212150714003500e440c2e86a8000884040da03001c42284d415441510402c070454050080d041c0700700340c600300100350a501f40b0020f00713035208552006145001041e00c0003445000d0907060b00486d0402e52440d902e90741c8800c440ca4403054050000d0344200505d00b59074240b18071a00414051004642e20900a600200c501380c5000c01840d100c00d601c0b124681c0441901142c43c10b005e10385882800210601c1a0030300c5101c038501c000203400e400c0c180e080820400d80f80e00e00140042d141980c1d8040090852889211082440c0305020420383c03110000499511410040e000b8140084a405100050005a5040080303c0c807540c0c07105600a0f000c0000d00401074040c00310035140460080a407844c0400594504d4181d500800304140030840880091000d5003041201400d0302d0708501c0114034007136020b0304840200c440441540c0c4035469640006030b0820745030142c0444117902c100c680f82c4030480d079042440604a665a505468800c0f = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 770822203 1250 770820953 770820961
    0x913050312190b0a0e040f06050a0b09090d140c0f10060602251403010e06100e010e09070330260411100212040e070e032109150c0114 59
    0x2482240d00800f401440c3c0100c1c02d140461102c560031008000752407001000445402080d1117010300f600c0b41d03556890000303040044104104440202501c2d03403941d584085144011036410820800b140301c0344910700e9858494414940d4030b170801154520070035002c0c40c29004848103542e0095010b031040c907001da9286003680b181c2c0a1302090742140c60454100e2840b0f003003048004040354005074030009800864102c2c00c00825502e40700050360392241d01c4401c420100815882401c82c680074180202030880b050801d201a6036490660307010250000528100280c4107455442c000c1d50316102014540c081a411010040c1103c406e40d640400b09407944106860b4060103480c0481c0b0442e40b00c1c2c08061195054000d01c1126080503260b1010340c071a20355000b4400c1040c4c405080205841d8482a92500e000140207145d4030742501014020b40c0400d200c00803d15030300310030b074140c401c040c4105900e0380310705800281600ca1861351490000e00014000c0c00001064104521082203400800d41c181c0b1 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 770823453 1250 770822203 770822251
    0x1e03130b06311a0904081b030714070815060405061f1d010e01090b07030504030803040b0a0b2b03090f290f040303050d0f020301060807031b020c0913050312 69
    0x28681e10f0207038408120300025000900c07840152900b4440c1221444544210302809440c5500c012000d461000c1d46200001164034100124006402c001020701000c03020040b0710900b4038005056175106644505c00140251034581c18540a00804108172400c410103240c0a043d5406a4800c280981e010060820040d409032035821f080d206c0c1039482c1c4050616003155241e207600201070072003c1240030000000420141000303140520302030584422142004400c8074200c1e480c81c03040c0f0b4022003124001c1c1d135224220000070061507140d000ca1440d1604185400c039100c0e070054000d10900c2a0544011598102c200d2520260007442201c036402e00311500f40e40d0344a8050803080c2c40e0445004c02c01440020b205d00041d24818075500e44c04500105004c80380800d03a0826008000080c9105080000a561500802180c540c50038105464204d51040094407190010032050050200c48003152400b6850380305040000d822205031307525010361038006aa80031040d00c5604008070601d040c40c0140c0 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 770824703 1250 770823453 770823491
    0x90507080609070504030f060e01020a180905190b011710170601050303031906030618053c10090302060105190e01170c151e03130b0631 60
    0x102030b40f561820725240d030340d4144801c0d050764811030b9580d4858800c9c0c0c501c20702c24005029124640e4a0f440c2000b80d03404a580b0510080764410014241818103001100604100c91040400030410115041415900584000541c680e80e01da105541c0000c0004043c1c4007021001502e00035155091402110150b45a8138402801001d91540082010801d108141d040000c2880145800803510b5980c80c3c450100b2244943c4203403c1d4908166144000c20500b40010f0072039031340c04020035420726941202e0320850745110103034104200f40002c83c003680400801c0451441400414184003000e850f2800940b9042c0c2880350b140503400c4031203015400c1004500f14404d41d00100c0510510342c0c40d01d42c0c00c2d0304641c808a0000140d0149880f00c1d48144c03508008100c84503030030050a555000192050b80d114620750022101e0320a050040c80791350040b10444d03040150704000100e2154881070005440710b48035400795046100404100720940c405008a48000e4500c20401c0080c21110010f8201c04 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 770825953 1250 770824703 770824711
    0x6020307020609010e1c0305070308060111100e0106030209010b0c060924040212150f0618010308031b0711090a09230304090c02010204090b01020c0310050a1104090507080609 77
    0x100506100310f5000c4c0d44144046038190380300800c50f4064001041281544034035688065000070b5000508105068010990f290801c40a1803c20301407542e400314640c8421110710070300303010b684800c60f410300c0b24400d4001201035500103269074143d5a5800e01d00d00f9640c840c004c1c2040e2405240009119420081100703042e02c89a068441050202409401442c050080c41264010101d8000e104002020030049804480c2c1001c200b5107414290401d14a10800521403407080600901402c0300103001280203044030f9014211640b0313615040303006c8025502d4410f0b14400542c1c00300340c40341406182131500101c0c1d1415100d130304c2c4030f0715040114401c3c2c441c04070014140d140d5807140c1c0704800980e108001c54580044041d00e023005c1c1c580c41801c00781c450344004080140c0d00032900f407005407030500c5544408182400280101c0c0c4c0c2000110752202c0f115403102406541d10300000c1c0e101405901b141d00e150300f41035985aa070f0b549904c4103200415040d607914000501c504001001410281021400707 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 770827203 1250 770825953 770825959
    0x7090507080115051c0b011e0c03050c101b0909020f090f040f060807030c0e040c0b0d0209030a08210105150c0c031207140c060315030a0c0608100602030702 69
    0x1c81e0300b01120703070f602c8003080410041040340420420120700a444034a042016101c03001140100d4141c0c00101442d111250381440c410b030f80340c08402a103421046c49a86158541419a00c0c1c5280c9444542001e25140c8201120b03410108450802ca2208400c006025460380310707070107041d4444000f001240100208548160380410200c0030b2460201080c10f15640010030219040303031090081019180c855201d43c800da03010b0003050081101109052002d40028501584503282c1902c4403400000544203040704000300042d00712441542d60100d881700ba10240494035030840134900794205a101070f450010301080c0f0968240388503a403803130450403500c0c02009100300010507a208c0382c0302e5000c482c080c1150300c11501c110400f031718240203600c0303840d181d5800035454206505010444c002003d403030080342d80140303041c14400d42c2c0301c20540383c012525030700091280c241240800d01d4101c13004400342140d000c900c0000360ac241e01481441c45480c00c000491410f60765132005036500e00441c0c200031340c = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 770828453 1250 770827203 770827217
    0xc0d020c03070303120213092315040e0a05070807090b0105070b010510050c010615110313031b031b08160806010308220303080f0609090a0b09010b0a08030c07090507 73
    0x80381c0b054100c5c0c40040a036102c014a006c1001000400200c4203a000d044480d8641c102900c4460f41e0f075805400ca80c4d10345422400030f2510325400240c42141c2c4031218030a981e150001203600d01e00b0420b03500003551202c102c60b02c0c151104002d0b681c038801c03403140500b401d04204114101d5482002500e41d1541d0002c4980c169908003000c0081c0c00318520352006c100003051080c4400351009005810041200741c243c400107203d800001000204500d07601d60035540100214903c803c4503242c110100c1781c000f40000b482401c00203014440141960020b04140011011b868038200b490640c00308603180b1900b01c540362904c10059840618491044800c15000107004101148400c4000e0154402c0c40101d4194260b07080307918444040f60381c00035030004d10a042003143d907040c1b40d40001e4201b00c003100c0400f00c900c0c04500c2c103607a030404a50002c00d803090b030101088004009411640500d2002401400380a84824440303980780c0001d0015402e503c1100070020f5070032a41e00c82c442c0141c1d500e5031548 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 770829703 1250 770828453 770828459
    0x813060f05071103010f060b0d0506122e020d0b0a05010816180e070c14010209061801202b02190c1d0915010b1602120d050c0d020c0307 60
    0x10030003115030f00c3d659003554903503c83d104109024840c0001501da0010103684079404098043d0484600a0000f030003242041030003064040300003030800c402c0e84d6042c5208050100104032211aa12100e05001c40d04d00115103401c0d814001c0d0003005403041c041d5103110a0396510310045450346010344007142d0044803440030307100e22031044802c032099035011030142030f040c0d903104110004680b040316404005260340414500300445098090f4144603144005d506014401000030800e03c91403500d944a99070244c000c041c9a4003074060709080b02c4140030320403a06407800f14100c0d2503c03035106411500c0051003640f60042c031400c3c25682c2c600403455000780070f14007640074001e420903d550810b9074549a11403001940c1e82803000c10300074500042d542c0e101e841c01c09000b4640703000e00481030148420420310042c03094660400036181041f10405c00c50810304550b0001c11810a18001e0412440c080c0d400d1f03180c50650000001c1c00140c0100c0c0c2101c04c58131800300d0885c1c540c0240d404050341500700306010 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 770830953 1250 770829703 770829713
    0x507080114060405152a0d050a030b130501050301140906130218090c120a0215030a0212042111031c1b0e0a121a04080702030a0813060f0507 62
    0x555046840680a545801c3c1c4442c0020512213164041c1840e000000841c03841c2d001124501c18401c8601d603e41c001b0b40b2001c14481c54440d100344610b20b08216010030110b0f420361107508190b4004901500c40e10825000b180c0c840c01038042405854003030346c2040c403100d0051241c01401c1e440f031590000a0440740c0c981120b1040c5881c26210140d0303000010f102e01c1e0003c4520002143e0048031004000d150148895081c02002c80c1130b04074031036a90f0803003018040903031510301e081130305082c4850103981d8a030b4807005080024043d40d50100440c1d00c8842c200b004111490609401d0000d0010450b041b48039407100444413000400d40c007542541050080e14440140040d038500b01010300c030008241e415000c0b40d08980d40306d4220600000510f180d40c2e581640c181a8600c4001d402c2c41014401140c0b002e8603021036210010200181d280d044100090034001200141c0d6400c540c01000e80d01e0380361490510b1170300ca8002c50b0030080c44c800c005800080c018050240f40002a40a40314181040301e281c680e = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 770832203 1250 770830953 770830979
    0x60c070206040909061d0a11100206070807020f010903022a01050711030c220f060f0302011b05151e041a0901091b060e0301060f051201020403060906060503060a05070801 75
    0x108884054881008a0b40d0201d038646c007000115008005020724020790400303800948001c0b1020303000e442c03803c83c0b0704081907003c40c40c590b020300e090400c4101500d40040891402a4408042c0c0d07465103400f8581c802c00d0740c040381d20700904507205000c0341a80d040000f5925000c09041203240420300c10415903000610b141c404145504004050b03e90702e00004000c1035403022500f8040c2111140d0405400425001d481141c41c25070304c03400304011007810600034201a040318000031703040c01b00d202c00601d011320f00c141280103240e50082c10349421440480000b88191703003e40c1c6089451528100710300460b61102c020901c901d401c001c00c0c41d4283d020072407400c40d8010260141c000c035502c1e09030010201304101081c0c0100450300e60b00c21000c9180170380003002c0350710003a002031080c1d0400d00c0401400b1403210455042e180201c2d100c0441c65100b045d024020311131644000c20250406c08100180010365005400300c400c25002e4508a0f0755445000c0c0442d0350480d07055001c14582801032044c0150414 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 770833453 1250 770832203 770832221
    0xa081e040f0f150501180c08071419030c020d02012c101103160e280e040f0b010509240103091a06030f120403030e010318030c0302060c0702060409 65
    0xb0b107851011100d849504142600007603441c019512040104940c0001202c0120040100c110400c58540e00040c0200240800341030402004415000c540030307102010115840750000c04040907a03103c441d84003801400f000f59901002d40101d8a41050180c018041c11540040112051400c0702c07524000380c40c12000001c1098071441240c42405440601344100c0138203142d10300c1015141e02d0081134800341c1e02491002c0c201040300484944440d078840e114071040381d240b6030340e503080051000300c501007070110583e0081000403400c009000074041c110521503080d900500074405183c1e00c0f1400d0190a00c401c1c2c0b00c062038007445003103011014a91044407586040140350100300e81440e500ea01c0d00d00781c1403050030301078000d120013409114901004060048100d54025081180300c0780140d4600c4d018910002d42440000a11442e00743c0c813a03800a908155200c460344494165420020922585040308501500c43c040114504802400698074110350040c811480d01381018200707030141520354 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 770834703 1250 770833453 770833463
    0x10321050f0d020f0a171b090d020609091e0f0f060f06090a030b0901150602030a05031312030f0605060f0d0f090206030115021209281a0a081e040f 65
    0xc044d0840c0d04100c1401005801c203203555603048003a00036400d003070589000d4408180541c0c0106610010141d05081d50051041101c507450310004600118000b84502940103600074012410000d0040c0c0301044403000001c842c00c0700c5040c1e640d01011009148041d40c0f8500100045400199540b44c45801d9600a0b6800b405150400f180840890b0a1a80326001202c8624a0004026041d403003442003010b068050701080c24558540507000e5100d100b40311060081100001c0060103031405c003240c603e42161311401035503580d144d0201c010001d00319016540002c608100f000582c601e8141f040c1d4058903c460840703464490303150384400007414415004c010a5480c1c81d25140580c0d5081c0240d802400302c0c4440d2410b916031480c00909000307928440111504090010140780e4a4000d071004003000d0a10461680300c54298642200c2441c1e42c0c003100e0540489440010303401c6d00c2c00d01030041001c103500c0b0842d403622503d48403076041680082000035405a1000600070402240312000a10300071 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 770835953 1250 770834703 770834707
    0xf040c0308130501030b091e040c080a060209091503070b0714070807180501061d1c080a0905010504120b13050703030c02130e120c15010e010321050f0d02 68
    0x1e40d01ca801d99000440c0d058480c440c110300400c95940c05000d0a070040208803295000e070302d0500c0400783c48030310584802c060459180c00180c03c0200d2011510007034408041220009140c3c2d291482c041d50002a45034001e0b4540b0300031070200d4001c001c0c0a032644200901800a02d42040c030381c01980d8200c0141661183d01440325901c24280500112026040040190100303e06014200d0243c9c0b80301c0481c154001d00e86001042150352188012561900700203030000e4141862001800708100e458000440a0042c25004104079188009000c0c00002e6111288000da4072001968a07006901c100300c44040c01010403000500c40300b02041e441346240351001c2805a0b540ca0b03d61034600a500700b280402d20640d0303c501940b904030284140c1c0c01c1c440f1000cbc06401e03560b0282545600994140007140c402c0490a000000c1c000d1060501004058480420f20340c1c1d181d00d8074100c00c0c800e20041d10701c0e020402507a50700100d02c00c826000795480740c5901e0300d0030111450542890b84040c1d00001c1050342 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 770837203 1250 770835953 770835959
    0x409020a06050d1d03030106112a12030d15080705090a02091f02010e0106050a080a0b060303040504090c1a130e0709170d1e020a0b04300311030f0f040c 67
    0x14000032001c04d0080040110307201d40c1001c0c0701426140300650f40d0301c00c65120030362506a200e8404050400d903021903440046621444c0e0128900648101c0b2002143c040400c611981c26010381c00520b40c10b002c10921000640e540c03080e00d48881c0e4500906030450007400009850156540003072204035006041e0607194080416a801d072488900c0b44100140d45172840044861401d01500c80a0501150803000c224a002d18890340c420301d1100080c006504000002da01d95000e1081d07034000c1270080c0091220066a140280706030045010311700035012000701200b44250803070180c1d2561000050240400d41c02d041900c102c01a00904000030400320500204100c05c2d1403032100d2a0412000007003202020031a0054454030700d4000701c103280c8a0031f220101d03085500094031120b06170481e03110707a4151103d061030147c26941d525504d0300e403102e44400c0508071030380e50044c810ba581d85581c104075045008000e091180b01c07e449101040300740a02113010703e10390440e0260090712850341c82c640250307 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 770838453 1250 770837203 770837231
    0xe010507021e031e040e070f091d041b1707051c0c0b0c070504183e13060b0301050a0e0108030306120c1e0112050f0109090f060203010b090109050409020a06050d 71
    0x101c2110908009480102e1000345603410210900151086003510ba0ae1441c0d1146105180400204050304903c2c2a58010108460401101026081c0101901780c1c0d10000e408a5642d20750600c1002d020f484580316200c0c030b00c46c0c00310340c0a0103268410418440d06152031000b446075001030141403c140030345540050310b59110701c42c80c6905508803d899058111508011036020611480600d500200440c4003414100550300e01c44420445840714031050008000300d1501e0031892040040c0529094004c545a403004000d14100c5004442d50f825042d210503015581807001c0c030444400fa441070020450a00c0c11080002d0b031100650103c0c1c082005400001d4110058620070f00800b20f181d0030740010713075644000c01b0440610000820301150402c2002d4107a0f0034014850840aa507441000d1010031408860040d0b01c2a0010000c0d900c03941c45022005e0590300c0202c8142c082142248002401e06182c000c031340209400614105c1880c0c5420402c2e51150f1144d0640d10703031142c0e521510a80c0c08 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 770839703 1250 770838453 770838479
    0x70303030e24040210050903122d0c070503071a0319020712110d0215060324150a150804030e1201020304051603120e0109090e010507021e031e04 64
    0x70300c080e0182d824a0038540188012000c8520580c810400100003410f40c0f1b8500203030086504124044140d510f00089a030792075031030744101c400c0404d408481e0b03d0743c40da400b0b0400a00b032640a0481942d510941d580e042640c0e5540b03c1c400d0544500c20300001350000c0c000070000e03581c0300c2d21071060040c0a17030060180b40120303405004100c4080c0200da00a614450703000080c0d205003028007000b0030702c5a42002e0040e555120146840c80e00b441140e000802c1ca0310180070940516010109030392a18044645c0d9051052045035200c00c016802405003000b031900c00700d040c00b01c441410f0540d61108140004441d90080207000750306000101c5c902c0d2032070f40c039580c0100409501d078070700050700c80c2070a00d802410302c2e0000c00800781c3c10039100b1003400801c1420b02d1600718080a0b0a1a160395022000141e810b5034880d0702c030038103030740c90244c01140ba00c0c01034000074405e01d12076003511405030000052440713520300c1b0513011080741e005000a03a808550200707500b0320f401c004513410b810302e595807150014213 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 770840953 1250 770839703 770839753
    0x15020d09050d02060c090402071e0b0a05061c140c152703070501050d090218151207120201030209030307120809030304020f04020f09030a1112030c070303030e 70
    0x209584080180501c5400d000b90114415035201412417030410401c4d1841ea400741c40c006030f21039980062480c0820400c1d0b90440d10036025034141002c0d9070014144003d001c141200c5001302d05040c040001c0d500d02c0c0c07081441003104000d1700e64005200c401d4885042c0f420682c07210b4007584c46101d506c00b2482d61030700030820800041c80da900d5960314101c801075100f400c610440404085020703500a4440e540803a0320b40a940c428038100b0f0720354140048402c0a8204900065048602070314010fa1114100d54600c0c42058001003031440b090300c1c0f1060204400d2000c07440c1d04a03402228007440a0010f174854105500d00514026081084480010b0300355071001a00b201c100c41e02c0910701030190f402c00070b220f6101216801542c154034003500411104100181254891036001503481c003800c2a00c4d0a64000001c090215481c0400910701048800c0702050105d103d402007002100c0402000030454161041c5080a4030500386140c0c0e00303070017911207094280c226002e0020481c0038004001e40500304 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 770842203 1250 770840953 770840977
    0x1b081009030c11210f010f09110105070c09111206060702010e01030c09180e1e0c040504150f09020316350d050d0f050108060f0919050a110a0f0308071502 68
    0x194021000b81404c6800350008070560b10f050030790354008a80070001d083c1c9c10f0542820441e50b605110702c0c1401c0c03010f070660002d1003694540021000c070504008007034444e400c1c10302820222522074404014407400307801d20007800070354903500824080d4444e410020706501070b07060082c01152100448600d0810ba0300060720707515901c800362031100b141002454120364040100c4070440346042c4e0b03040d0f00c130300500c41520b000e1502c07a030201c0d0030040550b4003042c1070701c01c100080041015015516020303110800e4268031034442d942c0f998049640b140b0260080310401c0e1150101c0303c40ba003200200705000b00c2c1c031501408194056003120b021061003100c803141d450360381312540d41803092441811501d2000200c4a024a84401403042100c00038a95030045403c0d43c21102d681c0e908541c482c60305507a10070b5461903904400700b24040240004201c05c0780792080c0180d1081481c0c13102803011000b003510402c0c8901c84a10020401b058900e0020010a4000c0b0742d2100600101d00801f4160391249030b003601 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 770843453 1250 770842203 770842213
    0x605030c03420a06080606030c0f090a06020c03011103100501030b0409060914060a0615081005040f2a1421150414060604050609010306031b081009030c1121 69
    0x40d1483e20807021005401c0354103140110b0b0522031301144103408004e08240182200080802d403400d00c8105444403428001d0402101c1504d0390300003034444424048250296007080304d24030031601c0b003078284d910a01182d943e2088040c0380c040110060003140b48119001540c2c1d5003e40c0104010780649002036004003401d01c001c1265014040c500f2100506004c1c03100c1c540081030100500c0e03001c4112200101d464140c0c007545a600e4000d100c07440710783c8501c2e80240741c44103991000b181608448908212015401b030340e814003501240d21102410110400111026903560326041200e015000ba000030300703181c05074150907030041040610159481841c03450710200c03003c083e14160007880d407102c140400e241e481d07051103404180749004a02510b4450100403640c1927240e4070030390007a001560800c1d222009140752980e202c038418a02d008098290041001c000082203540c01802c91540d815600c0d01c4041200d80c40703010a000000040c254007400700100105803046601c8110000094100a05 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 770844703 1250 770843453 770843581
    0x230220305280305090d020111010e010e0c010212400e0601051611010201150b0304110a180f0609020a021606020d020a020d170307090801060605030c03 67
    0x200c002001d582d0140482e000c003003070000e80e1100603580c902c0025103d4039200c404c548010790320000c081004e507482c0d41c6800450790f50024150044000508020291207002006100484c5c0392001c0c10741c1f1841411040108449405100e107075400503804190b1518401c5112103682610b00d1640e86102c610841229010b101903084042d000760880c0c001d00f4a2880c10020203103424070300c2140f840180c8003110401e406400c0c0e074000e41220305c0240824984030f581c9900c603032002009401c01e4400b6904000c0f42c0344000f0090502520400a40f0704802070410500055441d10703025107042e80c0084011516080e0004030407806001420540480b6009401d84082d010741c1e00f041000c15900c4601194041b14450603465008180c44c50b0796034040e038901c0402070075820710440d215000c0c0d225a05007a800020440800c0c1c0c801100d00907524010028002c5698440c2c0031100f600041c1c5004600c0c3c1c8080010400c12242c410b0202040c920a16801403045030303c1400040580c5403514544191101c54484 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 770845953 1250 770844703 770844733
    0x41b1d1f0c0507120b040f0524150d03050f130504050a0c031523120f03070b0a0506010f0f1110241d0a060b190230220305 54
    0x4400340490980d0134000e440b040d00c9110300410040d1014100c2d4035003028003030601c10241b0006074070f91131040300c80280000c46958905107a2045442c1c4030828a94a0711459a207000c01086806039015a10319080c4402840241000d50100c1000705c14000c1c580d10005064941d8041e1503c40c5105440014034420b1200014068645242e860200c90f246114103000c01d5240440c030078255152030040807042080d1345c0119640d8816a5002c0c3c0e01c9100d4450f4600740400000012704d4150720816000c4081e4840008000c1501c20aa0760940881d80e1090107199461041d00d030780c10050700c686880070b42c0d211414201401d001c4503405040e840d03a140c41c1608203c0118004249559141c2c04005800a160166440c002004011404c00100c0d41d580820010080798008101030308140540c01e41d10b08034090354603030b5032044084c89800b40c0925981d001009602d03032224006c8941c41841d1800d10900504115016480b402203104000100070211700e451102c46980d001035846040144040d03e014806 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 770847203 1250 770845953 770845963
    0x7031e12050405281503020403050601030804060f020c10051620180402090606091f08040b0f040201090b0d0f05090106080f070f05100c05011406041b1d1f0c05 70
    0xf0526025080301c00d04c0300480745420804541c0d140f0301807401e156400a048001e4070495001030654810400040b0078850780390020002c848007501c07500b0318a5104402661125000c05c4070580c000700f0390f000540003500600007001980109510130010704405c2e640c03609440301c003041c240401c008001b9500c0c4181002e080c5407040d410f00303142e003400350f11b4290b0020b80950760003001c450080c2c40218400d5040d0311000529010111030b07180310400300c41c0c00100180004400c031016a4885886030100e03800001c071851241c011a0103235102da003241d042134003c0301b40364000c070414100070703649400885010340540320310b0f030050600d0340010491030714140d85a403600811150016150b0800f501c2080244107c803182c2c001c0302c5041d0354a0828100d110010346440c0300220300034009509201040303c02c070309050200d0b4032440045808110884072070081c0546070307004102c000041003200714400c03209410300760100d0362039100500301c90140c4240709101c42004000100c003030121342d0003006641001000c1c84 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 770848453 1250 770847203 770847229
    0x3020601050a0f2418090b211005041416080115060906121b050d0c0311090402070203010608031303060b0f010509120a06180605060405040507031e12050405 69
    0x31081c040e81003a03101c1c086891020b0380103400029549040c003041d03000d003850103030f100c11540691514031b90f40c03646207020b0038424065605c80c8400402a01400100012100300c9145050040c83c0d18584551104001e200242040d40d0300c45040b0081d040d466405c0104104d5072000c1d800101036039280100b140c1c25500c4000780500c609181040030300519500504d031000316041071030101c00d4072240f0f240040c01082c608007004000003c80d00070032005c42d0404014051001007140400007030a030044100e0440c2c01d1182900e020307103410810a9801c0c0781375009480d000c0e000a000143d050765810003d031035035102840c84000c580c3c14120400c01d201d038620800c4d401320000e4440d85908103030000020030f40c1c4614038045200d440f440700c0d50004100200302140030143e11500800400c3c1c00c0c0d01c03c3c8101446401e01c100c80c03071f13800d081c0003507101d0425024541c0038540c49001001d884d419607490700001c0007034107408510b0381c040e03802000c00300748214480c100340c480603122180c0e21401c22050080100d4688 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 770849703 1250 770848453 770848469
    0x30f2a030b0c03010e04080d02070503041725051e120105041203050405030909150d03020f2401030b0601020f030310050a0501020c030d0e04020d1104050316140108070c0b0403020601050a 82
    0x1000400030b005c0306000d0360b540f0036486200030740d81e01030907003101e00280100070010b041c51202040c08158103480040d103200c4845018215500300306d414840540d001d40b9182c81442c8441040c0d02080582081c1c60f548103100400c01100250305208004124826091181e14040741e446200303000c1484041c0707404885a030b5561409100910706620ac00d40d680c03003005000c40c050303100c0d0b100007501e8451480c4c44031103261000f04511120f14150400968980e40040b40715007a004000b60300082000c00e4444521000c220008600705a1a5840d8081140b00042c0000d041d07000f010810b0a4000c030600c001e41c483d0200070804000107040000f809403c44403504840d0540d03101403860045a41d002941036110202880c250b4070210745030001c64041c1c019600c44500990900315180c00c9010b0700405001aa4026803c95038044819034100400341014450000aa0042e170740005c455481580120b0b030045042c02c1603030480d030700796850910104e0212800e400507088880144818a068070804008110314 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 770850953 1250 770849703 770849707
    0x120e0111032e06050313080c0f0604050714031b010201020408070609031a07080a0507030b0604090e06070c03200a08030a02180105090627030604151104030b01030f2a030b0c 76
    0x348041c04e148006808409401540048032007002901c008458141c000b280540303914208960b822581c0302011340f412a00760080f190040b40c00d61003c22071f1600e40f8001002050800303000d203a6807010400501103141195002c01001ca404076040000307400030135503692a80c003480d1450801c0c91025803a41085421640160240042e843c0c1c84001740e60030000c0c8080008003a16602002e60041603142d94440d000400803130300041c080040c1d44199150100d41c0709a400954448608460f200c8d1b22400c0100070407064904e00030f020501180341d110b045404412619443d40766103403400746800c2100c9104000e030f00001c1c0c2c0c5803401d2100903241d003407180c01c0c244142099208000100e02c0e001e0900c3c0f6181d10b4a411950203c0c4125100b032083c3c03404800340c00e076802070900d070805d4040440c03503180ca80941c609000c00ea50112000d00200d41c200e940004030080c0c60390941da40c44c0c81114144a0990700303030000c1d4000719903d60007000c80800d40e2000da80351001c11481c6181003111600010000c031001c00003 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 770852203 1250 770850953 770850959
    0x120b0906010e01120605130c17090703080d0b030613110405010e0a09020a0513020304051c02060a480305060612190207050d0909050403120e0111032e 66
    0x400340800c56110b0908000340d440020005400c010b04669200952000e0180b00707002d0010610b6012685c1701c5813541d00c1801e4082e40e00f00950440005580e00743c46a88060001c10210300d401019000c03803800031402252114922000078580070007a9107425440c541140c22034104003030700707002c1c8060002c251018866503240c040c0600d60345500410500009894108034021959024060000390400411280c02084039861501c02900119030844880c4900b03504c111341054456003c0e44450060b60081000765200440c3c640030707140d480204103940e00040c1041c01c080f011104402c1d51b0300704801c032400740a40d07046445010560100400014540307480288001522481c048580e0740d0100c0c1c564000070b032240c1c1c1104007540c0110118035005440030503204100b042c0840c0c50080d41a0715551400c6964440c17042e60110303032094038003c02049850402410107456600501e801407041b1b000010b40c007005602044041e401211501c0c01c0e0700340c803a6181c04000b561441e5a1030070071010800050303641 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 770853453 1250 770852203 770852207
    0x114030606161e0312061409270a0803010f0503150a09060612120807030603150e03071a06010e0f0102030702042c010f0c02030703081f122103051509060619120b090601 74
    0x6024009050071a0549c590003581c0200c0c0d4103503040405244101c50b2201c01d07034240300d0101c0d04280182c201c43c0c0800d0b100020940b60028031000521040280b200803512014816001030400103000c940710780c0c56010015842100c1c0d034409111500070810a101e414001c00000c2a154004104400f45032600100313002041d0002401d62a1501d51b00340020b502e110040000d1440c0100580103241390386404002d540102c500d0f049501a400a894040040007403004200d9501201c1d5402401a40305002d072038098541904002c0c00700300d0045950035100b18207504080583e038030000c0900a0b0791141e0540400000c03601c6204920b003040d04c059410800260760082c0400000340501c00101605400071030f44280c00e010480040401d50170003031034004245040341003000c00020303c002407034039184814041400390060b1486a4100f084102603400000100040150041c00d26600030500303104c0101c8400c800d40c0032210b000c0d5561103104080d02c04034890030030749007089103a6008003104024400f143c0d03 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 770854703 1250 770853453 770853469
    0x120b1504110412081306020a030806090717100312020307030914031203190609061503110307030f0216050a141f110706060f050114030606161e03120614 67
    0x881241e0920340c80c03100f9084c445242d000354091883d000080201c001040e40d000644070f00305910079164128240d5500c420001f040208544200220701e801c841c419910b2a0040e0305540580c011610020283d26038a03000074956400d0452000359000181031f805040d08030013000c004000028044101d504101c002c45e8031440140c0355105600c03404004035503c142084032a00f10b12600007020005640e6401a060240c049442114842e0f6001d014003404244603001d2010301c04400c8a1440c82d40d01d0380c540450050040b41400c41040e139090080c5403604c1d462401c4906843c7c01b81d802004600c5040c2084a02c5503284060541030b64400481262103007400b01e50007440f0605c2200008805510140703134029441800b00c01444c05140c98004a03c00c886c400d03582054400a0b03a03100071007403c11505000c60301c810307101706034000400d011181171200d00000d29140c461240a03034042c0c211407048003070f401801b0107404901140d50315030084915030040c0309020040070210010120b4407107510101e1127030 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 770855953 1250 770854703 770854709
    0x509150d051203070306090605090907052b050309041107030f0c0c170619110d0513050a11041802010f0c060608120301081b030d08060a120b15041104 66
    0xc1181030040380912605000003291200070910656507454145402030007042d07240101c490b030301e1030240d002c541800c1c00500c0611500d403100051000c2400c0c0700401c42c04c6031802070524401c01003401542e203c20b09a03141d209a441c407400056455881c802d08120558410743e00603030041e04248030700c401107070b0302201c040007043e0203050448040019040007a6402801d070815125030161014083c0e500c000080d00b1441044d680c6510000000c4141d138010603135620202c41110450280301c1d51001064590005070000c08002d510460f0404954805080804003001a50307207c20039210818203080c83d008101c0040480c0c00c030084c6a090b01e03400a44000c00c640092010002884d2140c1c04110030b80d804070025190517411140f228186040806041d40240500c807894064035078510003030001d180c58070b0002c18000303001e002d42c1d803841d00c130482c0c15a00080c1101ea1140d03000d007001130001c8010780820542400703800e44115516042c01740d0403040c10821155030241d0b15002c2d02c0001281c000342502c1c15 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 770857203 1250 770855953 770855959
    0x209013303060b03040302030307080108242706011e181a0406090c02070503030406020d0c0f170301090b150a0302092106041b0609030213020d090305030907050915 72
    0x3940411840031801030056030483e540b0541c000040c003041c1078001016501c551f450f9030b940d01031170381c0314500f150311040b141e4080d407040249100705186050100c00342e542d002d548244005035403c6004c00c2d903040580c505d1f880341440c0d0484801032099961301b12110041d180407402500100c0d190a41c8920b007907071241c1113a000582e4813039070000b07024807501d8500c005480040040c00055203616a10300201a01001d40c1c0152007012400212810084151002c5035802d40181c04d809140d4003040d914111039040c12901c2a5141d0318050006000300d4115003000d00c0320034041d07142d40c10a0314403800c0354142c1800510810409851075002100383c9c040b580700350801c0c640942c0300d40c10740c400f298400c00340100390b401341d03041c901800e14402c07000034030f40d4840c50040340c1c5100079040c6c54030301003c00d544602410001400d1400c00340003506061403600301c06e2412076401450095465140000c85a00460840014030000140705010710304105420160108030381e944a07905102c0044031a41d1070010242d40 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 770858453 1250 770857203 770857289
    0x111c030203060f13050601032414060403050105010b122518081903030b0d0c05090601090801020313030e12030706050a0e07092f0d09050f030412020901 67
    0xd910f840b2250410710b02c501c0a4045006041c0260003800603000840f0322a0000349840403100000641040e09079101c400ba900e0010000e00341007141c1d40307100c41710341041d4002404010010005409105c3e01d8001c0880700b40040e01c4095810152080f000040c010803111000501030f5030508002c465444464540b0381080c1d0403880c0c2c400e210144011b5036500184aa00850031600380c4074003600340c252003081c801d603005c000911000c820000305031002103001d0b002d8500324100380300302d00702010a141c000005043c409003440c0e880850320b0aa900c101d9a600001d405c0d255010704060700a424280d8100084904840d80141e900050780d980c0181c20300034141546070000320b5900c40790750340000344400318035080d03407510341c0c454a0b510040c0111120811020305040c40d4090110544803099141841c904280c40c5041c9456643c00040c1a0090007916075028180d103c401d1140308000a00c0100001264030250040a004000c4440c905901092108080500583e03c500204c0b440300d41c0b1180c10301c4008 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 770859703 1250 770858453 770858461
    0x10b01170a0e1f06050901060912060504030210020408151008030d02030402040204050303070506011e030c1e0e160305010807051f09030209040f02040e0f060c0705240106111c030203 80
    0x19260101209079a0000d050283e084a42010036402983c00c1d1501980d81d07107100d9a80c1c0c603049074240c80d00d200d04620090301d0101c82001890a800c01a0414000e10440348003015010b4000b04a9003e64040b4080e540aa0b011042990142007810b6000c9034604180d00b486150001d256180c3c420362810002541d0f00000050440d62550705a80260502034200c3e42c50b000706217403a640d141428001c1428460141014640003a480718100e000d0381d6200901120340c03440c180c5484082d6444202400c10030f40ca82001040d00946007060620450310020781d084260170b010030203000c403141a041204030307400c42c04c820f10007a2100504071047c0480d03c20508101d00b40b0403000ca07004000750b00001e50207000e1000740300503c00010f1141421f54001c482c2002035003070440c00f41e1780c0d4001c0341c48984056082040090003485200300034018041c02082a1044c28046024408002c004100c0b01900d01c40414014030a481d0301012001035826280c00a1040c140d003443e0307a070b0640c2d040450003010550004000307 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 770860953 1250 770859703 770859731
    0x290a050f1305151e0d02042d0b1207140111030d06080604021804020f040e03041212020105060306070503010509040312092001050f071b0b0304110102010b01170a 71
    0x1005841c09600100403504051a0b083c40f600020884107209000342c0f44400c22401071000d10900d81c802c01030140321080020b9003800054114000703140640010400385140300154480c020070900610800055000105010400c0b4107121404c2d10115608c0040140030844043c1c18600899000342405060600c00c500c01600c0c6114010405681c0c605002001848040004c3c60764040d40c03088400c2d114510b002c0e5404080d01c20200c034040d60102d10007a0040c034604169005070880c080341c100741d034503081d15044070458548001c5401c88003071603038201c00404140e0a00c6030581012084001c1c209505151500900900040c0511486003030268082400c241c010040030b03018450400c001d00401000e402d208203080c103020b0b40d81e449004821b0310700d50150f04c102c00b240c10045851a071903080101948401c1c803141c41003410000030580c3d11401064a0b582c80c40503603c01e510070304075290f6038401200028251250241994140032000c41122070480421580e030b54031903c41440002c204292080ac = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 770862203 1250 770860953 770860969
    0x1e033d0207050a0c0f050d03050904090320100e03130603020a03092a0905130618051207062003071b020901060201020d0b06030702030a1d13290a050f 66
    0x4001d20500c1810f40140800c0210390200e41100d140301d03100054240c0c2e43c001d00502e54102103006002540800001101c0d10f0145d0299813284e00138134100030000420352070407111841600158002c1c0d071084202c0e802d0341d1100e01030b103480007402d08040d40c2080298524100312170716502500d02419004141c10010034800da01c00c101c80742d008611640c500c2034004092103440104e0f80800340e03c810780d21021526041a010b04d5010765088144d0440348500d40c0c4410340107083c5c46480c00b0748260030601c0600801c10801c80c0d40d10301c091210040c1e580380041d1030f1200c01c0360b000603e0001d6041100c00803443d43c00f606030580341e11461074109244510780582010031140d4440d80001d500c40d40c400c002050856055000d0608040381c6001001f40990740c50800c80301c0d0004840c1880164002c00921000910568180c80000a641e607405032000c0c1e50000240850000060503034010380d119240700140040503030540740124441e40d504240440840804d108104134001e071801001543c081c0500c80e220355003 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 770863309 1106 770862203 770862217
    0x911090d0206071a10170d0927061401020d091206110d09060b0a14030a030c0311030307050a031b0e190515071703130b07030b1e033d02 60
    0x412001001000c00820185000f40b00380d02072027480d01410026002080c040e1899409030400285058103c1d0303000c238100003036500d0400c01d4021407800c0084c0990071000204803c420204241d095200b400318080c80e45103420401c2040c041641d02c00611100304030b40d94444103907a600310320b02000016500c3e540c560001e4018400280c011030306016214802c1c1015141801c0081d103250070b6400c1212100302294000400701c0c4d00c65494421040002040e480a05820021220040c03c0c4115000018001d21110218484858103401307018001c090080c20425802200d071072108107508103213000c81c0c130001d20008001d00c0e41c40010030342c0c0c45051000c2940c0c000301100c1d00e80d0610b000d800b500e01c01c241651401041c041c1c1e01c400c0c22150316462440c3d45011000c41100c180340c0340040b14120ba01c81c2e2000c0c0e00003003d410034a8400c0c0103503401c59032000d031094030200381c41d90000c5c4120a = true := by decide +kernel

theorem cover : BRFrame.Cov 770683453 770863309 := by
  have h0 := BRFrame.cov_init 770683453
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770683453 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770683453 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770683453 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770683453 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770683453 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770683453 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770683453 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770683453 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770683453 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770683453 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770683453 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770683453 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770683453 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770683453 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770683453 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770683453 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770683453 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770683453 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770683453 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770683453 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770683453 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770683453 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770683453 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770683453 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770683453 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770683453 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770683453 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770683453 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770683453 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770683453 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770683453 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770683453 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770683453 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770683453 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770683453 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770683453 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770683453 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770683453 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770683453 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770683453 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770683453 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770683453 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770683453 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770683453 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770683453 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770683453 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770683453 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770683453 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770683453 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770683453 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770683453 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770683453 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770683453 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770683453 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770683453 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770683453 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770683453 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770683453 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770683453 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770683453 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770683453 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770683453 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770683453 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770683453 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770683453 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770683453 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770683453 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770683453 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770683453 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770683453 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770683453 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770683453 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770683453 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770683453 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770683453 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770683453 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770683453 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770683453 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770683453 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770683453 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770683453 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770683453 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770683453 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770683453 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770683453 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770683453 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770683453 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770683453 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770683453 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770683453 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770683453 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770683453 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770683453 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770683453 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770683453 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770683453 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770683453 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770683453 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770683453 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770683453 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770683453 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770683453 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770683453 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770683453 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770683453 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770683453 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770683453 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770683453 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770683453 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770683453 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770683453 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770683453 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770683453 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770683453 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770683453 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770683453 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770683453 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770683453 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770683453 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770683453 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770683453 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770683453 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770683453 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770683453 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770683453 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770683453 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770683453 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770683453 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770683453 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770683453 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770683453 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770683453 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770683453 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770683453 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770683453 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770683453 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770683453 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770683453 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770683453 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770683453 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770683453 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770683453 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770683453 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770683453 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 770683453 ≤ n) (h2 : n < 770863309) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
