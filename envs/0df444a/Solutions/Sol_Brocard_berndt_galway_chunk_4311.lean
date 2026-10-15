-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4311
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T12:12:32.27925+00:00
-- url     : https://prove2.me/submissions/e3fb4bf0-c0fc-4504-8eeb-bd2bdcdfb438

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 775179856 ≤ n < 775359712 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 775181106 1250 775179856 775179871
    0xf090105040911040606020a1403030c03010b1b03160b130503043003080405070b0a0912031b060516020601031a060d05030403060204170d1706060403060908040306140f 74
    0x640300d40c0c0301030000803142030707000a001034130030003040340e80d020001d407036059590f421030f26281c82c51240d9202070000001c0d01c4c0102050020340780745901c0c00c01c4c450201c1d44002740103024406901d40340b031a604030500141040900c1c030702150800398041e14044801d0381c0024241c078100d0039040b00140118100005840a41d565508a2400c018101c1c1443d010300b01784501090444030f2100c081002c03d40d115410b54003a82c880d03403c4030481c64880e90303054210701807000c070310000500b0300e4004c1010f2448001074031410740c020308101107076013810500401300210032481038502a4545d07003070080d98040000c0c142c0480055101401d91075046a450048a5039602c1c8683d1042c072040c00801c3c01a5508003100c20010380c00300c2182d030344940e24503200d0043e4200e4130561a00d1448034a00312100800440c03c900142c085035034000c0b8101c186031004203d000054001c1340c100c0018400880007402e28071484400710300440350309840d1480c500c1c20000343c600500d008000c0e04100350038450320000f040035640d0040030703 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 775182356 1250 775181106 775181111
    0x90901020c0715030608030c0102091503151512071d0d02010e060711100c0308010f06020628020c01060f0b04050a09020f0f160605060a050d030305060604050414150f09010504 77
    0x260f03c5011806401c5a401039040b50000107141414031070154001c240c140c00c142d4425492800f8014203811501084a0341c40104008621f8015a0b2804030105000421009126400d140503c082c0303a415400489000f0049180003441ea00407030301850000e90305082c12100090f5000ca00e6000070484580c035490a8010701d008a020000c1201110b88002c2043c0045c0c100394000d24a840003c01e407408604058004c5004200049000c010090100056030403c0d00103002039221500403001030150003021070254503008010118600c0c4900041510390502d10022030554240a00c9501c800344a40c010518684100010840c41e01c50308500400c0315208400140c42e9407280c1032407205407180704158003200100140c8010012642441080c00500401e002c0086544100511094626901810b03034000c0c070115110000900c40d801456201c1406458181031030b603620041400d0303071000b440d5054401c1800703007000308001c000d4000300c11b981c00c200c4910303203c18010804030300c4030441801100e000d0364 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 775183606 1250 775182356 775182389
    0xf14190815030a0f03090f0e15030a05070b09041514010c08040504060e040506060a06210603050f0f061506090607061410150309020907210203040c05090901020c07 72
    0x108010740301074106005000c0e901d041a0a01e0021802d00c403031181180440c0c103000d4042041040c0f0803608055600402c440740c1282c6400100302c4016660411b49503061003442400c41c00036030140840002040f00c80c076420f44400c810000c0100340c0b030700300e07803021008004600208102d164080440d02c00e140300f820b01941c242e00c941480e030483d20464001b160041c0c20a02c0025000302c940304480e10642c00784c0c0680380962180c40400000810b14880c40000411945412000850007214480010142d00d00014820b0303681e524a4246504c200c166000c80d00080440108101d05000d4260300001801020b0703500e86061300040c150380030b0b03005980c0c0920804203d400400400d6800307808072514031007103502949402e007443c2c5402a011301071405104a420700010007030f4020301803a5605035000700340e0199a500c07454201c1e10307040079045800c1c1d0301e0420a0740c964102039620045001d1800b0b007540b40e064605260901203049005030100803960320420040304040b1002c112003040d0f030f2244410030201c4 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 775184856 1250 775183606 775183621
    0x13141c141204020108271c1106010501030b1305160f0f020a1704230f0319080a0903021503010501021603030c0314040902040e04050c120a06020a02011b0f141908 71
    0x39040c2d0620b0202c0900002c1381c0c0b03440b078a8001000010054031700e140d03102c05140101e044032016081d01c8c51046903448240148440e6000380c2002c44000c0000d00050411141c044494090b00c0c815503a505800900c4541c1800c20383c0d000c8100340c86174170700b410f104803400c01e100f000955032140040050003203d000c00300013444100c40821200140354542401c0d4014418050880b54072103a0301c0c80c00d100f00810021000d25007004543d000340701109010800d400c1100780c4964a860b8030408980041003006000400180c0c3e03440301005544042e100810344a60402001a25051424400115400b4001307070400010794403e19801d040d80c2c1c1450032201c5001420b00440950296801c40225203001041c0400c02e00c00841d101072203940203100312001c10300743c00300b0300442a59100e041142ca801c501490001b20b810b50300146640c4003c3d100008034907030060310400d01000001c1c20980011554103010300490343c800c0443d81c03150200c0e1007151030138020039000d1841400540f138280912035080e0014008 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 775186106 1250 775184856 775184881
    0x60c0201090c060e0a061407020f040b060301060507050705011418012003070c050603010b042c0f0403081b0a0e06070203070b130b040b0313141c141204020108 70
    0x60740c2d44142d110034820b0f1256006440b03c440360450a018030344c03a100014800e4816158050401007100b0b0941ca0440d1540070310203c00380d90005581c20688401564100b5203d200066000f0301e0715984440e00c1e003c081c9070007410450349900c000d04000405c000e14484500c4201160141003c0c07070907a0340196420001620351104485030041c006050b5131140e00c90400100c0103108143c0300e0603900040948500800050307000c280240c0900c002d090200b80005940704001203041d0300380740e80c1d988094000d241040d4001f2401c44a018601c2010420f100c10140c00c0031205801c40703600860100d003d90712401284003030003482c10078010000e0042c01580072b0340f6100215004145c0242c181d031400340c0c480d02403480030307400f81c0484031000d400220001a54030800007680c0590b11508100361950b02c401040c04c8035104109000e0b2a200e4007050f965800c4401041201e003090720081c1d04401d120300d4514084c21410030400d02100c1e402d01040903000e00c400103028940c0c03045d82420030303d00b50345400640500c0b = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 775187356 1250 775186106 775186121
    0x4021c02120106090510092307020f0d1707020a0b0402040b0109030f06050f10080304030b0a02091216270f1107030306140a0602033703050103230a060c0201 69
    0x5a51820707001180041322900428490100d000480103d1503480c0362507407c44500022420700090040110a101c0102c01c1b5505e40001861045642c1e1840e228001d0b0b0030300858400b91008500e0070019100891003161205a11840c1400640210f03a0035884010303403a400100020320542d55090141c101d43c1c01030380618044c41e000643d0f0b51250034036150940c002e09055a191516a5041000031007010320429180280c8000f40c01031810680303540d503070b008020006070101c0f01142d004c4c01841140e446400010340c0500020303000b40700b00000c001c0202100305c0c8540000c518400e81e42c4c01d541c50b2420b0035034442c40c0c10303855410001e5030189245484004000f086402100040300240200516900d60131613816940150410705412130400b00700300100000740300300c0005d170b0418000e0b41c0c44680e954240d012003018901046d40307200440114035104281041080c80465620030040c010300c1256071160620000000d81c03010540d0212020f565140342484d0300604554907907282003a864400e411810 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 775188606 1250 775187356 775187389
    0xc11061801020d240503010606021005130f0602030f0708060f0d080906040b0a090506270d020604152c13230115020a120e1203030c0901140304021c02 66
    0x21903998900410240380380642d0310ba21324440050004a514a07041c0b0503541120042e8004000301c0a602d94120b0250070010010058050300003a440c01003841c880c00c1c080c03814400d287c0141e480c689030b0001c00c005000a1b010b070741000001c4040000580740d0030454041c0c10011144c480303854250380b8107070000c0d00c17906403516004140401c00086050280014121603205921020109900d4400307221150103401c064684403486007400b00244000030725401285800a08420340c1340100f07030080307903043d442940400b000c00024031007003d010741c1c0302c540c4658020001d10304c40b0b481d00b0350801c00304030b2042040c03d0034860304c03c0d22083d05503440d0f29480001c501c0d0203000084c840c1d4071800d00c4540030800921914010380380101c804115241f01040440703029070f0281500c00030079050303a4115486840140030340d40015040c42405d6244100300061441500035800e6142d8540300c0c6400100110120344d41c0b107100072018001d010041e91064101078491000704103882d1391240a00016415248000c400d2 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 775189856 1250 775188606 775188611
    0x204050a1212080f011505070204090b09010606050f040b09120714041d1b0d02030304152d0c0c1d071107050108060609010c0b130201030c11061801020d 67
    0x81c5032685288407444a40251220791681000c403805407190b1204450800086407810010320080000c2100c1440844076440c2183c200905075010404864034007a003170741d00f01244420406210380c00d00855001c1c22617881d086040150724808100b044c01a801020260007010400501c01e40b1019490f5001004074800c6600d41d030b6550403140c02012070f01c0340080c081e504103d80c1010b0314185800f0038540310105070041c140c10f010b0306014420000c1c4440c1c03282e80407581c05844005640d04202070300191500300a0180c00d0f07030007030801034a000036071500000200f09480031004001c01600c07040c4000412070815072904429071902c108890041d8110042d055040c22000d1038401112542e688075125644a11031025044001b6596400007845024009000640003130300a041100c040c00382d00c401070610700c170261031503079070024014001c584a014401031208032609540e4103008050304080c1c507082402c0c0810315a04c0c1c2c2a201c4400400d0f01c03d9103004124104028802541100d010380c040041c00c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 775191106 1250 775189856 775189859
    0xc060f1812120d0b06070321110d1d01180b042112060b040b160206070b160f09140d170309011a12030405091008011802033007060204050a 61
    0x1004a58101160544145250134030310400c6040c5081100c02d580e0f00758403000c0c0320804020100c4044203045214481242d12122917685030714011000e0820820042c41c046141c0f00e5815000e501034070b003010441c1d0160305002c1140c8442050f0303105d58003410741181c40c004003a6542d09110340014024101134034100c40e100d07003900c4065071150640d105075002c0c80c003e108082c0e4400101609002b0b5000d002c00e428810442060154510081654014400340c10982080e055454010320713180101e0320005002d00e004103003904a9406840c49003450f1803800c100070740300c3c1080030b1010411040c144003405080319801400c24402c0310320070781007080c2000d02c11540d07030310304110b01502030b01c51700304031011074191174260352080d282401d003d17080ca6010301e00840c1428600010091030090141000c0542d00088001049070b80080c021580e85007000800c0c180400620301c141460810105d180400070109002d00c1c84492640700c60720301000c02408012a01ca02a50401c41c1c004d03c030b50f510140d80160003040 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 775192356 1250 775191106 775191133
    0x130210030e1203010e060f100e0d02040c050301032310050c0d1505210606060702130204080106060e040203070801030b0604021b06010501140307080c0a0509190302030c060f1812 78
    0x11410307142405d40c0d00c106500c40d4003e205440c003c10309070343d03803104c44804c8882c03c09110703507800103051000521000004140d9004035040b1f50210403075000007100040144240400007500319642e61030403900f0b05001c4500c034042c50b280c20344880d1404040340c4030000f180a5505040581e000035201d084108040140102c3c102d5210b4180e106103401000c15103101d00b01030413000351240d03401b000c24001c0c02c070039500c510400c81b140d40001c10880c2c1c17241d6202c800070891106c0e840a03001038004840002209428002d018015401400c0110701c1680104100b188059002d508641100ea001c85490125124440001c1c080c1c0101583e00000440e51403807189800380c0000c07500e048038002e0700c486022a550214084c03161000f1242c9801060101c0007042c43c104104c0018088a0301600e400d50404e410940092001c0c5800b003100038210b424240c0c00e20651609004070b86070b035001107940501c0d103170065100c07004900500d101500360a00c0c40c0303404000c940b80d01e542c5d035504007000416509402035054 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 775193606 1250 775192356 775192393
    0x406120204230906010f050d0b060714070e060a14040f0612061d15040b0a090606180e010c170a0609020c061e0c040b03040c0b13030201080a05130210030e 68
    0x10624403540b0300f100402e0041d4090a031211000495640d0f0502d0011201c000c0405421989036054100104029601c082400a440d406010704044041d0080324600341024020880242c003c920800c03914500300035140143c42250b03801107003a1000306410480b0b00e01d10300149650703404442001510f9500e90100305896000c04004a180303844201d003d0f003000703142a52941c82890051210740880040703004215401c0d000c540c8080070300b4010031000c586076074040683c4c83c194030013090309110b111045146941c41c01070050fa0804078000704403a8590b8000203040c040000d080045031004407000c6686e036200ca8001a0150065000543d6a05030020302169241411114181d05080704030a444554100580450140500d984120b003011b040a00901055001038400c0310f8500b05c4840020310801c3c0074000c0c1111540a040c00c03c0842d255000143c13107058010301d80b0840790700e0a0100140f071000201c2402c0c42940540300d0034400c148205095000b00140c1412240b1845840c407450b0322a00d40d607 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 775194856 1250 775193606 775193669
    0xe1f09030c0f08030405010804060b10030c02060601080f0604090206090607030c02150702101209201306080709090302150c2104230a1a1602030703050406120204 71
    0x40129000c0c9540e1503420125400090083e00d1094204000400c0298070403201560094000d00000401e0300e440b01c00100311022548442000c6912100310030b20858041c00750759031021080c200001103180c589080130b4a5140140003902c0742d990f82050300c056480740e4003030b520103501c050320403a0759207010f003006054040340e03050880c8504810700041d503002e800507055811141d800b03072400700c451080e4a405d40c3d50446904102003065503c20264022a035200e841c40049a681140d100ca10300303510b014414446981d181c10480c003410808100401400002c0c00340445030845000110309c2c0031850200e040a0005e603c002003001352400b4003542c295680000c000f1022481e02c0c4640120f00c5000d00a48503e041324054a03140c01c102c24081d414401d4804136054404500c20748812240c0d542d01c2a001d500035a240e99440542c00040101c0303514010000d5000380300030300007941000c000b80d500902902c924010b110800c14070f5204480e00c41c4558041c2c0700540341c007201440c60303411190020303030784411403 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 775196106 1250 775194856 775194863
    0x906140f071a06030a05030f0306010c021c110a03021c02060c0601060906031a1c08160f0b0f0c03040f060b0618091f0e090703051c02010b01021c0e1f0903 68
    0x861001ca0fa0300e1800283c00c50f40349030300c034024600301080300100803919000141411305102c4410034800041e42c0e051140c0400e654030b003442220300402410901103002c404401b0038019420000c060001d03a4034401000550004a060180030f80e545101252060007091036101560cc103000010503d02c0c0c10220150075034400d40d034100310b4009098038846540d184215415001005503111038841000590201c1d18a40a03d000c40d01d001d81441c0c2c03800306111080d07425038507504040e424400b0005941161600112481c80c45502e5060030020b045080c80701600090403500d9480c904420007100d41c00061301507100078012a16144158240c40300203994400c003503c035640e00e40000d4203a0246601a440c000d40b620740c81007025051010f068040803018082c04c11a200f04940000002c50401c4010311103041101e8643d80e80312501006400c2d100004140c60564010210603804010242c1c0f580728811401c0c603000e1a26644500403d0109841040250b1010328212280c4070103a04928408100ca10 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 775197356 1250 775196106 775196153
    0x50114040b1c05072d090b120d05120f0702030909040606082b11032b051f09050106080f0717010308031e040507030605190204090b011106070906140f07 67
    0xc083c2d904620b03145a85d0b000d0340c4031044a10741805200388503403045c41d45941c058040d92041e100c81d840c041c5488034900100001520028034008a14040c0c2c2c6080e8004000700c540001c0c6050005010b51030f40a00d110440c028415940054140400707030b08004003d000107400d55410108a40003078402d42d500d4811180300d040200d92171102e040c800d90743d14490345103c0b8040c2d0b051105010504482903640a0300719a641104401224182c04511400380900505c0e200ea04c038900701e140e290820710005902130031010b80b17084010050540c00c1005a640100c14400301019903a48180584000d0140e420f44040103907c01c0000c420004210003c50185070400504103070f940c01240b0492200c0411540148a50445081040041c205812881e04201075100352403104620864a030120380040e07100c2e030706650711401c01e078915581020041d62035900000c06880e5614060002030180c002c54421281044403801e40e8149270f0f906071042c0d4904009401c0e1080d07507044a824523404065603000110722900 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 775198606 1250 775197356 775197389
    0xe0609091317190314040201020627120307031107110d080c030c0c0a12240b10050d15031a06040b0607030c0209090d08072109030819050114040b1c0507 67
    0x103a03041005d92095505a000740700341e9070388000c401920381c880c0c201090303004050503c0f410f90358801d1011290044c9a440e52076124600b120340181603800003050000c04c203008000c0040494512080e240003000e0940345c44494505910b000420381c495428800c0c483c0c00003040034006400c01207042a08484100d5144115a803030300c280091929606c1e000400110344c20309114a801700c07003803e0b0035440c0c05551700024207104000c04078503203440034002040055400100c0d1210400076120b44d070390b40d81004035400d03000c42c210341d5041603c0c8a10403000c001080c1d1080001e40070380e5150468a030101c0042c044548600952802804445c0310b51400c0348183c0d001000107180c0580051164900c1c4259034880c400b0b47c5a0f004152441d2405583d5104011030001c2460030a001e140214803c2d68440d0751000b07920b140c11100b2158006040c0606107000e4142001000000b035248280001860300726070009030540310400040d0502c50030105120050b90414201050003004035880080b11100098000d011 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 775199856 1250 775198606 775198631
    0x1203050307030b1009061214010b070303111206010c0615090605150306100c0302010605090c04060e0a03020109171e2404020901030311160b04060e06090913171903 72
    0x1004004010000030400304007000f40500c0364500650070603407011f001498812030780510803100026004403002c190002540410160b2511800c1d6900c6404900300703003440408040340040e0030000e4040c0e030402661822240510019510010341883d00140d405042ea6a541c0224040c040c6031080798465888154900c0c81b2042c00811244290b2004101d0010b80722a000c2c291801c0701c0c2200103070700715960380e4804645074440d1008103014803000c210740c40c0c981d460f00c0380040c40d4007075004450f4000d051418042005036013110340c550a427100444140315400f00c0618452401da04003c6155203420b041e80601030280011030404240c80e460b04418250340600c04c0039555003002998000c1d0004c00c0b040040001c81e00c5030824584941e020400e07140721000785081140e920125800c8184804000582003001c07540012911409034425a8014100324a09002441c6c060000b00203070340c3c8107401840b140410440740e100034001d01c0d40101c41da40307400e14aa0700612101600c100e00700807900d0700c01061a01e = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 775201106 1250 775199856 775199869
    0xd02010c031d0705010c080f04060302031006020d090b1b0604080909161e05040b3702030708090f030d050d0501062a021c03080405100c08011e1203050307030b 70
    0x6080402005208184c5003100454840446143c00e1310b00f1b040604c0b080d904000741c8402000141080d95000d41c0340d060030300002d0701040c520361103a425984400c2203c4217a0340c10099074400c9038586144251103060480320910000034000504125011782c90070003003041011409000c0005050701c141100b031361140020310f0355010124403080821070301d1095080320410b121040c1118052468054100f81e580c103d0580076811460114500342011401c5940d4108031000010b88a00442d200c2c3c1484500c03428003035241e02c20000041c200d410002400e0b9000d84a0301600d440c0d04070094201c4403030355400003004015410900c0313206d5119061100000c1d0080c800c40403450700c004d42108004400701901161500001d07003520403600565010303003040c5004003103400f0900140c06034170ba603203c52405190540c14841d182c1c02d501600c514148200120540c08000030307044d0ba4040511100440345d000210b0520b4040d9400007080d4952a500c4000b0554060080c50207030095840a101c48004003041013074 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 775202356 1250 775201106 775201151
    0x120b0a0b0a030f0c121a0702010b0607031214010e0a1505010f0503070e0a090e01050903030702060612150106090e1015050906040302031b1002030a0e0907110d02010c03 74
    0x500c0007030880140302050101000f240418401c180940200e41c0e12816840d0b808030303c007000c0d1208220f41d21842d0107880341c1003a280e40a0600d1000700103004a0100042250050035005803c100ea100062508c800e001d0380301201810011082134020341c1d4501300b103120070100310344104160782019a090040d40c1c1c141d5040e0305850b0305031100e140c00d000706503044038142c000901c51404c11108a002c102580c0702c0e1005240034064524010411a0302d800d0a80c0c2562005400600203074410010048055404142c40c0c0c0c21100840d40100c074003d890903000e1901450017114203007210a540009042500319484508407031118a00340019900c2075040c513503983d06880b6030340144012940c1c80c5401403081d401403003c10002005103081ca03483e600441d2400900a60f008502040885488103510f4038001080b50252a44019032820009001c001d0201c03045902c00344c060700003003000c00c4126008101400b100013040c0122080c2500c00030009002e405007513012000300385403c0ba083c0e00c500f44007040310b9 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 775203606 1250 775202356 775202359
    0x513020307080c0d0f150603060b0301060b030402060f1608190e060a020d0f050c102301140f0d02030609060708060103060602030301140f100f080a0b090a050a02090a120b0a0b 77
    0x90303013841c261a0030b030034246090002ca6801c0d00400ca0340c660481d0f688981400345000312000034103101043c05060844040350000130302c8a0080c000c00006a55a008450781000740d4840c1e2a102c00700da001c0812002d0302154024403608011821904452030400320348804d91840d9203641f003412490b81840302c14403070b90306a400149c0102040029a5000e00c020341010700b2545840d81c0303091040e01ea5a4188006884610103540e1108023540e80185a409034000c0c0c51520004030810b03501d85103107001901040c030340680c002c0e0240c40d54140551390381c0707032461011034020702654154a051031510362107000485014000c21220404900d00b075110784074803015110a0b800071031441c1d00f050b414442c090428000320b580407802d100714072203d444514003040360b94401d4a425658078013071031016104502c018003c584046c41c0080d070105030365030000300c0741e08410020300024081d00c1d14060700b03020b8468810059000b225501d030003c0c08441030300005c1c0781c042c00f601c450b502980b03d82c0140016214102403c5 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 775204856 1250 775203606 775203619
    0x2011e0b24070209180a1a0c0301061d0301092001140c0703110d060e0f07061d040c030e070b091306060206010303050313051002091e0627040513020307080c 69
    0x300044c2000040c094100109118141d07a1074510307203005107021080881110130394503401d5109420000603001c81d1700170020b41046800d40d03050a000601c01c0700b107040b00c1c4e81c40501d40b210104054600f90301615006402a0401400d0501041c0d00c048007a80c1d000c180d40051a0606e0403410010f40000380d9500403c80d001501142c2d1858031401c2072402c13400b0040340e000c2c0c00d01100800240d160310a50500049a101070000502d412009904003082603214000384024050000d00c10500c181074040643c00403100001e40c2441d90800301d0040440248900062048000102d1800d441d08054602c100048680d0305850318007040401c00c0d2007141c42201c01580c0880300503c000780c00356028550140b0400841c481404050326407516007900703400c0c010300080d4001007130a49414001301c00c440d00c10403c4050011220382c0404140c940c8580c15020101c04ca002503c040c0000e00e01000b5400420018000c0c800b60501e0380c1002c81c41c0095140892003403042401c0001c20035000b0802c03085410004202 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 775206106 1250 775204856 775204867
    0x40c050d2a180209060405030105070f08091f020c0a021207210f02090702031323040510090b120f013c091a04121103040f03021002011e0b24 62
    0x10b4000380d086602c1e99a4080824000404d82e034400f403107131a2040440d503039024080940e00c04040c2500901901c4e4003084d4205500c2280d25403200e00507030401c00c481c40c07c0180c1d1011054440b509254405d9402035100f01d44001001a2000c006031038800e80d0819601c500703c01454600c040280030310a00010103100d0554803150152a00c40d2400781d0088a40c0196031400a203400c0c2100360b24402e40068000e90341038450011000c5000114030343c50f0307905440400c028202a9104520000c0512440b07821582304c01111100ba00d61200d120502c0c0300c0079040b00c1c0401c5848802502034003c0501001852001701e0302c0344101044d520414111840d80b6054803003030a0600340400141c11030003005d84e03221901c1a81a80503d440000e502e20034ee000d54016070710702d102c02c10010404000d078400d40ca1030754400d000c28000e00c091003000300d0450741d0440d0300028407010180300780e001d0721400c0449040712404418400000d4000c0c1c11a0492100440e00301e04c0396461584000ad043c0c180034442e49540106214 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 775207356 1250 775206106 775206149
    0x3070b0702240d0612030215041b062706080703090c320102010b032e0203010f061704150e0a02030d0203070c08010606080708040c050d2a 61
    0x1480c24600251400491803030310300b2000007000e07041c0300582160600080b41c08805206228a6014003000040300c89148030702d0b00c00a549450030409208804d500c1400b181c20002461203143c0400c004140014219945d1507014281e40c07258280c240d0340008030340240340340004400411041e12040d84541c800c0d52100201140148018141110140d9a2010106800440b00a1005142d644800c000340c81040d110f40c01300e150401144050540e0305150032a0020b80d40401d442c4842441c1d0440c407106903580310a503c6820880200020985200200214440040290004c2940c560742c903903070b0f09216046025500181d0071900034040541c1009000100ea4003500070809040114040303961101031a00001d081070110f5100c000541d01c0051100c040003100550340d4000d0031503400800c100c900d48280602042c0c00141030008210f04003001404000305182c03094060400548038010a007114501044202a80681211184100c0c1c400402841403014058140d0b40040c0b42a034450340c880c0c4 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 775208606 1250 775207356 775207379
    0x2b021b10050a05070515040203010b1e0607110d05010e160806060d0503071703010911160311030c01050c09120c010e060d0e033c070f0309180606020d0504050307 71
    0x1c2c1c56007040010060b45020560401081c02010031844500c141d0781410310405085441035042d25003e141242640b082003402c1803c0100710000c181d60352071351070700d00d031502c02000d11405121076481840300140d102840310541c0b01000d025003000440781e5540c65000c0304c0002c020144103100300e9074445c2000503e2030a0001c000382c0700510500889042201d00d83d61100b44000c418104801e603100800100007050f09800755401000b0076080071850b100106482480e5444180e4001d01441039550f80d044c1c41141c10000c9034080b12300c01c002041203003806007a102107a40014162841149030303516000c0400d0001c50b416102040507151040210100c109000c030b150801c004061019603039090109d69414144001d04001d20424001000105450005246007801c025450b542c000300c400d00308800198041100c800a80041100b100340e000351404513240702d10740d0002c2c1d4441e24103c1320100c5190280d04904181d5845400f030f034480c0c040e80d40c2c0c100d80b03e00640c42915410742c851141000241a0903 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 775209856 1250 775208606 775208617
    0x6151719241a0901050618060901090338131b0f06081b0a0203030109020d0f020d051608100317090a03050d1403130210022b021b1005 59
    0x441d5202210080030004411a040070180c1491419904002000b603d403071036029015000458801c0d0500c2c408a44840081000340100da000340d400040355100c81e030145211000541c0e20410803440c240d545000040c003031040410300c1c20b91642c0001c035070742220251400f852041800c0d03103081003240e0660311400004403102004099404802d60003040c0142600401d2000e8549625103c9881c01d04c1103038024108040644407201c000c0901158004660110032241141e0b01c1d8680036844404415000004256034601a28610300c0090020403241c030541002e032140c9008400c44420215007078064900c84c1c811140b280c062103440d4800d000144545070881302c030800303214030345040001c400007081c030304080c580080d101a84181c58403058564007a1010210410030102603042d8105004151208401800c0c001d100f500384003898000ca902c07c00c03135403500031030700c61240154610448001b840c00103a40322520060046000c0c80c0201104190f007808512000f0341500003103241c00a0450382070300720 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 775211106 1250 775209856 775209893
    0x1a07030e01050108011d03040303080c0a03110a1d092e15110d050a05030610020f06010605040f090603050a0308040c0e3d05040f0906151719 62
    0x5540d01003018803024800c0301c0c040c007034404c0002980c8955a070208035170700c1100005602c0e0352080200b480040d50102c60b098001801034400e0391502c41754582907025050f40c07040f0000349040898501c8106a012038081800c60008002c40300302c1d00340006000308458122860800100ca050503117403000204400c040d007450041c2000660191111142800340c1c48015040002403600e0980c080720800c10f02114020000074180645401c0710070f18046e20350700004111a200c7ca0ac081036034643d8600a110107081722070301100740e55940d0f031150409002034000340501e41030580141c80104400340390303200c0ea4003541e41201c020403950201e44c3e02150800001001111007156105000820a0710303180b0742801a15240c404042c00d1142400f00128120b00101c1d202e079629054042c0143c120702e038004441511419100461995124140c0901401000e40003e02d081d1824a140490000b80d1102009940344030894110f102c40c1040c0c403640d01c2054111000c084201103000307000080101c4400e0398103049 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 775212356 1250 775211106 775211111
    0x50a060f0c1e0206040b0306010e0612010b070206190801030302160602030409020309190b04060b040507080601120b060711031908040e060a0b0c01091208010b0a08060301090602070c030b010b071a0703 88
    0x10b00b43d0220b0440e41080d8028850b00344003105114035582c02c645040300c002000e441850500400c1140e102107024103101e2650300f00c0e0009041802e40d25810122680140c101250704111356960800402c03900003480180c0041c0100d929150741c8942840600e01140e1941c2d0080d4203140c03d04840ca0029440070380040301500c038a13a00c0004590100c82014440c0d030017007002c155589840c0c20120290b03403d0f90310440c40f40340340000b04841103402600030b03a04403000b0b00e0700307001e220003404182c1c00600041e4400f41d4402800300304a010002455400d0031112026400d81e21034000241d03100004251014001389075260500c814408142c03035210780c0798860b0f801405410340c640d1707038440d80e00302e948402e0301000b059469540403014800c09101c45150703041c2d43d151042c0c0941c07500b07201602c54018003c1c000c00f041001070103d84186d4094200c1c801d15a0014411590f8050038a40006007161612040315003215000000072001c440200b900d07003d07034100da040490700302d030f020705002c01a1009010b41e080c1507 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 775213606 1250 775212356 775212413
    0x902030106050a1202040314150a05371503140f06010b07060b09131208061c0c030506010801060807060f0e0d030201180605090c06090f010e1305070801050a060f0c 72
    0x2012180020f958148c0c820280c850085504010071500303000070540501c13641041c05102101e4952940d00380400091681c0003000000421884c00c0000d40034103010040e801d01c164050328400001459040368819041c1043c4025048000e60b22000380c0c07500884141c0201004008600503003008200361482042d00282903001a4000b650449090760001012100081c04504200054a095543e026182850000c03403070120f001031301c514601001d5500c5114140003410400400400480103103910000f42c0d01c3d15a1903a03985402845213108000492144903c00178407580589840040e8031990742c2c1d6148441d03441c405001820300b40b008110700319136841240c0712604202ca4003440865201e4400411507042407012986020401c0c03100078230a610400800380c1a030b481c0c18803418042ca007801c0c08164011070300c0014507032540c0381c0020f0030410304107020060380980c00420a4143d50084030750f003040e6600c2d04000c4908081109c000d202040f01d010140f40030500401c440c80b409030240d91400d4501 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 775214856 1250 775213606 775213613
    0xe06190206060a0b07150f060b030c12011a0412151a011214161103030703020c01060b1c1d1e07050f0303030a02030603030d09110a0902030106050a12020403 69
    0x1516054104005820020601c0580d1420003491001007900150580c02c158482d102c0c07901207820221001c420036034442801960400c0c0d80c0029005240c155045600d0385040c0114102c19030002d007107200e148401c071001040c0503c06c90201a1183d0388582c05600302410303c0d1800e0b5002c207250710199045d08040c0004810403025001d4800251440000c090703c2452000000d400e94440c41010842c1c64144105440b0300c202c0d10010310b90080f1044440141491100029201d11403038011b0a07206010000c03c020781103030550000c14401c0300c0340b4000c200160366560b006000780107110314000b01140010100c105d904103a085810a542e90340341c155240031080110518024104840d4020010f4071321900440315024041e02c8014035050b14071a088844040010f034607480024110386600c0c1d030102c08100c5c192001c006417a904840490200681c25950801c51a54010091001e00c02c902d04000422a00805d0090b207040300c440d0380310b0b1400c0a28410085e82c002a003007040f6502c0725828440000030 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 775216106 1250 775214856 775214887
    0xb03150103150501060503091908220f050603060603040807060615020d02010f020703020d05070809040603060209030f0a050c01030e030d02121603061404051e04050606100305010f03030e06 83
    0x20340c03065030120b4184600350841019184140d1048042c81310a200b0000040404181c2d0300e031400c0202c854100384c0b10326151501480c003c030325502c480c0480252040c0c1e5142952503003407090b5800381d980c841c0300e01d540308200045071004950554001030240081000203074800301030b1600d0351207400701164064076040000c6120004113044001640309a002ca01000d4084c420441d00845410041d450320000340c402940d294940d5040804110000403010280203803c0700340c0d000240004c1007484034983c0c9046c600c000c0d41013100c03481d21900950f80203082c0b200000420261082d402070103840300711000710040d030080c81690411031803400100003445c961941440240403007020101600c81034144003110800d400140c28a40046c1444e00b44c05110300d11a103600b100c4d1902040f1030100749552190000804c1e21046601080741c50502810f0000b04030001c91168400e400644041ca5002c0352a2422000da84007845a441004440700d01400404e216010654140c0c901500440c41c096604200141 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 775217356 1250 775216106 775216109
    0x60303070b0a0f0f1401060c05030d0501060302070605010803030403120b0301020f0d020705010b03061e10090c090618120b04020301020f220603050c1b0c1005040911040f06030b031501 81
    0x101c1c1560391054040f91401840798a00780c82c3c07010410820b00d5100c01c43c0d04130303c44046c010041405144001071041000400c1204d11603603010070305103d1940c1d9028041c002e5003180b0400c841450901c1c00200318850000b090307d1003140c140e6150f03000600c4407407000c0010184403902c2e03501035408000700d403542192400208410022031030300690311100750509608581c0c0d85000300703220790002424000c0c141d200c0b0000c626646100c45542a06e91035640c0900000800e981c041c0203840d040004203012150403901000459901d91114079440ca001850014441024050507040a441c1000c020204404020b525880707880500014509106881c00c40d915070064959000c4291240c0807011a5100c061310210090005080511082c1080f403051a498054040003000c1c941030600780701a0441d0802228071628006010400030004c0da40c0000e21a611070f019031f6403560b040c820a58403010324413040f40c1c1110b45140c4a00022810260114054a5104c7c0d4030b6515101c3c03841446400340d00c040c1201e0 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 775218606 1250 775217356 775217371
    0x102190c1401060e150117010815010b2b060b030412090911270604090b120a08030f100308040608040501180c061103070b07020604021e0607030503060303070b 70
    0x3030418410707240510421409084455075a41480c000700041000c2451250b0014210300004103d0400800104d550400c1c00c402c82003560f0003040000b9843c14080323840789a490140707405680d5a80c03195248809071280c030584c4d401884440e04520f86a110722240400d5030b400708039010170220b64884400d07c0c2c94009071005c1e6801010044035242842d00002c3c21002068581030038001d141c03540c1080c0010340150611842c4460b48a50844000d152007500401910340c0100059159500c50800c11700914003078007050b0151400d0f0840f201100400510222480d501c00f41841ca10303600d01014111680c0003504501840f0503000e8040700181e540400b800141c001d41c1e40781c04d40f51400d403c200b07094480020b00c21030500040703c1814081070420341c1c41020713243d0f40c1c24040e01180c010001e0038036612480030042c0000406000f4052682c0d0b012030042e00850088075071020145000c1d00146050100e400980d602c428204190300000340104042d55000d4002801c1e24100442900d40686c050b07011922034 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 775219856 1250 775218606 775218617
    0xd080c041203210606110601271b030501080d08061f050706020408151518060622060e010224060f0d030c0605090d0e060c1e0624010c14010219 63
    0x5104c0d00307903c1105602101104002091f041d4948184d1b2030f000b540076150300c4020504c2a55100b44207566401c060000100b1801c0d646003000701d8a00213009000a001d100098040c840c00c0e02551841100300a01480700202400c04920040b800400d0420807075070b4000c00d1001c1405042c0110b400c0e840904010b00200700134003640f030860900745075440380042c20240c811440c3c0d07220100325143c0722121840002400c0c04221a41c0701c1c0380006081c2d0140031044421205402e44403c1000f1100c20300700c04481d5582c47d08032048000d00016070f1030300200c46c6980240b484011010a240201107007541e00118007070164581344011038081205c61070304003405e502060b42c140b5a2003c0101038443e06038841e980d24081c008400035902c004103101428600a40709010106404038070803024844400e41000c0c03296075415071803104a0550321128100d0f2031081c00d038050401c012070480007184140390024160364010301c00c0015034440092000e1104010000d40d401e0041c0c8191240501586489540c0b98440 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 775221106 1250 775219856 775219859
    0x30d080703110a05072d051b0402030f0a090312020c060709050f0f1525030305060a030c030209090f011e0b06190507050f19050d080c0412032106 64
    0x50181d854002140c200d11a042040b0f0441952200a440c040d0340d00c04540c0b4540300300004070440145d21410007030407491207080201c080120000e60b101c401c8404600340581040c0900400040340002c40349403944c050f84a0018051900c507602400e01a40b1a080a10150203604426412608110911405544207405120815400030403c80007001e0454000411042c02c40100e900d0b5941220014054034041000c072403c94010020b541c5075102c1d50309422404200c0b843c0c05050010481c04c140d0102c1e1610011031b0203800e2021402d000d40f604950403103446482c42d8240060402c004000544500413000e010007004803e02440c0580d000a007440a111043c01c400c000c1102d10b84e0841c0c070b105420400a001c20110300a0118a12402609220b0340320203082c20083e080080350050030005006040300f030181c0c1c84450240c4071516010340b0031142c0d0407441501c01d46820708140d41d0b4440341842400304002202c1425a800c0702c9601c00d181c8a60790101040c4501803445010101c2c04d03030135807901c00 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 775222356 1250 775221106 775221121
    0xf020a110a171b0a1a0a05010f061409042a03090b0a05060d06050106120e0d0c080327061602160311060405090f0402040c020c01020606040203070c02030d08 69
    0x9154044815000c06000ca0014a6450021068080d070950034800408075241c600d55407401c0c0714103407102c0c15105459a006580c64111342c0803207405820303000707911110003007180c25045108280c1620711400110040c1820b18100350745030f5007006000031881a0811240b01070b92203d010726212116000503c0080301442c810904600b605542d0f020304151502d03000c840881c1c00000c40c260444075071140081c640d210301000c40c498580d010005498242004000260f980d4410a603100c541c6902d182004500700d50280503480d440c110340380400080b424091400401d031800000c41e008040924600501d2503440e80741d0507070301c0407104403c00c41e4100e041000545102080008905070903072018103121402407032011040300c0d4a000182c80e9a07016030260340142c60301011100503040040c041601031400c1e40001e000518100d804074003076800d20b280d112480c0d0000410300f10001e416006090f465454400f404001e40008140740104100c1c0c5030f041e009620240413408402c1d40329601d20001d0302e030285 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 775223606 1250 775222356 775222367
    0xd231201060210140f0c040b040f0504050c0901020c130e07080703060e0a03020d0807050d110c01060905060a05040902031903051306080408093c1207030b04140109060f020a 76
    0x3d01da05482428151001da54030406141c4990000c840699003a0a03201d0940442c1c2a00494100c000d40600019020410415180602084800441d401d20041d41c440c0c2110003a40110b5006030301507071002281344a80c0c0b50885c07d0704445054040002506259500b0003443d01800340d20510494004030000d005015160240f01420003402004080d082c10a9500941d02e00d181221481084511404910000c1c850300031650070b1580d4401c14841c503211101810000c0c0c0c015003a90a982d880c5c80d8001607010540d02902d80b040c80000c2414a20700d10344400c0c080070b80140c9208a030715008206001c030890028503a4162410b029540d110b032100052032a1003c0d440250b0041010f101c105010040040d9840042300c0756428150380d00c840074030700381c400c040b09050106c14812114047c003554642c11400c44400600d05102101d41035603202075640342d542c60705001e001c09000c0310304e107100140104500c1c00c21007002240352000040c61030a9038170b8403c21580401103d800c0b442d0005801400c0a41c0315 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 775224856 1250 775223606 775223623
    0x9030501060b120106050c0c060729151002030f04080703020118080c1201021b0d1403010821070f0b040209070203030f180f0a0c030c170d2312010602 66
    0x241030043c501400d407800f640c0090014803880c4c0c00c01500003038120b1420340170300c100304640c600a041d85841303a0040c6001c296450500020809441884031101100001d030800240a028501c0c80c1c031007960704440600c61400a10900d071001c2d44010450050303103c100034000c00003410004098580c03142184001418042d1140c501c0038407018625043c402440c0106515038024021500e480480741d1021410303000e40a59001c0100110028507841210080440c03803840401041c3e80d48640e6410581c0302c0c0c0843d01003030180308125444401980494400d040ba80c2d6840d600795460306042c0416503603054000d1005100c00c48690032080244000c6041c0058001e03003084160000d141546000a480950701d10000d100740010a518201c80c80d6051052180412040448007925401085400e0500c0d04810511046030204051100054a113040d41e4116281c80324842c040c25103031001b10007c40d03290501502100021f1403113111107049120040083c101840328104190700c56141c02006401c2035200c = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 775226106 1250 775224856 775224869
    0x313150e0a030c14150a02070501110f060c091f050702030d0305011d041b060503091605030a0b070314041203110a2705040c0810050d031d0f0a060903050106 69
    0x464030501c001040d283d070601c2520813008140203140303208400118104012031604000000c00590540c00a6000c5a007030305551082e07c4080303512442000460b03031b41411009251040d08024040b4415855500007042c01040003481e030406090340f0f070801d0480428000c1f4071404204d001032010114141481035203600c0030340e41420000c0d9803500e0424040c0071001d01022011b82001c2001604100002c0324558506559807086240d444e00d41c403028040b0782c070a8481001c0780c4150321060484042844c80c40e000c2d1003028001e0a0150165650b003901440c001c0e2235402455110741c4072112045c200380d4950702c15401410500880030b042140642101c96188000d00d10020801c515140d450b0030034684544013002091001c138039000c5511540501080d40c014950007801c044a50b000d40741d00041143c01603495101400035640e42d00200094050420402408200c0c480c042020140c100d094004843e41d01400210800c12074600140d121b00d12504203102089400d1030500c1070150901c01c284c06482d2 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 775227356 1250 775226106 775226119
    0x1118091c0315060807090803040f06030b0d0503040b070515040b041208060f01050d0b100509030609030315090a0e07031401060504111e0d110a08060d031205090313150e 74
    0xc01218550070464240586818810040f000c51784180c07142c0c60b0507006214590503251a180c448440fa40c05203024421800000d0420000b02e041d8030b4401403106c070340d07588100290700e007510300500341c4e582c0c0c1c00090381034490b401091000070070490301d80c4102e03100b0784c440c0f86030307107054641403030301041e4030f80500c4441081142500420103103480b91162108000001d00f040b40c1c45100114901c005098041e010a400070030254202643d540c00c0300142c6102c6000701c0503942282d0799403404503641c0c0402c40c0c04030007440c040000d155482c00c202c2e120a800c0350b8103580c0840c2003c240c2032071a241c10010380c42103580c142c50318a42c030081c120030f1148070068201220203000d220b5540c410b218082c0103451912018001301c01c000c40a0070480412240749140c2007505100503d90380300c140710342e9001910681d01283c10480080c00e0f40c0f81c041e18003010603506803038418100500d0454840103000003040000c00748010403000074034441c0c11540b07030020700c0c0b00c40d15403030003440100d0010507040512a442e4007408 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 775228606 1250 775227356 775227371
    0x15050f0c120f0a11130302010f021609020f07050d0f030506040c12020d06121b050d080d092301021b030c0615010201020d0e01020a091a071118091c03 66
    0x10300c040c4a800942c102803031030a64559103004001080107120070025075030002220018106110719800899000362114104100d5070601030f41c0b10b407911040038103508508102405000c00c20350140070100c001c60641c500f40541565013a1400700d010001001040203144005529a403600406034000740c19a401c0c445c0c0c240c20000504207440e040e414518050300030600c104441c08a03030207840100380c4080110300141c003034100410b280c50a03103003001c1c4a45103501c001c100c60500100035104290700c141a1850300003902c142c60000c2030664802c40d03c007500c07088408c843c2038042280c0d4120841c040001695401c0445030b0070043d0801c4491925250014804040900004549194404c4010400340e07515224000100d009100c0d0032036038510640b403c80c040346e9410303056029080c0b0304501e4803128a090340302c001425100031034810030308110720100314840006182c0128201448000340064041c051202243d403c9501c2c100c0d007103402070740101c0c1081c50240003191903040070546800d0411010 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 775229856 1250 775228606 775228627
    0x1f051f08030d09150c09080d050a0c02240315040f0603120807021f06081b060406030c030b0a080a20010801090e0c0a08010b01030e0312010e070c15050f0c 68
    0x9015505500036915940c10118040c04500c01505040d03140f136500400c110902040003130042e90fa940507100280c881c0a410600040c026401c0f92406034481c3c9a101c2040c5d5030b5400c1215004403003802d40070040c00a01c0c01c0401003054800f440c0103070281804000101851814002100c03842d001031201d142c10308104002082c1100d2400303030061054a4048501d981d80700043e46040144a8800021010200f0018113103d540c0c5c0000290780d11401901d8070603000b009089448401401501e40c8928200800c02500303019500c1700c030740c1d00313040c0c20080780c100d030a0307c0060608141c030303844000182c0042d6148010403801c4081d007800380403c01a41c0b40d01e8482c0c1c44c002070210105010f10428140c3d103000406100c9400c01a62084c0075000708040c50003512031071241e002e440c2c525031260110307041442d0044940e00204c240e4041803d4125068045d0380b0344500ca8a4002025060f14180210143c1c803c0110f1051038169040c918a80004103180c01e00580e040c1e900d40006001600810003400b203403862 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 775231106 1250 775229856 775229863
    0x40b03060609120f0d03061d01091d0303090c0306012907080f190219051b010e030709020a141801034a07031509051f051f08 55
    0x200d001640c1c015124281000841c804041d52854a1054820000b1900c0041c000040342d101a14003175070284401562a4103210044090148040700c03c10003000520000c440e5620481c2600003181c0f0b200015803600030800d0841d4420348030300300c0d0754120712105505c500702009034500418004642c41a5150b028180c0c034a0358940c4103061742d00105c0001c03404207100b103c4e000d940c16420744c84c80e02c6540b8022140340f8040020141040000b5020f0012596038481075841e800702c0894104001d0000020140052503614400408103814014407190700d90454a0030131504014140b42c45005030b0360900044060212400114461840e605c200101c070078101020034200c90b1540c0a00740810b0350070014101c0700c10641400045e40c1c6241c440300c001c4603413521005000c8a48000141d0f00c446d074444d014441500c3d52503500024016092091031b000030113209522560701c5500403016142244d2404450101c0c0d44861014925442d440e0340a1220205035455000407150142c0e804410b16850601c201c1e40303 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 775232356 1250 775231106 775231111
    0x41e0603030915180312021f1b08130b04021c0c090f02040b040605071a090d030b03010209030c01230d02040509060f010e1314010609061407030917010905101d0102040b03 75
    0xca0101c20000c48124000c200001c222204400685190074206208d07800410500c1241007690780003181d40808103005141080c0600b80780208082c018542e500d801c43c0d03d5901078400c980088503886240c1d5428420101005d00c0ca00c1030b06c20b1742caa64603040b0a40c0c261000c480130400f0051042004014266080c400c2f02c0403a400c80c02c0c800c0d260346150400760380d90040c5100c400406000c8030708102c05104041204420782070710352401c0290910700420f0500b01d0051400700e60b0541e1200c0388440c0c00750b002e0100048480d005240c903400304449102401503a40060a01510f144e03000320701440549040042d07542c0c050415100c1d2180c00f01000002003e8070742c0c41402600500c02c1240d400d104c50695080f034a00d14100c0302d0b045249507592403001308070f00611700c540000034403840c00405c000c4211800310380c0d0250b0181d031400c41035400c100481c4005c0c4145550b55245669135a02d503c0010340a0140b68510011801c00080c0b4001c3c070104009034a018020f801405d034410001803044071000d4059a4 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 775233606 1250 775232356 775232363
    0x8090105010f051e030a140d18091e0e060406050603030703081911040305030d050105190e0a090506090d0f021513030e09131e030806041e06030309151803 68
    0x100540b5641181ca120000401e034400d400d40981140482402100362265100c01c03100c00071507e20640c0400211290315107114841270180c00014104100022904030000d900700180050702a01c0c0c5602d246130450766200e1104d8100d0b000f2104100600c0702c148115940120203502031494804035940040116000074600300c0d696039900c4020b115035002c0e901240f6041d00502c2c8065a1702d4590034a559030b03402010441c10010704000012695041c10030780407010513404c076124034502b82040c2c6442e10000c401000d076008075603030b01d00000106400704a110b000380340a001421000005003c024540d50021038003605541c01618281c2c60503518007802a40186ca000d040e080014007803030211000e00e0110b800c05e500100002c10b0148020204100d1a0000d1141c034103407119188408a01d0303441c09038228090302081100e4009050360a01f50031400c21060001400d8005d10b1105440100b101e8194000b030300000da10312802c0c845c49040300c118003403490131410300e12040040c0780300b0b000c0781941c03d01004 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 775234856 1250 775233606 775233619
    0x10f0503071d0d050102130909081204060207021512010603020c070608090f0a0516060f0801090f1b0c0506090a110d030306080d03020309010b0a0806070c110a0605030708090105010f05 81
    0x4002154a010402ca00000040403100541400c0c107106010f5040701020300c040c0040500c00040c0364115120f04807442c0d6015201c135062284d0181e501c1c81034900240140c0300039800b000b884005070b503003400400b4005803c0f45036544420600c5d440c0071240c501600410b05241c4100000f10800c0800107480782102c01514100d0040d07a5801c80c45400c109092807a04054440c041410040080c0403d6084034602901d081c404036541e1610112141d40310901802e000c5444003005200c1c0b00c07a00e4000e4014081203803004904103000c085c4000402402c0e00c8a100000da50f11071520800c03106008490304201401c000b0190908603845681901910740d40292160010120810800d4041e401001c001e004c5242503841003501504090069441200e80030307aa0b503e07220202e000d40c6401c121946c01e40e80d024008100543d1a0682a80c5005940c0001d0b00e102c1503272400517905030354221070342c0c02a00039682c5007038503801c3c80710024214405c041d00740c0180d80d0400005100f042c058107070b88c4044800490f2135 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 775236106 1250 775234856 775234877
    0x8010509060f0612040602210c040e0921090a0f35030c0d0f03020a0210050703060f080a21020c040513021c2003070b0c0705210606010f050307 63
    0x241c4079210340303913034034034a559400304110078044207178080c0c51000d02074810000503c0509040804400084030000701043c1c0c2480144540301d0009004d69001008400b1101100e22500d030b4143c100d0080420b042c0d8110000405601d141402c80c4040010301104042c03000c02c03400d207500b140509503030301e0040410001e00d810404a25011401d28a07080b00b042e01034a40c3d03045840405070312500070043c110042801490030f04005440ba108589420f082503019210419940e541180030703000c043d00310070403d43c80360390208154204030280001047d0380300045c16150450f1030b01314032215820300c0c1e4030881c84000c60107207050394000c00d10740341d81602103600050b69502c0b40f907030b0144440900c1c40070f0b420030f0041107e1300302c41c003400107249416070151490264000c0c21034101c001211050300050b4258000c0c00c010801c0e84170b8000a07100031107035001a11149a02d803070104114102c00245800403920700c0c0000032200c1e40a12485400c400c080ca80f41e0502e2000c040f010305548405401c440820050045 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 775237356 1250 775236106 775236109
    0x503032b0902060408010c030b0906010f0c140106060302180d050316020d15020a030f0c020a02060304230615040603230f07061d09041110030f060f1508010509060f 72
    0x581d5031a07038020a4a40c0312501c4001140c0201034103004280860f180403031725080341c9842c102e40740c829407051b51f40681c540740540048459a00003201181c0805944103041c0c0030030000c0c01008040c01e45550016210b030320000c019040b20103010040350080560700c1c1c419010074004411260801482614000d20b2440c1c0c2c4046440c00d525414060300c04681c8c151403070143c0329990000d11100e81503039030a2200281400c003c0341242c0b0510814409039000c40400e00040c1000c20280d540035008003407044c042c5250440e010580341030b04401d0005604004100601c1001d03202110940070b0b030a55080042e41c3c1159161250300004940b2005503510000104107691303000c0090b0310314034140c0700548891030b98035000500320701c142d001d813080d404400c3c0045a60505002500b24400c0c3e0708101c030106041c60800a00022480c0040c203281015241c100240364032201d80910002481e85100b00aa401d20309601e1040f05422a0f420b40100440030004200340d6444d0424035810003012100205481d43c40350 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 775238606 1250 775237356 775237361
    0xb07031b080a053610020c0301150e01120506060402030c07120306051809060a020a17070c022d0402090d0204051005090f010812130815010f0503032b 66
    0x4014603915000800c890500d9001002c2c4c100e9060090f2000506120701a030745410b2403000704076002d604241040d441d120300d042d241120f030306140350041d102d00c02c50642c04030303003910403101c0710900364440311703004211780528044000c0c010038180c0f50800c80c10703241c0d9440350780b0b4040160103107100301c0d00030003c1000c08006808840103294400a20b0b0707440d000610002d8058001407007024800c003501301041c0c2032151500303d0f0724820020600900001d80d51130080344001d403c010002e000b0072481e68149226515202c0c0442d0103441183c441c840080d19601c100300032a1110041920411030306150f0b00149480182071404404040310302584030800000410b40f4080b0120b8017950241c200f80602c03da99070720543e04000c2d51000e0750414201e60341e124456601c0b520a208003001d952001c02500c0540740c4000140503503014902c0320740c1c3d950381d643c0b076018900340e850f406100c001c116040040112a1707280c5188402000142c02443c10620b03200701281501030008200007200160305a1005002400da = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 775239856 1250 775238606 775238657
    0x20d0c09082407111e1b010507020409030e03030d0f110c06060108041407060804050d14040e040204090b0a020901030b011e1103090406030f03020106080c150c010b040e03130b040b0703 81
    0x2c40c100c40c40142c080d42c40c050044090703e130851031801a001ca130000700c446c01d06000030056060b1603442c034124481d0700303100043c54039400a50030040181069a12550144010b00d030071a80c92201040381201420724900303c0e01020072512a8903000c000060701800c0101e1020f50000c0300342000507a655450400d1000c5801014000441c0d010b0000302150f82d5401200c0140a80d0054040710609202842c05691420b04103240480d014010f120800c01d210342c21505550061002d0004544211281d8480310848826070b5200e08007500428030075490b5a0501c00e00b90340d814246402c0303e880e0040030b12014111240d084c40300c00c00c110382045041101c030400848141d8031014004225150380c030705000c0d449406d840000c40040d420468000b40603000059011002c1130010314108030541c090300d400b81143d200b6a00e211441d52502c0e0200150b070b4440c0f02c1c241809965801843d503544c1030b01c441c24080100c94011582c40d00c401c2c00709000d65100380b0281da0703003a43d240c02c19040010f0041391241076003000c3d = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 775241106 1250 775239856 775239887
    0x20d03090f08071b0801140f040b0105061e070809040f14010b0706061a0301060909110a0c14010624051e03040f0f150f0e1f060306020d0c09082407 65
    0xda00009600038154400c14464030110209603c1e40c232082600340c004001901c0107860350320300d4001400703545404d038000c0400c2d41000720116903080b201d6401d11165048031500b5160007070007045100060815000b070103055142508100084071092170b24a84084060058110751100441d0070020420f440e0321041c06485200b072404241c0c94920824140c5600c01d0089a00052440d1030000c2d00712018001d0880c3c00f8030412800e1308003503610401326004d18490400340d5003143d80180c0604149420f10039100a400c0282c40d410380b68583c1300c44003456040c00628401009020025600e840440c0201e0100e200100705186542c0c1e200d1b400d1120741c4c81c4002e40049c4c4100f18041c81c1c03c0c10840340782c01100180080880034000313209a491000115025680c2240a5800c9074810202d9000d5004a401d070b6000e44c44400155141c4a071501012030700000d480100301650b6803000c0c10800c4c2c1240390100106890002000315144140040303104020364003d049000e082100401e0b90503004990440701c42d0701 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 775242356 1250 775241106 775241153
    0xc060f140a0912051e0a090b0a0306091109090a0e15070302070b010e01180903032408120f070b040314070f060b030607020d05030c0705010219020d03090f0807 70
    0x103101c005a001450841c0044850001450b480b10105004400342ea00140d92442d040142c4581c2c619a021a54442d058820411a404030041903501c20704019000744403550341d00107081810082c5007001c44044801540001c0703014091502c15607150100c165001002c5c903008582d0f81008910b952412481d80d48800c0070864401c20416996450303400303411790500034942c08460b41d81e103034072000c2508001c1c0100d902403240607681c11a00c20080c0c1144021600c00c5c5400a182e40000030401d60000314003442d1540c2080d4200d080003840d030104070454140d6500c0d5401450300507450b0050649110701000200f42d9103200e4001420305d4052000643c6003001d9030074103640c0701c0f0503160585a15001500c21104c862074400310100074100010b009101e500c03070360000c2547c0500c5c494181e8035900700801d840a070a00170408100000d07002e0024005211141a005000c070040300b10107414001c41072801800c042c40c00100c40c0c04680c1c01c40d03039220b0064002003000e9403280e035030620182d03055216880e00714101 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 775243606 1250 775242356 775242361
    0x1080615090111011803080717220c0e011206140c0306191e080d0f08060f0a080a06090b0702010c090e0a0207060515010e040561030c0c060f14 63
    0x144c0081405105031901d944441c10705000802a2023070560541d040c2c8041000305c00d8180c4241c4c1034002b5070702010b004100f101c0314107550303100002d0030030400d8000340d0071000c41c4808401000102c0c045c0c05a40030081c003140030145000d4170441000c0c000246038030311400c94000c1a0f0304910710842c1e03400c041c001042c00c0c01c040d5882500001074501036445031084603c035090800750301a109400c5010103285966a64000f5181c0d5820421210400c1015950001c655070001801041c10420801c4042c481c680c0814500c0341400c1c100044a8014840380559041c90301d10300600c0ea00208203010b031150000e160015440e20442000280150007008168074901028890380300d004e1019418941d0003607031001500c1c14020103110036510282c61012501894401281482c560340200380c43d240e50001e1104590410320b0501a2400096103032404402d501c010420480c003000000d0607010f0b040e900302480b20400c0c108006200070303943c420280050340d070340d1446200c2240541120f40003c0f401c4c40c1411860 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 775244856 1250 775243606 775243613
    0x20603063f0f070e0a1119021c0c030305180a0c03060501050301140103021203220e011d041101022d0c090c0403030309050a08030103050a02010806150901110118 71
    0x21128203030010724079501c0d03124840c1201000a944a07550b01c0c80d40181410526102e200035003100302508095481d61101c8070009030982039400303085010b0922502e500711443c1000081d0030408000319802c40d00c0281c03015180ca080c5c000c011041c54a0f0725141c0010541e980b500a010600ba600700c0c1d40001c0d01620200c0300c01d001d2a141d040054038081c072003c102599072a03040608031102089181002c0c00b0000c01080545400320b00d44500304038032409c0d24070b400c0e450120000c0000a189092001c020030600c00c0c00020a58102c05014040a615064014200190030000d0660080c0014500035180800c00c0341c1e64400d00110b844807606c072800350910710189818100440e00c08a480f40a0b202e802084502c030710b01501c03014003800007140e11520700b03170131524201c0180c00c1010041c0e1b103178800c0810010005600c40d00440c002d40c00755010742490040c52000512a1202034034042c4540c103000206080e50140354101d03001d9403c01d007801641d107038108510074050324a8400d40c08600d070a0850b1001072 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 775246106 1250 775244856 775244929
    0xd0807090e0112021918150302280603050403120902040b060a02010614031207031103070206070c080118051c120624020f030706091407090c0e091302060306 69
    0x1d0f2003120035921591600e0a0804155802e114611944500001d04000025030b03a0100d070705649010b812800454032a0082884640800600901ca41d24400100b60b0501d0f140ac401c0050038043ca030621182c20251001003090860b0007807114155501d085810455403035610903503d1400c085c1040351914031007203000e4024403151040a0245001c44120f8080d4174010410701d80c40910040901c0c01c162650300d003113030100c0102d101041580b20412000000d692240058001d00340318911070341c0071700d00b07104002d820b41e6070560a5400c480040d0308001d0000b000810041820320448041082e070904010b412103903140700b044440219842c100000c40c2c03011007030030300d0080d1196400d803008844881c101c0880c0d40e14581100c1c1c801e942c01c1800076400107505900901c4d0707168000c040d0700010380b0172000560f013401c0711503020085050740c4095420340d070b0750011424081000e084032415000d01d4084520004441000c2000340b0400001002600541e940484181c0714a007490007940320700c05203018810b9 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 775247356 1250 775246106 775246139
    0xc01030e010e070605031008010f06140f0a0e1e1509010506031902030c07060c0306061206052b0c12020123090d030509030f0a06110c0d0807090e01 65
    0x2904254800148010500580b1044000100105512840d060088640b604081c00818001c1e110880010f01d13000c00340241c0b18004905003000850307070f00d03003d8071380052069043c885008100800c0581c44641e140e03003030607045444140350a51941c0e640d000034030404c5c0c03452408101101000050044018110b660011241016100340086980790010008580811140f804111088a000303418019260f005183c0114042030804c0c02d098840d40d4010543d02003054060001e503842104100c0c1542c0942a08000191000200510b03410030011580d450845144881308017003103640b5060038201c1200300d10009411144c1801656101c00700084103200c0e0400603400101480000d130702c1807541500070451500e803080014039104c0340d0070502510f005041c00a0b01030100a20000e42a038605000b40c0b4556010070001d0402e00005180c000111010b542d00f4080001c0c05000001a017840040e022003100703c1418044155525200c00300c40c07605e510703001492003807402000054080111502140b = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 775248606 1250 775247356 775247359
    0x121112030d0f050c0c0307080a1803150b061806071e0b0a0605030303160804170d0c02100b0105120408090307030c171605151e0717030403080a1107140c 67
    0x455250184c2e640b106009407100084941c004001c0c0c103000801c5080108041307100e60500121592203200c07911117101069106603004041c141849640c50300e00e2140318800e0600301c6805080075580c46629040010342e10340d05000e10700000b98901440102003500265501c0d441e004040e401051401049098054500080c400d00384400402d86150110a80c3d00c102802c001c004800115044200e4214902420a0b25460108504421a04250b80051400003c10900071070880500342c8001c1c0f50520706a00a1600b62404603100750b607a07402800c1315000c44080f81d2055a9489600b4015154807419400640c50301c0381200000c100130481c80361000b11910100e41160b0001c451103415250001240e03100400c0c51080c800b44990305c5c0403503400020140f40f0014609010411046003441a4640941009c400e0007240b481d080003035440115160520042409003181415540a030565001800c1106c0c9540c55000215080d665030086daa55248c000b03140e01c28081245044545840007480840d = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 775249856 1250 775248606 775248611
    0xd0f0f0c020d0c1e03170c030709060503010b032a04090902090c07020f011d0a08060f07170114010e06030f07030e0c0a030605040501180503041e121112030d0f 70
    0x60304540e01603c40d102c52150403003404c44078443c81c1d5509a103440c0091800b182440750890303108200400c410151032140c42a0200143d60f41001035001d4050200383c0d00c403904202c002c10051000805410989400034003100c1e89020018090001c03034440c083c00456030324074080104002480d4000b6030480d0030090700a44040905480c0c14a10711f03181e200f00300380a5041140103480030701d0b5500c240c5841140a2284020141848031403001481303001c1c041d403240106a0000c001e105c0241e16000c2c110b5088010341c1464600d29006213200c020b054014480c01c00c1c03011460340d44030728603401116204040d1100615003903503031904000301c0134038020a0302c80b1000030703140c036003030080c2d4110000d00c0160880e4024682198145141d031650040c060051040b1059501c070402501c01c000d100d1058000c0d44e1040c0051901e6504110014100052841903075040d61400b08041182c00080317000d802409400041401810204e0300102c2c001c3c52004101010600c400500c0c085044540d6000706c90014000034103 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 775251106 1250 775249856 775249873
    0x5070e010302040815060f0d050105090124031707080c06070e0f150f040f0b181c0f140303010602010b01090f0f0506031b030406020c0c0405010810020d0f0f0c02 71
    0x4400300d0146016081c030b594041c00384c800001c000e00080941c030190081081900704440c1c0e008c40c0039100c0840d8100c40c0d40c0e45031000d0021140b000c0c003a00505801e00603160a410000c0810090b9540d0326100280146210059031080a00d600e803c5540c4c0303e40100015070344d14818070000350307100c1c000c03a022000650032821000745482e000040442003000100708080310301d1512840801640319454480d9010020000024108590a0240001c040501d035445d03d501201c006085031450582c07541f07102e9002c110a00751010003910f0160390060704010071102101e26840c0006902d1420701034070b00b00344004000001c0d61a4150460098a6801ea90308442103540c2d68000c001e08207540270f02980c401814a0a11282c1041c1010355406844004568000894184000b000e40d009481c00e594503500052075085030101005000c080017000c0c1d80c1041150b2402900703640340c109200200500c1f03500010711103005402a08813001c0080303032040811080c4070940240b0014032000001c5809400707445070 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 775252356 1250 775251106 775251109
    0x6020105060a0e1f1511191e1a010e07020705030f03040b0c1912110609060a0e0102130e090f0d0c150908070605010504180f1419050105070e 62
    0x210607088075040208a4450f4540719190040c07011080713142d86159a00e4440083c08181110044620040503151202c003050000001c6090108043c1100c0c0e8a01103c211200003400d035075080c0001d03c11102806180070081d20700341030411280629000c001c1d095000105c0c6882590004501510300f903002c80701c443c3e40d034805040d10b901d200c80b0f03900c3c166007040c0030810003a2018001492101c04500c141c4404055041e01d02e07078002c00864090300e10710f590210b034050241c0c00c8002c880d20f005011004140916201c1d80559031030400030010100d642d280e40c00c2001140d0300f501502d820740c01022149241a846100d503280c0d44030100e036060781a10038201c0b81181030001144100d01540155aa4202e4a5442d203421104000410304030b240346669440381804181002d02414050f4451302e07000c2450751600f01048240c4004109104060190441d4000040c5610701804c0005074030001784000a41120003041c10481d49041e00c101d10181c0c3e0942208000041d441107205010300d40362045042c4c40c900 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 775253606 1250 775252356 775252369
    0x91f0b27130f1101050f0706020d0c09051f2a0b13170c03040902120a06051504170f0706110d2f1c030b0a0e040206040302101e05040602010506 63
    0x20262000c480c042c200c0d0041080d0701d00100c545107040c10060701d4050310840080940c0c0c050001a2307403084d808113101070103803264000c500702d80d403403850448549410000010f801650045009141401401032510514001d455000b81d0311705e10784600113030410250500040700005036007180e80303050342000140703c00c00552007081901d8120040c60740c104000300c3d903202194015040c1c1c40e0075200c2030100088030407d5000510500c0007854080e06282002209841565250f0700418401d000c820710348640c00165009031011950040e1501042602400c0348a041c9200c2c0300c2c8161f0b003400344140110b00140c00c0b481d480200c00070541150703c0e1001e440d00807928011151131541d000e01e1076502e482d107424606800c1b07140324101001520000e00390400c0da540b2600406044c100820785542c104a91840e064208100a180066900780c0f1407415900040d200e210700e02000388282c009012000480748624496200754502d40b58400320540102c0020b4403540180c1701d104010744c01d00c4009a644c2c03e240707 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 775254856 1250 775253606 775253641
    0xc0501061d0606181203090d03091401080106020c0609150f040501080a090305030628060906121103011a040803130e0106050711040203070e130e070e091f0b27 70
    0x138010201900160013009074a080b8944449140d120600c140b800c2d81e42ea0184411850f03201e46c40b03088095240c40403480b02c0500795540d0034180410400100b1500c0e8012a1360b400000c0c0444105648583e0080017a805406030344c03501918100c0400c104808100078002041a0b4600340c80d1040659a02070400c0190f408081d030013000200244040703100390030161407404c120260ba2104480101c094184150760b4180c5034481000590410420400c3c40c1e0041d54060001d40740403014030502c0070015444140344412310440302c829485181c0700c05260000810b503409001c98006581e80c8403492001010020050301443c0c101501c2180005102405001124446035119a00c0c0311150500c2c02048001e401c000c0510081c01b09032082d003807030b90f500c0b01060340ba56442e002000402c422a0186280307009000d400c03604849054006004c044103001a41e65080c0d006200030380761040203461104040c200d080940b50300b1444d0742c140101c2444040001c7c0050f1030940326060701503074600040884c0756008 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 775256106 1250 775254856 775254877
    0xc040b2706091f06080402010c08130321080c0a05040b041e21170d1d1506130c03110a020a0302061609031104090f050a17070b010b0a0c0501061d0606 66
    0x4480f820412240100300441d44280141040110042180c8911149078843d810417000112458418010030141740e0304180355410744c0001905d202100a03024000900c0036008590601011410f10f20081c4204206c4002d0162550701640715036403005040c244c07040103240d118142c400280d000c234800500401e0010b505071404003d00c80c280b6030f61a809500742c4500740204032001c00f0429021949514019010500440b00074104550382441c2c0081c2010343ca00c0703070510a80300c0b820501c040c41d5640c0d5a5021103030100b40c0d0000e045000d00320190b008080d03c003000403068801184149a8907004030711103003c140a6002d4964603503030f14a2443d00c064803041800049940b9113800d20214181c1900c003034084001074000101c9045c2e030784564003810414035044485a200f40301c41c80c10000603860b100a85604880c51608025407980d4040943c0014041d0390030702040030038040e1070144035100000c109a0000300070041182c82e51240398041640805031051107415801040c1a0b041540032210704215 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 775257356 1250 775256106 775256161
    0xb060a080f07031b11010b031b040506060307050906180306040b34030f150b19050903060609090a0f0602040f060e0607080901093201020303090c040b270609 69
    0x88244156800246000f400745d16651ba500c04813855201040f078000d045103a02c51202c60074500b00304120075901c005000074010101801407050f16504030041d03a079404000c0714916100c03001c0071804e00401d40c541c03440c968188505c0d000d001c00d01440300182405220043d2403203210340c088189401c1e1072840e13804400340c4103400219a1030302612941c041c4014840c0700c1c8020480c030301c880003070014078003680d004210b0b03e81c2d00041d2a0494070b00710ba680c0c1030f00315450806a05144000c1d0004cbc2d00e400700202110b000380341d82c2c0c0000705001401d01c13082c94400d5022030030504448090034804025081401250102c1e08484008200680225170300801010000c1142c3d160001d141d48800c203503002140803a05206000368007096810f000c1c12013525548180c9030005201c1448295120441c011443d030a056410400510010a801254140e0552415903003c188080b46001083d44074900c010b4289c240d08100206040481d070406569000e20000c1301c500023151905418447c1c940d00000e42201c10b0503 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 775258606 1250 775257356 775257401
    0xa0609141b0603130c091b020706020a20120a0615050d06091a1503070501170412050c19140c01050a1b0204020c010506131107150b060a080f0703 64
    0x10303020000f0756100e10510349445540d140e40e81d030090b41c1295904850002030b15400c022859405910404440e051240300400141d171501c00d0294440c80002070260501e426001d01140c441c5610084e105d24440c0541800d0104e51010181ca440e25074900007243d250f4100400820f80401e100441c0040c2d03174004040c50b55401e80c81d80d071700b0018411031000710750b0541303030040c03881805910085543c8290030040c202210072007071070100760a04029412041c180302d100c9a480e50400703111248140d0007540322120010060400d5000c0c0c038940161f4500c1c414505c41e070b4603d04e02c0710400d081d691040038440c0c2000b01518180000c0203440b0386501454500042c2e0a01c13241c158248946440311581142e0b40242c01c14142507008074059074000b802e213000680d10f50041c0300706400c101049003840b001d0700d40c040100303499421420300c40d840303140300241035648140300c1721704043c1066001140541c0010140c594405020f900a45803a404860310360448100200084025009000b10100d014806a6424402 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 775259856 1250 775258606 775258609
    0x50601050d09020a05030d050301030c0801180312061e030501110307050712030603020307030f12020a12050a090902030a052502030901110f01141b0702180601050c0a0609141b 77
    0xc140702c14060707130301c81030744040014503071400c1c820a4100c100036650700b41e6031340c11810078000501180e030280201d41c1c508498000d0402c20300c0d2890003025898901a690020600e000384064405600f020704c03281c0d4031240d4401900c004108000c2241d00c101d00a120342c01031a080001c1c0d9010488080011490801100c40040c00d582c0e0208203040032401c0004d0080c0d101d4011a24206a580007207500c03005c2c9211440030311408a60b08401c9070030520090138201080da540b0070720040610380a81c1030100c0414800e603203d0180544801600c8003990843d160b1411a00d0304010305000c0d21260075810344410445450f11a106007000e14090303a80080d440c00000d070b00111250094590002032074003890a580c0318a080078040c11a09007810b40084c000c2c1c1c1050380c10111800d10b603944000560400300604c0006807102c460741000a0641c0c001640300f90340d00001a01c1c20f1051240951140c00f90810440401007243e2004201e035018241a0a00000350f10410342d0302c4290420f00c082c96035500b4a0070388503 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 775261106 1250 775259856 775259861
    0x7020f01110f030705030d1b0f050307110f011a10081f08010e010e1e1e07080f0304030c0902120406090303110c070e07031b030902060f0d0f0f050601050d 68
    0x5441c50305048540312030401c41040e040d60000389046825400008420001040380e0041c200850704031003001c040403074003902c0030f003500085070b40e140140900800019500c41c01071401c03040399411302081d00d82c0c120741a48854000c2030202100458200048520755040c14030540503100740c0c3d40790300d44505588500b000710030001d00c0307070000a01c2034112020128507807000b8026034003400d01c4400003180030511010075070f040031a00c00421000600031906030b0204035002880c10921112a003105000651000d40a401d24038550404209071003102c04c40c4500d84d030300100600449001709000704004d515101040245c0c41000880480c1040d4400407078041201c42d805461207500c282000a045102c1c07150035805900140d404c03240e0380d00a20300c2004240324803a8500d5001160307141c01c01c01c100036600058281640703008210304040e561440b490440d1109030845100340401c9015644820740929801e000e001e1021440001c40d007409407980c80744056001380f502509050310f8260078a20024a50b200 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 775262356 1250 775261106 775261127
    0x1060f0f032403030509040e010c17090106080304060f030506010320090d0c1202042304140316080301051201140105100c0c061707020a0309050f120f0c0f01030207020f01 75
    0x1440041e828074000d00d050b1400b00140214800d8494a8803400840e040204440b411002411180d04011003480c0c0c145e840700b201d091026041c407441a01351a0b0300d401c103005100030303080b4144034400014046503068002001d40103640107545e00b0302c510b40c0c60303030300460540f52106169a039405940a402a0a814903030162050b1350001d01120058000f030744076100c5075146a070180e54444222240c4c0410b5041501a0005036421144c03408481c050601aa11402c00020000352550710354a03001e403d400405c1c011200707891107402450341c0e508003a00b000b00250340f080c4501c86c07183c003001d5a84080740744180200545000a0800c00c0010b81c64002889046c115101c640801c02610804042c005251000c02030050a1a595001e094600a00700c00e96031141c00340c00c2c001558042180c0c080042d42c804002c80c1525800e980000380d20805101060044030818012600303030081140308030159000050810038000220f0740c0b6110003520100550882c451071002035006100c4040703250155000e8010a03a = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 775263606 1250 775262356 775262381
    0x304120302090907110d030212041b0b030403030605040606110a08090a0b0c01090303060b0f04090b1f0309050601120b0a0213030506070c0b01170c190f0f080601060f0f03 75
    0x62410340d640c07002489020f022a0710f24003281d07a4428100340321504001913084400c003410110314004030018000200c00000b0002011034414407180320b101f12007421610000c01c03a1081007038407410545805000382002d8001c080c0668548000004c04c00e1055440340b08001b00d440103060003800e180c44030103040e0301103400182c22103821032001640202c008020700b1035400c1c500c00000ca0305140e1600405481c0f03258805401c1c01001d008081042e040034007264129015000000303000c054400116440f0010042c2c1c030303000481070288200d40c0300e4041c0c01c2840b1607032207082550b41d5680c0303854070764010310064400541101614400100d04000da5401465500b110780d884140380c991f00d5a400c3e2601c0021034032400011480481c1d80d04000316080c130913001d4120071007101c01c0e2900070034a450ba1801c89100c0503104541603007040130155060100d000181c085007800358000c4c0d8848900c058210320612401d0041e00c20760000184680c4959840d01000c0c4140da544030039040f1541085001e480e1080511 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 775264856 1250 775263606 775263611
    0xf0c020f0102011805030c1002040503030a0518040509060609180d08040c080703140f070302090a09020409201801030201080c0703031b0809100e060a02070c03080d0b0901080c0603041203 82
    0x100c4c280003045084000c01803082c0000c41c4d5800310480c4560807c481080c000500b82d0051000740039580d408002d440c0d888080703141c80b9031508101c0310340314950102100c0154020b403414041c041c03e0107001c6405480391009441c1e018240c2c03140307201055211041c048028184e0800085100990b100d000b0b220307040b9008100e60040161079581d450308001c000e034002c80d000112800444a0313418280040740c00030428002900100345182c010886090004009401007030f920030300302086503282d42c48101059005102c41e41004c1c891030809010640648084d03100300e03402041311100345030b4510441c0c1030301d90603552401130b0340352902e000c0380a80100104130181912002c201070032507c000700d0b90885001d6036445010a05150003a5030901c103072403420840060801240341111403000812642184c07003040c0c01a034410352070500d0040c0f6081ca80008101c1d4900007400ea5120321300341c22a180c40b40d000c980b21107190346d0701c0758a1540d5210701000d40b0b4001c03409000181c0400c4000324103510799074480c00e01 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 775266106 1250 775264856 775264871
    0x206010b1b0102041802030708010f0e070806130c050a0306140f0103020c0a080a03050712020c0715090504050a020322030212280c1b0b070611130e04120f0c020f010201 74
    0x32000f0b05c001c152075240696174080b00b0007000e2648040c1c4503004288454203002c802d400e1000d071600392035005014605101400011890a84501c40403e40c0a0888a4200280c1d00184002407055000714112000607040801c04500e010350019a0b070354000008152101500325007005402940060020160a0260b9020b00000c1041d65000300110307030342540c002805143c8003c0213000c650408440d038180c6031051080000a880004203101528810600600340b0781c0d10210807076204d459a08040d402c0b03800c040902c40040925000f0b580a00c01d00d03105024580c420303030920030315641d6800300940168040c2d81c00c248500300150040c0600d41400c0685211200d01c21481680c0c150400c0300140050605c000090902111801c17114000c005d1003500301c602ca140c1024407003a4080d480f006044d01c0c0d83e030142440000c041e0f030200c80b09980039407813030301600e030f620203540c251004110307010754401d640d499800703480c0740c81504c0c60781d42d03d035094444001551042d000d01c4151005100000d0541d0768030002d = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 775267356 1250 775266106 775266119
    0x150e0f130204121208010e060d02010c080d02120a110a0203040603180b04080a080703020301050f220e0f07050103180b0619140a151e05120717070206010b1b010204 72
    0x10014403441c05024243e00d0b0b40544e010040000005030311283c007000c0c1744414080b4558610007102d4403d602480c2a4142c000325007030401041c8550481c44400303510002c1c4000c80a821403c0c0720384900e02e2102c0400c03101c00400b802c6041c40c41010340050060300108020b011080c00f0b9809500e0001c0c100e201c00341c0c050200c0da900c01290b1010b4405944c00c0c400440e0780c01c5a25444840742c0d911841d5071800b03605552400000c04e45c01d007c101a520f1080a034140e00c5a542100c2d03200f4902c081c10441000d100042d103040d49a52101c1d49442916454022680d001c03a90754007034094206030003c0001d040001e2446511915280b00c00078152503407005109008550804101c1e0002010701664078003003003d0021030b0308101810711590b001740340f200d00041c5100380140d084421031140543c0c10b04124140c001c240400c581d035104002403445142c0301d0b1002d0000c9103500114084001c12125051015600d40e143c080e0303500c0c00244500c00d41b00034100030501d61110b40c8550b50f010300d5051400076040c56150031 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 775268606 1250 775267356 775267379
    0x18030c0a05090103120909180b1503030a1115180d0807050910020a020d050313300f0c030f0210051303170405040216051203150105130503030a0207150e0f130204 71
    0x208d500584c001c410014070a94400603a0483d021800c00e0743c1a000350404a41c40f800b901260b8400c0c00000c1a008207094014800f082e6181e82002d1041d900d4513044c0194905600f07e0600017140d13110b1303550f5107072005006144a40c014845525542c0c00c1410500401ca0880003203940d043c11401003088410041e02c6400f144c0742490300c524003568403600d181100e07450b2554540d01c50126810004420b0401c160054100b880100d025a946208c102044c03c007140c41c3c0403a110024003609039030000105101c41f00380782459540c0700304c500c41c0036124141400c991071b02842080c030b542d250510804200040916009003141d2001c076040900342956000020201e800c107418220300740e1070194000e0f04200c4c080c040300892104100381c580c19810440b003041c0b2052140501035050000010b014100f4814000d4180c0c000d110043c12039542c0e1444d14802900ca10303540c441d20000d01050f8508000c054000d0b141198103d1010b080411680e0485042203150480c11001001c0194200f001007181080701c0c = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 775269856 1250 775268606 775268621
    0x31b040506032415120703060b0d05060f122e0e0703020a1e0308030603010b060c1506011b06052203052701270b18030c0a05090103120909 61
    0x51000b03c90b40000070955518088094040348258015140c0d4a0400c03629819114001d026441d0705d03041d41c0d640303e8242d006002c2600f110011210100d81c0f0a103a91b0140c00107445104140e80d5103c0e01e50f0108280940b061201d0146100c980100030180094000c501c65594240c000c40c0303000256540c2206440200e03803c1d007034142c0b240d400c231403428030135400c12405500082180c408000d0341d030620041030350301400681c040200076410000c08500c256409400240710284020b01c001d5460b541c84c0f014590b50340d10040e002074102d018000241641d800b0b14800300441c0f40540b03101c161410b0725950107000300401001009492440e5040742a43d42d6403010a180b043d02c603480c0c0c0c40d07441c007a5680c0401405022054210304103440090110540d1b0701407440c042e9402d400d0250381314042c00703a428008401c4242c014400021020500003032040b40c00c0c04401a00000b03400f560008680f03e001d01142e030b03015000b0b645d0004039100042000610701e070380410081d242880d1000d04592294a580f06961130f4 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 775271106 1250 775269856 775269871
    0xc0c12050a03090b130b010503070e06060c0a0501110d050a05040b01060f021501120c0803031501030f0b0405040c0512010204120f0f05030304120e1c06050703021b06040302010608030708031b04050603 88
    0x217003040c0300c100f003074203400c01c3e024103011002080d11503d440b40109145100403c01c074050040407814000c122001c2054101d0036034824003d1143d6241c081c200c4080390030005d82e0000642c240000300352074103546e10685006a0300814205c02a078285081910b04048082e01c800c214030400003c0315001c2001d280c2ca90182c8101c51801a5110300c6041454542809402620782904108248440c40b41c000003003149980302801c0c0840c42048502d104401485030300d48554215042c1401c00081060300c0c0d90000543c3d408452041c0b246003a07048150807402a40070303a0300c48107941c0340340b074002ca000c4c0d049021f50b81d4030412940a039030031030f41e503a242107410641d03085030701041f00588a000942c1124030010440030623103988140000321080440fa840da00355019008542d0b07980840c8020f80310390105e40b0140028070100f14081d0a00325100c0d40c400080300c0540c0154602800421514408000c8810894200f11000e0440e140d149214202405e41c0d60200d9000604100008980c0c407070720040e41c0701c0e114 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 775272356 1250 775271106 775271131
    0x311160f021207230103110c011b020106120807050102043f08070f050304050406080f06010e06091810051305060105030c01090306051503030f040305010c0c12050a03090b 75
    0x1803600c140410003200c03045000040d0422002881030440ba00e84410078074404a0322400a00702e801e0040c1d005100c07218150005402c0012200071017401500507035440c022504001080e43d4010b0b40c00c03400c8503540d0103070072820604c4181190100c0c000e100649000e030b0051340014a825900c40c0480c1c0d150a490b81800141181134015410030103914018000201e444407020049076045d070b0341d035020b52141e4400241140d00015442061100400544014000c082d00c10424030740c4510700030356610402c42c541e40440c40360790700218071450f0305160607000c9c10000e0188551903c501d461130881c5884884000401e00c100c084018058a10f070280c98026489a9554003100f441c44c201b5600f8560160071244c02035104a414150a991004000d0f0440e60403000c00034142c2c461002003040300c2c040200e11645403001240c5003038a44880030003401120300c81d4000300710445000d00161000101480c000d0040d42140c1480d95195000b030004290382d281514000480122550f1007050075102540e0424004a = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 775273606 1250 775272356 775272383
    0x2f0f074b030b072d0f180f05040e07120201050f0f040e150d0201080720030a0201140114060910020a0c08160501050c0303070c14060c090f10020607031116 68
    0x25002440b04e1103250328130b2688805952061040000a00d15559441c1006420f1800c1512248200c0e402c00305040820540700c002a034600082c2020b40003405000e02c12403400310a06012100014400300700c496a0400340c0c4e0b907003001e40054aa03038129001c0e1001c111420492944445049001000500384456813010f046c1802d1050b110b001001964250007801e0b62800b007009030b07800c026001d90100240ca00300b904000380e0440c3c2d40c007440305510322039241c1c400421040320725901074012480c1548180a010078030b0f81d0390981000007038101d80c0c58a80000d001c01c1010707118140034068416595060045481900d0a5034440c65160819848200c0c6500b00f42a00300351007041140c0c1c90b000389000d2900341c2c1820400424213850744009007140b0144501d5a80c59010041c808403225050070b03041043c0c41440c0f400c0700c6121404c2c0d000404461040101c8a02d500f041c1c070700039000c031700503119a5005214958899001380d00400f52040d2880c0000c00901840141410880340346d041035114003038059098 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 775274856 1250 775273606 775273621
    0x6010c1e0c05011d040e0f010212040b0702071d040c050d05071e030201120903020c09090105010303082203030f1b0201060e060901152f0f074b030b 65
    0x7941500000d04000d0030400d00c9010008226044103003010031107001860311000103c00e440c14580b404250219400803401200490f4144070892255000b14007410581d030351138204076140c0f0254000d1b0b409012180404265102e9000341b00c5a0240c403d01c0020591502c4000084808090900c11103031903000001c24014030b0b4800c1e0484041441c0340b0782003c096800d41c0e00281a14420b43e41e0b026003c2d84d112070010505100b00b0010300e0015014250a50f203082010409000e44001d00099021605850200d040e125103030580b1003180ea403818404c0b00c0100d5070354045000e0700ea02c206100c040d6464140c3c0e01f0840b140c8a0b950300242c03010ba000001c042c0d1908000036943c9034010b00252042000030010003c3d501d2080420311208450300e440c1d00c803110010b003680c51004110503030f40c506044407800908d00c100c0004501c400300c0d55800071a9015a0f581c1c02501e02e02c030245040c2c00704010003603400d484900b4100170415055803003100340e054021400c2c101c2d00d080400365006540324010f540034030050 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 775276106 1250 775274856 775274873
    0x120d030f0501050d030509040f1d0c0d170c16060306031a090304050d0c0f090f2a0e06040305060408120c0703080403200f010f11130e06010c1e 63
    0x1444503a680a20440d850440000e020128445018041c8803000814844503504c3e50311102050345100010081a204201c40c40d01040a82d003d0703c80511960780b80240e5803801d107002500c917036448a2041c0344d06424091002803078016101c200d5030751062a05102104400700d481801030300e070070f076000101e0516508058454051031040b0080c00e1010006201041c04084211801e4500588400851200320303d08445141c900e0350004400e42049880420f10004980160000aa2029090140c01242d141500305091000a80b079a1101128ac403841c100b40102c400c08215080103100074141130b40e98503650b01340340f01283d04507042c2e200000d105031030030028107200d9003045079450114203242e060354010b40624000b510240a01c0142500b140700f0411402c008015000e000f801d03203c1c1480c0b50112a40a0101340c45a12410340c00c203500030905c4410030007a03428103000203040307030f1002e8603103180302d10329920240003a41044661049000424209800e84050180d210954400011181000240c = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 775277356 1250 775276106 775276121
    0x71515051c0b1b0301080c01081e0a0e12030c0a0f050301060c06021305040c020a05010b180c0a1b0c03031b120810090903080a050604020a17090c120d03 67
    0x120740008000d00740d0111800381240ea505600c4128050180c540d050300c1211030b552500c0241081d2030010002c2100340c40466040c103180b0003030700e030b542d099190b000e1518584c6401507615500d0000c04000a9025030164200300346400c2d008040c4e404640c5a80c005c0140e9078011124400c070208002108070505502c43c070140350052962070302505650401c1002440d4490250000d040381c0d40200e018045840400310b2440200390050040052482d0070002940b50048084156529482d002034040f5600700801c001465000070107aa03117550340c4040481146800c800c024404009a41d400319580440344612464818040d00b90350305550f1039494010110140c0310610680000d1031003400000410740c12550000d0307241e13401d0004031959010340000003840c10390320441e1001d003080c0d0f055050540040a05010308178003c01884140ea07403a0034002640304602034400000c0c441c112954001326518116504941280c0580704110941c0c000500402d8401e05549020f41010300c8112441e501442240c2 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 775278606 1250 775277356 775277359
    0x30c1509081b0601050616060b06032404053706030b041707020f01230f180a0302031f060b1b0d0c03211d01020304030f08130206070807151505 63
    0xf003503040401240c1580120160740788066107807541d03402080a1a0072803180014090300e811b4981c038103d0410720481c2c290f09074110030700b20b0021450100341410700405100b80046042080e00b0035802e8400d034610200800c5101940d9011610782d034801110303008000086004250514443c00c0c43c1c01e003d182d0300c500200c12039200d2410010140161104c000c100110082401d00885540040c0310b1200018461242c0d82856640040c424851002c0040948241021100381d1034840906506004c024049408043d40c10341c40202410404a0405800311481040d244003040341a900e03490701129400103a400507114007480c00003842041e040240f0032030b48869140620b040d840030f1301c024200b4010707100c03000c01400c1e403044e10340c08000d026049600001c2021400903c581c80d0282420700035002654111300040804003008007040c42110440e008801e01881005075110a50800807150300800c0c085810300340520011020602d04000071541e22009034010503005018004940019107541009 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 775279856 1250 775278606 775278613
    0x30f0105010f210f060204140d02240415050904240501030c03150305070602061806060f04090206070b1005100206060405090307020a080d0906080c07030c1509081b 72
    0x1080070b96950a007050480e40016440e4940c0c29111105009041074804040c01400d030420742d034000c0000c1c9500034400c450241d103203084140140010003694814402d00a94010b070045441201516489080030b1082140c2681074946030340d03020034a0b2001031018200000c0350000c030f00100760b82014000d0391001d1ba094080c0c0030a40c0070001881a1400c0d550182c2810141c0d0ba1080324502c80c0a03500022040707041128501505580e442d0560b42c50b0006d005d0f00e8018091324010801d180c060f4015440d075070045070060301c010f42d90350f401e01c0705105501b0109940310b81c441015001684641004090403402483c981000d03185c51281e104c40700000e580024050442c3d030032155101a808128603401c1401141c0101c0d05445000c01c5618500a010003c0d40c40b5032002c00000d1507110000d00b00700c03210002d4a40e0120166a80000d65915070300f207070341440100e020404d14000030301c58034a201e503007031041c02d0441c502c5440802e0101112440700040310310280008402001c4580100b0050031200410f008 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 775281106 1250 775279856 775279859
    0x40c150c0f0b061507061d030c191b06020c0a050f01210b0303270a0515090102071707093606020729060a1a07140d030b030f010501 58
    0x392840311184081c05020b10300c07a8070202c0d14590303410b03002c00541c0099a0030282c803008107007001002001601006201d440601300074844030700300401900e45801c0b003000980b0003c420701e201c400201c00411412202a20080d44108200121120600c00740490768000d150000c618824415804000d80181d44500c0c0321a4000c1c441c1c1e0ba100d0b4140c0704c0c00303007001e17118070700d485026407810098030468034410b83c14000401c05080c0c4039002c5940e4004200e50740b910810004000003884200780c1b640c0900303074010100d980f0032003d00c00060300034080c1c0e24040c81103400e0765681e028002d110100010018449400c00e85081040030940d020b400960300f40c3c514401c41c0c0134050310b5001d0901c60f20407460040d000003c403c0b101400001e5041c0c42140d038000084d910401b0b1402c00460302150060914000004114003040840c1030203810701c004c0e28061600f51008514400c0925043e41010178100c030840a03624040807001001e0148850500c5262070100707400703489104050410000840c151401c2c2e161100 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 775282356 1250 775281106 775281113
    0x7050d0905040c0840060203040c0902090a1a070b010303030b0a06110601061809140402040f0b030c090a02090409080403170309030f0702061213060606020a08071514040c150c 77
    0x1742d058142101d030095079080d42c50002062504411041d0070b0684081c070f0b103e02402d2000540056114510076824940780c00d44038101d1714201d0044d204c21a0f00950104003c2c0080681c0b20f5001807000c9005a0080c1040c40307075503d5101d254402d81044000a40702c1c0e680c1821403c0100c24034000d0b1050b400d00d0140c20034a40c400719982d0205108840030001c401c6414600440c00c0b104041c080c00300c1d000c0500c00d4800c2c2d035940045072041518204e010703510381141628810843d204031660b03844010040d0005000010400c51100c1d0058001061181c1c01c211406040d507892056014491089003141d46641ca0b40c103009005d059010110707481c44c142041085141c250120803180340441903284161600424008100c0038000c0340d021100f00540d01045c0003000c501d0803d02d44040703100301400d01011b61190400c9864081d0814000e202041c00e00c20040002c0c03001d20112101d01c03c5010020b20b65111540c0b00404107802c5d24180e03a041030000007030081e10704501010316032400c03e0900705103100d055075 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 775283606 1250 775282356 775282381
    0xf120915070c03030809191b0b12060f010311031303050d0f0506270c0304170c0f070503120a03110712210b011403180609032107090314010207050d0905040c08 70
    0x8000522108c15003035084210703203905150760043c1950010142d200e043d0703c0d684120300e0801b56a01403140091003d1401a0741c424040c45502a80e6001003906646400c4208210160702c24003c80901100384045c03004030149110300d1490105c03151011034a8101581481080c081e600910302d2030014543e010844402400d91040d00258070440c00d41d80c1c1d0340e0b241441a018008120104200200056400c42c07404001079600f22080e400000c0c0c4803000e66030403c00d641c0c0e603061107621040c80f00c01c1c048004584d01a078818028444c2040146141c51419621007020001c0b01d00d0740c1c1e0100c0c11104a5400c1c58071310050750070b01d81c1d0522004000c04606400040e048030440001184205d9000001400e030f0410401c0d0348003105546000c40d241810300c3e86201391640c002c0e030740c1d1306540e50b0305c403041a40c20045030b100707d40500b50b03d441d030185860170343c0c50724040c25030040f03401d100f15034082040000140c03040100100b00c006076541d010700c0d1802c1c00108000e85040d1f041d400d08005036034003441121400312 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 775284856 1250 775283606 775283653
    0x927030804060207020319030f0314070e0102120a171005010816051b0f01111c09080412080301140103021812070f09050702060105030f120915070c03030809 69
    0x103051404850340e0703502c1c0100203072050b50710081d003500480003c1c0881c1803511040d88001c030b200340c90344000c04560010031411544100307002c64000150002180c0028001c045407064940c0610540e090307104d60710882c0e08983d1080d01d05800055030002c808401c0602c0482c440d030040700141144910a252100003071108030090a0340702188240c00018100b14002d030b0841e206d04190125000d403075036591010903100c1208000b250107a5007414420100703c1510b1041356441e245100038401072001346040e01006195903281120016000c00c00420f00400c06645241040d00c134809140e07496040401000420349405010340c1490f00510040c8046680303080e14003000c4e841551103a00c0c0c80b018845007072414443e90b010006014903e500172880200c181c002c01e100d41d446808450040c0da96100345940e500510012604c140c11000f000070349200240001e161114000340004429008c0a1440505507c001012540c402c08040b04004060b0030181099000300c8440282034008111503003805100b140 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 775286106 1250 775284856 775284863
    0x3070506102c07030f020405092517010b0c070b0c0d0f0804050606040b13020403030309050715170916061101110f07020f04021b100e060103021003151a040927 70
    0x211405c0c011843c0c00c90341514018100141700c8000c4d4204102d10300501c103031119813082003030400c056090310300e4081c0c0198007520390b1030150082c0c10780c82e055182c201c0780c00000300c01500d80134194000410349aa200900481c0d2000006003403903900d543c1c3e002c0d00c4a40895000e0045c001d41c8420000030030004107595501500544003c1103c0c6111070000e503916403030200b41c0a41c0e901c045808401d00d03a01d503100e8801144140112a2070641351204091800e99054030440000c0b45072500080a030a40a207250b081480c00c411a80740b181116452003105403e9003040002070440702c4916140c010074016102546c8501448030f02d00b1140e29002001032207031250184c012080c8140810701ca4550368110b40000c80001c1d6a0420584810221038450080400340820141400710300d410000000c240d050499a0050020009c03840040003580030b041a4045024210151403000a0640b04200d40c3c100710346005448669480c146020300c03040350300a00c9903180b11a20300c100300d15049038010000c29040d41 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 775287356 1250 775286106 775286111
    0x801080d090905130204050106030c12090b07050715060e0402010323011502070906030b091011090103091b080304080f010e03040b03100b070503070b060d03120e03070506102c0703 79
    0x442c1300a00c0e008440080009401c1490b00000042055140d40b10003041405541e405911076414021031083d21440f0002034000d90a40010039a030a01400c01010083c0c41003a80d140201071300d250440850300390350711000381d0504440c200800c41d030f4140701c0c40c40c0c20803181a010845128500380c1c0140c2c034405016407061365140310302c40b2103401d000304003000040600807403c0c84031139180c2c80e14012091042c2c0e00300846209200c07051078a800d15000d05198401c0220743c0c1d9080004900044022304405001500c010705d41d0688010451400f103d18806440716500445d69103140422443c940590a401e9205507454803024150254011084508880580c0c0e4469243c3d00c0c1c007200d03204001d1803603110a00400000404030f04012010024010803030250000b11110707a00d10f0140484041d2041c0c0041c00615441c60600d04c440c081d612250741c9490381d80850f41404000d03507909207010410382d480411100c62074401c02c0000d860070403c6007618010703441e4094042c3c00c8400e2a40d061006400e907401e068 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 775288606 1250 775287356 775287361
    0x506120609061501020a05250509010605070303050c070b070816030902030c12070f080706170112170906210c072f0402070305120a021c11280801080d090905 69
    0x280b007081b0754000e40703030041d0030703542500c18031044020094180003403d00320320310503e4000f5040c6015074480b4101d0340c10f502c604c1e00e00782c1241e8040b0b000700f20041038500b008405001031404140c0200c030192244400e0b46070030009003000c10f0100808a5a20246d03810181004010320040e00c003c502d00c11a642d041d02c181b0340c409003d03580e903414a00705400c00803654409190000e0455000600348084829645070b1904009540300304021500d42406200c02c211389100c0b401d8002174003001c6c1c4011140c1c0c8406004d09001403900040d086511203403205200b0307010107800c8030b011800c50940703d8105e68040e040c03628100c1103a80e40084441c00001c4000681940290391008904030f2401e22507101d00104210340e03178010351902411680000c458084400e40d01c00019000c03414510884a10f20010407110340503c0c0c41d00311400c05801c0210360204180f90030b000b0034604581c0e5004400280c59a82c80c445540401d1080041002d001680249043c1d405410001d140a400101c0202503e210810110b8240d = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 775289856 1250 775288606 775288609
    0x3040b16020405070c0606061d0d020102100203011701051312081e0703050a051b04141306090c1115130302160b0c0706111c110102030a05061206090615 67
    0x344600030001e90041d04081c20030a8056200030b040490500c200820800310382c41d0740c001c690701d220030500010f6003603210b00c103900c203403030300807140a0313078a10510445403020b042159910030380c0c200383c0c0141000341e804240050072420a000e074551002100e07800b05001c0c000c40e02c422225080d03048020050001c5003021800c03480d4074040071300840034408046d12480c202108024000d1104a034900b0704680303001c01069880014206855071400d115941078206818850a00103083c090f0244617809441880550b9a4164900840c0020b1824002c0054000050f0401070b00c0908890041c4125411920440214121140045030440c203030320031480315100b45141c16460003031002c4c441241e4528616001481034a84002006420380d20b4054664450781c80b807003030b80c1d040303d042000100768001c182203080000c0d0700c20050450b1000c51810a4251900c090341d00c3c00caa2058030b01c4101140c50f0400c02800d8100090089028a0040024816482c160741343d140c41d0900500740d0034140c2a10458104e95 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 775291106 1250 775289856 775289887
    0x30c0405010503091908030403110a030f0f020c0306011701150303052502030f010903020c06040b040e10051f022b0c050111120105150a020d0503222306060303040b 72
    0x585d20000014070281d40c6400c1c00c80741034004480403000507204205200310100c0c0070604040707803136154907801ca003e25540025501404055009030440c8129584a1100c0e0303030401c12035000301400040b100025555070821403d41ea89030002501c0d40070071a20400c0002c0c5d2100441d04d1900038010998030060303000920b17070140c101e010350196052050311184e440410b4194007400c84148070b5000c0310602e492810600140780a24840c940e2400002e08c1300b0084484111035043d030100381901c010707030103d454800180742c0300740c0303626a4141e1018181ca010b0469030100090310043d00000170280c81201800c213800701d0166440c034a4800c00807210000d20811009400c2105c06176280000e803621071f0700740c244980f100704003446424031444246183d103032aa4500c0c41103d00803aa00d90142c00640d03040c44090300e59030310203010110404c0c030f0105102c44042618ad11040c3c018441d4030002036040e040151620242d800c8580c14000c3e07000542844a42d80d00001118102d902ca0380d8800d071914800c80c0b0404c1e0 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 775292356 1250 775291106 775291123
    0x403050d080f15150f2a1905070305150703050106020a020a1e0e150102011a06071b080303010303120e07061209030314010e06090c12040b060d060f0f0e03030c040501050309 76
    0xc0c440d00402c07a003151002040c058140725031425112405070318414100e81120810846c0602c96803c50044510125440780c008015076008104442e48d142d6259a454903202d0038803146540c0c0c80b801c0c814084101d03414001d490061503103100800003a8200d8002030b00091251103202c101c01828007401110010070200003009142d5112900807a103081010401c036a2003007955140154030f0030291449a042c1c059a25010b5140500000d050000c2640e81d1140f182c14500c5900342400c0343c000002c3c0145040004501035442070b5100b0075044124401901503640d80c07640c0e60780079049582c0c10f004042c0c0c49503001c1e0500c0d0304c100340817600c0e1025040039001400b880c10060b42082c82307140041803000d840340450f4000d00003541c076400141c1e200c00740180c00c1d020b000305000ba003082ca02c0c0410b0105241040d042e030000301c018503d444444850b52180c08680b1440b04034644c03d522000c0c1401a035940c0c2c441c0f0311744a20b0300c0020358694502401071741428840c074012541884804800700c1c0c00000f041000d0b88 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 775293606 1250 775292356 775292389
    0x702060a020c12010e1c021606020f0d03140c07030507060911101b060510093b06430e011d040207080906030106030b0f060408030d0e01200403050d080f15 68
    0xa48c01e6807581c100940b2005291704c49416803064481d14962580f00744903212141000d000400c20588507074031200301540c40000300360200b110500201000c12017a00c980c014080c4120487d403016080314060161400c405c10700001030061002007228002c0b241440d1014055100c140041c1940d1200340c0c400c541281600400c0200d443d0004a4401c2c00c2c4852003886212800146000880409001120030000721280ca52441d00200007080b4503030048060741490100141d402c210343c40a607400c180403942d54410b0070003070203040106124083d81001d54000782c0301e02031921564000700c0c0303000c1180d841104bc030070b42c1c00769a0029408092000f00001d80b66407440080000c1e0f5a544d660a0080c0030f0724140d001c01d0b1040e241400d81f400b803403030680111812511031402960420106100c44002404400c0030540d8075502c0382c41d8400020307111046015140245803a9607121400d500f00140760041c501c3c2c1c2402801341030000e011181100c1307031130254412010b20002c0020003c4502252400d8040781043c1c = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 775294856 1250 775293606 775293643
    0xc0209132117010e0403090e070905090c090a0608160e0f0607140f0309090f0a2403060e0102030f0c0a180b030106030f1103010512030702060a020c12010e1c02 70
    0x5401e0380d000401e400c00040c01d001000a070390300e40880c1e031000501034900801007a28a08200050441140c1c810380c82142410000800390b0f0340c0020540c04042110301030341d200e0001518140b50320380380760000701a020f40e2800310a1403410011854040303034400c40c100107000742d480518a9075603950400208880010304203507110740301c601d890a081420154005154001c8000a901080d40001625000080200452140d847d1b003207082002e0b210203008107040313607119900f422011008402d40c81045004a4840602030f1940c2030240031242c030b28101d00030507401041407105003104145000c0c0c0150b44507171050340e20087c00b5000d6642c109010666a8802c3c4209000104d1020404c0a541200c00d640c42c1409050004000603089031540004913000100510040c8000d041882c00c68030004100d1003141d203850010780010303074186c1010020750700591180903070380944d0421042042c41c1c000000000e22141c0c140034036064580c13041415022001d09074a0300503050a20810a1805210031080038 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 775296106 1250 775294856 775294913
    0x91a0c030a090f060507050604140f0a0803061005161101050d05010603050f090a120f02011e090204060b030f010b2a0a03021e0604080f04030b010f050406060c020913 73
    0x180981e02ca034850b0200e1003000801c0054424060011a07207001d501c00054000c941d21591850300e1005100544803a621030341d03907244e00c01e001c02c010440c08e90b400f0320340d10340d200c1c42d00c0010840d5890441507041c2c10010700f8010311001520192424044031383c8070040d10740020750200106c4150296072036500110f82001c0000032800d070558007a9004507403203000d2903140d42d038042c0300c60307513584100340010300001c21195186041c40c80b0700034031000304005100219a280622201121001014141c1745031140e903040719104600c1d2a210f11002884841c42c21415840e00010b12045450144184c40c01020001600440b2001c0c155204a004000340c03c8620b00071052500b4a64481c150b540c1200940b14003034001d000020103080d00c0304a840003800602d00c2c0d50701d81e96060456081040d1402c80010144400300c0007811204195002c3c1c21843c0010134000d2030301c4100010780320140e105605100300c1810103005610340a82c041d500c94807810782c4079060403080c0b03440c42c0032924a0a40c0c20060b1ba20800 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 775297356 1250 775296106 775296127
    0x7080f0423010c11060c031308160803030a15090501030503120c0315010c15060608070f0801050109053d09090b0102071a040801020a0507030f020a0201091a0c03 71
    0x5402620780c01031205184000c058509030029021000c61804100805408000030b40c0101c00741c2401c01c40503110b41c0c18402800340003883c40e0025625004030441d401820700c040741c0b040003000781d404085896101c00500e00000d82d0380700d11000d0000501c1c0391322503805090300000526a030005010514081040c4d694a06115441c0d130041001a00b410f00d148010901440014013a0790040b2001480b40661108542c010340d00c46001c50806c0b6441a000c0034030785080fa5540c07203044c00400b510780b50649603207010080201389a9050705e9030000d0001c0500140483d99001e480c010540d01e05035000c1c40c0140021400da001c000c0541c6942c1c0300f1350110f2041d01c0c111284208d2540d581401a103842203413035100c40100064071102c40003240143e2241c00300708000a9000d040015045814003414a0304e07842d2111203003a6400310481c20085140050b07982e00b010b9208440352190381542c8040e1004080f2640020441b10a61298007241440100400100032000c0c045940002130034080300e80d10040c2c2132 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 775298606 1250 775297356 775297387
    0xb070314070c0f030b06120c06180319030f14041205010b040501180b0d05060c0a051306020601030201080a0b091f0b040924030b040602070c1e030b16020718020708 72
    0x449410a20001280c0c3c54280441983c17640d401f000c0141c0000d82da03038014440f481d001072400503400742036240750f0300e80e6460a205e1603c94100717800300325190801905001e04130322040c1c802c2000f01b0513010303240540c02d5032007002e48041c0e430415008418012881d08001d40544451121a540300385081c000180d040c82e81c100040d8007100350442480303095603c20400201071100d5402414a0700010005004041460300400c5800082d061031400c100f10035445450111827908070300c004d83c0c004030041c000c0d5a0000022944248074072000c0c4140242040031600c03646003d004007040798540c80c2500316588614260001418007080100d840d15aa403c84502501198500d80481d46ca06100162400e114200714001e6075040726a400c5a51076071799440c0300960011b0002c1d82c500c0d28401000c81c00c10801c0412503a07160030007652900031401c40c103080030311020160000440c0003a0a425696058000c2a603c0440c0d41c240e06884291241080aa000c0d215000b402418100c0000d001c0c54103c1002 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 775299856 1250 775298606 775298609
    0x5041a04140907080c0105042603071104154704050a0506030f011202060d050109050910150504050901020d020c0f0120040504020901030902150d0509070b070314070c0f 74
    0x308a0340e10740e03554400c3d65103030305c00f0a0300f0318000359080006100341041e00140c500030b06c150301c0c88108204030402c0001e007990400c4000321214050402c1c0e50750541781074002ca000c3c203843c81794983c0c2101d180410f2007402007514480076501c226441003007640d1003129032058141d017048808107508500b11001020b4690304c180074a0b4031905a0110100383d500704035058a1003094032301040000303642490219004580400000c030380c081010030581c40c0c0e1020a00079240201400312010429060540300503040842280c0b81111031484e10300d880ba90383d036803d14201c044602c1510005000d40b941000f2a019205141d4010b5001d40005601c030310050f0009142c0c0b610400e003000030003030070344140e490f0002030710320500303200c070b600c1044c08103020614180c1c5c000c08583c9414140010320761000e5000ca80600500c408907144103c002c101754680484502490364003688050107011000d041c0f0004002ca4060070a001e0100841c4000c90015080014121340b040e40c2c2204070380807240d0b65421580d0180c20f05 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 775301106 1250 775299856 775299871
    0x11b02040e160906180e030f0706020d0609021b0a0b0106030c020a050601080705120c0a03060e1c0503060a06030902090c0a0c0b0108160905100506030601030b040f0e120304050705041a0414 83
    0x40381700c010030040d10072035500d041400065850581c3e07032503d808568009280c250b03003180e42003009009010081c401c050050540420242e15450540d4007490004804c2c44181c58542001c1c1c9039000003458128060b0669207141000035140c0380b440b104a03c3c02d1020000288188184000401d145000180901c11110105e5030b00d50311500f100b2040791035403000c6107400e0300110501003c0c40001d540f0b030441147d840354542266040c072010b4441b0001c0981c1c00d07020002141001060240600301a103074000a00340f1800c09100248065010958100c001040b103014154081114074100c1d10a90451500b190410000301c29561550003403912107013040003440e0030302050300b8005a115918040c0c60310624101c0a4a00c0c080d00e800d00784074055000520702410180e4a0400c200d15540781c1c429004c44103000440001c020641d4008a803a0510015120b40c2002c001d004000008400080307040644400f46c130f01260400320030b030300041050703a0760841550040c10842e06406102868401d03620400c2e1 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 775302356 1250 775301106 775301129
    0x6051908010b060c061512030a0f0e010e0a0519030b04080d05180d0f0908030c01020c0c2b0f06020d020903010b09010b07170d020703020f0c011b02040e160906 70
    0xa0103003c01803148102c1d52408030f19044030000640608600c003841808078405054000340d042e04181990542e8001d20a00c004150705401c4170341c0183d40640c05100011080c2800c5445081e0203000a10003082c1b880303014414040011110000743c40802840025648030b0480320250402e4580354042d9080310490f098031500d840000340500002e0203d020400000e075000d4401104480d404460b1000c17003c844000f0720914290025101c40700f00002c1c0403d2150000040e20b1703505103425075007031114404619103e285654860001d0340c2094000200c00740c4e403500d010108001c1c0d85004ac480d5440d0704806040c1c82c1c0701043c402c0c00e031100c80d001420081d508400030000c0e5680e00c1d0401c00300030020300500540b40024040e2500183c0a146142c8288038035480c62070034901007003000300590b4448201100160014655030900740020401c900700b102090818900700026003c14140300011100064031890f255400098240d0003444140380c0c0f01c9010210110250f100c02c1c0100c080d0100703100300d00032541c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 775303606 1250 775302356 775302371
    0xf01180b0c090a0504020d062103020106090b0109180b06042c0c0a0c020415032102070b0d0f2a1409060403030309021201050a0522050606090a0605190801 68
    0x16000340480300c608800600e20850f69040101303020094204030300c1008201d50720742011032250080080c000e4070b182100314515410f0f1142c60000d00b5180381e54419051541412030116a580c0c00c032140300180c82d2070101d2480302d01c010050510181044500311600006e0005010940b12810506060441c0300d070003034035450040745400b011440b04125107030004d180041c002166200d00c10a490a0118002040495200208500305011409550080f940340300c03418502e000c0a0489134016202c41c0603070018109441c0782581d200b205116044030741111039651051040580d015030702c135242d5803a0300ac0b149034403180000001101025100f01d1400410024502540030407000707001c441c182c5601406240c105455035034260003805d00401c1c00c0b40c0c4582c1820f02d410780c0000034460700340b089034454000310b06410b00e0903001c151480342c9681c0240c04010103044901155000441e1138101c003056030140101c1ea14040c005005111035040315510080c103002c1428043c2c200703042d003025036400310020807141 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 775304856 1250 775303606 775303621
    0x100b010503070f1b061109010e09070e090a141303140901091404091703040b0105010c0201051b070506070b060901303009080f1b030f01180b 62
    0x7030000b142d01c03100084200c242c0480c000d104110b0310142103000d0760b4122000310740c3d6603980c003900d50040320403c0740c0b074000c24a80ba2940e0b0240c15080c0c0b21f0419180070f241c0342041440204801441201140115900d4020503030941144e4894925040e40e901c07400803a0910500d074600f0303001d150340306a0014446d60322081b0841101c00c125100f041c81616490312041ca8a581e458141041c0d040300c583c440c0e0b07103048840c081411140c43c40024415001155aa450149401c041882060300f1480c10400307010304900050b40c04c0030446400010040b1240301d04502c031423501e440c10b03145e03401290300b02402003403420811505513450380c05131008944041003681c0314902071100384454440f42e48074812950060400545568a80070458054104803505a00c0f903101c88000b00000341c842c0c0052803c1c4000750300e4150b80045204064541c1601801c032000c1194031035540e9040740d0f00b00020041005000354110380d03080000c445680103c00c02403021030300031034180c6806184007005a540a080308009135171b1 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 775306106 1250 775304856 775304867
    0x102090607030c0c050307031a01270504060902030d120e010b030a02190f030f02100c05250e0711061018050601030e06010311031b0d0b060303070c0602100b01 70
    0x640601400140c105030582d10121845020b050040e5141500300b80d0101d400c2d18240500e20245000d9211501d01c42c3e48621800c00717050301688010555050320001090030b1880d1090004a00015500070407552518100f0100418100500961511a8030075001000e178018107052000159014100041c0005c40103c03826140c00304110399040e00050f9100300103182c030310204c000400c000c3c0207000c1031030f466807411175002c5401c1c1c000b0764132014a40305807000c5241090705c0c103030030078003c4c68441c800401540c0c5860f51f400310684284114a082c000400c6041041a00d02005103ca50030300500e50400d030002a03d03012050564501030701541001030000c3d03a00300800c1c422134500c40000981501a4070310741006140c09049141090780703a00b1b0843c1031000400c000d41c0654040c0d0341c2440300c2c00712803040502d0110300ca405000100d42e168202400b55482080755025550002c1243c00c0c19680d4400090079803069040007000201d5200000c00c0c0907a000403501144a0b14400401801416800541d035 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 775307356 1250 775306106 775306117
    0x315060d031808061905071d060f0c06040f0c0b070308010608192a09032f180601140421050c060406030f1505010801122d0b01080102 59
    0x10001901001000042d1180c007605010b140a404441c0502e900c428829080c500260b800d2580c5480c55444000e10164a02c01d1035008681410400c5010300d100300410355100c40c82c0c0e03402d441104081f42100c24440301d041100c00c0ca61400040e20101c0c6028540610600f00110741580c003082540d070b0109003088600b0458449c26015200c424403a0310303042088808110003403000c4040c0c03e9461008900d20128010701703501004054140f41170107044031a56209000480d0b085c01040b180744000c001045041c2c0a0b4014125540c03003242014098444420350500741024042d00188400004518810740c00d00107801000c01340c0c2c80e64030b401c0d500c03101d40764140100d0048405044000d40ea89480309a070780c0c114000036215078141c48203210003000082040e00309911500100c1d40306c1c000c40c9603140f03c52003031b03201a0181c072040f88692414030b00020240c0c6014020b0f05065101c00c0c200344244020310405105071284242c62081c0503100d0400000f064600311403c03600b01c10110300119010506000343e81 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 775308606 1250 775307356 775307359
    0xe011d01061d040609020f060706090605160e010302090321031e1504052e0806060d0b0610030e0a080705060a092d0506090a0507090608030405040e031603020c031506 73
    0x307070300e440d5501c44c0f80c01480241e50403079011810020f686443d0322420049c10034540511400107007204182030003029100f004002500140d49603c88002d0b580c5c010703d410f000790b4402c0c49d00507100c0c0c0c0d02d2130100c1c0c90f0074803451a8103000800c175170080402c400c0c02c42c015880f0700034a100c4000a20740590000180c030105644071540b4004182c102d00f0300d130a01e81d0003241c2c4600500c00050b6600d465083c0c1128030040c500520201010110085c000d4a00810111360130402c2600d81407541e1407035132244078409102900a5114000c0443c04c00d400342d1090308440a0050302600f07940c10106a803816000c5607000800844090149000085c20503142e88921840203030007030402480000702040c1c02e00b144900404003000c101c008080540401c01c100102841041c00c1d000502c00c0609504103180f030b000c0350b6031040c25680d040c03190a1121420100907070341101c0082c0d0780414a1030241004a0840c0109082900d28040c0c0f600c0f16420b05500003042d4441240c16011303101b070807009034607900f4802021180d45 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 775309856 1250 775308606 775308659
    0x207391d040209090a060e06012306070b2a04090c050309070b09120a0c03140d0519050d0c09032307170102090306010611070b1602010e03010e011d0106 67
    0x20050708004015544c003041507002d031003020340f0f15652201181e40d41100c01d0300c0d9900103401400701345150341844403a040701c4103240c00d10360103c400280761340c8240d80300208113240b0a0302003000701440d519802080e500f0041e00507203144101d401c101c0c051f001485003801d02814071400100090142d03044030301400b0302c100034107407007810302070b0040c425071011035183d401000303e03803180420040c2400f50f165400d00c10391610301e00d60301d0341c28640040c860090441c50300d5044602c504824940000441d440c5a8203200740801020381200250f802c1c0c06080b203c1307010700f41006a0002d0b1151712868010559110b84010883c04c1e208058101d06520318245080669014200c00e00c41030300e41d4225040484944070015140c10410f40210b4202882a0310080c042170701c8001e01340340c1000601840000d4107035a0036041c01d000084030001c00315506d20a0190601044200c0480e441e01c00f90041032012030102c1c02482408038900003102c0c0104460000c0519500e00640414050b840d504000c9000340d06070700e003 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 775311106 1250 775309856 775309861
    0x5030d0f0c0528051e0405090c090102071401021005070203030f01060f140f13030b01031a0601141e0c03070314030103051f021309050411040b0307090207391d 70
    0x64407807800c5a9903203071042c01424003107555210002e038409070200c000740e40020b80b06c03440d2105001c080d90029051428078502886441d01d181d0340043c0315421110b481d900405511040d100603810006542d022240c030b14100000c00520940000003180241d00880d50448160303620759045a03a95070511003000000d68440c2030200600c2e459001d0425010328078002072034884c0b02c0b0f07820700100e101584102c0354078000310010414001000c1e000c160944104d24000058505000002c01d8501c0402d4100320540c4041011070a003495070251481a030030381c44266030360314090800e855494024443c00c0300000d100c0301c200c41010422000b9641200c0d8010020070035510803e80c0402c400036100c814152a81d030a0000304c212030002401300303004041c40800000d83c2d08003070600d00a034030039170001d2500480c10b00503612007036140052000102c803028003005803a40c1861034008542d1000848100c1e03c00142e0708003003da001400c9400f0b85c1c11a004091000007a603503c04806122504c0301c083d100140800300 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 775312356 1250 775311106 775311157
    0x501060206071719110703021f02091507060213080f16030c09180507030305180301090b15030c090f270307060b27160e1e010c05030d0f0c05 62
    0x124000c0544d0314000482c40305000340402c80c40c0d4020a00c107600682c401c1101241e40320000c0300c039042412505000358500801b0401040c0001c62400d0141c0140b0703000111171080c4103155058410583d40c01003d000f000742d03036415050b5a6642401c0001c4540180642600c1364049605840c00701c80e44640d40b074510350719100e89480184050103142c3c94800f18980c1480014230203101401c0518400e48425854240d000001212041d503403a280d13000e030385401c80c0c1e100820642c4000c503900810550160321100b96180101c0c3c1001e40303401031503802c0074101d0248910b40c1c2446500b94030407616003041548810000840550401003000c640e005c0d50003c100a0700851241d4216075451540544513201c20303c48020700b01948140700d003030f107000380320020284801070395211001400405907142045040c03901200084003020150b8942ea03002c480c2802c0920249d000f1080861001d4010095a0300d07080603414280180086c44041200989006d42c1b080c4401d01030f0701030314500c1051000f12007481c09440c0 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 775313606 1250 775312356 775312381
    0x201081501020a1403070212030409060b040b071101050423030114100b030a090c1403210406080603011b080a0b010807050304020405181b012c100e0d0605010602060717 74
    0xd003130005a0004000d03550261321480c1042041300c0d8140c00840c0c4c0d03140b0f0041c6802c12506150001d110002e0104410401d061070031056628090308042903511040e18600103031f82d40c0c0b0841d800386010740c110340c4000c0180c00301c04103c8510301400750001c0c8a2003011401c11410018111030111600c0364a08050040e24050350203543e000710f00603400141c01ca6142c4407002c00ca1182e9000301c96440550610307003800e0509004685030403640840f411200d80100e0443d84890180780038510403c070082c4005030981d6000d42011100c002040d504816086d15450001d05181e000c90f5100441c41c01c140d01c00c0c016500c94074a4510441e06561080e00f50303140e40c0d08000281501030b20080354500c5150f0441584401842414003503140345041c07000341c02104001510340803a03001b4607100c0781180d0302030348070400ea40040e0390030481c0202c034030743d003151922481600c2c0b101c2c501d0302c8590810011758400b003c0050301c1e481f840c16a40750b602120407641c2d40c20400c8402c054504002134064441c01c01040c0d0403a100d0317 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 775314856 1250 775313606 775313633
    0x140d0b0c0c0307020d0b160804261306080f0903070807113001060801140a090212100b0a0b0c281e0b010b2d04090f06030201081501020a 60
    0x120650b4942030b400e800160301e010781e8200940c3e1400c2c1d820b0900201108a05014400307c0031070402d84524035050319a00000080c100d4000841d05112030807031842c020281c00c848046160032041d0901c07035110100142070b01e0044400c1c3c0b00c203001c6040411702e400400000e441500d0790060a0600e031010300c1d629456640c55a40c000b5420504c080304641c4807500307a0b0051086840303504030400740071091000b428255007031030f0300030f6165900d04101c1c81068051158029844045182d0209000b031a91010400c0030b55407501010882c0203c4000c1e01b540d40042d00704003c2c082c03045880070300c0d8a441c0c0070010218031401c55014040c1c0d0000411702d40b0f0352240c45440c0c02d54096840075820788034568a450803038a9080c1041d986a603000e0040a0400900424003809416400d6200d03040000d03c100a0481500300d41443c052002a54200103445030480103c4000d0000ca103c103000d0ba61112100e2405012140401c90210351041300256801c103a03284141d8408105030300420503111280c680c0b40c54410079 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 775316106 1250 775314856 775314877
    0x110a02040c090914090607090302010903080901140310050a05370909060e1005090307140c0a140117060d02090c07080c0a0302010c02070f091d0f010204140d0b0c 71
    0xd07440003c0d240701e0f0ba100c1e103139050306881c0b502e0480e03150540c541c0d802e188000700b4050510004c00018070150368081c500e80140d03503000600550760501c1c5001070740c41c0206581c1d50600380400104100382e83c21450485c0044400980705e010300580c0715030400400703880d00c1c1540c512203140c0d1102e040c010414900c50803401c12200c40c080d0f540315203d08100d0107498020105440b101e407109584251400c04014458501044482c20071440c14001d8045460b881489400b900701b080602c902c03000d806050100403901000286903011050b5641031000d41c09030308000c00b50104031050956a9200100512148070702001803240702803507103039403c00804036000f621460410100b0b100030400075600500820042a014004010301c01840c40e0003429074000061000464101c18400c00694056a03000703419204900e601047c2c5182540c02165000c0c50203110704001c2c071955150030030007a010b50080c010344810101c180d441c02a4035060141c420780c114001440b074840c80c4005802d844080c0d010f001110075 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 775317356 1250 775316106 775316117
    0x15050a300509031c1b051c1d010509060c04180e030a0504260c010804020d02221a10030506030a080c010506130c0f0813080417060106110a02040c 64
    0x403000c0440e000c0300c00407944030020354000145030400300c80341c2000d20f6244c44540414814803a030301e440444948102064281030000116001c002c000406440b860b000390807040c20001c014401d08460588030440c0000c031a07552a01c0e01040354640081489071046443c010518a41440c00117808e500e041726150400321a95504000c2c1c0440000b44000e05202a03940d42d05070321a8240050314003000803621029418201341c00700c080c400e0202041c3da01d080202401c3c1305810390364a001040c000c1c000003200075409500d00501c0b10030031109000410110882c00801c0040041c90b0200d0144030402080311903200940c2c0b90150847c038402e4200c0c0d40d220b1000340540d10350103260b580c2c8041d00c3c2c00a00c5001c105945450400005080040c01031443d480d6441051107640070104001e0880780706450050108104000003418031300c0d0311100d540070542e000b0b0550707580315600d184d0100700132001c895203105030003001b0001038918030070b80107002c0c0d800000010b041c840003140c0c00c0000829aa070301c980f05104 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 775318606 1250 775317356 775317437
    0xf05061f0c12110303150307080a1a06041806090605060103110412030201020f040315050708060108040b04051c0c02150903032520040b01031a01030e0c09070915050a 73
    0x14400303035009406d403044404c1c00c00d0340c0c1c504042c10201c1c15080408254081410540490200000c1102d15408000040c4440d29080c010a014003102c0c014401e22030f0b08143c52404000c401d42c8400e00603402810100003585401c00110103031001c2c2d5108030075034003040c402404004025070341880c1171480382c0001440c2c45048401110707941c02c264000c2d40d82c5007003085084000710007805016130001e002c1c5420035941c5030500018202a1000c2d0000e030605c1310410001c1c1c00c010080080c002040070342e03c0d0f0084044d0701607a004165160501080b0b004190f591805000070761540141c602007000100034500341200703032403158a103840c01d900c0d910309900000a0b0070007143c03c0c04101c603a0300c1290340300440091000c00500c819a170301140d1480c109031404032010400301140600c00320320360003441c01003925007112401f207117000210300005a11107a8501031100d000d80003078143c4111100c0c0c9000c00f40141440c0d5040e5400e002e041c1005003c01c0751281440c04079080c51900c10000c0c0c22420781d151404 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 775319856 1250 775318606 775318637
    0xf070506341107080d0903030201060603050105010c1212021303061508060412300e0607090603020a050405040222091401091d0f01051816140a090f05061f0c12 70
    0x5d8122821040400d4200c03000b4000c0c141c0c2805108c001e0451801c090186500d0040020030383e00903101e0207410340b601c0d2008603182a02c00c512214420100041c15900d4092845040d07401c1d81c0c003403108a660f1807401404043e000c0d5042250710072a92400003422040c4e469440703910709018010a800208440001010041040d40a90840d2244c04100e4408000c502213804000c03a0051011440b255003c00c3c03c010307645501080c08000c1c0d0718a03240258480180f05c0080d01c1170b02480d00181d512030f0000c900c0400a09012030601c41161300c5600300c4800765540c403181012070f400b042644103140c2c4a0401408000c21a40000601c0c44443d10341075950614980300c0d90600103514600b12441e51a0001e001c40d00250780704c105540c042110141041400a0340d110400351590311524030118941000440b1507540e101d4244000c160a800900000c2d901100341001000d007140c07141d02c03c007030810f95402c068007002e11000709007580386c54107211703a910782d1110101800e412401c00104018044003148a = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 775321106 1250 775319856 775319863
    0xc1c05062803050102072004090b0402060f040803040b0a080133050f03090d0906090605190c02100206041205040b030406051801020c0f2512020102030f07050634110708 74
    0x1094001c1a1701e80741c103da8104902e000390747c41046240b003039040a80150100f6403803440e00c2c2e00158100d034400d942d40e900401440c8180541d43c0030a215000c08100001c0020241c030040403940300558980c6580da13262250702c03040c1543c0049901f0b0b0207189a1102c1484402004c91149030980750410360304208a5136010595903004403412000b80d00300e843c0090141c0d0b0048040c9000c0e04260616020301810241d00030120700138807607001c6151482d031000200c0740d03005009204003150046c2c821079a880c0c40c100042d50724281a501140d455074840d01c0760303005034440c0c0305542c00d03640080352241c6540c6030740c0c440a0240102a05151404030051280380c0c00c04801d2004050398900c82000d40360036222110018181181d82c42400705007412000031408100002003420140e1390b01d250101e820b2001400100e1460084040c104000e150010b000410f0040016109108100d80ca0b0b00e490400c00750042011204081d07803c0841c51144be03001025801d0040d81c0d56244a1110320466140e03541d10354290b8038 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 775322356 1250 775321106 775321117
    0xe040912030209090601050c030a2f060106080a050103110112272a0e090a0219080d02010b061804090f0303020702030d110a1104140c1c05062803050102 67
    0x10a80c00102400f00307041c840c0d44154480400d007016800c041d802d090b926160310030285403604000c043d01e600f150f64054081c2e404944401d1050340400001c0a820465403050203014440200d03c40d0b0000803494240d600686040ea0382c0084942d00700111040156a500c0c03004804003040c5864220708044000000702c01010302c0440200010b80c2130782070410407900e07003410442e0b40c6150002024130400c91031b02c412610840b1083e2042015907a59140341074209808520300a500030007000e517440e81d00003c4140002a2207607841651060b0040074000c0c0c1c04c035070ba01c5c010141c00c00e909105940b0072545051007036201c080c0292000c01d1020301d550f10403184150008003140801e9022603008150b0a042110056012031410144403c03000d60300740d16610401b03403000400c541640c4002207003030303201d030b4100500701c3c07003d4001d00768036050920105846801c62021008004214000004101c42d05c5c01041d0294038080d024142c0001802940046502d08610a039115094a0800400540d0900c010716 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 775323606 1250 775322356 775322393
    0x7021f060603060801050c1b03160c060e090601021c1206080f0d090f03150b060309070509060a031113061224050412030e1006080304050312030c03070e0409 69
    0x359a8200400542111400d07005500070b80c1c9000104003414401c54200c070100000455200001aa50a82d42c0c0c9140709805840c803d0b100403070b107035100b0001c442c1a12402d449054464007640c0b020501880100801117428500590000c2e4081c244086407041c11900c003002e61400c411003c014602c518144c07010b96000c1d26940d840700007481c201540c144051a4864900d00d440f10219240c444102851b0965002c0600042e08030f9034025106109580200e02c1d903080940b0807600c91400b81c03510368a0b04074911505029030400b500007039140c40e02d00942c1041d00e074007101001038103100d2000e20621501c3c200684055554500003c1026070210244044251240d068044840d0b60514604d1030100308070307040f840300d6041a040c8000240121180b05440b000740c580040c3e451744403214640740006007180500b0f010306c0d08a01088405010000f0029038509600315021000c0341e030690403051004581e0750711011800d1001c42c80302031050310b42c0c1008000c01040448c0808240c3ca07541100742c0080040c4 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 775324856 1250 775323606 775323611
    0x3090518011401090308040b0307121e110c0a030c0507030204050903030a0c1701030206130e090a03030e071d0403020a080d020913090203100e070f0603141b1207021f 73
    0x1048a007004000b884039201c020300c0c02801c06031850b5241d0311280542e0082c201400c1c030220004000230704c1034010644840780c41d40184000b050b1080c2031840141c42143d02d44040c1d0614480841c1e00125104072440c84803c0e0300100025541c1d52000ca4140c81d00c0402100c040c0210356000000d030b039450041034010240f0340080c56590800345d140783c08a450a00004051064100307154654003110340f80681101d4040d108a070340d41289002500c41303070099030081c80d16050300700107001e800300300005c01d04905c601c2504c08010f00b6164078100c0341d8689041c89014000c1d0070b885001d0880c2400b40c00642e801c140300340119a00f40780701d0303614109545c001038150100c4541c00b01d681c4090345041c118242850306001c00400c105c45a03034020944036417207040864006625400ca100070400e04005d50001020310351004500307035481d03800050140440d0b4901c081d000f41c0c6000803c0c000c2e89a508010305078040410443d1404816030071b416035142c4010090340035409110622200f102c84000c00355003404861000 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 775326106 1250 775324856 775324859
    0x41109180f0f01151202130b0307140405060a03020f0c1903350c070b0a020706050c040e010608060a0815090601142d0a0303031a0103020c03160309051801 68
    0x100300c24880700400281d8040a50300041003506042594400b0082076407038071900c01c680d01141c6a01a20420000c064109028200090340b0182d1502941c090f083c99a1140e90710807512045502c40d005134050b182d07000804003c02e10045009600800c50b055071548410700b40103804001505141440840018030381c2c1009000041560081084071400d04035441c58200c2c9070000e4400500d1440c403100c0000103804500426140310124080d11b110641c8a040988980ba00c0e41c1d9101c0a508400d00c100e420506020200b030b81140c0300300c10340301512840f00300c40300e041c1c2c81c081003110003840c058040c0780c200142c0303900810a10014003410358000481c0a40203010b080c4095410b162820503032042403041034240d83c0c00782ea40d07543c2c41c40200000d56070000078245944005c182040711800320300107a1184e40c84400208150b05a00701c071105101800000c090200c04e9001942a440360819500d280e410400100c00074210389007690312030602030724052808a440d0f0001c02d1041140d10b91442250460000 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 775327356 1250 775326106 775326121
    0x4030213270f1505090607031505030f16240e0609040203010e04031103130e06060409140a110406090902031504020d02070b01050f01050403020607060f1d0f0a0c0504110918 76
    0x1200203e0302d900804101d18909940d4603600c6e03e101405080c00c05882d03d00d000040010f0f039480e00090305004081d0741282103000410b83da40c1c034401003141007885d240d00001421459040000c8c0c0d0ba0003108035290051082c801084680c0210a08101d42c0b1480a20000c1c040340c50350f1000d54068501d25444003d582428103018040c20051200c07031105030300400c181c400910368444a2011214020680d0031591207d03000104980038980048001501d09161141000ca0350720700726015070180c4070104034944164050ba5041c2c850703402001c003c140c020320f041000d440c00790b008540c07110400d45c0200c1c403406d9440001301a03900016226100380c2c1c000c91f42400384031a820050380107100c02c840c0404043e040348000f82c190301892101030700ca62000710b01d80040c04119001076202410040e410000e003074010165031480300361246103e14500c40c101e4000700c5c00d400000c810042c1a0400940d20f0300c1440c00081001a011a914201a01030b090007407441e0351300d89050a03100c001600340c0003e01850a900c = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 775328606 1250 775327356 775327373
    0xe04020117010b0405040b0f03060405010501060f08040b010b0c01141017031e070c0306091b06050313060b121509010b0607080a0f09030b090610080304030213270f 72
    0x441058501d12688010001c1105400031034045030020360703000c209160900002011305044c1c5001c03a8043c09028200001c011065202c0c60680e0b005403600c08072900040e00880d60020100c40c002e14026000f030060040305000001f500d8041c81d014008903e4007880400004004809e035100c0300e03200c410381000d0100d6420171003410300101140000350b00b00708038071401c0c01c3e5641e011100d00d04050800031300807080c00180d5600c00c024580020f02032210070074501d0407151035001440385114000f000f1601041481c0304404032409008817800e101c40241107903c42c03c0061502400083e8010841e504400c4050020b1100c0380400710515941c4006150106086080d2044000c0b150300c101c10401401c1d00007003034581541c0c43c1e2180c0b49000c0c00804c0749035000707503943c41c4243c001034a0140f0348070800102400c002082441440d4950043c0c00303150b6908241ca5603400380f0301000754469540035a500031440158440f0380b00304410b0032100e81401e20382280c0c413507101d107800303007a07485401040700704080c4010030 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 775329856 1250 775328606 775328627
    0x50601121a040504020105041d0403020d0e01020a0209061306080c0a080d020d1209140f1b06040603201309151202060c0109141e070b04032a0e040201 66
    0x31a000e00680d03510701000c04454481407400d40c8550ba444010500b96407003039040c1d42c0a80381115961140201c00c50120381456001c40d0101c0040c442c14607108034803440b8030b00740c5100c4001a0000c01030704a082e4208404041c0060070a070308070807181403151440d08103010702e01c0100102d9010380040c41d03c020a00000c28410307041865980d10a95001d58500e43c001032501034401d041c50f00521082546400e28094400034401800540114611051144001c03608032410381c1050110303140d03c143c1e082404104050700780a1548800c1c240400c0109a000b070300028080c1d25895109021001c10001240c2240c0015a400f42d000305065800d101c0100684100170015619141c1180031500c0c04d819031072071a0030060000d001c1e19000c00c0200380c03404c0c250040a09254040100200c5c00c080c5201785503260f03411802d044942d5040d02552520385000325152064819002101d07140c2800c0d80c542e15121000c10300501c50100141610619800f205412900036000d403d42c85915418240001480e02110 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 775331106 1250 775329856 775329887
    0x303050a0e060a0b2419030e1606030b03070506190c050706110607030b1c030c0b0c091009120303020c070b04030819020c010e2b0b0609160507020d0f0f0501050601 72
    0x40050003054104003c140d61068080109a000b03807682c1e042c0c114023401034520100842e06c6207102c1b0744003458031040110165034042d501040248010800c1550301d21485c411030750040020800e017040050105e2090412004c14207000125041513640c013031920102d5030003a400254030404000c6100014480b6030f0f003006045c03070140302030190b1900044910813034000220f00d20b070b00c0c80c17062401c06000300080c1c0340107074000340d02c106c0520b8118203406031540092a03091040890329964482c0501901c105415101684e03030003404c0ba600b42d50283c2c0294010340020100d8422181c00040030060b110082000e5403148560030384507070358130703a40020b10b012211641055420031705080b20f45992003071b440d02038214101d034802480350b91190038400141042c4071600500561080030f0080c02100f0300803600031a401d40c1e0000c0150740e03101e680f000344d210b08000310740003a400300030035000741c644403440c888100d004100c0c440401201ea51809a2085c490908a40c2651070300704120305903030010421200d8142 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 775332356 1250 775331106 775331149
    0x6100626060d03110316020a0501030c08010306050c0708040b0903070501090602061303031506110f010902210c0409050c040605100f2003040602030304050105011409040303050a0e060a0b 82
    0x80300c0e00c84040140014801c5009481d0580610141031244106204d00c2c0700d11825690760b288120884e100c0c0d011858810703405031345000c0000446502c28845c15040b60125950342c14641d007036a45074005000c000d4042c0400c41001c1c0851004101d55400074002010303601451699039100400303260501071580d010074180290707110b04109050300800e80c42e6000f0032420950342d2452092030705074020450000c6035040c038100c2c44404200180c00281030100d44034a0011128a10079240406007a07441d4044000d40100c80c0c1034a2200c584089038503001c0300650a42612001211540801c0450b40150000d031803035400400700044500b005d01c2204040e003c10758195440b0107001c200a030008840001c0c6408118601c41814002900e100312120801100c0c02031f684e590b42d440340000e5a0f5081540c06441d40d503c0c000000440c4095080c21681400c0060214140c959860300c003074004207002807160700c6107034440c1c020207503042c0705000240c031441c403a1500050a9103540284418048800d035907100006 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 775333606 1250 775332356 775332407
    0x111032e1211031c05070506222d1a0702070311060c071806061107060903080f0d0e0706020c0d080915070f0305090f0402090d020609010c0203061006 66
    0x451070301404550358201c00b16400b0500c1c207001107450400050390b01c00150000e84194840c1540c064000c161490041040311055210524403480080c10180e005a502a0000d02ca01c0051018007221501030342d100d248541c8084141c0c54400c00030800c401c1220708a0045030b10300300e80e41504142503005034541c401442c4260a560384c2140040d80a49060b02c6810045a8206540c00400c90040508070200c030007002c807029a00d4034000742c10140560000714142214062602e41c0002d40402150480d0b940d041c03185185403a010307410750214070a101590000c01948500001c00e005208082e1144c8000340911440c00c480241010141c0005030310403000203941e100401d000d10103a0b844070204544c0b6502c06500100003500c5846100c5008165001c004c0c2e0003000e040e0400058034000780144c0c3c40c8440381107800208000c034840c220000758464000300c039a0000d402e1804c0500410030b41030520742e0044001d40c0002e07140140450b800c05203100b00c0d280c188004c0c0ea10a000741c040001040d00000c809 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 775334856 1250 775333606 775333619
    0x12070b130f090e060f0a1d0c030706080c090103050403141b070b09060403110609030607030e1b010804060c02010f09150f06030203030703030f021201120c082d0111032e 74
    0x1804081c107003100c40340e103080126052800d1544400d141c105000071582c84821140c100c030b510b0723800040b0783e24405c1c0940d034400070741c050080440a00c1006c0d6019a5441c02d0807000040d002403002400980c1085405420703004007881c081c0041c17840350030400344044103101d0002c0c0d2618000041c4c2101c6000d8100b440148981d40f5648280e0701a40c1c0d20500072003a000c6800c011540300e000b0b0712a559450300c03501084c0003a0030380550200801c1086041512403240400e1483e001c030050551185000404000004002c80c0c0145d02604000004c0e10020030300c5ca0021741c2c2038080e41d00019040d9080f5140004100b03100d5041c0c812802503411401c8180012071468001030380340d0043d04d402409141d00d81c0040400c1d11860303411038a0406904a000c51696140c9403c540010134040084810990301e1202045a500c002007010890681854015201d002048c090702d14081c10342c0203500030f640303550760380400d04580006944186d900d4450940e0381d400052040d0400f01304041303d02080f1250b0141489003 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 775336106 1250 775334856 775334863
    0x20a02030105280f020c01020a05030f01080303071b0515010605130801061a031f090c201905031b0303071d1e06120103050d030e0106080a0212070b130f090e 69
    0x398200c03c009140c0c0e015058010191060404968095100007440680c81e0303040b07009503010341c02028400f11117a80f03840086a0701e00c0152006408078105243e4000c188034540035110b1494490303019a00b01582007200110321101c00e800c404045500818184400090509040003c080420080c01000d01d01030b0f03100001c000ca09078615002c1c2000001503085480301c404440740c2800002c6a000141da0f410f960350041000d541e45d00006100e004501c1c1084140c10610020824a800030b011490714504016500c0002d60701b08072580e01080c0700c244449403410195250341c0f1001005581e580ca8900d5000b03007881c03000c00014405156804e100c04598403888980f40c0650ba20800c1020726411040c0000c045001e66203605002c0c040d14070001c010405c000c60f40350007010300d40c3c4062180c4201c1013043c13801e9903250701a42a042d845459554050b240855090401802c1d03501681d0743c003612a0f40018541e4812039200c01504204a002c2040c0750b00421504000d00100000700100d2031200d00a0381c4 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 775337356 1250 775336106 775336171
    0x2120406051f15141c1a0603061503060d020618010314040507030803070e0d2d1a1f0608010609091a090a0f18020a0e0603030304140a12020a02030105 66
    0x400131191401c246200c529411200441c0d145c1c64814144001ca8102802a02010300c2c2150351548a0600c0c1485040200a0380e018440040550142d00b000700060340481d0401003003240d00c40f0190084401588410700146043d41c0f801c01004101058900050f0a890034001450001c01c080020400410000f14124040d02d50207100d0341c1ea43c2e119003074104c808982c0c80c0a540c4c3d1000c1c50080d41c1c4104941e40e001c0c5078201c0781e48074032004042401401e1a80e01403000c00050031680074690f1003004186802d02299010032802c02c891482468009650062000c58020601081500c80140440358100d84164018408901c06028446200d0340c0c1000d80a0944102c5015900200108100c5c110540010190080315841040305454520346a4003070800c0c00c000ba801040e242101213408011107001c1440f849001e8011860360b05d840c2e882d020070a01d10000700c8840d001d00003840b00040e0450b2100da80d841041da000b00184c134400d004140c01c650007c0c103d00602d8000001c0c44800d140c0780c0d545440d = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 775338606 1250 775337356 775337399
    0x80d0c0201060512010203040b070503010807140a1e08070801150e090a080a0203040e0105030f15070c08040f08060a0b090c0c0a051501080f1f05040602120406051f 72
    0x14114052040a034054051a0403035948000850002c1e4400329055000d98800c40c000c0f02403034400d455408040e1007505c400e009a000582182d00c05020105180e41355501c1c518018150300c110710f60756000e1042031003041280b41130314055000100314005080181c000581542002081030f43d9001399642d00c0070320030348650000301021400240c6031880600040c100030340c00201c01ca9640e0301840009449a1180c05450f446c40c0c0100c1c004a801e08000840e18413078407481008290190004610010001e4010400010408070700e4107500041c0d00308001e00010f001d21090070031101d0418003103502b4454002e012100003481c102c1445215600c0f5601d098001d0200d6a08665805a81e071b2494145200c1000140081c8100b289170000c0c40120544641210992000d03a20136100c0c0381102078a0b14051760102800c0005c03511810801c83d1079a02540c1c215128200040c6021408140142c0080003190300b130300c4003640c80042020036049a841881c45642000803a140305041c5415411250888d00350303407 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 775339856 1250 775338606 775338611
    0x3020408070f06210b04052a0c030711060409150603051e070e01020f060103050c0f100e15040302181b040326090d0c090c09141002010f2f0304080d 65
    0x10101300d07445034042072500b000540140b0062420107080120032044075103001c020410380700e0940070302d02c03500c0c19140310b0341000b00654500303025a150b580d2066030b02010300c0c0e032004081000003499500e92055144c555000b8211191030382c5070503000b80c204c070700090044071001500c001c80f205045140584652094070380c01e146881848550040303103071240701141000c60f44500300010081c4440002c400d03041000c01c5030204417640111050103050070020010704003244840790205424940702c0742040083c00d2001000e81015982e4002a0b40301242d14000d0400046107018000207114021040c1304550004052902c4c00349540e851b0341b00b045070014840440c90350b42d020b000000080c10708079030840c507004100020901440c00c0600100d100792080c011a01e20f0304000081440c01400a48119050510100c0c0c3c0009110180004249170b40c41e0042195a01c08a101c51b64130302d44500400440b2814900840601801c07490000c842d03070800c0141c008800340204800541040202c507040b50780300001 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 775341106 1250 775339856 775339907
    0x30e0309012a150e0a0f060504022707030b0312040b07170417010e2a121911040902030601121506030b040203010b040b0a290a03020408070f06 63
    0x1c2c50101002204203108206000418400c3c80601c0c01410400381d0011400c2011003c43d400700c03030351806000001000c1c01c00e40707200003010a000358441a8401d0001d003000941c00c894203503440e81080c030b190340034a00083ea4824810842e92600c14004032010507402028040343d85941c182e19805244100740c08170703030000b81c0ca40812010620003502001a07104447d287ca0300c036240d100f05040e6079907a90b0f2540d0719000c11454041800203038105545d504810002c070b0840c2d80c1e81511101681c4600307280c0c00c00c440f079040304200c001c200800c6039645d0428404855507082031500e84c1081025401c030612a6007446000c0e400b60354041419411128050051800c1100c070340340ca0104020300b8450740811b2881c0c0003000092250781d10140b44294400c8008001f00b800c10410442154030b0020000d81151640d0028040788080210705c0700d809150400c0c0521140c070185d5698450341c0302c4a171800010b50003140400054001308800e00c0642400c00700c4103140b60030088001c0000100402046088484051 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 775342356 1250 775341106 775341137
    0x201080c090409080f1c02090607021c050706031a0103110415140f03010306050604020c0c060a0215090c09090d05030a180b131e051504020f090106091401030e030901 73
    0x10001081da071020b0445c0d180d840d0300107018042d4200402441945803150700c8042a9021442225042c0d11700514690a02603241c0034460946a0302c10208948006800c44001250013004000000c00841d079011540038148582d136130080d080b26040e43c0c1490304080c500c40152840da416a016214170700070030114001052000c84941c40b806c6010044402c0000d080340d00c409800c0300030350584c1d00400c0c0c00d00c000c0c1c4400f41403004034890044a219a500a444094080d1602c00010b04100b4040c0c4100ca5051242c4070102507640c00c01d58201d80c02d0b070701c40b46025405040c00180d0903400304090b0702801c04402c034603002520703074800106842600e580c1d92000d0304440519498608581d50042c038420310130300e000007580301c002c105500c051b14808045106050040020b5048100c21a03205001d4180000c0c250441c064020001d041240e00c140b81c68447d903903035120718140c14000c1495030b9a20001074a464031410724086403485160425042204003800240000b04440b10700c40b0038a4001c0c81d500074500e = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 775343606 1250 775342356 775342361
    0x3010e060117090105012103050d09060b03010c020c03010c031b14040b0f0a020f060106050708030915040f0303060614030622060932130501110a0f110601030201080c0904 75
    0x80e0b44848240401804a0f4a1056000d541600e0703500c90340c0003040317004c0134809000c0d94055038004d00051040018519110041c2c2045095620961011810302001c00010b82580c096007400c4005910400e22600a89424040c44203992080d04003001140b40d415058803401c0c40a5646e07900b404810f00741d5507030002010b03048500508228203420384500c10b07144c1030203459002502410052040c90005c140032200800c1d994129421621024603180a607502c05040d41c00003040d415440c044c16545290500d4007440d054825071064201170489502440d01804803001500044c082142283c0c001400e20349010403643c108400300c401b9040340c280d03110080f05c0340c5401103041304281c1c10039a00040240c90740d04500f1000802c2d00900c0714200b002c2000030404039069180203a007418002c007280d100310361184044031444c09980041601011503184ca440e507800945840c0001d803000c802d80c98010f5105440c0340d0108509000b0700b6055255400080c0034080c054052480c100000941e030300e499a03141e = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 775344856 1250 775343606 775343627
    0x131a07020402120403020c01020d0f030e0106150201051806060f0f1309050609012706200a0801090e03070b0f07020c030f0f010516140d020909150406050d02010503010e0601 76
    0x3401559501007098100f9403502096a04801512400d14500b44660010a54000c084090b40e280100c0c401d00b100120003410580c1d00210465607240030204290305407544007542c6036600d40001c035140c02d011642d4051140150180300709500403809000c5544d071500d02c982d4800008841518002040d50002a55031844510103845076203400c60070020004041140391090310104020403241104503810300040440362109490031b10162030100000350300f0b62140a0f0200e581d0300104c59041d03c1ea00b890f0080d030091075510003041c0f070710004120030002401512444162807001d035082c54007517503e0b8000c43d1009003910f9148144440003c617018030030041c009219100600720b440072290000c1d4262241125800c2c00c00a5003884d001402c0140c0d844601c0d0140100c0d645c504085500303609503801c00d50842902c202446400b080074100b03607680c2180c2e01c1e00a2031321040e40f4802e0008078080004075445a80301c94001c2c28400301c600003507070700002a80d0458042d0381280d0703070aa403001d0040f80c014024 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 775346106 1250 775344856 775344859
    0x91509180e01020307080118061d07050c100615030b10030917040b032505030f1012060e0601050a0f031b080109080d0606051c020d06050604060e0114131a0702 70
    0x8410011703a240e200900174100d4421050440d21804030000d51002c0c1e4500e8000c20150894101c15212500d0a1420381a0b02221920304107061010451b01a8181041c08417451159038580a003403241041070440358000e0500741c141003094020b000d001c20f005c0200002d030a41895552300b550018408016520341c49405200c0b5140e90311a110a4030302040c0c3c2059506000891105002142169000c032498481905940340c4900355600c040c0c8240c12030b04000c0084030f884014841c0040d0b00c24903a9950401c0368443c00e80441d0404e00340c44c240f40b40440503400640f042c0e280c001d04000d40c05014110300143e0350805c4c0d0798444540c04000e4191601d019a121040fa0742c0382500303403c00d2050388805007416540b100c805100031652010111181c0c0a1250a9042c24101411290003140a076006081d003407043c000220314a903668002500c01e0f0040e0740400085100039480b00041d40c0d0192040f8900083d503650a41050498902d41a615030346009200c0f112183c0040840315502050a541ca10340c0e0 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 775347356 1250 775346106 775346111
    0x302070c09020d02070c290a030615080f07030c0504120c031707050d03020405010806010e03010e0a06020c190c031218031109090a0f1b05030f0d091509180e01 70
    0xf91110044002c2d030088000750342000403103102146000507200d030141c6809500341c1030340d01e00701d103200c040889500840742c100c10305540d8940025442100c49400d41705c11090303290a64189403001c0360064102c0002c018200f00f510703059007012a0b64101084c2d034190f980181d070754502400340b49080305800d0760030b4102400040d0441c0542c41c068180d5002000003034032490907a01a1082100103406901032405041d000c2107503440000d560354030900344601d041400400110b541b0007030751110b070b080c00740c1b012091310700d25000180e1600e802010071084410540b000c00c1e0001c400d420342c82d81e180c62486400000c103500c50752250079450314810007140343d4608000b040111613550320b00c4c144040000c1c00300c1950181c08a440041d594281c0420400d02898025410310560002d554507108000246004031400034405403022405880801c01c0c2101c005e000402060881c0c11460041c0071218030741d0140702c800b082c1049140710107910500d00e10884054005802400c0c42e140d40d83c2e0003802a403c0143c0181d0f1 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 775348606 1250 775347356 775347367
    0x15280b03090109030f0503070203070201031518050702010b0a050f09100e1005010306050105071a092d060c0a1d06070f0b0402042004061b020316080f0d0905010302070c0902 76
    0x40301076002829561003605c5840e0111480711050b555400101c9104000d81c1050003218099406904110040b02d485003502c103e50303440c1d003403128214400340217201c0030554030f40401c040f01c1c2d024891000850070031104103258600d018000781d2400c9610b40158010f03012640421148118440d40308080c02009903254140d00d0002090404c044030b43c07082500207400c1243c0054203500a00403100055001803020076800c0c0c0f14609480c0580014000b03a24520070f0703101c80a103640e034001316070b0038080d4005002e10011504188583c1b400c10702421340120700c04204168040030b50480600c8205141e0309143c0444c2c29144000904240103e507800f800e986013100000082100d00030019114a01c2200d04000000c00d00e040d064a94880300a84008600200014080d85024094903d100008158040310500499020900b0400b18440040000503004010b210408090100c5030b80c400042004100c20200c410300184208450305c02c0605040c1c0c0051081c00748400b8403200d1000c6d180305075041d507588 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 775349856 1250 775348606 775348621
    0x715061508100603051029030106110609070608070c03090e0a050106120c0e01050f071416170c01140702040c0906020f01020c15101203090e15280b03 66
    0x45049801e0324440102c0038010a14502030312880d0700441074240303104606400d0012200074840380107240c11135030114003203004100301041c00031406040c00360f840c3c0107228441c1007000d1a00b18007505a60454000c801c1c00e0080550182545501060030320741070003120302e00e007001d5801c5242030b04688200030400301000032201c85900130604895856071840c540c42c50b5481c0c01d0301121104240d100c0060390203c0c0d03000306503220b20007910302141e5000707980d031820b0b03d6545e50321810f0030752040d0600c0c06c1e004007411100c1c004070300c88200c1c01003040c02a0b209881515103825078440000545407414422948100c14850070b000b825078201c4d59001d08100920042d50202408180c01445404014410707103202070303081d18060094a40d902c508000600d840900300c6510310000d00018520024219905000510012048403210032a4081c0c2c6030701d0101e60070101c0d0380004080081c41c1a2012141020780415500c40146815a0944480b136083c1c031700048040c0308030005061b90040115a41c04018040c04 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 775351106 1250 775349856 775349867
    0x230603250806101107270912020607090b0d02030a1425021212090102070203070605031b04080c010c020301110414030f0a050d0c030e0406150e0306010b07150615 71
    0x180104503000350500202d4a011200e016005440c5003072901700d160200841e8814810300c003480080d21104c10902005601c41600310303285504161050341000700508031242d01840070740d41210036071900400650406c51503131958416240c00034121540040001c14110195000b00400e80748041410513a040480c0483c0303018030022200501c05022742c0c00001c3c1c0741e000080240400000300b1580c0d050042032281003240600040100a15540030401c40006039001d01c0303030102804051301c8041d00c8c1d003410b00714036550b4404034601d0159007104200a00a00c0000552107150f02002d1a10301034540241c400304e13001d0200c000780904982804580818500700c166603600d11580282c0480c0c9610700cc0d144007075a0344441003006071a42c4c0007000c404000c1c03442100f0401655000c0d00b4030b500d030341810350042070441c0c95a030701641c14040011141c08486034010540081c02000303c2c0140034035410102100083d11030204000c06179100e0303034507607180c542042d046900148007400031020451070311a0302408 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 775352356 1250 775351106 775351111
    0x80606034c0c030506031203040611070309081005070e0405070210020415021002180d0507050d11120c1f180f03020111030307140a051b010606092306032508 69
    0x1c030350b04114116101502c6446410303c02c20780140102032107480344039003400d03c6c0e00c05402540c8240c3c03940c4450303242d1001c20300244412486640d8403a8050315040135142811004812964440e0410f000c5c0511a5800265159600c6044a001035607840d00c880c141d1420000318002c80c00c450000c030300019a043c02c68030080b2103c10a4095922402161300b0050032480b86d20380ba20850030300c282414107541882502c04441510400454004540300c100003039030482c0d010804c44100d030031000324051509105401c640c1000d00342d401401c604d88000c000500107880014400b0500d030700d1049070040c46108070034034000c02c0349400b602e14071a602c58040799141007113070005a0110703441021800c0a840c00104a03403041c0d0f034582d41c40c0c2102601c0e1650318900d62010f841001001424840001181a04c102418241d25100d000181c05460507001034525030440e0300004808000c240c203100b1405032004013501d4614125146982c03aa501b40540403504141400c2c001d4a00380038801414294000070b2250 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 775353606 1250 775352356 775352503
    0x120f030702011d011b0819020f1608180d05060106140f070804051c050a06021c0e0604032c0f010212040801361709030f07050a08060603 60
    0x419021048038142c07030340b000540c3c60340c1d6060101c1c4511f074021300341390380070b00075146c03040013000d1800c80d41c400c00020300d00c14941c0076165220009020304141c4111700030424422002d03501c285030483c0795200c0d41d0320f45c3e405208090505c0410441010300f03e0382c40040710040c60105841d5612094142811203039078125004044c00307080d070382461107101c07070b9051040c240d800d40c44001050403024650700c0c00065042503e20300e481c04e6116801c24580c0320305011b41e4407401c54403802030082d80b810b81401401100102540e80848048034809213029200300112582c0b080e064566031002c85041d00100d00e00340c042c1c0224070380f184020401180400064104450301c00a04041040034001c40b1484000300d076401041412500c8100c4520001885104000c0c2c0041c1b10201414100009180400c0c01d10080038030000d40b60b0010402441249403005204018040e244001c101500d844004241d881c8506210200b40080300d01500a24403102001124424251400041c0da101d201c100f5400404d034010924 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 775354856 1250 775353606 775353641
    0x6131815060602030f0a0c03051204050a020f0103050c1e040504020703111605090114150c0c09090604020102060426132d0b2a03030702060702120f030702011d01 71
    0x25080f0302c000281c401041ca1156031904d0070b10b1450781500c003948124011000d00809001130315089c091580c100380b045000b60090245081c2c1881041040204c8801c00340c18507241a091001c8a40c040040d10082c010111100d00022201602c004440c02039502c516402400051900d00300750707020f8100b00300e0340620f00490300c0765a00400e61081d4030045010310ba400404480c0104411001061403003840306000d8100c00d0400c003205d10f061000e030700180360a0100c2d4003d40c1d1841c0103081050b005036200c038101c0041e00541c2040e6000030345072200904050403100414101c1080d003290010110655540c0b40d070103c0daa0006800300051505262044048400921003404070b895140d20718a5121803030050011745c02c50401d80782140f550040440c4c8581042043c080941d0282404040c245603140c1c500259242d207400c103802803402030004c14102c21504400541d030320344200f550554a80303042d40a066500d9949010089004020050340060007480280072104100d006600c620118510502c40c07 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 775356106 1250 775354856 775354859
    0xf0a080714070503030d1a041b091410050304021516020117070f0809070906290c210d1526070308070611030103030e0a090c080613181506 61
    0x5042c2c880c20030f40300d03058060700300308010600c8403019808a180051825a098803140e078007030115003182c0252500c5648c2c14510000341c0300300ca070010700d0b410007014005c0340d8110451000020600c002070780c0111a0501501001040842d0346085c00c04001c0b800c1c100485440d5500c81c12605840403040c0d20590110751481c01022a00681c6540760784240c105840301103510720b1103d07044a9100f0001c03c0c148103070045200125031042240140002007030795000700a4902414038600e68000400a1b9007410b040702002000071005010a0300d5501e40800c0610400040e101524034484cac0c86170a000d0210302c0d2518401d0500d00c086010b80743c058503880031040180c64090112601e0003568040401c1c4aa40201020400a90f4910041070000c1c42200080f8800c1da65a0055480c2d070401e0700110f0114420268968090610440c0b2400420580800344600b610214000c0c0c0700c000060720990040700300c54030740084040c42e500003202c40c0d0218881404c5440e0300c0d04007055040c49180c0704281841c01c0000 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 775357356 1250 775356106 775356143
    0x5100b030408181306030809090709061d0402070c0303030903020c0102070501200106030c12060b030604150203040609051902040605090c04060c06061a0418140112050f0a0807 77
    0x40d68803032944490420b107000c0c050711201116a24480c0708035071052801c6504c030030780944c90241e0002144540c85032030715a68880200f024040000342000200113011004002140d80040d51440c859461480a01c04540e40d0340460041c0c0719420700a020500c504d0800004c1560561005800354080d500341c031154504040120707104d0b034031b43c41101d00003607a00d040c0010310207034000008076401540000140e1180e0702d6807598030202c4079610950a08649030b103640140f2a450240e4450ac100032009000585415982e040c0750001500d00c5030000d580c080700180030448590711802d50b41d07800004a40050558800340c6215041c0ba4000301c2c001d07070500d4400102d40c1445030600d40641c4240304060300789420082c00300c410416642d401e03540580c6454000403c00c3c01071b52144012030701c0c1503149560320304203201b011034402c1d030080c445202031402504044050416010364152040340701500081800ea080413850140340702045000c80c007480c0c0c0481708000445000341209841004042000002044c = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 775358606 1250 775357356 775357379
    0x1803170105090c1602041d070b030910110d050a1a0306040803040605270d0306080f0616170a020c1e0606010e0a1707182306040204030b0a0510 63
    0x401c90b40c100c1881e5010440040151000e082803000440d004032103982140c00240541c1c07054042441e5010516140035941201401303004080d00c2c030340000a155050030f0003029500c03444141c28280d4656035100b410004240002180c003000d540d80303418042405d01c810b42c1402000001c0003c1d021084950541c4a141408074a86200e941c1112440307007190f6450b00d4030400b41c80f004084080c00703800c42c4440d1080141c000600c10a0703891a070010903000740400c2e0098101c82c401d4005002c00d0344072400318000302500103003044c4e22200c030502c100700c500400e00c0162a0268202c45c11480710100404200300e04c5041e601910440291303204540148e41c0d0740c1154406004082001c0a40b5003181001076010750142508001043e4083c0c281c0b094030769242d4101d0f20300b9828410390b900c190001041004103d410980482050000c12000c201c1d4080480440d59442000c000c0704486002520010f201c3d0b5a40b07a040d14001c5402041c105003500d400900ba00c01040105e0b0036040c23032100000d010800c081c201 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 775359712 1106 775358606 775358609
    0x80403060f0b30191a010503030a052b05060a090e07230a03030909110406120b041116020312070201021f090618031701 53
    0x5150260a80d0386249841c2001820000c501d25a03940b240414441d0840e6080c42039500490352400400c0e000d180c01ea8000180680e0108a2030300400300440e4a03010301c00c001c004d680f55109000071609060a01505030181c1c000d000190b4440e0159000344038410400071440740c0303c4851032035401c4200405081504160300c81d02031101e1030400f440008068141d40c1020f2104182c54170794155258100d200300c10420184145600c03c2000020300c0e504104400340103080c0142e01e0f810080c00b0300c8943c0c032a8a140601e000840d11850f600d00c0c09440680d42c0d02c0e0780c0c40c5000254282484082d00341c00101c55800307640d8002e00300070030405100500060412903a41c080c62102401007506004001d40c11030000403042142c040181c4c0d010440004114441501101c41440382900c640100034142000f07000b11b29109165500031044078041030450f201c0c0e51490301ca64079048090520440a = true := by decide +kernel

theorem cover : BRFrame.Cov 775179856 775359712 := by
  have h0 := BRFrame.cov_init 775179856
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775179856 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775179856 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775179856 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775179856 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775179856 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775179856 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775179856 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775179856 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775179856 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775179856 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775179856 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775179856 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775179856 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775179856 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775179856 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775179856 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775179856 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775179856 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775179856 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775179856 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775179856 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775179856 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775179856 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775179856 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775179856 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775179856 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775179856 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775179856 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775179856 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775179856 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775179856 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775179856 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775179856 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775179856 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775179856 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775179856 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775179856 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775179856 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775179856 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775179856 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775179856 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775179856 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775179856 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775179856 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775179856 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775179856 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775179856 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775179856 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775179856 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775179856 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775179856 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775179856 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775179856 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775179856 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775179856 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775179856 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775179856 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775179856 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775179856 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775179856 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775179856 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775179856 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775179856 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775179856 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775179856 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775179856 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775179856 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775179856 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775179856 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775179856 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775179856 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775179856 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775179856 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775179856 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775179856 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775179856 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775179856 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775179856 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775179856 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775179856 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775179856 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775179856 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775179856 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775179856 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775179856 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775179856 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775179856 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775179856 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775179856 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775179856 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775179856 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775179856 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775179856 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775179856 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775179856 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775179856 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775179856 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775179856 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775179856 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775179856 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775179856 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775179856 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775179856 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775179856 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775179856 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775179856 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775179856 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775179856 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775179856 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775179856 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775179856 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775179856 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775179856 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775179856 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775179856 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775179856 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775179856 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775179856 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775179856 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775179856 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775179856 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775179856 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775179856 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775179856 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775179856 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775179856 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775179856 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775179856 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775179856 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775179856 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775179856 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775179856 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775179856 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775179856 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775179856 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775179856 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775179856 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775179856 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775179856 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775179856 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775179856 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775179856 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775179856 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775179856 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 775179856 ≤ n) (h2 : n < 775359712) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
