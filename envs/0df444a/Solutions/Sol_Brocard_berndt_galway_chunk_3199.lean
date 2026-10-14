-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3199
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:57:29.961144+00:00
-- url     : https://prove2.me/submissions/8cff44cd-2047-4a44-afb6-94d8bd316615

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 575179856 ≤ n < 575359712 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 575181106 1250 575179856 575179879
    0xf090106030e1e06070c0519110f0f010f03021606050411010809120301140f18010801061a181819060803090d0818040504050309030d080705030109230907150905 71
    0xc540900314140d00b40c7d800d00584054049207075422566103c6280290001070294000340200464403400488641c03080000c056416801d980002d4181c4000b61395040043e01d95013528000c82913000811402441d443c5041c041104001240440b03011403035080e42d400c409035a54403101590b03988822001e41d5800ea061004002d40d16501140b0640c90748087c222844000d00c2c50080f4141c10a410814245c0648000051042d500b003442181d00900000080881c101c034001d810307414a210b030fa40c202d0002c1040c404600003541f541401c6d100340f0040c1d0000b810701860007048180024411003900b107000c5090450020f00c0c01e2001056610030440245a1200300e407243e40c51102d40d03400b25444606400700e81c0c0d084001652240700da5482580502c02440d600c10080d0100b44c10104c03000c0c090014080350b44140921a40d0082c10703281520f2106000083e510440340c81c0052482880441c903020354041c0003003092200c0c010031064120307100792001813043e1140e07603401d54049032580907494100001815 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 575182356 1250 575181106 575181121
    0x204020c07090e0f070e1e0a0c02010b040209010507020d0c12030f0906030b012f030f07020307050604180207080d0c02101a0112110d110406020c06070c03110f090106030e1e06 77
    0x203d041d0041051f0310100300b0104e0300c0400076034110086609004082e0b59140400c402c0d9028050b10000391000c0b0303030071403608010800190560140490103405924036422450400104152050190520140f0348065036100d01c1c0052010f0030900106000402300880050907074001d0047c0300d0740c040143c40e26940042511741e038550700034540011107400f6100005c0b4100160b020b100070700e881240d41c0403455070f0700868014141b60200c541e024030b01400b0b04220401604100d0f0f490701403c041c0c0450090ba8030b030518103000145008080b5000c0b072043c5802007080c1c88075000100c081c2801c49401003800000c050182c60749071049203001d001d0101e82251403100381d080c01075020f811302060104030740b030500004105004c110b072141220309024010000c0c05000803901000340c0c3e02e040e1812600b86151245a9540c5050700d100c520004000700044403c0309003a90b80c3c54600741c406134018001c0c8030740790b94a41006000c0e00c081c40b922402400f40c2c0c0d00700d20400315a881206408c0e071030180104100e484420 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 575183606 1250 575182356 575182379
    0xc031008060424200d060b09150a05070b011d070903020310020c21040f090e030a2129090402031b03120c0106060f0203210a0204030204020c07090e0f07 67
    0x40040b10b10340d900c002c0c1d507003035034110070721043d4060100c04c0c5651903455600d03d44040310040d42140e5140b407000e1050070019520510f1044550681100045d07c49101d481d00350784a0003040c10003000340c0d8170f410011600c0070501c41c400e82c0711026400c20f00140d0700c420700c094803d10302078000607403d90005040d8070303107400c0d46400400d84400c1140442d501c6810641889400d025400c0c200162890000b03001c20041e02003458030005030581038010403191111400c0241e60344189410002030001e0f00400c02001c0591000081541c2c1d01201c0c103020140c03481110344158104258092a100c201d819050072600303000507014810f982c090000e04885510720805103800c12a803030ba04ea810301c2614480418811544003500c181821040041500780c14940040e041c100701168103c00c651060000f140101e0411000582d800c0001c4403a4006889103600c0c0307006442140c1020f0341050001600c80e00405000801c0812521074500801c000380b00f41c1c0900340c44080588070304020b43c0c41940305024500294 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 575184856 1250 575183606 575183663
    0xc02010813021206060108090d050405040911130902030d0c081c0e0d0305060a060f0804060b1302040b0c070e010e07030b06090a14100503011d15090c0310080604 71
    0x1e5007200055503000500d0340c004280030180f1500314400340511942c02c166096080513102001c2d0203402d01d0440000d0640c0180c3c80b031f0038840d80c3c0f103660001c1440005030208540d5800504400f400350b0342c0001503000b412610000b01d000307110710206404018030441d0807603052580300540a16100304c8a10700d0505001e11160422090b607102080d1221100070000103a400030143c401017031500d0020104414000190b11020034081c174001c0703050019920240c2c1c1984141d03c42400641c0c50800320208960f002da83d01d241d826688000740c0031072406010400f904901c0d0500c0102e900fa2900d82034000c603500800e20907041102c000e4400b05401500a802c110084032000d0308a60800c502d001c0041c08110342507200300081188011859010304110003600300f650100d041980c0b0315490032a1061b1100c3c0c407100211010b11030440401c10421508a10121140c0001d25410541c02d1034405108668025a40c103500818006000240180e0104100f4030498220652a60701c59043d1a905200c02c0c00 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 575186106 1250 575184856 575184871
    0x21b030a111201020304240b060a050d141f1a0f0304061121090105060a090b01110d0806010206010f0303170606130305071706010e060607080c0d020c0a05100c020108 73
    0xb81c024220200da0074406184207501580901080a00c2042045500b030000c4102045107400d1480540d010344803203045600808840c6052a80c4201d0054a04001c0c10040880d4091521131000d1103445c1303544100159415040d4001880c1041d0303941960f1200c012958800300360680d00303000d40200c1041690195034064041c410201d8495050041d606441d4080e00c09601060003220405508003040c0d08080d40c440d000c0002081700d400c25100103440d1181303d100b03c0480c140c8541940786581d219200802e00b10903904119203c5100c00d02000d44540d01c220f80b6603005201d40000051410b01c0183d060049a805441d18000b4401c0f5042040740401d008000d50340181041003a005000350300d030031501c021401600038020741402c28042040824840740c0240c1c8035405500103201402c600c408480e000001180c81c981e5030314407440d114020f4001d004000d1041c0c09440c403060b00303464002c1443d8003254070444592000c140c417101045462080c1d218242c000442440c240c800650003031034101e070403504 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 575187356 1250 575186106 575186119
    0x30f0604121809022107020120090f0603090606011403040b010e0a02040305150105040501121109090a05031201052e0c0311010f06210b130602160305030601021b030a11 74
    0x3c640030f264060b03078002035009240309502100e90041c03101d005400c90708805684001d01c0740403036201031545a45812481c0e0440c41d040000c0c1c070002c59642d000c0200c07410070301070483e54403440c6c40103440d17441d000c045038a240450f80c4801c0113000030450368200c0e8441ca50140b58900d199081c224102e0341243c0003846811401c0c0c0c00c00010002c039408000b0b907200c00325044100986176041a05000c01c0d41c80603408028003031210844540090034030928414051029586100075a50f4501d81a140003c1058040c1c2680000201d50284104440740c0c14161202a1070f90f0990f48800039000b0111004204080c1c01401104904e03529184207100c0e09005500a10b07001034540a020582800c64030302c0c82400020660343c3c401004455900000e1115803012245500d01240c05521080c10100c001045540c0c4520700c0c8018000f0800c003507040e00c0c1305d219035044440c01c0c0c1102d1314010b0030584c026203c29004d44150344800040c1c41c8200801015010b000e4003605064000c0c3c1c1c0d0342002c0802e1030004036400103 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 575188606 1250 575187356 575187359
    0xb0f1303140d02010606050a14030c0403060608060a0b0d0209131b06050c19020a06050f040305060c04030b0f04021c05010e06130c0b030609040215090306070509030f06041218 77
    0x4010300007094584900070040e040340003010740083d00315071883d80090305000e000d01040e800e0030b400581c136a89003010f16801d2a9241c3e500c400c0031a540c400c1e07400040000d85413034404a031780345e400582284a4041e090040180e074284008014101184d100c0081d480381d4810700182102d0788500748912954424220400a001582000b00c0c04000e00c2d0803880c0050000710301c44040c05005c0106e81c0d0900384150014122000300c0c0c001c100382c0a414012a0f060040010342c2c02d21003642001190300460308031003919070ba420102c0030024294050710044e21102d01d2100842d075143d011b550307518051640103124408542d5081540703102144241c10031354195580707012400c1440000c0c020380b40b18a8001d80426030031400307403038154008a10758101c0300c0840d000340304004003512298002a00690122141203040100608100d05840741f06d168035014080d03030302801042c4e90090054140801304809440001e10100007075690341034215409040c1780641c00c1d01c1959240160034103031880402070500d80080c0d = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 575189856 1250 575188606 575188613
    0x603040210031b020f07060509030307060506010c060915050105040516032013150c03120504081c1e020a120209060c0601080723010819150902070213060b0f1303 71
    0x19100280f054056009120103580c1074100384003d00140015080049c10480e085010a40e02d00807030000404060303445000ca442a809400c0303914005621203401d1040e01041e14000003e02c0301c040400c407119081c240007040c00d1a207030040c1c1c3c0c4100708604980720400b0041d0412006003140790b458404612103021021901e90ad44c40003000350201c111a00866075290003201060341c00b214504008200b407400104000a512849a501c42520150007145603202d90410094500c01c680c003c10300114079041d884640f45d03140d000101509030040070200f6800c800720800060f40f20b481c0b205400503505d00348081c860340e016805028190b001600b120300b00480e80091614048083e0092006a4415203042160302241200c41c251141c0810480032113010440003e07110782006880783c1c030200c0c40300400e1680c1940503806090030030500b5070390b40c55180e550240d10300258000d4405900999036a05442c20a1205003d044102c5050300300e414a402c8002e0209242508022252000c0c0c9600d901c001020 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 575191106 1250 575189856 575189891
    0x807030b040204290a020304140310020a02012018040510080601032105071a190c0903290f0a0f060b0d0b0405060f0628020304030515010302060304021003 68
    0x9010403408000010502144c001140e46640340b00d098000000c00c00d82d4161540403095030200d0300c807404501ca8908a41001038184180c81ca6032040a5101040791030081d5415001000e00c011804080503076001484c911003100d00ca01c07004540c4241028051000f0350505502c02a8080c01c1401541000c43c0c0740c3c4211401d180c0d00303070320030340d50741c06285003150712140005140300300e10015051041c6404041c0e50f40080011840d00702c030b16640307203040006214415802d00d5414116170500204608230f171084010305010414041900c0c1414400c0082160703a410744a8046619041c0b00d64120641d580b078503003060800c00415401d215900c0f80c041c1c0201d03211324014140a04003112100d034031500d1076800442105d200e4240d03a13124034201014048a900c07486241c0846e81025500d4507500c10744200f6070f40c0314020014003e081140d4448036071240c154080080c100703492042c1d0680d80c2408001c191051502001c1c0030180d40003100f00701150041c50400c071321100003801800e0200382e80d1480d00c0304c60301 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 575192356 1250 575191106 575191109
    0xc2006220215071b121e020d050f0f030c060a1d0a050703060b040207020108063705040509030c0303270d030e0601050411090d0203010b03070b0d1401080a02010807030b040204 77
    0x2c035107004074110341000003e00300540e00c644c1038510202d01615006054011406042010301440200c0318080c181e20580051032800903000340c13000319809100d140403030380e413101c42d1101f8100b40079a0241c07041d03942e00401290324001c0a0001040c407512854805c000420f00c015102001100302003011003500002e02501c1d52680c02000034120240c03441c1007100c00d950000910b9072003144100040b0300140e0700080c00a070803040649680b0707040e051259803941203060540e0417410030702120050b0310495102c0d031502c0080d2402075030b051190717407074001036a0354a01441ea803189040e0014000a00482c60400c0342c601f01d0110707680b40c8004200d28402e041d0410800c050150002516040d070194900380c10441ca600400c81510304200c3c040107444e00000754001c1103e03035071003400d0071b001b0003041d503409401c00014650000c0075901c6072951600d49104540c400080716020500302804494400d0750745404078100c0d10080f000e00044a45a401100d13440c10080076801410341c0c9148810340c41d100c80c40a00f0 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 575193606 1250 575192356 575192389
    0xa150311010c0c0906140d050d08070905130204150207120b1e01140103061502071a040506120702010b04050f06011815050c0114070c02060711060d0c20062202 70
    0x1905d9410241c4038403c00781301c4c1409900030100105071800003a400115148090b40390b1a10009640f241070f41222000000e81c0041e910040360344e444884100c2c140e000f0411214040800d03201c841200341c09988450303184c0b0440c3c204000c01104040417a0265400a82c00b100590480010641907070316400c0030402a0009050682c04032008031855806100e007801a04a00c44c08a40326001d1540095591103580911800070100307075401d090840f41501518050a401002e5076201e9640c6164060801e0040307a05200560a0005002c8240bc1034490f0501070710000541500c036946044c0191400c005c0030001c421210050003000030440d190044009610115946196903030f640f075101107081d0390f21500d454507410052018400e846800c140610390032541036940944414050034918a030381650b03c140d50b041900080c41996002e02e5a00105440c03003d41c40c4d030401d080188052140b488603a06000549a010f000854285421840d80e0035040340346460b03000e0f500296a01190f0481c42009581 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 575194856 1250 575193606 575193611
    0x6160204050f22121107090204080c090f01080c0607031701060503070207081501090b01050d050403030b041407080a020313051c020c0d03140715090b040b0a150311010c0c09 76
    0xc840d800780c039001c80110840c1145446090f4849032030718850b074140403030041d0910405120060700d801041c0a0b510080c6480c4004544540d07550056540fa4130602c0302061040c40e07001d001886c028448020769051b01d040100818001c207404082c0905580582410b4081c41030300c401540040b600e1456081c0a0402c40d51030340e03200e04108401900d4100305030000001078025296100b40005061540343c111600c190000c14401d092500680d864030071100c1c0400c0e03941c2408104814103130150050150703c901a60104940c540c10541d980c0341c0c06084e1507079400a00708a0209600d001c40d60040c5410410300b0841c030f00c00c90700956503645003035501145880c84194408030180d0094050001046002094a208400301d1031640c3c014800710f0491403060321241d021903403005002c0c3e0340688035602e00261800b04002a1a4103145401d0001141e0458290800600240207191640079040701200e03080056001d03141035a40d08a5049030b041c611904002c6250303409800f00340c1340548072009282d0100d00 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 575196106 1250 575194856 575194861
    0xf04090228090608161d060c07140a050f0f01200a06050a0e0703030203030c0a1709100e0c0604091e240614070605270f0c09040c0506160204050f 64
    0x180920030020199041c41017102680000c0c1ca401ca03010418111142d801004201c0d211000107101e4051000805118403805501040c16030004d0400740c1074403412a035060195a03a102049548040d45458a800c0428080c03452007650203001d041d0016440500b02905280d9130081c0145080740c54682039070303c20f44540c140700018095204224880c0350280140041c1030850306c019540388000341c0480c807061000604000c00e54486d1601841b0002052402c1640e4141240790f596241a000b4100342640d01d0103490304c80c0302e000014802003039031010f00024200362814400364000c007030685560171246102c400180c001c400d644500b540f0f980904041081801522011600c0841725400401c03c2c04491710441d19140c980384207139088e10b0351004011801e80e44215020401562104d0050003c150100c103000d44004085540c0e0381009000f030456400b640e0303ea042082442d01550041d0100d04000020f0140f800e0103070051100d03000d5410340c480d000d050781d4041405c84e58121066004000400306 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 575197356 1250 575196106 575196119
    0x261905040f08131806060f0f1e052a0c040b01030609020708031603020c100c030b0a17010c0504050a060e03030f03040c05040c020a030917160e06040507050f0409022809 74
    0x100c13151062541c403410801e5904084029061f991000c0342d602c28400310310303000c11540307200701c1090741401d004100f05280f5440fa40000707400c0703803c00c5110b6108114014506884504498503250118002c07034018041003180e4000d10004184859207141050b45811011810014500040031000d00c03801503c1e52340c1c40c000ca51018140c44220007101018010042c604a035000002c8e201c2c40103905080000d000021540154001e2104181a80d04580140000181419449484004d144410000380000c80a120f0115100d00c680d0081c954014608407007882151300c921010160800301400702c81c9001c2d052014414560403c440844601c03c03001000c1c401030609000e544194001400180180609940e020388405035600401880c40d508980d41031555504000e07103d03950031480c8000048548481c00c00c6d01c10a41264018001d508140c00305a00900c2070301140c865002d42c8001a0078603040c10080d9020b0741c0032a070481c8454032240840f01043c1704c6001182c100407065228011014038014 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 575198606 1250 575197356 575197379
    0xe06060316060f050d1413050d090609120503090a03080c010c05031512121c050f060105072414040201030c030501050609130f0c261905040f0813 64
    0x300d460411180310400c01c896600302035400c14140306420304030303118132003040700e94000c00b01458280b0401c102082440540455804007102c1d0710b005c2c80a0742c030170329980e005c20b80720848ac6102d01c1e8002a0400800c00100c1008882119680c0c4104152454014028001141400f291304103503000b82c40060761100d000401d01c01c41901030341604205095103000700d11040c684440008050244000c507240350050b100a1203144085002c20480700d80301c840122902620a0710f00280642d8546060042030036503081030440c601c244070503551a894822207a4803900940c1d65076070503400311448501c001000c1c80c250f000741404209100d900340388030300d0240001020b840d030400944060602e004010701c0749460f00f07c11500211415a403020507411141d42510042441400000d000c620300f0440d243d120b5070000b51900307103d0706c01010a10b0b20030740101c0d29000c56810758007012040c401d454544100201600103551250149000d0003904070b0b04e0b1100412035001c5902086000d0034400188009c21a05 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 575199856 1250 575198606 575198623
    0x606090e070e010c02010c110405150910150c060b030601060c05012a03110f0c060402101d010e03101508160e01060c0c0b07050304050907020a0507051908010e060603 73
    0x10b02c1c040030141000c50003c0e00e926810040a81040703801c0510342c01f07102114078940414440a0700030001d624052000450a50180c10043d02c41e200c5000402c102c0c2401602000695109184410705c201e82c4c058241c07413481c260601218060b4403120720060070742d0306101d681d0081409449440c0d01841e03902d0802e003123441c0d04c04404440c0074041d9003254500c1740d89007110040b030168200000e645900a08010032401001c480307242071080041c011542c14408541580568400d031880c5600603903a103426150f00c01e41404001b240c050003101c0c034803d58460000d400c0c107004050199034170900c01c0290b10061f104070140d07840445008040030480c8090402c00c6103811445e90445102050800e8668000c249062062400700303d1a2a0648148250403c0607801088000e40560b540c400740d203081c50b101d80092080030b108000400020340710703900214614000e55400009010344600348020400307000d030780081e102c490800d0b8010109510380248101c9880d4500c0400070a240e1420000b01468460742 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 575201106 1250 575199856 575199871
    0xe121c0b03010504170a030b0607120801050d0b0a09080c100516020307020618040b0d05060601140906030a1a0a08010b0907020d23070b070f0908030309070b0306030109060606090e 79
    0x1000204000705042100305041412284a12652030341d440000f02c0250076980710323041d40502e00050306010031005046152aa00750703529120211780e41c032020041d0a105100c806058007040c03c00050514031581d01c2090190321a00d405401c0018900c0390b41c0c907000403c902c03054199130720000c1c0201e58403c41c09070b280300809840150314041d04d680c0030130080c0c043c845180c840700b042c01d240030001d80c4e600e4004500321038001d818500e0441403401c0c159540c1c1c0045c0c8540e400300750b4404c40d4007030f0190405d04a503858540a844285542c6401803000000c0414100580018500d5a12a00c8039074402040304001c20001d070010464070700e00c1e001c100e03403200080e020a0555004444106441ea00006510342401030081041c40d030810401030380c5200d108200005209040315810054090f40050340c040d244d01c0c295644050741916029aa5560301c4243c1d04280c0343d900c48002044280c1090009581c07056000d400841d10304280e603240e10903100c0b16003002011403c2d07080d0500144980300b9865a001a0 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 575202356 1250 575201106 575201111
    0x6050c0a0b1321020a02010503061f050a23040b03040c0302040f020c0111090a060c0309030c030c091506020303010b180604030b090f060709030b0403031b051803070b0a030e121c0b0301 81
    0x1058000c0d40d5501c105c0320082c14007a021001400c181c0c2c90500880d0381812801e940c030401908010014099070218081d000401c1011015110013050344c01c403c43c81c50018100c1518140c1003110b8000135820040084071b840f01c00314000720041e1140c2c01101940e2259000158864000303020050940e510b45a5518081d03000380144c1c5101e903a503083c040f040f01e8443c20b1046041c16a4201100e0071001504007502c0740b0f034803078000810010f42d42c0030b100c00c5405442040000c0f0440750071141c0c0b02e1142e48142d0303005170b10030b00041c0101451440142542c0c40c1211a40300c440b01c0c0540450301981080d402620000360300020040c0b0250f0511050011721116001b9000c245420007018111450500001c1d12803053340d0002820140a5440112800000504910780c10b4881c80c006046921203e400798100220121011032414000b40d00b2040d5580f03401d0042c1060700c03c040482c0101311025681840d40300f2030b00101403c82e01c820040c14005461012075108044441003001980c2c0307000d90cc82d000f42e2 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 575203606 1250 575202356 575202413
    0xc0f030307020d120c0f0b0f010b0306030706030e03040f0905010e010f18050406091a01031e110603090c0a081617030702040b011206080c090c0c060106050c0a0b13 72
    0x282d0394040f40b041140e025000405100300c048084407806203000b4002c2040f866103110340203002012100390b21403010090424482c1e078035a8500d002500083d1401600750380508000c2c0311560294000d01070202800040320b05003691000003181200d1107074854102036550b4801448805d00807980c081c003408505030143e01c1d02b40741604c0e141c01040703030b070240c82c1c54107650f00302050400560783c200506441d04501040d4041d800e455002c2d8540b0400e100807a00410200740030100f04070440002c203462a003140c01400c1d00b20703202c014028298001844405580100d0040340510350b40c801107440508829002042150341041c9008010309040c2c100c0c0f0038080105100206440000003201c1c941c660541d00840c03280000c00050720380c0171003541c10098a601b0004089100c100010b05070b52664402c5800251545a0090f0412541309985490030941c00c150010b02295018400416058a2800c00c481d000c10b1240c03a0042c1b016010780f03a00a001d420387c10210103009000d051003c1105100744040302c0365 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 575204856 1250 575203606 575203609
    0x15050d050d050d0609140a0c26041106030124050f04180e0601060201020a080f070c03140c0d0507030e03010e28050111090112180b0a1b020c0f03030702 67
    0x10764680401d0001c02c00001a000030700940d50b00864004c119100040c0019910035403410145541103074000f245500e0030160111a6100d40c0d40d112902c8182c0c160341d50700001c460306081d05510000e2043e075101c520990306030200d4440000841c02048100071030f000d40300c2c0c40c034200c0c80c146000f00803c0d82000014098121151000c60464044880390510100f81c54001c203032000c0034042910340c80015000788400010804e4040d00205440c002c01c5d910783c10959507000600100007c103946200000b203001c54840002030049201488035101c00780d480d401c20501001032442d04420309814000108040b40b0130080540290008140e401d08130000e100000f0705034417050350340ea81c1c031811034041032804040c850a51600e0701400c00c2c00d60410000d0003204200d02d440305180d800070501c9030010b9000e1001000510b26841010b8200300700074524030030b84000d0749444040100c0944850070084c1d407082e0240c42500d500100320501c0c0c0c0c1702d401400f690102036041114040d100e5071034501a810421114005 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 575206106 1250 575204856 575204863
    0xe0c07051b091801180602041a1603050a0c140a0b0a0e120904020405030109050c0f0a0602060a090c12030e0112020405030601031b030203030d0e120406020319031e15050d05 76
    0x864441c1c03030801040310807141214003600301e03a1204a203112545c0c82c40018054560001c01c180c03211802956250680f01d9400302c254404c1000031140d01941e03080d50b200180c40b800040101e181140740098038601e041d110000745031041d0361039420507403100700c0040802100e8109140d00c0800b90b041080f10801c0c0300381039511410107010001071810009180e04155482e41d0544001e800050002c0000c0a10352030825510300d4981441403081c4c18108298215140c003c9075101034444a5000d450b281d107a20701c400e4064841a0310444540200010126890581450b945005d50281c0c2d50642e108040400140100d0407518203140d11500421052250340c40c0040c0686c1180d40c0140ba413a090307001d08400a00c52080340c1c000950600000038007800e41c12840d045144001d81400a44025180d0700c00350101e90300c2940b00d02800340c1c0007801995031540e9100981e000301f1404d4140403c250041010307200c240705400c481010700700d9440e080c00110510010189014000135180403406032141d4940555 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 575207356 1250 575206106 575206111
    0x40b0d060b03070825080a02060a08042904020103141003031103370504030c05060d0b0931020604030b18070b0d0507020d0806190e0c07051b09 63
    0x140ca07078494507a01e440400100c40104046000c0d100202105139080e03240086481000d051441400404203641d000440d10030001680100001e2034240400802c0e17800020051040e41d0110356240c18420401460302503410314004520100503d20305403002400b1244035500c2e2540c4200b41c4802c004945403078103000e60a49402d410301380f20071070039403a02c01e00d580b21726418940448000d0080d901401603000d2501d2141c2d2180c004000400d0184808890300e014500c40074060315039840c0208402d0401c20b005042d07510031010046080c44120010034211700c0c0503203204e000c4096006500d0036180884054402440d240d1140b1090420150000f444502460101605500c07800700441e40607141c1d01601344204800605540130700e81e9603544d404181d04802d00f0b8036806804e000000703240c41e10206540740c1e48907454841e403240b621241e0a008a01011480703180f00400d42c4480400c9480160a40911030188072800030395407000ba10305241052003015001c000142c89405800e40383e80c1d000b03109130307 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 575208606 1250 575207356 575207363
    0x6280f020a051c050f370b0a0b0708032e03110a05040516260c0702090c1306030b2814180a0b040b090a0c090b090310020307030b190602010b040b0d 65
    0x5018101b10751001d0210640d4000b0b081c03e030034881c2d04000303c0034150000128042c04403424039910350303903d8081406206012000701103400c104000b41c49180080303504081d99802c0306061a91541e11000003d13240495081919180031502c0c1184c07991400c200250080e2500361424441c6040c0120403184040c9032044d0705082c04000c1d00a4900305502840030000030502c4643d200351400c0003090f40c5100d51210005a000e01c0d230350340004209440035800c0f00c0c2d4414032032a04940151400004030300502462001e01e0703010001c0506030720034400c50300c00d98025080c000c2202d50030502c3e11305182800185600002d0140041003818000c107080310204a174400c0c041c01740401c0b04840c02c1d0000b0000c0400302c03e0690701290590502088820303640c41404440e0454680c4000217495a01c030802e58010079644a600d9402500bd01e02e41c001c494010b15001549401e0100c0d000840000003000f01c5000e40c441f16081200080410809609004001030200d09650802c0700e02203050100702825080103014 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 575209856 1250 575208606 575208631
    0x15070305030a1d12071104020a170c0f0f03061207050d030e1503010306021306020c030712110406120c0902070b04060213090f060602070806280f020a051c050f 70
    0x968018820704412100f0b0031400160303440c0881c0755078804e403150414402a0341c04038046c0c40d04800c80c14907100b01c130100c2e42c55444249188618190b80e040c21600103001064055040c402c8080c1000e25002030440380c9199000305440746400c10500080701075407141c1480303d601080b002c203c10b48459200702c120303e0b09403504640701082807002c1002c0c1c2083c58480e000c0800c2c0040000140134072503010700091000038075401d42d501c1e59180c00700d039540c2941d1101941604440d008015480e10b42c00c0f286c5400d4402e0542024082d42135001904464050384418400b03980015003c082240c2414000080c0c40ca0010441c00c205d00c6490300411194014401800c060f80000d2200740c41002213100402480b404d141802200355416100700038212038801d44015200d90540450002c03c0421460b200314003a01e110780c10068020302c0200f1050000d4007002045c2d9845202014290450000f4801c01900c0c3d2501c42d07803441500c002d0750f0403c10040140700c2a07840d16040c000004903140c0d08c96008900450309 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 575211106 1250 575209856 575209871
    0x9031107150503090304150c2604120201030b091f0e070207061101021611040b040e0a0305070c15051305030307021503072105101505030601201b15070305030a 70
    0x1c142ca107101b1030b00507207503e01c0d90042ca01e0b142503011004145c488d20952100d08042c003800003080c41d0080c1501406500642071000b440024030700055120420300501d0085225a030b80780229000310340581e4000c64204141110405040800c81c004c401481001a140d0381d92421440c02034803075509004034804c000c20003000080e00002501650401800180c0d1045403940c50700d0100030b8041c0100206000d203040641c0b0304100d1806100b12070442d1404009401404580c2d602151241d100c003500702c807801594038000c5403128250341042e400409035115155190710948000d900c1e0455540950301c294030030410440107840d0940c8107455160380d41d003d60384a4440b10019161082c28683d4060800b0007900601d41c00c0585400c00307402420100b07036901065403112098600c808000f10441c0101d4020000715810b944a0f60b4020010400704446151142c41d00f142030341811a0003402c80c5080c0290003003c42d00386032a4188034202d00b0500180b620386285c503500035046010080c24600301c21303a81c0b0070 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 575212356 1250 575211106 575211121
    0x3090d091406090d0b150a0b0f030c09040207050a03020d18051012020409021317010b18190f09030e010f0f110a05031303120305040f060902030c030303090109031107150503 76
    0x640780d9036103511445c40b80c0b541c0750502209443d070740c0302003c0a20030f11503501c0c00110740c103d0500301c50301c02510300142851070b0f03901e968101c0700f40d0100c00d1058101e50f0801c2034a011400030b00482c0000c52081c2d001e4404d9030000310004024405c64044080e20f08800b40080081e5500ca05001910180c24200844004a00000c1f035001b0b00496000034130590001a0f1910200342050a40c8140c950315049820307949400c016031030803900d1407544542c00000400d0b05480d000b001c1e01003298401c40c5055003c201c0c01d0842040d0040e103500401c0381c81c5941e01c4401c0c08003019006070f5800da9134002032810054054566400524500c61000304c4024418038000406000c0c0085c000d400029070001c2c112903036000104007111180240d0722017910300000070080c031242c02e41300c0e0044034080e41d000310b035022480071030303482d440020081054200d0703151164070581000c540b41071010358410f070300f4040009280c0d034980c2005060014541001001c80d040b90740240700c02000da00100c42007a02c54030b8059101d40d60b440 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 575213606 1250 575212356 575212369
    0x7060906060816092702011b0210080a1b0807110703080310170304050a0314031201030b01140409120e1c15180f020609010509040204080303090d09140609 68
    0x10000040e030300805200e68500c06140001030104c6240ca5010408046001a17801540008006440b00d214960303040102641c801d107000481003c424000c441280c1c100e60001d560215140c0380c40340030940540400410035441e124200980501e1104608050101c402c01440c0f008020282c40a00843c0740007070728420302c00c11508014541c407c10752940c0c1c1c01c0111644102420038403800c030002c10080007175a049103010085d20204c80b8090500c4031104d0075651a02060416802c00d00214031042c444c0440300403903000e20600030360113030320001003e5040081204080c40801c82190203641081400c1c40001e030042c0860781c2c03404480c98801c54011524001980818000183d01ea01c0d040c00400081407004c200071410802c110004100143c1500214401440c0c40c034010251482841003a15409410854020060590149011440c0114ae2000079080f41c2107500100c0c1d25500100800011070340030442d05140da0f04908100700094901214485904220031549001d18000300751042c0701e84540 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 575214856 1250 575213606 575213609
    0x2150708100e090c09180c040c140d0b0312040e040803070c0203030703020f0601170604030f02011e0b030d050408101a06030a0e16150819140109140105060706090606 73
    0x502d0442e051441201e0390380c1520140040c440c41c400030100c0c0f07207006407000741662000800040c0c4400002c00f070800000b130030030000020611640140c001c04001012000700140b80010200181019203802858070f41103d0110f503843e5520304110070703c5540b00304140c1c941c0c8540d004000a80d41d98441c94100c5e0280ca4000f0020340511010403508100f5802084d00e1000429080032aa034680e0784e411000d501003030a40200005c1e0700031001240200c0e1090084400660b064000401e210701c00d42417015031020502e580a200c50f990380381e03020301450180401c40700c2c2c000516040d410141401c004580b00e0700342c000c110245036a0341c203540a14281d40b1108118410b401401c054881c0b800303c01810281c90f8002200d42c290203001fa140c0e2502003000c2282c019603002c400940742000b4128010f541071800980108024241400003081c15416030103101803180d072501c0c841c0d581354901401d103815a01c1c040e070000e440364084401884940c80e50000d031410190410b43c040f6160009091180c0200a503 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 575216106 1250 575214856 575214869
    0x509131506050309060703050f18070305030a0201090314041409041a040c090c0810060c1403030709080d02010605130203061207080c010e0418020d03090e0a0c030c0215070810 77
    0xd40c40024010340003405188100c08110541d0310903074a00d04200d00b1594220b0700000000324900100e401440034080c0c1c0c400c501e10351411030b0000d80c0c50391a4980b86401c010917401c0143c0d150030405080583c410b0711090000358801090341030504181511524a10101c4124041e41806002405008041c0c0d4078100010014860030740600b004d0901000090b15401005401420308045c000e100e4400d00c0d219101e000c0450f4a5600e85060110481d0720f004600c0b0706441039035101c8600641624140300460050036151079191031075140c41e00a44c00d058690b040341080d64503140040100c0e4582980c05150018041c0d00140d4a6903540f0014807260b11200e400111071058040105444a001505060202007600ca904440e60100c0400c02511200340f10000d1403051103070700000600340060720384c000c1132107401d040035815180c04901c0b01940e000c50b540c4501c0c03a110300000701525054411040f00c031000f44040e000c403407240d001c044540d25000e03102c501085042400944ca5062014950020781403 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 575217356 1250 575216106 575216141
    0x501090e28090c0303090b030f010e0c04180c020f0604031d0109081905060a021606020915071a0a020c1b0a08030f042409090b04201306090501050913 66
    0xb114180481d035081c840c0022008107041c80b00120b45020300e1003c2d00e1017210302002ca00601c1c1e080510f410407400c0040e0884003001c13418440401c120301c41e0741c4c5420300d494042c0f00010b0000791240d002458201c0448610340d064201e6000c3c0008640e00500e2035402c9119800c1c2641407540c00c80040350a080b1542c4191214011440a0315690b0f9000101781035440c003071812604180c803540e100204a20646660420340c549244d1b01c800007451580103001500001001c9540e41d810000b07010715035a00040b401c9400c40d6044860980c1458420411904001207030000c46c10504016280c0d6500e0300d00b8440c00000035041100d6428559071584207502511a08040e80d40702c02101c441242c4030f81040c000c81c444000d24000d4041c40c4651030428075525082e076903402c030b0407528201c00300004041d08014180c0040e00d82c00c45881c90041c0703400c06990142a02c1220f82d4444800310010401c0700282c0004003003000640040140307a0b0312905880a4043c21140e00ea2980c0454481000a00e10b05180110f00349 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 575218606 1250 575217356 575217371
    0x2070e010e0403020c09010b090d151104080f0606060d05190c050a110102090102071206270210030e0c0f1807050c0708060108100209190b090103060501090e28 70
    0x9845407890b0140f0700c00e8080f0351403100035104000005009015500c16072a080c050707400c961600651441480d4043c04684046c0c07540e01d0309040a0321082500d10981c0040081c00b040043e404000107811903001102522541c1004000649184070302407489800c42e4444002c22120190120918466509041c01300004602c040700900107403c0b40d80040d01090050350f0b00221700307006000b2038040c1e010590241211504120191480c0303615000d06031449a45c612024541c041e2140744002c47c041c007440500c00e030b03490910402804660a01f4040105428040d440c04841000600784100d007804075201c0000100500114048184492039904810203103400d11481c580c000d001040700040403002d80d0b1580391684411550348400b84a81c2010341d00c400c0700d590710505c0d04d5002c0d01a00100400e41a0802908e010707804407544550001e01e20f1240000b4403541d00e40c1c0500c1031400922003030800754a0300345454085148003200801d01021000e000710303070203500074410480060301c07040040100b0049 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 575219856 1250 575218606 575218619
    0x402090301050702010b040c0c0503030a0507050c01021309060909170c0a02030312040b01060203040b09060f19080106030b0a03080f0f190c0510060803160302030c01092f060d0c02070e01 82
    0x34140c4006c814050391800400148442c1700f80e02c414902900324004601c0e50b280c0380c2d4100c0003000d0040c814000c1007814401c40350701c101300b800140491260840c1c680c02481c01c0681500c01c659150380b010500e140781c840c2e1000020740741502c0001d51300f902803c0a40319440030f00858203040400780001c6d4036000000e640300c004044400d4241c0182e01035808012540c2e00c1c1d03141660341f485540940504500301b445442c09910b0500024194400b03424021070030003400c1c500703e0035010715022641010440100c01401881d506101c0c41016200803580b500038140345441e00d000c1c41c8100301880c80f40e160005248007401c80f01d102103550075511907040800c10013800d40020f002c01840c480803a003038051804484808031450041005442034007001d90f00d01f1001c01d441e1054a141e5110841c1540420701410351070503400cbc862581010300a040000344482c5194007910306a148414443c2a20b4000e03600c980161034003015554100032608001031401c0701010141d14181843d03000301c0d5028903102c008600f0 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 575221106 1250 575219856 575219861
    0x2070b07050102030a0b06030613091106030411091b0405062a0a051005040c0e04030c060f0903110102041511010b100f020c0a18020d14130c0e0105130506040209030105070201 77
    0x80000340400c001d91b00321581000810710080d22417a900c03105031016030101070030b0341d0700c414102442400c01c0030160300004040707a02030300b084800340d03002d12818080c2c04881c10050384460380074040422440c1080b105003480042401240215400303a43c1c04102000c20109001c0c0c1d07090004072000107034034000c03d41000e150351122220b500712858012041d00e03407011055802002e000341d43c8000c0d1211201c0c2130021180744000028400c0e000c01c01c3c0080b00f0804207c49104e4006020304521011548034440d081c080c08400c011910701459a2041000300700420500c2c41e030724040c0c241441c0040700d034940150041d025000301c40f4106d034004041080c1001d042c1e003040b9401d8030307055a902910180d00410f0200031901c042e9109550f507617055006500da0700342c855401040e0440a01c0ba001034010314074040e1840d450750407140010b17484603000c00720081c0031000145000801e0300c440d003000c6647c104000300e1105000c0143c144d81c2c961325040410030650b1542c043c0c40d0104c402800800c030500d48107400038003 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 575222356 1250 575221106 575221111
    0x3020307080102041a0903060c0c030904060f0f0e0f07110a0614010f0b190f0201020c120c0609030c03040b070303060b0d0605120c0d0209070912080c1006050d060c02070b0705010203 80
    0x30004821007005c1e505d0064a800c2d14483c04004003d001c4035a111209414954884964014240420041501903a0b1640301d03102c081c10403080308060107403c0c445410411302d4107402140800c440d410420148103008101203900004511b800c039114041c0c0032031180b0784601d02000600700c500b8200c00180c0101c4140865040341d20f0010b03800240c81e951950315003544a00315118049540016a00c8030050249250071074550080c4001440c02e06110b409608040400c2081c0d4031f0300b00d001500c80c14880d000c01403140c1012005c4042d515001c101e0b02d90a640c0e20031841601d48480001c209038040c0750180d032000c0e0040040c003050564840d81d02c080d0900400181c0910f601c20140044000d101c0c0100080124401c01c0250035030410044a0b001c200440d4001040b1004000e100c0740c02188007903940121b01340052080324041e4481b24115202410304403026040003e0700d242280410165854440f801d07040354103e0000203103407130005170072030509031681c00102039010009420410414154015417 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 575223606 1250 575222356 575222369
    0x160809010f0f08040605040c0b0a080108160e0f0a060e010b03061318110a1205060703050105031b0907090b040807031a060f10030212040311011407080a150302030708010204 76
    0xa01c003002903406403150a1110492800125003600040004503203038000e41c2c22034000d400351404070b40c0d900306604e038541c804040e603030000e00030780010001e1507010042d11980098400e1003a04250400d0041014440010600200c4092030004981d00381c0c0554400006030054241041080d81c541150414a500984459005100e0921040781c42040361082d01030b480b80c1e0b0071000041030407540b00c1402c3c007005200c065600c03021001d000070700e00380356180c44c0640d188034034090070b007a00d090b400140403188168082c0d40603030020b510041004004030507281e1102e400302ca100300b8a03240d0850458111040d80c1000c81400d000040120b0b00f0309002900a0459100310010b83c85010451081d040881741650001d41256400200381c0003858a2202071030700290a1500508050035000248911201550f058021510382c4503002c2d030a0000b8000e00c075801c07800c404040d18509060301e00400c0614014000040c06540b155590445103401005070f00964008003101c0d192601c2c0c80c1801e000354868459403 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 575224856 1250 575223606 575223617
    0xb090928020a0e0f1f0c03030605040f06051503060307210203011532060a1e030209090903120c0c0f0f0601150903081623010902010e01110318010516080901 69
    0xb0701d18548500c100912040000d4100c4030845d54180580f00700c0c0b0078007822400c1c10303210800824a900d031407048112144030804041115841d003414003a004107010f5001300300d008108104440e0351070000300d41c0c040b00c1c1d0444550781210300342c600005051010400095141d402c09084109034100036171722000ba280030320105489050300290011054691001c4182c001c020030244094501d440d034050104294542025211311030615010504402c20304030f0400483d9011410a546003844403d05601024240045160402c091200c0c5e4062800401c59494000300140406c41c42c40f0501442c03130641e095108444a0b1000d0700c0403a0b480d45424000c910200c61296080e45215110320a40011250030181079441d0403a506401884859401c40c295007a20070440e45904031141d081c8172404120b242000000c03014802e100040c00103000614003410010442103901c050b140210488515a00c0b90400300c807007641c80381c0142c84501440c51000105000d51900b08144003100d801400b03549800d0b070302c4 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 575226106 1250 575224856 575224879
    0x3020102011b02060c03060a0b0c031305100e3f010b0301050c030f0c040b2205012a020a031b06020609070b04030b13120c030305010b090928020a0e 65
    0x224034078a20300b10b602000690014000c5074503941084010760700940080c29016005880c7d01803180c065001c0700017051194400541e440c0003103000c20692026040c2100c05001041c04600002e1003482400a070303900c609645007925a4a401510003040050580400c8101241e001080860083d004d48a4081c0da542002e0040c98680380601c1964030803c100e118076401d40e201c02c894100906001400c2c40d1071a5802c100120740d42c1c0040018204201800c20300300c401c0c00072168040798201c010703480300d03060080f11410045a0142c4a81c010141c20b100c081c14184107600d4000507080340300e99030014000c03e104120860150410014500030356644d60200c80c007507191610300c2550303013920381310b00300c0e5001c03062000340002109940120b8010a00c00e5842c10b0305072207501c2d01000990055004000714110440b28802c140d018015240106402c400c0241002030360390101d541031100400041450b040708c1d01c00140d008240342850000364800d84219150400b281000d400070000e1a00e644c800c842e040714 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 575227356 1250 575226106 575226131
    0x801181b09061b081b1006120212060105130e030f030a090b10120f020409020a090e0d02030306060a0f020a0b01121e0c0306110405031218010c0302030913020d0e06010302010201 78
    0x2000583e0360300c044158540528000142d9041c1d107007000c44001c074040c1c106148210b41560090902415543e869080b01c12503610400c51580c491144c1010903800c4480104401c2d551807003008420480c11002050720302c0d800d88a01d003188100b413101604140c01000f88004100303640c0c0010401e520520040000ba22070084098404041b44509803003680c41b0502d4070300040088280000d814806040414517a44d0780e400030341e0400d16904504242640d5003014918101c04100c0f9160000003400614a035050100204000344580f0030318000740068421546c50061082002904154200c0030900072540c50344c2d015010051020f5003906c507601000b082100da031240688000300c0c1a40400107100d1145955030300b4025051f4587d604410241c14480010700c0d80b4140110356201811101c0b1503a00d0a000320388101c1f031445070b030701641001203690003600080d8000003150a0f008080b10300229100d414094400039105020032a801c003405d1100c2904402c1e07002614074181c038800d80092004c4d802148 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 575228606 1250 575227356 575227397
    0x60f081b0915190908034909030e1e21070303051806040e0411130903020724080c0d060b040306090303052d1e011508090105070801181b0906 62
    0x9904200c00f0510311f00708401c0080001d18018080c440c4c0b00110711290540001482c405100c0c13010205662540b410104041d480900c5190042e07003110303d26901075500c2c00d103130805162081c140d805420390b0046039009807043c10f000105452200101c540c400e0f142d00e00288160007940207544040003403e07444d8050701d80b45080d202079403038a561446050b540c40e12818403103901400007a402010418001c1c94402ca5400f4000c100360094008101942c54482c03003a80b80320a0f0400603c907510410a40d038842070380000e84503007013126070812030f482c0c0d440506100c0c001c2030302d6032010840c054001800403c01459400484401d4081e8504020a58402445001510f07145043d40005005440800c00810a2081194000a9488003840350211600100300c0e0b02e0820f800699451000401102d06a5805402d555101c9600e0b03000380103030b042104001d840124180100c01c0805d40b50824a051810980c0c0200802d1800a2040c20007504060000e031644416001d0000010444105042c0045401 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 575229856 1250 575228606 575228617
    0x4080706080f1303090e0705040f05060304080f031b130e060f010912080904022113020d03030c050c010c050406020c030a020f0127030c060f081b091519090803 70
    0x540030303464a42c2d808420701e00c42540110f0803800d1009182010031341c00344040a1034440d140f00d450f4541e9550401c10002c0c2504000d600c140d108040c10000c20000480260a5940c04c444211a8a4036034650310f6100e540d0120764050750000400c0414a4042c0c0002016001c0807504e4500004074692070302d60900404004203c102800314010703c1d0100701c80c441050f98003078020300540c945c60400090b03200040681e030081c20030240400407112544084071204890315081211200704000d942c0040c1c1c042502c4031300221000c0d05055030b49041d0f00800c0c0c020350489200038000d00081200c1c1c0540726020304550031500403040144a0151141e000d42130000d048103c0320340040001d0f61040c031a40046901050700c0402d01c0440d10000011041c1e1408900e091000e5441034203030f1401d1130b052800061030808002080c004200a51040c821a42d0305e02001c1000010a102584c0e0b98a14103404a54480f440c264113900002c00003640d5440b111060fa120050a5207035980c1d000c1041d5035121003540c13401103 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 575231106 1250 575229856 575229871
    0x6050a0504170f0f03090307020102010c020a171b030307091502120f090a030816052802151606051008151303020109020d060b1206071403100e09030408070608 70
    0xb000c0500c2061040d04050106074114507071440c5030003280b13092802260000d54141d84c0c0e6a10101d9404215a020700900080c540c19100401042185440e4400e000003205400d400304880001c0c01d003903d428070a1894040c01501c1c08a03a603900b002100208808414070404d8005014140c159000c144049080f4104101d45101c02e42411300c2c1162090881e40714000d8154000340c22000080000c0d500000742c0040b55844001c61f005401c6418041e00f0181005841c0c010080000700000ca40c40c9070035400310341581c05842c0f15030141318807920806140700e0158211800a07501c08000100242c0380c110a00c85c1782e14102071110f02d6620542035680d42c1c983c1c10740c121400c61010014110921200543e0340c954043d1001040d10440c0381c01050511000c0b5070103880341911452103803c6420300d804568848200280140124602404000d21019450075082c82d4040000b020034403414038058440c024010381000c50580e0300303202d07a4599981d84107120b82000c6008400000510314011541b0a108128 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 575232356 1250 575231106 575231123
    0x216061d0c042315031c02100507050a05030907030204060f06090803030903090d0c05040c050901030c1e1d130618060501080106050309010213140a0b0c030904022d0706050a0504 78
    0x44001c40c903c0301400003070034020046030f0f4194010072079604000080110704240b0504c4c030000301d0340320b000f41440901d4950314185402c010501401c0c80d80b25084808220007031800079143c0d21a43e03a420704044096101a40c01400c05101203415030191140310304803070040c1ca50042c00c5681348a0710741c4902049400c040903030028420141e139414041442000c15100b080341116050701c58000400301c0d11000c0d078210001d0f10214016210356010300c24001741504a09161000c0c000c1c42007042241c210807030302c81080041080d03181421000c00f100040c048071009042c81c001078840345030000105001c0c4102034940c044000c0301ea201ca0298410700301038031070694850a141e0701b0310764244d030107a0015100d450559820001060381403022040d040c050314180390b4901e81e20342e81508100e81c120a80d00700320b0780150100026288030000200711098400d094901585507040ea00c06003482227000c51920498000c124402c540c18822000100f584030310410081240d0345448044408951003110020311215 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 575233606 1250 575232356 575232401
    0x414060609061e0f13051807050a09080118030207120f030804150e010504020f03031206040c050c03030f2202180406020c0d211e0216061d0c04 63
    0xa00000510155500070f100e0310050b980020314181c96849a00303040c9107000003151124a00808014005c002c10080b50400007200c0355405035603030b00304003a2126050010000f500444240038410b9803004009100080005917680000740004040c4018103c2c014060700401045902c40d080584101542284c015010a821541d0580e400d10003c0d0043d220b200c5880701d040d403509110300030341100300d00c080300200e010f00345481030103040703000030300c440d07110381c000748809101102c0d00445550711030f000700c60100d005160321606036240d12a40800c0ca185000000404c40c00e0f20340080010301440c034410003410700680c02200c450b41500144030080d030041040030250b004000301c104454210380100801850300d00c0b0483e409107412005c0c14100d000c034022002c841c002100d03000c0e050940f054281400d000711104c0d141c16814000140014560f000e60115010714441842e0749607a0312203034401c0041002d0003400b01500a0380100780c00e140f40d14400d6814440300c1c1c1c245801240380c201a16440c140050 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 575234856 1250 575233606 575233609
    0x31b051f0516210906021e0313031b060213150e221d1b030d08070c030201020708040605030411100e04020903101409060a0605060301180e12090414060609 68
    0x60750301c040325076600f900c00195585998540300d0880d8079441040c2c0140c1d2118030140c1000f950000500001e1103480a2013045580326100803d0744d611039151030609405c07185500500718045c523442c8040d0865101180c188000350f6068108019038940b80031203507200d0694141100e400004d00d954a40000e40341d0b241c81c60340381c0391112210300403030000b001040701800c401021111300031601e01d031072081c0c0c0590050400180b20441325820b00c1010b402400054019600240643c0b1029200c1d100700500b081036102414400e5065841c4103030711907929035a80ba610340380280160410b4070140c40105020310800064070742280c1072002c04061f525103004012000b010400250000d03448130f40c041c0160748903441d019406218038031000ca610880d1a849090000b101c2e49007c8008180804241c5000c00c03c0c4603d50f0784034240c1c1d0440d9101c00001000c5110032558501802aa8810007214031906e1510662900620060103d0940645040084c030900030b0904070801001d88086800010402008007103 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 575236106 1250 575234856 575234867
    0x3080403080a1209051605040b0d1103030c030703030b010f020102130509180102040f0603051b0f030a0b120f061515090103020c031309050a06180504031b051f0516 72
    0x920010341000c00f80a114141007034143c4e40c0205007280d45800000c5101ba0706614007508001629041e2410003486c28003001080c07041400c1040500b40c210b61256540c0b1503501041100c6015102c03005480d100e0426180c0540641001c120203800300310070300d154040d254414403d450710303c5100c40610400d1072400090107140302c0c0c0580100300718004031001c1140340000740003c000808004400d076256520780600101260300c0941191880c1c00d5084180044044200558404d84420850705581e43c51300d4014800030030306040e041d5004500301e40051145580030507180704014508003940c5140c0c2c0d40355811650012a407100a078410741040b03e990021100d013010f4111142c040c1001480d10000c1480a803841d041032280e5034251014510500c90007034140111604542240c006100e59403c0c184d0102184070301011a0084e55036910024040c18441c1201d0f05199020a01d010242207042c01c1050b101e400900000041e84421000c40b0301c1c0c5d4219204041c4508040840308200c18070004080b200c = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 575237356 1250 575236106 575236117
    0xb010609060c320106031419051b0a050a0b090310020a090618080f03041403010b01050f1615020d1a030303060607050f061006261807150c02090f010308040308 70
    0x46611000542030f0150403d11810000c1c0d80610414800311078000b41481c03829040034410000e805130041c28400107880000d022591034082c5109028601c00341021601c00074080d40070650014640000117590400c0e04018a803411098080e11010302c58043c01c0742c107900c191b000c02400640f1150341000401e1241100d420b140e240c9140c910701040c2d4074941c5516048040c641ca0710030380c100040805c191034010845c501169020340003403244150110002c0c0c82c41c0100d044400d140031002582d2008081f1842c1c2603903540350b0182000c035070f03c40c0d0261044000d411070b15207142c030f081ca001e01c85001410350b40c7d2101e4040c2d4005009620f035a44441c1405403540115600b260140303d60000c18003000340038040d84d841502c0c0014045083d618140c03000b001c3d00031020f003121280075001c1408500000e020905507001d80c595040c003206040c007244451400709640c1c801c0040d0402c9002c01a0015400183c004845000301d07408035181d201d011140103150803c0c800200410720401040000a880c0c002400 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 575238606 1250 575237356 575237423
    0xf040902100509060903010e0105061201050408090103020702060c06040503030711061306150e040b0a11090f040e1011071b060509010c0309030506091c0306060c0f02030106120b010609060c 83
    0x5d0501041d00d004c070307003510a413103500100f07a51200208081c03418060414100003213000f00038002818107445500640c824580d01604140d00090f10405649646040302ca48410150442c0c081d4901420710035266041900c40000064180078a031459150000b45c45004c3c030b801c1e0020501c042007e9403040010000d1280342c003c0c0940c0344100048403014030b030000703110f00c1c0986041074070b510341903c000c8211041e10304d0707044490606000300491611140c282c40d12018058800142915240c80c107680b81100d142c841d816440e0608200707074032014a02d0060640c00c0d1140e40031080f0740032400e0302038000440318040c10002940601618540350b10071500095100e0003803c0442c0c8142d20703510394a00b09a070840b1580c034141c2c041480c2c0100182d008503540306081031850304009160501c00001c0a10b00c0350356000d05250083c11981c0c00b55a42980200002c003d03140076200c0030103003883c043c51510700910842022551140703001441d54040c0011940040e8440e46d901000e04921041010104c860010350 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 575239856 1250 575238606 575238619
    0xe0714040b09150117010806070c0212010606020a020a15050319090f050f1e03090402070c0b0412120306062001110a03060906050d0f0305031f0902090f040902100509 73
    0x450079125000c03400e019414440e00fa401000070480003528424010005036034509113540104400d03200400c42c030760003a01c249801d440b0f075881800080c0d0408101003d0342c01952a102000030026000a8001d00341d41c403d94628031060b41d1002d014094280244500340440e10410015000c100c0740e0000603403000544000041440c51625040800c482c2800c040b0750a03404618181c1d03842408001c2d00026030203552402d544600701c031590940700e01614490398011070f000300d16041008010038600703016101c110407480d01c4560725650b11510303682042c400e885099495446200301c900c01d0107000250303501c64030794000300010780c0b00050b61f01c5d803448a54280c6540c0d51005c134002c0620003009080c2d0460b02e980108000e41812990400c4480c00d502c21442a4980000355001810455103880701581504100392a5a584031074118805014505025214205040400d5510056000e040714100070b913000802030700b1b4001404201c489491001c0c0d48121000c010395007a600c070704002d0444181c0900700b0f = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 575241106 1250 575239856 575239871
    0x5192303070f0b010509150a06120b03010e03070309140102071401051204080c070f031703040507030803011d0c0c10051e3909010c020609030625030e071404 69
    0x542030351940c108001c40c3c01c008040010411807406145254020b280c0301c00354100c407540b1600241c000001441100c0602c1542e0b12140104466a0701036501c00300040c0c003e000503038600b0a12500c9a21200084010074640c40b0042034140c081200c05071109070607001450043d00340420b800403140010031040c10001c042040d0340501c410481c40c00c4c0902d106401854403802c140310980d007041003a40041954080e408010000b040f40d403035011010b80c04084000f507a0b0b442c1c50800da420044e903a00b01800c146c5c0d0000c0001441d4081c5401d00c21102e50051413071b641501c0d042c007480ca40784103000300781103035501c80c01c080303c1060410342c01503810040500ca405000c0d0300c804008040c1400454400003458205c2000c4110035080b819a80d03400c3d034245224041072210144040d819000311204541040411080c0301c04544550003164038406e0001c0807500d15143c001c0b51030009095056413144407038211034846c101e26002e409100c8055240b800039202d02410451948401d01c903880000f82e000f0f84600306c = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 575242356 1250 575241106 575241113
    0x108070e040213021b0f03070c0306091707050c0a06030c051b0c031002071502040e1b071707060b010203040518251107060e13020a14040906030519230307 68
    0x606605e9602c00040082c0c04042207000c3c10010040c0010394150800c1001c070340040c4416440300180c07a88488009004c2800d81040200844080200384201000090000900c0800140c403458100c003101e08038209511544110262008220800b0100d00f00740301958a07091855104a400f41c0c071942240c4401018000081c542a01d400d010060039900041c09018080c50040709007600c075040d0002c0d41760030314100014039040760051030741541c3c4003648075405808034100108e811079900003021b40d80217103a141403030010750b00c28101203891900e44070102c0c100d540040183e40c02c0360001030440200c003401600d60502403000401c8400f10302141c0344800003d03010aa880c6807207201c6a524501c00f05140700480b894450290006000e00152000c001c40c25034690f0949a10308040e0a00580c0f968211203060b0b81450704540c40c21030361170022801250300c4805600c06812207002c2c070f0031100c00c010584008001c00001150140a50615002c0211050003141c50643d00154840c01c0320f162186584 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 575243606 1250 575242356 575242361
    0x60c02220c05131a1b070305100e0f06010b0a030b0a05150703020d020f0d030b010e12010507020106050613051c0f0804090506030d0c150213080a17030108070e040213 73
    0x51041c00820000303c1d006500c4542c44410502400c8000001514110400e61810580c0901c490007006203400310b801d2400e004c0306010601c02503a22004841c101520000000c02a000d00d081d00196485032032810030341c1000011340681251090300b802803500b144c1442c01c0300603200c003855aa41140042c0000070302500c60030244003040002503002c035240d52152400070709083d0304c0483c1303004552207070880c0c0034440c0700444c04022911480c24001071203118100140c80480300c0341e00c038a038041400c2070640e132408810341025210b12040c0c0d000b044102d032180d0800c001030166050083c445038065105204505280c20000c124241240b15034042c81b8040c0c4e20401e80030780074001214000004901042242d400303000d0140c01400450242c407003412051002003401172000809880c0d200c82c4511100050f44aa04961502e0076662060307045036192408141d03030702c5100808403560410b01e070b05543c0082d24001503d0580d0340b4072014101d003501c1c0654219880300e000d070059900401209107210030702d6452 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 575244856 1250 575243606 575243621
    0x1c0f02040218060d090204051806070c11040f0b040f021608070204060e0406020c1b0105030a1526070605040b0f0703020c09040b0402012d030e0106090207051006050406060c0222 78
    0x2141301042c1c040315403040c00b00395003000c1c1c801040c8114001f00c01c03880c1880850030661000151900c00f48810140c01c00301490500f0402c0a900b003440c11216031040c4049801c4030040b030605980501ca13400b0512408405c030f12901050058501030b0a100d07c0026041100174028140010030100d0895100c000c12000d8000c103440072250f4960006201ca00c90200307000564500b9229140342005156003c0081e009100c02090328108985e01c1c001d8a0174903012101160142551100180b4200d01d070520740684c0d0710441843d481c0510440000054032441002201c0070703684114486400c1181c1e02134140d00e2908071807021810360052048942103501c5070803120344500d0040140c1c546c0d83c1080e0002615098840701031200d40c0c0207010031101e0140c1d288010200214585c0740c00104442e4002e0007500612698001d0780c0014000120725050200000340100c90110440d01000b106a650301040101c540c14800d800100700ea9810200c09850301e4002c00c640844c0c602c560550412840740c085049424a = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 575246106 1250 575244856 575244877
    0x20d0e1504060c020d0c030c051f0f110901052d0f030601080702010903082806030507080d0504030308070813021801151b080f0f030a05061c0f0204021806 68
    0x90310800051040038003800c1e100c1030031070018040b03408992070010050f03491080c01405000c03401c007004003004020845041041c0e410b08001c0d00302e400441c2030001070300c3c1c18887e2005480c24085400b011002c0070b8200c64030803c0503100c0d28a002880441c142d80445a51401d60a440036840721141c3d0030f102034010986052400000e503660316090002505c0c3c1c100280440c0c0c110380c5014079131000660030000e03194020142040c90511000703e420417120070113468840881031400c0007800800c01070005125410b0f00c1114003605e40c580d182110407500c038000e0b0b11002d000145900f0110711060301582d0f10640220141c41c440b040e2405603000701e154807420128502050100f1401001055924103c046905010380f5025203480954180e165038181001c4008e82032010006644912081c034030115402d94040701d0b8810703100d140a00040307000300811203402d0b004403440004900e0310107801d00708054841c0e10080d41640550607400b0b0100a41140005135100061f610110702c05640e000c015206200c02c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 575247356 1250 575246106 575246143
    0xc1416170706020901090b070b0c090406051504030506010e0f070f03020906071203050a02040b0403020f1207030501150e250323041a06090a0f02120103080307020607021204030204020d0e 82
    0x611301c0010050083c5900000c0860028005040006c42d00484290412400110551a07040d0080000e00501c0142c1c0810341c091111400703c401e00c0350403000381084a004070250f40c000c2c3e0341c80d1a40e07038100200b1aa101080098040007030f9900703000d603140c0d4000e02803d190040c10042c8040104080744d004040684110700602108000c0c030303030b16010b03403980300b840d96606504191409a51000c41c0c0182e000080c8280c01d10210501e6a80351203024224500b0640200c6c1e481558a04100c0c0c02428a08248110f80015820100e01d00000110084c003440104aa40e50005038000c0981222010700800c20201034a8122034142548114403042c13407120f040000242d6420140780c0a009c40d41c540e1291191240282c0c10000240d9464241a50105540d040454031403009400c0c0002481948200da5003d043d201c0080240030049015502c100103035002c48030a84c8580000fa40d80b51014110011075510811003800181001d402810901807450000b00b415042160482d04121403005401c0e486074 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 575248606 1250 575247356 575247367
    0x303310b0715110906090609040612060513022b0b1609080a0209130c03020a03061b030902030c1507060c05071b0303020d08181b01030c141617070602 66
    0x4100b820652403280c2448104a04068507000e40114000c4400c461312a810110b0000780c5621100c04564102d8030042c001c00c0041d894210b805032000c40790006850355403a1000141720403030840600c40003990010044448440d844c244890307910203013a10300103606481882c01c0c3c00248000e1916004003048000740c0109030300c580340180100700c15401402d45903c08200f010268540e03401840e00b04e16030318206001404103050410310302a032507000035002041448000140b1170641d2056102003040e42c1c071924040306a010072002e454090001075410b400c644c0315050036182c5601c0da0418891280b00306410014241c8401c000c0382d54161041c40420f10014189082010103405070482c103518408030b500303140c01d40d20000e6540c20700300c0c41407080c4650f246c08200150f03104a441e66408d501d120480d4140700800c10031182e140144040302c0c3c042414031107080d54403401000300c10300c58880d02c101c01e03040403000600b19904011010050f90b0356110764407180301c14004c0200410180c0c2c050712000d0f0341c60 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 575249856 1250 575248606 575248613
    0x140a110a0c1a210c0f0a02070311061809090a020a0312090e070e060904090501020a0c0b01090207030813140f07081c02033a06080c01030207020303310b07 68
    0x2051110022080c2d20800c40e55507050701100300d41070605140c10588250f6581d10159804520561415145030b210200c2e10807901c40c0e0000c1c640c03041d6403148510003100741078101407004078000c40310284013502d00400301091904010f4882a0321030700705011503000d50074980115024102980068549215210141a0050304106418001c040405c0c0d44400b85c505410000c01c49014202194843c0b100082c0c0d040300d0365520f030000180c19400c0b0000310341c5c800024501608829031600c0c1240d40341d11a400010f408460740c82501c0310940c050b1071b044441d80e10203042c46110302002208449400342000000c1010310108491460443c01c0001420303c2c070300f0101280c1c0b4090320800000000d8501088201e001035010054440d00e1040500c01845400d141000f151800252808a107130480e005c0c03248503c256890304554111110b00342901c0400d82d00400440a902c10104041c1d010340c020004001143e02a126291080011071405c2c001c403140141a15400c50441d4007036269420046004802d1 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 575251106 1250 575249856 575249879
    0xa20030103200603041101050904020c1509011802190e010b031b070309051c060e0a03030b0303030c0406050304050c0a090e010e0601080706050f0f0a0306061e140a110a0c 75
    0x140c140700b00c0000003204440010798144002000204240603460031004c03264000c0050790b00002d8024410764a8015032407002d0303541c0b8003c28085c03141d4424500810301c6100c0610810000030a035106400d074a03d40c0d9000d1003102002007007084080c1803921000138039040710f25182d034003800144000f00e41d6800d00b002c0c10400038542550140322144100080c3c0c3c0001d030864800c408840c000d032516086076000314481c91010500200180a040c1030840642d03035030f42c010551a5084d031003a1000c02c0f041d02818103040d904c0c003084032040c01401c010002845010b000308040e65001c3d01c244200d880403000310020500d40702181c1d000803010754031548201d181100c01c0c0201807913070360402d004020030740c94203010356520380b40c0c0d100f0b040c103002d4005040141c2c4c0d618502210070500c4040307030301d0342d45542d400b500030f005240342d109001c000b464200c207169156018051814605030140c0d00c00b10080b007003408162031940803040da8001c1c48220401c0080c901028811031345d17268000c100f010641c4e8a4280101207 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 575252356 1250 575251106 575251133
    0xd0506041704050907030f09060509010b03070e0f07080402030f0d0c200a0504020c03090301060311010809070b0304030f030b0d06050a0b01050705100c030603020303041707051203120a20030103 85
    0x181c46105000070310207a00d034184141d5020310303185004a803056819000d20000c1246140140425040c801040381001d0150818100380f001601201c8410b40d80340b8405071501401d0f01c0c3c1890b5218210040341da103e109030126504030f80014255242c00006400c40c0345005a42c0d48110003107041121810b091000c00e690112003038a080c641d43c6c111802c048001110b545080c09240d206a9020400020700003042055411008015008122958880c200b4a841c01400840140010541e40005484040c003044510480300072841850454480765001e076008020b8065510070180d60348102c2419903541c502000c14240280000100b81c10712140c41403d40b4008540d443c18042c040101d00d00040d400651840219040c42d400580c542140008074041c0c0090380c0701079414880441c022400c10200e5130304104107a140c1c3c0407078982c56034640c103100401240048405082d00103002502c05c0c03184003440e141e401614010001201ea10004105003815a4a840c005510340e0100c014010044044e203180c9 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 575253606 1250 575252356 575252393
    0x30908031909060f020a0f060b0d060605030d110a0b0a330b09130e1014070e030111040501181a070b010e0c1e09130516090b030a1503020d050604 64
    0x403013081e10710b58065a40e0080ea83c0c01010192890703524000d200159102e809080b400070042035068200e03040c418050006409a80d00c43c2c010561111819070007054110810344031203010f092100703060b44441c246104010007103514207403110300d54000c0130646a18071030540303100007501a1048900f04440110754481e049506140005c126581c0241c0d02c0140d0000445d09154001c42e08401722a800f0342010001c0c3d200d007280c00c5c18582000152440c103400e89214800a070760310302040c1d10b00c0007010700381c46102e09800c2007100c04000a01a5510034140b01c03040144041ca4407221740c0e0707103101420140c16500c0e01317018003100c04105e50080200b104003075401813241e80389a801034240000081c0ca02d02c14446840d41000040501c3c4040d0003e0780c3c00e40c1c0703032440c000341680c6441e0704040450b0042c100840310102013054100b40720038203d018506190540e89603040503425640c811102c2d00c0280410040080d9100c031049001005030794104c0d003c03103030b54428009811a0706140c030b000091121040d0301e81 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 575254856 1250 575253606 575253617
    0x90315060f0b0d02071e02121b010e21210f041e09060b250f03030c14030a0219020f0a0305134403030f0403090803190906 54
    0xc00c500d8001c1c0481c4410394503108045540d510020085800a100d95900100104045a0000c00721084d00401361070250086e50388000c1310039140190342d120030b000b01882102d0000440e1303c0f001e40d4414080031031400c201501c0207031041c64080303030f490102d24506100241ccd640048400d0101c0c4a2202c2c6441403814681d00103414201440b1114410740a40d0240c85080722610320300180c0b403c1e4801172a0010503030000200505920398038903160740c2d4002007945041d00031504210f01840411a080d5180607046a83c02c100c4e104156401c401501c041e612040400855005c500d1105091100460091008075030050b84d5420761204008000100707447c5d01d00f55000b110030040048000f01c2c0790400c459141c500140c1c1e580586a11700031101583c0c02c000d92800380d11202c04840c811100141a07454103d1404100300143c6a0034007404a403c4022039000782c0091010440d201090581160400d20a0400798502619108004c0c61070700000c1d0341e50144080c1c56006e41c84241c2100112002d0000e62030030b03 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 575256106 1250 575254856 575254859
    0x5040f110d020a030b0901091506030c0b0a050711360a0b090109091a041a0f0601120504050c030d081b04030c0605090d05030409090b100302030c1507060c09031506 72
    0x1e8189103c500c40544445803400c00124401800c3d4170030301c02c00c0e5010704406182e441110b039010040c82c190004076440c04003503a0100720700140405490500300c0540d0785a1070100240c0c0d5000c8400d02d408601504684106896000d0301c1440d4a81d000600c1c030760781586042510851500382c1100003601c2c1402e003503d01180a5034035155044507506456036002c02064070700e00c030b01d01341d502000d25401e0311040c50000300501040005191081e18440c80000e045805501c0f40907140c0504881038550501180c0015200040352040e03270401c1c1e80c490302480030340f0403402400c80441d00307000d0030006400002d03900000304801f80305001891900245000c6200341401d041d90b59004a4000c0c0d80a010288840031404052036075420b071a51021507405000c0d01d03101c0e03075111070000c05020403980c00c46540403141d001a2010034016042d2040b2a002002801c107003200c9414050691112560300c03101000030422000464090b0249600300c210a9440c074000a1a506000f01c0700d100001c07032a06040d042100 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 575257356 1250 575256106 575256109
    0x6170105121509070e07080703140609150105190302070c08010501081b120d022d19020d0c0803040302041a09070e01200102030702010506010203120c09060d05040f110d02 75
    0x500700b4000c014020702c151103454401c0309500d02041e0703611019694900070200003000307a020540902810709910144049901444800c051000c2124415003002099000840c9d00c034044400440c001c0060416a10700201807018600c940c003c0810440800d400217803400800c60502071003801003001800030800c030750601140e140c4032a0004513180c048010f5041d00740c2c0075a1550508840c12400108464200045070320181d03c078003584640d842910901480352588004150034a00c0c02c00c0103002407c404010040301185071000024240d030032026080e4a00c001900402c1d5000203880c083c402152a1440c40c4108001c1e5031040c03500d480000d44d43d01861825450740c40b6081c0e080503490400e040307807042080048410b41c85e40002c207640c171030a40000c102250030660045000b50410f13402030080c1d0ba40d1030300590f40d0303100d101050a0a20310344000150718041035006090308420013000c07e484c0606a40041c001e441c0140d0b0300b60780c4c4c809082c0c0180100079002c510701c5840030066030142ca2000700f82c2c0 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 575258606 1250 575257356 575257363
    0xc060f021011040b0a030507020d02010b060d020310120503070605130819030b0301020f04030c0503030301080d030b0112020d020d060f0b160f0503130e010b0403080409090507050a0617010512 84
    0x40700d55000ea140c000010400c0288800e0394058061110401c0e281c020085004000c0c04080d1802c002600803022610807141c418000e420785d056002c2c1403240350202c80c01c180402548010f040c071621540c2c1030400300b40c0c00c00704c1d0140e80009006d01c00840e140e03040c5051103411210301414062202401d880c400300041c160300244d039410b1070f0381d004000c1000c90529069001e00001c81e0020345c0765200260a003283e8402a001d0b1003a40d01445218103090703154018156248402e02a1100725800700400710640c0d03110790405012004180751040030001403080314020b980041740d0404145801003804114801c1d248510401030240c074407154000c51820742064114070595510815032018540502c0c14800303a03e1039180440c1d0f12001716643e40352078000c1a0940c410300d00486420380c8034440000744c4031a0030019601500d4112100e2807425180041c004c00034040b03094100e5580c065280c0002d8070340c1c1c45000090003401c4540740c0d03844901c00d401850f01407003816004644607045400e00f00b00e00b0035001 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 575259856 1250 575258606 575258623
    0x7110d090501031d010c120e06091f0b09040609141b040c2703020a0e0c09010f020a02130e0c1c0204110706020301180509010c080402190807120c060f02 67
    0xc0c00c00080b595070301c400264480000801c041c03c60340c00d0650601445038800031207a4084a4164200001c0400284850b1522000c1c0c5107441a03a101d440e103403203000010340c407501405483e82f40000310092480041382265a048805507641a950400d44040c03002e00f07540040e020b489032014006454404a01c0c0308a0185084c0c1c2030300a5a894100300400c3d8025481c0140703140c2c0340c13a102c1c000d0745024115041d400c400360001324016591365000280c01100341c18101c1c040e2400545040c1461245070044440040d103021034402c40c443c102d940c0c0e000d03131691075440140c0c02c0b11038000318851a60100b00740c80c0c1404145e2050050555450b411b07000c54076100c13190021641111f01140c4500c80d148002070324061424041d11540c400070000800e40e1b401d201081c213240000030103010aa40d009600d80c01c03030711a030b408040450a00307400200180740501d40385043d03002079005d0400e06521514014a881060382004143c003100303100d500240034401115000401d2580303040c2100d004902402519901035 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 575261106 1250 575259856 575259859
    0xf0402010e12121e180a050a0e0a0c0912031d1804060203060402040f091b090b0a211d06130c06080a0b0d050102090114090f120c030106030b07110d0905 67
    0x309001241c4030703200c1c0c1000c41c122021440d003503d034100c207000e5003170b50041d044c0d40ca446090380300c80005540c10702a002c402200d107030a503102d001c0d640c2d00600d403000d044800c4862003004518500840c3e0a10854184001c65010303039545110500500d522903000314150481e00d10031082100300310321407601549076960096000c000940c072522600c0110b0080d00031600303c81100a4800d1003c9010399031903010280082c1c0300036041e0642c0302100026503c140c034034010382003030140c1040085200e5002c2c41814626055041c4006500703002c0742030520895441c010074084454494244404130f007801c2245075040412104000241e10769607a070082504420b1050a050100500004900320002d60004c203c1d1035000d4800b106031700213458514000c0d03000301c01c035501041c820740c10845141c0004050350100c40c805051060b45001200030848500f00c04411854640310700302040640352030038040c3c90015442110342c01510300705200081c0c1190181e4021171a143d00200240f80d2860f0700c5441081250340 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 575262356 1250 575261106 575261143
    0xe06150d142409010606080106140304020d02060c070501020c06030f070810090914161505071707050a120c030206060609060d0e0303090111130302040b0d06050f0402010e12 76
    0x848a00950401401608168190b851030000c035904145140381144100c614400810210b5111030007500c58003800c0c0a8100021480c0310000005240c2c03030000c5070000c1c0001c0050700030340c41c3c1d41d0004113181c2c000b1401c8d000942112030100043c0d40c041011001c07408040304c000e411840d0580c58050034890042040081080c0f40c404074030200c0e00441640050300008200f4820b4100714100f10604007607850710100c80388550308800440c8040311980350b0075100091008003146142100446040c1c00203c425102d108440340da008225040700c1c0101001440744000e800d00500c141003071840c03168100074443c00d0201d1085032600103903000c582e003548543d08603600c80d1562290b00c0030848a0041c20902900c4a00d0f14940042aa00000155100d000700e60024061126210b044140e036014030300800840e80c2c80b5480900041c07a10713812a01d0301c0c3c60054144040071580f5250340301902c3c019502a8240440b034000d000c29542d004c190500031200603103264020034107088003e0745e5041d000c0c00d210030110 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 575263606 1250 575262356 575262383
    0xf0605061c0902010c08070309050a12151a1807030b0105030108101107060f0b0a06230f22031e030203090f04060504091103070905090706120f0501090e06150d 70
    0xa00905d0450885034101c8060b940307035252841c0141480d4454060f00e80324078480000000c02581115a01c11200da1110907000c48503e60781d50304c0007900805031521203040103000c9076040c40d2124154491820024a004c0ea51802d2465016046482c004540c50400500300010311000780002100e1800340300552002420300c000c00c5060015004185006240906200052918a0054003c0980c400c81210a080a2aa1410180d44030342144c2d000003400d1100000c3c0740000da500c04c002c0c00c0103500c0508803038a020b00064078103154a080c07a0b030103881514420300c00d1051100c40c0700005c40d1501d0500040050030581c0e100695a4040e41404c188a0042580d40c0c01da543c41e950404401400c0203003061001c48020718021400c0c0c01120200b500078424140000780000c3d00d401041e00908001024000483c00c1ca10111104103a03162180b03121a15114400341d0546a1700c03c0500034000708100150007494036481c6400c0a10280400316503507052003e5803860b0341c075040104c4440b58442802c2205a = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 575264856 1250 575263606 575263609
    0xa082a1e1605010b0a080105060f040504020a03020a270216080307030914010c08311b2709020a09020c07051008220506060d1a07030f0605061c0902 65
    0x52040488030344010864626181c1008015003003444810f004a913403803510780d100d02045080380e40484905502a181e41100312460070594001c0c1c0c0c200340042c2416481d031b0380700d8000c01d802c10a2a4811809a01508019904c2c0c10410880c3c445082c0b50341025450807680b0b000c007a003540401c00300a0040440000802d8100303009501c04ca0304282d01c1401081c3c0c40401240c828024080903d444020404d41d4002628000c01e503441c0902080c0e035900608448640e00320321070b12440c22024101c0d90130005030300071a2001d80e44d01c40e0000822401e02060104080c0e024580304446000082804587c20072a03140e0041e6601c8030b012040d500d05600050b152480041c000745456600d52020303400600610001403078a07801109540324070103140d14602d00030700c90102140700784041d0318050215007100f80411901c0c079007054203000c5180201c110301c400c601ca0014064508034151103c002107a41e0380c0440322640d44900401000303080c200ca0040c1440754280180110f9441d88c0744205c442595140f441046 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 575266106 1250 575264856 575264917
    0x31321050d1b2406140a2105010906150506070c090b062b0b0604060816110d080709090b13090309031a01030614090d110f030a082a 58
    0xc54020b200701e8880c80003400d00580000c0f82480b414146401d20301c010900a8031212120360711000039064141e20b9250070001042031a41c3c00c80250702c0d0801020304004240c09004c0c3c2450240600c2c000111508018100ca01100c42a03000d0740c020780342401100045000d030700b4400c046138488007003c110725400380d00140c201c1c4506041c05158400c2030140615500d03d00d180802c811010302820001200c82d0820071000d40100c1c480c51000503060000921901c0000c103105502c14014184008411803910b640d90400348204420000144000c0800881c0350380304150f00d0080030180400c00c40ba1100d00041207020600301d240344015629280420304040c80348010200440d0061081e0b12090f0b5041c0141d41c040d0801c2c407080e02c02504051104801c51031400c0024019500c110003861010704e500d200f43c0d800703122941030482600900d8018049030105200926003504070f956054000d1405c401c2500182c40e480882000c2e000310b443e034038000090a0030456611044000c4064240300030f14909141 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 575267356 1250 575266106 575266157
    0xf040c0e0a080709052208070206071a07030b0913170d15031202060c090d050c0901141f020706111f0b0f0315150a0305031321050d 58
    0xc01c2910108001241e9002042e00760585156182c240300544a038180317070000b2048001c260780c041d140d40080c4c100144140d401825041d00c00303001a030900b00b280e1503281014458012651039641c80d10100b100c196418480c900b2008412140c0e50005d06100900700c1d01070540101c000c1007918140c04950080c42c1200a40700042107086090100703014194054140289074401258965040c8003440201d074000b082c00c40c41b1300301c070064040c1007040c524200001400003c0c02501c450007190422086070b1035500c00903000e400c814444007c0b0600c4a02031009000760303142428886400e005500c040e213940491500116182c40c07500401d946c010400c8a030400380032a940380134141181e032821003840c500340c2149407003110171120710003802c61400601d42c07100c50501003a0106480d5a0005038440c66400803d007080a02416148000d130706da07956a4950303070003c0140c20300e0601c0960100180340c0c8040e540760100300036034141c8040d01003946d14503507608412800c0c1070901101400c642c003114240c844540 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 575268606 1250 575267356 575267359
    0x9051308030c07060f020c071503020304030e0405040303330f0b0a080702151e0f160513030c0905040b09120334031506020a0f0204200301090f0506010e0f040c0e 71
    0x660764810b07e18410b07910901c41c0304001450344000809002e4174080d200380c0e442a0340648482180b10a00c81c1004002d02006000710180760743c901a650005134003545c840020320880c0c00381086140d40440d840340da9982c0381c0c8041c1c4000300c840c005210340c507049000e588900c5114185441941c4950301c059003071071103172a51409a07450240801040204801c1c3c2441446901d905d20b0900c3d4a600c9080840725400715403844030180091500030702548960002c155001403844045150340e100c0d80e41c441000801d50111072025241c00c18003052150b1681e541341c0000100005040e01d140c24804024540401480781030100c0c0d40841548101c589000008030200301e03507810341440724402c40c0140091a640c104580b064001d240301044050000a0b080340c2d1680102030304001010726400c000150140c10042c405011104c6042c11802008030003541c080c000c0701c1c1020400003e414100401c07954004c03d590304003d8414080942900c4502c014901418103940c00310700c44c50418001e44e0314410b60081c09 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 575269856 1250 575268606 575268611
    0x30b090705040510110a0f020402040f0611151e0402210d0207050406081504141204091404170a230a170108030a050d0e03040902030109051308030c07060f 68
    0x880034075071000042c41601d00460300003e0000c10700104403005074a42969096a5014840c01c0380440c11414080e490a0b02c0104050300d019142d40780c001e09260554400404100310041485002406001d1085001468852414985007070f01d5144144860280c4080f5140180e101007015034540e44007212030b03281d649040441d440711401540d591843d4910464005001e022000300d2203140034012070f0126503202d0f004020610100301c2c2203c0a42007d130049404002030103040020700d00500450410900c81c0300c0b02901c1e00d00c1c2281d07035070a49030745040d01e007002e403131132400c110019802c0b03e6005404082d22414603107071401c010017038455159880b55495004051019084122403001c028080035210741c1c3c500450041c005641041948280520ba1450b0400e0003107064a42c81500a41500800a00041003140d4440d100c0d42c1503034004d8100922481c2c0020051251554500460350840c0704040d4081c1140c045855240007400081e0004e8043c5200145602c00d00109810003400d81d00c904c4800c = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 575271106 1250 575269856 575269861
    0x5030901110708011b1d10030e0307060e030702011116140d020a0f17030717090d0b0426090a03020915120f0c03030f030121150b01020708010c020c0d03030b09 70
    0x818200c108040301c0000007813046401b050152200f030840c0403100c90045e0500c00302a48400d0141d014001c00f410000d00c6100500a100220300d1038011a52075582007400740d662810540001441d0707041c10302084a0310307844244002103444024100a0403101c606552040c88545100000d00390350603010040c1d40124000c00120709407410f8440d40301119000f02554410040803041c8a07124002c110380a000e5070f0038503281150b0103800400905401e04010300b079400c404050b81d59100c00200944080d500080d48803c9504400daa14800301003002d12540302d14140b42100e40044c0c0007050703900000380a420204041520b02c0c2c19000185152400217040690170511083c401b551b0b580d0065120050f0f204034260b2403424200802201e20310400780803000d1442c2c1c2040008030082e10b05c601d02441940e07000310f009c00418116030313018940600240003c502540743c007000900e8640306401204459142100b110201038000401e0029a48180c03014070034400903040c15002000041c0e805a00300111a04 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 575272356 1250 575271106 575271131
    0x5070e271003201503190e160909050f0f030a0f030b0907120609110c1b0603010b2805090f0f0d23030a080a0f0b060307110a05101a0d0503090111070801 67
    0x202802c80140c09202084041d47c0b8200c110f969403107850301602030980c0000d051040d0411130b008007240b28058411580c4644c40c1920081c07500101c80b03000920b68001040f1840d51543c41025400c2d01c0c00f480c0b0703090040b41801000901c0c800b402801d0442800441c4400d2030300c51010390054002050001410401004d490040c02031a60001401c074441e0b0082d18894107031035102c0d542c40e95403a08090242c034107603030034007007040303096440389849007440110090402c54501002d01032090b030489aa60345030f19003485200340100c00040c159418801c00e84908013051a480d9416040c501e240c004260007412807405010001454590600d80107a000024185010f1034010020078056186800c0802203001c0f00701481c4c00300d45010f81c4040d0f04c6007040001c41e0490b0311491003d02c6500d004c00079111081150f690740b5143c80007a05041400d10f40f2070340824200c04405410590f40501a10b101101103240e5441585900c00e6020f80c0d414040c1c2400d411105050402040f8041c040b240c000704524080d0a0 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 575273606 1250 575272356 575272381
    0x11040b040920031c020304051e03071410030b130207140312220201090e06032b0e1e0d031205270d0f0305070e271003201503 55
    0x12500074464604803504ea50768030b007503890308140d82e50b010314141820a420050090300c0349000340d400000488402e00c0c65070b410721400c801460141c140d2040c00d00c030942030040a40b0380344000d40034545010440e8885403140001200c40408040d0016030740e000320315050315030361591075a07900184804201400303070340004407501c0d010713008101e020080140280006c040c65a00c030072000703000520304542004002d014017510303500042d000741a20f10200d660a045c0a540ea042e20804442c100c030303000d000401c1c2d608182d0443c0300100688400d03120040303201d10119a00289114240150114548142030610605c01c403c101c030300c0154140141d050070801621095003201107200c1000e2400c0f0f0044040400159800c11115035446804160540010642c000d0074020040030a02001192034051551640c0302460107216404041d00903400e00d50802004090041075007010320780f00901031011440e002c3c01881c802034011000343c10700d0b181c100403540c40454030388400c03070495000c020b06c1800072541 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 575274856 1250 575273606 575273663
    0x330112060b03060412051b060a060f0605041212050c0a050a021503010501121d03040914220b0613090f1403040b0a0302070f02060c15100311040b0409 66
    0x5803424001d01580c81c1c101a2124400c0d100245240351441d0144916070055014110500315540d07921551040c00d00d0290600390708407013040c030b800d076075040622071410403184020141240703140450803d80cd0520300c044000c01c40030701901c1035032000340000d03050744108200e8195855180981c2c80c02c003424a00640d6074a8080c500300d104000708020081c101c0c0b0706a050b41c1c102d031816901c0d004103001201d03001004003983d82c0c2d10648107404180b4a01c9500082000b070000700002e14001031440b00480c0203104100010703190700341062444248488002540104001a035000446844951074800002e141c4d9400a0f4448541c2401c02c0700050034450f140070076152447c007601100c2089811141401d4482c80359018a03142c404062040c5080c0e10b00c254094070542d8880c12044d06c1510b400c1d0006400d03604410000030b0302790b2054000c600c00303170318001d4841d400101080d40311201c2c5003582d45000034402c07510001805140e8030000540c680c0e549410142042c3c2d0855198100e02e66050210110700788031 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 575276106 1250 575274856 575274863
    0x60705010b33120402060a02010b09270601030c0b0d1e020c01050f070f0f12050a0605011206271506030e0d05030105030d050304140601060c110409020102330112 71
    0x2100303202d1040d0494021940b80711102c111106a6070703501d40c200900b81d00186c0382c403c210b40d61000e60b80d88030303219052103d0182c00b10881c0301051800c555014010641e8241c0b501556801480040001444d1424040c081d504070b0030609898102000300c401c02000c10850121003802c0704045502810002e500030806c4d036601c0d000a001c00d80d030700c0602980842007a2210800564072011941000744a03c03000414000c032480d05d01c019058000c140800d031801520701c000015500d500c00c00841d81c002420038103025a13814103015592509492248012000c110041c81e9103601075444113101e42c40d03206c10210364403a80c18140c1281c88420082c014259440103401c54450b000040d84524010011f881c1290402002044c805110701b008036074034ac00140c411144600ca20064000403501402004c0c0030703082540c1c48040b4060b650602039031100ca221032460050780b83c0811407016036404688280000d002c0c41140c81c05103d00440341d082444d5500d505908228007100201e07014950709100c41d480da02 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 575277356 1250 575276106 575276179
    0xb120a02061c0207121d0a0b0c07120c0e0f010b180f0d030201050603121303021e0303070b0907090207350d050a05090c0102060109050619140307061805060705010b 72
    0x9164812004011401b0880e503444446e00b00200400d0190074014103003203007501d0a40b0400340d50b0740060120f195450f401141d000802c80c100344040108500c040e40d21806d120030a00c4154504030482c40d09225080204400400d1b8111000d1192900c54210481c0c2c0300190105070b180d202410028000c0c1400c0d5880b42c401e00825426541b038000031820355202801280d15040d20515560030015002401d6460140e00e182c05d444000303aa54003400504006070080b04022040d00e0710164180c14180250404829184107003c248040340450700100c560949040032400441c41d00c04280740080c0c031200c03105102e0700002924040380301094020340d016059445060201d911003540c025180c035070501081f40168054801005454110f400c080c0e009200a0300c60009221a62544d40c9402e03c107410508800900284a030414201000040000c02e270918088030989050700001c0c0f00c00c40e9a01c80d2610405000c070344423091020a601a08000d07000610002c2c404940380088100f1050101c0300f40e14681 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 575278606 1250 575277356 575277377
    0x1107050a09050405060a0c090e060d0206041215020f1209120c0f01060b0403030f0c110409060209130c0f2010050118060303081b07050a03020f010b120a02061c020712 73
    0x8528010003181c11f0700c94480c40e103001e09080880341407040040a0941c0040807140110158541d94014406855400540040c00c4814100100002117030308403000034520411034143c080040b10242c0d9071303185154822480f1602c4040c482d61502181d0340e03203030240c880001003004480900003401070061442c0402440b80320383c0c488200005008071701c801b4000ca8030040450303480500c200700c02c08956126894004107041203101007012158000012604107500260341c030740c5442c1801c0900c0d400c0358541d0091100104900d0003c0c980707184902032905200d49808074190320018140d252070f0b0140380340115154210400d12040141c1070038810240d42c15a091400d1549007201d000308000d0300d0305515030003142c0e00c401001403410060a854800425424070000c80001e1040c000c1520700c6000754001e1514091b81c910090031074a4042800348610000b00701406122030120711545c2039034044035400d481c0c50b0709a0940844000c0c80c0250b02c0d909100050320810042c0041404c52500440e9440c0008603 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 575279856 1250 575278606 575278621
    0x30c0105090303030705030c071e020a1205151902030906010e0108160b07170a090603050108011515030204030b160210060e0a0b031f060314030f0a1107050a0905040506 74
    0x61080d0100c040d01600104006201c45000700010742d082300700b0048a40c5002c1c400e072601c91100601c541508d04642e042d00f00b1100350b01c2c0400c10640509820701406204480c55500e2660711404000809400900301c0c2c00a003103c1c104540b04144080a01d10555903850642019a00d451090090890160280c00040b0b012900001c10300c03104280146001c003900c1c00c005403000d868100f03030f008070f400c5000c4040ca030124040101c00707007108981545801610b42c0c00c01001505444058002e1071340c680c075040484041c0c00d04050040c0072200c040c0c10840201d003000e4170071006440340ea0400f0306407004210500a4418a0403030071a0010002d070709590700d010404643c003040d5220352043d1550812900301141c60044240c0c40700300c84010041c1114002056a02d58a1011041d200c0b08402683e482004000f40084030041b40c0c80481c40c000070313528181910b150f41050740200e181c10320070843d4030000381ca91440200150b00190000904492100d030f42d442100c00941001c450885281c05403c006c500c09 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 575281106 1250 575279856 575279867
    0x90521071a070f1d0402040602010e071703040306110d0c02030316030b1503100e10050307090209010c0803040f020315091b090601121b1112090609040207081e09030c01 74
    0x1140c8542e5040c22410001c0400c4a103402c2c20302d0181c8001001c030441001170740d981d10041c40203040940001c20420220214941841c045601c00d8041c948005641101c500020086030247c0741e0040000894540c840400d41b03142c020015901801e43c6045400c422980d000006907100e4460030702c0d121140c80060341c084054079518078103aa0001606108a10001c110002640d1f0200020720310320f2845a43e070f00701419080c005c1d40d080505092a003002d07c140e06041c001c1502900300c08105603d07103540303240020034192035402e01074410f00e00480414200808011504042500142280c10a0b4044242d00e440b0040603199001079100b201c0d101402254070010201041200800000040e580d03000190384500009034940092980c0350f54419100595040c0080c00100aa59400600a00f5024545411483c0701d10207a40401400080c0c456541c1404136984014152070240e12003500780351034030090040041003c4103108181680030300c6da40280c050a002c00044040b02c1844c50b40600640d40c = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 575282356 1250 575281106 575281111
    0x7051c0302040e0f07020c0a06110f0f030306061c111b0d1202311a120a090206121f0f0b181c0c0609060305070c0303090521071a 57
    0x106086400140e00b80e138444030051791115042c0107581960204800040301b00360745800c25000301e1b450400c41c0d25551810000c044172035980300e0082c0046480004004e51340e000c010700840c4a1800020500f8105d1364901000420700b0103a10140b0035017020b980008025081150401036548401084801e01880025080410021a103a88100b15202802c4001940c04203601c0400441c90384d114210342e0031212048220303000313840b03034481481d4240300003452460054040002d400205100341140c02007481c141c030b42c00030340210b03000404000b81d101245060240c10341000c21180008204001282c49022032500c10040d82a4140500c1e122403807403590380c03014001d404c1000828407840300c0200300100007000c80c560080c0824891030001521045554510300c041760541034819003085003a412040c481d014242ca41001c1c0061b1a01c03c9000303020b00d0b08510058101901c405100703060203424040e1842d241c102a0340d00310848480240c01c04a9403041000300c5a81d2038504054805202c2d0380100d50 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 575283606 1250 575282356 575282369
    0x1090c090e04110a0b0c0c100c020d0204021b06011703030f01150c0c060c030f020609120c030d051e06010905010e010c110a09140901020310030b1b03100306140405031911010207051c030204 83
    0xc071401d01c9a02480018be0702e00404980080d07080043d54856644121080c00e01c004c2c07100213044641c10440041c00b9031281c40d400b025141d0040c0140100040850340c40ca040d00c10b801c41d501948640542c00f26400489040040c02d181c21070320b8003240e4254007010100000e4081e443d08412444001004c0340e894200b2108410f503508003682e140c0c10702c00804d00401c19901c1850489040080980c089412a00300b9183c842903041462103911040b51100c40590740300c0710074200811050b1038100040d11100d00d260b0500c0c10811040d413010700700034034072603060300303400c005040c0b800b0f0030b62544900340c01000c0e030610404048810000080d4052014000c8900ca2002101d000350610310b10390f6400794a00001d42060321280400918580000700341019604c9026681151031a8518606000d4212065804288150340c2040200004910000100e50101d04d0203c254240548042402c59215419095068039035000182d03d0052120008079021880c0402500da0500025145d00740c040784202c0c80b0300c2 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 575284856 1250 575283606 575283617
    0xa030509150d0c080402120d02060103080702040914060709080c0607081608070605012301080f07030e06010306020c2b0f120e010e0601090c090e04110a0b0c0c10 71
    0x3500d4180002100d2245010049050030008070005000c15103620b0580c503000104007200308019403808104260300120000081c0c01c60341504c44000f51030744414003000d841d45000150031000c5440d20350000495a800000e64090390701c0700c0e100c1a80703070318040e07818000181302504040380a40000c03038102d00c40b041c01002e00345407010079134428006801075101d208244e038480348040c010504207030041092520803500010258102508021407240380400c00e02e41c034496140c07040341a6045000701d03802845801400b444c507a9601021409840304a0b45100c0301e000f03c40000080010940144c031440c2241401d5444107042083c01d4070050340349100540d504020425910780560081180d00200d04092801d113820408000356082a158541c0f03a00030380c1c0e90344940660620344203001941c0135201d0305000340040d840c926001080c0042d10b000e01d400100c112400700d410403124500100d981c00b000b51030710795041d58a50003c903e5802810b410b85070f44c00352441d40b14541c64101c2e00c11410103003540341d6 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 575286106 1250 575284856 575284867
    0x507030e010e0f061c15081903210207060c0f020d080a0b061602090604140a0203100b072001051606020337060b070201090b03091f02070203070e0c31150e030a0305 72
    0x44c0423104031503243c20741c107200e5144503d50800340d6050342d03800f9203025114007503520406850071078101e80c01c64289c5020400d03807190350b5122a81c0481e50240041c42d038600040c0c1d40d140d088000e4010701508500e07a621900c00210701c02400c2e986189890058022604e8098070340c0d441d0140810707078080550600300200c44000145138110b10b07601454102952a514950444c2c4401050009500444055995403109404c15004441e01054000858001e10b811810301320401c0421225421801c1c00425054001c80001e0160780307c4001030185411503000e64466040100c1c00422200c19892074580880c180480483c403e01c00f8070498808550694400ba5600d00e0400459402c1d0000742c1011002e000b4841e6040a1480c1c2141d100c0482001510043c0d07079007101d1040502e003403d01d5004241c1d500281e420409c0a00050050781e034440d0180703202c00c1d00c20b070011b00e815002144460644032240e10300180800c1c03100d0b40d0303186913400c400c0311b459408cc4080c21804040d60381d004903000800041c82040b2 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 575287356 1250 575286106 575286133
    0x90b0412020f07030b161103031303030b090a0501051c020102030a08070e0a170c011b030c030c0b040c1502030712110c0901090c0f0507030e010e0f061c1508 69
    0x500d903811054510645524000040710035040003455881174498140490500641c40007644105080d14a1405c1c40d107142403540d074142e61240401405030f42e00303000400142c403e241c042d8110703410b1903c00410601040c9020100000144401e01440c0c0c0151540320a4084801c1c01758550b400c400e0b0142c000f0b5082954070001201c40f1321004007881c0400201480404682d103503080c1d00d1002d0915071200020344201509202e141c0161003030fa45040100042d80c411101c4a02c501d0b5400964052400822a080d10704081e900c0c0c01c000701c002420300140c0b1080100b40009a14071205440c001e02012045c07496000040342e40b8040c0b01c201500d0020f03d042d140c2c1400b401030840310070020002c819034062100c4900040c010f208260710010310140c40fa01000d9120360700083d901c0c0c1e00c581909150b400c1c000036450042031003200b02e40c03503814001c0c080c0389850260741d01c800d940c9845500030700d407580d5030204418240c4001c01c009110300e10035003050308802c8a042001420790503919100008d107807001910701c = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 575288606 1250 575287356 575287373
    0xd09050f15010317090418151802040914160305190201120f0f0c0c0203010624030b0307090c021c091401030504021813050d14181f030c03060801090b04 67
    0x484c402000c5041102c0503042c5c896003d40d0241d41035201c802d00001040b802d1015481082c003075a01071040c075080e0400c0c0f03181d0442420a00c882e40603a40003a0b131458910b001500c00e6407020010446200c0c581c820a05c407000101b0f4007054034459001d075070903881c0a42c030710000402910002030101e08000714515110241d9402120701da4410000410395054240d80310382128900711078600041e4510601380107508007400303000000e0400301601c203810881490041d2605003505805010151106682061507404129a0001d001103580801c0140410325000e95038003403441c80f9103141c0340442c3e902d2800038004c92080c4200c0e424807640b01c070f581c008040110000e000007442203030301c0900e02c8201c440c1c070003817480342ca4880d0140f040104901000e034141203240c01f240044510800c80c11440c002412550b0750242c2d910034449107404034000720401d0004949000310965480c0a075841c44019940c1d03545508045a000307a1130f01e08011264a90001c0d034241d88445002410f095900d001203000100c840 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 575289856 1250 575288606 575288633
    0x10b191d0d060b06031003110f030d18031b060f0906050d02091c05010606080a0203162001050a150603021914120f060108061c110103020f0d09050f150103 68
    0x103100000c3d41c41c40352000503103650070903a88083c0c011b40c1b9101c1481004442c403c481e110f10411240050313015010170000380d6904211283c60200007100c42d411214040c0c03801c50001a40d0300a103030145038040b43da103062841007644542c9000443c0511501c0d00d140c024440c0c2c1050710915540c0f41e161420148201d0040e41c4500c604e40d4000c0304400c2c0384a403190304510041c4020b0300c50310012070074902d01f0400a0084001400d03000c03c4900c100b06201c80c80041040c15240042c180c24804020741c494500001cac0d544450540000343e5081032301304612808181d101409400b40313201385844568658030100c00328040ca48819844c0400d03800300c1c0c01e410b40074010f40b880b9404200d140ca07140040c8460701c0750003040244e070079801c009001010b1010560708000c070760347d01c080c0a17031701440c403440a0b0350880d00740300c0000c00260443c0c1c0c1b80d44030080389901c690100c40001202c0c550300c59842c070b24100c004000300304441d010746041c00707088001480d030007010542c22038618902c0f030807181507400e5031101c1d400701100c0d = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 575291106 1250 575289856 575289863
    0x1c0b1e1011070504060b0d0c02071d1005040e0606030d180e060402160305030a0b1f031a0a031a0a110d050903070b04050d09050306070c1b0905010b191d0d 68
    0x140000083c960381c0700e00034240a0405084110303240d00b00b8201e031100f41d030611310590095401c410424400c1b414a6080c2684032945072100c0c01a81d1100300d0341b03980c03da510f50030564202e81040c1c01910031040010b8568003031802a001c980038441c4a00702100c1b10000d018030781c000b401c03d00303804012400000e005076030001c200400040c039254400c2810b07010702514002c114040350b404002c2003186030413449003540740c010994442d403014240e200300344580c400141d1500e0605590340f86040c5030f94603000764850080320283c141c10881e61a81000686180d6040d02180341e80c044000281d6907850f00e0140044014011920609103a48001c004010b00401006940c7c00c0c441071000c14081019528001d01603030162014100c58504050010314540e515040140a40e103c5018000c035254405919a001e907001170440c070041e4200380e400c42c00c000b0302e03034407842001d030400b00042001c0c58110000c0160075403007448000d501d25040b1003603405440d07100b03452600200c14401d0080c1424481c96010b2020f10 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 575292356 1250 575291106 575291113
    0x6110a03050711060412050f03040f15030f0e030c010e01140105010f0215010b1207020715270305280c030201300b011701050904171c0b1e1011 63
    0x1000040391917a0059408040349185084001d02030001c14020f941601d10340c0806540340505284c84408003113003521414490802c0321500401451181d402502020b00c0200c0134441142e4130008030750340341c01121a502c501d520b0150020110b040512400d10040d9030030340d0b0320500c1c2e0318000040d26182100e07071007407043d0300a841c0081a04105c2c1040c4c00d02134200104210b4444050f03201500c4850701c014031000641d4002e4506001404110b00007500050161400188004810491031030000c18022003201804041c140032041003000f2541d040303401da0013507218401c2401c048000c2c0341040b50342405440305900010503c095403060680984240d02145141c0000005540e81c01c1c115007020005c80d59107950388440692584d016010490030b00361a5000d450795414003000074021072010b04001c1c0b8580c6031000c01100c09840e0419120000c0343c008070182c6103070104400401814040c14010b114581070503605030840700b00c06a01075001030182010342c046100d9074080d101c1f00c4040d1401c112070711 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 575293606 1250 575292356 575292383
    0x91c02061902070608010803120f0a0603060f020d0b061e07020f030d030c12140a021803060a0609110703050d0b01111b030d0e1c020a050904061506110a030507 70
    0x2441c2002400e40041e407036004014036032501200404400068104000ca074204200c070b00c2c400d50300d59080580100305488502c00d15200c415814000300900d80c00240b001d070400c4c48a2017a10159400392205021a80040c0250f540c074030104886481414102e41880640092130f642607003e60f006001401d03c003800b0b22045a1038000000d01d032031201151000001d4032000c1e41c0303070391660001c9644884001904284004d1400c40081d04803410000c16600d2050b0b4082003440348012880f46c540c0b5a1f0001500b5281c00341410040800904218001d445015040121141310340320b11904460703100da003650394242800103518141c0080d080d00b0b07040700c0c104415110b001440c44420310142c5800b002c40c2c222035402d401c6840038181007a24400000f0140700c040301c8015129203410300e080b100c40041103000f841c1c0a0301440001c0440c2842d80095030848002d80800040101c950b1081103a1003540401014955840d81304030b8200d0840c04c0361114540040c4010f80010780508053314206102d150900b00e900e = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 575294856 1250 575293606 575293627
    0x5150708031b030a090501110a020d0c1a100905010605090604052101020a0c0b0a051b07260711030d020d051308010212040c06020607020319110f21091c0206 69
    0xa4000791901613400350786000d01400c000d800d108000da90305e4131400c06400d04510200180d140c0740c07040750820612441c2e0942c04100007010718808204c090001d000344c2c0d83c0c20f02885001f0007039114040c2c4c2d88054035040002c10307400c3c060b0003990880380d4010880ca04d0300c0d09040910598040c01c04065010100d807070f04c3d03908050420300181490820b01d039511130002440b424507050302c0708040c090750103480c43c000901064a40c0c403080890b8003040f401019542d14041d18242d00d01e25881c25441c05149600c8040142c0d640501d4010014140200314201080b601e1404041e02d44039881c0600c0c01603408031107103500050282d00a03001000e2580ca091201655661156003641d00183c01c01061010304002c0108220f0708050310005040d03030348000d100074607103050007a5682c0305510149080046d541d500d218a0f23407181c0c4034a0103000c18041a100c80a0100c24071658031140c000512400540c41c3c00c0307540c0380310744000540c0d01304800140711005203120403480460302c2038038031340590300041c0c01c0002d4a40c1 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 575296106 1250 575294856 575294911
    0x1230a11010e120310120213091707050a0326070e0d020d050a1e0302150c1603090608150303030a11220305060a0905030a0809010615090e010515070803 67
    0x65090f045002da4902d0f082400301701c0700c0800d030442c400c51038400c161800513840d105407981c101005501d00180c0548182000e88e080011141c04041c0e800d00003031407108208003c0398604032103110b901e0312a126151894819024a501000c0a00d8902004c00080c24103114007002044101c000d040101406010f030081049c00107498829500c992041789003d04019480950f070740d441c1e0440b1009240f180a6940094547e2040740c4051100c01c5510089408a440c0b50100c070201c02c0200c02e041200700c0c0c2450060400e042030701ca19004210385800040c03180a406000388000c46006010f1461503030785801d51001440b10710b04100303000b07a09022402c0000c0c201c543e42c00d9003d0f446840c1da14214078601d01a89030003401415103a02c103040000d184000b03080001524045105070508400940c0c0707081d0060700420f050f0f840301e96296210400114201d40051841e001c2e80c003200d10a05050381c8420501c4501d840c01c8103810030001081140d01c000c05c0d002c40145800404c01d0b202c000040d4490564a0103 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 575297356 1250 575296106 575296123
    0x804022808030405090603010b010804030509010905103c1b050d0c050120040b07050c150a0917070b070602040e010603060608090115180609150501230a11010e 70
    0x1c1903000040a01a40c9007001d04158412000c800030b028005003800020131a0002400003014407a0120700121681e0003411418081d140c05444401c51400500700101949084100944c1071203041d034240100098030825907554900c1c64489245406142c242294007081e03000c441d2040d490010341d0000021000d21540c00320401c6565050f50012403401c145007194001f0402c180e410b20310748410070b8032a680100b528101c455081003252074000c00c0c10641e0a00d5030000c20254080304801040343c3d01c00c08003005d031121048554580c01d0090311001d00d8503000ca1422a01051940700120070044481144001c0c07000d00d200340000f50030540d54914032042e0210a0700301e18080b0f520340000303100455000d12800c1e13005480a000f400f64140000f24104035142d14080c01e1040c981d086102014500c160708150000c0c001100200301c024102c4184014080403030240f1400150501c000b80c2c24423000810300081c42c8484180c09103031004512066030324003010541d8400715505c4c0c3d031800040f500300348020322 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 575298606 1250 575297356 575297369
    0xc05120307080d051e01080c063001090b0a05130504140d050a1409010f0e030a050a0b0907050102071a03040201030b06160303110a021504030c0b040804180c08040228 73
    0x160303030500f0004844100e030100314006606170000c004000e0610006118400087d0580c0d6440d9107604952104281c0c80d0300c13101c144120b00300b0300e80c40310b5540f140e559020f0485c0e800d03803010003401c040d50041011052492040c1940151006001044203600303a0050b41c20620420400d001c0001d1080d4075801c0103081112203000c16070124588000d0f0303400500b51000781600d80c0f43d15290110b4500083d00c90542e00005200b004400441c0354101d0f01c0802c10303280103507000800c60344810094909903141d1003048443c89805d0046002c001155400014003006035102c81428002c011600850440d142d04024004e1b8105600c1d01000f00c0d4540380c401c0200076204940d601040904140d06010f001d60740003900c0b08408207400c01c13813202119404545004404409110040300c0c0d25242401ca0b40c4001d5480c000d00b4074020303070301030004100b8a05c00502c01c50304c00b0310381d002c28484080020001c445200c11a980412075400005006160100481c000b42c1c2c00b011403545940000c045441d01c0781829001203 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 575299856 1250 575298606 575298611
    0x20406020c0103063804230108040f0f0501020d1407170112260c030408010b0901030c0e060d050d02030a110703051525050405010e0d0c05120307080d 66
    0x900145506000c616151182820b00f488004c0c42c0094004030005100c01d08101c803180f40b901c81c45110080b01c01c01c98921030b84100140c90340d8441c03c84449450200042000c20100400008078a50090705600c0c86290803c1007119108220b44440340d00c82402a000c4425540c03c00000701222403a1180d4007107880250103080321841c0800d0003810309a9000072007202104103d004200c0115030600c403070240ea900c500000d982a1100a002619513521803001c01095804034240c03501100c0080038000f181c21580007800745540030701c03e103c01c0360802c2c04090071203401c424080c400c840441c070445401c41e0014201c07040380c0046455090034052002c01060041c0c100042c00044036505c80364a00c42c80c00310304080d10307040b441d40c0d4030a40d44410107400341058001c0440000c000c554171000342000349640a0321010038040113035005103030b940300d070007207901003a40c8009030b40840c10411480800030f03910003584071f00c01d410001007140e25103006c451000a840b08001c0d0000044100001c1d0000381c01c0c20001 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 575301106 1250 575299856 575299859
    0x102040b03010612060e07031a0a03050a0b0109020307020715050918090d0314040303052d010e07110a0206090f0d0807060c053f0f060a09090b01090203070302070c090204 75
    0x181024101c1c0740301c10000781021742c04c1c440c0d1610004519048191f500380010400382620508891050710300000342e2041c1c0121000081c001b002c030304c0860711845940b4140c032030780c1c0780e0042600700d0200f6140782d00143e100100511142c0c44002d00c01050355041d0420794180b400007000101c40019011140494032288000c3c09150082006031010820300c9050500c26240350415003090413000910150030035440ba0041b4014046035210341c4500d10544546003c3c02250000c1c1480440082c85070704c00b81d080600020f0342040c464580104041200b101400d40403415408200483d080025415400f100308118400c69641714134000c11101e224a2020b6115130290814a04580310000d0045c1070107010046180240c44d481e03503a00c01c0d000d0740308050410340301c05070400c00f4080c00149001c051100e00801d20600302c2400a4480c81a0002c441c480343c101d4444080b0425612000001848400c900f00180b04200003500910380c0614645030043c00c10a20b5240d400344a15964010074569900050 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 575302356 1250 575301106 575301119
    0xe0303070f052b0c031d03180607050307030503070207050906030a02011805030106031401060609060504120512031f06390f0305070308010506030f16120f0b1201060e070c140102040b0301 82
    0xd10102e54075003030700082e101d8048146e0141c8034452101e40000380d90001c100da00d466039034102603404160308501140d845961607d405000c46d0320941c2c4400c0035115521001802d40360865140b8429079014000d0f083d1032404d5401510001c48002d02c0c40c0c1109180c601c041a9600d092207908010b5020709020030fa1394001801943c00c40d807594000390200300d072002c8180016074003d41210125620000b05c0d801d4040c0d103003082400c0ca0350421000e0502040001401003d80c504a403400e0840100000c0c00c1d01582d662000751001c480080d0081400081e40e014002c040079102d8690000040311801d0020040080d0380324040041100400c8000ca080440e183c400d01d60300c40802400740c030081d2281895400c111003c80c2181000414104d1103204414501c0e000512075030500003c00c1e8010300911002444500c0a4003512a81c00085d014210803100102004d005005507812980003d41c141c0881c0c40d800d00458120a2921081c0c1d01d914a003500d0306c98100003440180700030b00b680c802c1d803602c0b94140319 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 575303606 1250 575302356 575302361
    0x150c0f0519020406080f0604022416211b140304080105040302060903160609020102101401060215040f030309170f0901030e031207181a030402040e0303070f052b0c03 73
    0x10000c41711070384a600f41c1c282d04000095202d0300aa0100c6000304000c2c0024001706124440c40340001d40c460002c41d00e400f1101c5038152211055104281c2c07002d94010040d41c192840409402e19800100d0419007458088609840061700314080c003010070200429103086803841d88107078400c040c00c0e95583c040000b03256050010f03e4011801c107001d90715103490000d03a0105411000c0340904101d41d14843c00e821a80200803440c20024000700038040e0401c80c064034044007030f0900c0744e60054041c0b07010641c005050203440710b229551041242401a0f000e440440c000e02d08240100c13035101282c1d41440803024103e0240005442c0880080d0740c4002010004094075911010602c842d8400e0107402c03803219020b48a654082150b103400940c16010f841440c0034030200760300034400705000026074540600b16030011440b99000340c0702030050442c912282c507900d202c02c031007003000030f600d01c04255002c901c0783d4020004c461070186020001c8920038521504910902c46502900e035898080c043e1903034060 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 575304856 1250 575303606 575303609
    0xe040f020102010b03060132030105040516050102010209060f030c0912010c030c051911010b04140405120c1c021c0c050f03040b0f0304170426010501150c0f0519020406 74
    0x80e0081d01036540b510003400c001d640035200c0042140c2300c001a9044035501050082d0301d01000800078400c41c2001e007462074a5407609640c034803007106016000301e9194014000c84482c040007800b10b52801d0f00915900055420140c860311040c2000c000c5403107650303a1003600c03520003181e0b40d000007a405400103003c1c0481d0302c0350400030f090002c00d00400c407010a080d0580b210740c94079420001c00c10030461041900425050315070540c001c1c40c0290846d10080403115031442284078804035105209035030360a01890068001d510a180d200f82030880f6510103008290309180311a0040794082d41384000c14040c1c03031412052a000090840e0348003c1404000c100c203100d001e00c18005585040e041c503000c040303144281d003040241a0000170214040100c0582d6100f21441c07455226074540c1e440314044150789081d0082c60115404c0e0320310004600c041841101e04035100b07040c4480e50318030385010542d080c42060340156084140d650f403c4011401c00d100f2010251106040844a100b05104201c2102c215 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 575306106 1250 575304856 575304859
    0xa120815090c030f1324200a0f02012711010810050d0c0f0e010e0114090a110903010c03020306120109021809160b03101721040e040f020102010b 64
    0x7400900155080e1a01101d8000b007111090f00060b980d0030710407a59a1908100003403000300c12000e0400d06003414036120700301020584041c4a40c41c600ca95081c100c5600b41c10805000104200d290b031503e00a240701047c2402600010407001c101d032001c02c490010b840d020f881c3c0740540c501180c0030020000f54040d245082401c21000c907041141c401d12146210380503980c040d104144880d814400f116410900404a0a0b00c00000d152103041c02900030600303215403810207003e00c001045003540098040c203103440140c10300c401503856144140c0580480c41d41103412440803c1500c50544080c01007281c0c808541d1005070b501d08102c000c1c0030400c0c50881d00003505034035208a10005903140a02d00c0d01d9100144119005c40c0c0758440090b007810150500064429481c0c20b0029a00107004040d500c28203444210491041c0d0320720400c101601d144405981c280c0000c0070b0307002e07000c068107941039211741d003d040c2c2410036481e50711014010000b602c060b074140c9042e1803a0700466a090084c1d04541e01c0 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 575307356 1250 575306106 575306119
    0x210206070c0b0901090209150901050d21140d0501081b1804050111120601090b04030b1602011d0c0a1203050406030e10090b06120714040e0a120815 65
    0x30490001030074820100e100a2640c0d00c0703000030407a181c000750801c030300e21600109800614101164001c081d80c01200c4c0a0b4090b2000307000000700c928006480d05c0c407944d003040c403a00c5a0303100d0114407042e620081940109101540c50041c1070003c4000280500c04100c603000038030355041040b00d42ca00300141c3c00800c0b02c42c96480980761607441c0d140540080041012800b065501c40d440c241e400342800b000d03040065140441c408000d006109042401030a0a8070b0382141c01c1c0e01d0380c81c40c4510b8800d03404064000c1d80a5400b142c4d5240000d01c090480154900c00080c042071520000d01414103c440c0301d101c82c3e0b0040c8244480b0f840c00040110080c007101205002c8040c0541d4082c2447c082ea201741400e0694580010541103014495503e4000f45847d04101ca5102480c1101c401c2a050701d002d030054203035280e003c880100014080d0180c841240c8090700308804401080050203030000c011406000301c0c46500001003c5004280d00c56103d43c44048003844e1020a0310184684001018855003 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 575308606 1250 575307356 575307361
    0x1e030c2a05090406140c03160e0a06270b09041a090601050f0c0118060b0103090b061210110c12030c0a081806070e0109092a110109210206 61
    0x40e12060000071503006480804841d0b0b1a428480001c150f0145002c0d040c422031001c00c410440030b803004501c034035044080321521104481c07045800f2500303c3c4019030014103034502804a68058802d418100914208450514166995040070000c10b03902584590f00003041003440e51426000e43c00d4241340d0401c0b05502d88440800285512502404450501c02c00080402d400c1000e001140c0b1860440d9000340000300100315081c12240f90781c101510410318003e81c494166101717000d40e003503140c1c02003601c150685034030080044511120181087c20701c1a07405000c201200d81c0175509210170014205a1100083c142c52810034060a5036822902e40c100100b041d8800e4140c181c1e50114080d103441e030003a40c6d1380110b00c50030f1141d203a40300750984614800c0242c51035020550010354002071340c40c1d1124558820289003a07640d101c003c1c408501c44d0210080c024082c0c000c0b004480722451030500c0345040c4c4501201c1c02c45410300b50662342d00300041001044541c645006524240580c07000300001e1 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 575309856 1250 575308606 575308673
    0x5090d020f100b011e0503060f120c09090102071407050108060102070e010b09120f280c0902070206041a13060918090215181503130f1e030c 62
    0x41c104840100c454036620008999a84d204140301040d10b00081740c1c0c0d20070100c0408028280c0d130811154540302d0b082554540880c0d051404520310041c50400c01401154641010001600d8004081080542d400c0c0013034008518941026800c2403092000342032400e080c80001045071000814007415540000030130413a03100070455950444944039005512900307000b0009161518004d82c200b041d20481c1c950461001000c036000450342244031002265101d007000708481a0b49044024022014a04040108e001c40341c005011440c402049103181540700e020499404c078051004ac00024004103d10701c04480c560100340143c981400c00407480c1d468902c0c02c00b048404100000712864456100c542192501040c0442c0820390380d002c1922014000d241104160300710041520904100400d484011016000c9038041c038541c0b0035030f040c404160340f2400d000d000400800c8621070a55024002103160700c9100000851083d031311041e104402d410031a1401d010000390441c6003440d0b81c0801c081c0c = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 575311106 1250 575309856 575309863
    0x40f0608041a090a080309100b12030a0305250206070e03031608090a03120507020f090105060a081b030a0e06070215010501110f070801090c080a020904060207050c03010f05090d020f 80
    0x500752040007400700307903403188811420004c26140c010f201d5503010091003440e003804a010b2030b03032404503141004140e050f1410040d2140c07200d203c2d904150010894600c042d4400d41042d0b600040c88145824108000d50510030071000100340140180c04c001d040c06030040d40007901c0a042c0d14100c000310300749450301c0da1a040c000710425000388600c900040441158070707801441c03001907030080030081800080003405401540b01050403489440e41d01c1d4040e884d4580342000300e058401c0689400e00745000d01e41f003a00c161901404128000c004418040d100c12001030045201303144010020070101c1c40c10000c0d41c40e02102400d1142550404010010200f444128242c11107400b443c245030f2441c510000c4506248a40340c4156090080d18000b10ba10b2130705400000025100309580000142c1d241d010b552602920400250f0000840b0040360201d4059005085114050410b0300c01c0d0440c1c0b030380000c0c21129889a0391025945420030401c070400140000003e100da980050800c0e05c042a080584 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 575312356 1250 575311106 575311133
    0x51b030c0909070c1406192a0504080601080d030e0109022202070209130c0e2404180c090e03120412030b06040e0a1b390602040f060804 60
    0x14910b450000d402544602410082c040e006840c4250120f40c50466a03100c940848004402c88a00c14413443c0840041c0314280320019404a1422525010482c40058811074501041000000c0c400494030031000d0162900a2407014024404030021000c050203a4030701d4030b82d200b81170b45082803400260311414240e10015003101c003d815513400e000c074a54001d005040020350014844020803500311003400e1004220760248481c103a1040c0d4a544d9215031803011100b1000321070f5103031a80301440705001451010250000e2021404190b40e04403821140c10700032040e12003540c41041000b890080b48a21030482c800740c0301461a213200b8a62604503410013a1000745040500004516941d201c1ea109041800004040556455a480d000f0301c03148020b840300c0705400c0c81c2c1860608900d41c6180d25103041c00b01038a84030b03041925650a0095079011070071040061200011000710342040282400110f4400d90740107841c0c5041038010400c9203c1600300078240702c0500244000300e0b611105200c0d = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 575313606 1250 575312356 575312359
    0x5060901122417010f0903021b0604090f1d16030308060a05061204140c0904080307091802070b1302060f07050f15010905070807081621051b030c09 65
    0x61104401c0e04904004100c00242e250030702001c1d00c04940f40380c1212111030507006a0009104485c48110218210f5030304400083c00350b0300c400d0300921540641d42030b6644000d07008014900f46982e44001406440c40c0300d0070058803540d200110000e80c25413101160110071031200400304040540c20250340390360180070203070520414000181c115038600c54644040c01000e08100e85072812844007504104094a0071901c8802011100301d402100241200204500600c29401a00d8580790004113500c007a0882040040b409000306154180d06c0d146031403802e0044005a9034485814480c010590291600c00d0076100000c030040503079217140940340e031518807c002d956211070718a4110b103001c900c24881c035200d00861603810884c140c60046103040b2141030b03c007403040c0d81d01ca8000300c0b00e440b0211400d00100381001c001c21341d08a610700c4550a0200e00d420000000c00b17000ca031000c072a41111000340000c0341c41d807080007208009940381d07442e44168070240303605504104040c50224003036000480d = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 575314856 1250 575313606 575313611
    0x5030901031107020d0c0303120e0d05160c08031c0b1005090111060f0411010203031b030703140414070b0f0904090606051306061d0307030605150907030f05010506090112 75
    0x40040e850082c0865894513401000000d0f90f1450345000e140b840788502c8140c0120300740c3c149200725000d042c007942c0740c4098880082c204007000484152080e40080f941001c6555450070340a00243d1611050000342040d00c004503111040902892208914003403031400d91030515086071aa6107130380d1036010300512a41403d0780ca0b100880300403100701c461001010399030720401c02031100d2400901c440b20b0040d80100c6c0010807405c418401642d8174807003590600c8002e04196400070819207020065078118803685804140c43c000c810710302204210594090365140348410100b1540b94041010748000d14123902c0050410142c0d0444825500401d180b04d4015600d400b03244007001361a5008902401c8000c24010402c4110340c041c000a20150042501056a0b002804220f011085042084420040040c81c0702810341d5a81c41c0a088050140c220400d16101ea0350748a503510302086208110582e0005500100210036005848042e0b109038040d540801c0849116640305422042c0760002c40c902 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 575316106 1250 575314856 575314871
    0x608010b0307021f05071e08041b35010b030a06021c02030901090203010b0910170f0a03081506070314130b04150e040b03030a1b020a09050f070c0503090103 69
    0xb40c0c1041034080c0c402001d810b520000442d035407583d43c0007a002d1880c50b82c7c0c0c2e60412105c9402c504e0020b009060a0f004640f0241c0040c0c001048070200c100c00721802c00010030a1581c45074100346180c0a1010440c0d05555410f845040030b10f031000c02e0300f03940c000600901414a5841c042901c07503503400005042c05c0c1d000185c04000d00480030700c541030382c03182c0d030000c650b285000b501d094020b00036500224843d50078030503003508601d403880c0120301480d11204000241841d040e01a445410311940200d258000c2d0350049400c020144207504900340240c803851603915100501485210744181401c0c403910046c004280400d0380078203880000c2564084007551034035242c52510030080f141c3c0c8480040c0384000b4002c40e41c4802c01c1d051505444050722070501c40305c1c8050800058031510450a50540d02c1400300f104070601c1a1107081800c00405e1048441c1c098a402140c108601500500511516a4240440441d080601a1340a03140340f900350001c40707031076803242c0c1c4902c160305000d4105902d0380351 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 575317356 1250 575316106 575316121
    0x70e0d1b0626010e1b1e0c06090106150f020f01090602190915200601080f16080a030c0c1a030103020109050d050d180e0a05060307061107030f060b040504060902190608010b03 77
    0xf200e1416002046c00c0d5030b904d141d07104d40c00d880e901050520420340941000715408020500555042d5245159041c0040d500c01d1070485900c807002200c032046100341410101070200c284074a89105000d01d102590b5000004003140c0c180548851800c10070800343e504000c050101010121380d600a803030102010300d04801d81c10100c82c0d074040b20b904a4010f0f0000060051800541d030f00050041c28140c9180a14865060842120310700c80c060940c1c000c6159400020321658020182034418281c250b8216110b403005001e4600e10b0a5444074503030f0001c0103005560300728800c0740080c01d045034640304040e20fa9540341d03196004001c843c1c0c140310b00305008042e0200b0403903541010380308990251015261402d0300d000a4001940d00728040c2c0030360b45012a82c507114007c03005410154a000f1714174107146698180030800500e00680b0308940d620365a1815030303194081c21f4002c0d805410301140e2280c10740100910700c20601c1d640500e842c0c1c600d0300bc010f00740c4c001c072400e41140c0301041e41c141c40b40d03600103 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 575318606 1250 575317356 575317411
    0x10311061c1d0105090a020d0209090f0307031706090c0904050709270b031204030809010309020a12031403060a060804300801050405070e0d1b0626010e 67
    0x1c00c1424503042010b2000050b034041d24402c10490314500074826520362944075a282c4803c0c11002c2e4202c0054513428000d0700300f581e0b00e6a00084160215a011540c100c0360310b0440d0000041103000441032495402c1034181c180c0e609801c01011525036060b4202041c00c550203120700043e1a00960b01c900000e00807900640c0b441e802415805203410354030b0411001c80018410800040c21814500f103a858040c0c10009a600340f0301c00d40c62003051030182503445414080c0c00c42a956030405449901c540010788910080d0b500410700c480c82d000c1044028940500710006e20014034441d1b280500411045550340b200c44803c4410b0760801103c40e8070341c1c0c02c240c400c9845501c21802c0694810b011002c00d6242400c80c40f20002d4250744000715039032240208429a4010740380e600020b2055400f103040c0e4a4201a0000c45500c240c4660487c98007100325110080c2550348460041040c50100410000b0031382c10442c0e80036560740c0340b00f600d5070414110320120080900140d0890704c201034004212001403 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 575319856 1250 575318606 575318647
    0xc08010c1d0d0b0705070b0a020f070b09070b13060206070e31090f02090901140a18050715030e0f03030703090c08030f0d0e0d081503011104090906060e01031106 71
    0x1c003119200f4906010007605d03640c450002218520070120002d072010040c0c0c42601d44040980c8201c6160517010f4595000035100030340340c2340180c050081c000880703484510040103184445503091862601e04500a420070800401304014003c2e00810030314a82d64608050a020f0420b4500c0e51010100c0386d41020407841400d0202ea241d450f000101c41800b004030040010244203c030103801c15662000c106003a1100c0044541140c2610303000303d890310000ba00b148003202012a1051421156500e880e4035180050b8060035030640130007001d408155040c040d061403c121180206081c40c1811401a030383d100c0148460100345e59100e11608004000e02c006c0001c00813081201c1d107070015102111000e5203d503408a201502e41010407110400c08902c082c4a80b030070b91600b010540d241a5421181e00d0b60201c0207038036540e04c2c114800ba1500704e101070800741402c1c0c100041c0d540c2044c6090011255181c0010344840d101d40b004000059102204c201455030130344542c0e071580c0624002109000c5e03130 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 575321106 1250 575319856 575319863
    0x3150204080610030b0c1606090f120c020f0a030213020a05190906020c040515010c0305130e040b10180f0917030703050610050d05060a0e130c08010c1d0d 68
    0x442081c031410500f000b80c00c4040c0c1c2d00486034140d6903151a40b80b4102c80c8183c5a60038130124580400d03202091302507101c000014060f4101c1c0b00b0541907035441c40c8003003144c0740d0702c8000320b102d44911500b94200309152455500d01520842e042c03d00b1600010030044200021500c56034000030308050103803040041e0361507a00c0100007071640c800c0001d8040c00501031b40c05510018803c1c00e02d5900d4620f018003d207402059151002c4c0b0800020138011200800e00800560500004200c00280f0342203608950008040d03508121401c0e04051404000c14403000d0224401c020001d0340512586441c29078540c60004400070000d6040d10312550039014203100c0ca00548400f01c91107910403080c0e81d440055210320025602081655170f14010800b500ba801424800020018400120710611542c0300a41003080200002d03041940c484d00110080c208441034805011080c4c000010405112641030107080e41030000e02105075101e40040405200038607460840c0d01850403800c0b01d441e608404a107141c1c0 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 575322356 1250 575321106 575321113
    0x604060f0e04030324090207020109050909010905070b030903270301090b01080f0106140f041e0920090408092d10030504021c140d030c030b0108100315020408 70
    0x181d881603079440000855065010908120000400c4466001d01c83d010b1440b41c90303040d28407820041c1d00c0001b50820300089060211907203002c113880e51120714052050b90b074800041644040c6103842420703c2070075442881c40b11000d00a0184d41c12001c0151403881d402d00340080c1c1c0e011003003440313080c17031800c28160560154a4601040140400428968141c0700442d080320520880300400314201c0d2001c1c03203400510141c003000141e0b549400307da1682c0c0404001d0000c10140e01c0c0d445507611081080300509480340d40c503c40d100400020008801264035103040000340040014080b42075508010001054501c00003001c0005039501103441a038201c1070341c0402c0c44489c40c0d4075100d0104603100da89a00c03840f0100090000399100380100c3c0d1251394080c011100c0c14000840b003a4118070244800c84000c4001d0600e1000110108007084074003800c2c0d0741c041818140352002808484010040c0c5041001c0340080182d0740b104200340c4001c45e40d02c02d4010318001400180c4800034061600100030300d00 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 575323606 1250 575322356 575322359
    0x90c130306020304081222030e0111070b04050901050d05060f040f080315150708090904060615081f1d22030c050f0708120705030706060b0c0d020601060212030604060f 74
    0x1080001400444c91104100c0d0501e4031030b5a1f4151551402051042d2200c0d00c242d03905001074404c0c4030403100d601d818107007451000c1c035038001117081408030340200c44c1540010070204107070303e4140c2c109030040c8016207080b00004411b03110705480c1d00c0010301030b000d03004483c400301e01007140f001640c011480d048503c2948a01384451040340110510840900c03e40182c90590f8481d007000b0100c43c541503001c9000d501c1c00040d0b800340701400304000c0c02a00c03003d0351b4400c00101c901c04490004100700d42d0740d8802da490320f4410364100d1103e070088258042203120300c4c000d01c94403904410500d0b08225196002c03960355180c04080c00c00b0300c554004805003404074500d82c400c068024600640c1c00348200259130340d002d02e030039070182d503124548180801399000c00010903900c0c6082006090303e038002c40c1903a290a032140c843d001070751b407150320a00ca4240000390350007107003800b0b20040c00e008159101030080343d45000c60003541c501540c0d2070240300010000100c0c0b11a51140d011400401d0f40b0581c003001c0d00e = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 575324856 1250 575323606 575323613
    0x227011202071101140f0414030f01090b090d170105090a0905031305030105090d0c020d0f0c1403010e012c031c0209010206070207030218090102131e050301020702090c130306020304 80
    0x1825295443c90100310101c035505d0003590402d0540d80803141001c01541090b02d0600e150301c0309060b0500c5240c041c007c952170318401880a000d03006089005840814441c109194118948801010400200684400020f4002032081040c5045035402ca070781c8040c030388800070158000c00c40f0940003841031100207401c1020b00b444100c1d0000701d440c220003c0020740d907030204842c0c0310700c00c4602000001d07000c904102d006182142c1070000040c002e400b502c8580105a484500444140d01302d003004a1002d030741c0401919090003001002c2c2e080341c5c020f11085e0a078a0000c036849100403141c000c1469110002600c1140810503a01103a80d00304445900c9041074880300c2c000d51004407024010300034880001c14103400050030700304595025082d540150214500800460009071254040e5502000500b00a642c402c2041d005000210203401c6180c800710388000c0a124950700a234000e0340140a0500960780e03c4c113840741e101000d42a52907480060f003006042c0d049194200814140c80482403000f070 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 575326106 1250 575324856 575324873
    0x109020d02190f020106050a0308030f070216030b06210c040b0f22060519260a1a091209100c0f110901060801320a0603150504022701120207 62
    0x8003c9181c000304038850300d4206120300a140b501014100010030008603c982020010440d170081d62407040d1000d038207a40c049154100b4090b4419540c5108400500904d843c3c140d41c09400c62070010b01e260404400c004c1445e445941001407941b149980340510304a548070030004c401c200030001c010300c039102502000c16003d5841f42e5070394069189019404036260a00300700881c0c500460001449556207441c4060840801048004100b8402d1821a1440707660030040d421071140b2504030640e003074880381500060b280009000040a911180458184d005600b00b15281c071901501c007400030411070101564500c030000702c02407142c50b11070342040c180080d102405040366400c039498403450b6139600080b03801500c01e001d00400c0c8801c1a001402e010b5846101103800c070740346404c0d01c84444581c400a184c1c1e59a65100c980441e403901c4818480402039071503407001d88402c641c00c505200c1c3c107031045100c0043c1e000c0500000305200c43d0764050740e0301580070311702440c00440045d582d81d089803821040 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 575327356 1250 575326106 575326127
    0x9030f0a020601090507020a020a09050709030c0e04030e091018090b090f012d0f1103010801022a070302130e070311041404030e220509061e060105030109020d0219 72
    0x303d081c41c3c0385c0450051440880d8000000380c0040500503803c1c00c00c0000c07402001c0240c124402c0c4010050000009060700c00444000c184504000c4124a07290401400000c010300032a446010048100a41d41c629020b0310020f0741c080b494502040040a03860500411341044090100c01c00c00d0100b00c80075000082c041a440603c01c002d02c0684507141556545401c110030004071488011804885504154003001d40c500c1c001c0b6000c07075070135088002002e2592081c0c00c00551a500083c0c02d4042040ca951040741c000002000c400c1c1e81d0840324503954442a69003c001d2143d1092503220460a2080d0044800c1a186405460381700c0e07034900d0440940d401c0c203054035010798106031000e444000c111024901c100d405442e00140a8100420407802c00d56608040703000b88440c0b0702d800c0210300284142c61090f043c01e001441c0c00e007440000c3d860700313200140c500404100343e141000309699200702a00d044491180016880e00744111520029000c4c5142c00c0803141100d0313480703800451780f04241703a9 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 575328606 1250 575327356 575327369
    0x31c0b01020709091703060f0a18180c0e090f011406041109010815010507050114041703070c060504020d12021501050301020c031e0403021509010215040f03030509030f0a020601 78
    0xb00116510000d03041500da6040c0013a110280701918000c0d4299000000c41c0c5c0080b00810010500380f14000048105640381c010100c44500c0403002d2010500d54410b80d01c50521880740744080c104191f43c2c0c0d00002007a40100c645503030920000c00d4611904004901220b200d000081c889a280e8801c40e6008a10403581c41c6e10603400c0420200c03400300d40344111940d900040e91208099521403e0000d0003090b0440b00504110040140c000440c1007803143d8003170310802150340202401c1a0500e60b0341a0f20030796121058990400500c0712041d0410940c50030f1a0f4030800205d4150303504d000058280c05034000c0a0f12910085584600c0603a0103c0c0741c01c9103120079100200b050f600c8400780f500701d02402240c89025170041201c1e80c1100c041c0b0215030003410b114429949801d890368003103031803038140322600080075801140780c003c0c541e01480f40c100d521030303851142046880c00d40c0b2500600e043c41403020b000c0c142d4480100b1800c4600344100c94006282c00f0b0390035503550001800a5a0384800d10410 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 575329856 1250 575328606 575328613
    0x30c02030c011106060d32070906050105070b1f030b0f0703050108031c020d02270f280b2d0405061b0c0a0609050301050a1104060c0302031c0b0102 65
    0x103400700e6002d800c99800320940c0d4401804540d49800c140400e80c6a140750680e840800300718860f038410303c206000c240842139804082e2035450800c240a00e8400f094000c03030915400c00780244078a9070307c602a203017081d4128403a032602c2d07114410194144a407601c0d102943e0703440390f5004801d22144c1e1b181302d4040d820160501407039540d1b000c011402c0340c80a0103480c5003a0420844020140130f8020100142001c4040052400460114820482c0d00400344a0002d090030009541c0880580100d52490801a110342c2d131840318050000d0988042503205020f07900280301070400070918506142d01400c0c01c800050750705e0950072020942500030b000c900b00269228900540b035881140140c8040383e0b40a410241010449410300d51710500142180f9804e2160428058044d602c404855000f0b00e49511820a82d900741014542035800052452441c40c1c101b583c0d49140c0c15102c0100c404503181843c0000307101c1a5407808030b05500c982a2500c1c0081d000c030b03c107400c0410503580041c0e0141d400340c00301c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 575331106 1250 575329856 575329873
    0x303080604050903030a1509180203161a0d090f231c0c1406010b030412030504110f01030603060509010c03050f090a240c180b07082a0703030c0203 65
    0x10001035a200316501d5105400c21305c08640880881d82050075000c1e2a282c40944550700c1c0e13844a02100c120032401c1042800010007107003035080521460b40e0f81c00802941108107400c140010051a0000303000701d80d080c500049800400c0c20540c411070340181d0240c2c0c2d003441e0400c2800e282800701c03040252a04a11007040003002c0b0444001815100c11408104581c0c1301ca410b80b50a43d49031210b000140ea01d98036141d050100ca15060001c14040c0002e40c0000e91241444d0800d0621803600320105c3c014103103020700b8000440d09659a581c075039442100c3c450080300e02c51004902a1196500090105090005000e1940d00c190441c0c601920325a40c100b2071541c808040e9041a030064501070f40c260030040c0e2107400f0480c2001c5000d030250322680c840e40c40c0c00608262030102d9030703d0030b00301000420075901050f49011a10400008080c1400700c2c3d81462100e0302c6490366031280d42d07005400c00d901145884086030b0b413694240307034000c44241540c03e03241e901e0a000e0440c41c40d202041748030b030083c1c484 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 575332356 1250 575331106 575331109
    0x21003020c070e0a0902060301170c010c08030a0c020c0411091c0314131d040b07021c110a0206040f031704180b04090204020c160b0304120c080c061003030806 70
    0x3500c01c1d441c418002054110315002000d10440d6001c3d007000360594a84203154056183c803030065000340568584034100703907207807460342d8200140c40c0040c030304000200003d0800319803800103403508443c24201c0000d0100d00124160b00c2d116444400c0d45c0c20038104100c020b0550560005000038400542e013240000050b04d004149118541a000b00403403181484d00e0111040c5102408050001c1911070300d82c143c035520340440c000c0072030b4441522218114100020005402807403a000100c5000411524880c10fa00424040f101e000c1c510070001d4040100d0004202001200521600a00041c0d581c0b5180d0305190340348540f500043d103030b842003100c8207524810b80d80304980031501a01038840c800805980074001800001031840d50185d02c0f502c18101591300c0e03100a18001309084010100d0300010210700001045a50041100030800e00410010440c420090302c4c9442092502503c0d4008614000855028050801710300744079980401c8040000c207040e80c8103480c000d444848a0303139039000 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 575333606 1250 575332356 575332361
    0xa111207051b061c2405131a0d03020a02150a0f0c0512090415090606030c0804051e03070503190e0d02031b04060504051317070b04170705030a0c021003 67
    0x3407a0400b0b01000500c0041c1000c8513121524030150002254401005800c9040e510314a40406542c020b0210b04004c503140c2508060380030180400140300010700c0040c6040302102403400240945681c5a00f07004152090042c0006607900614112096500d400600d14035000041450042020188002c0741140560340320301c0c42c0c5511030700601841040b0b844201e4150000d0340c0e4260010703111080000d01800c1181c0c16405400010303000201c0e40d18040c4024142d4404004420621682c0b00038031022540100300180000f240c2d503070010307007250610180703803851169480140c110300020a070b480c5a55411444e01541403803035529a020b00c600f4904010110003e03542c025451790014114a40a420b00c1c2455404800010400941c45554a012800740c6908654031450410200c4080d020003100c90000b40d41c204400401e0f43c10110300b80e40705040300d000640040e02080c1d041020202c4804503004441a4903442426071340c5a02030f10802400b00b1201c001c1c00c80c03080c2d4200d5040d50180d842407 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 575334856 1250 575333606 575333653
    0x114060d02160606060c081e12090c0102160f03140a1709040605010e1327050f211608070c09140105092703070f08030a15060509060a11120705 63
    0x681c82442c0108100342d1081d46010a503800031610340521440d04944810005640b050ac80c01c07000e080500e42c0d2000090a0403080b50360720a240107142c1040c00300811994001081d248c2c003545400d5404174000c62a458810b079034500400380941d0031241070b04540090081c00816000b6038040c8101078440006545040d900c2224036003044500503111a00c80b041c2d00080071441d200075101250003c04140c0708502621315100752482c1d4407002074940c20140c20411000850301060b500c40719500340d21b040240c18450000c40c00d0480d00c03c00e04240510849000b2501000e0f0b001400758203144d5940e6040004d8403500354840c0300c40c283c1600004071428543e840300c0c0315100ca2034029034000e0458a0408040d00102c1041d221407206003c1d170340020304061030842d201c5010300c0c40680c40f03160102e01c0c54192000e400744408902c03540641003106980000039191130042c00c840454440c1020a01180c0305d0080410301c44140c450500d01251802d002d030b00030010729014400345e42c8070b59898030501c4a6041d06 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 575336106 1250 575334856 575334863
    0xc0306060803090922020a081f0501050a0e22140c1f03150b0f040807080c012f010f0501090e0303040b010329101404140114060d02160606060c 63
    0x3180005d4107600309000f8410543c002d45581c0c0041e2a07294010a0280103d50032000e4290b01c912203d85130250f461030380c40f9803000025010b009660421000c924003281d82c3c03044541c1d6580718004245402d522840f10b070302009200344101110b0000341408580c01d44030b8010505580105484540f10b42000400414030b0b03070740d818407447c000007280d4088000780900c00d00d17450041100400401c0000c1c0900060454031206e80080303440314103010401d070410811f640548010b0f03200071140011a43c10142d05440703e171445250b405481c008035030303600610006145041c410352038000403541072403040d4800c40c10723585840820400d220f07000201681c0c13840142d601900d1040184010000290000e01010904103d484501002100d0111460744403000755500044018400303424000e00d080425613000c0002c0c00c450038400ca0401008103850078106000d00300c80b2a0340040304400c0ca4440c10100c0d416403020003421541da4181c03864a02c540e8180780001c40b029418000009000c5200c0c07031601450580 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 575337356 1250 575336106 575336119
    0x4090908160c1a280e03010e010e16030b01140604031e0c090915050414030a0206010503150f160306050a0b0306041103070504060513150206070f030c120b060f03040c030606080309 79
    0x22aa455400c070810454020400c11a4a016801741900c00303000340c031040c540c0c0380d00100d204500c81c01d80340d0901c0800c0d6454858100c690000304045032850031040e0445224000010340c82d030050f80803444501c070b16000580360348a6101d1609100a221410b00c4800380500b00f00d20043d61201c05400a0320f21403040038250b04290308580040d44502d038403280c0c21034845d083e00c0307a80e010721074002030540c0c2081d0305c068007581001004004a00f010f001c00b0b1501159049003071098680204130f10280381001c1c003507501c2c11403000d14000c4614029400319029060003000c1014580e81c07140302d48003e0740111142030050b41024032a1100c440035200b901e000d50241e8880790304050030302d50103c5040d040305801d841c10064159002030041040419142049140d901814035072402600c0940a006007208000400d440d00100440845e4041c851007034025003504082040c82d07004002038114020000c084010100000c1400200b0000d1000c0400b1a0310441c020300140b540e8030031040c0c6030701802148035040394 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 575338606 1250 575337356 575337397
    0xa0f060903172a0406090608150406030b01090605010c030512060d02031617070e06060f090d0f0b100324020705030d0204030203070f05010807030902040f0e0615040b0604090908160c1a 81
    0x600504e12140d000c01c2191f401054027400100280036250300d0b620680301055004010b001e08207050185502402d800c1c20310760004c2d07043ea6130080c9540b20310802e512040c288440854a10395880c804e480001b5001402c65000040741c801080280b0514442c05600c3c108648400030062004501401181e80b0320a07001d00941c3c0f00007d001840d442a190a44400c0c41000800d0b0259900b5040700031a500400c01e40102d03038030500c2c1080b003c03034010300205040c841000c401c1001440c40f080c108180260002d0400c8408484030258029014500c002090b80c0800301e0240c00b1030040e54003410441c1d008908a0f9a8140d41e00380309000343c40c0c94040d0500003440040040d003d14000e401c02400d2038400340c00054001c0400030710307000702d80341d0300240d42c941d0f0411410300c01c03400b00386a0f4008880c00c044034104142845000040c2880c400d6202d0800801c1d01c814041041c0302c055401d40c0ca00014104c000390031040c2900d05080064941d025a044408541000c15210003c000903698020207001e0035509d0030 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 575339856 1250 575338606 575338619
    0x71e020613171c1a0402030907090209150301031217010617041713030b180309040f0204150c051002040803160203070503070f15020a0f060903172a040609 68
    0x62080b005030b2034a8100141c0901c600c10003200350207807028000010300801c1da007400c86034044550443c3c0d403149005009010f00140082103d03412030b00440030041c1e071200b80d00c003c24a2a80340c3c00c640074036240040000024020442d52346601d03c0c205581c2c811a010b040030807503030760503001e02a42001a2405481c05400240090900c0d0000e0084041070303664000c0d45600111a070100e6285040782d05551000c1040211503a81990400d6000710840240da80041480d95a40201e980985c41152182006003c0044a50441d40644000780c001c1d420420f122101811407020342ea01114075100d9602e1002d81c0b03c0d494401e48080e62507403009035103420400c103101352014000306420b81c0e040c010b0500000da103a07010494140180303071400d070300c040c41807601e0741111401c10340491034810b40d00b1500d044d0001a8840d118003400c0f50784101c0001da40300711810203d0741e81c0320304034640300c100c000f41080c00103c01d01207200d003082c407218550011200010040c0900ea07401148150000725103103a0f01440103 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 575341106 1250 575339856 575339873
    0x409050a0f02010207030c09021c0b1507170403030c05060606090a260601081006080c0907050d06080303151e060f220f051203040509010923071e020613 67
    0x1e20300510488400383d0f00c079120f003100301c01c503640710780707200c40e030000c2c0c901e00c032100003031041841d403040c08020030030304d0901004a00b83c0442d4001c40e810383c0704006120070400c1842c62004151502280351151626100e00c0e0150083c0c4a554003605c00d44264400030300d0a141000880d40210005421400c0359441c041408040880c003100313044481103081001c003141803003001454002c050410090100501100e0300b48101c0b422904499000e80080c41c0d04251502d0312070030349402c5801c07843d1181e40c50164040d1b072001815540c10180403804008113115000031a00122140f903441100d90280070001c40000c1d600850a50300302c00d8200b5400e0020340d024504ca500500111040d66002480c1e402c0c2a80907d1060072054100c0008030442900500c554100780f0030711b03812404050020f628007820032000550704041442280c4d003080c0c8400304000070f880f090003048203a040006103002c0d6400c1c07441000d41a101003005101d034100e110070707101341c0e620301c0050308501800c8103540640000a080d10713001003 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 575342356 1250 575341106 575341133
    0x408030723070e090c040e3a05070302031c02070b061e010f090503060c0a0201140906010b0d060308070311010b10140c0708031306020705090903090427050f07050409050a 75
    0x404c0d0142c060810f401c1c1c0c42c0c501514076200b030005e002d0070b440c11647c400c00c80e401170381d5042000820210700184141c40342410b001903010f602402d01a44034281ca01d0b04070b203075200c1c5080b20740710364152400100318001c0c95006021658859091010141d03103d20901500200502c01e1401d0449108020001d0394054000c1a84070321407450000c0d0601d89500200303150100645101d90b42c00000604984102e5081c801c0e002180c444042c0c000482c00c04602240c0d03501c50602441013200c00c0050607944101c0240c7c4403600441e4400052a01c90b0010300700139110090380d202c802e03182d50030b128445080b4642203664202c00c046607200d8001301c0100591241d01ba8014440c09180361182c1400460028800c00182c410303003c1000c00c01280600b09003009082c8910b03030f400107000c0e001c49000d202e078210003c01500c00518080d02c0020382e03d2540b03001c03280007c10740000512583c0c00e803070701a818480e020410100c2412202e01300c40c00341d07640d8801d00085615400005d0a00c0d0132032080c40380002c290020f40b00 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 575343606 1250 575342356 575342371
    0x507060902060904020c03120c040f0e0720011a011103040608100b16050c09060d29070924081909080313050c091b09150408030723070e 60
    0x9043c0200300010030201e1780140c5a800c01c035400410100b0503000ea2011407607214804010b4030341414036080301421602c0c030340e001b144411284074000501c042e00c90000141c4094194655a2031003901c0109203000f0b000342c1c040c5080380074103001e0342802c0b5400742e8a0110754039603141c029486d042c54580111031401001d00884c001c0d6181000000360074555001031f11003030001c000b071002000c0b15032800a14045004e40088d02818114040182c5640c4603070030350792410340140761009049810480c3e402c8652070900031240e504039107028004401d40c4203401d0010307a01500c1507c83d0001c51b460311441d00888400c400c4d4006608940003c016042c86016074400c1241c01a0229800c0000c0c0c1c7c401507160001c6540c1c101541c0c500c00e403041800810440c400100c0000daa808915003800b089900d0640030211259100080018801c0c03400c1e00c4114404881d85400b0b0101038840740c0361030a0b43d84a600070704003503038031040c1d140103038019085505d2403129000008009040705880c04165524500c401050007 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 575344856 1250 575343606 575343619
    0x1050f1002120a17010308030f1e0601030f0209030a050609010c0512012606070c1505040b1609050901031b050a08281a0402030601120f020d0203030403200a060e010507060902 77
    0x502e5140e04c50000601075031080c08550380340d1070101e0200442ca07600411030300100d5940300c042103040107102e201640100c0c0a181c08601e014520307070b80d200640319082003a0f8040c0320742c010080510001255403801246410000d01071120400000c035414024048c01100034502840100300f10301c0c60701d801c0a03100d424504180400140000410f040560482d2203c000c035142c3c4250502f00420001c440902c0d008001080100d0705261300d4000402c50010043c03001400305024058045010b1101d110040100502c004890340c2c580c580a48603500c80030703403a001c41c990b455001c1207500d0018000410360340034000030510040c042c02c1442c154016098000c10f008062509078003c52000940309c542800d090700110014206032040c5482c1180c16070108020608401c40b1000060030002c0101c1c0b4241c040302c81d000117100c24000641107100d00d44c401458508140c5149800c12030340c035400704501c1030465076030b4034642e0303500c805460520711145000c1c0000c500304030705000586568420b6a0307150000c0d012 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 575346106 1250 575344856 575344877
    0xa0e06010201060b0c06010f06050301080604020d06110a050d0e120a120b060a02010b0328320604060e060601080c0d1e1e0e060f0901140f01050f1002120a 68
    0x30b1302ca10b030780850158040b6400010040c448141403403e458000d00c114601280707998501401282c5402c0044c10080c412641d007003185041c45201d800400c489010700d4115591060b01c1135000c0c101d0341c0300701c030000600350a19414441c5d0f0b02001c0740c10195004800b0106282c00c420750301c2100d664030710310200e2249a90720544480562590f0700030341150781c2547c0000034550f00c1ca00c205407800b000d03c02100704d030415080c1c0113405030981452125107268406401c807122030f80502580c800c1c03e040300b62015054000300255094100000b002c1d406240596400c200048e0060710042d00d0302012034000e40480c4550022404407000c00000b03140307968070b14000144030f8614882074410315913103c1ea403d400507150316100361261003d141701c0a800c03070811010040500900c0c40103850703010061010307115000e81000201c4082d0203401c4400396404c1c0081d03114162038403046842ca210303001c2c0541d0780101c022031808895810310084003800094150000d110724800c030300a40c1c1180d400b441480301003251a01d00c = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 575347356 1250 575346106 575346119
    0x2090d0b04080d1503031106060a1205030405060d020301030c08030301030b070f11060c040f0e090d03110d060b0a08010503030a020a1e05060103110418080d0b0f0303030a060915050a0e0601020106 86
    0x1d4180c4c41c01c0e002c40010f44241c610704009210391a46661010640c1000c4184040c599420706d106e0111981d908804205442d981001800c1d801141d02598108000080020701410568021070503030381320b40e030540300aa0b21581031503502d0200b404000d0030001c42ca00402d10345030140074105409031091624000c0034150080c094201082030b80d41003010320010409100d0b4286410403100a040e10aa00c00000d1030522041da554041c400005010305036030b0901c1003c6200d0090484005040205041c80030603540d540741c0f6400e40c000125480000c500d60004103503450041308581c86106190f0082c14140c101b070301d488240d4180d03410b200070000714404090300010300501c0b81a00840c09605d64108440c0300c1c13020312083d9a5501200c8512031391103042d05001032980810341d05000c004000c0041e4504034200881c0c40000034181c015030511011080050080c5150401d9090750140f600900100d009010a8200f00b4014050640d0001c6001c00c00d00910394111415980b0107414400814031907518007 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 575348606 1250 575347356 575347361
    0x114190806030c0f01080c0d110a05090907030504030c121b050303010816030201021b011206120501110f1206041410081510060507050a050102030c091302090d0b04080d 74
    0xa00460510010001945402e02207600040e0096680c8030400480f040020000a4000c05c000a01c030008192008161501d9003c2203800e0801010140e68a03494400540709030021a566407082c044030001a1009200380149805180e154071464410040740e03aa81030f0f509980c1306001c3c10807203c10029540304008110040e4405d0007007014582d25410903520b5420300010441e100c80810826000b040103076400141d204004000303120382815034041e0401211800782c0300c15072082180c00c100001c40d018044031038816005200c0c000802c145414010400715901400907030703941d032040502c070422134080900c11240e481407005100003403c03624450790310382c800390960b04810340040c0c002e02841061810000c8141c610a01c0003640e48514100307032407942440d91801000304029021a000041140c204041d01c4a154003100030b640307c2c5030207040c102c080d820034031502c0e108040b894560381d100803952080307814010b40070300303949050100c0d5182c04a04210240003168a801c04000c410664506807 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 575349856 1250 575348606 575348647
    0x17090d12021006060905030705030304060f052b0606081311060f0d021908091b0d020d0203070314010b04140f04030c0b011211011e0e06040b03010801150815060114 72
    0x181c480c0034105e400c0c00e051501c0c00d505508128081c1d4002c00050061503000040a8850081850003039540d1401c0101e50b286903c82401000328140d0302500fa40070100160041002c4d1110f544d00c1c3c130312550361060141342020023110003816170034149882e2551410310200510300755001603589403030a40e40d480072604990055607406d20f40c82130b8034400f880480c0d00030a41c9800048610080089141c2c2c4d0201031040300c5908580e82c410800348404404648801c1c1c0a0000a6002401d07100c00a6890070801d0b140e0407a10004050341d460700c5600041c0e40b5140c4102c40ca01e4540e0640564265500001d0f11104000030b882a428010920401c00002e200003c0d014080c1c050002d4140c010250791400c033401d11480e022460500100342d1702581040c0340b02c142412480c1480c900b2044003480b21003c1f03103080c4120f800c0405404c0e800000444c0c00c1ca415006083c00400e8880c9240d041c565800e0000d880708540324480c0c00c5040404086100d540c452101402d091101e0040e0500e000d242c40103519070041301c1c = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 575351106 1250 575349856 575349869
    0x40f0e0f1501360f14010f063009020a060918180201081510080f0702060108030a0e130623041e02030a02121317090d12021006 56
    0x20900444110030080652401000f40c40700031801145410505415000742e00e0002000060b8030002912004803038004034001c3e2030751002080300b51480c0591107aa01824080c0d003041521143c4002071451185440200b040c11418051200d42c4a0300c0d007040c8191a1580c0100c000c1d9120440c440c00760307403400e0200c0010000c645480e41e503245071010f806600002013a0383d0701c030300b490800b030309440401c3c1d04806c1c1511582481c1c40b01041e40d44134500308080c0800500141c0080c00800306007091034100090b2401079010b031202c07030813540e1034400032a5107001c2402920f110350001e10112203020301502ca0000da44c44000e08008d003202819a42c5012030789a07a00c401c3d98411032490604200c04900c01d0602500b0b4146c1c1e0610008440c28080043c1090701c22468540c143c0c00000247e00d401e40b50b0685000390100c01115541d818107986d40310107a1328401040d40c140c0c03540d601060a0f014000101d40c2d00500c0904010005501a1151290f11041c0780c4030b2002e600403030800c52880748445c400e150181c000c = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 575352356 1250 575351106 575351113
    0x6040b04030c0602010902310e07032f10020304180b130603080405151c050f090114040b04050f06090d0906020a0c03110d0503040305031b01050411040f0e0f 69
    0x1c0c6003442c400c0c419480e84400250391600c52000301686031071040d0050f00041e5442d400c040343c122100e2241e04104009000c1ca900c0c90101e180d4803902012440070100c07806170ba8240e0040300d000058000c100f116040c0140c00071441e03050f0008600308030060361040c0a150041d81d0505a480400000300c81e10200c0800303c150b0745081c0c1850a203040d042040c6076041d144020040942955510925072041d400b03001d20030707046410000e11380078070385c400c903600005516401c01e002215889010080e04055a004251851000006203812014414040200b04001003504a038a50f80c448000100002c0c0c825500d03400303001d4120400840c1048024001d9042400810907180c1c90780c0020700c548840d41111046411458810021034100840f51068079003004480c2450100c40b00010382441c1c598000500c5400003003000818081e0220180c8903003103500b03003400080c052440c8150300701c40b0111001400c1070080d90140c5154102944a008201002d01000502482c0003150510301500c5c282040410340c07 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 575353606 1250 575352356 575352359
    0x12050a170703090902030a020c070e010801140408070b060411130e090724020102090d030c0314190e030c1c02041b0f050f091c02120c150304020f06040b04 68
    0x115404680000140c08006642464000e580080c04440d284c40351300c11050700031002c94212010b5504a82d0030f607458200325049659504564101d0403000d200340b42ca15480c002c5440709080b034440e41d481c80395503c41c1c00503150071030a40d141c0c400390b074000d01015045aa01d00282c64002865401084040d1500a041031036928000c54501004c8000f044202ca50700204420426041c10520003403041100b0140740b011403d031500224028003402082c1c9911040006000d003d0540240240f803401340030b40c0c3c540d144000f400d520010b4070301c9010300c0e03494010040100b21440c00d10540b050400244002d090790000b4442c0800680707084c0c504a04220000441640c4004610f010300c9180724000162501d52405144482c000d428a810186280180000000d442240d0300003881110111100105094440001c10f00d072013504400940040380a01d841c840680407440c4001150480500c000b4001c000240b40c1180c0132840c0c1c0c002030b00c1203800c040c0c240e0340c1384043d50313440f4081c1c03010b060885582500c03203 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 575354856 1250 575353606 575353613
    0xb07090e19060602120d1107020402030708010e010902040b0711040e030f280f260a1e090b19090203010e160f0b0a08040305090a030302010606020d080c03010e060a12050a 75
    0x1c80240c0d010f84103544c02442940c1d1031841c41c07004c0c0c4e80341c52680d0f14001420701907510b012005102c4c0b0710000358803070710010420644503000064030741030b44d1145940c07a085a885200c218200e20440c041c0d810341e62001d12404001501d01d41d030341e40e02c1210241000c903003c46100403640c65900040059130414134042004050142011005000c00301c203800110100400c092016196420825805080141501e402c03016240c84c54004a1242511503482142d8603081041400801c580f2000400800500b8401103c6000074000c0c07000d059007180d0043c216403981d00030307405000c1c928101401c4d06600c40b40b42c20b0250340c00380708250305c0ba50b551340a0800e0802c3e4040e0600c5000240d004440304801441040c00100c0818098403800710b141c2c04e0414140e1101d060540341070050203d05580500000030110426038190050011285141c00b110080c0f4803818052354901c0c0b00f1112840035107000d10040228030318880055405c4003004d810075500c1520b030240180c12030300001060750590b0100c150403081 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 575356106 1250 575354856 575354861
    0xc050f010204050f0a03020604141f0216060315061b0f0809011b11010e06041203090905010b040b190c0c14091518091207140d0503040c030b07090e19 66
    0x1311004503800665642180c0c00281c050143d806a903218021010042419031102c804061110844601d04000b000e50300d80002e545400c1c541c413a040c4201200c100203529400b03809001401e5180741c102e942e03401d0404a0448150000d100100035103410040810301240360700707142c0c609960040050503900c2840d54000b5042c041d1417074107a4405400b940c01e140214040300e10260a84509180c601c07c80c3c81904001181170080d03402851030340c20348210f0300b0100354001c4a001e0272200b0703001050140382ea03200000b0f441b030701852103100c0004030f040044000907a01d001200c0b240d440c407030034008504080c6031102c040d011040d0f0451000c400624074407145500d0561700b640d60014100b101841d4101c480c0d008100750302d00185c914503203c901c80011071003080d0188190700c3e0340114113410507200c11281c00e2907010ba408070102070f15540100c40c0034100316803080301200d210303640000300d01300d00900c0c3d907948154a0710014092010020340f40e201003540d03c0360041c0c0e180141c0c8110300400d21115001040c104 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 575357356 1250 575356106 575356129
    0xc07050a0b04090902060405060d0e0d1d13020d0c05033408091e03090906120d1101020d020313110904110f0a05060d0501030c080609030d020306010c050f01020405 72
    0x1080c10200c100704411041c1c0c5007150207039900f001001c140c6480c6071002c10102e00032604029071150380400c60405941c03013980940c88600d20351089403200914090281d610b601a90401000821180004019030030401074070100100c511000510385040840040304540f200880800040e4001090083c01c446541132920b64004003000c8440f4443e202c107004a108010240b91130a000c0c8240000f080b0039418081101040f41c0f2441d900300b5903605000040c0c40703a005507202d502c03845112000c282e1034200241c1440d00c0c100700c0c40007480078020701081514030000000c4a04003d42d020880f0f0300380100540040d501400300103040c111080410b1a1400303078801e58a035040c3c001c02c144420000490f50013010010300040c20713030704140000100004520070340c01c07a80105030840e034000740251804841c1e030700c824126030240e0309000c0b07440d886007011919050180d8060700583d0080c840ba81d0704143c264000c40d0000014144440c06400942ea0541850b007075080c0125280d5011900300178608160a0304c92 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 575358606 1250 575357356 575357359
    0x6100e03030a1116030530180d060c030204051201151a0706060303120e010c0806040c030207050105131106030403020c01120e0d0903050c010224090106030b09060a0b150307210905030c0705 83
    0xc40562121049040d0040649440884000407122310158456840b5a90a1908680700b802514080031001d0083c0d40a8420b0718020480038048290000061050320200a65450201c01343c030f2501b00407040c500714210703080405450800120700011400c0c42441c0007184642c558603245010400010211102d41c1c807105116414a040714610960141c001c0d40d10a100702c80000e51001c19410440c028050740304014025032811082c8452000c11026490305a880b034640312101d110341c5030600109000c25035000300541d10040b25120b20b580141d007841c000e14001c000015608011804d0a440c080845002c6004503102c100d042c41444070038002c402d0706403002e0008101d0031407940e028055080d424540300041825650128810319000c4d0010002075801503201400d40c24103546036a1910030585603540407900d000001206802d0118170902200c0800342042e04680d5942400d482491140e04801070740c0058540e0302d03d4840c0c552082c800601d0103200150b4131030b0007010800d03242042542210703 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 575359712 1106 575358606 575358673
    0x1207141e0403050f0a02032a1c0203010b0307060e22050c1209010b06040b030702010b030303132627061206100e03030a11160305 57
    0x41c42960b000310b06441c41496120341403669840b9408000307406401044c0c0f401c0761609201da0148521908907103001c1e41d10301050004d0752340000c98400380080b400042070301301036050034404d020038554190003c0150b9810030001412500820410301c0c070440110b901c02d00b65000104901c401040d500c0010b001c41e040c1b24503035144542103008417504000902001660034401402423408141014000d0b41c90603041241c1103407a644020b0551080d9902c4140c02010750b102003009621070314128920345880d40c247e18040b4401c1c010f091844116020011000740410207a02c11181c00800100c5030980060044d144900d400c030050001617801000450756020350580c0001d003501c940d8045451140005032003405840c94100c003c16207402d075005004100b800d80c0907031880400380c213004007140d124910003841321003402c1c2e0580007103c40390440c0c11111864026100046a07040d442c01c0c19 = true := by decide +kernel

theorem cover : BRFrame.Cov 575179856 575359712 := by
  have h0 := BRFrame.cov_init 575179856
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575179856 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575179856 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575179856 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575179856 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575179856 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575179856 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575179856 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575179856 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575179856 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575179856 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575179856 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575179856 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575179856 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575179856 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575179856 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575179856 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575179856 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575179856 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575179856 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575179856 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575179856 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575179856 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575179856 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575179856 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575179856 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575179856 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575179856 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575179856 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575179856 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575179856 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575179856 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575179856 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575179856 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575179856 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575179856 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575179856 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575179856 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575179856 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575179856 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575179856 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575179856 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575179856 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575179856 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575179856 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575179856 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575179856 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575179856 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575179856 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575179856 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575179856 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575179856 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575179856 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575179856 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575179856 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575179856 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575179856 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575179856 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575179856 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575179856 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575179856 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575179856 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575179856 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575179856 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575179856 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575179856 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575179856 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575179856 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575179856 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575179856 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575179856 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575179856 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575179856 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575179856 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575179856 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575179856 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575179856 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575179856 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575179856 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575179856 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575179856 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575179856 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575179856 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575179856 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575179856 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575179856 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575179856 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575179856 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575179856 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575179856 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575179856 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575179856 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575179856 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575179856 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575179856 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575179856 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575179856 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575179856 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575179856 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575179856 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575179856 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575179856 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575179856 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575179856 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575179856 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575179856 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575179856 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575179856 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575179856 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575179856 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575179856 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575179856 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575179856 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575179856 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575179856 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575179856 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575179856 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575179856 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575179856 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575179856 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575179856 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575179856 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575179856 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575179856 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575179856 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575179856 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575179856 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575179856 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575179856 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575179856 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575179856 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575179856 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575179856 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575179856 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575179856 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575179856 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575179856 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575179856 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575179856 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575179856 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575179856 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575179856 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575179856 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575179856 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575179856 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 575179856 ≤ n) (h2 : n < 575359712) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
