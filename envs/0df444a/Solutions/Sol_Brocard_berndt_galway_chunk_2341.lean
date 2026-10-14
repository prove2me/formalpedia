-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2341
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T06:25:06.856049+00:00
-- url     : https://prove2.me/submissions/949a11c3-8eec-4681-9fba-cd6ee8b921cc

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 420863309 ≤ n < 421043165 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 420864559 1250 420863309 420863321
    0x50d090615031104050a02031e101a0d0c03180b06030102040f03150e030720150d0204170c06041509050402030a0905010c03270201090308030c090a150f08040f0212010b04 75
    0x8400c6d070310410030303c44441c51620210303000d0a0098802c0301c2c96500c104070800d011000390710159410810100c0a080c0e070020310018555528464010441500300700812070071030382c07101e100700c50705400051404045840e402d180d80c1d00c044c0050026103400e80710550000505e4850f44101c1f0155104140300509003009c1c0100301141003240700035405c00e28240c0702c42500c0040d002c1346842e00b2001003001d8407281c4889211070600030744080010f9407100f040070078000940c00b900c5407040b0f00280f004800c0c0051030100d42e020204030020203080c2801d080401c4550f540844154060602000000004003074030751b80042d5200c0d001546002031614014184507095600b0103120a00301407a0840d842030f81d04603103001c02d070500c110891001c0328000358801601c500d4001c1d007019112100100800c08a000c02c00c005001c09e920076181d403140c13599209008003100d0b44031403250020078085c01c07202007100d01c40e00701281e2260045081340d088049903004500310908810009200340d440302c07400c05060030306000350 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 420865809 1250 420864559 420864571
    0x1a0d0819021b09040303020910090f050118062a031d010c1a090c0303041e08030304110105090a090513021509010210090201030e0f0607080a060501050d09061503110405 74
    0x140c070342c141400c0210400415003000841c0b04003502000315060503c0707941560f015080c054800d502503400c0e1303480545220754611420414040000000c602e6520a0503040440250054484103690038200c0c00d883d603026542849003440e001c02c0411503020703044094941c46a00984400c4048455401400c0a0300c1c0b09030725481c140560081200000b400c9040040e0b01185146101c401e2030321503c002c00d06049035001410361520000c01c01203140c01044081a80240d410b0b5101e000c1c2c0c07a0b41e5900c5517200d000c01c880c080c00c54141e0b8100e5441d1035000e50700428440390000d00039007042d511004108111a03007074a160700c45c011525081000c5003000d80c5160744d00020810810f003007509060000f942c0d400d09220084116444106d800f0459009400840f0740c00c4180058a20b062640400b0643d2003900b1602400040c8450012504010187c8100d4080e81e5040c0e4070706161031601c06082025020303030f10044840300d42d51640c40000c0c1394102c4c801d0018522520306550301000190810091320005040 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 420867059 1250 420865809 420865813
    0x1c060e0d03110712030b0d050105090c010206071b170d020c0708012f0c060108031e0304020d0f1a010f14030c06090118031a04150504020609041a0d081902 68
    0x40d01d810100d10001e658101354841c0f51070714800d400704000c8001e406910700440c1c020040546807001c009041d000745200743c00a6003210038192054004a940b808140d400801041e116150084402c460540d074010703d60040750200204240800b8604c0f00741c0c040020000d45980c00f09529200c0441401588010001c075402400507002a41036007030203071192a0f03034072011815040314581503841c0b0404e1350382040100d01681d9156070344101d11522540054069035291b4401e1094800d50400242928000c0303401800c2c40b01114426075403404d510070a440140d940030906146000c4908000441c0340c00b81c0a50000034000901c0c0400409032400c21000b024481d0300040079060140c1c45a200703a80550b542440d0000103040a841e411441076040c0d00054440c3c10302c940050540c03132500700300ca4001c500c140c061b400c001203020010822950142c400a500c080200300340910740c50980c01c840c0b0302041d00c440103494218a480040e142a0715840e040311000c4010641c405604c2000021510950781400 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 420868309 1250 420867059 420867071
    0x91801080123010b0919030308091603080f0313020301060603240803031f0906080d0818061513050907030b1b0703180506030f060a060c02090609061c060e0d03 70
    0x1c11100c02e540140140f000800c00811031008a45c0c48841c442e030504400c400032043c541e02c0341001001150200c4080084d403040c407c4400200300c168000104070794200e0101400c0000368045580d407680301500d0307010035541422008005d83e50a200b41c178000c1c40c5549001810318480400d20304850040f04110303616148040c42045024404411a548040924044c0030310300d002484e2403890424940050300703511701d004808610080e0000315580210401d4942c010180d80380001682c14881c048140c03000d0b07070401d1010451150489161581c0e01c00000c01c14400c00522034081390444404a03401c41c0b041e07109520820510001c0b00c1002e810544e1307a40e0100000388030910b814100d121b0214014104122500703c1000c000482032031340c0140c503004144640d2420a210419441c8005842e5644640a82200043c6030b50240951101140d40500a40754654900d420000407020080030a500050307503070200e41000d41e65a1034102ca80340b050f0f0300002c407410700c03469007460710204407140d07000c0c14a80b0b4 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 420869559 1250 420868309 420868361
    0x3070201020304030210050f21060f031504080c10061a1e030703020f0c0a0204060b09010212070507082b030603030905060a121805010b031617030918010801 69
    0x2c07044605890f01501d060b007041d880d8039002c0743e40388a0300d40291500d08000c14024503401443c0c500c0500c010300196078019a8484404004e114260380703205d254941d00961060101160103015940c0c0903001c0c04980b405d0041c0d1180d65030800d0b007440301c182000c0742d50f144140001e0f03070710b001a282c0c800503118145013030902024a05003140010404c0c0c1c0840721000c4009200746200c0e8044440c01002c040e080c0d91520312584040d66501010301c822841141422408504403e050081d1907640c40142e000b04400e01c401641c2c0b4160354020740094074180612200414414810400c0548165a409082545401c3c00c0c800f5802c400d64600d041c41058141041000465400300d0301205450301103510319621501810191400c820b100000200f1a08100c101040318141c0000c00c54040c0c0100020304c00c842c176503410507403a240344820f121280031112400b400301e15506171a50f01841c0c01c44089030701d02600000010188000c2c030030703000e121000f00d00042c4803612007800b5911214820315402481d1000340 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 420870809 1250 420869559 420869563
    0x10e04150f120b070c24061d091b010e0405090618030708091005070203070b03100e09100e0a0b0c0d06060206061008090124170d090b07020a0302120105180307020102 73
    0x4e00782108100c28400c0d003806208017605542580540300f83c03c5082101d2444058001e050030b84a40910340d0904c407207070320f1034481d0340140780d21601d030304409450403044919035580103507401c130840d504001c0c40c030b00c00324196100c2e407080d14050404400201041e10340180300041124807030503000c2564200f4400c01c8002484441507913507041c01240c80c0d24402e48400022109806420b502a6045c442c0d2000000c48100754001103005030706080d00d415a441c0c5030520014407802c04c0d1070040c1d281d0b01c0190300c003034a011242d0120744040381d80030507a0380741059a100e44070031100545192172401e0b000900e101903c081803281100401160005d8601440c0100004844208204c03002003840480e800150981780c081d801100b8080403c084113003806e034207440d45403405219001da070a03280d1a02c503c06134100e10024050341500300c199078007801c060601104454640100200b2600b01c008800040300507596014151055802c0340000101860042604840200503a08480c0304e50401c1240c503000d82d0b40 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 420872059 1250 420870809 420870811
    0xc060a0804080f0f0703030e0c0418080a02160f0f061b02010c02060d111b01110406141c0209030c040c0e1c0f0803041209060807030b010e04150f120b 66
    0x415035482c3c1c0c02030100301c1e00d5442010b901031006000010540101a010340c007081e2001c8100003110540c02d010414402101c4500984402e9038880f00201c40018401000034007c0014501c1500c000d024650041c00c42c0d4113850300600c0c800b6035652410f001100c0e000782c0a100034102483c080c1c548100701d841c4a0740c03071480c0710320103410065402c00380c1081d0740700c4404441480204c4501041210b1b035458a40a450300036607065015820340141e0b400140b0f205024454580132070350151845c080c1751407002d0f10007000c200d22070741e224042402040201c04516141054028a28501513030b5031040c0010181881280d11600740305070f00d0300b00d514000540c817005101480c2010381c3c10a001c41c0000c01480340c01c8191440c010201520410480100448800035500403032081e0241c00806640780d0007a0f500300118000c40c800a004140001c1c8030f40c0c420b401c20030400c441070400851a80c1d04a020900783d840511000126018100381007210b400d00310700b0303440240780c07010401461220743d584207049400 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 420873309 1250 420872059 420872063
    0x2040f062606040e0111040b0d050c0301050a0608090715050a020f0105011a07020109051011100b010f0804062a120b0f06090310020d050a0e01091a0c040b0310080c060a0804 76
    0x84c0d941c60000d101c00d000d43c4031000900d1401d51440d03d440e0303150034000c015030102c0500d0218504050200c0e9041c054142030b03e059440003041d011101c1d00f450012100000014036150861240700d8002450280881da840c241c0c1665a0360303a681da002904000e8a0704040354000700c180e038904401003240001d03546152040b40c2e00c0c00e045903902c1500380012668160203400c110380c041000540c180960b500300031046061088a0103507003523088100b038640c00301e40c0c042d2000b50108a00061000c80d591007904c82c02c0e0b10502c65600001c5030198615540056003007016502114429160181e200700d07002009901c1d40c5444081c2484030075180004940c0314845401010f0140d100803466030019601804602d99070300520404545407618a880c404c05048103644004c0180e10305000302c03d903002c060007180320241e0400d810314030710f04c0200c003d186480002819001c0913001408080b500203081c10085014401000342100414240310541d401c242e410001607200c0c500070002e104207250044c1d05617600c15 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 420874559 1250 420873309 420873311
    0xf0303061d091c0c1509170f040b030c2106011209020307030b040c08120d14010617060a0b07080309010b01172208040303020a0605011406090f0d02030102040f06260604 74
    0x1a807100144c0b000350341d000340204131040072841007400010310ba02142c0c00d180110406500410911581c00441c414140c1c850b01c640c034104004d104001594004542000300c201240b4a0100d514560380900c21441078218581030840060002c03540e4001d1210f441045154010450380030183d00090ba40c5902e80f00081c03002210f4400102401003003401c2d00e001f000150191030080c80f002929000310360200300b0b48600546045001001c801c1c8110680303059828903210480f600b484200601e005240003080e030355111000070004204c0360080c801400d0214424034400f510b906104924500b961500007540341002a000302c5940604c0441d505c07035070000d400700002c03605440442090350710440d148c8000351844400282c004100340e4000340b400b203c82d005801c03c0201d642c0307400031140701c1660119190361000040c0030509403031401d1a50018809801050005884029404a42640c00580c060b15044d9103858040041e250000c1c6140c0040308546004401c1300d20380504d018405001404039030180d = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 420875809 1250 420874559 420874603
    0xc040909060b030708060a0606050306010c0f1103071215020304030e1003060305070b190c0c0b0913061203080c0702060406080408090d080c0d09230d0f0303061d09 72
    0x2010250b40641288200a01a82c0e040743c1c4500701d240c2e5030071054a61040240c600180040c440780700320280d90162030141c2d150790400031300781ca6038043c44140043c03d03600e545099083c00c07140da4003008200e00400d906a80102d500006003480c0c0050040c00d00325030780e034038010800c20000a0388034840724503180d021940c003081d85444860440050079aa04010a148140140800c01c0310810024140f20200c144031800950b250400071540040c3c1101c0c01000000c40c0b01c4144500b1501c1006880000c2000d00403e506a2006400718203403003040e802440c0482c3e003200c03110149640290025401030380d00000c10b15250040d80420003502c510300c59041084120808a030410440408655015800034041d100c00016800c101c06c0c01d40c02100000b41e188510012104054044c00400080380c0c448085155500e48036807207603c03a08a55070f40a94000c01d583c16880c002580c84281c0020036020755400035800d0308086411010380c024007584101400b0650070402c1b05070000130805880c07540442ca0742c6038 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 420877059 1250 420875809 420875813
    0x310090512040b07020f030c01140d0b03060a09170301060503060409060e030c1c0c08070818060712030b0418060b010e06041d1b0f0319050406050a050f0c040909 71
    0x4200707041200490750780340080c00258003516100900700320340c02200e02e00b1120317801e0703000c05a03600c96040300d450114480b03d4202d1056542900540620060907402045281541001a050500454401c000c40356204600028030400e551500c0c008001100054615410001d0280040c00003e1205215507142c80303400d4104045a00409011030040c2d0859440d540b5200031517454050800c078000400309241304004003948100040411079422071002071a0034441e8940c91029440f12400d040003501c14205102203071600401001a10300030490009600340c0075100a00340c40404041c40e200e9401e00c0f41c4034100c02e003102e41d001c0303049034008000550003203800c0060700d804140b220040d074403600109000441040c0b031381c00c5034182c1c4140740369100303280e54102c000140300c600240203205049080c0302c6103026011a800454111141c0c1d510800d100e44011301040c01d44404680803034400c0c0e1102c0c00d000729251a40640e640010003281400700500c0c0a03a2001c91700d0281e803050f01c54135516880500c00b = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 420878309 1250 420877059 420877063
    0x60f2307091a0a140f030915060f061b03270405070e130f0509070617040b06010f021203180615030309040f11042403020703170405010e070f14010e03100905 69
    0x21100300710341c1000d6101c0c0d61500500b03101b80c00484c1d022040d0b02800094440040d0b554503198424080200340c1e01d100b1940b0b000b07000c220380000400d0080003110420382c801000082010708440401016007102c0c03500c4122082a0385445540b980b4041c40c18041442007045d00080001e1080717030b0503110b00c0403020301c1c208140c0140400d00c616074802841e0100303000702000b02003203107010b45603591103010507080d400002504040301118003800c00c0c2e5040010a07001e601c1040d82a16001442c03040b40c0c0f80c00c4030324a0070f840b594001d072485020080070001c5000c06040510010f03a0201000b0440e80720030f10f00c134000c2601e0b4271400c140c1900c2607a590b0244000500716902100310710030180507807030302c3c0d41e1203a04069640840106440000c0060f04886200e0340c17180c000ca03100c807075241e550740d0708911001c404185240703400750007262503540301c84c08a80701e0f0404003c0c40004000041070035800b24035150441c007160684401c401d040200b0000b41358070b136482c0000d10717100c0064070f00d200049042690504074 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 420879559 1250 420878309 420878327
    0x71a0406020a0201060b03060a1505040e24030f070b0a110f011a150406050d020c01140105100c0507050d1406040312110301030f0f060f2307091a0a 65
    0x10010040050a10040c421954007905440b40542c00802a09840d00d004e8203041c041100c0ca02d43c0090039041c2405604401e4640084100d035a00f01281042d84803440c5d80d0350904e00326400348860a90704056500543c035910000c0899030250701620490701c0c0c60031007a444d4500d40c080c0b100f0106000800801c40e9114000c40451b841800003610700100002d11540d010300b40300c030705440c0f940320350ba07420b4411440c10102d04030028040182851070140b0705541038030643c02050a003801d00743d00f44a030780c004070030078003a040c2180d8142507218030325810801008054480c2e840b8075410840d191440f43c00103200000c0501c2924011110808900f195103841c00b0f80344504c0140031180d010b0b03003042c40100340e0003070300030030514800e05401e102a00200c841c41030030f80802d12000e010700c81d05217155804500012000c1c03040501681c40070440000e01c241200035144507103c82408280c00c009460024422504500c0e000844e5203040301e105031420b20686949030300ca940e03d0205690001380440300a008803104 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 420880809 1250 420879559 420879593
    0xd0f0605030c1e1002030c070e01081906110c06070801090b01021b0a1707081b131a030d0c030201050906010e0403050c0708060a0209040b0f090c0c070b0313020111010c120207 77
    0x35141352050004025140e030848401050079101e0610003040c5040d01142e494140c5a9a000421000e000a88000790590384403030161f900d940c3c0c40d10740b088500040b500503d110811100141001d0501c01002440824141e0104800a00d080103074803a03603074081a50b03020016a40d10350200001c2240025180c03540580c454152195440541f5140600110310038084511400607900c3c0b04016491030300003400c3d6100419403040c221090172010010a602003004800c07202e40061307100c148000424074010f10015070380c0208100c1d9081008041e42406410b5101c2010f1f00604400d500d44038400010460141c40141403141c0480c0d0f089100400308980d40040c0b000340f0440d011804c10850380f40007544034520082c00b550500350003070b01904205041008403040980450850341e681c5a200c0150b4026201d21b80150180c06000100e81200303102940c0650803125601d4110880741c030000d08004101c140f50071182e41070481c00301d00f16030006e401507070325500964050782e40e09251811000340700b091000 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 420882059 1250 420880809 420880819
    0x1d15130b10030b031615030f0213090501080706090e04030503040213180210031e0203070203090d121704050303190b040912020111040b0f09120709020d0f0605030c1e 73
    0xe101c405a00d40c0240d034803c0002e400b0b81d244202443c011880b040164012184c0c0143c0850504a50718800c1e8084000c16200390f50043c10901c1c44603640c00c40200c964403140c00c803902d8600601070440c041c80a0002428a810840203807403030040d0342044440001d00c05014850040001025900c804a0039800d11054050410003d030900c124042c404060040580c0940601801070070300b14020f2160f191300384600d0522004100111440401961008084030b045000a112a084588405140301c0a2034420340c0140203400b1f4100000b000707410300908922421217a0b00501c0046100841180d80041c01c410070444242200309848010300040000b13283c015292090b6181030000543c14810780c01019070003803040c8000550244054000d03070040c0e00081c04100201f1010407401c1c0d005240d00000a00300c610340041d4641a1403c00c030641d8001c0e41683e80001c0d40e916070402c9440780f540140c100034010061282801c0209503524079040500c2d0103004181c0b40010705c10000369001e4101840240 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 420883309 1250 420882059 420882079
    0x10926010c030c1d061e0909100b07080a090e090f0d0e0102070e0a0e07080d0e030607090302010e130614040f0e06070503100e010b041d15130b 63
    0x140009410049604520654078000701089464460701034858800d8080d41c030000c100e20400f91301101c1c0600c050f46154850803c02503044941c4081d680a05c50004024115440f44002400c2c0401e03920010003400005401340c130148500c500c100241c43c2c050341c10482154545000240640380361456801c002d014a01140030890822400544030144d0b0702984140e503030100c00100305131a0300c02000710441c050b800065040c0800c10104003c076600200041c4003050a480005500d41003121035004500f41c0c1d00701b415618bc0341500490940307002041070f0020000c0d0728000c00003c003805801e000090400c5030b426400c030402d41e40c40350355042d808100c660400c142a5a444203151010701c3d1510a40a54284082070110700080d11905004e1080400a00110f6840100889050780020301d0086a04003410001c078403d4810b1296074040c0c02000750b0940e0365070400e1080e0030710700b031205071442c0400c140c80c04103c03400c0d140c3d8040210215040c0c8136022611605101280030f0400025800c1e00708851103 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 420884559 1250 420883309 420883349
    0x6071a10080a1202150c0306040c031104060801060906170a110c10021b0105040507060f09080f03070317160e03032101091107050c0f040b10020703051606021002090109 74
    0x105030f41490a403602110081c03001580c032150361103021110713024686000e1002030601d00741508810b400c52014030340040c0c40400e464401c00f640d041500108001071210006001840c0c0048541c0e01074190307800c0465158254518138450f40c0700040c0342c032502984802c002007411808806a9090782518802c0c1e80024051150000094115400030100441007100e80006e803a010702c986809141c0201c0900079880c1808001da07a1072036401d01c003004000f06a0740020700900203000d5058401c1c28040619550340d034a0800610384000310085a910141d06001d012001c026000032082d19002070800e06440148140001e0030343c020214030542100d008110422400e10503501c49042e80e1031603200700125614070314185400e002e40c1c94000c0040c3e12443c10350500b03103445001000ea06600800104802c0706040129200c1107000d10440090303401810705008100381880014900c60400204429291070904020740c2da04c500f0541c170840c42c0d0b0016036107103164032641002c07025040420002080e00109 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 420885809 1250 420884559 420884573
    0x1c44071505151005040308070c0b0406050403020301050a0209030a1113020a02060103120206130b0603010b040f1a0907021f0f020301030813061b080a020a0210030207020a0506071a10080a 82
    0x2140c0082c403100810001c90309500d0a0481c14641c120031341e039424201411982d800140360311180d01907650001864000480e00407207402000074001a030380b1941c41d41d2070342c4149800d4803001380201c1070a40c0184004443c42e06d00007202569aa00003514802c200104408628084004110301c14254000580300c0e90a030340000c0c265049a100d0b9155881c0c113030200c2012a22903c00395042c0440c61015800c01001c1071290607401d4004c5001000051071074a0340f0005000ca900c2c00301305071100c2e62181480340003000d4209511489031011303142c3c81903d02d88024000e4071403075800f030360701003040031260320b550300c10b142e64031240d84200008011035695131241030041c441e801c410340e50a140300c00d40d480407400e540f20306126a500f000320024584c0030f2480ba0f8800c41550048a120320440c81420b43c040050b03918081c030320340b5002d500e4038010f98035041e0303005100501465400c00c5014200800a1000184105038200c41c5141d071055000e1039030715050b402c44211001a0301012a5200d0040340310300340700c09 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 420887059 1250 420885809 420885811
    0x80711100b1212191106040b061e010516050a120903050f011505010c0302010f060e011d010e0408031e070801060e03010b0a031407051c44071505 64
    0x1111900800300035259215690a8070540d68030003203c0c24003c001c07845818002c3c0b245124901d0404d08041441c04c0e20152a00204039025141c00d0300c004240030707460070050304100304c403448982601003440310000003074880d01c035031800d0515801140a91000f4840c00740412190944d03c40c0195403002c0b885040240303111260301060f0740c0d50107001c030b068425010520030100340f0a0841c078206108d5207001d006596034241401c054007035548884031103062140b41e114074800303440310095028407541840d00c445001914076052800c2c4940c404014031400c001c0d0b842c0c2e42d50060b88000e480d43c0c0c030342d1400030511103031030802c50760507a8225040c14020701c10380104a182c140d420580d40c01e038a5451100400d800e940c030815035260012a860302c00e1010607520a951010000240112844d0641e11380100d00070240c003240c01d15428030344401980402c046400c0d400d4120881104028054035031402d106a8101c0e80d2880d24601c5a0380c49000103400051000d40c0c480d9600080c0c0440c5040c0c03400840030103024 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 420888309 1250 420887059 420887081
    0x70b0a12022d0c0a2303030f010f120c0902070f02121b0a0e06040c110a0f0b01050d02010816121d210a0e04020705030f1c02070b0708071110 62
    0x740800a038410b801c0d280c06a5211040040092490403925211000007040640081483e510708084000400a00304015402460923588040b802d602d0002030f010f1030501600301031001410030201ca4003140d01000405d054481174040181da80e02c4d60316100203410017000c4000d40fc540750b100030441504001c03a80c1030041d1480210a00c1040a42d400c00140000e640035030381040d80186d000c65060b017020762180301710451505126000d41000b0165515000c61801c0458404040007203a00400000c0741c0d61500502d030580d58102c9200813a400030380174560003840950b50309a01c0c40300403400d610480d0032065801c00314504007c2e41e80d1a524a000712020410001014441e00b100b04480190310004210030080210720301e404d000922034120340505d0311044082e8040e8017440081c0100c2d0051004048010101c4241b650720444441d001a003122051602c1100310301c140551800315140381e207060b070f00c0b10390781c58902d0095540741c005071601d0340003207150117192040c85240d00701820725502060202c1 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 420889559 1250 420888309 420888367
    0x1062607120f06052d090c0a0f0303031b0c02130207020d0602070b07022a010c141608010605030307030c23030c0c0411090103090302070b070c0911090102070b0a1202 73
    0x140c1e4450341081d00381c00f0207031955039080740c1440c903980c64203c45c050030390440016000c0d1907014218070000f0f1200036503500945480e2628003802c00c2010f4151180c82c3c1d40d0840c00c207040420480250000e090090840c0b0302901450b440c14903100c804509078101ca070100e81c0101414a0504d490074194000c0d003141300c0803501003c0c0c281c007040d0003d00006180591400ca030f40d60a02c0ca00f000d110702d031101d404802d03080341401041c60a610000350413222050455041000905500005402e40c0ca41100d070740d40000000c2c0d03d801000e114684000c002c03548003642504219156540514001c8090000d4180040d00d4660b4204130700c19405e40440140f44580c0b005080380c00001d084003c01c0210b41c600c2400181d01002003122519a5020340c001d40400c6002c0d00640c0ca105680700c511800a91000c1000ca80345108200184507a000303620910800c581c070b00f4981410001d4500020b5569091801512010000070954000ca60300c5098000d0f882405902d0070754684191181850003020344485000d102 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 420890809 1250 420889559 420889561
    0x305030a09050f061606020c0a0507080a061d060f04140a03020d09140a051309051204080607091805250203090301050f04150b06071e0302060901062607120f0605 71
    0x143c5808025100c07204080030451781c8460490b903a02c4000c1d070000b84110000c0c0241c000050126a05000e0b132001003407400094010884c0e1407800004540f0b5200c81801140304012185d590104000350265008404180d0000e068030707a41440994070311240c1e0f00d40098810310307407610105507001c02c0c1031080c0c50080d03c41d041302a8035084440070020480721079036041103220504000c0b030314040410466485404200003401243c1e91655428461207403105081e281c00020200001c9030100145948903005d458814101030800002404480099104e03148081d110400703d1072800002c154200201c44e9190410704142d0040000303500c80d044400818807a5203001e001609004d40c0c0800d162040c0d50040801d01c000c082240c1c9200107000002519400c10f0040c44404002800c10310f0b040012140c04071000325104035480c000b4640400105129501e904001c810004500403142203048818142002c100880c14481d50515021855014013082d6201043c61014441c4010400b030700180107007802d200c5 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 420892059 1250 420890809 420890839
    0x320040606390204050c07150501181a031903020c0409081e0f0412050105070f020c0f03100204030b0610050c1f0b03010c030c02012304030c0201090305030a0905 71
    0x35a0002c41c620440401440c006160800c1c41400100250306410070050009555500800d04590040300d600c1003c1d00001000c0c401e000d0303026041a60018090010700203076040011000c000a0b080200d81c01c82ca441c0c10240c8030290542c031111401440103011200003000e017070034611081d80110f4041e13015000705a0125924101402807a50350364000e00c880d07142800500342003800c0c40d4004010700d4291800d102040003202100018401844403511914228200e41000d500b1108080c3c1501c00384124030320140d00e980d401056655103001e08845007030314030b84020007180c01c007260450110b040302d100290200411000c814203034020001901e0140900b640384d442500c6030310607026504440e51009d8100392440919892030010208050400300324803d00c440403900395551480a400425140d0b03003c1508140d0900c0340c20190f522016002c5000d001540c413150300210b0141c030180c10081040b00d00829a40109409001154400216680c071400144014450b20081c040e151155a0200794441 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 420893309 1250 420892059 420892067
    0x9030e012303010611100c02010c260a0b030c030f06090c09010602100b0409141c03021e030a02070b010e0105240d20040602030405090c0301060f0c0c0320040606 71
    0x250448242401d501e180d003003c9003135039000c24070744203580035102e08800c5040c10324181c010b01500d80055000802c3c05506a58090308001200e800380409085c0e084900b50441e007440211500702e0307583d10b0300083c55400e04001c01e0503d508603541d00c0d01486a140041d0484000080d610711070a401e409944000550408206c0c0140080c070a90005a0140401005c181008e0340202e0425074000d00000740a0317020303518403042c54a5450f44440d140c00c0801e010502c04440c0381f20540320b8420345001c62400c070aa08038401d51442400c2400398000300031002480148190341110445034104180158540e0f4840005035007107400d0041a020f46041c00c00001400709064000c0c1e260440359000504040025100c40c0040001000e45482c074150003072545401c071004402480a0a1a0782c007850f07a5504010a000d80c5d43c40160044044260030401005800d502c40c034907102146592600e40703e000c4460401c001c09905a82020f030030890038900c2c2942c1c203c0303c400b8075141e800f000c5e0ba040c401c2903542c030070943d = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 420894559 1250 420893309 420893357
    0x1060302010f030507021e01091103060c120405150c1306212408070e06030f060606030712020f0a02010b120c060703051905092806030b0d0609030e01 66
    0x74041031800d4211070800740a81c10941d403007102071040314071074800901000c070440c0064005030001c2e5581c0545400b4010311a00c21360205006a000705800d0501544580452156030381c0c240e0300c20a514007040800070144220300c1034228081c01c09185040468244415600804010034464180b0701d00241d910302030034000700785002103403125280c0d101c00480200905886110300383ca00c00071000c5145483c00310400400070700050f03401070521038200252072610b1034010717241a22980c0400050512801c000904580c403010603100c045d2a5100d00a05485882c24014040e01260003c1085983c110050001d48404507443e4000d001c45030031041841481d040ca05a9000230781c11040a000f101c1c109800148400303403007071505510305151601d10040f002c05500324940086e4001418260902e010441e0005188185044000004010b030340c1c4283d02d04c2c40c1c4900000d0640351911056031b9070382d04031444861030f002142071003040d44501d001008145982c00f0540828506040080b180d4800c40d080b03 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 420895809 1250 420894559 420894563
    0x30509030115291e090d0b0a0c020f0d18030c0303050306090705071a0c0d06030b01141f0c030504030b04050a0c0b070f140304170d140a0e0f04060f12060e010603 71
    0x2c0e21380b440b45607245240e07100d0f5402c0910079203400c0008802644560356000e146602440d50910181000d01d001c40940f148075811004540c403115180d41e5081000c12403007400c904504019901000003940d510500100c0d90002c2d207501c2d280000082410380200080d40304040881f841c14460b540d43d034060320a4003d00801801001c9035941c0f0440400e41500c0b90390304144e00c10f441a04014044440d03900340d40054000720703054840c041c01080310640070b40038842035640407039418580801c00310039402000030072007541c400c02c40d4801c0d5001c28540124101c1d009507420010f0b522040c8bd040c1003695550400d050111282071900034000303a0023a4840c140d6001a90026841d9030903410f50b01d40000649003200140405c1c0020440000c5442d01c1440152090030030801401340d12043d55406089660785019a81c20140204102800725a001c0303405030400340211a030080c60140c2901140041c01c203031b0042003e09020080210324448242d04000c03145202e0141417111402180c1e00d03500740e0b2014400 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 420897059 1250 420895809 420895889
    0x20120f161209110a081b0631052107060f0203040b1b0d0f0807020a0b0c221403010e0714130207050a030509010e0a0e0112030509030115 60
    0x110300951061500000001030203514801e0483c42c07460f0004010000c0c9610043d481d6004031a10404102c2c11500b42c01c160a0441d00a03042c1451240301484c0c0c8540c041e9100380d195401e0101510405100c00382401801c40908540c04440c145032044441ea4505050001c0030b02c60107000207a140c1c403650142180321990b501550a01d460b00c19414450380201c0b03100071490600442c61400717020b0411080d60116190355618040d801084400f60407800d010f0102e004541000c0040b80c04111000001074020790590306a0369114003c04c60300780722142d044844d04581440000006074a0820321291164000843c02000100d09050b030159841115219003c00403420f903044a246242c01c1c1c1c100f50904105101c054a054000d40c4c400f4188441005c04401245c0f02240c0d1103201d5034020112040503070141c0c0d00c6940c4d07030b091601c03070703402044148120780c2c200304416074a00c10903100300c0c262680004050000c0c001800c050f85c0449800400b8000c1084841c0441d180281c9480f000304100703100403003c05 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 420898309 1250 420897059 420897077
    0x40201050a050a050912060f070323040f051006051908060c03041b0605070c05090f04080d02070b10150206070e040c0c0803040c080607140d20120f16 66
    0x200580d41c60f04007150102c14484184641d1203d5104c11664009038100c04000c0c101c10302d071900c0140340da010301419400c201840e00700d94041c0056003041c0c41ca50200c40d1201000a99964074081d498041c1d00303900102036026160a0406505c0c2035044038059600803180302c00d8452800c040f48030b40b14054031070010303107910a502280e404595400210341160151400c001c105040107219240e0102541c404400504002141800e00944035100c02c045e201c2140c010b2444e04040d50002c0d0306007400742003e414081c0000c0c000900711f1403541111a001e0740700d801c0d42c90a140510104401d03a185100e500d1800040449186080f8030100c1e09600c54462626150310000851003030200034181100c82009100d001641745001c140d0301409184214451a280340c00b560030302c0307409070400c50081d00600034803404101c0400c200154405503040b18004000008480a07000f0f480d000f40c84104030001d0071000c0014000c610745141c3c031046071181500c10000350081d180c01a1080103440d0b03900b10740001918100e = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 420899559 1250 420898309 420898327
    0xb03060121080c0601180c05030721060b0c010e210307021014040c09020307051606090204020a0f0f02070b03060d050106051905030111070f1403070b04080703031404020105 76
    0x80300c01c900740031003908604114405075940d01515486011032240d50380c040302c0100a600010707000d205081a8000003408400c0b0104400b034400c2c000a041101444005075a07540b000002c40080c0c5071480440d01c1c1807020681d10a044050340d4004840030495500b00b5000c605400c40000300410690075401e02100f1076000c01c010f001d030a8201800078803c500600a0031880404980140082002c200716000481d0038285021801d0300c440d5442040320600600400410710b800c40e055400e04400480f095142c07001c5444c282000705503c1c5002544544040b80f45198203600c200e200c4c1c0010000c6d1241c520f40c02500f90b090780c3d14020307072080c2002c81c00308200146030750608801d180c04c814030500001c19800c0d154000202100500e6080982240700801c007000700389401d024001c17080c08602803052601c1025151800b528800c0c084c09044610b01c294003540c800d0080044608458101105130180d0505213003000d95603120500550000f410007040c40441c0403546141d41c0116070503147d00b443c050400d = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 420900809 1250 420899559 420899579
    0x6030b04021603050a110109061a010807020d0e0301090b070f080c090d140102191214191515031b02030a120b150301080f0105130f0318180501180b030601 68
    0x3c0048401000b81d0007032008881e82c1b090084c2030b0345a00c6040c001c20003014681091802c0300100f59840e040200c00024001015008580500d0b07401042c83c26a07108050390010902402c1c0b00358005140d0710846003007118a07a803000d803820b1861556078a0078815128604003031107500880c40c286078400e415240da50006030341d6580c148021074400d0b0000d800c0c0100076a4200e204001c4801c50740c08521300100803140d502071817050551000000f040141141440b02e01e001140205210320f551295585860700755080300320641400800d9920801c140d9007140e024000c004d8059400c90342550106480ca09040da80040282c4c0d80d080c0b06130f5195071144591211b4100035144d2910003507003004008102c6104166004025806411614002c00000504820170350840d14014408001c0b8100d28165000161901400b4042241c00d407074040101801050f0000d440d0f0b9213030313100031030a45204902100040d60381d040a0704a90b6011008503194900407140c1054030007040406a03d500800010b220141325 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 420902059 1250 420900809 420900817
    0xc0111180f0103061707090506010207081e03070804120314040b09010e06040b07030c11040b0a03060e0102040f030f151107080309030c0f060f070e0604090f0e011506030b0402160305 80
    0x14903004c99060355507503104600240030802d0b21604d801568041c0a21b02c4507020b1140c00140030b1004012140c0761a00c02912016070075110168081201d5419030300400805c151803402e0b0b00100343c1c43d40c5550703d0b10b01c0c8680301e80180d0201c01140758130485407101c40c4603c1c16141191100c08405240c82000c8004480700103109655a62000c410701c000304800c0030500113000035520a0b1101401d540550030582e00c0507050b040c515225034240080b511180e12103071703200d1084076400b0101003000c041c90203e0902a000d96001699a000390010000500040a00e1560414080c400d45403a1010103800c2074280caa400c011440304101c20441c0d480002c800c2c000856200b0195420345e810700244d8405282071440c4ca0b10a0703e0746910200a0103520241c000c4e0706c075002300d2241494440c0401420104a0300c1c00b0314402c0d105155a200e2403101c01030081d03080381d02d64503a0791008103d503d6520203942c10f020304c13038041d06001030b14000841071503003001c1c030031120050710900700c511280d0000c0d0303003c1b586940 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 420903309 1250 420902059 420902089
    0x13171b01080a1e06050f0f0102070e04031734050405190806010905010519030b0c0304050a020d060f0c0503041e020d0b01031110020c010f08070e060f0c011118 70
    0x540d400d8505010448081c1c40743c24003614581c04100f040c07a04040144503220480704a12a1500c1c02501c112613070002842d0007260519011220706507510700742603402246011313603c0203954a1000304121064101c010940d91169500805400145260300149446130b28003c14081380080000b4012460050809103820a83c0740020100d182c0715624503080c040e080e1b100c5003843d070315240140304a1500e44d0800440b031f400051642e0342d00f40365441d4482400d01c064082d0300740b42000404102401002d00c16540d9498010700221080e80141c40e1044c0281040d015060180313184c81000311003a885042228040d0350404544581c00503801d031080328078240c0c00d8049903c100420600030000c0d8207100007a000798010700b05164100e080c0e505002d18940341c0a010710440d0040b0100d0055a80c00140e6540d04040518080c070300c03680d0300308060300c403a80c204905c030380d210700e0102b9040ca034100c1100081c820504910000c0c005101034405001e100c2c01580010741d00d14201c040003441a090070030001c0743d441 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 420904559 1250 420903309 420903311
    0x5070809060f130c0b0403230a02090402060c0a030e03010515030715020102130f0515071e02010203041a03090c09010609090e030d060306020904111602040f1113171b01080a 76
    0x801541c2d00c81d00c4004c1c06170700c807403800b074804141002400b40c14580c10891801a001d503110010424441584641c0865402407040d5419404601507458040580d40380104030022140340301171509000e0003101511355028800d600740340c001158052084040000b80300c0180040940c181404042c10500701a00317000d400b10341d800d001c440712426000c0d5412008000511850140a00f07010174030900110507184038040ca81c08205800001d05070113400c1c6008800c0741d0500e8000314840c80100d0552007958860141d49001c4000d50180040442c000c40c040c01a203030807611035040f054107020b1070f40340906c40c2501250707180b0400c1080c0c1d0400e8000984210980c0190ba02c3c20070880354403800c9914607041550712560102e0140780f9806c041c800c0861446aa98059051240d1501080881c1c00c1d542070003030089448540703c070501001600110000c1c81e810345c200d0785a05040031816610500b030712503420031030145012481d0780a000700e6003c62140400000e594808403030001955400f00140410980c1 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 420905809 1250 420904559 420904591
    0x10213051f03270807060606050a0e100c0524010801050714160c0f0e09010504150b0f0909030327031e0d090c05030708010b0303070b061c031205070809060f 69
    0x2400d05022001c2c2c1080c13003a580c0700c0d214082c90800b402101c126412031800e001c030030050501050f81042c500039070800212030030340030121507040407904000b80c4880100b4030701c25000e5050856a00006803801e20030701c1c1c09180010303a03a5000380c50030398005440032808180b050f507081c2a4021000000e09210030441188581c24003d40d61b06000c440d803940c0081070300100440d05102e50b1070300501d09070b00110988020312160420741c9400840f008107110202095607a40303040503080c0c6990b440c00d155850001c000340708510300800c0316500c80e40704448504620700c0c0321354500c182c48074141035014941c070300700011401e00805e07006010b0b0842400c15040103492042c058200b0b0700030a80100400c8030f00ca03000400e031603840c00d010f05140035a01d40040d40716074103191580c44c0544000064540031500140306140d5521a440841c0030210b41d5508442d100d055440359000b40754000061012540c8030030010001595000000c8030411001e4a8200c0c1a400c90710100d014500380e052004d4110365003076100c0d60b503 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 420907059 1250 420905809 420905861
    0x2c01050108041b0905040201092c07140412050c10050d09060905030a020a0c06110615120d05130609030b0f2d090c0102060c030a0c12060602010213051f03 68
    0x65182ea541c449003140e45c45004220031075074410320000c000e12910303004480c6007a05415903540a03000000d0099031380d01c024001151540b0940c0c0e4003200004044200b03581d540c0b9045003074440c007001a401e132518480c81521503400c1c1060b00b00a030114500b9981d040c1021150909900940141075090703800742d49816441021880500c001d204140e041d4004001101a43c0360044407503286520003024007440605451171f030000070030702551001010700140f034005464000615042c9050700c0b4a00184034004c450304845800400034511000c2d191120b501032540d40c40c0888991100c1d00000307001888490100340350f034400060440d044000754010390015414103c02804120184504404200c108014005801424080070f4000d6900b803002e030403d46011108840d00d403101a100e900310780c0e551441514103170310412440b020040b08482c05d0001d02d40c1d40100074080d4001e008001e011b125040c900140601e842202c03d405028115503410002c01200c10a170300800d0301e0080500c0c2d0301900350407151 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 420908309 1250 420907059 420907103
    0x51603270f0317091819020c0c010c0203240103030e040203100308181203041a07050606010c030e06040b03180a020109060e0609030703030201021c06030b1b070b0c042c0105010804 79
    0x20f0800044c0c130400b1886c54401002ca5190008401d0b0740d05251040003408800140400d21601d10002030034104011000341c40400e28001e4602d0252030b0392074180c040e1901292040460a04807802555181142c80c0c904040004034030003502d014402c51001c140402c0045ca40c01e010f000400240d41d0103100400540c00404d41760314070403503111810b400018084c01a640c544110017400c0c0320500700b050a1005507520341c1d81c2d80b00054592030500200410309000c051040700005c40b4820060315460304c0c0d0340c3e0350034a23010039001500d094584104580306074080ca0340009801c0c0405405070350301500c45190540a80d500c41c80c011941d90082c5c820000d445044e00c0400019000307503c44c0c2d000603a10301c4041500e0890368155007800309003900303041040001c51811070980780c01941034811008005031200d0002018865441e00411154130001000341004480c8042c1045685403a9099028900703101d1051303011005101560b9190039105c01030056510400103036500c503100e20324800442419080d000b03 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 420909559 1250 420908309 420908329
    0x30423030604050304080f07030206040506032d0708090a030c060e0309030a0b0703050f04050703110d02040f0e0d26070c02060d0501140f0906010f051603270f031709 73
    0x3440c0b84e400010200130100081080001c107072002806000d80b2030a43e400280d85228600c903162140b0404000314181070003001340c5000f04e03400c00c51031140742e0300b068620600004084400c1c0300842c1d101c4000a251407000308102c0c034941d5155451304080807099480758024002044059032a10080c8410192910f0400891500c180a5084c400d0a460710440003070559070000c2032140301d10310310300c00e010018000045100071b03240d000749048101d030034100200d81c00c0d03a400e0310040d51090515141066503145035014401c200e4200701030315034a108040041c0d40c9201120442e90a004040711080ea002c1860402d554110160345410500f05240741c00190982d00b16a480f840750396660001046404007281040010600540d1224000c891200000d080544000c00007810701400d550000402031081d42142c411240c07513180262094018240280401d50302c508010661070000b01525039074004109845c121018040c021520700c1c15540d0b1004408000034140080402c2130088800d1590b0302d02d900 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 420910809 1250 420909559 420909563
    0x30b1305160305011a0301061a0c0a0b0114041a0120122701031107080a2c040b040605030705150f032508070813021903060b010801080105010602030423030604 70
    0x708222440c0d0101703007a01e2100c007a829100342c0c50400c007040b5021080b040030701401c51203540c042d02c601c00080e01c0360401c1217902008120100c000300200d003010382c1e610b2541c45544c06403000c002402c1c2e05d4000c1d01404070402821030100b01c8100d5040758003440095110700301604601507070907002c21901d6031211900203103805041010030b4207103240c0c08280c0c5040c06900300b0003460240040000031102407101c0c414a04090446180000c00c1244039010b0300f4840c4040500070b090181854000305405940a003281d007003840740313041513404c0c485440d190141e4411b44030010040e001d064900410070442e0406003551802c400e00c00e00064860000c813030050361240c400002603156844004410344101c16081d20000306104220341480032459004030303500e030300603041749958400c0862400040e082d1f024404043c0448015604003008010740da8014500d0b00f002a00ca1034001c1e40c8403010307075090342c0c024040c8000607481440200803148034403070b0b090b0340300104a202020050700e503404079090100403202 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 420912059 1250 420910809 420910811
    0x30304080403021f0f0e031f0506031005100b0901120203010f03020108010905040309060f05040503120901090b070b0c03060f03010e0c1207180f270b10030b130516030501 75
    0xc20000e40c10850740f610350b1664101d5414134079403510400a84102030341000401000b9a542c4042c0300c036201000121100e01d5102c009031600c9800350000d202511085416501900a50780c41c1401e08480d4062507003d021403070740c40040c1d2030170003910101c0741c1c100948050401610030500c0b1202a0b26100942c0603000840500e0a45801c50002406200c01a0300440d0309910300410000460340c491400c00565546203040014a40002700403905130180b9040581e01d4000c924200b103006103074500070221044280c8409070300d0340d039a04004209001300300000d441d80d86410000344030b40720840019640000020300c00400703580342d50042801c441018000505590145907031500ba85400c10020b80f0030320315080108059410442d80c085440c440d035444060385074036091810300b100309640049102812441c900e0621009480410740c1500b0070000c1500c9400b12280443da003004a00100410340760030200003980b40d1656500381503038048804041d0389a00030140d400c2c00c0001a02c094500540c02500 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 420913309 1250 420912059 420912067
    0x11030f09010c0804050a02040911040c02031e0403020109090c14070503030601021501050f0f131401061d0a06180305031c390324060e010905090118020c03030408 71
    0x210031801c4801e0480300302d003845610401c02000600001d0300030750107a410342c1e005c5010002440d00c00b0000d240032460075481800d01c2c4d001c1c24a5a8008040c1070082c1c205000f02011900c44015119640304a0001a001818150051150001030b0300011032285440c5003003d2480d18920003850a504036200890b481d810010500a9669041013080107041c0ca41011100c1035240c100061561058241800e002d0003503950020140d950703040310440c00c40038401c0c090080291700c0000b441c2d003134000d009141c08910422603403011065454036440c075140018152003040c5040800c15654500e82c2e003030740d0421520858020000942c284080e10f20b0744503000029000a541d440300c1d44c180e4240003100040041000c0e119205094004c4801c0c0380c4201298a44404d10100c4400b00c1c00340083d06602c1c140580c516501008284410109504499441c2d0310800b501c40240011980c048461007419405400240180044044200030b420b16207001c03100107213800c021403002c600b550002c450503150a90085 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 420914559 1250 420913309 420913321
    0x403031205060916030e0c03070e06010f09140904060213090c0905041a040203060a080d0503070908150402060f0702040501090207110d0f0b0703061706090d020304051e010311030f 79
    0x301516800500c111940d4919181294600d2244011102e110f030030140c1b18038807a40442414031a01415040240544080341e885031303100f5000301000c0c0c2d10f580c00110104026018075105a0404080d00c20340e56000106030080000c00010714005081606c00340c0d800c000d06408010300b01103500c0204150040498805420307140502200003e034400d42c015400c00a408003600c410402c0030440b16001c1750016180d0312460041910a0015085402c4c070740b10344904034040035001805503100b4502030b56104101600d4000460b2034201580c0035404607401880410b005103032441c05000642c6981c8411801e280403500020b003600c00c203030b01c1200b503264005424014060210030f52203c1c00c00503540c40101c220f40e99203039009044441405042d004048011900131741c031a400c1940208803240c0b6041002c000c1e942469103e0f00140d5a0310018403c00860a248600103c02d43d4102e940c000c240b44112581403600b019954030807081c403810103603140240c91421802c240079600400c17040503585403500d021 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 420915809 1250 420914559 420914561
    0xb01051908060a081504021302090306090a0605160c033504120e030303190204050607080a0305100f0b070c08010e160e04020906060a0e0306090a031b08250804030312 73
    0x140c02510490f04080ea4a1002c082c041711401d40043d8107a810308103e0782003064010090045114280c0d042c0603103001d008108100080611616028400400c0710740c503801c4c0002c000c540021407041c00700700214861408a4000c0d1308c0b14881891f00d03400b2990030b0190a2118801e81204101380802842c20824003060090581c0c10020380103282c2080720740a111400003a56078000182690940c0c00d2180600c0d031405c003103030107440042002924264450000f81350014240e0859050440000d04d8080012420b07c0e46c007070100304507051160410040c034100201c40640303600100381540c50b20103c840000b5017000c01d100380c40f00001100054210780c8944407910840d038009602207414400c0c800c05100144e23880d003a0944e08044210385480d0350b012101030a494118501c41d41d1641801500100088100007003400e0100340e101307076180d60001065803140c61400b80e24200140040c181401608501404503524800303180f02600c44c695100c003a5912000c3d1a80b05400031400520f6404042c4048505 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 420917059 1250 420915809 420915829
    0x40c1e110f0f07150207090204090903030f060b0301120309030f080309070b03060a0b0703170720030c0c040518030f0a0e040504020d0809060706050c03010e1e0a0b0105190806 77
    0xc01d5002c1e000c0440d00c80398003543c0350103c0c0610241d5403040000000628020801000105036000702517454903036a01814006080c099030681c0441d040014030b840080d1640302e58400e840320101c1d6941503900748211015034130750340d00040301801200840803010540600245085074411400b4a68a29091b4405410044581d0001104e860f061003441f40c42c0e60366120f05802e0710b400d440701c00d0311201c05050444001c00d60b00420f1760381d220f42ca02840741c41c3d64869100c01a06d03480c0001d0300400040c201c401c075035134803e02c000c0c174015811468900440d80f030701390400d0790007041d110724520b55110140949820756001c04801d05080a0014412104076000080100c240b481241c0410a40c50030343c010036401d2000354001091060009056856a551602a540d8281d0400000c0025103040d00c40400d45a000707028581011100c2000201508100f10744491400000e65640000c1e40300da00310400600725825059050041c10300680140d4060542c0120010314565240c90183c1002d0003070065840c4 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 420918309 1250 420917059 420917083
    0x90307031103130330180515031308120a090209100503030a2d0504090b060a0c11041b27080a08090604080a031e1b02040c1e11 56
    0x410b0208000768103156100d20122600814460980c07100705a1700864550001451401c2d8550040a00e45455100c00f03150842d078060b0811100c0c042d02c036000c00510000030185882040010000a640e00c074042d030070320540034071503a1842d080400410010310442e1049811a03103840e034402d40300d010b514295540c590440c03800709140810341d04120209489200d40c805542c01d1006190044611002e8003100d44800107da1f900c0c8080807a120070018400d03071061154420581c2001c07c0c050682c84c0441c00c88101c41825151340721064203030ba444071003001c14000c2540d84265a0700203456031031000d80500200220981c0e03a18061200c503807030207000c545c8d0451a56040f503585007042c411603000050340700300e09820140d00ba40340c102e01c1c800248284200c0e086a403040c002d002500381050f0300107629503089480481451810150200c00f00c0700003a80c2151074030140440704164016080540c00034000e030a03203184c612501c40c040ca100d22080090b205010000078001c070740f44c0c65404814444107108039 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 420919559 1250 420918309 420918313
    0x50f152d04112106180f1e0c09010914060702011409090414060a0e061f0305070603090312090f0209041b14101803170417010609050c0703020a0b0606120903070311 72
    0x201c40007849100307100700a12544110f100c86d80841c010b0008440001104401084840c0c024a000e0341070302c00c25004903050b00e001c21030360500801d54201825030010040300142ca80d034109a000e4004442c41c2e0341c0b800c050380700c07010204800c2c3c101d034680c512001d1141e40145114500503a00750320182c600000140460465450880e5040d541800822826044140030724056158a01c1075070000c0000113542c402031961180781c800140140c2c042c0c10114030140a601d401100340003040c1102d0980320402401001490b460700c00c1030041c42c01400b01781e000381c010f80c0c041d001c03004000ac10146001d4160031650f0070029000d01d50181d880e00c141c60f40001a070500e8071a0800d09101440700c0c2c501e00e18000108017240b64102400c0d00760300c1d041603500034a84041404464400d440c11980242640d000e281c202909002c0024030031900c103400ca404180e4194001c00c110100340c1c6508948480180c00b090b0700031402c20280000002440400e40604507172805940e50303400034580540f114015043e003020903 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 420920809 1250 420919559 420919579
    0xb0a05100207061110020c010b03010c0c0317040309090203180d0e090406050a0207080f0d1515140405040c0504080c0f09040303021606050f152d04112106 68
    0x80354003003201803ca030742500f858071a42e00c410082c903043c0400c0034088515144003084d10b60f0303041c1054000130003903d070907002040804025981241c511540c85000b501140a0810b441c403c407812b2000b642c2d1143c02031800c4080d040d01da08840c0c0a9030b00c103036500101240e000e072416001c9031061104005500039410440301307244251000c1009260010000742c4010383e6200000c074100c14a40480f04d40b1f0780c0c8100d20300c2e521100301c80c0031501c2d0b80088a10031000c61410170781c00030340c041d44030825060360794052031101c20401200301207d24103882400403c84d140180000115903c50f405446041d50285c1c9519481c0c40c2002c0d840d80c40c3c03d01c6801e08a210b40b20420700c001064542c1d42a8903003094241c6000350351520320a6550308603418880300103200303601e01400c100c1501b6040324858007075221000c0382c85581030103804100c56000158613102400b901204455022b0080100783c20007032070041c0000c1100c034100f1454540b160044001d845c2c00440984901801c104407082240e8010701c110749003419 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 420922059 1250 420920809 420920839
    0xc1517180c1210050709080c0f060702040203040c03241104030f120c20040e0d0203041e0302060c06190908070204050a1d03040815090c100917010b0a05 67
    0x141e0308104144500444a01c01c0c5601000802d0107004040400d0034814801420881001407460380288203500c2540510b10740300b0f2041c50103002c8001c50250007000c0c14200b01081c2c0800c0002d6102401c1101d45000301c80700080003800c214000b000400c10090030318403d400982c1d40741d041d10001c2140c1160301034200700900c00903042d0848005003c2c0c000051a2190100880030b55044001c0b15002d0011000300c0c5120b02c2503a250000c0c2c62480200341d03000d1100c04c0e88002910780c2d400304103e0ba5800340c0c20a00050040240c40c901e010b01c03d808561082040da030fa00d80200b81c59900c030f410307032210707a42203003042100c00000c0a443c004240c40d600c2040000c044e050301d41692900942c08024803c940380c0010810040903030b042031140f9070300000212042d003c815580c0d9500d500501c1340e02b50b079000306d40080f079000381c0c1090041d218074040409445100f25480c1006144c490342039408042c00308810000c1035000081c0c0c00b03d020082c0070390001484070104c0041201c94074040d07110078440d10880c542080 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 420923309 1250 420922059 420922063
    0x506010306090e0a06091403041e08011514010903020418020406060513150509040e0a030f03021312050f0615030618031e1606050612030304020303070f0c151718 71
    0x25013640000002400352103914200c2e0490941c40d00d03502d800d100100700441c5030310800e58000c440d54010905403c2c2c5941d220001402c0e01c1c0100d600c40c115401d0201d0401003050007a0440b0107468052400358050b91301d0341e00040487c0d41c20b0f601081a6404007402104504091041d4000703801103003401400e1a40780020340e25104100c2c010b980060503520b81d000d031520300541c141c0f00700180040080c801b0000140d002503403040e02640c00d0740012040841094110700138400c9031117a140c4107080c040d0039404c04040300c0005800250441d42c0e44240d603008103901d24117200450052101320b6819400549000c2011301e0080080c000301c00012000030200002c0c800002100c9480d60300d10b400c8819030503080010481d034050420904102e59405030365000700034603a03105602c1900304032103030311040d00d1611680d90b0340c0c082258001e41580c0100480c002041c02c10450b030040b00c0c45184000030554032a1201203121824041c1e080105851581c41e280d8034001103403607a4012510359040d9410100310f40119 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 420924559 1250 420923309 420923323
    0x309030b1003081803150f0426040b0c0c0d050d020105090610170705040518011d190c0b040e0103060b09071e14040f1a0f07080f0c010f0506010306090e 67
    0x2218450b40103c0d52081da84041c04064804002040440031510340101c403007c0381d080440b003c85e0345006040e8209034110140c0080103c10b071400720380300d0819040400c101025401a0314406041c86000c0440a0f990784400602000901c074101030210520b03403038800390035103101a184600c81c3e040441008020540c03d81900704442085824629009504100d142030101c5031b0041070308682020100b294094543d80c01103103882e044c0d002002140c5100f9107541e07000c030b98502c103503e0541003c4108a03502d01d4040407018000e018280500a050340c40b07421403160f9000d50300540003001e43c00e0041060106c64441e2540d281c000343e45001c1a03250504005040c241d29810f0301c0d099480d040d02988076a03100c1c20740140c021484040c0310780e52315280d04980c0f074031101900c03c88401e0050402d0420780c00304e0900a5a0030507940b8060b03642010700658038804036404c440c0512800720800c0c41074081f079483c240200f200118024100281c0d60801c2d031300040648032580c120021090a15034041843d81000a0031 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 420925809 1250 420924559 420924577
    0x601090506010c0f150504050303011e030f0311101a1c1110030e030c1b150301060806011e0906080c091503130c08060601022107020f0312070309030b100308 69
    0x801300304162490685000d40c2416080801c46103441e040004001c00000154143c0308000c0e03800800805241d0202d403408810f00000f40500c0045505030300081c01556038807514601d040513a01c00c40300d8a8520000c64080700859032224003e03146000c107a050130750081c0b504c00107141001200303642c2c0c1d4603404528090340300c515015280c1e82d40001c500c0b5100b5031105030307240071003800d481d80c5258846000d903403004c84c00c40040b141403203620321082c64035240c0310791185d4021118034141141e01c2c0100550b01c50318010b0065051001007001d40c801d882e4185100c00c00001c45e511451640f60500c00020501d040c0101402c0d2403030b03404c012686843e66203508940810101d480d4056036907907802d120100b9030030485001002401080c002003a951310208205103c0c05080e800c40e4400d040e46c101800d80c45980450a03003010342d08220110140c20605400054040040d04556190009a01e0625241c4c800482074000940c1448240100301c03607113400c160003482804099080782e0654903242c10b103110318811 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 420927059 1250 420925809 420925823
    0x8120a020405060a08040201050915070c0b1201030f02150a0315170c040f0209090403050a02010b06070b0f06011e02011515052a0618150f070c080408120403050601090506010c 77
    0x46d045a200c0d070100c2e03c4107035005d401c0000403550114800100e402299084411000200c1c001c90404000c03000d807000e00380e50310b11a505c0d40e403954880c44100c0040040c1641c021f08980c800840d5040c6500c02483c0c41801950001046c051071203e52803020016004801c0b880c406c440b80c4680e80030b000a04034181c1d04c088034001400c0f80745000d104020f01c01c0142c683e030454188420081495080000b070300380ca610940003403000c1111201003102c280b03c0c4510080c081c400b44004106010340d414030700c07940541e042c104a04001c0c0310000c1c14410159a0b841040144e448a400d10440d109a061000041038044020091000004000b800b540078080c0100860a8410000040e035410006c4d1190030034405001c1e02c144c1d080101e95025648a4149408550b124114600501390280f03009a8840c0f5080005003000c0d4691200403200391000f00c00c180c5004c2c0080c0310200e4902c5043c007400506410075945039640314510b00c2c0040c14108164410a4800d1800b810400907980119480521560043d0303 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 420928309 1250 420927059 420927061
    0xc16151803230c1606080f04020306010b0c03070501090606150302120c070c030c0e0106030e0a0c030809030c09090604060501080610140402160b1b07030509061803060408120a020405060a08 83
    0x10b40c512440c007486085001c00d11443e8000803525a801200d4810799609036101c2e9039980d1080d00c0c00302c182506807002505a88910010000448441c02034500c50042c802660b24100007a1925802c1da1410b502c00e80383d4607070342d080411068620640e10f03400b07030340f080c00e05508210f50180300d03031b000601c000c024a44c41c00300000c15508014007041441d0156a100d054050507507202c00890054550074010200400c0c0b400003102241040000e040c0030480c0d10040c2d542040d41150760314803c07030300018046074051003420081030850303032200d201d0741c400c8002d070b00201814642030400500350f40040e400f005482c1c0046003404401c00803050000140c4540701d090b0312000c480400410028412002d200034039901d84400c4008000b14070f00058043e8840c0d0000d020a9060420b03000407512541c10700601141003013203001c6c1242805001741c11320383d102680030080c1c0c03480c281c0841d0500b4000c070380031190044002008a00105010402e035000442c80c0c10460505050001184051292403091024025404 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 420929559 1250 420928309 420928367
    0xe010c08010e040201050c030307081929012105041a040f030521010b0711060405060d0f0e0106030803090106090c05030a090c05130c030f0908040308030c16151803 72
    0x3801f02c030200e20109046035564134010380700420300003081d24a6914094a40404000000781d030044040e03c2c1c980d0714409903005141d4007960440d528a5540c2c3c4d051015112201011084641c085220b0b010b180202243e00d1900e807030101284420405041480031008007484042140301c0802d6940d1541418490798800440c0324000244108500e40f952410011002141c2000c17110003510140d8824006190a90754480070082940030f640a10f503000a800d00840748000d0941e0041c40c0020309440d000111005c4032240301d425200550401d441050000040c40301e440d109106100082240c00810858070760003020040041c0700207443c2c0421503440d041c514040c005501141c000502005103004d8407051406c94000103403031134198040100e807801143c0c0c0f14911950180c00d915590000004c0c0c541821071381d840101d40c2001e407144078500c0302400b9048103040c0d6000807806840c01000d410311503082c42c41486c4161070503025210400c0c14409010400a60000d203020207400b4008008841d8000d00 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 420930809 1250 420929559 420929567
    0x10b0f090607030e0f010206010806071b0213090b0f0403050703120e01240f1203200604030e100e030a0605060d0b0a06091d030703121d060a0e010c08010e040201 71
    0xa8061580c4a840001c80e0380415030402851003982d0005c2d1505412a0740045c01642c94100c01d110350b101c1500150000788100c3e100d00c01c860080d6402c21a400308640290700400c40d80241e40244003c0c03155586400c01c1448900102181e100000c1d121030b80040c901070358000c10350f00a0540040c240044a10401580c1402c0d030021010400c881008200d4030081000d8003040e1006a0303142c80d10101c41d40404107400e80280302c1c0d0026104444000781146410380d07012950070340c0d01c1861045245200b0041441840b0038030440b070165000f5599000001070000c104045007540040c04024000c480280910940b008a06500c6185e00200005840d50714400411480003510000401a804190030000840542d030b01403000e4440441d0204807020f0b100b00c000c0012070344c081d20401554000e104060000f4403036a009401001c00000101c0c40c030142001589044032032581404803504680100700850042d0b1040320628002c0c000240000c821007140504003200601030070303070322a0700000050156406 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 420932059 1250 420930809 420930817
    0x315020310030f03080a0f0b03060f060102030708030901050103110f010c020f040f09050a06050f0606030a0c03020d020c0c12030a0c0b0406060302060c030703020d02030702090a0f0e19020414040b010b0f 89
    0x254100d18041c403c2e20700200602421203415112900d01011081150403134411507210b010003134000c05143d2a00c40c0902500031000b05441c1c114072041051000259141d0090340c013540f42040042029415450041e81c2c000b40c0281c410b0103142d002c44150a07581e480001c021446d034054913080410450000850090055003115842d000d06007441807040110014400d10384600a044c10002521404038054921900791f56013a8488410300c00b007450040c079540f064000e14094180140343c12241c8100d007043c1e8220740f040c1c010541060b003101d801814148440f0104414400103540b03800c6078008064249196107401520310f240f0340c000601080469840b040255800800a90325181260040ac0d501d9210000450040c010311a228100d03c1c0004241c0c0d4130607031f0040c0812115a1111078444c000d00c0c000d030f6180c00c000d48406c42c00b0358440c010f2100c24032280401c0c000840648090040c041a940d00107543c3e80036000020800c80030550382e00b401810340350110881035548954010401d01405 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 420933309 1250 420932059 420932063
    0x30115290a0e09060d0308010605031005091008010c020c030d030902040204050d11030f06010510030f09021002070602150c0a0e060409020c0303010906050306190b0307090906020a18031502031003 86
    0x400103003110982e03085034103804071200c1110700000f1030342e5203c03d01001c40c20341d5000601103660741d801444480e0081c40613503440301c164017020b184244d0320383c0060040302040d15481c69a82804200f030100c4242070283c00400812400140342d070345c0c240ca01286d45d518440703840b2002c25a6820002d000c564540d0125801801d0051800201e107469041041c0e40d03080c00440c4511074422010518003500700490158104c81c1c004103602d1003400d03001c00036406401e806028001d1290780e44440c07001a41e0b40c030869070303041002780d000f4010141015800380c501460002591240c06440b0200113601c2a10400c541ca000020b20349856100c1120300402e400c1c2c0115001029124008281e512407001e002000c0d504989203d2402e009841e03171281031680702c5909980c045084070742d120008031451059040710291030000b501b110341007a51560001e0484d01e05c51000c40b01e040d000070b0b08806540d1710101c2284000380380303480c0310480d40c51952514542050a004116050703004400200019014203500d00215 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 420934559 1250 420933309 420933389
    0x310080601080c010201140903030f13061e0c0309050c061317010c030f020913110408150103140c100e01020715020a03092907110d0c0f05030115 64
    0x2503100d64256448020303c2101600540c603000d82c0d0007000201000843c00b0320b9204010314a03544a100340d00c1c0c040d0000825440d0b4042c040205072000603000e1241c5a104801c56a0784071a000502c0600703819581f49104031000c02d41019441030200e41c01180e05224068122017065464000030441d0600c82095444102c4a0106c1c4007581412001904400c1c1c40308120354042109958610f4602d040b4010070629540000c0f0300d02c600e1490040c2544042510100c2c20051411f090340c1e203188500d00080c1907400c0d0400161200100204107810311180000300001c030141030703d03403101404500c0801041c0040401c014a80700f402400345d0017408000098010b0b900c1c01d900101820202035640e56400c9811800201750f00d2002aa00320b0124000d0403120210b440e6400250443d00c44000a0b00410800c0e00d80801c00d0441c0d030360955071031500040c450300c1413141d40f2401e8608114030440c8400c0c1d42c4058081d17410091203040e1402d54a9103803098401200c00c007021400480480a64520904a425108 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 420935809 1250 420934559 420934561
    0xf22030209010f06230d0b1503070c0c080a08030c13030b010e22080f09180901090b011211101107060e030d090e060105092d0f030f0601030803100806 66
    0xc07860003149005131440b50711006103903c002213460044095030150340281d03480c1404150308006c032581107100d070800c00074800c2940ca011101d5403541903000340e070802c0200301c001d0003140402061854401c000c09002010304102030550f2280d809074840241043c290f04000565440c4100e002d042e801e01031504800a20840e6845880c80111001d06440c1c40501d0032500b41c40030b03002c05101e003000000329807107003889050419051b41d6688a80004040c554400a00e45160400e11080301c0307524421001c0700f0020444940c2824403400034003040c0c00c0700a00702300b0180010046822509291030300300c03041d2140701011450500c00c40c0e803425182102d103007501a920300000d040358450078405a61038100e0a84003001d2010b402521507046d81d03c585000030b40400f00240c00da60080000e451b030791001400e05900d942c1030501c141e110210040f04020141c044500d9517542d401c190006c035510780f50a50007050642078a83d0103d0740e410f414440104030f80c10010000300030950041004004240103000c07030741a = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 420937059 1250 420935809 420935819
    0x306021303080c101a01021507030e060406060302120607080f07030603060c0c05010507050703021b04180516050d110906031608061b1306030207060b0d0b040c0504020f2203020901 79
    0x444d4400782e29501103905060b03c25005410008200c80d403c1c60580080444140b9100030342c400c1c1c00c0050121045c569180062040303400e0900c04d06100c0d42c410070300082c0c41801d52040081006980c00c02541c6a40010100144503800c16912a00301d103000e1200d030726540d18100c04070040c100581000b0b0425081c00140b11046401120039a09988104c00a114039540c6c8602102c16001e484000340060b07000442502c1d000808a04c0e1803a82000540041811709103241110344e4101a81350440c0c695000d03202407001407045014880c043c100c00c5030003103803014454a0b0450b03505050f068940c03184c080c140224074542e80810000161520002ca01c101c00e0780d49181054070380314215100c4612070300c00107101140105080c00c80d40b0100c032904441405505000c02140203421800f000c44526588010220941d581e031940441c4107842500c1403191840c05152001c03072072495600c018007460061100e01480c0002006840c0b6011101200c003001c0340c01c0b10310040350500c1991007c1c0d0032450210003c18 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 420938309 1250 420937059 420937063
    0xd1410140604060522091407030b04030212030c0a080703090605100806011a190924030f110316030f020f03041e0c05090a020c0f0d0e03160306021303080c 68
    0x803041c03408460030401203a0300e509000f4850701d10320106410b100038908100300c8603502e5200030000385c000d4580c0040984685c1000749889010b4105842814281c1d04101c02c01d0345c104440c02550090004032419400e002d8481c80003801081d04000c2404040c20002e07500e83d2085d441180c809800c04c03400c0c0014107240c007030032504203640c0c0655100c80c0103000003c14802c0381140001040f46800d00020700d0110403041e500c44400c1451000020801e1504d0002425240715042d4580c04480750450640107480c003101900301c0d80c926010300c1d00c0a05140c0180aa0407180c2e05681d84038003281100030020110a000714000c00404441400301031002c00d0b01c4801100e02800365200d28490340380ca000310700c515058403942008180008000500011040c441c505203100e03200d03049424144050b0400d03e8403c81c090a21001000b624010752006203100343c0607901c90703150584034405401a066142c800ca8109483c1d07001400081c0a03507400140c8502c0c8042c0642c0c500000710f40009180c0d81320903818200903 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 420939559 1250 420938309 420938311
    0xc01021c0b010f17010b1308010903020321061005030a061806050f12100c2006220b060f010c0f0804030b010e07080a0506030c030d091d060d141014 65
    0x9400203548181103c84203000340f496941101010503020a01d83c608640325199a1001c025103140703800348000010021424020a103d0a109401842e1540c0c104c004151031010303405404034204050034244103a0352502c0c000071b850324190b8548242c1e82d546003d92000601780369400100324100c22170381a1411081075001d201500c008a40781038000c80c2c2081006659812504080101c0c0c200b103a0205441e0b2503580301050440a5087c0503203403d0500131081307843c081884803101c0c0750300201c1c1080440e4000e942400c849803828405007006004c1621224800000281682d000300c02d03d5880d0f205036805100071450045d402901d03580466803c1c82c044100340c005100403251144800c0c000f050741402410802e1099840e80d45042c0a50307076010043c00602806003810384c041c0030340051041180c4051012904440d002d8941d0b0850b58039001c541040d10320010728000381541d50006108295036400300e40b5540c00e81000d1008150550f060724a41048000e862192950740b800d00d01200e80800c0003245 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 420940809 1250 420939559 420939581
    0x609091906021c060506120702070317090901050105030702191a040c0905060f1c03030603080a0e030610060e01050307050d0204090537020c160e06032806020c01021c 73
    0x5503510703a5182010050790700360f005d039540c000d000f40300400310308050741c2d030302c950020f01c42c81142c400c1950b030348806101004007003045110f00d10004810344541014804103004000c00e20340325145180c00c070402515a103805442c945e40003c03130b039201018450030b008000c0c40c0070210780c0d03120f04609003898443c506005600c1291022070070600001c1d117501d003500341000100006083c86407150301007107100640303022114045042c10f5071a140440807030407800107083c02007070703c0d2942010600c0074406c0516101000704141881940c0910500082c0c1e03014a644810700401c1c2400d80d100e458044c1d003521036010b07009044038410310214000840c0c2c120f07604194010103900d05030580500c0305c1802044264a1032030349010b00c060300007200844400c564020310300070f4250010355020b41c116102c1c1303200115031b552140c03400d050b03c034042c800c2d85c0c64140643d42e01d50344000c0b0540c985816048110441110030744018140c103034003045c0c44a05900a40443e0240928900b54230700e88024601040000d0041d4540 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 420942059 1250 420940809 420940837
    0x100203061c02030d081807080d02160b2d070c051c1a150d0b0a14130206161406010611030c03030610020c06040b03091b0603060909190602 61
    0x14601c802003018904210031500036001d000c620a070a042540e0800c400383c0a40e0b01d101d52034131040c440c0c903400e00141001d0a000000783c207a560030408000c0c94840200d8440030284410041040400508021913200c0c0e450144100c441ca640880c4030f9001e01510500c10880000c000341034004c2020b48014a800d5400c200d5141c210080c048010100c50845400d00a02d040c0c69060000c1410784910b192035400440803103902e098110365404644c80070120002101d04e0020310080c406041900d01640100800081c00b07000e1030314100c0c40360703001d0354620381010b402800000f50319040d544c010041080002c1c0c111090241500c00c2043d520f0f52100242305220000d5405500c00440c0c0c0004070413200002141d000541c2140c5070300040024070001d95441c2001e6204410404905440d15005000203000d2075510346e48030f2620118550030400e1205203684903602a81c07400c0e0307160703032071400383c903001501611100040d550b016031b2140703444e41d007003c074441c200e007850002c00410507940c00401c449601400 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 420943309 1250 420942059 420942079
    0x60f1c05060a0902090403030905070503030403140d02030c100506010905040c080412090f0b03100e0c03041707080a120e071509080a0b0112110405192d020d02090310020306 76
    0x104070120f980442c002540035141801190100f0700c01d400c5420083e0040c0c05603025035135907000280c5141d200750310803140c070200d005202205803002e114080541c0824000742d0724240015a0540d2144058445418200c1c0e4a9010900390b034802d00c0303003a0151401074802c001040721820080c1c402e840c01c6504a40090b605103862104500c142005802c03500d1540d840c2038040c2c182614107042da000200b8503440e20b10102d9000500e2202e440009014004940c502c96807400c0c18181001ea20405400c044400d22042000500242d0f0203803ca810b000340b940b40104402d51101c0c0260080c01c0841c17142d10103849104030110b241c0c0d1400ca0200d50360700340c83d02c1d1542c0c07003a5180d01c030702e4482104000c05030040e8840300c01005500848010030302511301c00c00b1208840302a040000b000c581041d1040b04409480d416403000c2e524881c410f90350181c20035000c400601c407012600040038040c0d19070220400d42c0219445090b240f082c0c040d10040500142680d00700c000c000308590080d08103d400b184141d5080b4 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 420944559 1250 420943309 420943321
    0xf0614040e0c01110a060213030b0703091e021306090c09050a12120203041e031a10031b120b061f02030904091a09150705090f09060f1c0506 62
    0x211a0303825107500c0c90050304128007180015241e101d00d103007581d0030601038500320b000000c0b09131008102004c100c604c40c0c82418294101041e0b1100000d03e07120a141c50020a40c000c200d11152241c508008c800d1282240c01c854804a0700b454031081d0326001050801c0004500c103903540e0801c022450f92656400981c540d10303820405800f00e60321501cbc1150182040d40d60205d80d0082203117a20003080d004503881d00b0b9503408aa80203a180c100e12020140303200c60144100180702101e0a0b00d0750320144c6055a6080c60740305c0800d0044a84001800a40d40641a0306291100d0390703114005c002c2e0710710408083e000d50416a8004c08200c0d00c29200d040f00341c00120341e0f244483d8031460850195070041d400d005040e01400001c0c500c4040560722181c0a100190346940c009203440e105842c410061b200303c80c807420f800d80c6006030143c44081409404e100e012a19240d000145071080001c83e0070000540381d030310101d1007100c80340716980d40010315000c554980c0c4043c980c0c0c81c1c030060b1040301140c0c0c80717907649 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 420945809 1250 420944559 420944561
    0x506010e031f0f0b060d05041112010506040c08013804060c060608340b04080a05010f05090c0103020f1608340813091b0e090601020607050a11010f061404 68
    0x210304c0b9a07034045410300014884940f00d80c032495216200c1c80b1803900c074102c51400220f0215001c0502d1915139110340801c003075810613010300c44402c111030404001d035504062020140d41e4138501c1403c001801c43e820340440300224282060700202d18181560780b0764561000418400c0c8540c001c0d600941425000078445c440052000503203103401341520005000004030340c0b002c902410190201010072000483c0100340e1200805c000d000c96801000c40c42c80f207140c100d0035640d8030300c40031600900d40340030440480303004108009012824600181d0f1441c0102520120340070305000d28800304200c1041d982006001c000812421a030840d0510154402d03101007603502c0d01078140850050700c910400d1000a407008090301c07044044510741361100b0b4407908e140e01218802102108211f00340c650700c01100d038000c451686118816a107000c1c15142110020355070b003601608441c100a00064031081e05403090805061003820345000f44420b200680203c8041c05641c000c0c2d0141c0c0c201c05c001c4246514003 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 420947059 1250 420945809 420945821
    0x100e0c070302280b0a0507110c09060607020409060c090807080f0d03020c0307380108060f130b0109060303080105010e0f04050916030b04030e0d0c0302040506010e031f0f 75
    0x1c95401030a01010b404014041c140b5000382c000c8003480c22080c090300069464500b05d1140d1010341e00010b1034030300640014070b00c2c4051101c1c3c8020350408083e041c02c03030301d07802d603410307802481520b655554081074400300300200503054014201c1490710013441c0346d20754002c241c102290060750440340c01c1c07078961354110b0f201c1201040c0314240da40540c3e03810103060b010707401500202c145082031ba81030854503180c040d901850091508850305c5051032116507812480802c4c0500c1040401c000401d40c14000c449580b03501c080d100c52060203507100000c4103107400c0140c14404035800440b190965a5a48441c00035140f00d001c110b0110700410000b00d40d65114640c0f03c0700c0c5450003030031003000b00f8001050100034180540b40c0c030400e0080781956050100f182007080021803141c0341d014518a013078200200f601420a5203e0301c5000000415001b007900003800303070141c0c1e80480c0c001400341c40714001070300c040c0342c1c4d50412070300350190056401104a40351580000e1540941040c04121080d005000c00c03526 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 420948309 1250 420947059 420947063
    0x609120f17060d02220f0e0102090913050309030a03111011070308181209040b09071e0e12010b09090f03040612020f0712021621030e09100e0c07 64
    0x801c000080181c9480c9110722201800504660300040e0580d805081459451072059501034403081c041c00200e0300d610a8242015414008500701741e45800001c0701c404025011401070501451804103005042c000c44010450040444540303071003910300136103048000784451a0324025900302015030b225034052400c42d903416100c0380f4900700340d550b4261106c04014040180314401c0160003941100300304000303920b914030f43d1400398450120008001c01c0e00c80001c030070b60089e00020140911640c00015000700c40340280982481a505c000c4205c17070b4413110b010010351000e49820384502c845010f500915000005031405005586e07404200f59a40e41c014000340420f900400c02004032510641544554100c15040903142022501d88000740740c2100400365248120b00c0d52021900f030301048000903002883c14040c05091500c940950400c1d201c002c0040c0e90700360507181c141018803801807481f101c2c0004148040da401e105130f482c0e198408600491501030060f50200e00002c0309071003903c040c0c60b = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 420949559 1250 420948309 420948347
    0x200d0801030201050c160602030903100204082806050406061707080319090f03051c0f02070315021201091b050f0a0309050a170d050123040b0109030609120f 69
    0x2074078603401101c40e40d1000060315400e000d01924480c100d10400f007180000c051070b030b001315166580b8104040c104000c038502c12010510410041148180c04602580c1c880112006a10549400701450003100044000202010300d46820081000660fa1000341541d2100e071100b0f0080b01207261890b5034112078010108103904c04c1c80010905c2d541504031100c40601da00e0680c0d0410399520036039800440303d810450322608156800c2e48041c205100429013044a89010855185403400107900c400e42400041c1095081460b00e028084a81d0100c5a448042c0716601100390303941c00d42c40703000b00449043c51400e8411588030491042c40340d425a603125075001621031078100f5a680560042a00e0501116180503e100c24404280c19041c0c120903d0005010715544004a614500407104c05030800c104107808100302944070003084942000b908025640041c03102c07104001610f501e01507074001444e660500e01200108031151001c0c905505964498050381d51301c51206a503885e1040303041003c05 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 420950809 1250 420949559 420949561
    0x60901091a1c150e10090f0e150106140f160606031e031b110607030507170a050d050907120317131205030402060f04090b01020d0f02210f030106200d08 67
    0x14400c04104070b40108170b0280005840384c4d51052201a00c590001d80203101d6580c960000b9400c0050242c860201d614100754800c66042420160070603000000048444d20702040e010014481c1e401103804482618141c10090b055510b03001c8051b04960200f00c4a00100c0c500c4184c119505440c0e00311019030588402ea501101c89a40c40d030080d61240c002d5804030b040c40b001ca0200d80328903004002c034501039500c8503074400c00303400d00286e214004a0440007602040001c250010390090640d49803000f40007010907a40c540034034640c40c000c40781c2c2040c03020090851224040580005004214190160b80c14541d80e840d05002000c8440b8280c02501c010015040e6a00817032003030001b141d01c244000c103081d090004448980202c0d40054200300d11182c6d0f0360410160940e0100069558000316141007080094120340003911341c1079130309600030102a030341e2031b58403200c06200644060381ca4091401d40c480d039503aa00248074100c0b0040140c0c40320410004000c03448004180856140201d0b1281005 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 420952059 1250 420950809 420950819
    0x90d020f0a03030f020909010f0e011d0711160803040311030601030201020d0c05100516020c15090f15181e060a0509060705070e0a0f02070b06060901091a1c15 70
    0x307013003515034006a2990810411013a582c0c0c440324a40600004042c58030403c0c1449122100342c0700c103030440d0940241000035403080f001d50b020300781e6014000d494506807020741c0001d5036160a0010460007050800900e01107101d660000150045900622540d01301d40c444500b1316803034031000e0002030f005030003600a140c10980541d2403c0105c13441007040f00c00070413407401c2c0901120390036680c90440c1140e40c10303180c01d216410440d540c0c00318801c41b41c2138400c014011640d1154032504100360300451108445201d00d42e100c0d00c40d01408904c3c80d9a9584e10116215080481032043c4201031040c0e07400c0700c441888044110754407a0042d4040c102c685003007802c91050740c1d507802031181f03654400010000d05000420920001c03000300f14502c031007515424440b6803a0103440140e41e0f4071001364418400b81020501c0c3c0c40c1e4140d0407080941d8000c0c1d962514a0049580c510140c100e19440c00f01c0100102c800d103544401018082c07010b0401948044003200380906454940d0031000510341d0a04081c41 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 420953309 1250 420952059 420952061
    0xf080d0f02030d050a0902100f230c060c0c01060b0c070b1c021201082103010308070317070804020108010b0a080a0c0909090b15090106080f040318080303090d020f0a0303 75
    0x341102103801101d0400c0030b034401c140107552044070f800b03002645407248a0700314141403490308202c00c00e9003441c01035203412400003441c60803010309694080042c00f99038601e0b0303000903003211104010302c4103995a80c070740000844480d078000d1070000b143c1e40c41c10100041e0024080d060701d8425030408003404015240070320b0001a83c00801020650404000c01e43e14606100d10050000340c1c00e0214400780766241400441c20287c498004900240d422000c18000c0c0c14003904403415a9030249215484018905084075000c9e4000300d040008800310017801041900040b4051255100f603032481d92581c4c8402040c1d00d00e00825484e00c0110f070700b0381c0100c0c0d100f103126048503554103141e2501c40800c1e0b65030010101582c000c1c1c001554000311040c140050b2045428841018690a491014180d450500700a0106e0401007aa030322440320980071030101032180d9003880008401d04440e545040d00c3d0015140c0b20360083c0e5a0004600c031b0308004552441c0003103107a03540c0a40603800b50014841a48083e0 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 420954559 1250 420953309 420953327
    0x901140903010b100f02070602122704020f030123010c031d0a06030b0a050d0b0705030c210919121b0c0807080f07120f02040912020105060a0f080d 65
    0x560554031401e681c4080d0304c4620390304054004959075002084140040641000080d411050464000c5100c8900701024a000c0310f499480000000c1c1d4040c0400c1102148250b1040d94940e110780001a043d0741425100050f50503074561100340050070b2514414458541117448945007c15007a000100200e40542e03000c1030690155103a01b0001f094030400158550f000b50003440109a071980269040d051147d01e4a0140000f070f280501c00840585580580c110000d00303100400c00000b00007040001c091060354080d243c21041c007a090a008041c15030710740c000f19141c08230b621aa000c0815102c2069040c5110b031600070000030f42c2e600d2154003c0380c00010f062100030303480c0149621000069484200b25005000d400040c03c41642422001c0d41080130301c0c0d040b0300050b8449002442580100f400b0342c4051944078005600c005820320204000d04400c10000d04480d0301001550699038041d00290710400b030844410b88440e4503440030a984015a0003000010380c4104c1b045c804841c040c3d42d0035 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 420955809 1250 420954559 420954577
    0x12092103050d0c090801061208071214041401030b060315041a090a060e01060503090709180f050c04051008030910112407030506060d09031103220803090114 69
    0x685031044110300300041d150f01d5541c8030b002422004040010007020711810f40075044040309a60701500703548508245028a0b000505030080040e210102c40780503180300c090403000240c03603c1e19556241030600110054012190103e801e0020710302403481c080307003228070076002011142a030603501c17814007005001d00914201e02c88800d00c4c6c94103207503132603c0c81717075101e40c0300800041002803c0456801c130346141a800103007803082c140700380304072134101140c0182510641d0100086441405419640b1034141d5100038050310f2004c00c4440c2803002c0481c0d8000400e0094a042c0403544800d183c1d054030f20301c1c80c442c68031075400c28001c00c2958901005040c40040084c60a031140c80841d4040f1420095540180702181200214001c15441100211a031040142c1000c2189150120100d80184500b5000703a8050755a04260380c1010b00603034406c0c03900c2e81030404a0341c8031850041501d0a0210300a0301c8400b142d03c000e000516590000115515800181c1d107003108240305100400094000b0321030 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 420957059 1250 420955809 420955817
    0xe0a060e100e0601090b0f0904171303050f07061803020613170a110406030f140f013e1b07031712060102150c0d0605190312092103 58
    0x85030341004502e0054503980b080d0080901119450300d40290203c070030f10403038540140344030143e400060351a40c0805602c9a081900303044210540c03070a4020398401d101405a15843d13008e0040140107000851a01d4201c0314011203100c1c54071030000341c2e1042540341c881d05030004111030038001400c1000181c182e20400c489032035440c81c1c40e01c00c05604540780f11040803455101e034002e2001e011000c0001e0b007650106407010000c2d2425a15030142e48894014060520301d2488950041118104000040f0007954402008003102036015007415030100d048800240c491341c28142c2e40407520280c0040c1d00425481084c1c5800d900244041d10700440da080102c05004403040000480e00d00c1c0d05003585c025807000100e646d020814a80841c0c0711020f01800d045600c40e0b21040c038160303082d0804541045966680946034000011002c0142500b03820107034106a10184050580030448030cc44152071244503510f22000301d10804846400a0388035103501203144814100c01d1450340103402c800745000b841c0c = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 420958309 1250 420957059 420957073
    0x601022a0d0804090b180c040b03130f030905012318060f040b032d070503090a020411070611250312020a0c0506130809100c0f0302060403120e0a060e 66
    0x111034180d0f4006034802500303652518540d1415107000380f001100c10349106020201400c0440013400342d4001d074082c0c00d02e018800000700310810807078044105040d07403191200d2051781c400e142c010b0041d10144101400306500e6140303410344404e40903541060058814025050004e11100c0d11241d0850900c0a50040e804012503d48000d040300100050b10f00c102c40280d80341011498565007241102410003856441140740130002e4800d0500d940080c0b940c0f61594803500ca14003c60300b0130403480e20096020740341138030a81d0b0070080712005e82491030280740100940c3c0d040b8000c403c540c0c41802e11915880e8901c0c202005000d042e07260040c055406450084842014a11002c040781c0c030482d155804980c1720a80c04040120030002d4550009e03485070a0322662485991b90503190050640140c8100e0244a900031030600c102caa048980e5005900d8004118450401a4480c04243c500307a000458402d03124004a909004541c40199080010310120b091500c8140c0144614a0f0741e01c1d250080320707 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 420959559 1250 420958309 420958313
    0x905010f1a0f0d02153402130f02040510080103021008041721011202040614030309040b040b03060c030405010f18240227030a170d060b070c03020102060601022a0d 72
    0xd4007418240c0c441040c540c1180300e00501da11400d2214020140600010440e2080161540281c08400b50262000411400275100900c00640034680000c0d82014030084515116076010171801d04070ba00079110303403220005921003183c0311103007150068041080300b42541541d0402c98010080b81200c181c4012050034040405010070301d0030b0b80b007940ea444000c5141000d51400c0c0c800d84004048004101d0605d02109010980724007034950010b04c143d541307040100003500c0b00d800c01e072603210004080d52107500c1c001c80410300a0b0420384003500c2c0c035031800302001c000c2c081e07030b1050340e0000905080c8c2c0300102c2c1803a0344a103185c000440d0281c2900445015080300e10f42c1e58006004019240021000c959601c100742d45007a44603805414820b500c09203615001c01d0303001d140b00751180040d1a03110b0384e824603c2d00e49006401190b21014100100060010500c0000032604095034800d07401d4803603e44841c0012a5141021110095980307550829017069040380821b2a010702c2026060000d1340786c540d = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 420960809 1250 420959559 420959599
    0x60c030909072c0f04051005040b043218060402100314011721030a11040317030604060603020307170901110d05010f0b0403050d0f090302040905010f1a0f0d02 70
    0x80d40f6881c03440c1c0031940701c45000d803030043c0021304040c00c182c2d01041540b808100c4d86840f00114801c09010782e40c1c0e02819070307140e240c94100c9041400c10740c044500031444102d6075030f40705010345412103510071517201089041d42001281810031229500416050b20741d9000c0000b285032040000040c1503440510382405882088518020201c2d407a9424100b011000c0d8117040450f00442800841d036003608040c8940551402c1daa008a4034440016190104840850052145030005440c0c0a204500d455114894000442c4162030554080c8440c0395070b00000c1c0c0a030700042d0333001400309040914013481503103250105c581c081010780c00070901000d0781c1c4280c045540400035608280307442d140103125018451121200815900f000c8900d450b10b135440303003a11072002160300000c10800084c903000e8184908415070107150000c0040246081516185000f01480c442c02041e142c01c280c0d02c101c540a43d804200100200580000780440b0b80e6010000340e00040c00f02241e106140302c40d814158084 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 420962059 1250 420960809 420960857
    0x70e1f050306161107050307030b06150408010504050c0f0d1713030b0a050106080103081b010f02030a0b190f0e1b03091005090313060302181201090c05060c03090907 73
    0x81c8041003d5810795140d4000c0404001401c1404a940503441c108400d4034000707801000c60380c01003000c070488d844d6400054a0345000c140341c4c1000f08400328000c07480920651225009038820310403a1002d1981c8424042c41c400d91040c1c9551110034810702e6000300b400311481c1c0c02c0d11405140950300d0283c1c0c00740d1182c00b00402da0400e442400c4000108140903429100380f80c00350100b414981010762440e5500f09284c440c0b44010a00e2100620341d961941d402504a1003085020201c15034480c506241104010042d01500030b1042c40b40305490a4440740d0f608841c4151040c40c03103100c20a50414680040044020b00720398505041d52840e600c180c201c1070007640c003c400c0c181c09060810b541c0c004060540b0fa01800889254100f0024595001e0342ca100440494a05060150700c0e4041c0f08521034031454241821358000162200e01c81c20b440043d4880310700c240c450349001341c1c056103e40c1405558000d88001d00115802000800940e01d0b02441d00c5500040d42d00c0c1510501c4c50608100c412814 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 420963309 1250 420962059 420962071
    0x7020f0d1e1827020301030c03200a0e04051b0f060c07120b04171c0c020a020d0501020a1d0303090d0503040b040f03140a030804020f060d1a1002070e1f050306 70
    0x6040c020312144910300112103d81010002e040d82154110f4a03440380a000d00e2000803d030f503507113200c0e4103030b0400319400030b00410800a001d000c20984c0c0d4140312180301c5085908503010b01810031f80362100322030804086580c00d0064070a00c3e12101c800217010b0154000354040e03600b40304824000890a08529105444a2064445221505044c90242c502d000c03006250aa5981c06026114000003d900c1c031507080c0c04105404500c02294203401d07410510b4210020350843c00c80031500c0c003800741c150001c0000d483c0a0390741d0300145040c95249081080c074521000d030325030070801c80c402a83c50018000b03c0d45600074030a40346804ea449a034415141d1059004601162240b24100144500000d0b0103080c1d0b400301d0040e0038034941d01c0c0c0d00101400b00c0280001d100e02c04d40c00d801015034580d9400e403031020f032501c1410004500300e40c0c152a80106042c0d031031031040d080c101007080c04501c042003000850381825100c0f11561188888080e0880c4000014281a0345115000800340e50800c0050302803a = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 420964559 1250 420963309 420963329
    0xe12040501180806070305040f0f110102060603010c0504030204022203030207060201151202091b07030c0209161202250602030603010f0b131d01020a0807020f0d1e18 73
    0x245058005480364100b6003540d014092528000c00070b10320086111350f40040306150001c1c00e41d03038a1500010050350f8100103003a1a01e14070306203081140d211248282c503c1d090b000c0703c1c105c1d91480c003010b0070303504c10b44500d10008105020800c0103080540242001780c10052401c0300107038011900035440d1805510503030040e40301110070419280c080c4998181d070854000e00383c08403420982e181410810049000b402010741000094260091210b0740400c54030801c01c4541e50185070600a01c1450380840c103030b2180c0490004611160380140701141044030a440c3c04054900140051009400c580110141701501c0088000d1040207118028681f5120391001601d0b424824241030845407070188003520240740201034003869a0356146090b8803029000b01203000e0350641072807040003030b00004030740156002017076a01080b600f25039014400c1c4142e134200d4028951f0a02d2076030f44c4103906030000c40800c400f005c204202c0805800241c400010341d06188270501d08120815181200540c8804500 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 420965809 1250 420964559 420964567
    0x70c0c0602070e04030c02040902040c030b1206011a0a020c03030304150c18050f03011e0506030d02030702062703060702030307090609182f0a11150402130e12 70
    0x2200182485000d04030520040508600703040041c80150300280014013072215407030000c01155100d030012150103501400c280801000088090040d0032035049407840307000308004500c81c0120004049040312810395a50001380d960109480c1c11390f11261401003140110219100303140c43c00c10003580541e1180e4002c0c200880d913243e0003801c4454008200041100d036045005c010641010aa0f042d03036400c60383d01308600c0040001a0050910291040310703e540d110003400501ca480d4032480c450b50f03003034080c0c4212302e00e00c120490b22846000002580650144150b03074000c814500c45256489000040d021105180ca00084ca00801202c1400060b0302c000204440710f030340030079103500903c0749060010f1194240843c9002d11126007501d14440c0740d4a003030801c0901600e04241894881490781140b089140d0000320140c0d40c009200030020680900c0d04189902e4000b07a0003444000c0b40c3d9200c011382d2101d908000240d0b1845541c03440540d00d958182846e0001031080512503100000c1071030392 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 420967059 1250 420965809 420965813
    0x40803030f0a0c0c03020705091806090d080108070e010909030504180903090f0614031b0a05040e0c070203154201050307020303010b0f040b03090a170f07060e0a020405070c 76
    0x2d0b29070002030302d07007082155607044d40000d80001e010016182c0498160607142e03541e00b01c40d030003024112005003003803140d441817082181c804144494000d1035a81c0d8031741261b8881c08100c0d99812640300312286000800e004102034803141d40038000c014030a1511901e0255210304a40b640450941014a0340b41c0e22018082016080038000000302989014042e40070314216010f090740c2e04504905000800c008001850080d01d00e035110380301010125000c6e201c040080004000d90040d0103112030b02007a000200d030238400c002c0280c440aa030300400400e0100310301c420748074429502038143c4c03071190081581802082180c18075115600414490600700c840e5414100240d10184c02905040c04010030a110045901004582c155241007000c2c990b18408511420a50b200b1607104454400c000b100b48800c80170081051444940039440c0003200110f54050340b0864810f20280000d030b1b000400c854000195581c00c03049180800c58103440005c840ea40100b020380d0402c56819001070420052481 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 420968309 1250 420967059 420967061
    0x10f172a0f031b09060d08071b120c090c0e041a031209010203030103170d06060e040f11041e15030504140a0f0206030406020c070f0503120f03040206030408040803030f0a 75
    0x6122004800034441c400308069180c42844040c0f54440c0221142400a41c094644103003902840b80c0c0404215511711640c10910048120303e404129140a016000102d082c0780f01d10403580d0503008019810194609660341004080d4440540284850001400790035a1541b00d0b412b940c3c00c0a08a1480642034903040508120030014040d010500600041e8503690740001541c0c1502d034090400e40071103000c1c207040c025038060f02000d5210070781041000314a59900014038010600291805d1080340c0150440070281c1e202402c4600c520341c000d2008008503501d1400840902c8660106164000c0c0c480190030607240500701d00c44c000c80c0e1a00c00384002c0160102c1014150010301016002004517540d405e1010307161460044c2c4950000300204090151560440e4400806081254046507440c280e2441c51140c52040301d00ca400380100c032044402d00c40341100c011401e00c070262031441e0b13500d40c00c010b0306400242094030030b404240008181c3d034900b00002c50003000d100603100003910703220300710310 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 420969559 1250 420968309 420968329
    0xe01050d0b040c0906021908031302130e0304030b01320609030a1103060c2106010e060a0305010e06011809050a2d0605120c13271a010f172a 62
    0x764000b80a1113640023185100b0140c035042145180d0701d0b002c3c0c0c425400007a40d102c20160454032000d02e0721103401711400f00000180100c81c420745548400f0303a0b0341c08149840c1301340030b0001c0300c0010310341c1415645d1851002c441c2010860043c0302c50300380a030020103e03181100944040780c440803941c504900c0c42c0740030888030b940030341d0541c641803a00b00c1d030510003070070012141100004c82c84c10001007120b60b03004410742460400003908081c0c0350b046a82004014090070300c01c0c1d1b0080a4200041041940b0590034682c182e501c0c4002d0a024620303015004000b0300004021a8503281d03121443c0d005256084130f140904102281c0030503240e501140188201c40c1701e94402886034446005142c01110301080034018040101c0f02e07410301c0c2034100400700240c00e105030740103901982d03104c4052601840f40000203459010741c203161821608050407000c6501c0c01e0049540c1c0b8040c501c420403829502d1030101c0d0300e042014040e1401e07a0314050201c0c100b01c120300d41c81c1059030400c88512455080c0b200b0030b9 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 420970809 1250 420969559 420969583
    0x71d0f0a02040b0d111b01050601090801020f09010c0203120406021e011a1c02120d0e0307051f03060b030705041e0509070c020a080613021305070e01050d0b040c090602 74
    0x4501d0030f440c141c2c04148502c41c0e40b103c01c1c40551106a840c20b807942c40003d032480e40b41c5002010320200801805a0f00070203088031120b01054203450041045030701442a1554001211021490041c00c44010740d80405d01c00000c07603051207800c03a8907146048580190005040c0e50b002410b0301c80c0310340111f40518071003010080705a8980620012203c01c03100018208840c241c0e03240c000051511041000c10b4204d42e00030350005010712050248510006102e9201141591940c407102809410540c031200306100c0e903603110040035080c030305144000c2c118060300c00d854100011016954406d100403900110344910114002140c200b00206c88030340c1501c0c103a0500300281411300d0a040000c1c1c0d4105001e0903440c2006840d951103000c6442d151212805004c5400032a042e034a031020011100004d1104228022091988403440c468060f0107850b02606068840200d00f20440d401144c5a82181d58015441510f42c80e03c4031294542c0e100d100b0091582da529100501d081c000f0280c6840100250 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 420972059 1250 420970809 420970811
    0x20910050c0a0303020a02010b100e0102012322120206060f040e1e031b01020403061107030c0204271218060804120c0b0109060807050a180e071d0f0a 66
    0x5030304024080400c2c2108816418140103845804a880c101c1c010204030481c950803808080d03240d14520780040496403a41400d078001c0c40a07486c1d40d1320080082421001c043c0c4803c81581c04100d8207410b4a80b203182c90b000e0410488046000c907107525881c194050a1b40c4e015800c40000d0200d1420308036841402828262401e0000d41c9008403100d58a0510740f614064040041551a10030f500c140100c80702e0075420131803001c9000303007149081d001303501510049500e40d1400320042c480c40e010b401942c04098154860030310b60035072034003440301408500050b418468205503590100b5040b10000042d42401480c0001621200b04400382c00760124075409140b00700074082c10030070a03610010b80341e440fa501204000c180290100b0580c0c100300200c00080079004060008a900c40c010b9000b01c0031107400c9022209000d507600244034508a10703000e0900e84041301581e1101b031795060742044409506240c1105d001968880f9610403000e644030203280c087c14017000703200201080081a43e040900c200d0 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 420973309 1250 420972059 420972067
    0x203040b0609090a030e121501180c082802030915090c03190606030c0b0c070902090603010e060f06030a090302010614030a030c06020409090c090507141c0f0c0302091005 75
    0x10b0107690f44402d100001c0170844200d00419082d1680d0380f854520847e194200c8400c051800543c1044103004d001c2c40080c2ca100d00a020f000340ba090180215182083e210b80e0960340314041c600280c454400c602000803698030015200c00030981c401903201302c424401804050100c00b40310000f111001e080c03003c0a03071080740c507401e03540d5006c60440e01c007152090100c0301481d074a1030a000a002c040e030001c0c14172104c3d8000040d64540c0b4400501384000300109880c03889440c0e84058040b40180100c070b40d0003000a00c01403160003245110690000c00082c10704095454020005485a000329103200c0030315201d0701450100354090040034040c0c10104110788401c201400882d40d0b61100c810081c0c10454030840d02c034140074066044030040c000d03568040c0090903180c00c24950f080124400c0b03030720440c513042c0000e04952003024504000c0424410281c90842c010402e1100c00710100d805208180e84c48140801c10072240c410740c521301c602da450150311024898100440e8004e400544030030300400704 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 420974559 1250 420973309 420973321
    0x602060f0402210c0904140706080708010909020f0405040c0609120b07050714191a061e060904060f031e03080f270f01050112050c130209130203040b0609 68
    0x84000c411600081d80c50440c3c03450628014a8070391454806500b0548100901003030080d0020010010481c0c00110780a03103a454400f101c500e041101c886000030103100c010301044400350070a1f05060300040505a0864a40c000641240c2e030654044801d0140d481041292640101e1008000c001c4c6003682400ca5013141c4a583c0c0351040100400c040060000d0160700b006102040924445a00d804680807424902c20b04032800d5108502580c2c04920000000e1600b00f1001e03009220390000791410030807800c0b0361840703916007201c4255a80c1c01f07803060103000c42d1500c651159000610203440004461451410040054069440704811003824400b844d00031a8004050300c2d044807a52880c0c2c205039807143c4079162880303641c1d01c11020300384105402c11f10301c000020b00c070003145d0038000003013015981c0c0d002a00180710390650300078200e40042051043c80e02d802c015151503070310003980c0545055040800548808031110030401d085a0100c00c3c04240191050503c0e4001026121135099040c65 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 420975809 1250 420974559 420974569
    0x81b01050903041a031b0a091406030403020a021210140103020f040213030809040204090603050307151a090408090d14010c0f1d0f150703110a02011709010915060602060f0402 77
    0x955141c000c00c010000114082c8050f09140c4580100c0200d07060387c45201180006022030410300c01c051904806101d00c20b0b8600e00841124000c40e4140c00a0641034040d601744136208a030030b039440805000300b0011741c140010a014854041202d55000403a80d03046104111040b41c0042160340a90b20510064180c0c05e120320000d416250040303c03854030b0301d1140e00080d0180c8269006a0480c905162000040000010240451920500c00540004506450f43d0100d40c42501e51403a20709d2034990038055420130112454005010303001803450308407a1400314101c10350703601045a04000607407a003040302c07a080c03145800c1c0303200b00d180a4100d21071a080041001c600015880c1070304890031055038040e41c45800141c00c1304009821091104001c04801c54160803c3c00141d000c50f40e0780c2020f03240ad450100702c43c00710903416111841c1d100705048140881c100001d01403049590307104528400301d4400951841186031409010455a0500500904005d00905841142c602e80c5061000603518 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 420977059 1250 420975809 420975839
    0x60f08100c08280207060221150d02030f07060c1502090109060f1e0306090f0504050d0e19080d090611100203090304030804150311180d0f081b0105090304 68
    0x340070101207400203c21158500c0440700e02108040c90310009421081011540203040120700750001100e480030281c4107400042000c490083c451007a00381c500010f440c0c5208a071502d0f90014044444000c2c0b004011441d0411035007040303010801700b44a060070403030b01a0200300c1c804c0d03c8080541c140300f010800a420a0000e0007000c0c01c1c070004094040c4114401c410380385c00900e00d11100000d9441d03020001d13004140900800030501d003044440c0306180b00c40c0c0900c1e40625840340c01000180030302c5408030b56544081160560142c0d02a010411540c02008454013503c00c401c090b00f21551500300c044c082410701c0d8401c0f010300080e110400090540032907141d01001441401581d00ea0790140080e040d8499900001c0c8004400710b008034400020680d180160141a2030070413512038441c1c40d401c4107001e400150103064070703440021517048c10900f045803040d9220709803862001144c0d68a80c0956013104e080400b00780c0303190401c1051070109025058024600c640610b142504100500824143c = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 420978309 1250 420977059 420977071
    0x40f140606161101140a090f0501030603030c080d02040302030604031d0906061b070902041706070c0f08070c120501021908010602031e040305030408061006092610060f08100c08 78
    0x30f600d10440c580307074060003d9102d035400340c0000698a00360350002810f000c2090050000c0c80994410200307195020388150800d51780c00d5111410150754540d102101540650541c02c016a000e01002006890800003e80600d1081e01e410080303040c2c0041c198405c54000131214401d2841005101c0c01c1d44542040b00d4120b10114034661202c55885045440c01b10507900c05401c0610026000442e91514869103801c0e01c018800d031880c43e12007000c101c9144a030031801804000e04030b040000000e4082005000c0c01d4402c05403020640e54400c1c0000512221042c01d95003a500050400094000d000c00c40078071100da030a14401a505004c4025601d00601d1211074903441e42e04a00f100c44a440020f440046034090204c07030f5510b4903003058585480b001d65042130610070040c000b10b4424000c40030003007a900340c541c80c50380710104080840c00d46804d4500c2280c03a401500521010345405004030400740003500d0200410781d00d890307005481e16080929242100385050104580558052001c03a0401 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 420979559 1250 420978309 420978323
    0x703050d0f1b02010f03020702010201060f1d011e060507170a03050414070602060c07051e0106080f0c0612071803200d080703080c040f03201804031b02040f14060616 73
    0x88c0c3c10340b0060b030040c07400350060059280b0000d0002440030100250032a0b54400040031900341e41c0e01c40c003d0f25543c00c0d240103400090459502401024400c0340030300900c501482c0495001e2a1103044515136a01c081c2059001035100c20811051107000004034503030306040c00050240c01c0c039104000b0344581d400303403103909180f10001e8141f0078400c00300301844a620400e40f0320850200e07a814101c2c02003541e0f100b082424040c0406510000c3c00c04905444c00707a01c0544114034180c85006d07400503e907001000302083c001c902041040780d000c01e46190002d1480b8210300c88070900f2608942502c0710050920300e1280580b0303d01540000c0c0d074002921442540b41c01c240000f62103200d03801c6400d0280b40c005240070643c20300c001060100e01c49201240d030502c03c9115034055210028040c0700200500150990020ba002060029102d80408003400c0008014503010305820790015066440406c582003120751120880c52000354802042500840c0032a00e0030b103003000c03c039081009450000b00c050908 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 420980809 1250 420979559 420979567
    0x110a020c041e06120303060f06020a020d03140c010b092a090301020f0c0d0f090506180f031204080c0603060a150c020d1209080f030d0e0703050d0f1b02010f0302 71
    0x30009004441419070b18070740091007950b0311244400e030a6200d4200c240c00090900e6000102800b1500c001030130344000d54081c0110f042d04d0303028400c1c0c6041402c0e0440c10800e50103000d200d044400c2000d045200303501400421032080d8031041050a80001c2d00507900d410703046044120408610b4881905001c0c500c84480d25480c0000000e4024005d94003505c0760309a0005401281d003502045e103080d03081075500ca110f60701d900240c046800d0246801040e03003160b420020880084006214041070400042890b0340000000b40030034145550710340c0d546080326000c00d040c0055270b024064204c1c0c0c4103041d18001c2c10f40ca00000041c445843c0b03441200c40000300700050041d0940b1411182d01c0381c0c2c0e009002c8003000201858400d1400e9a05402c150000e0800080810211808a41c14440c1007892004609001075525500c00611580e07100c000036100e0b4007400000140e05005280f280c40054545480104c42c840c07000e0506014020110200e981078081c150050b030704001c441c1178420040c6801038403 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 420982059 1250 420980809 420980831
    0x1302011202210115051207050904110a090e01290a03090602180405063f060903120c0a090605180315090c03010203010e010b09151c110a020c04 63
    0x34401d00e59040c810b010203102c006045004640094121424502055019518030700100c2e421301801e4010303d04003001c1c2e00455034461050000d00764031403000b0030000c0c0360191810041e00b6944000100700200700c025a042001c3d0403044210b6006209003202480307800040522508045a00000c0f00d03c05100494103080080c0311f03078000d000450303100f9400c550b00d44105003941083c4809030070700d610690030100000e4181c14403a00000b0b50714541c9241b0740340e42000c5c05a99041940c00c1c00a080c400b01105441440220204080e9008130000c0c00655230300d480b00c204416059500411154101c0810441204803075404a03241c021541a8541183c80303050440f94446000c0360303000080d900d032003030204210025900405c002c0c010800c0004131100880c8010505090f030009101c1c03900540034800041000c10602c50082c146080f0042000e07901815101c8002c101d5000000440b100c52b9600544007490100c51042c000061044001542001c0d0510310095490507030b8265180155180c8400c041 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 420983309 1250 420982059 420982061
    0x1e0c0a03030513170a2f063709050102070807090507111005060103060617190902100305091009082d040902121008071401021e0d03050a0513020112 65
    0xc00b510054080d007205801244ca581c2d40c4c2c1e501c80f0010b44480b120403007408540c91030220900005aa400b650884261241e4100b101302d801429030850b049481000500d10707030140c0985202c1c41c0d00d0804080c94040000c240007801c40906411150556120f40340600c0030000001c0c040701254a0000701040d02da0750705600715980010660708070150320806e851101e85c41c0807a0819442481d081e07a0420046036110b604540d007040003403c03180c841c82d8050220b03615040950740300d60700d5050030601150804c420f42c049003120580101c00701c00a65141705001c101c0c00c09004035500e07082400410b01104419444820842c4161402403c00850706102d01d400b00c1d40c0f049a40b000740100404c000d0b200d90b034400080c8060340c0500c3c107103180c050300ea07000140c511072000003903c184c0b1001c00c0105020350078407544070f4a046403180814103510480007c10704a424440701c1c2e006007405140030384460031900c00003400760342014100c1000c950400e0b0410401241c410320b0460026024a85000c4942e0102c0b0404 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 420984559 1250 420983309 420983347
    0xe0108250e09010507180b0f0c030426010b030d0e090612011a01030e010e060402010c030507120f081005280306020c03250510090218091e0c0a030305 66
    0x100c4049180c104002e103010040d80034501c1100683c4544885801d66a2a01144021030040014112040c41442007082840000d400b401c0d0008013120325041d120f040813011a05000310030f0b48200b011085251202800f8090740c048200290001c10348104482d00142162604103c041d01403245000052440c2d030700c0790350841e40e440c0030000810401b0b541b00c0000820f04106900240440c2c101415150100c03030500c24034150003013480180105440760f5004545030300000c0010360800c0414800b010224406541c0010450101d40310b0f0480c0b64560030010f400e1400c0200403100701c2002c020204042e4580f924100d54080309100500003d00071440220b00110b1150005003000b440821924080c800000c010942c51065286103183c52040704028104981c0c2080b0013042500071074073700480704856421030142e0500c01007a40c0202004c104109181890845450304561b202c604465551048d0b200c44030400c03407212016040044925021590783c9503a40310007010480c0004101400c41d00e07a0b00c43c8 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 420985809 1250 420984559 420984569
    0x90e040b151906031802031e0709020d0207060c0302120402060306010c080d09110901030302070e0a020c0109060605040f0603030c110d1a0907062c010e100503100e010825 75
    0x104103200840c20b0849041c00c0e50140102081c0b5200d00784404599103140c003075031654014018000704d01d25503402d02c0010380c45a001c1045109200010860101ca400601034045600d10010703118038840c00e0045c1a581100c0c0100241481045030441171420300401550194058600950f82e441d1400103c40c20181540060700c1c41c0e80100b00100201d4980e008440058043e114541c0c15248810412090410a110040240c1c0c031441c000c1004a511424003030340f20300400d40060429901c0400c1c1070a4440c542c1044410356900c240500071450284901001d10246c00010004c450665401501128034014041c200c0014100758080b51303666071000d90080c5034000440190034004010203604050180d070040c119000e2042d01050f0180710300310681031641d42103040d070545842c009405c01c41070400b400040c104158034a805105443e00c2c60041d040fa0010350b07840366249412740c401038079145181c0155100b5511040100603541000842500d0407100c522885420324101d410084039400c15882 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 420987059 1250 420985809 420985819
    0x40f12050f0d0e010c03020c0d03052212110c060a21060b0a0212071208180f0c1e01201606030c080a0b090106030e032203030f090e040b15 61
    0x140002e10642c1c1c0050034403c42c110004d00550103802c0c003c0c0c059026000c20707041d071584440d00311724480d4425000150880c464100600c0444544d01400c4032039250307440140e401c050000c1c4400070071540720124440b0840440007400161207141c0000d4260b01c101070703402c1c0810100b41d040c00000c0f4082d01c1d4a0240b010308507010440690382e4440c00d805d5070041b641800c09809060248100b401e500d40480d0071640d40000002000c07001d01d030003902e442c0340242c400c0f0806441d240504290b4071040108a1018141c81c000340650502d00c8100101a045004010311039142e2a6802e07131281d030801c41101c246482d410003c004060440d881a161401c080c00d4401746810950001078080d4140d400004268440e907560700603075490741f00f40c5040d40c0440361100e812103030b91001007000380d1180c2c0c01103000301c4100082d217180140c218a03810360101c030540c0710314001d0700e010300c20030815800009565503060a0304004044c1481c001c0c0c06000140028009004c61824000148030300100000c091880500146 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 420988309 1250 420987059 420987067
    0x60708062812030215070809281b15020a050712030c05010204120c050301050402030d140909010f050a170a0201030b1503250e030307020409060b1002060f010e040f12050f 75
    0x28000d6440140c1d4400e1000d4600042c0440c515a109290880c41003421070020031418003054071174002c2d4034040001d1203205c2d652008401c00562a41240c02b00c041001c410f010189041001c005407080700d03542242c0a65200010038070015101144410450300d404082080d2015507060640318003004240080c00c41d4030014010507444182c09003400024010100d000c0125100c40c1030608940050390082c2d81355004c11810011144501417441003415001003150400e40140301081310450f080c1c00640ca807050100040c000c908160620400900c20802140510302003088582c0d03c440700c212000e03041613155074100c6019258414484000c0e0390381c205803075a03403900b0381c55083c5850030444084502001c20241c14995442650394009929005014510300551942004000e0901034000c41d01e298071a030000a4030f51741d2a840c90010156034015054500c2c3c0074860f400447c034144c11000740c000e00c00b800e0001007180703102c148000725844001501010710006003580d09000b03408504843c43d00c001 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 420989559 1250 420988309 420988313
    0x610140d0c0216060c12090503010606030207051002030103031409031f0e010b010e061c0f0c11240a0e01140703020d0f020313120912080c060708062812 67
    0x152101e256076a40303a09484a0008000d440d940c2c4665078813500d000640071002c40d402003031082d580d00b0320544007814809450369a61000c2030956605900c21001700e94042869410b00006200c0c400703c1c0d030000c103401c5246606580c0c1c0500881094240420046000300783c0e4502500c04119455040400c14001000034088002e5840a800130040c0c8840a50a00d80601801d50088484190008006000d81d0502c09142b4030003003c50810720807000920781300d803e440f00300000f902c604441d20009554a100303c1c003c41740c1d154500603084c4040e0099003407106075600703400161700c40b0503080713003410384042504002d10302c3d054094002000801e410076000e90521a500d0742650003409152036030141440310b10003030300707000c812800212003540c0e03c0c0c410303c01080002408051012003100b40c60801c814a070351076003c0103210f1840c860003180d203400700042c8107030502e4007001042d03070002480c500000c2da4642900802c0302810b01c040c1d03214558507440c2c51700074054003407505500a0640107032024a800054 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 420990809 1250 420989559 420989561
    0x80a1b05010f090203190804090c0302040f0609061805221b09090c080c03010311060f0418050f090a0803070306051203040f0509090c090411040e060a0e01090201080610140d 76
    0x2404202d1081c469a2590081b58030b40100454815801114a50416107000c242001800c100d117010410942d00300804640b1a0004c1000b0b0003504080c0c0da03c65046d81005406006200c420b022035152002e100b90405c5160394a01c0c11120402280d03010205251840c0c0480024201903d080c1600280b0000c1c1d40c0c3c9800d80c0141d07070328202c44402ca41803101c007038148026603101d1802d841440e25144108018008035580d04031490403440301074079003031038081c50000c1034549400a8110071480c059103024010410014099160031006c261404686400d152000c0d076660800e0719170091200d0320100c0001c0301e4a0207a401900109005081d0304080804022840d490364003601031590360000f400004030700b60030800805032082200d0001002502c5984007003008100c00100300310340c0c0c6031304043c985809440d24024030400c0200c1c40000c0069060104101c070503244d17100c01c0c0030400c0c3c1c90035200e000581c0c2c0c0020a142c0189081d1200104c4031030f801c40481c2c191000782d65070041c8000000700c0d124030601c2 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 420992059 1250 420990809 420990821
    0xa03020d030210051e010e250f030b010e0603040f02060405031b03101e02070c05041a040c030506010c080904090219031b0b030106031d07080a0506010f03080a1b05010f 74
    0x80f4a040007150348000c015492007960358043d2403040d40000041c17003401c194540302900808500d041c2c04491000b9a203440503108040745070400180844002c1054a800d0700469a00103001d0802042407040d02010400c240001040a81402800500101952161400c0b41c0240c94080c0070307a42c2043c4560b03140c080926002d04030501a00c107250641d20001078034400c0320b0b02e0b1201800d44006242d14015200c02070b4000400030b03540b00c4006880080c03a955144580030030000c0180050000180280403c001ca07501d895000041c18200360800a01d40e81c01100c03898404e40c04260300340c5407003255020400030609954025002081108080003296944400600316845410441200324501540320b448141501c210107000380e080c0010310400b0701075041040c130011001c2d154210740001c41282441d0211030342c07010a0076041800854140b00051098501401c2c0a038060381e04545903507982100f1380301e01c5880d401080310103122680070b135055042000980c1d4002e8024400c07100500c0100008080d = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 420993309 1250 420992059 420992083
    0xf06090f210611131802210907051905100201050115050a09030506040605010e090309010f110c0d0b100807050a0504020901021005091c0f020a06050717010e060f061201140a03020d0302 81
    0x40d4402c01d8000f000d0900888034560501c0c100f00700041d1f24070740061601840685400c11a000c1c454000ca59522150700c03020051401401c45894540ba290a00c0802c4601050380340441e410100184400c011902c80c24801c501607152003661084552011901540c2507000140140541d105002c03e00c045500500e041c1e40b03104507100e08039103400001d25a284200c90f8401c0c0410004540740d43c0d00341c091200450080d0b00b040c10303180d241408600140319000c203000c0440d03200c840041480040506054480083c1280c00c0043c840182400001001c0c01c002c4d10406206a0300054602c0050f442809401c5110b07100000600190824075059034a8208080858200b008140b01d2a1185071090a5240d2903000c87d030042c0c405441381d03484880240c2001130254040c44140000c4042c0241056825030003000e041741c10390f9003814060100402d1000340d4140714858081405200e800d0b2070943c41c200d04682140202c000c0c40c55510010a80105241d80f020f175011488080e513409154010951a201c61 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 420994559 1250 420993309 420993329
    0x15080c030d080106080a02040b0304050a0b01080c0f0d0501020903070821030601120e0c131b111f0b100305040b220204020309010b04060f06090f21061113 68
    0x4058141035a665900c88060700064851004002c018020b10342c0c2174020100010140c034003602c1342c0100e1510307401501d0442d881d5010308040c800b0300c41035142080c0900f001e60040c140d031802e044001080700504003401441500713a54002e1042002c2541111035480c0058203881080b956002c3c1d5503250b0301d18500b52412205007100480d4807820002c1140e110325016150407410360b40c0c3d00082001441c0c0454681600d00c141c1d2820f003816641e4140740d8120810310303c2c01081d04200e0203001c010320245040b00e5020700031040b460b1003800b00701041c100c0c00301e9440710500203100480240c00000d401c036050300a4010541e07103182c004840c0e15400c03107403180c0d010726011132513611815010301d84a00d20300000890300070000d13610300c018139158008640103840e000c000701d0104883d00004048403255031100000c0c2003074990400c400b6070805c501500600401400940e190310b4200030304244113441c8000d2000d504a0740d85042080b001ea130003401040c000070100c40d101e6403054984030511f40c00d405288480 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 420995809 1250 420994559 420994573
    0xa09021b0607230313060902030703060204090e160501050a0c03090e0c121501021c0e04060b04061b08030a0c0210060b0c0f01020405060a14071a0402090601020c0109050609060d1508 80
    0x5000000f045901031405004204d5209101d903e840000b400c054004a80c903004218000011509a002400240020701c0c0b0008a4424440c0e0141c5012110b01d0000503e103210f4000f00300e107a0f0840140c4518005600305003801e582945002ca0b0b1b15549038011481e914146410701407422040005804a025203104041440d103503a4044500c2466941540c0c1c0160f000b2160424082190441c1c0c803000c04040c02d040309030b0740194001800341ca00c0b5401c5003c6d5910041020081c940d408813101003200b0310708082d101c00501d40e80b2030100c0d40c0302c002c00d4031303914503181c2d00d0400790a0720811426901071410b4608101040d241c01c580c211a034070051032021284140d80741c00c041041c040c070840702103a030000d00480c6403150180040d21819558024000400802e0000201169404d0a1001820f20480b00c011043c9030500c100603030003070058031030b5045502902e10000c00d030340c00a44407001c0d11400c5508948490408001034a60f20a9048410019082c40c0c0200801d42d4a0401901654031041c260703405 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 420997059 1250 420995809 420995867
    0x40e0915010e060f120607050d0b030102070f060506061303061e02070311070803040e04120207030f05061e22060f0204060903050c040207170d0228120501050a09021b0607 75
    0x11030303007114000c1e01d40040c000311f5001c40c022401000d2100e001c0700003082d0b4205201c006400c9030000c0708191544518030048508000f00d505c00c3e5a03201c2400c49505051410b0070410701e010b22840e01000346407581c2c0b43d07119a84815140c011684442500e07101f907545403468034006082c50300c6401d1886003403141d0000032034071190120584050300c802d20720514865584d130300c2e04204200303a0503d960035070107030200c00720102d0040c400741300d40070340648024542d6091144580e5481d904412807003d1043c2010140b021510744402c030049801e500501d41c41c0381c42890704118008041030307030310807509a2000800140301608000040102c034015029101c51078629400e02090388198403004290225012840b4803054400e0050070464246841c01400c2000e07103001082e0b00b81801c5000c2c09500740100e0a41c1505510440311158240001c0044c41903500d05804241d400101d40641540c031600841c242401180c0c0e0103040e204518000101e81d194102004083c011013a8011001c5100030310b0104200 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 420998309 1250 420997059 420997069
    0x409020909090601050607032d051b03090a17010605061602030111091813060c050c010b030111030a09020118060c030f021b0111340608010803040e0915010e060f 71
    0x104071980a041c180c5803c485550072600701d0803038611080345c09248500000100b440c1ca106927540c880300e8594907610510352984424203540c0f9414104030b54000c004000240d140c99400c4130843c4c28030000d00d5401c03038181d90500e002d006d0542083d5001040410030303a03412545090715159060091713008103d00c0400c000740c115207108041046400c2481140543d4000a0b080c05140d8010005640c803040d00c002ca5980317209560340c100c12240010350100703031891509820310460a0120044008001e0101c075081e4500301800010b18440343c45235566609003d59004210071030b030301210200e0005800d41c9861000e810250310713050070b0380011011100070342c91382e0000407024040c0da14025042c200e08880d0004451a000b00e4030b0f20030640c000c0c04842c030601d40303505100500c8a0911040301e24121030541b600080d6000c2640324000300002140100302009003c801c480c1501d1444140c500181d5424003060b01d00355150740304004098162000040d010300b01e220359400342d18111040d0788880c1701ca00401c0 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 420999559 1250 420998309 420998311
    0x513090f0807080c030304051b0105030609070806010504050d050105100f031e062c10090c050d080403330507051c15120c08060903030a02090303040b04090209090906 73
    0x3403500040500c04000308400300040d0220a01c104540c6150640554a450170b6810581e42100c650703103d02d40320360040410300d6105540c5c600a183c10760440c1b60420000c0c1c1d4210019090400384603d82002c10a10f9206804480241c0000384c24820500014541079000300340442d9028185041d04c0004a24599640114811a030300104040301d42803880c00800381c507124644040b54811358420100140b00c0401c00b40d40c030030b01c0d0001e405011030071203000c0c0c00c0c1c24007107503a50241f15145040e0842d000651007a8484040d12003d80341106814024030704a0514415508041c000c9000402051075815002c201e048005644007404190390311410031030b1040d58400c1e210305002c140188104180301440c0340618004406000001c540c0000482c0301e010740c0355103504680b0b801c8003c0300044041c40081d060701c90007042c0400090504e89810741d83c01e5100d000103810703103040640001d0302003440e550810030f80b0040c1503008078075980d1f40d0b60703403040c0340c001d50100d0203d50203082010b00080b15914003107080703 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 421000809 1250 420999559 420999563
    0x3150102070f030602030603100f02130501020d2a08030906070912020604120204090804060f1407111002030c1501090f05040302060a020705030f0712121803110f060709051309 77
    0xa090300b02d0869030382d100a0b410051200390113210752a41c591400016000301c04081e002804010b9482c1520250704800c00b4044d00001d040d54001c20f11904100da0183c100c1102d01940d94811060245036814903150301078181000c0c02c00078010040c0718002e0001304440c0e005808035191140840e541d07910701c6000101101010f5030203035082c0700811401c002103800e04e07001403006000041000c0140e0b1880096040b1750400c00000d1400002c0d0541d01d80c004110b04035144006000340d0405a00d907966508400c1e1010b034603400f58296800c049500ba00800a441c0340348465030680302c1c1041d20000c541c16070f003000d03c500c80380d150808084911030b41d036038403515000300d405501502081c0c1d5503100110296101c09421200381c802003044e45440120400940f0782c452003901d0440b410131081e60b0040ca500401e803072144100349058080e402d40851034014941c102c0d0300d800c01c80240304015061b581021201c2c00d802e180d50007410100420140e000580c18161102100c01d40210740e4070310301c03202c103c4400d1900 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 421002059 1250 421000809 421000829
    0xf0e0c03070f020102090a030c09060608060a0504021c2904090b0a0513020402030405031e0313110a0909030c061d030d02160f0c0305010507080613050402120a080315010207 76
    0x104000c144030b000c008204180c240005464018400d011130303242c4206520584090320307142e0060000d00540d00400340203041b185001001418444001042110903200e02485981d0010310101d04c00f088040c903036881c0c50720341e5040015040c102c40c0c0000c0c0c06d10300340201c2e425010100d403400d04c44c44d0912600042d1904003010204a03912807035808000c1c00058240080c1e1402c440042c001a500c0d03000840c81988184060368440b81d4019001c4041d541e0404900d1003000f00344100800080c008100003601c42d0814400c94840c41c0300008103080301c07181c3d002081000c3c10030304100c061603040209407000d2407182c0010802d911400c50300c0c400c0b900244110b20324540041005007101902500039090250340280102c400c088981c0e2420306042c2c074280b04507224107000790108184082071180380c1d8400c6190800780c0c1d0b140307000d0000400e52014500c4400345641d6444c0800c0030b6481d95100d080301d80700700100f2240f11000c54105a03000e84c108031550804151502c0403000030703501c042003800840b02c4200c0 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 421003309 1250 421002059 421002061
    0x1809010f0609140a15080106030503040e010f030515060f060c06190b03190203010f05090f0708010c050403020105070f0611090f0f01050313080f1b0c031b15160c0f0e0c03 75
    0xb50703001780185410305441058441800b103401a028850341004500c00c5008540d6246402c0b465210107505074018242000e507d002040403c07000b0441500908030150b4040700d0340d42c0d00780011030750710111210a400030390100ea0100b0001c03000a6450007002d03074820300450a841d0b5a038603002d0390f42c6e80c0c2a1a8041d00000700c207490303014130400e17440021072005001080c0302c11101400c800f01c0d501115010140d90001c07070400507500c1c091008801034203004009200100290101612910640c8402410440e0000ea5070040c081e0014280c07910380c0d40204280520340301803140308030030340000741424070035500d104102c0c1041c504800c020075600c0d0103845803030469486545440c1c1c0d0542c00c440585220004100c020440d1a0000040c450f0810600e0861280d44070030303601d01d207800c52142e00180079601044001101c03440c06002c044607800304032191696080c00c10000041c03405051841848100d0b80c205500c1004186510705041c0c80d0b0703082c400f030f40850350703410482102c07a02682c104641c0b407004c01c = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 421004559 1250 421003309 421003321
    0x60c270b0903010e190b10030503180402130b03070905030a020a0e041e05030406110c1f0509031b1002060c070b060d05060702070317040503100b1809010f060914 71
    0xe009041105030003000059a2110588280c0c101201c0402541c0442940000b0341c00304040000e03201d030001c4100014258150842e66855901e11812002c07403010003c21100200c1c0e0303a03480e0111948902d24070b03142d8800d140d88030304810190304195070040c0480e0303e0500104003801c001940100b04e640040540e0540740c81c00503a80220400540140c3c0e44049000f0003010b400318106514185038807450003165200c0c030b0140d000f807041039980c9007070055170010149402d55645001008801c0c402c000190701f0b10341c2003071078142c40520451001c00d400d4010f51070b1031008a80d10542114849405a41e030780c0341c4408404007242c44001c200d5040c080d81d0020701086020a00e0541400d0740564081c3c08040d490040340c031154039100c42102e0010059011550500c10402c2d07010344056a080c5900314282013605010010b9195a4251000da110517030340c1c200109182e881089001c0064642c2046140c10b041c2850068007820000c04150102410720070b0024002c41540700b2080001004428407109464007 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 421005809 1250 421004559 421004579
    0xb03100905150a02130b0d0c0c050a02010f0201023108070b04060e03070b1204060b01030e150a0b0907110f06130b040c2d140904030f0318060c27 64
    0x80d00d0b0411080c0d00b44511701882c0568503081015015070400340740c030742c80422a40c40c00d0304c040a0612040112154803000011000589120425030900f02001250207081007240240121042d0391a80c29407141d8000d520b102c51041c104800039505040d4003580c1e22100b110790740317000c0c0344a4064541c100300b104000310f510901850305921401000e0f1800603a5030400d03442070341c200140d85e0001240311028002041b40c640b00c0da070103000003800c0c10b101f0f0001d1001000e0b152242642d0380800340240c14001404072586a014100c0c44130000c040c0541c60400e000010001500080713030001034410100d400d80c03502000160584141e54444403d042c400e02a9120002c2907005041124400444400800e00ca001c0e02415290b421601c080006101042c1125061401300795100d1040c1c0700c1480b0004900b80c40d0405031590007601818207a519080da00030450080544114201003500060324100c100700c5171360070112403182c0035504c1b00380c5510425800d450070100c54540074a070703490340301e000c004803060 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 421007059 1250 421005809 421005811
    0x6100b0f0310090501031a1302010914011e0e240706090303181b050103050f0402060304021f12050a020a02300c010525020712080408030d0b0310090515 67
    0x44607000b4114550f500040016940280c00441e0380c2600280448550110356650581c04090310071026500c01e070b0380d00081c0c0001c1c6207004100f040403034a80c20fa00f06034003c00c207041007550024021801c1c6211a10000c0c100034458540e00e00c90b081c92091008039000900540b000b803c20f00724010300d0240599a20300003400001c00440c00d0540382d00010781c050756007801100c081030245001510b214541034140740c29840540015061524090070b012000600e01c1d0010f51265040e141240d41e80c640c0e000180541c03001c166010421b1800b03600414007241c0c068051090494000400d011503107580c1c440c2e5084e4054840c0c1000181d003e910041780c804011800c1d0344605030269440f040e40454402481003651002c640140169120010712240ca5907600c058116440e5440d0103c601e0303200c0500007074075860240300f104001d90468402c8424040c6940c00c4031b008160841c21a96100c0322489050302402c5000340840c4a070080840841848005000e0345601941c040040d0508c80058140d04080640c = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 421008309 1250 421007059 421007071
    0x30b0901080616170907080d031104052407060b030c090601020c010807121a12030a080f0601051603081e070c2004230129160c0f050306100b0f03 64
    0x3444d4400c811015860740e40c6000342c1070789021b407022078148558285010850851081050310b0901b109440c140300b1320070340741900c03002c890500300c25042e403840c60000f140c07085c00c0f4910024002080d404100069000c0076000c0026425074940720f01c242c041086891048800c00c1c003680202c0141c82c45984100f203a00c1c0d01c00e105041031007508081c102d040c0c3c112950118800c5640ca02045042200d1804910412070040780c14001d5281540600004015103000351540b03ca240b00c5201058490780520300351401003c0300003949288810500b00100441029140502d1501d0801141d42d403010900c1010391041c28161074028180d2050baa41c1c203d1045510800200040b850b2040100c2d56124054450201510804a504601070500000c41003070103038803903c1442039001100c42c03c2d2410015002c0007032a00c081103500d4501d20030802481420f119002080c0c0c0b410420b01050556000e20098240e400c00d400b10b407040d507210100081e00c0e8401c1c1c0503102c10040b0921004003420303510f10003158000 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 421009559 1250 421008309 421008317
    0x2160b0a050c0702220513031101021926100e16210608060f1b1606020702220e0d0203070506010302041e0507020102040612150605210a0606030b0901080616 69
    0x5d42c0d001c440f104079001564202c0b510804100c0e401d0505a0003040c0050555103840210700d44900c2400f01e041304081605100c2c00d2214039000110450804a8404021010503d2108180c580121229440682030198030300c41c07487c55002c41d90509001c14000310020039619082e020140c014040c0c128505824105410a900d0302000702d50a10144400341c040c040c0000080307554109552040e915480d030300c03400e022f001c20522280701d401c40502401c2e2000d80d002400140d4980c1d1500104100c1c684151070345071130b01803501712580c010740c655114502010300d68042e07e80000703120208903128841d20740060070702d601080047c00540b0300f0b584690000207855a43c0f40c41089005500800e440040355601d004d41d60100d0100290390304403402d8581002d06207000c2280342c0b88c8490b80c2002e80014003d80c0100300e00405d0031400d0b1024000c81c4d40300c0f12208c15803081140703000b50500f0003034079413400361000081c281480c8840c0703400d10030201c82c140d0715005c02809440d074032810382016050050719080100 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 421010809 1250 421009559 421009609
    0x20a11040b120f060a14040c06031a0607140712020105040506090a1203030204050913020904030305062107031a040206031306110a2003131e03050102160b0a050c0702 73
    0x1844080001d09603c1c01a02d000d010030380b500c03051441c06c8078000c42c0041500a01e0008001c001204900f484007a1885428000380e807052015014030307200d0202c2c0c41a500507500207946400c1c88a42c13003005c642060800e080301c1046032070380511500c01103040c17002404241d040c00140013034a000000b5002c07011020380311001003036071541450715a540012094002c40c0e80001e0603c544c3c202910640d50080325000031480034001035010038803582c00100054101a80c039008654540c0c5c81030400c001002030003014501400c400f01201d51a00600e10045804141d800d03512910104014001c900c41c071340040c5160304540c3d5058410030704a400107421103005a499101a0920700c2d010090580000c403030b41c8084142d000000b0050020500300c100b800c5c540d00c180080e4103950511800d00c030580e05010000c1d00e01544d094020940948a500024595400450300400b101c4505007059482da005050035403d0340c444840e20f0301100c00540d0300300d00e04c98080008102608280f00d0113410101c44003030741104 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 421012059 1250 421010809 421010839
    0x1507020301110d06090204050d0609170316020c042703020a020d0f050f0a081902070504020315010f110a03030b010e12010501080f06010e010608042619020a11040b 72
    0x2102e10080c0103001039030b00801d2840c50402584030b51005010f410f0001c500c6c1506200000e00c540c0401c540080c050743c1c54190303917400c0110001c0280901d240303c0708802d4503404d0940d02240310310710035803d14006208640200306140b600b4091120348001e0046032080c12603a000c08442d5207008410254258800d0a001c4001610f8203819180810f02400c01707012030000901e45182001c60f1100901100d0340020a4000800e080704100c460907084001d9801c007140c9107aa007a03013804880d0740702d0355019102000300f15564207c0c61510b81c420b03d003640c07500304801c03002405842020700d410b1600c007071f94015884400020301945c0f000800500505002c81401013080001e481c0350b80a05003010301e41d441d100100004c41c001c004d071100010010010740f13415814400c800034100e0f01481010100900480400c080c80540d400c802003501e2140484c01c220200b1845001166100d03171100f2040044150719440340c14800311302608001d921110501203011a081000003500c4110b949582c054511012549 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 421013309 1250 421012059 421012061
    0x1060b12041403160b06010e01140d09050f060411060309070e07030905010e0d0e0109080606090a090807060c090f0e24040f060306050c0708030a0e0304030f0809030601170c1507020301 81
    0x44c280c406144044114900303890034030f400400150130307981030182907801070b11241e812509122111110500705c0751070320921029400600b5243c60080c200c0e00640c00303100c100c05c4010070480d00c243d001f0f0300345600242c501020711000d803108540e54580c541208000b0300100b038120303800d9074100300d03039260200300c594054960608503400a1000303030440d031095112607500c0740c00c54514910300d0424200442c5c1140740520164482e0002803a0038403442a07200010b418055550000291581101401c0e441c0e10b402c1c07602800a00c0f00c5004800030800000d00005c015150f081040b09444409103180f281e81c95126541c10b20701901c860341d2140d8282140e0800041c0c480d0310a018007100d940202265035840c0d03040c0a000c03102c02a040e0349440c80e0410410000c58a03000c100d82c0c200310410000100110141455804d601035a00300801b52003a4180007030603c40514080e00300e05804030207441035a662000c0201a03650510711208107030704442c1030f61138645840c1503074400595480710740798a05011030340068 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 421014559 1250 421013309 421013317
    0x3091c030509070f120b100905100806151305131b06080604090206070b070c0f320d050c030f160c06030b060304061a1f0f0201060b12041403 62
    0x580000e58900801c02c02c0360080004000030321341019030f842d165042820941100c401358001804040c0031a0205001e002c3c0954100d0007006440d80030005401c0010000e050543e240c402d1041a100e404080341604688150500303221600030803910707000d11124403a002404004102018000405000d0703008142c0d0304413191a4498030704141000141050805840b00101510780c03400b42e1f10304942000140c950302c045401076030304a100184907581e03410017201c641c1c018610051050062103d400204610814444074648501402ca40400b0000100318a4042040000c0c02c0541c0240024040070303010f240280090380f01c4000b9245406d2444e0600b261381d5004800ca8524202119880020b0000c0740c0c240101521a500e02401815140030000f00780d804003520160101d50740d0b94010300c10040c1c04585024003080a40034001102c0401489090403209a006101003007030440c4c400b903c01d1040c8214401d0390301411206042c00b8042c44407283d904401001190603151043c0d04241e068800c0001d4 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 421015809 1250 421014559 421014613
    0x9031212050a15122d06020a0c02270103080901020f0a050a0309080a0305030f06120d0905090a02090a0b0304080c070b0c070b040501120b01230904180b0a020309 71
    0x200d0240d2003c80709200d01a06a8007902100e01d0038042c8800084031600303204d01d00b0008400200001180075100c420340700e40128010f014920000c0e61001e0182c10000451500c3c0c0221056119444000e4180740e0071440322003000c0030000c605c001800001e030044050b003411203041c03040794007a80540d41540e2805a0a1405031115032000400f42c04065000300800094140c2c10090320104d6800d64025010740400703842955001420400114241c8a12841c6a500b100c1c500807512140140c4801815902c05c501500340a940038400203402c1010318000c0358122400a45000c24892070032010140f2500058001c0f51074420400c50002003140c2000428040c0c4066811660364001101c007261402d122607000c1e11100a0502040141e81e800926032140281000c0d000304501c8100e10040b07840d28100d10318130a441034044818989104440c0c00340c03084001c2590b0030000e054a40c100001546c82030100108a440b281c0c000030705000e41d9401440e0040d900c0c00894040740e140101900b1044150020 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 421017059 1250 421015809 421015811
    0x507050d030f15260a0206030f090c0603010312030c14040515040e0907180c17040501061a2a030304021909090803060f0a050108011a09040c02010608070b0a09031212050a 75
    0x407544c0401a051000d154030001c00005d041d42041540801e0050000802c0040c010350300c40b0001d04401c0307042c8104020154010082030350b135a10b0b8581034401c02003107148240040d2038401c50405181c09020000c0860352401942400c0c6031521041151017162039200018848081c0800642002041d0090303001e202040040c080f1107042110000c10840c003001c821726074600302000600440c1c0c002c001040c80c140d002103030802503074503810201d01415065020044a961402c509000844d21f60094800441c54496024007420650750140452040c1c135110105a001040410010328040082541e20405029000a000d65500100c4e089a80c174070010f407100e0710008200641d41c580955108000d0908441007180d0a0420000a01468cc14003a031107040382c45074501714041d0444010394160110007001403080422501009000e01000c0c071640040f40f1030700c4408101e1140c228240e90b001081640c90181c810300c0d540342c1b0408440103003960000e1007000e45d000302d50310300c45008951003040d40d254 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 421018309 1250 421017059 421017089
    0x306060303080a0207020609040e01021303050616021b060a0c0515010911070b010303050c01020d0e07321021090203070f060806061b0708010501150507050d030f15 72
    0x20060010103000f088682c800388108140790050703540d0380640e25007090643d000980020090140c13070082c440c105010303448100342e800000420200040b540c0c80707106500315080c2800c894401c10303a0348614200f500c0c6800480d0490407491410404040c0c440b804040c5403001032071555031a460b041281540d02c1c203901140780c10040c04400c400b4041c4400055058903035528000641c0c0b5014800a01030200500f040800030f040815480c0c01d4054420070000f80d4810000d0102d120840c41d50350b241da202d1000e00480e40141201003503484022250303c004142c144040300e01da20420412031211184041051002d03030301d07540f07a5100340081ca41c0413071502008000303000700389401050301d0244194043c9820000f0444140555a403206003240c201d40203a070150784034110358120020748150462040000d100b0b00d0b00009595205400c20790403038801600902d1489011002210207200300d400c080c10f240c0c03205141c0c6001c14425031082c0c42d00c000d00e00e00019520952045442c150b12552306c00030100d11889 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 421019559 1250 421018309 421018313
    0xb04060f09140102100f230105090618041101030617030c0f01020406021011070b0906071b1a1015031d010b0a1205120d0c08090c032109040603060603 66
    0xa40755001412a4905a039404400080002d6031100d07540380c601e0181e1340b6102c00d4691070034190030420701d00d00d16242c140782c8003043c100b403d0088403091081d14420400b501c0840c0d114200f151202080e42d030310b50301100a59035181c440901400e50722869034100340d42e4600c000b0b1408102c03411011071481a2015568408200121a00c3d02c022000100410391042004000e2945c0005c4c0040400820360380214841051155000090203007041c080c100124410410007111404a00c0601c141420780716040c550420221440c151046418020184541c283d840c42d1100745140a035680203102c520600d071850703294100460010b41800f405030110b6112700700100040e540420004081ea030000003000000507400000d0700100251144250451000412006109083c414a0071194041c2c24071903507128040c081600a203001c4956070009a1030002081d828000403070712200d4200d000300245159011840b10fa039100c1d44600307039049a03070002c200d107081c0c580340c901030000110700030300c00090528954 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 421020809 1250 421019559 421019567
    0x807170f0613110108190903030b0604060e0a08030f030105090a0f11090a1a040b160803040f02150717030a06030c0b0316020d0c0602090a05130603030f050913150b04060f 75
    0x201010f24140505101000903841801d900a070000402d41c0c404640e001b0607090960050190300001e540140d00040c012485640020b040383c8000801d884038038907595107034200e5840b401580b6100b04078990401c0104014a442180550400c1f0700d51000a21300c28403a081208070703095202c030744072911700100d081c0c0c00601d0203400705170051070881c80c0040c2080e00c603c0002ca06104a00404221141c04215459000b104d4803994010303d0b809010242e590034503040c888000300102004030300c6162120781c80fa00780000d0b807090300c0f0030302d501200b00040c0121b1481c2400c2e0301d4000406178084039648260010109080107860401803258a036007a6590401814001504080b14105019540030804000c0c0480d0b2048096500c1500076a0041c1c45d2006e141c005001d508081e4400c540c048e02e544060b42e400c020b19480700c001c03244251501d4a60482904c2c040d1400d025000000c1c2d0721024504203921224681c0e002800c0c0c0519070665440101c3d1140c1c2d111010781c1240c0c00c81000559604250310b00d030340e04 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 421022059 1250 421020809 421020833
    0x141503090a121106011703250c0b04030b060d150c0e091602030a0c05100c030b12010510030803040c120c21021011010905100e060604060807170f0613 66
    0x264500f034030580c0c0c990203580d951058188203c49821100c503440c90302268082c802d8501d0401201184c283c40e0034100c00c04000528a0f00c42a1340048460100060604210045804032540700e0302038025650741a041100000320f0300d200740c4901c41d0810f0a00e80c00300040c03150140d03c5100b500e45176805103900c2c1c1442402040100740b89031940c1c012070000070340c40e0000240ca0440c001894404205059454000c2c01c01f0768080a0002c83ca0900b44483e60080c1c243d000840031000c10f8490131259030b5880101c0d8260b03482a42c50511101c024841400441c0c50b40c00110790080c050004028082d035103d80c60384032510003100690f02ca0115603c01d004000495001d04c10642d10b103000111a030b5074170780018400900602c1030600744442d0703500780b500703074002074100554058100e02900c0e603041c042001ca101405420200c17030010b0080000055591409106031810b580d5070300d0080201d00c4c1080c0d094201c501d1100c020300c155104254031303e6443e441c204100c42c0714007810100081ca80959180641003042 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 421023309 1250 421022059 421022093
    0x7180f06080f0604150204030b0f161409040c09030203030d0501081e0c060c010e07031203060b040b070b0c0f300403080a1508010906060e060303040807141503090a 72
    0x25a1144220160001c2c819802c203411a0317860307950488803a442c400a114650004100f03c0f610020080480c0703444000c80e115520074403120070280741100045400c8651800c0c0b00400350000d01003001141000d0703000d50340116083c1485d200301d03034072900000d01c0c1d50481c4240741c03891740e207400052140640511143c1c003161000034410021801107421030381c0300c00c64009040d000383c1010030380201d0070009401c8402041c1e401d40507210711036161f00b040c0841741c5c040040a404a8103000d400180703201104200c03812159035034200b60410078a90340d01800c601c009401c03442490700c02e20900c132176503101d6030050101038080d41c0c80080c1c1d07001000854440c2605e107104840d40c4200c000421000c2500030190b030340c0c40024030f080010300440070300031805104442e0300304a21562030000b0020401000d94400c0054690b610706075010360b0740b21020075a507449180900c44140d00940420800207028644556420034020034050024446420401c81c90300211124012a40b041e0000820704c0344c41d03035070300070040707 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 421024559 1250 421023309 421023313
    0x15020307090f2117030f04051903021002220605040e01090b180901060801020a080907050a120803060609060a08040c0608101a07020303030f01030b092a0307180f0608 73
    0xa00c1c080c168801100b0b1200110f0240d07555043c000100140d40c80d00c03403030100752034601c03035140d08011502e034407507000c1200c04460511480440700b09100c400d400944d0b029074035074010010a89240401000703500035400b019403403d100700907030b0b151307035130312641c0f14064215542e03441d465500e80007541c40100810707407120350b105e460040d50209035140c201004600c54810f81f040d40d941c3d100d41071498010080759000d12015480800d2202da101da00141e1170703016540c20411100c0b41c98481007000200340162003481c001d21001e05590780010010300107564848001800203040c100304074003185c02c0c0d510400038070000031b000c20108403c11511510360406002c0700c2c0340c2036a00d0300d0a000c101014203014001c0c1528002900d105c0b1424011030811144c91313941c00f40940c0d4880c244528201ca4268084c081102c00c4422a000038282920004200550403c40060060070210113140e10044900740c2c1903075030300743c0510500400d0410041502017101d0b00000d0001403090305040078442280c1c90390300441115 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 421025809 1250 421024559 421024589
    0x10050a02061014060912070b092d0d06150b04031401051b0c01020f040801200307090608091501030b011415070602090a0e0702030d1a030d120204031502030709 70
    0x40751054840f040d08182c2580c0309039469a044c40060a11b01d000702c10310071144514a40420020000300103000200d03010755214412043c3c03551019a00b070144035817007018540714040010b003450700c410220f030075600075000041d03500401020003582142c0e640021a01c15400982007082000d18030701680300c0c042a07802001982020514003090b030300108820022041d0100e074000b0b1841082d412915140486404180d0782e555508209000e0500c1000c42d0603104001c2c14804459011b05003220310800b1590b6440c26014240700050391030341c50180c50f0913840c5c828201e440d6943d001401180e8042c60046511503a1589000c0408114801242029004081411110384a0000d40d03007540e00855212001684849141c3d01080010300c0b9944040a00c40003e4244026075130044000c03c5901d000143c14000a210085500610a0b51080b00e82d01079003d03002c1c40d42c10307501c24608a8413044a442015151541e44d44487c015402c5942d00344101580c000203001800e1381001400e0010686c0c40302003286 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 421027059 1250 421025809 421025819
    0x16020c010804060c02010b030316020418030e10030b03011e0c020a02061b0309180702150114040504110d031e08010e070e0103110d0903091e12060b10050a020610 71
    0x1d20100900000d05107503c0d2400803500300d00079088000554005821644c0f01c0c090b808080511a03c4605d06900075450001c40050301c00310b41c1c0e4003086094041e160307161612810740510032411041640340c4101595810000165075080c01102c18520303c1185000c1c0e240e451410100440d0500c0590605660007081c0440040e01c0b444243d0b11000c0f0b482104c450650340f500d50040c02e51042d100709681c03109044440f6181c0724014140c090044c1d005600f212041070048459080d40030f400e014035001d68020f0022041a4901600265449413080c1d121102200c03d20b0045590070700703244801c402003a40380c0304070300308404c109030746c4a280111850070303584651502c801540710351009040c040400101526440c0c80c1d90198000c100701d510088900c030340c0e46014401c404001c11f004101100007484401d03001801035141d000403244e1b20900406c0045041c0b81030030030145246600d400b2103071240c9840b4070100304d546400300d401d0000c0682d100d04d969907150200013404c000c1300410310803150900d2501401 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 421028309 1250 421027059 421027067
    0x3030902030601061d130e0a0b04050d0c0804140d0206180301050a090201080106081308030406060509130c211a040311031326070603020405040b030102030c160c0f060816020c01 78
    0xc4043c0c0c2c0c040701186c4a11103402c042d00310f200c0c81da07156120396800f9800700183c1840b503900c50380c012416614110010041280e0005400d900500701c83c0040c801403190b2606840043c0c1e80d4140107002031000c40181d400b280c6140c001424661001c5140441c500c41d40c1402c1c02155404480c840c01000b051840f03500281040c2818041c2d502080115030004e03904264100c9402c1030903420601706604c9140924041001c0c0c64240078030f038080d04a1402103411810b51941c08403100c1d5008201680240c1070002c0e5429284c507100c80d14800c2d120341c040317100c0071a901c00c1700c0b00c41701d120520b5941030170b2400d403c010f8200021512491065801080610201c07800500c0b980166640081016802d021486100020034100d2035403480f01c2c0108840014243e4059008004070744040d80c05111405402040500300d0000320340381d0b03184103010803d80e13032481c0101c0b0307000b9030301c9201e05444074016854018000b1112943c0d0032030004a00300c8070500001207051030411240e804a8401440d0391152580002c1c = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 421029559 1250 421028309 421028357
    0xa210c021b13020a170c0703090e070f21020708030114060313081806131703041406130810050a1401030f20030f061905091906060e040303090203060106 67
    0x402c0d240d60102d44402602e02c200124459078a9a801c4052107042101c1034684139840000110041000f104002031100010f0110b103105e0442d90f1a080072000c00070b0b40555010b038000542c3c024000741d100c407080c2c202c42d0500c080e141c2079000703404d46500d071342c14017110b1040c1030440c8100c20b110300801d000b08031494040788a1101e215a01100c02c98139810b94140c1480881001400242d1102000c40c031005180250401203080b42c4804201003400a140e00105459118074000d0101c41c86000b0b22114040c1403003001030484a0900030901182540c03101c840c0d040501000c0b810f00415100c106000c000c0301c081c01440f0041020700302e0050554910b03641c07481070f003200000c01482840524406805401c1206ca0107800c600090196002d00f9200401643c80302c404407170002c0c0f285150510380e6002d00c41131041502c140b4001d0001c09102c8180340030784603501e44890040b0382c0d05881c0c94011031078204221105001324801e45021800c117070140704050070504160010010000c0000032200902e15500c800 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 421030809 1250 421029559 421029589
    0x60803070c230a0611160b09030705060a050a08090f0a23030f03010303030902040605040203130b0f040210140d0c121a060409022d0a020f01050f04080a210c021b 71
    0x5046505c0c0c00d070070b034070703041140b500241410a44150400513180301d1a000414404e0421001d0b02d413101c1d00d80041080303d004800315040052014460031001c24050300400750011400d07030403520070003149482c0604d00000c001048803a1001c0149203030380400700c2808142201c031404040c6040a68050010045000511000d03082540f42d84050056450b294414000303481d0117403055550b86042c0e240c1e42002d1160000854111506000060031800c02808240c06954010311031480141c2d01c0104988101404103040040d190030040741c81ca4403010310034102040c0c1c20b0384802c4c0303403100760707403240d4080b112080344006074414100c00f0960a90707240d40490b0284c0d107240c82c0c0140c98080d0251100901d403000c01d540b00e581c180c40780024240b400084090000801c10790b00326007908030f50646182c01d80b00140c0e0720300c0190713008001280000d210800034108040f0f091a103c4041d10342c41842d420b2180c00c103500903580c1030f607448924020960501c8101c032680324000c50302041e030b07202c1030100786941e40800038 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 421032059 1250 421030809 421030817
    0xd020d05120a1107020a080105060109050a030506040201030c1b030c11010201140c030c0403080309010209040615121a0405040c24020c061602061c051b1903060803070c230a06 77
    0x42d00c0c444000107a84c0320381d40240c160709042d030301e84030b00900806090303900034085506210005424a000c5205005032940440a0006038a440c1e00560107071004281010a100310326421000c2050070079280e4074001c0c082e654003444500d95081034510302003040481d50459040c904211400c0c81d415840640000900d450b07941d481c0d03108051011207000d45e4000604ca0b5000009114814005402804440c2000c03602003140c40d954121140c6600901c942a1000ca0062480c03010000d4150b4801141071101380d841031802c4444100040440c0c0d02201c080b0340351000020103100505406172802280d10900c900d400b44084001320180d6911a2211800c3c17151500080042d00300400e0300039450440d0703010340001d03140d02c45209010702c080412220040d80ba46050700090001e10000ca4100020a0248006160806000c0c0d01c1180030791003280c8800f810307103540d4001036440c0b080004180b01c502a401c400360260914544040f10820150503541e4981080c0301c81d407103035803807000d41411188035041c = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 421033309 1250 421032059 421032071
    0x1407140427051e010608010501150f050904020403020402030a09211b08040e01260610060806220b270601051308030a0c15150510020f0a03020d020d05120a 68
    0x6400b501e040c103100407422088500c11401d0f110b050054001400f0340e810a0000e00840ea242c080c10200a2781c0d6801034000158080717007520026009070010800d03103c020b00050329041d00c1e034010034280d034404d4513801816a40e481c500420300140000400083d039140030780804480c95071000600c140c01c04c107594802d032100d800400b410414202e0850307009004a40c00b540066944683c1c41051b040c001c15005140300f07040c00741203854180860524810000c000048031000c1c00d0a40440307020714000d0070b05d0b03040a610500003c50018641c40000750581704c91011036031030f4012042c0201c00302020b02c000c0000b03440c8110810180c1041e4880c0d41e01100a2900c01d4444001120111201e04207600901c0a800001104201a940210442c06071405508801e50514048035014200e404040300040c4120840d0411f0115142100d500110a02540304036000c0f400d006181c5420310601c110201e0150b803000d01c801010540500000c0c000a01074200030b0b0030703c01101081407205800500010312155070300 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 421034559 1250 421033309 421033313
    0x3280c21061a1b06010807061404030b070507050f0109050c0a23043801110c030606010f03020705070b04150809060f0a0912020d0e03010902031005070c1407140427 72
    0x101c0075802c8200131904956540e411043d00c0d94221701031940010740c604100c5040404100c200ca0450b0b0f4000d41d22141a540c80604580540154208030742a01035404900c40e0f13214240074001010740583c01401d00d500044040020f000050703441000001010707510315544d0304e8072401e0562140b0382a2000304d80c1c628150096514100e01420700e90000d11446014101541c1c080080707501d6240c00c1c0c9841d8105200b000f03403190380d80c41800c0165410741c0000d00041c042e5104101e0180260f107142805410045959141802c0285540020403203801c0403c0c1000300d00140c3c810401c04104c40e080c40c94803070034007403204d9031075450040c00c0600c0382c3c1985006ca0030004c540d41c440280147c10481c07a08000d400380c540203444844145007040042c0d140741c660305080c6410320503045c0300f0798010000e21050b003d00102030041d200003400101070002100362440410000c9240b001540043d00c081c0c612141017403000e034003813803120720701c10f0145240003a01e071800b103d030300180356840c07a120040007030146840c = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 421035809 1250 421034559 421034587
    0x6090b0f1006082409011502060a02090d110a1a090a090204030b041b0e091501150e010c3206010e04030c0b0603010605060d0e011b0503280c21061a 65
    0x10444c9410404031000061200c1c500401540c400d0002d5003a25415116801b095043c2d01948079581c0c1c0c006800808600080c0b82003810105021018001c0340290759610041c003060000c5601801e05003000145281d0180b078080c0140d0007601980c9803c40c1020704640303c03c124050000c2000303011001800c16941041c004000e110005c00c00707600c11340d01500e40242c80031340342c0030131480004501c40c400002007001c1d906101d0320303510b8002c1e40c0d4600031f08503820001160749800001040e100c4003d40600f40200320a42c100708042c0d02208a0318441c4542050101ca14020059000e011001e1807901400300180d48002ca807588103401a08103015510340320300190040110b0360080358000000100068035100c00d070072500c3d040540e50001c00c10030691407601000c000d03d134520440003803010030000314500d80210301d103070112412a140c2107485030003d40c8801100d542d45a68004110300c8500c021500072030b03411050b05880041d00c1440001c2c5805080c1558851082000008210100b000c0d4040e42c40 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 421037059 1250 421035809 421035871
    0x30a0605090406090201230d021602030d0c140319030e0c03060f0a0b030102090d030c1703040501050a051501090e0702030706050411040b060a0c0b070c06090b0f100608 74
    0x800e01007203400c092528a0080402400490200e41800d04440d0440c1d9200c40c4040d040e4140500b0510305181044080d00a520400c01000c00b07240140c08500503850400110002c043d603501e031480350794100c2c240ba62891690a07140201c0381d20810140344000e40c00b841442e1020b40c01d040102e81c644106003070f00e0800b0180142d030382d0144038a01c00c00440d03441c0513000500402c40300038104410704040b0103060a1344214a00c407500422005d1802c800a8404d04e64164168015540903000160404078024954000d9400340c034940c0d16003050000c0c00e841845a15084104048481807010030600041c014103400e10500041d00d900e00000740d5114001c1c01202c64995002c0340c10051480d007450484110054910707468080c520b031681704805818014101d0710f840003a5201e140c1d0410031965910131b0008000d20307803c00c001c0722140c5440061903900a40001d18401e41e404071452820106026607107100920181c141c0140420400c4440c0d0012440398020700070034504141d032581c002030a00c101013 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 421038309 1250 421037059 421037069
    0x90102060f091f0e2b030902012c1201020d06050109061e02160303050705060106030908030a0504020103020706232a30011e140d030c02040f2c030906030a06 69
    0x64038911160760b80c54001241500a90121462400e09941e80c00c46c00c0300e80c4c0a800034040f580070424810b40e42c2c0c0c03400d0360310f001000205010070030003000300209444140090f0006540d070340201c0e1640c40c481450041c14068102803030085001c920f0440000c001460f440c14440180c01841d0781c50b40c02034800e05c50704001925010f141d444071035491500801a82c4242c6080e2a5401400000b28545120380074440003180c0000c2403e0071a02e6030100000100340242003241410350030050880010307001d0040f00301416416049103803042c0c40c1c42035460a030400800703910403003561f040c1e080080103d2540c4018450004500341303403201001c0c202c44802c6503c0050107101c22600002c140c0c070034101d4000041c162000b196104d030300074220000102c0a01624001c1c25520a801100320040e42091100c5200183c082c0c9042c2e040c011941d00403504580d040362070483c1e00c6840e0740000244c800440b1801d021620b1440003000540900ed40d1070b526030040e00c03605803107110300202151411800340c1040010340 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 421039559 1250 421038309 421038313
    0x303021b070f03060501080303090304151106010b041503110a030f18120207090b0303070201030b01021f06050f010c0203030316170702030909060414060103150902030c090102060f091f0e 82
    0x55141c0719031402c0104644000c480550615001044454022050341e0003a956003004500f02404d00000c6101001d801c441c01d0200801c60011090844040010500030019101143c0c0e0f65070038440360b2104090301c50041c10500d400c12900d00c0784002ea94048400c4850145000181c05800340c1201024003854001c1c0c80c000350004c00340c0d100b030281205a0031091201d64007180c150503618155001034074030744002a07505420901540e009540280c010750011481441504d512001c090035840498030002581130800d030352264140708508002e0b524064598003400c00d04103c080a5001907980c3c40002c10300303051002d80d000c601007518014180c4074000701d031511001a19207003001000b9502c0e00003d6440f4890b1074104003050705410140b1a0419a0740a404504003940d107030001035020f45100e1380340800c01101d040000810940030b2004e14003c4039019031030b542d11400c25000928140001e03142860003401d8078103000600c0000036044040200342c01c03220540006660200004180000e1305000c94 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 421040809 1250 421039559 421039573
    0xa020c0a150501050102190b0a0b03060712060605040b041202010201110706150506030405030a080c0c1b03011a03071a0d0603110109060807120915110d050f04020603040303021b 78
    0x101c003a100c0501d401c0c0060354104001d07aa00c07801240e89001d02e51840707580080344640c85000c110304515035584480803a501003141032039080031901d0540f00f141d0540c00140034209441888445008100051895103800c40c20142042d42d0f000326445203201e006298100d0021013030440e4002e4100307080c1410075484545d00c61186081880c0030380302d40350003241c10381d0108401144c85d04d48042a03034010394201001314100034403120190349946016107d1051503100748100314055200b04001104917958031411103004903a0801d06083d20b025090181c1005540f414807852078500050003c200e4000f038403245500d0031180c1800c2124840c2850f608010350410030040288407014204564048082c0d80721354100b559041c0440d802c030360030380380036001a803400c100c1c0345140d4058100c204214042c00340c0b60381340d59007418010121120030409a5008401007131070b420070800c610845a02a81c684102c0d80a0728091b03000461038800100300500f0b0540c0803d5200c62008040000c416080d0040122860 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 421042059 1250 421040809 421040813
    0xc0f08030f0124080402060a0905032a0906060708071511250210030e150f0115020714010516050a081c0608070303200304061d030d02060106080a020c0a 67
    0x745071003401035012a04010101d1000f440211000740800d0403281d440d40f200c0d0300c0355403c00049900c1701c3c0e45401080041c4e203003c80d5607682400040d402c840c00141050091401c2c0075013540c05146043e81d070b8800d20b20503007000311548440c2c0403142000c2d4013201c255a03412035442d10f00c140e0003000301480d80880c40c0c000c000114200010040440301107201310032040f0440c41001c4c0b000b45001400007034010f070061418400190213600140010618071003520900420000c2d005400c00c03080721196100d40603540100424998400030091030a0b00d031001d00301a500f4401c3c00c1c0c01200c038489060381017000004100e61094200c031030b00f910781d41d401000d84554188504040820750072460245807501c020302e40c0c0c2d15201603d403090004076100c04026289091070341e2015100013880f10520701410313400b4428502c014000b8001000038203920340340c2c240c1c200f040042d141345a48003580c00394000d501440c071406036a500011002d0458407107107003039085941c52041c88000307401014084400d030710500c522242 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 421043165 1106 421042059 421042081
    0x190506010c0807050102030106030e150c0f04120606050418021c06091505070239150d0603150b0a120203031b0c1503010f060c0f0803 59
    0xc4a40e5110700c105a80001001c45042c0d46c00030060140b990144214031034a48218002c00800241440191083e01d004c0c03e0304a80034008030b07400300000e10250455000c2d0000b40000207920000d440c1440c00350000b8041c540c070407030500d85000003d000300720b000e01790382d60000c22410701008150410090740d140d447c8291466500c1d06e2203038012982025000c8540d142d030105c00203041ca00780708001c7c1490300411104080750901401c002c1c0312005034034142c0440410484038481d9800c07240004404c42c040b6410040103030000300362a5140c80169007ca02128042c0c01086c480da140300c100301084880c0c030360040e64441c40900c03050000b00e81c101d020742100c1d0b202404036413510306a41c5040604107801c0700701080070303800300100a00a0030302c1c02640080300b5200c0142819541000f400c4d100c09031460180104105044164905202080b01c01c10269600180000e503a400c00807200710b = true := by decide +kernel

theorem cover : BRFrame.Cov 420863309 421043165 := by
  have h0 := BRFrame.cov_init 420863309
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420863309 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420863309 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420863309 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420863309 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420863309 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420863309 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420863309 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420863309 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420863309 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420863309 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420863309 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420863309 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420863309 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420863309 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420863309 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420863309 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420863309 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420863309 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420863309 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420863309 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420863309 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420863309 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420863309 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420863309 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420863309 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420863309 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420863309 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420863309 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420863309 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420863309 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420863309 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420863309 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420863309 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420863309 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420863309 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420863309 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420863309 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420863309 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420863309 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420863309 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420863309 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420863309 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420863309 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420863309 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420863309 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420863309 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420863309 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420863309 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420863309 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420863309 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420863309 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420863309 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420863309 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420863309 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420863309 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420863309 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420863309 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420863309 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420863309 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420863309 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420863309 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420863309 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420863309 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420863309 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420863309 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420863309 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420863309 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420863309 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420863309 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420863309 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420863309 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420863309 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420863309 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420863309 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420863309 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420863309 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420863309 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420863309 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420863309 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420863309 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420863309 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420863309 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420863309 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420863309 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420863309 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420863309 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420863309 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420863309 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420863309 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420863309 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420863309 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420863309 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420863309 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420863309 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420863309 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420863309 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420863309 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420863309 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420863309 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420863309 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420863309 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420863309 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420863309 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420863309 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420863309 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420863309 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420863309 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420863309 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420863309 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420863309 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420863309 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420863309 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420863309 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420863309 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420863309 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420863309 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420863309 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420863309 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420863309 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420863309 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420863309 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420863309 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420863309 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420863309 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420863309 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420863309 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420863309 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420863309 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420863309 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420863309 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420863309 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420863309 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420863309 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420863309 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420863309 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420863309 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420863309 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420863309 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420863309 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420863309 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420863309 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420863309 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420863309 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420863309 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 420863309 ≤ n) (h2 : n < 421043165) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
