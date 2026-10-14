-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2610
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:12:46.008828+00:00
-- url     : https://prove2.me/submissions/a6a88095-d5c4-4215-bd78-3733a9383e56

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 469244604 ≤ n < 469424460 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 469245854 1250 469244604 469244623
    0x504050412031104060c020f040b1008010e0106020d08061e0d05100f05070c030c05030904020d06050a0803070305030f07051303081b01110703030207080f0a020601140102010b010c020105031b0c 85
    0x32018000803c80c4840c160741c91259010b103c0c0842e9242441e00c0150400c114004040b0170003400008500004900099030040c48030b60032400500d1510041c082c08050b4040f2034010280340c002400c0340903e43c900604802002407a041c040c80100e40700000a40c411504441c001001030701044025280c0e04205031140714221007402c450723081203005000d400322440384070300c115900d940b2007110b200596400c6410300140441035480e80300901521102c0d0380d491005100c58a0001d1000604925280520428800d03c0d030001304107420902c101d1307000ca030700982101d5020b903104020300c981760b0310300c902034440f03010f0404001e40c2c8a410000110030004104020586034584121380007444031640700d010f083c1c1e203043d40aa1242da00910018001a000e90058070480f131203240c850781010700b13040700e00d1a540c1250320030310010780c0305c08010810030781c410520b00d1000700c080c4001d0000420074030010303202c0408800024104100000024003400084007080c501c00740402c1d0740340c1e403140f03c02c507020361780c0c8da940 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 469247104 1250 469245854 469245857
    0x90a08040b0c07081c050d0e03030a1a030303010b070f080408010203071d0d0c0603270501051b0702030a0308040206090a060e030f150c2a060f01090b01080c0f040504050412 76
    0x2c42010500381030010703003041d0348034881c0000840f81103858000c030b4441c1c0000389201d1100d500e41b00c22070b034208d0f0144059403280c4100080004c1406c3c08580408809082d0203540b03010360000c1005010305a654411a40c131207401032110014203001e464080c4482c80303141d000710881d51001c414001c180740e00c40d2000c2e112601500c50001c6220400041103030b10340d48244000e040904440d02045041d000e5008114503141e81440300301c0403442d4146081c0307506002c10040758180d660f80108000404115200c040ca11240f10b002402e0030503581c0826507407a41180050b00f8441844006421540c0e0007040301d02404000c0c045400d055039880014054160240103240f1a008941c1c0480f0261000555602410140103072100b041d00c850390070b1502503000703e603204542c81c00309150440d1400c061600c0081c2d1404e4000400300c80c60704207002c0f240703040b040e00540041c0d4100142c0720001da81c8080d0b10354201840c844840d81d100296540302031284100d5000c280c00c10708241c10441070111011401c01d000c08039 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 469248354 1250 469247104 469247113
    0x130908040e01090e100b01110604061407020a0507030201051e0c1501210b060d08030903030a1109030a020108180a0609050c0f010804081e0c0a0c08030a020312090a08040b0c 76
    0xa614140d41642c0c440580042150705c40389081c1c200406a410683e980035040c14640d100a40713588925090500440d8151660b07911086100c0d0105521112603501c201148007509100402c2d9841e1516a60244800303030421a01003041c450b6801c1001c0c001300c2e440c5400d40d0315941d8440079005580c4840c00d446030700010104620000a1501205a00d220712a60006524800261640e201c1412080150046410207060640d000000760040c009500031020785c0300850303c1e483e14420603001d6510700701c101c0440c10301c03c0c001c224050700d0020f000386945509080440c40c41e5524242480010340c5408001c426201c0c6038042c2091140f5035100c8140300e8001d90550b040f00080d0320900540c7c0070385150080c001941c850016003c1040d850140c00352180c02c4061501048070280d000071190880c8903110003540000075000108222840e48030000c1c41198040d5041c4140c42c0e4000e51a8001d0310040215004090000384407940b0511000105551110000f5101c0791241358107241a00040080f00c0c55108 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 469249604 1250 469248354 469248359
    0x714160305090a142b020415050303030c070507050f01120f0b03031306030b09041e0f05030d2f0f0a0c050d0203030f0a0e0a030c1a010e0610110c0f130908040e01 71
    0x8845121001e04480c1002006010710036400d00005200310280841c08e0700030b805020916030707030500c01075004115555010380c0302c02070303800c202d810035200da4081e070310440311b0403420039481c0d800c1945a01542c21642c800207403002c0c2c002d215405408442803035030341404001074949e50085011190420f40d049560100500f944070003c0c41184102550060088488044028070586603214003840d003a110320042c11014403203a0b560b91860b007080c011040060340340c00d21880450321010000303858801c4480901188072204030206418424003000c01b440500c0080c0c0b43c02414080c444032071081754000c0c00c40e1800500f10034025202d420540322048240d00d50b1001c1000e44d1114022a84099000000340400b1285541e00303603a801e408480c204c814002c1c0c0c000071110300801456441c02091003114036030305880e01c00c0c00c0041030b5018038034590030700400750580401d5001c00030711010b4101c000e442801d501300710440007910014100b11040c90b154140b0300210100141c03080503004481440716140c2003643c = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 469250854 1250 469249604 469249639
    0x20a18081203040c0905040510050f1311150d0c0f050a02100b0a031202060106110102120609040203070b0d09110105040506161104060b120714160305090a14 69
    0x29564411590158401e1a00700c10101c4001c0003150801d10841448146503540c411602c03d0f01d0b0125802d0780d0b1600303c0750380019400c820b800b40320350000744003040f03031594548101d00d00130740e0750303491030140004104902a03c00f0b91505010b0200306240034400720345900c07240b0b805d00041c049104110000510070018003e95601840075180908000e401802085194041e440d00030321021001e66401520814000301041e403004c0d80d6240c11240d41d0241c40742c0d42c1010300107010010001440c2c40940e01c1008282c1d02c0c1d02140d5003e5130842001c03100e6050680311400020b14100080d08510980300c40021032101e5860140d0146146d503116400d00c007038407002e03a801524140514465650024070403c006644448003c681c2440380c1d1080c4c0341c01112040c0c580c0443c0840b00c29401004106800040c0d0b401d036004104041e0703070320000701d140c2011400b41ca0b1170001400d003d04919801043d148104020805005009560040c8000360000d100c150303841d0300c401b505684001d0070340e0180c079804072a14080c0 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 469252104 1250 469250854 469250897
    0xf05010504141e13020411030a2a080a0e0303091c08010b0409020a0306030b1515030103020d290f0a0c03050603071202010905030d05190c0f111909020a 67
    0x4440030f00b50965400c804502254101000400615982e9001c011103801a41c07948100740c002c0a81d4042c0d030f5121701d8580c1c44c1100320341d5610000d81d0780c070881190001081e109103003401014081c0f841e00180a80f01c42d031501000d01320001c40301c002404044204076803100c1c0060039400c2860303900c803c08000111443c05803035589082c05035050150b400c21061040f5883d5400509406120b8a000179003c0e544e0740ba03903480c0d003c080d1904400c803031902101e1400c901e04100000340425140c9501da203176514640c00503650400040004001e201d80400230300503984441807c010445254001c0d481601c2c1c4801c00203150b54044408900091a24401341c1d4240e00c00e11505129980c050700401800703003000b500d8180c1c2011410101c0c100b091b00c07000071406031000d0120902200050702c2c1c103078982410b6a684202003800d0303018401081806812440403800b0072418110b01900106162203a00c0d03c0070120342d01e1030701915010944000b6000c001441e0140341d00400204246603113221080b60260f001000d03e = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 469253354 1250 469252104 469252111
    0xf0c013306030c081b160c09110c100c1e030b040c0809070506030a0e0f0604060c0c0b070e130914011b0915020f070303031e020403030c140708010f0501050414 70
    0x41c03040b20000d1036030401e68414414851110b001107041040700c04940c0707000031208000b00d40b400e4030001f04000350700c0940605100c10300c2d5100f07070074205100e2020095450381c03403200c2c1540d829111102d00004034054040222603500c03800d4480c3d40310503480c0001e0090325619031854000d07403800c60264001882144607901645212010380031982c9804208140e41d0406030440c64429030b11190310310804400c0010b0080f00107a500501f100c2c2c601420b14000300c51303e881c800e00c140001c04540900040c500002030f40e1008442c10302d00c0259402a01140c2c00ba4402035581d1402403030b0400140521138201c45c07401000300c50704028452490281a06c40384200b003038100c0390119480c142c007800b800841600b010001685c3d44100e4008907400c500240c40c0c522281d006a01007955005141d560458442100d0a000c064100c1540782601c1d56400030200000c604018004480c07500781089006403c0c0300c14030007002c1d00d00c000e11980c010600143c00806081c4203c5100e84e1034180d0504503080c441d680c1501c03 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 469254604 1250 469253354 469253357
    0x10818030306100e0301090f0c0603020712141306050304152f07021903150b060f070219090e06130b3c07020c09010b0f0c013306030c 59
    0xc5803282d4007070082405640c2c009200b880011805544079850034407401e94160300400e980d24a411860401c40181c104640007803007010700400c03007900415102d0190601c1074100d0b2070a900c900c16400031988003030117010603110400c00082030000d41301d9481405035016901a4a4603c01e250403a00403000302c2c0c400010f4002c0c04031040c00000c200d8450b00d0351805604c400030081d149000c55503800200090710401c0c52041c00032b51407500b4028030005410400025800341001c01c0000c403400c00040310f40c014031403e11808100081ca040c00c54407451000308a0045800e00d8445642c1c44816404c094440f2040304107291050b100014460f00c0034200c5039084d250442011600c83d203e0315140400c0d800e4180b1948800064590b220902c42e50703c0702681b1110009000614860516250080c1000080e032a118803c540c1407005210f500c100c2c00803200c0744800d400469681c0e007001e841d618007401c0c00d500ca40009003070b0155100d40d10688071020100d454812a070070310015444810980807200d600f03d2070b80 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 469255854 1250 469254604 469254607
    0x1a0f0402120f1c0f0f12020f09040609020a120507080408031e0a05060f06040506090405180a081b010915020a020c04021b070f030b040b0a0902030102070303061a0f031609080f0c01081803 82
    0x1b110f0549550080c1100201d100003d0300c0d0212442c00300303080e1480b941c0100c002e254000b902c10106544804601c0043c0b0b220388041c0301c1400c1c498001403c1c1138000e0700280c040c4900201090b01c4009900b144c1348804403105c0104520316180070110b0080c04211103031801101c0501e41104680742038011074013900d0000740f03c42d08000c1584c1c10701004140c000c045441d004400080d540382ca01c81046024500c5106540300c90759080b5110306401c0c1c0310054440c03009940c2c101002d2800080c000803c4800300d000034100140c42d08800f9000701d00d05040d42c100650401c1c40000d141e5914906512018001046101103408150b83c62a810038222018840549009001c7c40440c000604406000360040c407a03600100e1100400d8000a0882c0e100030422004a075482c042040308854040391100f2036040101003a080c081000116801840000c1002c1000c003c030381c82c1c5000d254004c0b2285000b605641c012a01e4031a4100605070307640314400300071382c0491400000680e070010a12001340d448140300f406036 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 469257104 1250 469255854 469255877
    0x11703030a0e070f0b090406050906130b0105090a1e060f0503041113020313050618030901051e040608010905010b070f060209031f091a0f0402120f1c0f0f 68
    0x4002040e010070860580d01403500f001540b40c00f41d0f02101d02a02c015410b055031054280c3c20041229040d610081c0a40410010003039a139407002541c03612003001d50804107401c1081b900485091241002d0340d50300c03000880c00421002105880960003003e20704440d140030381c81d030344182e43c2010849000400100c2c1000001c000407008402c4005408000d01241030301d888000c1c1aa041c0d030004c50700201443c8405880c80e05000d8100803468000030b03180e50b46150008019074458a0784200e005507410300c42c0000303410345440e43d00396619007800e80445d003058565482c0c10004000e01028480c1010780e6091100100f41403c034842202c40f055448440400324040366940c80300690425400340d5858003481c03205200c04180381d500340c9143c3c0440c060014419407149000b10418961401035602000d01c0d5041180c0c00310131030309594025404698070f0b8103680c4000307d034910781a040304012200b03000f403182c00755106c0b4007580611111000e544403d41c6a00010104482503d00d940b00c2000148400c02003 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 469258354 1250 469257104 469257121
    0x1305060a0908120c0a1b0315050610080f011a040e0406020a0f02010b030c04050406020909093d180f0605040c080a020310021b0f030c010b010809031c090b0405070e01170303 76
    0x540c0501071302409101c4500e079407038444440d480c1112000700b07080c627221400c1001614058243d070307215400030700b40000700b400c0190b414640d42105010b4103d011403800e0010f07682000c1d03d000d4800030841c00b54441810302d0546000310180d007040c045200403894080809101a0042c02990fa515401070000e2080c080d103541004080e00c400351082d41d130690b00308528269601d850120620580701d0300014019080c2c6820207201a006046845600450a40554109090030380c0c4a009441d013034130020070003800705501080a0344407080010190b080520982e4200710490300214410b034060442c41460681d90409162180e0394054029030542056506000304007455020b084a240c0000319182c0d006250b03404540743c00360f5034034000001c1d0310104234024603002c240074460b4811021321b40810182440c50b0010780d68001c01740036284520340010100070007001c6901100c42c183d0090401a40c2e400d050601a0304e41c40e4a004440340e11a049001040e100820416a241d0741c1444005502c2c0d660313032918 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 469259604 1250 469258354 469258373
    0x160b0601090314160611070b092d040b04060521010605060a0504080601090e0a120c0602030408031006030e15061201020309060f160804081305060a0908120c0a 70
    0x5480d06014907081c0100226608008148507504000300418044c0188001951015501d40c00401049140aa02c010000001c40d070301d011958000039443c3c450030300c8800035800d12441c400e07034980355800321011210344131a00b90300c0c0ca280505842c1041444d070500148426117245000303141c2c0040c10b4440072180e00000380302d00307881c201041d000000d81c0342e100c200080441d4003403c0f40000180e004035092003801c000b800111700628545c80c0402c0401400740e00552a4801c00d440548170f106030f038170b010031414000c818413036005a015908640e2807810b85444140d40d081a98807a8035000c0058003c209603000b80b04000300030032144020a039000580c04648504c800052449410800c0e0601da41c41e40802400914064038800000c1e1240780340c0214a100368217802411101d0139100f00702d1080c80c064000c211035030440e07002030000d40d4a02d80e09864100707a0340c059001d542c000700000360740e14042c0d40c8409628240d820100580785c03141201ea8800c0e0442c002c0840d1014903401045466000485d12403 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 469260854 1250 469259604 469259611
    0x709060902040e0f1801050c0904140411060d0f02030a020a0f030501061d0301020c0610030506070e0607150e071401031409100b0315040302060f0f04030801140d050303040c1a160b 79
    0x9014944403e0320b85c2e80b8034251513090f10b25441d000e8000c00c590700b107460140035905481000d00118245864079481d2800045e0300c040c0100c2c01032030002010b08416429400800541300400d07400c1d0750fa0704003440004003d52240c030400d00010151a81c01003094403900941c3d040b640300355503c00000c1c0912003005031340d0f0014501942e0540d420042514003070b00500c0981d100b020020000c807501441e5040c01402c141c0010f0800e0308021002c12000b145583d094261003810360000014140041100d48000082010b13540b28801c03803040303400006082c0b12240c403000e000310080ea004d10040602c1c0070390001c01e01064a00f01241e81001c0e01542034950954441c1d1001c09005080b6000e81c80c001c2d10350000c4020654060300140c02101c10405020f42c004001900319000c9140e103030292902d0340300180202c0041c00b401405030300b081103a131256607482c0080300070503030040d080e60795074102464040f0760340304c240c45000040094124003502c1c42e9106015180500885074a8000d0364885558035029001c004 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 469262104 1250 469260854 469260871
    0xb0402070b010306064101030603140a140a020d02040b150f0403031e0807271403010e010c08130611030925060c0f060219020709060902040e0f 63
    0x28040440032482129403107000f5806100000744440c01d120400c242c0340c0c900351058046ca0802280d50b105d810030640b0036410300c180d150301984071120850040700030b032510350700117440180701c04007500c2380700c1010901d0240303a449201d8512001c04603810035519281124000307548038600520701005400d01d40c00580805100624801002c0b001c501040800c0e001000400070300103012070140209900808801c040402075402445101c0b00c0b0b44008050120003410310080000c0f20b0310740c44070300d1505002d9000031900c807200640c00d607440d440c0c20501c460021002501c60341c00c008d041c6494078410303c030f101040072481d9074a450581d1018290315141c02100400c0351015a11020752509554000c041c41c0035440703040240480c240c0030001002e407881c610941c0d007010f8410013000c00085400c400e01c129407552144d1a4201201d507400d0100080c052080504003015040598141c13a0f0350225065041d19415041008144e84560621080380150702901c0410a030642c080f4138401c3e00307488031640c080000d = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 469263354 1250 469262104 469262107
    0x307050f010f12200408121312020d121119030f050f071a090c010e03030421140d1206060801090b0316080303190b030a032d0915050c0a060b0402 64
    0x300c00401071041c00400900000600205d000d0001000910850b650403000110282c1017110259141c440e082c1517200704140e0150403e903917401c54848407003c890740350700000b0700b40c0c41d00c07d240c401901010440414443c180580d00c441400d80360301c018903d1903243c055a0f070a180e0303814610255425801100d00e00c54881c03041c02400b0021700680258484441c0e01c9038600450304004180510340031843d1001410322107490031151154800100344c0b001c64110b84d84511446840b2051070b403804041010250802c0d60f40b5a070604803250008806444001c40d5454110001c401804882103a68a004017400a844038004010205842d0450030b0b08440090503946404524a484e941140e500d51180c3c106170000301c10410050003c3c1440c03a440e90107403209001040306000001d40780c050b5640c000301403164510710584076170b800b42d001c0f03d00c0e5811240a0303401c602100c50060405840c6216a40c1d451042407420a8034510a40aa4401e0361030040285501138241d910b48015140c10602a03800503070 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 469264604 1250 469263354 469263371
    0xb030117070e070f0c1b09060605070f020f1809030304170c0709150e0403020120130e1506040e041e0506180123100801051303030b0a05090408090307050f010f12 71
    0x61010641c50b14131584101520200c0ca000313a07010503101164010b00034480144a0350f00801c2c102c10133000740c030b83c4c1200c03043c0b6281902800076040c241415600340d5032a40345006c10418801c0000214002d60080c0303065055070301105546021445024050219074006a40070082c00701a0341210201c8250f50500b06080c0d41c82d000c0c401500c02c0d04503015401030303445c0c907020803080e1124106000e8507042101c01501e0480920a400322041c80d0303200b1038801000000005001c011300a00121042500410050355140c1e122203170b214015003a14280d60403c02c2c000c20101200030b0a644a0060b640300001e031005a44018901043c2d105080d141015552a03440c5040048840918002c00d01390140002c070072801c0420003480c5400964000c007419a242905015012595440c0f01c1d889030f07490b19011540300e03d0a004258040125845142c000001000b0b002c05c000d08100030f030100700c405030203c8400a5540d010451901c08081c48540482c406410100c100b07841340f080090340e018040400b003000300 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 469265854 1250 469264604 469264613
    0x12001020706142e0605130302030304060809060c040f140d0b011d060315010e04060f0c0903031107031203020c03070f0803240f010f1101060b030117070e070f0c 71
    0x8407030409031443c908112003040f0340b042c040840510200c2e0360b13001c5504810040d43c0100c1200c80030380140c0e030510002040114500e00240302c0c042c00b55074040c05070703a11a641d400015000c54400e031090201401a10b00050311202d90380140c0c0e0445070112034052460f49014403803040701074001002030b0051061105480800c10020701d060080c280111070512842c0f8031001c14894103009400c003072080d04040f160303000701144080e000c2d064800e449404002c17170b2114a000c0c40100100301309000c0e201d040c6513103603140a80040d002d2040300d010b521280ca241010360744860b11001030b030100809010082c2c2070791034124443d5000d03003c8948608100c3e0f140c01c8182d12564550840d00c102200c8007580081000386001e0000c10030252070400d154004201e0200c03400003005260307480d90050401103440039121000b440356002c05d00c4c0601c07100007041416281d00741c40c078039640240a00403101204003503402045a002a01c8800c03660082c203c54966200d08a0480342c0000384d070248410804030030907110100c1c = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 469267104 1250 469265854 469265861
    0xf070510110309190c03110d05060115080a02070f03050322050321220c0e07110c01020a081c060e0732030a1508010204030c05030f0c012001020706 65
    0xc0380e0314400d5103d15191030f030680703841c1c8564040060000b94080c8a00081c000032a03031015698000440410807812102041c1c50850031040a003080c0304001c000144880c055200d01d92426043c0c0d100c00a41e611014000b06a02c13800c1d00052042d8400e0548002182c824000745400c08100f000c20f1382c440ea000241041c03c0c20102a050382c01da0400101d04100b1110000d03141c0c190581e200000780e582c80c000541400c8824407001c8100590200e907548020402c042d502500a41540d03445032125040018009100300c0a420503203000c1d10809000300c4040d8000100055016840104549400d0344801c000f106180102903901d01c6ea6140d01e40491010f4032800c0d050312515095448060f00c0c403036403502c0c0b610201c1d0195a5403001c80004100350f83d8101e00801c43e42d002c40305c2e900200d10801070800740f0b030b240542e80e03220324415480440e002c0100514a0115130031a0741c100d040358403140348200352a881c0c061080f0490301080001d04101d01840111804c08229008000010b040030707059100d06064 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 469268354 1250 469267104 469267121
    0x2b2615060906131d040f170d0c020d0e011e11280308010f0e0403031e0513020a09060b0301150e03031204050d2a020d0c03030807140306060f070510 65
    0x40c0041d641c2c0a100402c00225071180000b00c242118020341410f8807040100b4500e03500240080c079001f00300c04031b0b00380c0070000c80380c694482080400c114600c00d1402500c9000e5490a040050600c0c081c0d519558444c11a040d0602e0a074401c0b2010300309200825903132002c214601ca580b40c0100c01c02d2403003072440c20a03a608114151011504101101e250003816280140c000c20000e40c103c480c00e1000004403420180e2142d0300d03040000e620b540300070821020711401c0004014003402d1078100302d9403203075030580f603180c8510a131810401d807515030000c502519094001c0544a64082c8010808441d68100032545c42c000ca00708402d600d12502c010a00f1940b01c00e107480502ca40306014001044820012070381102800c2c54046600113030400404603120042400740d9112092100d03200540d9595000185482d61000351903429a5803440d0150041004031007c0e0040b507840c091a1150220440442e40f0074140240114070b00002c1d4520041e41d82c0007d9400c0d9141d12031818910a000590b1082440 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 469269604 1250 469268354 469268377
    0x2010c02060a11030106050d0b0307170d032a0c08120712020316111203040b06030105010e0c0403080f04090c180504060b0306060a022b2615060906 65
    0x4580516200181c034055028040703003002440c0040d40c5594511031011380781561800d20b00b2079900c41e0b0803074940c00940841d14007113505000f101400590000030084d00103015580d401034564080050a09504480e03201c2e541941d50740000c0c0903e2400014030f50b45918620030350519017416a151340310f158a40d0003d0b40340e210703142001414081c1c21504000c03a10b03611058081c0135441e5107000f4200c0405550142c5020043c40402e90444031000010300c9410b08c0f41c541641c0040c0c80b032801c0d05001e28030203000d64819000c0e52034000045844805982414880c00f4091040b9180914540d150103440c2d0085418810002d0144000700d1080e2560081892a0340c0c40d9503440899181080680d12036541644900e10940c54420f08100c1c20140a0a42c1d9000d6821107000307444030103802c0c00341d0600c400c51000d11074860510350802e1030f5090700c01c68005500d81c1c543e15087d0002020342d134440c548418144601d40141500c0000c0d02d61001c06250103880e00f400780c01282005245000b0441a810040e110310 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 469270854 1250 469269604 469269611
    0x2030a050321181903050f0f1305030712080d14010b030a0509010203150d06060b040308040806070203031902072a0321090501050d060513050f090c01080a0e120a0201 73
    0x1081901e401001600003200d162021441c040c0122100d03664521844041c1000941c13104050515000b00d0540c0c02d100128640e1581d200c4256840c148a60b005960303042040c80d0310b200c04542c80c02c0c00207818040e03440c0d0903452a8912031035202c00b00e40d500300d050580ca0043d110207000500300000314020f4002e01e9058102900c0b401c00c80303484002d403030300108000800d031720500030030500704541e401200100c101924810340008031401c20801030413007500004480e40c00004c0000420480c0d100420441c2c0c40541541d0142e21070001c103e86a200030f440794072039500381d0020345210841c158000c0c0041c42c8079000240c09450101017445002d207125504410f140c002c0c0e48200140041e00b40b0b00014450b0354800818403551514029083d01d0b00b5000341d6040120101e070045880300d45501c44000b80500510141c001c0d038400091001078803003120904480041e00010801c441d400092546284005848185050381c50206d240001c01031182030300b455205900c0e490041c414514000d0011408035400030 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 469272104 1250 469270854 469270897
    0x12090c030c050315071b030207091104030311070803090402092709010b0102070b070b280207021c02090408130e04080c0105010509010609030803100b1803070501110a0f02030a0503 79
    0x16081c013010468140e401e8000b8001c226607568450080c02c0c201d403602a808125103454242280f0340800c0d60004400b56140030064042461304001800c2124444c2e5107486841c1d200d8825251100290712130b042443d4800d003c11101d6103003a401a001209002c0d01a10542503a0f0040101a006111488038090b0710b48013400311f044021300441341112400e00091220324036080000919220740c81025103c10240404542c00d1024081c542c5583d8880040c031010400c004940c0400a501c403084c101e1081d080c1c00c0d5070f4008035070190300035003034250000e2a00c0c03883d988a0700c480503903500400070100160321661000c51080e03180c18034a4003413800740b001c0310f44644d03070100144d003164410b810491152105400410074907030322600307000943e513102d03000f103449484040041d01000d507150001c90b200e60000c00c40d944549400c29095408400c102c00301c032001940c81c0019079422105140c1c0300d51b250804040d290128404038000010b0510103004c40b00d141c0142d440320f90958024001c00d03400c003482808003 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 469273354 1250 469272104 469272109
    0x3030603020a05060c060402040c0c0506010e190507021c050f0406090e01090504152c10050a050705180316080d0e010807051611060c03091509060a12090c030c05 71
    0x107002c064101602c15602c0e18294441c1d05980e80780c0100024411901d441902811900c1061812699548081103500f00d585814043d100d110044401050b41c0f0095a55a00300b48818040c2e140910415009803011121203002c0988040c0040720900074031a080208a00c03816021008000170500b1707076501d480e011309002ca503002111040c3d100c411054204001c0c40302251021541d92107003800203000041c900d5000180c0000d1907500b02050908400c0c0020200d000c1030f02060f00003a182401e00100016611102c44004443e0700b03580074000544140b00c2031400c50786904140081c0c5000404840700d640c110035a030f500b10002c980092800c0d1700443c00500c010350f0801000349006c0d50908111016181200c80244240604801c40000e4010840c01805014220300001c0a04d040a4244c2d03542c1da0311828241d40e00d074051000c15009168918900d0f0403401d541d0107490740b00c1801044203143c40b00c2d080c0708441c40d00c041c5400e906001d0340d4852031070014050704003050085100c1c003505503015240404 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 469274604 1250 469273354 469273369
    0x609010f060e0a030b2d070813050f0a11040c080c090d030e04050c07020114070f020609040f050a05101208040608090f0d08060f01030234021207030210051c02071e0303060302 77
    0x80e40c070001080001405580e07a000b03034409500410003100214041c0783d44c2800751420f41d4140d0b040e01cbea805098042c40500c5072601201c0000c100545081c01584000f000c110341d86201103405002c0c541d418001c0f90503a00d041341c0d0320003403103000c3e1800c0d40a0195080022703007141c00c140c1c1d400341c1c0c0384400600c1c0011540c2000707011040c1c5200054a80c1003560a807030340d04800d0000c10009108000c005861146981e40f5489031140c0030103800c0400072480c0481a032401400181c8420202240c6810000382c441070001285400551082189041603e4040c0c1501c4218018020a4807030061190200c0252800c11041c050b5550b103039a0201c0c00d04002c020721200c84096a2004d04060041142842246000da115500ea1103081c1d90010345540742407040c040e652000100941c4101c42d070070b100902407000205501524003c030340c6d040c01090b81d11302c20b81d19840751416000030030000102582520b1400e60140c02c240d40240703100c0d4482c0541d80000d6038a660744240850100f81d6941d02402035041440 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 469275854 1250 469274604 469274671
    0x3051f0606021501061b050a0c05040e030901050f1b12040609090516120f0e061006030b0d170702060a050c0601050402090310020d0204080307080d050609010f060e0a030b 75
    0x2500d00c030300f09202d424158400500801c1d06020b90701412100341451046104100c6070800c0941d11280e170680f03480b80112035144241840781e41041c0a00a15402c0801114407512058488901d480043c00c100322542c2c00c800e000c01140d820a54040c8042070041c041c9480d01f40d9182140f6030ba031410710714003800e4110203400c810707109403070402004000035050700e20481c40e00c010309090727040444d691b480c0c1c4003130302c0100000340d002030420300107040e0702c0c5002400c1c501440c500c0c08841d1201ea25000106c0c112588800c1c10fa51040d40c0e002920080744980c0704c10644502c0400d0400e00d8100c0359008208079038009281480054000100054a0f0345c0a1000a000d000112429403074405440006561880300d9203040024560000b000039180d000ca034100c0e0020007400c4241c81d150010ba05202e00300707810a48690341d019007804000b52040c41c04a001b1070581d01022a12003009060040c00c48036580100e0701c864002c40740741008030203e0403e22003184141c240c54182071602d01e809020b1414a507405 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 469277104 1250 469275854 469275857
    0x40b18010b060906131520032802030d110a0e15030c0f04030f0305091008130f080706050138190903120201141305060a110403051f0606 60
    0x75840300e8550392182107914101d412506107444001801e05050781e4100d42d4000c001020340191a4080c584c3c002c640140320f41094650090304030040201940c0341d1043c84014005c1030701908940300d01400082c1101100f6043c0c1c4101e0303007010000803560302117a01c41483c442e46840c022444005940d4482c0f20480c1981c020384481c0d036072200d2071380c0002140c040034203003602d501c4000c2001040364007901c040c1e400454202600000e144424180500940d01988020303000d0226504102d55480c021181c0c0c07801001c60422001c14200c0701d48032000b03032030780580c400c490758501040760b000884d2030380c0903e501038450110100c113002c42d000f8040c032007050000ca466034000702101841004213200401d0710841895410102d1441c8056142201c0d040d0007600014000f600300290581f500c0c3e415400461100f200803c8060b9580302c0d1203d0701c0403001000c600520603807202d0300062040c2151303000500030200b4500411308158580c1e660905002c10b8146424a21910020100008516004610080266 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 469278354 1250 469277104 469277111
    0x40314030901020a1515030b090d110a020402090409081306030b0f180411120c0f0a05091915031113050f071823040609060f0e0c0c0105040b1801 64
    0x10740001030b40700c0d8800d403000303044c0381306400740100f5200060f0880031400007140d0101d0720040d02c030316024444103420b030345c0e01c0003130302c1003c1e281c5203214015006200c0101400d00180396a910721350802001c1d41c41820030320741240d22240b80314006030290303026241d640f03041100355407441d04241c0003d048032484c2121078800c620304101401242c60300903880b43c10701203a6402c207140f81d5940c00c1103041c040b904900160001a040344125050202040480d1100421203810614510b110200100b410b2a40a05a0300004000124082c684500c4060121110606010420070000c00d901062501c1e96401904c4101c0b04107010b45003450401d092010420b01844104018104003d4407070000b10000d2122040c80350030641c144007001003422102c01000da0600c04241c0c4c0c01c00110b5400312060003c3c025001e10b090100100e014a154041d00d0b003507885516802000600d41380001c8003010002e000030a440d5000c000e0249421000e000c0c69118501404c044611403d000841040aa0740c50f020070482e42d24 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 469279604 1250 469278354 469278367
    0x7060f15120803060a0b07080301030c0e0c030109020a09150e0f060408060f18161502011a04090f020913031b0206040905090c120f010e06191e0501030804031403 71
    0x94120701c00045a41003021030303881c1d41e075040129984010b113401c25001240301040141c1000b11080046040c0d074402d41203c61100c1d45c4922461116070180c90103482038a0034801408a40c2d00f684c0904030203110781c03030180c81495442324040c140e00100e1841c50001450101c0e550180e08000510700b0180d103050390070780d00d413518020490f03480350750242c0038041001c8400e0102e2101d0075152010110044104140c404159050036020689042d51062171805004031321075a10f00c5006114101ca07001d00c91140c0703400301c8085410000280408242160600b91038010000541c55200700b413449168201c0700350804101c0380c240500954074030941001e072010b1070303254440161035800541e401c580404102040c076072981c1c0191030400c002c041c689170300013074001010101c03004002204002d00c2808402002101001c01c15143c5900049451384e02c4003c0e41c861b001d1405013940d00c12264100502d03010b11100d40912116410741d0000e903c10744400c030010805000f0b201001c01d00084180d041001180fa010 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 469280854 1250 469279604 469279619
    0x3060d1e140706180b0a090306050a0603030e010e091807090501180b15040e10080105040606140a06170c13090f0c09030b1803040902040602010e1c08010b0a020705040207060f15 78
    0xb071040c045c0e2415014085002c1100c1402142c1c81c402a550040c02070042d4605114003000a100c00d103c1640042c0d02107460403ca540113071541c070055400606020803503561101d4050301d1480141c1c1c1c0404510900c03c00007100b41c0703503100380d034060414010302041040c40d1640d032100b0b8820013844a8850301d0301c5845192011514000c940850344e50718195441980d560200f0300e140383c8698070100642d42090f04020400c8802c0e48010300b070f2180b0701d19416103082034201f40303da00c01d824080c0c0004101301d52114180d001c4807606441e03120b880004100d01c1c00208080c00c11380501c859100300189a00c076405800d070110140140160001c0520308190000d01d1034940710703480c200c040d0070400d041c1002c101c0116604414812640a0508610255070f296a03680b0028000d000700b001c060124007903151240410740002101c402a01c0103991024903c0e42040740ba9951540010851030640c8107070180010a5180d42c000380900600405d0009185c143c02402c0342c050303c000c840e20903d1090788840922804 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 469282104 1250 469280854 469280897
    0x1020f191803330b0907260916061d010c08030601050a02100c230901050915220303030e0705240d090f1e0803060d1e140706 55
    0x303a810191905000382210101c9100100080c0d000c0c5a044880008541038034032a007012030f814409441411250b5606074044686000051f00514002014480700c1510b0050341c6034a030300801a042a038004079000c5903640e000030707096401031021410040c4660030042d101154520075141c213003032082c2250050350b83c20559202c02040136060100200c0c0102c1014402c012510b000440700404000000541c80c01400746030400c86054001d206000c000e040d40d0075080c0544043c42c0068444c581841511400c0202c041e40c5000103540c1e49009012550280c030401d03603449109500b2840c000200d5045040c0241541cac1c00d5100c081d8140d214460400940c0c0700c0355943e09550041303002103190804940c0e0765803014820818034a540b2420040d001003031041e9210300f410f200344180b152004401030b68201c040801044c010107085004140000350860418101443c052803040d0041d07000b807005c4842c1083c1c6c540c20808196a4441d2600200400050030040000034100b541006289030400108501c4403 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 469283354 1250 469282104 469282109
    0x601090e1015020a0605010305030d110403020a0e07050d0213050f010e010e1c061e1b02151e131412041707050a090e2811011101020f1918 61
    0x202c0c001c10980c81103041c070078441c08207903940c44001441903580d6407d00c59906d40224a1131007506140c240c4100c0d0f174800306800c171000c690b4050152032600d440e02211034076550005040109100c0100300d0380d582c0d0000c510007061990042070340300c030080d4101030070b019850494144440c180144803036207400c5030380c220702c1d4110140012941c0002886007001414924074580c000140294145546c807980c03008400b21641c01c4260b06142084001c4941c5014280c00d00d4102d48d803800741c3c001d060908036400105d40d2a540c04000b00c04942900c15040c0120601c50b001240c485030300d01660713100b41d000c10003c0304402030380d50142402000c02401c44080140c0500c9a4454100b006a16000d20f2090709014051080100001000341d4400382d44c40c01040c010303140e99015052280511005410781e080310600e281150049881c140c0c3c000c8a9680e284040b0300001c0e64002d050211001100c21010424001841e81c012205440351311071464424075055800b282c100042880f001c0c9d040320103000d200030014004c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 469284604 1250 469283354 469283369
    0x50a05060702040c050d021303050c03070b0f03060a1208122d0a06120507032109150201091e0506010f0302010206071211070308161d060d0b040e060601090e10 70
    0xd81490b0507800f521280714010b00354560b03030700203c3c0170a40c923910750013280d044900540681c1c42a40c08401010740320003060284000c500814401c4800d241c000c40095540180094010b4200d00d445111046034008034100803240c1e0030740011850184441205045c1c1c2000c2141054161740c6070140c884941c1c034107104072082c6600d04003000110800c1c190b0f00040028001c000981d0040b40709800c1140d1100101e000644501414450100d41c1c26080c540701c0415403102c1d43e504002e141420710307002c0d4640950580d04115901c030742c00c0f500813500c0381d6001c103500d507480442c3c0f940c4202589007441c14800142e0004c2e1020000103000c00250340c011901940c00310b01440c3c40390f199121401664001e04140802c141e00f070714081219020107400c400b00070300806280d28021940d50740c2203800ca030b80100c150b10401d200900075080013514104080900100010704130003086401202c40840d04480c01505000300c00d034030400a00c041540c121155401401c4489040784440c0351407082c1c144c4088040c840e403c0d = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 469285854 1250 469284604 469284611
    0x70303051c0f090302030a0f08100501081e01060201020a23070f0516140f040c09030201080703020d1109091311060304030e090915090c030a110102010e0708010504050106050a0506070204 82
    0x1201849242d110ba4048410000200141c20340b50400940d250440f10010005c10200d02d905414580151491441100500240704985060000440b214007028111101248010442441d1801e40200e00380c01f030a240c2c0d00042c0c44440d00702d00201400c8c1c40707071040e815503954008411b2400c0f2030801115401c541090707260180c800300b403819501c0c0102c0c21380c00320003210351100c0201d006403103180030300707002c0c44201e80700b0780b5110894003040100e41540c0d41e5900801c0d05198204010f5001c0d18403158070885509005040c4080c000b00103050f00d28949202d060754400080d400001d04d400314000c0e42042c0c0d4644940c00d1181c0d15a02d004804044640c02c0b4410000400050205441600000c12104010301025014100941015522000c080780d0354080d00c105400600c26481c00034825410000c010003c1210046d2921280ca083c1c558400041c110754813114950010801048118020003442c2e000107414500b90515608440d40c2d82c002900c03680d0040707010006a501e580569103066012a0b000 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 469287104 1250 469285854 469285897
    0x1504050d050f22080a0302010507080c19080a06210606090506150f16060506150307210e0a0f03020f06280917040315020c03220e0c0c0c010207030305 66
    0x91803159000c4d031040b182c40c4200410340c01007580c1900001c1c01811140c071442c503261903e2001002c1380c0980c0c0c03080518880305040030302995201714a019040b0010f0100025010340340d05082a90209074492080302c1c65820610a04020451041100901040d0003c01039410040000380700c50043d0340101c0c0c0340401c04158440b0540281c001c1352506801000200c034840c1c010701c0c106010303240440c3c1041c402d00fa81c0501000d102d0b07032041100c5c4a640039584203d0400c034a82d85840240e0840203c1c043c4540d079401e0406120380c020000450001e001d9500c2c001d44000340c0c40c00a00d8001415001038803608078070b051184050301004c10301c14518a0400c80c880d080310402d00c10703004141e600c0001d04407084260340703015070309000c00040c02501d00a607010221003c44100c0d88003a489450764846065008020b460304421000072410104101c0c080310940d040e9481c4024082d5041c2031394081118003000030f4128620004101601440d03d0a00180c03060610307645024141c5c2c0034100318030317210700a90402c4 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 469288354 1250 469287104 469287157
    0x170613020105031801020307091410050f0d06030c03050a022d010507081c0f11070804121703070810150c060209030109150501050a050117070e060c1504050d050f 71
    0x6a44c001c100040210345901d02402e0003000810548262a4058101c0c0c068004a041002c0403400f0f158550312850f01e040403d0705080c5165001818041c020740d65600c1c040001628950b8002c000c44c005d0005004140c3c03070740104038410b000e06d500e075810503680828100d8072f022842c07036103164010242031441e2150708030308040c17195208803a41e01d4814410045034481104840e4000e81c03845260b40c40030441146218940c07441403040708000f83c041c04040c00b04025204468404100707841c400d20340d070485e49403001c504810541055801001141c1c203502044800710f01103c04400901032003940d0b801d108a804005002703d000c405020f4859a000078212150352807d402c0500c28036880102605100700340444c0000400083c0203481c425203106400003000e6104680d032900d181031203c170745240c1d42c5039800140e840a6400345601c0d0040310920814030641010302007061110501c1501c03104074038003454001c2c05c00500d419800203021003804075890210080d001c0e5810030400c02c600341443c2070210b19 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 469289604 1250 469288354 469288381
    0x1206180718020d020d1805060915011e08061e060d020907030b01020c0d030c110105041d070c0b0a0c020d050319090c030b0106110706020c010c02060a0e12030417061302010503 77
    0x466001040c10681e4406c031154a041540703851034041c0d016100139481d00d2807941d40ba034955403408850120408014401030700d000884001d4040d00202003055640e440c030703945080c95030480d000f998207244681600715034012007101ea94000801c0b204c10b8070504107039002800e421f2001e040d040030590703078040740c00040e4000c20200b46003810040141000c203d041ca0014460001508100c80c29209800c3c1e04456500071000c0c0c0b401e8441000c9120028030321980c2500c2001c0c0010980c0003008000351080000c18203c025050142075207601c08201000e4002c8040d18007004405000b080090400c1080307401146010f09485003400240080f600e5034031401e218602414540010345004040f0000084040d00500c80c1c6050300124000c0d40c6c007150741d40e08141e0b02c440104440314003281940e0110401440c4c000300600310740c0103a040c00c07400030380c0c4000440c0954801c3c0d030392001550301c00901808410309802c1c1c402041c030100c0c1c0c0102190b00d0442350101c508804400000d042c0301010000c60019290f0702c4 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 469290854 1250 469289604 469289617
    0x20d020a0b010621050a0b040b04060501050a05070812100501020f07030c0b07030e090702030306031b0307031e1205030601120b1c030c05012a1106070503060109051206180718020d02 80
    0x4ca05001c1418000c54100042c1019150584524501003032060182050f0203507000b1614140c4549042011109007076403903038042d4500b00c680309020081c2d042000c0754801d201d40281141502c405a043c20803002a103889500468035016900c2854104000b1f649280004181c42c3c05108060319035026143c01d66511896601c11a80034070790340100030300c141d800800346100f0300e81102286c0300d4403100b090301168680c0c12004c0d41e07011b4002c8141070000c40e4801c01141141c540c208071600c031283c800d0300d1b1065200c802e2201c078400554000b003808150760f4400c241e160700440c03142042014580c0d41000501d07003028200c1003801d440140000c00c0506028142204215401400902229071030050a00e030240e0203229007201415044551101540b01d00032700e64880441400400e11703502c501d61b05640079003008001c20304116145a001c100c40d160300140c1c1c0d030408041d00003054981401c41100002807000014290316511a035010411020081014541200c12013030044e0381c0e03507554481a01034403070031 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 469292104 1250 469290854 469290917
    0x40503060a0b090c03010311060a0e03030d1a03070f03110d08070f0c1a0909060a050409080306090714030403080c0708160615050a0e0c0705010e0706020d020a0b0106 73
    0x81040090411060300b207900c400c4030880307040e0308541d2442101c02e901e000c00c3c0000380511909804150050410000902854500c0c2c102028551041d00000e4615844441c209850036142c0d51021850f08076841c0405151f03004078007510581e0304000c1a440701c100700344000380041800340d64841c416110400740d00c0c0a950401101540c5500c10300300924110003050085400300e0070264000380e030500780c1d0303200e070b18218035448a54038101c0c4c081c0030400c810320b02078040c0c4e5204864850010b1141d0f9984a0070003054854a88903480e49007a008000c001e0000400030000d00c901200d20101110ba05021070741e1082c0c0c1420209499261400c140300240a2498001d140c03da0020b04c0c0814100300b450707200085480703404140003c8101c4000e604450701d0521038550040c040c01018002d08854159103603110f054080b610742810308640f82c40e404c3d0f031600c8454100d21340003200140304841d414426044e01c01401d000405c015043c23507442c01b4100c50144555410022180ca035105c03441d07484d144011000d200e4 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 469293354 1250 469292104 469292113
    0x23060406180908040b0c15060406030c03110f040f1a09010302030a030f032d05060f03060c07020105070803070915082502031920120a0503070c0f0803010f080613060b010302040503 79
    0xc07204187d03650b0002c081e603501c08a003110001105403805000da801580d901c816001103452031544e4186281c450009003a50040d03003140c030383c42d240d05ca40c420030000d01840f43c000f141d60004030a0340ca4a40e0003401a850140300d00e0001030000d40c90000d0a400c1c056810300d007100c00d580303400d04100d00074888982c00c2c0c00010101c441544181f82c49140098810f400400c04120f541c44100400110301c02d44d22049030540c103d07000184a030000080600380782c1d801070404525181c0e1903514546207900c02c507402d50229900744001d2201c08a03802c1c48074445181428400001c3c00e12030081c4480710490340450032286000045101070b140b0a00903030b2580d0104bc83c100b2110765200e84043d02d202c200070451881c820340202c0840c10381d000002d410b03020300d5041076802d04d002000b4908032450341c0300074403500034001c4840d503020000d855981d050340c086000b06a4291254104042258890110b50018a8540c00281805003603031482c045104e985d54050000078140011400613800381c015540160740c14040c = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 469294604 1250 469293354 469293367
    0xe03070b04030320012018060409051509040f0f030905100201061503060506160c05060c0102090312040303081f170a020f0603102723060406180908040b 67
    0x800000100f100411100c04e840f15403841500f41d4221034105003641d048003842a4a0030715003c1d590000d201c02c030041100780307000107031450102d00558041c0e030003c5040c641c0c5d0301c100041440541d9110000c12011201c00b282414281c480e160400d408400107890042113910300d00401d401011000e000f000007900c1e01100c03140101010740281054030403441c4004901e998615158802d00ca20b00c183e44000304410300b401e0030036020608044150340100d440001b0758901080c20b9861201802c64241000000f5a0728032901050500b41158140c1c1707400c5030f850078401840060b80014416500c501012030314120035007200b505400011481e809406d41010280c0c01c000d43e00c03004103c10005500030307a5019054100c0303100b486900d2004403040d100e1103420b03100910a006020000e40c0310340d50800100c0d40d82c01540c04254007182c141c040c00782800c0030243c8107041078440040c01c059014030304480400c81d05250840704860721100b202081e105c0d80c1e80d103040b14100010710003a6000b600d69800010384840307 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 469295854 1250 469294604 469294607
    0x20409091a010806010503030a081803070506090d08151c0b160206010b04060f0f0201020409110a0e0a030c1e03051e0f010c021e011e0b0a05010306050d030e03070b040303 75
    0x114200050811607445000114180c203001900c54100c0da0090f000b9407800d1029a03007114541c1018283c0007d074006603038004101c80040020b004840d01450203049542844c0044c01e150100240700c1805019201c01003107071700440a514a0800c1c06c0c150380281e8111002e01d00c0c0e0285189502d0000d1807a00540b05102144080541d1005001d210f5000c4410300e988070380d00e205044c0141d00c105000540a0880071a145229070140020014280009030500c0d8440c40e00409a810701107900102100c04a006e003461503101603006124141a600c030440036007075840da40c4071079020340a00d4541000440c140c40210408003050340041d5080800d9a45c003c5a03256180000c469260441640c1d00c112404000d00d41d6043c4141164070039030b600245102180c84410303a440040381c40301000b040d540d48060320500000112582101c54901c98000b4552041c0020403000b4034030340d00503904044c540b88042c07050351125000300030b8554040c10a1108029180002440c000301e43c4c05c10004410040303070000806 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 469297104 1250 469295854 469295873
    0x70e0a18110a05010516171209060a05010b091e130e070305061828080a030b0102070801091a06030a0203030f07050c010311191b0c0306050f06150a0302040909 70
    0x840381181c2c401d070034542c1c41d0011643e43c0103500b80000300c030f184c100e0f81e04001b40e083c3c980104000400c25842d8117180407200818540c0c5422074000d11140c0043e420002555128132a05001d0801d10300c0180c01e2211100226821040c215600c80c4201404604c00d240d50b40c441106000e045040301c0284800c200124245464800520041340c0d2845004041a40c00c000300028120140c1450000c106406c241e00030b082405821180a203440240a101b00001c00c80c128003c1c0181080d030f807070101e00900d0f060002458034a03da445400300381d1400c6e903070340b000500700341c800745000040022071480e0f626a0000a4241900c200000354544030004200300e40c1445640039019003402202658991403a410055003507c2c19541040d8502c90208084c1c00c0c0e640b83e03c000b207401d64549140c0ba604216040041a81d4454205e40a44013180c0300e04c005c10402c045400b58a900c0b84030b071000001c55080203000f00d56035004801d521380200c00049007a101e80c9100394142e4006140364041400140e00d40d003000d0021 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 469298354 1250 469297104 469297133
    0x60c19112107020a12020303030403050307050d0207061e060b04140a1d0f06040c0f120902042301080d080c0a0e0307031a1b0d020d06032a090608070e0a18 68
    0x1404c82220000e184601c56401450854000e8007462855445a60843d0369500080107041440803c1c084c0c80c02800551029289191160307400051001e110340400011704210344c60f80d465a424a013042c400d10110805036001ca4a420f400c14003080c588000041201c0804e40255420800f0b01498082650031090b40034000c5e41c41075031200c0d180c3c554a040c007042e5010030625a0201d03183e5540c040e0414400d1061442c01103603200c00040820b01540040d080e5100d40700348842042c10314010740445a102c140d01c41c01003004400501c106501120042c0030381c0c270000d11003106800e0100b00d07404000e02503140814404001415101d07855202d140a000c10792400c140c040c0040d00c0400010b14449030351050701481c2c20080e61280c1009000080500650b10088040260742d4032008004002200841c0ba081e1058120041a600c05078070483c0f5a0f0000607940400c1d42103040c00020805900d011808070207a0303250100c5440c90b640da070f8200c2d05c080c24501071180807141c03503100c80c0010300000340541c504 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 469299604 1250 469298354 469298359
    0x1603050f0d0c09330c0f110424030803041b080a0c0e0603060c0d021605030c0606030a110d1718040b10090e090a021c05060c1911210702 60
    0x288648807580038001001d03403c0010f0600520040c110a81c440904081034015130300d182440c01c680076580e502005119840d02259018100906c0c2081850f0034003801e504980410340ca20400062007403442004616072101404602c0e0010108041c001030b13116043c01c400d2200d040d440d5140d078545000e0b503911020501034441d03148102e0003286000c2030007001805140014010441c88d103520200070a25071101c01d8400b404ca03400c00c609034000780c0820b48141864014005075071510300e030300c2a0078200480104114469048040354400013000c100d041c1e01c90410560381d440d4000400d00d4004c44051496800161032039002c1254001000741d1010f070090281e09890a011000d42c07001480305405910020781c010564002c001c2c013210700c4d0302c800c40384d0100390b66088418a60198006c1905980e01d00b000c404880f003810031100038040d040000307680081c1c151515030b15001c0c006512214040e8a040c06c40100301d0341032000d40280008120051500e000100080400500000851007a5118001c100e0 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 469300854 1250 469299604 469299617
    0xe03071a2109120301080d120219021f090503070f020102010605090405030a0f020607020a150908121e01120308060a05130c030e0f0c01080a02160c0e150102031603050f0d0c 76
    0x3503003d041031050b84d04070b80f084c0000304490a91510241d40e008441444c1c04107007075003445055050140002409485000d58005d802050141002c442e0780038040c810307002d40142414003a4000410010407505503c4e0081100809a401440102d0151100b81d0000794448041002d00c42800310110003040d25541ea034442d07265200c1c80d214140e80312041240d01a0260300203400010101d601e03541c685001c0345494400003400d2505030303134000e0250403d01d00c4022070107002d0100701120704090010320f02c04501c40c2503c0029032601a541e80344c2c0800341030080070400b0307160100398180c0f11710a56030094a0010f000020308127261213600010404842c00000282c00c042c1601e00c20304022401034190903801e8050824680da100041d01c1015018040b5000550708006821201d81842c0c0504003052094443c40034840c0f418844011403400545000e240000c02107071440c2c90b130380002c2103c0c3c60020504504034000900d0409a4450040344081d81440301b0000700d035039040c11242e03c04046824103441d5030 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 469302104 1250 469300854 469300873
    0x120806130504030f0e0414090d1d030709020d090b0a0218180f09030f04060e0901091e0513020d060c03060803040806070e13020d0506100e03071a2109 66
    0x180160303001900c0140124802e0b01d0902e40540c072900740c04240050281001c40c7d5144544042c2407841d80485031a000c6400140d82141180d900c202054090071646242506c00c4141c400020b44a841c5881581000d03070380040e440c1012999a0030501d134031a00442a4001460000329040180d03100380c001294030341c2842141c001d5490300403000d03403d40c1c000c3c1041d5049581c0b40500080045030242040300144020f00000500c00340d500000c0020b0300041e0b0b07030008804880c030240144591f043c0c001078440b43c200540c50382104002c42c03410240541050010500b515140c00d480c0e403c0d501811b000c2d42142d4012042f03004c5c000b45800000c482e4205907020404a03581e03015468480c001d50082043c01c1d0001408281030f540b00d94203001000000600d007400000944000c441240d014014010301d0540316020440c2902d0051801481107595040c49441000c9001c000f98880f25175000c0c03c82e40d020b86112400144500c0d41c252500c0354801842041c84280840c440320242d20122031000f10b030720500900 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 469303354 1250 469302104 469302139
    0x10e0d1401140109140408030a1503030905090a020a0509040b040b0301060b0306090a02040503102304031101110313061112010e242d040c0e01090506070506130807120806 75
    0x4290400450030517107603c5494540d46c900d40f582c4054050800f464a500c041138030f00c12415544001144251110340039103150000340861800c00802a043c10380c410300c06004115040f50498426401c112400a404034125000074014a1040b448035050b42c0703003140200e007100c2c2c8003009500402c811100c990003581c2380c0c2a0441603100e0360180036007541042012030f1102e200754000301a03c3c030300900c0daa810515070070700700494000111402c2e00054203041188079110420701c03030701e50746070280310740a031030751130801c40704003e500c7d0720840201308541d15042038285000400075038090140d0342007007040315651120b500c80c1100d0203840200d80181101c608403403590802018180380e420107401c2031031003901c0d5445400c4081388204d2490b0b1000c10103180c04516541c078805d5008141d81910340301d1400580500041008803107422471f9006203000c1049030081031340018801d90002040a01d0a418403c9280600d254060003100521481900800c0514150054480b600c40c29098030280d04480c0004007 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 469304604 1250 469303354 469303361
    0x70807031b0f1b0816060612061b0206010b04180612030e030d030209011202030601030b030f07060f0804080403110102120f030f0c03100302120109080309010911120309010e0d1401140109 82
    0x1e08400c2c00b001291440305c441103c102d5040d000f0700340010074a80d11044004003803200030b011901103903984400d481c0f2412081030030031661007503c020300e425814517290322454400c0d030003010040f489240140003000100c0d005440a01420005c070380380c5025a02c3c000d81a00074010303440c0e21a02030562040740e458800e20a6030384128050f0f5408642400410701c040c000e601c0070744428100360712203003440ba00e5141040f0303460380040224001d2888600d03148006000d40c86440c1840100702040c8140408200c17a9003d40782600c0e007088040c1010b000800050789023915000e020068a107000c10040054880e100266110302101d0342040e18603600c1c2d82c40d40c46203210444844040441428050015050008091911011581c0002210061368442c0d05007504212001b2529a444890704000c0190f601d00c1e0161404098883c070200c0c0b4000904641c0b0f80c02400070890401c04200d02d00c000d15070f13820455100258000298982c29040340f00120701170300d170440710000003008401c0000381c2c6840c0e520 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 469305854 1250 469304604 469304657
    0xc050c0303150d02210d0504030f08090d0f08130b0901050d1509020c1c0206040305030703050915040b061005040501020c01080c120c0a020105090a0b070807031b0f 72
    0x40e516642c0c40361107001040c050703018100e4120800d60700080050321440d2080ca00700c11031303c24800603a4402c0d0003c0e450840c02c03000c21070070803200f80410800603c0442c01e0400c03056100c061a51542d007540042400441806405008100001e04210510040310b0092000f4004241c41e03542003a1148031040183c412490781500184040181000c0b00c03c0c20740c094804100c5464407040d000b955000d00c3c600341d810400107402c03180c11400d00c005107101c9812002a8560309400540f03250726041d14050805d0000804103024103440e0800160881814081c100b0030111214101e102401d2905008800035011143d0707900621071440b00c13000440c015400da60489105900402d220018100116542c81c005040d105089100b0700906102e8183c5c9c0c0c50782440307400341036002c540710729400100a0949002420090040c0c205c4034110001c5111030518903408030407810262010b4480150031002428804117003180440310741e08880340781c1c2d4001c8500c00000a16510344100002c00000507a1007182803 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 469307104 1250 469305854 469305877
    0x70f0806090a0f060f090e0f061003080d0b19080c010809120a110d030209011205040c0303050c240115180608040f0c030605060405010905041709030a060e0d030c05 72
    0xa4009001841c0903006500c0b84000450042134541d5141141c3c111540280c1120750001e07110b850458000e130040081941341c5c00401c1c01441c0c903090860113440302040c14040546142000a8006100700481e0055050744001400c0381d5002010862229800440c3e40502e022900a1210201e240c3d031003480018000d14101d0041c03c214200c0000920b001e81c0b11080040c01d101620b141d05602140c103004844402d5460340340507070340e54000c00c00180135040e1303400c605403504d180400f8003001c501d00da2420320607660301d410110365400d40b040c416450710510452260f09607801c0c00c914030890000d4903a40d4100c403a0104040c040301d00080c000d582c80704643c007095440d011503250810295100d4081d0310b401c240609121182c1d001a0b440c1c28440c1d03042a0410b8809a840c5c0703061100c4c40c00c20384a001d004204034201000f031410306507600b40b83d000074030a070a9056000811011030b581d40610040710103540c003244c20801c642c14910141d40ba201409811300200c0c1c5851001004103000700c04565114010 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 469308354 1250 469307104 469307119
    0x120607021510050310050a05010f0308180a0e09010603050c010e0f1507080714070b04060c0b0709051c0212010e2806050a0203041104020406021506060f070308070f0806 74
    0x285048100c00420041c100100008250000074003918140a9182880d240c85d601280524142c011001641d0045e403007540b40802620007040401c40311002c0d2a07900b01c40680160300d80400000052400140f83c20010420700c3c10030911403088415804242142c0c45901030383c0107000b0f1400159100805020300d1500203001c0c0020380c045241899010b015580804c01035818800c00f074840002a03005510101c0e00e860400c1720f0010a450208213040081206207038040ca020306100b001000001c1c4010014201c0c240f17907001ca40d050340103c458601030032018104c180c41e2034001c90344d518030151548081e4000c5403070504081024006018401c172103012040101100d201840301041c800c808039445825034000072400b14009042070241c14050004000d015840e401d0078248203000901d2607a8062060344100010030a036070300410041b26400031042c844a5942c1d0745400b1400d944580c00401d200d03100001115020907400095003805226566250103c0510244056801c46403c2d102c803a0300000 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 469309604 1250 469308354 469308373
    0xd0b030f07122f0316120f050307080f12010b0a0f030203191b031409031b0109020406091d0703390602031c051312030b041a130605090a0902030307170912060702 71
    0x10347c9107030001d400344142c00b00c900d05211510b070313480c042c3c1082e00f07071152440d1700182c0d068841d002040410f01402c0c8008400d490008001d00281882c444510482c05040d000320004000ea03440c0e00000d00041c039100c0f0f00703000a103102c1d410050325000944210380400c0c9891900a10402010840351003201004020747c54441c070b818840403000ea001041381c90664076152041d005031031340c1c0030f0140104405070010508014220f4444401c9441c00304c181283d03840341c4402c1020078030b10031000915100030881a900c10740c0c8900990720385003040c2d01c0c641b541c02d4050b800040040c0c2c000000c00d03071035124061618007080c90080d8142a02c03c00d9516240000700c0741059004210401c40f641500101810001480042e81d00800c0c1990891030800388010704026144041e800d2030340c0b00d00d5070000c13000005c01c00142800001070f00c0a0001d00b038518920755881c803900454800308200d651090f00300d1030034400c010324a4140c5103694040071a07940621864000d19185580000c0c070713035008080c60b030040e00c010360 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 469310854 1250 469309604 469309613
    0x1c020403050703031425111903031d120d0206100f14060c0a050d0305130201020a12030e1606090f060c02130b060f0d0b030f07122f031612 61
    0x1c05094480460180c01c010261901c054611b000c100400c43d140300400281e0a410104d00c18090803900354000c01111030b104a001c00f0b1007610009696060600c0c002e8200004043c603a11964200411b070001880c1c0c0565610f9072000990010031b41c010750890707400c2e9866200400a17030010f8401c0407411802140203000c1c0c03c0d044451a9040c44001e0700460910300b042080c1d5192210340c60054076981c00c2000865440c40c3e01d801180d40c0a1034000c49982d000e40c0c190300007940c038005140d01a20704800c92940f50800342c82234001c08600d486010881d00e224441f100044d000c48158840c58000c0381a41e100001c011170b012203a44101c0d1002e84a90010010940901c5244034a54001c0700003a030390740400814964642c0080d041d9640841e42c86600e41d4a2856100121254800e200c0d00c245d100320f5013400c40480c002002c03010b0360b44404040c403a0b0f0000e4500199501c5039803a185c1304c041d0441d00751488a404024010305142c40840c2116000c2094071031008006a01e03018849424554003501c00108 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 469312104 1250 469310854 469310867
    0x6030b01050f0403060b101103070809180414060924060f060f07061401050a21020919050a14060103020903070801090c050a1a03040210020a020a09021c02040305070303 74
    0x850060600a18040240e1000300c8258044e82007102c07140d964500aa00c1d034184804126044051402c0c4070210540310124a580c80c00b9410b4014143c0c100011030341115240d04800c0740d50110564000c03001c504152401e5000d401c140d041540c014030600000440c02c4000184644c0c00311b5011810b001c4103a030700345800d1141100201660341040b04103141c1c0000303443c2c0340010300e8007100404440383ca038082e5180c01b00c1660045603801d20401c003a000140100e50301d401c050f1084650f043c401c040030300708440c40d2a1000c9040303980a5400301c0300600f0801c07182855210504400161002007203695910140003040f264485200c21680d04010000340081d4020340c010f1015500040031180700698400e603490035103101d450115002c1c40700d55000c04c0300b0b08005110b080038041406800c10940310b55640425203000041010384101605c0c030102402d503000b070110394103ca8000c1c0c090a1002d4940b04505d002e50710503d521020001078007007074049801c042c070954003546d6014018001c0d10f807450310100c600c1d = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 469313354 1250 469312104 469312121
    0x4092301060e070f08270a11040b0301020414041d0304151418012f0309041d0a031817010b0a140303070204020a051308010605010905090f060904060b0301020c0304090b0f06040603 79
    0x52103032031b925918020b008202d10340c041072288112207003a850110a000a0f51201d803801c501036030040c0020300c4018002c603041101a6401e480004e101c80f4080d4142c2d00031f0712090346a5190b8000010302241c600c04451031500c005940b1340302e40d90761550401c4822814420510701c44044002c029040c50b00398426110389240015a840700742c0c120902d604450110011010070024a60000407402003600b024000d1a905c101400c0000c108156207801150700c17000040c03001003c2003004a6040c12184d5211020070140c07011010b40c400312180c80c180c190003010321540151040c146080001103000d1201d114106600300a0051418454290709020180d00b1503114041404024044001d000080303c10705c41c020070800c000400d14a01e05800504900425004140101000403c000e204200d056403560051001d40c0d020b4160740d10b0b4100380c4028144001c7d1a507042d400003580f00415600000613105a800b81c000c100045400710040055100305250b4490b0010ba0a001c04c20bd50740c0282d004a12 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 469314604 1250 469313354 469313401
    0x1003080a0f1e02070f05040c020d1416050a02120c0f061617040314060105101b0519050c03030703020d050a0207050d0803042f04092301060e070f08 65
    0x2458504180b0040091800e1925001640890410490b0020821248000701000c1d213040100c8641c03040001d407035454a003074800a03c15244030761014165001c1c12603400380c0c4002c0000440e810546040b607203032040d03908268881c140e00a0411074890010402c00c1c40080c0050501020740c418405209203504416074940e2209880406407021031403065003c4181c0e103c05a003da45c643c19440c0ca80150b09072030340030000b10360000f40188600d88032a901d182c41e030f00880c01c02c65200c41c4c6141c010601900600001485c50090310014011380130400b21440c1224801c00a58403103926900c145550303806142d8000d00164003680b6205000f900030401002441d0451042c1e030071580d190008074007280701c1880101c4181d400081040f050080d4524141c05440007200020403103110f000504511004000705030303200720303600e001403001c1040903203d50303120400446201d24009003191707400c1e009168601c107200c4041659070004450b04e1244400d00c40c18061511680e0051f280e007e0a0311110003c0d400151 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 469315854 1250 469314604 469314617
    0x61404051002011b090f0302010e062a1506030303010501081905040516061d041e09200a0f0e1b0c0601051c030804080a05071b0504051003080a0f 64
    0x3040d899545a4054840329500003045501c0e15070909040d02e40c03440304000410919060034404500311620a40032290246442034441d009600040da240c0b0400c13100002c0f9141c1200400d40203004d44078a180e0441c00b42040e100100840304e1488400c480407144154590010170050140798024100150080c0c0903600103100da071558103600741220000e48003030310240d004c41e15620b481480020501c024224074a0900c590803894140d81d19040390030b0b10024170860702c8409500c1b080e81304030400015611461818409103030203040000751800300701c2d8110070100c042c215400d11820605680411241c060314542d416034038010302c1e10505040a0001003141d060840b08135a01200b4201600c050083d00019105c41d5242a08000c40740714050080152600914a14008203400805041d4403e411050041d61000a4641226184039012004004844c5001d1119420040000c080150386050b44c042250340c50310691000620541d1000910b40b401c00c00402c5000c40c490114490040114100701 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 469317104 1250 469315854 469315859
    0x1c050405030f04030b0a1503020306040308041b0e01050a1a0703030903051c05090d03050106140325050403030806010912141002160203010501050d0f1202070b0d0c08061801061404 79
    0x24203030351050b0b100b603411001c41070510140410070b2103990001f2102e034403001c1e2001d2a641c042a02d60704000c20290a00c05068001002d00400b8401001d025070011030100a040c1c50b01c400c0410b8040a0160398000d419505010608400d070744403841c80d00c92004202424110300d0b036001c0300a003008031421020000c0612004840548030500d02c040303030b1072104001c02c2610b0015a080e14044107220790f401090b04240c010840160040c6041d0260480c01924a980e80c0e520f2600100c800300451048200c2e208c0c030200c1c9610103600070094825203100ba43c1d000c40e036032251001100d2401d50360091b14a0285002c01d550700041141d4440001020350100341c40c80039860102007800c03a040800207044419800c2c201b101180340030300c0b4403409840c0c101c179980c5240f00320342c560031142420004014280010300b1070903000c40d4000c000400007800903820547c0d40f03205504950020304401c0d402d58002c94000c4010400e40d140940d0340c00d50129500c00f80400d00d80c0703400303811240e20a01c005802405c0030104000b = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 469318354 1250 469317104 469317127
    0x60e0307110d15050f01051008040308011202060403141509160621090c080712110f0105190e090c12040b131406010609051f0518060706140c1c05040503 67
    0x5891080320010713041216581f40205210640c440800d01008008040e000c000000380c00140d481c1c195031454014039030980c1c142c40419032030700c15a0000f6004c404900440100200001180301c0220420310031130085031203c8206640d41e452400440030100b64004040c01424403900c1070345a2103100b1103114080303103220350610044904814040c0d4926902e01002d1060000401101c0002d01109a42800d90a07203602d80040980aa8510700d102d01007a02042866a214209440140110301d00c51050303650807a80241140c0701d8001140c0c0581c1c0c4a0b03000038011002d01c0c0030344148600031000e4444954840c0d81d000d03002000140030100400c3e03000144400b2451a00c00303803003403071808002060345504042000c0d104e00740c554081c501c80c1c02c0901c6101c0d031442040509002c0b141c030341e092894588441c04000d51240e01c45a1400390000c40c0402e0300c2091103410f40100c01200c1441900c0da64548580340406100e00c5500e210840018502d0010401031031954806503000e40900252828050b61440 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 469319604 1250 469318354 469318361
    0xd02030a062312150a1503050d0504030501110301060518041d030d060803090a0e04030903020d060b0906010e010e0d1104020f1305040c0f032c0307060e0307110d15 72
    0x802d5000031000190940c181021058a1180700110008211120201a03009031510004114194243d125017104040b040000458005154040181c404481c1007010042090300144429121513080856680901d82c0b0b440840c0e040e10410380d1040d141160410104001c1c50001140c83c0d0040da07100ca0a591301065071080c0310404501d880507698433040251034109444013a046640150010003440d0320755902c0c101c94400302d40880d2505401961103080607030b449007266001940100d41d180c44501002880c2e4415118410100c17450308040d22441c004446418010f120203011a4800d01c90442e240340c25059905c4841c428001c101350000e20341c0200d801c0c0d8001e9000c11a0401022808401c180c041c803d00380080c0c201070750204501c040c2e040c0002d0449103400402c809040da1030b141036166070b580c101e180f80300b00c891700c821400d08001105107036079031360262200742d49844c50b22000c1c0340810800320858115035044139800d1076140c40c0e03c0803c200c1040b40601180c00d500c6510465600440600 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 469320854 1250 469319604 469319639
    0x308100e070e0429010c03020c031e010c020705010806060d022a06160c110102010f110301050a0501080903071410061508090d02060a11070209040f061805030d02030a06 74
    0x2c1d162101054448144029564641c0c000411107240c8855110020512401000000824039150010074194102a410310884200c13503905401988240c1c0394420232a0500040e0001c44c80003045050301c0080c2c12621900d840c0110344c0040d4138040881d40c245040c07409000b401301d03800c0006140c495000e00c1c0030400b445080215072155040c0520341800f04003442036541c084149050052070031101100101403403503400b0000d045441d01c1d00b03442e4180e4400d502404230028084030400410f02c88094020080d0800d1190f24462140e0860114041d440b07000343c03d0040b000ea000039405c2210640d80e1022001c10704100050610076901d502d0390814050203003e0041405031500240346c1143c520041c074540004107812400c0d803010b00c250040c154002843c65210b0310905002aa6000715482c10003e449482c5c0080d42c0100010241b10601406d1940d607181300f8070408081101c3e5001269500c0592a4040041d201d90000d110940d40081250000c551000d40c00c800024125100e407070811041a010 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 469322104 1250 469320854 469320857
    0x7050118120b010305120a05070b04060b13061514090f030102090a0e0a0b090403170402030319021b040908040905040f150219021c2322090908070308100e07 69
    0x1041072040601c01400c2413000300e141546887c000d0390019000788034002004024120350000242032201990201d502c94000070440081e481c0290540b80103440280541b2301d000981030300b081c100600980a0190300c3d07145e0b00340360b4140380041e0304028005131024155038055400300312410715951902044000b41c46045202201814030190420482d5000007110b4081c400b070f00e0500001c6074010006004041c661030310002e6966176440401c1c00c0d40160210f0f21603c1c510780e0642c8a0b101c0c0c020a05451185071800c418404219000820041c3d504003400603042c010100030a0056200b580c0000b5403080c018007074460106560f642d215040003032401c6100400740d001c60307104406451512108040d20b0075100804440d2086602c07040b010141701c01041c00c0c00740342c2c2c0c1d8025491140c51208001c10381d04a4645e0384444107850180303030303070b40c0b00c407002950b6018081e401044840c0ca51191304000e1f42c00201060420070740760380544d11040040c0c06107441d10f2440c0800114046800e400710300c0391203113 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 469323354 1250 469322104 469322123
    0xf130f0905030c060709350f0c01111912030e030d0b031501180c0e03010501090501050a06090833090309270a1d010903020618030306030705011812 65
    0x10f84040750f0404002504000410070050420021510f405000c0884420a10b604143c64480d0700c01100040a103800003500301d0040f0462801034200115009604090a0301d03030070b108900d40c100f8a42c0791121076800a1203600d500c0405000f040f1100302803d42d40c1d40030f01b000251209860325091446c0c1000f0f031000000c07611010614218102401302003c113030030243d40e1180039410034150810b59807403004003054043d59002440c00840c4981d07403600302e09001800801855840c0d64020018207002d001c0c075070148922030710005102c0d01c118007540494460b00058019518008441030b141800d00010042c51080307000660909000d907498140100d0305080103607076802d449018007d40030526001c0c206041080844d0031005001040c070140d00000010002482c414001c3c940b13034610004031400307500341d0701e800d40b08420150001034072405941240045d0f0001c200c044c21040c1e03244022901160076170026241008070303500070950180305488280740c0c07401c1661035a04800388802e4070079040c1d549000 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 469324604 1250 469323354 469323367
    0x30e0a0b1009060e16030e0a0605010e07020d050c03041a0906120105030f0d09290705010504030e2e05040b13140604061407110a090903031a0f130f090503 68
    0x8035885840000c29010b0000c0800740780c4031170451019460701000c6003d16444900c41030100c5420700a0f4400164004020070543d611070b2801e610500301221160003611512400e042c1481c000d4040d10303036015001004615041c10081c81e4840d43c0c1030300c51509000305060003455800d9813140c0c054110b5000ca21100b16866240c074080500d0100203031407001d02600503140e11507c0342c2d840b80304803041ea2500e2041c134128288071030110840c1c1441544548030140085130120800c10190000c9000320300031307652007920000d40c0041040100c024071a55826168022040720305519945d010404014075090040c00c0c19a5440c501c10141c0c0540000d01c21210300050500500f034160f0003a181030b64081d110181410304211000c0d00a1b0721a400e16100c4040100d108001c00c240c0c2442c9461016007d40002201603507007000f00c024080300c0780c085011905001101180980001c0143d01c4148000e0195055803000301c140281002c0040100701d207240c41d5041007110391403038040c0d980080d2160004564544 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 469325854 1250 469324604 469324619
    0x2130216021005040f0e090c0411070c05040b09070f27170a0302030912010207050d051c0b030304090b031e1509031306030c0314100f09140403030e0a0b10 68
    0x11507201615050010a00c41404031726002e510501c01d035044091505050b480e40d120440c5406044140c865202c0d04114a08560040d4030015007041c520662000c1002c80d204e000b0007060b20701074464103030051041000a0002482800d1341c014442160401069074610a00c514014102100c0414100808080304000030341510b5540141c4a0b0510060004c0301004c0d50020b49a100e40c40c0709038850440b9030400803050a081d41120902d541c42011140902c0e0520406409a0072901c6400320031103518226001e10314490258a40ba100000c2c0510b2500d8285844be07001880c840c040550188280c803010b03d40c80c400200c40c480c00850000003030625603c00000d14114010007018a03400d83c1061001807100360b43e410b1a1000c0d103440e801d001c5000282d04070b04400418455048484000c40f580034007165500f13034051002982c01c82d40c8034208280d195030003142a01c2d00c170100540106040400900868030a0780290442c0c0b9101055980f0f81d221900d403001c0f42e80f000d440070200c491310302000b0010f0f40d = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 469327104 1250 469325854 469325869
    0x5060106110f030414030304090905011d011a04020a05120a06080d022b121a150a0c0206090612070203270906191203050d0609060e010308070213021602 67
    0x1d03850000c10b0306049030120141c8a0065100da507024040d409141d900d43e607024415030b8042c240340070b010803581c4100d0410f43d020704030b0700120070081141c0400e60300f030218040c050307102e450985074a1101d51030002c10a102c000e51108543d00200301c2d0520240140782c801b00c40340d81c09201607440208000707091285290070089412080c3d4150741c0700c28600004950b41740c2070300761b2507404551180c0d8004007200043d41c1c83c2803515800311036546014440c0c0d902c10014480304c000120140c0d51810f013000c0e004c2c840499071140c9a905000b0410481d09100189007440042000040c060101c9092044510707100e0405d0000ba81c0100145e000411002c0f4942404802c101e00b03003a010610296400512002c10007040f40a880315001d4492000402562540c01210710010110349130f44c1c4640001c1402e0045c038982090307661035015810040c0c0084c0c1c51440d40100300030342d20500840c98140c0d00c0c585d16030f40503610518040783c00403074503000c00001a20b240b0280459600d024043c00d02c03080340784100442d6 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 469328354 1250 469327104 469327127
    0x60303040909080c061f0b03090a0b0a0515100e0402090301020403020907170a09081c060812071a151e0901030c090b2413030f05160b0c0c01050f070f05060106 70
    0x1484401440c8006c0100c00aa00301211581003201e82e4a0300d400100c1c90a00c0803116002d0310400401d000e20050080c1c80e441107204100760070600d0002d8005008200240b1510050700c00010908080e201407864240d00810400e9802000107161950300d902103240300c0350803240fa6010580d6105004419540600d0060344845038140070041c1d50103d03a60003215010300d64003c1440c1d442c9a00c400c645210980c00711000e042c20f102241c1d030100d883d030100074082d4496402122038144031301d940d9150718241f0030b00d24001c00c0800340f1a14200143c2040c01502509450300c0401c41d401000d0822094880680f2503020354051307001e0030801401c001010341515100d2078140d011340548650300c584a181c0a141c140c00559140c0303500c2e40ca110744030355a80244404d40018040c1c40070308406c03001300701e800035481c0d10070701c1e0f0300301001c1e001039940b00c8411250282d21030a15a54206030307000301c120741c401c030700a01c56845048003160519496449002d04000d183da0202c5069014100600c80702d03400c4201c0101 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 469329604 1250 469328354 469328371
    0x30105011512290607050708010e0c061908090709021c06230103050c0c030c010c0807090e0c0a171305060a0b0d0605150303030f1e040503030708060303040909080c06 73
    0xf2030981d06140e40070400e04041c900091814070300405686039a00710845c1da4881c2c104040303a20007521510428000d25845a60740418400c80c1c49095903030a0203c00d036a8419801e00c0c4401c0b540122202c1500c5a0300b004106000900132544c000c6200e03111803004c1e00c44604000c1d00c145070f1040d0050f4810886280750130950004503c00f10541c1407440750481400c0844080c640420207440d0f4144c240e80034065001d020906003c0481c110840aa05500002084000b83e540e00c4541e200c0744400d480c030320598040c0c44080c5800000140841210400a0902c4240b40c0303014681d07211210b20200700d507481a241c0c04541040585c0c8041402400c0140d66000a1401c038100868442c10700050500345003c14010711041e02d0741d00182d240c500401c0c051000000c05030a6070b0383c2c0c0ca4880c04c1c6024a0741c04489540355410200e2000320301500a4030f40a1145a0200042d850358842c10019159220020030880e854801080302040c003100d9806105000d0b885459501e440b00c51707040e1401c0c10003400521621 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 469330854 1250 469329604 469329611
    0x12090e0711060714090d2f0114070c09050f041502040f050f040e010606090806070e0607020402281110020703020705060a180b270906100e030105011512 67
    0x1e00e128041041904103600e8144070103400107481101d082801241142940202844c12100503c00100c2003d02203000c085460b070209030302c9110312181a03400e50900c500155001c3d00c01e4038408804030080c101c1c0703809004c8055205988105040680c0c0044034810355006c1da4030180f100300584502c02d0280c1490402007035050500380091100c1c442e40b00d12540e803081c00308031040d410940751540004101c3e1460350080c4002394a91038040c0c07200c0c0061127240c44610442001600b11440b580c0d1200460030000c1040e071500c4080e03004c00c006500325106200a0f0480d00404952403010344000e80700301106510f0b01c0000350b16200d01c2904010600316410100e03401040380e0f100195021600e04152942107440c1c0b5150840030500b01d136031280901d44088007a1040c04086170400c5400301600c0c070503a803500300480008502180c078207100c240e201c0c11074000b81010f011601070710384041038542e044054640700e2103010300800040d0a54a080e0b020314070240c030b0202c1982c501648452801c400d8500001d051 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 469332104 1250 469330854 469330877
    0x403060203040f4b080d0b030d02030903031b01150303020105070e150301050103050c040801020403030c1101031503060b04230601140a020604120c060c080121110d05030712090e07 79
    0x4040104074962484621071310801d034480301d070141254142c9031500455060340f40c2d6950000e4000400c050016240329104403400d44581703620000031036a40c41405805035041c44640002000780c00d9180d101544c06541790004080901994881c00c0c005500a500103e11030400346405030851490031030761402183e0f805c043c082440c1480040309c3c11605c0030301e0001042c1c0d8688105030744501031504803c0d903d5000040c00020305030b10400d20f801c04c42c001c140900c0250111001907013101c091801d01c60070100c0080c010800f1035010352040d903118001601c04101032091140350302c800b480550007182050350800a104055a2100c00e803004030150002d01450130a4402d0081c2d42d425008000410107007190a007946100d1241d400010210341c4120280160004045c0250040100340180c1001c07001428034800582d10342c84c5507840b102d4020340780901c4400070009014036844040c01c10b441601c01000004001001c0c810102d070f031145540d99074080c0381e0404184000186025040340d04000030041c40 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 469333354 1250 469332104 469332173
    0x1140403020303040e04020d0f05031234030e010c09090c02010b06031801180f110301050105061606020f1603090e040809010e0a09020f13050411030103030c06020403060203040f 78
    0x11034050319241d20411780b0719900d070704c00280da09000d200014410000204200f041180c00400761140039507a00302c0b40095922000d40c1c0300800e41c0348070000210801c03a81e144c05a484e901c1b0085100e070101d450f0200d841c820214000c0d00b0740e241044420700050b180502044102c4062007800d1900d45688000e2014414541c000707030302e6000c060441c80d0903054458030302501d00c42c25800f503403810828038014a00803196050005a40e1032105c41580c107000d00b413080025501d81807080300d0584200505c805c1c14024030046103c04943d245000700c0d030080e42044080001a0340e18050030109901d0307040441192041d18004100c44100c2d400001d590b8030410a00000400d041d081e1048140c0a1810f40d041d02403510000c1d40c2d005007944500d94041c400648050389076503060090a03980c06580d170200d02c4075a1340741800120303542c0c0c03490f400c0c80000520040c000203214141541a05005050144c102503c940394130301242d000f960121800c0c0350706800c140030007800e000d051b0703454002401c0c02558120b50140 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 469334604 1250 469333354 469333357
    0xc090603170313150c180e01151107120210050f122d101a03010b0c1e0304030c1205060a0e0f1e0c06040609060f0e03010507080601140403020303 64
    0x1980d400010003100044100340f410718402425600b00840041162840101c0c6000b494648034441c0000c5030190f1001e580500c0f071800c0800c54010350090a580e81c41c12500850a400c4030354040300b040861500102400010007102d0040e0120a000b558800e1081c4108400303803203090320810078440c040c07088805590055065620000f0b843e0300c801c00b9952a80c0010030001041a01002c03412031440151400c420301c4030070a881580c00489091a10340c85c0d0b2030013010039254411f58840c4c03490400044c4020382d5040050001229a01e0865a44518030008040c190701c056000c54a81d0344003060800c03d108804040d04010724190510102174006a12500d0b144c0d10300800012020703807102c0c0c00013514141080b20f0500030303490800b036591060840e01d1003a0001444e4907440302d64410701d00b00001c9480c007030b003c0360100d581c0c0d0345407900c4003071925106807104600c03100120103011000880503c40d440a0040c64891076050343c45120074a01000090207850347d124103180d00c400c0c107000900040c1c90020 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 469335854 1250 469334604 469334633
    0x20d030f09051f050705070b0c2a010e071a0a08041727150706052a0c07081902061803070803040602060c0702010906050a02011401060c0c090603 64
    0x19000c0340d09266010090301521150750010918800c000d0740843d403003410551250740a500c1502031040d901e804904075240e002da900050074034148040800c1e001c000c0d580003401c072640c0b651081c2c1001c82c4404c4001c270743c100561032910341c107075111298900e04150501c81013000d8106201c7c00386000010510401250041010b20807c0c4aa8180402d041c80543c080c3e0301c141300f01d0420030540d581100c1e20201c0c01603400d5800a102005d56140052031440d2100c010659801c1501d4400d0401c1e8a5845003000391a0203091300d40c0610694941d461512658030400504035101007401c2e40d00c05402461500d0a00994051050340c0c0160407840c0a02038505d01041d00300303404958103500e44101019184a5070030040800c0e615102c0c1d20b000003448070001c000761048917615004d464542e59140b4440f03901e889414402070004280d20010700105026a001c3e00415400380f0000a609800030754041c0f40c03003000c0c1c01c0780c2c002c203039000e044c07100300070100d0250303000740400300000c0c0402455643c0c0d02c0813803070b0f845 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 469337104 1250 469335854 469335857
    0x603080d050f22050c10020102120114090f040c0803030717070c02090c0d02091804031b080f0f09040603030e030705011103030720030d02030402040b060307020703110126010801050f07020d 83
    0x2103803c828000208600024014024001e02c00340c01c2d40c0c94064000d41c054040100018850f40c00015504408a00f040d4084070250020000780d540c15540e40c14500000c1088444484051011824140c00c0000e10320406554039130400303c4140c450040500d00001b002c1c0420010420b00320b00068845140c0b4542203022014443d89030f10380800528080c1c018114100d80001111041e0300100c10501d031907901543c02602d40b03801000f903180c1c206080e40c4110402402d511000c01681c00315452000040ca040f8460801c042c0c100188400000d09a514070b83c0300350300185142d464007036940307418000ca84c0100000d00380310170081c4c000d111085e102d01004003000248980c6c1481040360708510126010442c21803c01d40ea6243c80715030000380250070503103040c2d0040c1c3c5000d10648841c1005001c50b80607620380d030010b01c41c141c55680c5080489180c1104a4108182510200100c1201e4a100304210f0010b280b4074455604041c0c5441c00c41c0d500a01803507103040302100b400180c0350040740716407410459 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 469338354 1250 469337104 469337161
    0xc080c03100e150406090303060b0a0c17070f06090605070219020918070f090c05042904050d060509100204230409080f13090501140906030a060603080d050f 69
    0x20180100d0810b03a40b4002e4030342c02002d0303c04000c20440c40d5400f40005034420f032010080c06450309078080c260300607209500d000c00c0d049100180855601a400401441003184951414005507101582c40000e09822540181c07120000c20401106024040d0710203d00d10003019003030101c664690003c00f00c44d40203401903d249001c58108000030b402030403042c00010440300c880d5a03070181c3c121804803d10030198442c2c07420405008075440342c03040300d003103500045a141e1440c03495942200500c030510f03001c01c60b4190401c40040c0700d482e03600390980781c1030060000244525084030468200f03094680c0e41019948100010300591030704041b00503030000031801c22002c0b40d00010200b030081c80701c074601a0440d48007180c61440502c0d6040200a81410f910b2803c3e20305070745101c00c0040d0340080c002c051504504030340800301070500c0304019520290040849810200580f1040110b5080750405d99040704000342c1900442441c0c0900303500710031021082c04240c078050450304110585010840c100044 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 469339604 1250 469338354 469338371
    0x16260a05040323122101050a060e04091209030506010504050610050714010227040e071e15030501060917190218070f0f1e05091c0f0c080c0310 63
    0x111803c01030714124648040318544071408035000240c1d004000d100510030b600425000001070042c400e00c0c100c070000b41c402d194040c02c100b000c0c0d4501c200214050f07089030f030300e42440d004600a8550b18409602548840f600c0c04c0c1181800b40c2401c005030400c034015030400040c89400d40311500d00100150300f41c5811a103070171451600008600001100725115030001c1400303045168250241d001403015000000c40004400b000d00c010b403941c0c94903001160700900c4d01044a0b41c0945800d81d0140010780210284645602d00316860044510b14900000da541c80103000d8cc503004028100500008642d204200c0b103203d0803650349800e92688a1600504907050f40110746030310413500c02c3c0f26030002c5030660300e01d4543c1009204541302038a0b0000104c00142072581140110901789d4002032220600e0802d0200080a4500e0f500c240b5820350172400001e1080d07621000b200038240524852504a0703400e44140c02d001c2c950403d2500046250b810504486402d540e000400740380700c1803921008201d204 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 469340854 1250 469339604 469339643
    0x30509030412050102040e01061706011d03010204090c09080f0c1306030605150418030c020609300706090602100509010e0d110f0c0d060207050316260a050403 70
    0x942c1d40640e0008a00069680800c00c1c190080c00a452280300042066a40c03002e0880c1c040950303144080c40555000f02007481944104c420b007003030030044600c540c0041d01070400700c6e0132603100e035002c05880d0355035150500001e5845800c1c21b00400c0e005005240e481258524641c540101c43c0d0100c2c480c04004840c00c0f1949034503041040115000744081190b490300c0901054280c848209442c4241d00c5c2c40403a01c64800d407803850140b07598160b51407034558030455080c0400c0758012000503030b110303031450030210701a42c0c206400a64400e001400c00ca4080c40100e1580c40c064060700030344140b094002e401c0c810709500281040104510b5403000c04c0e0760b11540038481c0140f02c109000d160f2401681146c0c02071030740155102100190744801c40d1107480892401d02e844080a40350741c2d034043c12042c072800114015030041c0500601900a81c1e02d4889256001360512140078401c9a8290084c0b144030004042c00c40c1740704002d5036202170b03903140c914154801041803190340002040065110810410075 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 469342104 1250 469340854 469340857
    0x309010b031c120f09030c350309121603020601080304140439180303080402100905180403020f07080d12020d0609020702091302060d0507172805010305070603050903 73
    0x20b0f040d010017000404043d040051100c06c0c03101c01658403500f03111120b0000d85c8540301c200301da26011006403159551000c0b459000f64400f0b8261041c0344105200c0f0410f40807080e005028003114038409010707510b4203280203420484141d0100c00345400034041000014011402c85401d0036040b60006034480c4501346018010514030400400308400107010000c2104402101407001b9031520f44100721031040c28090a4030405000003400102c00d41c0118005052807107140c81c503001c0a0030046070356070b190740200c2c0c402013158088a20311034900003070000789601804990800240312000d8030f903507801c0090041c0e0b60f24080c01f59404004108400e04900d64007035040d00c2520006840901c501ea59841e00300700603400c4800c059100308a040046980d2485440905140c55405800c4d1b90900606035480001000010580d90900200b110003000c55030691001a206080c2c40c04583e040310485841d030082a24072030f020b080294a008011300203d0000034021088500501c2c1c08940d42d5180c15505045 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 469343354 1250 469342104 469342121
    0x30609040201120f2c070b0f07060c080f0a090308060f0d1704050f1e04020d02120a0e010b04060602060c0a0e0a030302150a1418030405060f0309010b031c12 69
    0x441d460213a148403d840c50340c201e0410781d4000caa00034100d21800e0004618001c02410b6040c4903032007890f0400030f04440c00d0281c0f06803107451040c2d5003000c8440e10f904081d298010590000201c40c4c90402081003c8206c8654003c8508601002900c8032683d000e4128000a00f40e0380c41101114074011907a6943c8440c0302015600600c0c6000040c1c9401c144801a0041d0141c984074403480e4010310307981d05000c0c00d07a0241112818408000c00c00180c103000c020345c08070860b460465002c001044c0103d0a0514040c0110415200069481c01034070b18242156402c4012620450a050040243d0340d4001070790307034008441d0880f803951611152020b407003880c50208181d411040d80c3c140001415004101099401101c824121003540c0740c490000481e01a00311002051040c1004500f6200240b800a40012040f0301140c2c03030315454000042e040c0e04900200da0303d0390800420400d00070801c0c000c413022100701707030b004280079000a0403040c000091090304404100d070320104207800800c00d4100004 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 469344604 1250 469343354 469343387
    0xc06040b0901020d02041202420405041406090c03070c0b0a020904050c0d1a0109060f021f0b040b03030f220f0605030103140a0312090609061503031409010203030609040201 76
    0x1030f00c1f40d498803041c400341030310001a4441c00001040030140b10b00e400801071410410700c02008a400c8001c08040da0549120f481e07141c40005200129640d1564402c1c803c0080c01211070007100e181440030428600c070014515020080c042c4144100075401c1141c501030f4a40c0000700c1c8a45681d050a048028090722801950003820304050182201d0603000070540c0c0b9442d21414804045614004550f43c11100d0300980010040401048403030300c03400303000f0000580d0b807040c1c4494840d02c40c8141001c0d440148203501407a0380e010310310207518040c0b05000c4107850a070091360a0526800789480e0900900111801c1c001c0035001d078800c0b110010705010080e001650140052545501c0001c01079042400111235022041005c141c0741707440024032407501a810341e0b400c0000600408190050101860226045074607018440c001602e50f0042e03038030800195403800045851800d00070074810242c201040401400c02090740c00c1d990110450794005000d4034403c456450307078801212050403c01c540c84 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 469345854 1250 469344604 469344607
    0x813110d080720010905060c0f1002090315130b040f080409020310090510180b0a080309010207120c050f0105270f031f0e010207150e01050c0c06040b0901020d02 71
    0x108a9071030007900300c2034000c045591841000b5008150380340691540240131920400c0200821b241c00001402810004015210443c105a480314500480c4031168403001ea00402c801686080c10404401e00080c201c034008a0360034100582d00400d107041c1c0340580300e4090b4000040900c5550b600d40742c811030340510380640c1c0da9515030360400290015200000f56402421001494504500502d0700801219841c00c210910340700540b0803260440905448440d19200302612681e50094040001e20003000035564440e078140c00203007005410303009070283c42c83c4440b0345400305080741d6480702502c02c11360301420320070310180050b03885000d403a6204c103c4a41030740c414481a42844228120f40c007007610f0780c0206030b28840030942c80e16410042c00d0021900090603640116884e048110002f120a0006140054075180c19406060b1302114100e040d8030742c200c44030124401d00c1100d07402082c2269490410345560046901c66002800140c5440603000100d49038110a6041b0703604c101c01c3d401b045 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 469347104 1250 469345854 469345879
    0x11e0818250302040501121a0702010609090506010510031419060f090f0b06030105010f0305040f02030d0801230f10030b19030c1a120403090e0106030b091303081311 73
    0x108008920b400120f0083e814000009903e030025050511100e0344800103914003c0030502d80816488000d10403c02c540d212800041d2040035072050600d000d01800281c1030755030401c1d003403195001603410403008051801001d0701440703a01c4034085800045000c0050303641461080c043e4090300c1c0ba034001e2607680200708000201030025600c8031203407181a40c003d220b210105820868103000900c2013602040480d0f001d20403452081d4031403075100340700b810192030043c17039600442d2421611044038004a41c1c40701c0180008000c4a502445034541c4800354400d902131031010030680340c02c031040c40b4001e40c0c100750b0259601c0d0090b007045802e0355016090002c3e801c0c040a011040f00c2c96403105440301202054086100c001c1888a100c103240b108070018909907500e42864040d6030003c2040e0104400701c81c001c109401103aa0081c003e0185680204030300300707203d00b0040032800151881c480021a49078100000741c00210741c40d400454011424880c85140c01d0041000c4512001b1030791100c1d0301c105c50f = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 469348354 1250 469347104 469347163
    0x30a0332030c03011701060305060118020c1203041b0302060703120e0d030f0c080f010302120709050705120c091e030a060f09030201201c090f030e011e0818 69
    0x81c5040703400545c2c0146841017607491842c200c0d401c900019249421200c010712040680d443c001c070800b030301183c0c018500024918004d0410600e5034111440750b5000007484113001c0148804583c0c002100389c1d07003d4151856000908074400c1440080500c0704094081403003002c00da0151040003104030658611b190041c17030017401088000341d45c1d0780c4c0500c4c0004d1040340600c11107038244240809084402584d003140c0820889030040313400302c246403040040205501c0d105000e032502500454580c1d0303485500410050410480007014007001d0a41804205002da44490182c80900f14882c24941038105a0002c203041004008d0083d003d0342c10019020744990300c82e40000803841c040d80c020031040030a41c0e400d00014152403102d010b42d103000d200748a0340e244c4412012499503204403000a503041c9580c3d801c1078080903080181c01286141805c0a02c650300b0082c10fa107440c020800e480c20010702c202005c0c20340c0c0b20180001400580095211a84003000c20114102c0f5400705201e00d4241a50030f403 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 469349604 1250 469348354 469348357
    0xe310f030809011e18050d030b030c0d0f030c110303160c050d05100e0c12150105040c120509070503030418060602120405010c02010c1202010f0b030a0332030c 70
    0x100d00050410380003400518040c8104803103c2004007101030124081c91082e400350280705800c52019440307100e40c5000550030083c0070481c030802e45021172140d1508080600701104128558007810303403403048200107194000303088402d540c1400c2c01e103034105603410419080c00c48400c010341c240c400002d0055104480c0b1421400366889540700148141d124001c0c004140034400c00105950700130300076500c0c5800c554200c002081d90000803600e51111000c0081c2d90400c03501c841c0085500b00388111400c010506090318007400c400d1b5001d01241c0c9841f01c000b403e2441145c8600c1c40a5035980c00b080100400f804480018800141240c0d01c5585800344010001e03081d2150b004510310704040043c0403400440c4000e0b40300f45207820103090920701801583d01c202c00b550101d0411140f051220002000c0003030720a440d50040e0300015055500b11700e5501200e85c4040010320075404021540b000a501550388201001c0c42c242c43e90065024030607504003121040883c50304410b0100030482c50441c481c0 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 469350854 1250 469349604 469349633
    0x40b04060f1a121b090421090e1b1603021005091612051e101407120902031902060d0207030c021008091b0303160c1e0e31 54
    0x140c1c1d61030300f800b600b00c1c0305607a02c2103190342440310720114521406034a001e8000c00d51050040103e60303d40f04c10030359038050414580a005022400c000001e0180322443c0b4a40c82d4001140300c02c0305058002da000f620f41d00d010740e40085c00d80f000c0988107182054030038048084000030261041c0b026040005401d9201c00110351170582c0501c13400d500140c0007c80050040c05d0036007080c054207143c2d108081098200001102c2d00200d44504203140034600d0741071042c00081ca100d03482d20301090a003003800409804643c6d840342071182c1050000d90150345c1c0440d004940081e941d86007240d120070380c40030034180c0c014103244401540c804104030f0203054004032100016031088031100100300e000403081c0e4102c041910110010f621590b40400700043c200c02106030200b008044030b0a1074140384c070550424001003403c803150b003c1080d040000008841540444000c82a03807064500d06180e9200101c0b0300007000890500d0300c01019807401159440c55590040c40e09041e0540b40e502d50a20003000120030 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 469352104 1250 469350854 469350859
    0x1a070204050f13080d1107121d03070b1318150e09150c0c030705010e010b15120402040f0e031c0614010c290417090603040b04060f1a 59
    0x440096581040b0005a074810107110b01c0c8200090010b8940408680080f1a8007007816501c505c08241a0018405040d0703c900c2448581800e24640c02c2c01030a5060394444480c00810f0340105007603541d004603180081d00ca00846058680c5645002c4d00040103a035401148800c1d1002c800c50408082d0b501300d00e900007188080103652030754550000c00030714006c640c001c3e802e41090128800d10400504074607040301511130343d24141803031120f50701d00f9540070f000c0c11541a9035502c00b202d6a500d007809006d10400084402c003400c110300040c1c01502d4031074080d00ba6000841800010219035490b44000b8044403270780c004000c41c00d05070b6640c0d9984d901480040c680b040000325608104038030380c000c0c00150342d60b907811010118400c038015564002802c008a8640300d410700c01c0f83d8a0030410840540c1c00c19805045c40b5142031504007003000000d000fa0560380001e0401c4143c0064513201c0c102c03500990f200c142016103903101e05100004040d104074845000d402c04e410300e40c0340f180300d4140140c588001c = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 469353354 1250 469352104 469352111
    0x50d050f0f06010b070f021203030907030203061f06082e03110a0305030a031109180f07020715080601020a05070b040501031a13090503041d010f0e1b09010203041a070204 75
    0x101e0801c0c0e6520b40074840c101d50340c101005500c0010700c01d0400c3e503040c9403000c1c01482210905d55030b02c45c02c5400031500e014235580808000c0055260811065420280041800d4002d40c0f078031040c1042414140152814000c081c008a07039503c8031400082c011a40301c5140c0d01d201c0100c00072900002d2590b01c400e903200c02d150007144000e80340c01c501c0300c4101c9500c080154641192508268003030803d130000c040450000340f0104609031101c00c9102150341782940d182d800c501e00005000600d410281c1300404540c00300f603043c410016111141c82481c1114200205680c0d50030300102d182c45641f0600800c1d40c060a800041c0210b00f060182c02522001d0300c0a000c110451084c584602c561003101660007110400c1007102020383d688130744402800340f03041d80d28050300d82c03001c00c48411481c0c1d400002e400100c0d0040001801044044d0f001c0d14141040031002e040c0b8141c104221130003400b031041c1c083c00c0003400400c642c0c02081102e004000303051142008014528412086801241050b0b010300d08 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 469354604 1250 469353354 469353373
    0xc080702030c070306180b04050a0c080318012a0b1005121504170c1c0306121b09060902030108072709110409050105190605130f06050d050f 62
    0x442915645922940101071aa2540d11030380050020400c2d146c200401c8003554102085000346914410790140f002081d13141c0243ca041f040700c850a50207402c00380c0050080c00d60741d11071400d0803800301c582441c001180d0444100d4120100c01103102d00703011440c2e140c03100c1003000303a032481e1240b0448181c0580031280381d9800a221302e207518800041441e4002520003400d00041c1c031096500700d03010344152940001c5155900e601e0340d2002c0e40015041d8001c1603a07140304101a0208a8244540d01c0c0031b0001500d03200700751400c1d03035022400500441c940c005c108502e04e01c024640d001408041c8092140c42d9a400040009505c28040c9040364055a000882d8401c01030f0f59288555a980080041204070802802d0080c501283c00720b071070007030030026031001d40d03a14040d00c1100c5018100028540c01c02c403a1160081060304500054241850400c0000341d4541a0000000d0b91914000c40e0081500d20240010185500f100f0350001c42084107800340030300001d008818107003601c04c0341c00210 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 469355854 1250 469354604 469354607
    0x1e1912110c07030632310201050c0a02060d0b1302041401050a030f0203040b0619030503160201031b02070e010e01080309280603020d0c030608060c090114030a0c0807 73
    0x2040c0304611407981e200b240d0810004003640c1c010300707035003c000f0141aa2050002040710104842c214075014515100050050303a0708030b00103442d00e0754106010401603140080d000c41c003400c040c0c40060f062010115000c1c80d010b5050040b801030390b071b00801c225940c0b001c0304140b100511003110803a018074880901a042c1e40420b200302d605441e5038800d412000009071004507240e5211039485420991150011503220505001460003144560344e41a40c5240007001e12008140c40b0b4a5050884502c43c81040444c001200300c030a0708107002c52019400301d580c0010707009080000c0c070102c00340400c8040c50020f40d6003c10400d081d140d00ca61040031999941c81074504001e0280a01400d503007003044081c02d10725143e00e00c2079080034a0400c164003001042c4501003041e91b40e51010001c29000601700300c080c59684166100f1803107074102082141c0c1014002540da6500a0040d240d451001540c0e92460703001e46080c1d8031004040322075035a01e1070001da50030050100c19401c240402c00c46d101148409 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 469357104 1250 469355854 469355857
    0x150f020304050705040c051b0d032301030803150910080142080303070309020418080d020904060e04110a121e03050c070b070b0c0306061e191211 64
    0x7140c1000042032041c1c02c100800005012110b40d51b01407040400c0b031103214020550740c04c80880080f0f00601071801c50000060140c400c045400750310116800d0800a0412000b202c0c5810759030080c3c1c40d0303a20f99076800041d8858070141c59001da80082801c0801c6080c45d5580610416984064000d011100c1c05185e81c2c940036034040051401500c605d20071745619644203550f240c2000c0705e0855003140c40da80d614503500750350041e03d150b000291212260401e600f094015101e640c03000c04041d101d1a20151650a814020521a10f408035000100c650b015516034100b00702511039451042214203051808009040126400600860302d2000000744c880300c5620b9045d810b40c101c2000342103200000040c090b20030303510600b1010b0000601c010199503100700140705c060540d24101a5540c54281000986c41100800a4882604c02c0040082d1525031034261001c6800c5107003c01c1c1c0c68410701090200758000d220070201581c905c3c0b021840301a600115501c02c005100700c040020294500300c0c1d4815 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 469358354 1250 469357104 469357111
    0xf06050a0b030f040f0204110a0807080702160b0304060e0f0d03141915091505131a060a05070501050a1e0c08070f090807080d140703020d0311090d150f0203 69
    0x1283c010f840081c2c082564000a041c242d0720007800002c10390034071340c4210065004030907907200042040c01088283c079080080d107034002c0c050340020036841d02080e141031080c041a01455124400200120301040942d0b080000c06a08000548120071001000b059407051041c0030440003d003041960b081015598001d640641c581c1920007074540c810071a40300141c250030310411a07001030300c00c000078a1903061044900d40b44490008001e003c5c504000c0011241d03204910b0400d05251a07030211142582c0c44040549000540d6065210118520280c8050085d40b038090324650814040100d03803000e41c0d000402045060110385001d0f0680b0344014226107000401401107030303100c00806c0700240607170280e41601005c0c0c5000381045490742d002c0c508041c3c081e80681840d034002c2295082c0c15401014404040b586020901c3c200180d54500a41e120b180303a088030181071f50344441450041002c0d00310b0303a400da006018603000000d07614021001811203100000403600c2c049028030550010f00842c0d00 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 469359604 1250 469358354 469358371
    0x120c0a0f080411030a111504150c150e030405010f0e090f090118051c021501051011010e0c0306130b04020609240316110615030708010f06050a0b03 65
    0x500039080401d48200c440508180c511001c0e025903524955810400201c460b803180980d40034441c2a001803103984443d4041e107144000c802d1005220741c003020009006403000511300702031135000c2da052174280024070004110308981444c160300d00042e4000700800c1101c01c03c2e60380606026803514202c500815200d0605da03c41d0401c0c0110350000d14009900b13810107d48000003e0303004640c1c450800c440d4000c0d41c03c84441e0040f003030b0b0710f041200c9000c450740a14041d002038040300480e01402c1031440c4050207164031039009002000d00c0d00784100d281e0b64403541040000c000e4444211141555a404410268400d20031100011038042c85407003002c1e00e081d400b15011806485503400c020858120481058106460752982c02161b818140040c0c2d004000c40b8000c1d030303a4102980052070320144001054144130f100184020042ca000880701d07408803031541c620440300c200c100000c1c1848900e6010901c2c96007400516181510140c0c80750003104c0c3c0403182480304030707134030a4000180c3c0001c50301c810 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 469360854 1250 469359604 469359617
    0x1e0b06180a0504080c030a030506041109100c052a0a06111207080906070f150504030507030c11060301090609050108010c020715020114010e040203010b031c0f1103030705120c0a 78
    0x501807242500301d07a8000d446582014104000c10b540c031451900000f208000003511001804103e09041c86000141c040a220a0346850f0744030002c1060310742d101c46200104004002d480382401f0080c80401c1101d000d003074122002140d0043d100c3e805141c5801d0081c800c5e540d2000004100d07000e101030000445005000e802c00c00800c102400540c0c00000007078076140e00411070f2203c00d03550341c0c0041c0501403040700884174010039810036035044010007484807900c901c1c00c028000030a800c4010703903e506516192075441100b951030400b10400c01d0031521900018080004a40c03100c43c0c2c1c00440a540661004022036a640e08509090b04c0705c0001500150300112020f1102002008400b5008081e40c000801d85000c3c5080c2a40308900c240d00c2107808070940b01c00c2c402146002c1c0100c407034007082240101b4280024207030502401d9540e5400405001858420004030b501603000c0c0ca407507a001c001602d4680ca42400040c0565101d01401c00ca440029000544c005211000f40c4007803031183d94a86 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 469362104 1250 469360854 469360861
    0x30a052401050a14040b130e13110d1403190201061406030403090e090109060f09020109180b062205010908060a0f0e0a0c14010c15090206071e0b0618 66
    0x5440c164401c07010031003000302c2d4940344c1180a25080050004003100c550b030b581c2d5a004004c01940300c9a098001a6203c0da8080038001403011001809407400d40002d00641c0b0054020009441405131b440c0046c130032030b44103003c13803044400800500170451004001001809042c0320807401c80742c590140514035143d035201101e003414031802466200d03202e410300784407450b2150b000c206041000c80e4a8038890391209084000c2000302e010701500520300d5a001d00480c00141e0010b03201d14150f0061103206010000b80201401c0150001416034030058469070344c1d6400759060703040c81c0802d503041c0d0001c1805140e000440d54401e0070f8890884402d40d02401203a100c003800613000d060250008868030762074000c078400c3c1c0c4400b8070040704810f12580d021b191031460500b4608035503098900da075040c003c403003109101089a00d0021980040995000119220240300040c00d034040d4810140010380d602040442c01804c004864401074001c1d110b00d9038590324030007003102600704020140030398174045010 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 469363354 1250 469362104 469362107
    0x30a0b150a051807020f1204081006120212030f04060801090c020303010803070f1b09050f060405060a0302011202130308030f0c0910030b03100c031a04180224040902030a052401 78
    0x10b8006201d8815958204001c41c2d086190407c0200021100c160008003000340711020064592140301c02e440601c8150b1519034400c8200911590103402095014005401098240308554580500044541e2201d807610402032112500340100c245262500810ba810b203030002060364102c80f0040c3c002d40c0750801039a100006a03588071812100c041100c101d00c50703408001e04070040a040040c02c0000c0398a816519040030304d10180c1000d015a103080d0038400541c40e40d0500c181520b4083c20003040042d100c54100e0000d10481520704416102032002108120044004500480c0380040000060720354500c3e240c1203200304540035501100002c143c0c00064029007040891140c0201501e0710500c203452010b090701c001f1510580002e540e8841c40341024181c03800031036081f100b51030400506511080d490301c0f03580354440181c80340215000c041c1102c448800703207802003180641c1143d202d40c1e03034a15a6001e500207580070b50381103083c800021388100d40701d010151581038940f1441c07501241c2c5d100 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 469364604 1250 469363354 469363399
    0x20106210c210201050c03040503071706070f0203031602120a0306030209070203031e06040e0f030c0111090a0306180f0f06050606120105010f030e03040e15090702120306010e030a0b150a05 83
    0x3c0e86c1070758042488009450751781400141c00500c1c1a040600922504990541c10030030014a280140080c1c1c00440781c10300c0d800001d895010041c108035a0481c00d8000c4180c0c80c0c802150340300e550700c03c400038600c1006541a0000c904a034800c0d6540c00d4161074030305080c0c0c0c4034001101c40035200300030141311f410322140c2a0030650704407202403c00101e441a00d45803606007111030000c944143d10004200c90b4501c000d12540311241c4602c0c1d0664240812100011140007161101a01060700c8511a0025a41140e00f00c00074552056180c00c4914140ca80841c01e210743c060b043c0c45c25483d180008010b400c003242218203003910850440410784c21320700155428035481805400305a55920400818038040008202070491b0076202010351034843c001d42d050b0481850910701949110050094181e00003807070203440060060305580760345e590350040f2051440900d1560380340c4036000408090010508009018883c0c0e200150030046c9020240011003545100c0c40f0341050030000b5007940c0c8203e408 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 469365854 1250 469364604 469364617
    0x1150503151810030b060111100e1608062a091002010605040906090507090e070e041b09020a031d0d081b070305030a0b10170403020106210c21020105 66
    0x60002524040750700d840d90400350b003224040040c0c4040b140600500100f02041c81d40320101746070118904243d84005074880c5002611007030499154441f404042d0002c1c0030840c46201d4114002e2802a600c440c219580c0d041500c082c1d0241c034a010f83d051000894030711115003038280d8000145425104002c2c8a442950320000000715580c40c880400c00d5980c500880280034090310020801c10030701e0900c3c0d0b007040d581d03900074500103280140c5400b00203800704100d42141c2d85d19032080c01582d21400e04200060720096955004882d940d000308101c0800e501030f2a101070b01d5030b010422591042401c02102c4801101030445501050000a8240c801c06030b05500c4804100001c0c031940c04c880340d10034503400440c01180071950110030021810b460b44030b4409212012107450110258104020304400120a0041c40c1c03172460000240506000b50440b50090034800d40300d8001114400307441c0c001c4030210004407207000d00040c000600c14003031001c007190820f141d10000e02030301d11035005541c96442103 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 469367104 1250 469365854 469365859
    0x405010809012c120405090f040501180606140d0b0c0a090302040212040b0f1006030209060c0703110112090b0a0209030712050102070309290307110f070e0115050315 73
    0x45407002128620009440c0038070b0300702e940701600d00b10a083c0c580d0800c0300860300249801d00c02c1c402042580c1d520716200d0b40150f0750310400885a195410120f02410661610590103003000c0c59142c100070090307000750111120701110201920010b420011f090300c0f88203018007004d503500042122040050004d00103102070b03040c11049281d40c1e502003010307a00400740705054007810f00700300801e1154448d400341c2c0c040e034070380c0181b84e8038506010f90803550340d0325010360410140e0100300207200c2d4580340111140030b00784404803074199a407440c2c142c0180ca11003104c00d000039001d581e4a0080c619034010540d8495000c0d0031452a0750392503005d0f00082d080000b480741d040c413401d003000030320201d403104032030395a40a80d0015a0300c20346400c020303114848644c0b08020b440d0f540003c1c542c4840310500e21482401485505994a496002048031160400d0f0501000c50003940c80300d1080742000905035040f02e000d4448140240e81c0ea0fa05140d14400101c880e4000c207008000040d403072140d0168541c441d0200 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 469368354 1250 469367104 469367111
    0x30d0c030503100e010b070b0601110304060f0c06420509092e0b0f0d030c0206090406120605072303040f140105060a0509060a0b0903010e030307050316030908040501080901 76
    0x40f4101c1807500315080c0d204c40c0d814500080c150081c04561003600d03030301c4403081c0bc1500d00b1900c251002c6913284511720601042104079111501028446d010028440d6001402404001090688101d429101c900c0315040d401c000c0e8000c40d0598000003038400d0b0324408a0141e2101c51030300d0b007801030303804000b040c01000d800380740c28103191342800410340000690350800c0790045008040e068011142e1120856109002202d04400c40d580d0385000c900c2d00560514242408401e188041a910b01071300d40b03103a5119087c02c4003c1034215990705031460fa180a44428092030312411415500032210030b65901c4401802c54580800030030403c02903800a02c0340017560342000980e240c0740400301c0c40b07003920000d42c0d44070401d120851800070401805404212203429944c1041000202960150f10a0340c0ca2404042a00282590294456441503010105880d03491034982c80040c017640c41140c681d002c9100c407541c0013180c41d00c40d11036207007010390240c03a25103802e08000042d2004140100b84116039900e = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 469369604 1250 469368354 469368359
    0x1403190504081308070b0d02090a0305010f0e1009020307030b1f061e080108030315030a0215130b04030b0c030c071a071116060c0813060e0a05030d0c03050310 70
    0x905108052180380038480c4280c8820040040000d07075006907200c4901d550000d141400105000d5040b00e1441200080c0140d4400611000c2803075005140e10160455191801d10a1702e54000d4001020340089a0140d4016980c2000320104880b1030142c00b039090f9004603806c1c400641c29034910b5400980c00c4803a400321200a0400480704441500f007400055082c10014140145a0f20220044400c3d420128010342c180404c0c2c80d5a4000180b8880c0d500411070300c1ca03000758400380080752400745c0207066100300c112219280b0800f03510000807d00f1844079090002490308044043c1d8081d294442c2996110381c0b140c4250354504d4102400e00d4000c100104100f000040e0f40c41c1100c0c1800c6407150360b1a2440c03501c410003801918101c1c0c011441c6821495045001c40c03180c010394400d4800600701005c943c1d0460402c0c0410340a044240d5040800070940440d0a41c0c200c1c076814082c070022039203510354680381c009154403203d4907440900451505080600002d020f5001355134810000750541c0000ba0f0b = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 469370854 1250 469369604 469369651
    0x20f1018060207020d060f0204060e2d12030403060203010f0f03120f12050f0405010b03010605220e030d0b130c122a030b030d0306080d120209130c090f061403 70
    0x700310500100c4900d2340094204005c03600032501900c4202c0c01c89280380c0300445105d0442d90b4030190101c4c15030400500c4041004e40d03440500880c81c0c0c440701400c480e2a15100d107084cc001358000e00603c03082c00240c40c40000c6800714114120152540800c4140e0f4091105034207603003294004e401d56080c02030200448442d681580300702449000c03078506541550400d0308280d42100c00007240d031800b0741d06040d0301380069200e24442d40c1c000b20350350410303803c4502d01c018243c006007100d0790001c4190000080031040c002c010303000050340c442c003190003d031820b92216020040724500302154000c40d5050a201300150700960101004102c01c149d408a003016920140b0071203000c4981d2840070070f9071000200100c0c00d0401114085100034142004176a0400384415550407040328040200a42e02d0002026024140c058480100c2e01400c60030100280140b144c01800b00017109000107010b6800014080003920000070071100d554072500c600440c0550305c01c40c143c0c1300900700704c0b001a0300c0c04207001d00c0 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 469372104 1250 469370854 469370861
    0x6051002160906230609120d0f09030b01050f010210060803040303170106051209010204031a0a0c2a0534151713050a03020f1018060207020d06 63
    0x400140d01600c01011031500c1030304144869001003860a24107031081c08100b82c00d6107150406030301c0b280081102c2c0d00b5130001590611a0902054014080c08a04a8482c400040321501012551142080112051012146c2c910b0300d00c806041340c56503000400c80723402c045810241ca80010b1068402c0e01100705410020b80c3c8141c2d10240c0c81c2c2d840003030104145a0700890158886100d5540c42c02294501200104280114030f1880030702c654400218808600950466000f5940401c007c0c005900f40b503520211400110340b0000c405080c0340c42d1603412482b562500c00380702e11424895106042e075924100c01140a06821541840341c0c0300c00803690b101021128184aa0304881186409242100310244035201d91180d4500d06140c0490380311680c10940d45031102d115881d95040d40e5540341a070194413045540044c1050141008410a2650114203d00409030070802c541303543c0d000340c40003c21200c199100900184031400040300080c203540090001350700007407501070740c46035940307075617048 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 469373354 1250 469372104 469372129
    0x90b0a0e1c05040612150308090604091b1b020108070e01110709060302150a0e040906021b061008160e040302011401060f020c0a210305040902070804080c060307210605 74
    0x70070000301d01080703850b901c012080d10b0200140c0d006d0050300e0364107100c045601c00c98040145002d501040703140c0a901d403c03040d20001d2898010502031802d00601c4111100d400715850000505102c140300c241187c02ca0104c4042941a5034a0141c0c0d61100011654600f047d0502410044c0a0b0200c1070609401c100d4000500783d0204e0000302a8518070412850100501c8a0b5900c000248520140d850308003103495000e40040d6000b254000b140c0c58004000e11806603103440c0d07004035400c1003a20201c00100288602d2140c000b1604154644049550390070103946685da400980000501460107100c10f8160070030300c0780c000400c0e0241c00c2012440005001d8010400240340c12800d10402541000711122188068800c26410790a252880c2039820180340304250701d01d5402845410588103004460041c2100d503021900c2d103616140c00b240a03482440b900800c1c1c45004003441403490100105e81c001c54a6031101c20b204900e11400c18140c0140386041d5102540e204030000702903c450454500 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 469374604 1250 469373354 469373357
    0x518090102190e10020109030914060f030a050708060306060a090e0312040b0f07050a0c0206090d170903060907050d02130902030712060e0a08040603021303021305040510090b0a0e1c 80
    0x201d030005030007813100d00d00c0c40b802c070b800031a070415040c0c5d001309401005030b02c241c4503403034400140d4105000202c2c016100740c1c0d004050401000040246440c01d59211900070165503803880d19075100e00d03041644c0c60b501545d15590201d200c1074208130701c42d01680b001406049030410780c2d0803c24003c0c4036282342c94044600b502c03409514410401c0003c202510140d01220300e0600c41c0c01c05c90b005200502c0c0c2641110001e000c1e4200045106142d40e402c80405d5040c0c0d4000c481c040032041d4407000d05482e801c0625a0340c081d11407140485c505a202007840703025500090180d44000c1029000c020740644ca842001f242d4030742d2801811f025031424000301c4050802400005115501464020200c880f5441900c0041d006110b10b000014201c1c800c8904030354042c500581c45914238052071802080d6030748002d6000014000110750301100b40c01c100d03c90b60249080d40d01c42c200181c104015212050b0b002406080c80800140c05034809503c80d19080c82054101c403001c0d000001514546907a5089150 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 469375854 1250 469374604 469374617
    0x1092d030b010302030f0d080f040807051e0d0203040b03040305090a0305030720030c0a03060c030b031c020705060721090320040b06160b130c0303030c020610051809010219 76
    0x410b45c101082041201456440100000ca0320b10700001c0c8804000340115050759800c1000c2014000602c05450006800ca81130701c29500a4498078500e40c1420481d10800b0700881413101d442500110030340341240c1c0700051403455585c86076000c030307900d40c8030352a540c0d800106400302201040c001c10240031754034440c04151405c40304452107485d07401c5480d030120707200e03034802c4809005035200d01c013509044990200003c18841c9001c407064000d0101181c11070303054861010300095910007040b01d6001c14205030256002103403038005000d0305104804024002c21903000d01140c140c1d1000403441401401d0389429400c591f100d50354003001c0c0e0740d0070028812246004031348616a01c0c1c9441140301050048bc1e100f031500103c2c001c802e040d520030b4480501442600c00000318000e24480800052070390080c890341c08a40c89280c050001c0c100204808014845c00300000d640030200d4940505a81e001045001d05020a41d00b0002440c1d005003040c002c0d5400303015061241d0368004500541c030b40540c9500 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 469377104 1250 469375854 469375859
    0x40e13050f0a061104080a030804210c060510050a0303120219080412021f0203041a090a0b060d02010e040b041d070e090316120e100e1002070501092d030b01 69
    0x42d0960b0800c0c044c82d880d46100308010803200c0c0f13001803603840b5550302d410450980da9450604500c4e8540e0a40c00c2c08864040040d00e2181550244610b81804d00c9a0001c0166032941100e05151000d01e008030f80c6c02004072082840480e008065181028031051b00c007620786000a00030541c4c040e81c3c0846800881c1d4020240400c1044062008105142c2880189003520421608911349400f040c0400c2600364000041000d1041c0680303015404502d4104903982c40c2800c80f0103da66680c1c1160649080c3d001c0d4010506918140a0913042550143d6403400c448400034200401040040300c190f90255450041600249940b01c507205032802200180610500c0c0400c0121800401820018540c008000240d02c41c8445140c00c40c0494000504070002549400182d0740300500c61a0654092428986024404e5100d4224903002c0801d5400230b00041d84000d00707a03541d008078007613140442d2449000b4402032801c5004200144610300c07001e25040168600000756030100d40050b161941d507007005 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 469378354 1250 469377104 469377113
    0xf0819110c0604090b1203070506061f020a0605150405040309080732060d0e0109021519031e060b3006010309081c06050a05040c05040e13050f0a 64
    0x1290554055403000d45680042000062594440ca00032103007065aa200c0c0000d41d600c0302d00f90110300094101c00c80b541d9104034100703e90744403c21603103030b84035050000705400c0e1070603000d04051040c0000d400501e407149482e580d00000d40001860302020300040030324034000785e0b103500481e4011806601c51103801420014002e05100d8190050340380c489400e800308008040d407890311502c10380c885041d4071b0b1803450700002455622500c11969280b5013058508003030703000198803445900744204c0e40ca010b11450140843c1041c011881c545404460103003110341c110b4000d4210203c00715140360460400d03c10015007a00720b0724190440c650096003c641c58050b54a110382c3c80010350503101c119090301c11101d001003c1060002c2059040540350054a030401c00410f0954100c50001c81a49020388188084c0b14007c0c506031288a100c8c2c424800000f4980c140392140039103412465a030986018100407000c0b200c043c020f000c00d0301c500d00a070b40ca400420030a10400700c2d101126400b5103184004e42c1003 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 469379604 1250 469378354 469378367
    0x10807111c09080c060910050702090a020418111c18030206040b010b0405030d050a03150e07080114010e04090804240801080c010c030315030204050c1c051308070f0819 74
    0x29858071391110904265981d2001e09075030300d524040311001d070700314070346541140d950240003030080d00090381030103100d60244150080c0c070540e164240d6201c46030000e1034541e402da601003610f09501c04c404010a1141c1c1018104040803090f00e12401b05500c001124018a00080d01c0b50550060f0494410b2000f0001c042203038900400104104500f41401e09000985690b101d601c0403051180c001007107141240203800c58128101420030044090790b4884840043c034004640110000d075880001203010302803000c41c21481103040c0d42d805148a405000c1c84001c01d6039640c1614682c4041c003000039490903030310b6203800149811000507400854070002514055060300044802c3d000306040340c3e040d0b6413110000710450380500e40420b100030141c10070314220f48160070194100303040404011504454400415420740040800581d550010180c1b8049900545a105602c0ca80d0502031012a030b0080c040d0502c140142c0341850030007401c0d651001c0c503170b00101030345106c100746140c10051944c0108 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 469380854 1250 469379604 469379609
    0xf080a020109150509030301230a090e06060d08041205010603020907030905071a0f1c090615120506040803041403040801150504021309050702010603050f01050a05090d0e010807111c09 81
    0x2d800b03101301e040132910380e40c682c0014024400c2158500303a550025549c0c9810042800c01c2c041c040c5e1081688404481003d441d41c452036480074806c400c0411041c1c04c10403d1001440c1c0c00c00c00e41818142444907540d0740c4a40c841c0159029904c1e00000700140e0303240d4040c4d80c0a20502c0d1400212849a4941942071810580c00344501d4a080460304280d0a5904116014580c0082c2041d40c0d43d00300b01d1080154035500c48040842c40e140c000c0c0d407820400a980420290100603460025042d40d0f40020080c40d164588010040e810020100d00082c661034041c681103031143d848001040200407881d03240d500035034050155607444607815201103003a00701c00d40103010140d0303065207401101081c40c000c1c0c0b4510300c5001060360b903c800060a1038400c4d07020101850744401901c65980320500f2042c080e10741580d100b030015213401c011a0700801c0005460661004c1a200c2c54040d081080042d0359042b0002e01c044180b110340c100400400c54180460420a500c03c00c00440172103c16100600c1000d264 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 469382104 1250 469380854 469380893
    0x13090b070c0506060d0c031515090c050d020c0102270a09090206221214011817091302040602150603070f05060702031c02030715050606090d0f080a020109 68
    0x1074488000c80da011a545502a006540c1114140305920b41240c1c5002e681d4005050000c510107141100591a000809009010f0240303141c110f80b02c40c002c1e030488c1e07010100280400e00030040801c11106c1038001e0100600a0310006040510400680009031000038030661545101404103440e45801a59880138280f40d0004101c0611030b40d010075114400c1ea44102404100104401940c200e91039545020300078810740352a50307900500e01240a01c0c40295400e105500b00b20440c0840040f4020346044180c21041a11000c00250f410070442d07404500080d80040100041511824290000f00001c0c80e00798018021200030010500c20b8a0700070300214030039001504100003c5404000c000280d410481d0200d603541b40ca0300c0041d250654140f1041d25101140a00104958000c000b51184500888500480ca29450100c1c1c003103400858000d6800385e41400881501e0410804e0041001d209001c1501581c1191b00d880403690080c5141d480140e4440c66080100180d4160130303000c40e000d5 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 469383354 1250 469382104 469382117
    0x100509071806140304260c0a0c05060304051c0c0807030507030f090e0a0c0203090301090b0609070507031b03030e060a02041805060604090c05070b0106022b020a02040b01020c13090b07 81
    0x4801c3c40a00510010f032000d0400c030591001412102c0c500b410004040c500d80100c02c5d40e80307400080b485d8070b500c20780b2820741d040b030394141000865040000440e48a80e500401400030030b2600c200b01165a0400203004080102c2c00400348005050800184050340c002d071a0103480385514503005080d54242c11030030042041c0810100140000c500840d034005402840100e01c086821000301d19500845082d240e066013801d2071035060100100d2050701402060701d10510301c0d99406001e0306c02d4410074100400041c44000058601c84015011229240c481e01d4080f8441000c00d14052a1100c20b558a401d62640000c0130020640000342c0c80002c1c0354100d0040c045464400002041c5000e103100705940c690722466020b0b2503a200341c00300c5075200d40c45001c41c0d000d542c5400d00250303a1081d11034480c2d40741d03003c2c0c2d5004006040d01c40340c4441020039030b402400000311a600f4840a400b900100314103510841c403080b69103698801c0c0c1c2c0d80b1241d203001c00000b020b400c2800c2040b940c4502038241c2091101 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 469384604 1250 469383354 469383377
    0x1f0e0a05061e0105030a0f110403060c1106281a0103050a180b04110a0305210705210c07060c110a060f08041514040506070e1305100509071806 63
    0x42d500150050803509080654032540c401e140440a88090a250050240307800c100b00b030380c1c5603420044e100b0750740a65010004602406004d031443c503105c0540c40c480354442c03400140e03400d9840b03981428030402c02004403150f1a4002c0e040d401d644004030080554410503901540b00c0d40d240c42001e82c0401007103018011440c90b0311000180c07010854020382303c5803440001a00303202e03120040c2848898041c100c190700d55520305225480c1d41404d612240b43e8600d0074691200c907011101503030708140c1c00c000689418603191a001c800110700400710745803242c0501210036040003d00011004110a48900020480500d080305c042e64620270201d03c80c082d042d90a00009500c28600d261078052810000d10b5030301d8034185024040d00080c0000300071130800180050b40c09240c06624045c51041040f00d956480f2a4410388054054141c0e076500440d690010f60b001e24065040300da040700048584080340c5072200c1c0490410041254000301041c00c0702c07403410b10316000349901801000d251400300c0c0b0218 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 469385854 1250 469384604 469384639
    0x9060e0f010c0f210b03030c0d020706090b0d0b03010e06070c0215040f120519030e090912030c0d0b03010504030c021806060d090305092214060d0201081f0e0a0506 72
    0xc45110210180012410f961036804e81d5114a03607500d80101180d888001944000d541c80e81e0502500006006600b00015104c0c01196007009581005200034208800c10b60406d00409080340da00307a00d5900e540c40071005c04030030320000740160040da803a40d50910540c0180322001c0c060364242100140201300801c58000e5148000003510032401020541a415040c50b07454202000d24600a4080c440c0e081e0f0100358014220b07051007801620706002070b80d2150b00c2c450311411400341d0310100d2401040050548045171004140c008101c0600050319075110001c0303800c443c412207044022907001d850305000d5141484c01c54401800966940d4120300d01403000c582d09010310070015500340d40742c0c0c14801c1018011810f803629070101820305d0144681201d40314900c403c00ca000c40146a00e420500440b46100c10526071080380003420780074420f4800d0703004442651001700f080c44250300703240c415104550884821001010001c840750828144090007034205c0d0006088588198241d00c1c0c0074980c0c0 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 469387104 1250 469385854 469385867
    0x60609060512030d11040801060b03010e01060f09050906270601021c02070e04020a0902181e090c03090304030f03080603010f060e0612100f020714060f160309060e0f010c0f 76
    0x55100306000c074800e040003200c0e065030b0050f1f421900c469400c058000c174418428101450403030320107004010a0340d9031800e0603940c5a40700c880100000d2400318040c0f2090528882298112602410a080200b0300e290303140d1601c601000c00008000303c00b8140f00c469a070402c6a0b0100b1070551110a00d07030842d0000180d034800ca00d21a1107114000b00001905650750718901200410211509542c6c440400b8030707025110400703000040c800d803d03818035522342880c440c1018100703032030160205202da140d11020340c2d220b40000f000c0c05540d200400005c00081d040420070324415210380c84504290420078101401e446201c400c00c482a850007004010000c1d01740180c1e03802240a603030b40104000300143c0a0305020034070b480d0030101400c00c4440c40d03440029600804095008031164a4103191000c1110b484400598603481011510301c0820700c2c480b801c020f40400b034455402d00003810001580c81d4020b441d0114141c0000350040011482902c03801c0c00349102400311464550b80101d5001d1010b03100 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 469388354 1250 469387104 469387117
    0xb030705120a0f15050a0506010206010f1406070212030a08040c05030a0f060b031614012a0311030412060522030f0509012a0c0602071202010507050c040906060906051203 75
    0x980f182d10405021312050000400300029030310030611140c41c294a8801c09014191002030041c428030000094240c120503142040e980c0c7e103200d0f0f0440804260402089070020031003640d002c50658510410319100300300a000c0184144c4420584d8501400d110072150f42c83ea1065001e608849910300014400d050081030a40d80040700203100c40c000750200c0c0c0f902c9110080641cad00c5191402c080307080c1408021441d1882c800b40e13601d69142c2610083c000440480c50180320071003185a80c0c0c0b0000030702500140017108040000c0740d023019954202c4040b840e44c214010f80308980c1c2e4100703001704d2040c925011819012031090030b203007120450b54000e08054003c524481000320115526129a00c5280c6080c20070041c0348028200c020000e45002103200403c000701c803401624140014141e0002c00c9210859141c0780342004c00c0909a001901c0039808644112510b001e0202e00d52080c1d40c0390f200b8000e440780680c00018119042c8046803080b18040e411051007040e11100c1c070151400004210795a = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 469389604 1250 469388354 469388363
    0x11040902030f010501110d2c03010c11010c021c0e0d150501061b020901051c060501150905030607090e07051b0109060e1203010b0706061a0c0c0109050619050904020d0b030705120a 79
    0x42c07280850b15001903100100c81009e031700d5424040c082d02c2030359118191a4841401c18001c20060b0004401640e42d4034070b0540c4c1c2d0044801100082c42c14502070a060440c40c4009003407400c0d40380c05130340c3d0340304951040b03140d0228580d600c0e4010322803d94400007920740302c901504003281a503420380003d01600c00500c80c2901c99484c0c02410003108010304031510740b195100d0b000b80720310350b1240381160407203840381e00160024026000000d068500040c40d41c1c014001511407000c40c5042407000e9550a0b0001c0c154018080b0400960000000158446040030700d0140001100d0003d854040b055459182402030194001c000e1448050411002c0328111041204140e544851500d0b00c2000b403e201c0e8804200303c10440d00003401d4002c0b2800401180c0744a2098901200300781005451844450207070b69000300d4144400180c11084e4010710f80300300e0050034240d040c0001107001034140d034803942480c4640c1c0d4030b8400782c00c054107007040484080e0408440a0745603496036298981d982e0106d040140 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 469390854 1250 469389604 469389647
    0x609191737110d080d1b0f0f0c020a24020d022d0105131e15090303060f080102070c09020a020d0c080d1503140c1311040902030f010501110d 62
    0x1c00003151003000d58910064040741640d0160709100d065508901e4545c500903040c603520b088480c0203030001001100c1c580d120035103103082c40030086540b580c00312408014481c010842c400542da91108480040a849000c81e200b0341075211490160401c40c40c4140940d0b00c800d420710798081d00806c0a582200510f210085500c4400420803030150381c182c43c014255180005201e8402da0103007801c00058050a90200040751008110402e240610005416003c035441c42d500c0d000e03a123400140001e4040e240c00719117151543c441d850200d809622a81013a94001182c004200800510078002c000001d011404c2000c40c1001940340c4181817818002c000ea00e0144204020043c810b941c010031402208000c0b09980ae0081000c1e0000c0c1e0100351340d0b0110f6220f0804519000148440c4400c001030003041d141e80c0304015607005400c109a80080c1c0356001d0001107807003403151001c0c45c85004404000289549404009010402149004021034101546100c0440d0300500e0342e10507510080300c4c16 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 469392104 1250 469390854 469390963
    0x15010c020a0905090304170705010c031101021b010c02210906030912040602010606030e03070309091107050f03071103060c0a0e0a05061201030201020705190506091917 74
    0x1480d07024031070300000821843c120034000c1906002015009032040f128040f0500d0382403402c0585d40351160b02c42c01e0300141d104162140080d102c7c1031080070103109040054144104028402401145400340845c2c4e40c0d5284d1000045a40c100f003122101038001c46460350800c86d04100d108544209a00540074180c00004200c0314002005070a1605d62051200c0d6242e03929030070000d000c1c110500c21480064100040424200e00c0070045030516545911008040b40c68981428094030301e41004416501c000d11091000c60f000303014000040380c510010f50387e030b0400e500e070080d410001403c03200d000340c0c0100108842c0c50702500c1160083d038480d08050001380401400a0309154403604100e41040300410303942100ea14014150307041e00d00c02d2b0280c07a0050b44400501c50300703031400e082608200c00d65460800460502d0303401040c1b40403000d8500181542940e1031520840019800360f120b800a50540002c03145052103400480265403c02c0e50f180340c1e040b59402c2d2041c2c011600480c0d4240c102c21b14 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 469393354 1250 469392104 469392109
    0x20607031a090f090c180f01090204080a03030905030903012a02030306030307030e030c060f03040c0602030f0f0f040509010305030403030815060307080603070e070e1c05151003060515010e010815010c02 89
    0x180742802000034205130180b041050700c0d41c039402c001d0750001ca9447c0280004103220103d4020380342510b001c0c5005100b60046910201c001d003014101c2136a0318007042018240c0c545084c011150007000507140e050a844580010209100c1003c90050444d0001d02c1400181d07034021089601807501807800034421881040040c0c104003c1c0c0420f41c0e4001c43c0011f0b50000daa010402030340c801c80c0140e0641000a940302410f81c0c81c4d00c941c44900340e004100300310f4549900d01203005051801400c40025061070744a01c04982c4070b50007a0400d035920362000c18100700305507006080b2944003010104800400c2c1c1c145010540600001d0308002c1840b00e403000190860f00c04004020081c00200d50741907142c02e11010281c02c00c08644500d6000d0085403843d121a18801006a41c44950020007040d1042c613014080500010142c080c880f010158240000410b50b9405100d0003103140d03400c0c1c040110410307800500041e10400440f410b1116810401400700c880e400c0340380a55a0a0800d0100400103200 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 469394604 1250 469393354 469393363
    0x1305030f060103080d1427280c0513060305120702010503060d261e03060306010e060a0b071203060e04050c102a030906090b04050d0609060c020607031a090f09 70
    0xd014401c0f11b100405c0764200301031001541500c040c80c004415951044401c684420f4011034080d4503035000d086e40030b11100c0b40000410001d000704c0b0400e500d55151800141e002d020700000303491031902c8140500500001384291001e130b0040088142c038004840c0d0010340180002031401d40f04401507991401030003100b09201e01c0c090942016071000856413900795146800000802c20304c807000c030780d10961262068007182c2c0150801402820268a0710b441c612541000800301e40e0480c0c013054000036145002409816000e2045041414808802070001c044035200da2210b401802ca140501010640c082600b00564400b60703a08c80c0b080065881c1135584846104501c15802603c0c6061800591340841c032424480c4641d540324030080c2c1c0c400007129083d00a00a003d240c2d00100020442c92910004000000384549004900d0b4020741d212101115001070041f80907801c000700708614a64103110b01d0902844858a041d8982c203950040361503070000412800c420301d0820085201102e0030007 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 469395854 1250 469394604 469394621
    0x30c03350a05070b100e1501020c0907090b0301030b310b040302032101030501060503010c080703090201020712080c011d0304050d0f0f1401321003060f021305030f060103080d 77
    0x13111008142008140c01d28407502502c14400020203a0000c58150054400c403001c0140050b80180340d0b098242d81000100b28015244009004010b000000c90300001c030003640c001e600880301d0f035645207000840c08200701c66140410882078003000d030240c604180d0590007039503950042e08402c03082da00d80c5000d0385984075070516200304089440b014464504052441030589100d1070081c007117548d661040c1402e840104030100082410f600001d034549120380e000200c005d00520450301501d60301c80380f07100d004900311415648884000f40e9011f00c2c1400b40030346001c40411000311203003202e0150f200da449006502401e8414a040c000c4e041c280944400640c2030b554200c140f00110002501c1c2c2161407044088000d5055401d103e080d44155600c01c40d900310640a24565122640340c0c0030402d100d84100802c039124480c00d0403004000704038103100f401c01c3e01140710740042c0d90b0480d540500c100040740d82e010505c60b42c00310fa9491803440d000314200341100c2e03104e90469100c0240d91070303a002600c030302c0c1e = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 469397104 1250 469395854 469395863
    0x904120c0c080708030703020111071a090102070f081801080903032205030406021c0306030b070e04092013050405030a080402010c0b04030e0a090c170901090c030c03350a0507 77
    0x6400c0031843c2130012000b01034482c4039400800100900111080881c000d4140290139810749000c00c0c281c0308560507500360302c003045c0c0000610341011076035a07000d07610071040c00341c1c0c41c0700300414a000c0a084d0b82c0030a241c1d05100342000d210502d001e0882d184c1d2844024400031288454802c0101d29110040d06428415800420380c4d4aa540b1244002d50307a909100900e01403805441c24404010301901c1500156501b0500103440303552041004d035075410048020a800507651100180890351030304d044882c60310055000715204e40040204450009000380012900d0b02e010300780301c005030380001207c600c0600380c02c02c00d407284d0701d5000684030800602005810820002c040004141d40114041c0100c1800c44826100949440010003100e407005030120220300d5088101c0d20240b540d00485a200c100741c0d002240700c0c80142d07201c0c69201308690046444600454042c0200f11041c4010b508444451000c2d19201e551108030100002050780d0041034100002010448030f8451003c40e1b8100c0d400 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 469398354 1250 469397104 469397113
    0x40902280b030c030f10230a090e07060e031609230c03010824040b0c09030f06061c0b1f2d050402030c120a0e010c110c0904120c0c08 59
    0xe104401c10f0ba40100d642c8522000c550300000e10480841154000351802002c405c566400c2c41e03075403000030b081d5850000360b00c082c11020014681e5071500030048110403003005440b4446c0b40c05800340144042003c118802e40102035040040780756158104201d94200e10f001c80c400c00d0220841048907110005e45410980c20801c0004940209009504807094801101c0c00400b0541d0004d0030620301d007c000c2c4d203418848010501107070306060b00d140c1080141c0d01651800c00e5400020b46441400800e940480c2c0012081010a260181d10004038010f1752449001c3c0c15020303501d11400e41d0b0001c15658005881d2540808050760008100340070f000003401c0f806900a001c124010050b03d20420689107041589001c0b69904080c002c1d00d020f00203403109a801c06030600340d80c4003442070041804e81d03240c0d0380da00402241c0d42c0c00d006008a078041c50316040303030000684602a080c20015100c0138050f5984005000010307201c0b50100740d5074810782ca070801c40d1551724601a46440802e500150142c401e = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 469399604 1250 469398354 469398361
    0xa091406010602070b070222240503120f0f0c190303050103050606180a09050102070507120c09090209161b03020c010224040204020708070c0b0702040b040902280b03 73
    0x80040d806050701e1054003180d00669645100340c00e603110710386000303400c4403202c1c2a408131600202a00f54000480c3c0d0404600c07444164600d1014604615601c007100e05071803c00c2240e0304083c0a024010312941c04402c0c0f41c103508407183c016a10401e80340740d102810000d0301e10383c029030910403007201e003004014010304030035981402800390400f8001a0381d1802008081019403030003803421030080c000080200c1143e940d4822000040c0240c1005481030f54082208100254090200304003a1646075903a400c120254100318900552030b800c00500036180800368070140c3d44004c403d07030348105000c0740010b410041c4e20044445000201540c03101400c07024640c010560045052980ca00003070b8221000c4092414244080e07441c102c56010621680d000414094206a00104403050140a83c3c0307181012a0351208803480b407560200d100a08046404000c40c03130700740034080118408075003d0202c0c020070b40004550106684000c1a00f1400e010741003480849404030f1802007580450ba41c2e00c130f14 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 469400854 1250 469399604 469399643
    0x111503010f030204060909030e01110c030604080432060d09140a0615210602120109060602010605152b0c020c03010606030e03040b0a0909021603110606180a09 70
    0x48071804100d11890400101107a00b404520800c00665099920075003d4002680151080e0100002c100b13031600034865030701d4682c0c404000c40c50081788035071007159942d4542022002124840c4000d203000161601d00f1050840190003032554005c0c040740c40b0740d52500080d4110f00100404c10300100786043c40e0000f4105880301041c244651800780c28148940980b8511b0300f00500d1045c040c0e80207030b10411041450001c5c0280b170507000b15210b0301005140c000381500c6a810407400340d01411940b91200000d011282d4213000d14402480d00362000b0081d105072002c6640940039811440781d02c03903d80205901c6060b207504045946440c1650304004091004400075100d464601c040c40c025030800d080090030500c40d1096000d8403610201450910b41098840c544560098104608020400101252104036440103202800062804a03a0417500b407030041c0c500030400b4400c60158200c1c03810080c9a8072518501b0020380c14200c007681071580d4840800700104103204001c6c203c0322407680b9111102 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 469402104 1250 469400854 469400879
    0x1c0803160905102321061c050f12040e01151206090207031d03060606070303020717120a0c0e120106080105010311090c091503091903031d071211150301 67
    0x4003000c0015219002c20311180001c9104a080d1103c03040d00d10405ea0f102d2a204200d0b081d04564000c019020302002800302d03442220360fa4100362002e41000c171164005003c208800034000c00c1514449060501c1e24040c8040c20038144140c66241d080300f1066909a881a0b211001c0c10101c0c070030400c000303503c411001c1e0003500102012004105000c02c4a0012800c01c5200341444c0c030300400601e165541c0c1010300000c3e03004141d04909041d02072010000080b40035400500b494207044500d0b03180c80b21030000c80c095800140103054601d141580707a00030158070003049010b880083c4c5000c8200c2c02880b100d0f500411440c0d025220715443c100c004400c1000e41261506da1810850707c074003942d1a004024110703849103a030701d113500c0a18044200445400304010707641c400790600c25a491000f034102c25294844040200b02c00003542e82d2980080f110100b1001c6404008100c020309045007001c3c039680040303854a0000d808020300000c0703152715a407201c03074072442003d0740e40200741c4950b076806035141d61 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 469403354 1250 469402104 469402127
    0x180601021006091508010e070620060f0a0b060901080708070c1a011505040b04090f0f0906050a1a0a0513150303090603050c1c05090f0111091c080316090510 69
    0x540346103003c000f5003c40e050107011785140c0c1f01400b810031249412000c0e545440c0250207038140e01209485a41d442400740001846804e0601c3ca803401441d050f8500701c04c803030440450350b1062406104c04034090340d01902c9103070300039010f081000032510303210b41c1910301c2060018002c0092020719440c414080d03800c0c244c10304032602c0d14050032164080c640143c0d00c80c080c0d409011404201844104204a4560423585910244900c00079060700c00552000039900140416950151100103000c4e60700514410704001071500036454656644600001c1c4424043d0301c10f0610444004020703150b603107525808055010701004400c550705584e8680a41412078030703c1018042840e101c00240824801f000f105c0d1040d4900541034125000008014010000a03101101500c1003020004104009100b03c461000741d50105903100c0300c2d44000c100124414900b07440201001045400000781c481c0300341c9420000c503880d640041c02d91004100c13100821030340001d601c90700d0281104216034010026142 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 469404604 1250 469403354 469403381
    0x2090718032a0308031302060f030903031e0603031c0213030309060f03020301141c0c090605040b0a0522090206030126010507020706030908040e0406060f0e0618060102100609 77
    0xb054903018142c0020103403440003400e0004200700040f8188403800640545910050400d401c00401c1410305110341c000f16040030b09a4000401e000201c009440030400003004145c0c170402e10728120012a440e8040e0003003413070341d48220b9000e1201e0020160140d800d400c460030a10070101d6a00d04004000d03100c148914404146c0461003c01c1041c0300380220f0341a17942031700300c18036001c8451060203049207028074120380260710f003050313107001407140050341c8024a070003140070131400e0420717041100f180da03400f10305132262201800402c000d803a03031010030a2464284082000d03402000780c1070405411480070081d4050000030011070221701d001c0d201c400c14030548500c65003049198040703a003250000e03514070b00540d01200c810441d8a01c02d410a02c803c2e80b0034845d007410b203a6201c0d5849181441603c3c11210355407500c40034851130121260752401001040c012982c5810084040f84100d20b601050034504100308000940a9008022940c1d000100380000c0203840e55a02c451801041103941290 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 469405854 1250 469404604 469404653
    0x1180c142d0114070f1707060608010f3209100c03021b19060c0306080102040902072a0308031b07030e030c0604030b010e06010c080c01050f0f040506040209071803 72
    0xf0904141442920321450380001000b40801c41c0361504800c500051041032441d000070808180005c1340d6010390700007061000004100040d01d01102d005039052420315001c500408003504980070300200d034143c0c00d0b80c26005003020036204c2c20000d03400c00c40780b24413481c58603040a04943c4100e030300d0343c02401c0c06001220402c0300c076003c004ca0140c60703014103d50401c034a100c07200e071140807030520350000e80c184a850030005159a5070b1101182a40c2250f0701084200743e0104000082c0a05040307500070600110f0040456540038041c184840500ea0001074552440403000425146014100c00250090119580c3e29680289030040008490b404100d000340501c02e003440d100c0c28041e090b5016070b940300d0007504880c0c0c04e14050320b0310a0801003585040000d070f00030b0030300407801d500010700d8007112140001c210f500d0616910740070035002038000082c25000208010204101107207240e040340d411507404040780c4602d03100300c6100c840382084034200c030207800d000400c1241440203000891212918a03 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 469407104 1250 469405854 469405877
    0x50a0b010f0f26070f0821030c03150402090604170f030c0c060309160b040303020d020303040f060504240b01031821120212010801180c142d01 63
    0x10941402c891203804040302800180207505001440d402c518042c2500880f9420b540d41d180022400340a82d012241c6a001106074002c3d200ca05004081c0d405902d00d001880d50a04810a40712840001d00c400008450551300350015078580e01211a07945d4028a85a140c1392504900345040310301d0f0011003968030519180303920410022056604114440019058840c610f50500c00c02e680014494142e500a4031418540c0c07040d0b59040c000981642419240c43c1c50542c980a841e10f10090038400030b540c418020803000a8584605412403503200c08045401d03140c0303103481c644031004110311400320340300a0401d2040007599480180f428209903002d101e10218040d00c4500460035000160a22441d502e441840d11007a21b140300c2c040c1207501d86002c44006204c2048200e821507031080300c0450100e401040410424015006211951018902844101c2d0348581c00e822141c4140c84440e8180c44440740e5550354001c801c0c6555810100d43d40c000100040c1c40401e200408003440d000c104000b07201e = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 469408354 1250 469407104 469407119
    0x121e03050103030503060f03010b04060e0f07020a081c0b0307090b03151009021309021602041103070c060506030a0203100f0c05031302040b12101b1d040b01020703050a0b010f 77
    0x2814102c03609520f446103951600418418040003074038100707405640307030b005400d510b84552090340020b1911251152441c1001045400b44801c00350402c01154007000c81e4001241c0003000302c801c06000b03185404055135003101c1000203841c4c2c00216a50601415000040c0b00605400180c06c19800f141611821104204c04802656055402809864025105001e6230f5070941c028011050b54504851080340e0b1800c0c180181d03400700000c14000d0b1501c0c5000030840c100760191141c0f80d400f148443cad0540c94042d40043c406681184098915526500820703000c0e141404580e22035500070701034611708408282c0300310241c100000c1e5820410f2a103e508a492480382d800d03a401108802464454100b03540c003000007820140d0300304c5502c040b080b2a891261001004404a00d017040314010900322564804080c1c1700d94607004010030700c100301400011590a002c01c0c0f001e07034601200d0000341070380b40000403860684190402411840345030104402c1c40049403116049072805076107001481d1f01c6919 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 469409604 1250 469408354 469408361
    0xa0606050306060d09120e03101b0c030e03161401020703050709021c020313020405070f020709180b0103052a0d0210030b031f05060d0b04020607050a121e03 69
    0x828001a4060000c26842d00c0c08000a1000f541c031300c940424511510307180c84000700188140c81e00422201100380074941001d1141d150a003010007010003421540316030200d11640c00a1b20002042500030220003014094030034085103103806011030703c949091004800ba25442801281101030800c10445980d61000400301c042d01d070f1041c06046a18500740700c40000e50040801c0035202d100b44808070f15113403680d1001c4c522504110007540002c40c2d142c01070000700c0b40040c1000c0100121203140340081034000a940e002c0b40c5000b0360004180d07044500d4003580c20b9441c1b0303008181854003070000007845000142a054100001000402c4024014014a42545200e0525042051565510f01501d0b08810b01600e003101c600b00462420510310000b81030040924840c0c0c4240006c0140340340ca00302d40c0c45100e0f44508180d0b1031441a40e1151121a00c01d400140002e100d081e002440d1402c1010074080700440f16841b1100b030704034481402000e040c510108070b0b403401000020a10904c00c42c130902 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 469410854 1250 469409604 469409609
    0x120a050103032304120c050906041a0d020406090f09020306070f09030311161701110702060426062805150103020d060e10060801150206010605030406181a0a06 70
    0x48445900c91070f20603000c103080c10b08080b034402c000020f02000846078103115994507414404d40f24aa81681003d0800000d00303800b806090049260202d007110030980425406800c9408607400e02c09090140f000401500c03080c1c100c0781d80d107030a240c1c80180d50078268211000d074610890645801e88e985043c01c0301d1a00e009642040040d20581e03040011a01581d5869104650398055401960501c5012001e80d4400c3d402080b20310700b801804c400048080c819540c405120340144e619003190358001448070f02031405a2041c21100466410b000b103103401c482000480040156082c5150010b0000c61020501010013090f00001b845c0c004036050318801c0c1803041760007014072a610340000004600940007041c003c680350f81c0e24000030599034144101c1501c50700c41d4049003540030703052000044c440141a84510a42031294400a234402e40200e0101c0c10b640782071421544070354803800d10f1000b510041000b0580c0c00c0f0740a01c480180b04a5400059034082540c030b00204c15211590380e281250061f2 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 469412104 1250 469410854 469410857
    0x601061d0906120607080901062c090a1509050d0f05070f1b1e050a0807090903050d0c0e0f01020c150c10051f0b1207051b03030903120a05010303 64
    0x101804031151410360340c1280c02c848003404491403922000403c901c0d18105982ca031010030301107010048030f82000d0140e10040c0c1038400c2a0010100d5508031614413003076a580305c10600601e0320010344480420003034040d080e83c10208414030340301c1b07440c0c492000709621007099406014449814a4203409950340d44030211440c0c4d00c803881c20980e612450745016002e90100d403011000304440402c00d812104480c080c0c900b20159503d454030f485104001543d50341d20142c041d8207c030008006d1010003003000e00403070b524008042540c01c2c0a1804517081e11030020800c02151810301030000d0349a001e1000701c914901510803158480e00c0500582c0d840100c4407160f58080540c90030030159103c1e02014048400d4800125200118055045000e480741100c09080f11412516503111401d81260200000c2c20103034030161a044c44007086191404000f000b00c810710030005035000b00001c3e0400c440b804143c11070300f80c4c0d44a040540101d91a070f80645910440d4428035000304030910356511800d4102ca515 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 469413354 1250 469412104 469412147
    0x30f140306150309010f051e0603070e01030b0c04090c030b1014090f031e010b10030e100e030910090f08150a0b12010c050405010801080d140f04030c0f0503060106 72
    0x510b2908050b66000030403800c0103548444da03138110180540141c1d400380350f488401c2c0c084080c061121a04888004008900c40e60221004105d244c0c408452a41075035041000c04d00f00d550740210110309403280d9808195140e00e003510005200e549680040381000d011114401202014281210000321410541842800402582900f49030040900c5801031016040da4903c40c2c1c000d0301d06d83c1120b007140000b0700300d94480c12040140d1800303540d0720b141440d07031341001c2110740045e0800d1650740b10300e503602d010182d40e40d0302050350703610f010000d4a10501e80100086603402800b01d00504240c2c0502c81c0c900c0750041110046100480400c2115000000c5100340c0c0143da1545a070300040c0401080c5140c1014142c28614500c50081c0104400050207440f81c0ea81d552500c0300050842c44164070190a5070049030b00399560503409a0301660b101101050640c54000c88040030181e0311640d400103005005542c0c002070610300c5240701001301c810480030b03101c00e070703980e4a019207800090585940303241c0038 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 469414604 1250 469413354 469413379
    0x50f010507030c05030411010f02010603060f020309211e040b03091f020403170f0c0304030807021509010c030f030e070807170102250c0306020f0d05011502070b0c0f0a030f140306 79
    0x1c101c591b03e0009c80caa10011070099503c3c2ca4410844150310750158006030000100700814408111402c5003070051a11411c045000d09000d081e18000d0142095a034480203100308901c0c0007a105890140c9070841a03559a418400115550340e18038a181075541400e810a8101004152007964101c980003a0214606004181c2042d141d51040298030241c040904c20346c400c242c03040000d000910322480300c4c55510000c90040054003040038842005440d03007000b1169090364000010703056140d1504214040300ca16000c01e030003a20894212520903c030302030b8006070f01e03500001d00004649080c078800b0352030400150300d28203034441c15a80845541c58044140411000d40e881041020700500c070f450909622640c6010599001c09440c0401da5008584103a0b4215184901030040980c03200c03002041010100103512045c9901c900c20400201041d80f600c9080c0c20300000111200602c19a0f800011514014040f0079034806282d0001d090700314619410154042100e0044c50b009000d9204600c = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 469415854 1250 469414604 469414607
    0x803070b0903130602060f0a090812060103091b170a2f0d0305031f0f0b09010309050d0203031608073507120c020604020904140a050f010507030c0503041101 69
    0x81000e8058409848208800c0700303c0540309007002c000d000b260b4080c2c503060511820000c0e4010015203600d5a4618041e80d800005584808a5942c111640710040741d0382e80d2a4016001400ca500c005010203003d540d84070144242e9076203150941c0c40d1a1a800814041f00301860740c0d500c0340301c00090000101d420740c01041075210380a0a00c3d803000614098448d05000082410703413484080440100344084148118411658803c050403100e00c81c842d460b452800103c00e5a4090611503582e1380040050500c000364820340214011580042c05c60f8803145840000950380d0b4003c444d010080440c89881c03027031407441217114500402c4a581d903000c490001c04044034040c2010824080c0088a104c4c144910f1411403000f24801e800d2615070502e50032010305920180d9282488140443d00200b04000c0141c0d40c0050058200f900912180c07030342241035240c1c524200034050f02500030b10a22504486461054101c284030f108240e0b01403100710403d0000341d80790301059800402c0c0001e1344000c10542d5 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 469417104 1250 469415854 469415873
    0x9160e090f010216060905120403050309041107030804030e0105070209010f06081e1603091509110103200702030f39030a061e060603020c010b030a030503040809010519080609010e01080307 83
    0x1140035a050f6000e42300c108000300d9440d0b01a506c219040e8001041c600502d18051040d1516a072182c80b03900d1900506940060002100400c01818810941030001082c1d1252040d42c0440e80d02420b00710095849100d220104030303282c0303e44030006110400107a00800320050030745a06d5803e2492592a031503440c200040440450000c208141ea604039070000302c3c542050074055034400c5000081c45048508018401e800010600340c103050407d03044064502c0d440c0c24014090380101409074a580aa01c0003070304151100d400f800c19407080a4808420100740499508005a080102c0c040a030203820282100103540e2041d6615421a011a00214902c0d400000d080d86100c201042100384001c0c050044a440790440000a81d0200e01da80200d6800d104816410008030002d0071100c0f0b02d598024000e01c40207200400691000c101c181040c0d0242c800e85003148085206400030482c41440189001800c542080c031516841c0c1c0001001071071500464160707400311000c1c6140c21010784030032100 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 469418354 1250 469417104 469417121
    0x409170a020a0807060b0a0812090d080d020f04090b09162105100608011409010611070302041d0c01030e0303180a021003090317070e01030509160e090f01021606 71
    0x9601a400b4a900002c1521004020785481140001101c4014000b8000824080d42008209034001c0d184980078440490070794101010880d6883c101240d2031400c0e00c40c0380142001000c0c001d00101d8035021045070b101c080d01c19551812030402c4008031000400c26030740d0003515074250803010305043c141002e10a4bc0388400031901d050b5071a01010111106c0000c861342140c0100d299503827403030180007090f48212003500400c01c0781501d5860b202c403400041c40c04041031060409101d000034000200f01011f01103c4011600144200140f01070001c119002c0010308140da1414055248040c0441d030280c8110852208038000460071035032401d1812804810700c1169444522a0850b641e0060342c1d540340c0d655070004640e0300426241110719010b400c1540220300f1580841952081040c415803040c07481c00c005600346800b04054542c41882410024000780b00d00d50021403d00118550600c001928051b00d211021642a24022000da0f402c170700800d02e194803144079001c0714501041140e00550724 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 469419604 1250 469418354 469418357
    0x20103020a0314071d010903020a0b1303060501093303021212030915100e0403081806090c010207140901140109081c03060e09100c030e030f0c07050409170a 69
    0xe9a0110207001c0540800407140400040c8520700f0380d9a64041e01c0300e44645d01402824103e66180c2540e00180c0b041006016500b00307068045528550740b21031307551401c01560009810441941c61741000c0015221280708140104014024000341401450b001c50220a10032030040d0403904580c2080746011443d4400c007081e20030701c0d410754041c40b10180203500440300e410041c00c840084030000b45040c6801460390340c0ca40b0b46c0c4c1c0c1c820003101e40b001c1c910075801941860140440d9865016100e81c8103214480000c2e58401c06003085151100055558203040098007260000c45e0303035801e4a11816200c0000300e4100001c036004000b01c110a40c0d090354100d02c141083c01983c0d0312400014a48611801041c0d2808002003480300d0300d503054454840a004030703075040b80c05071138200c2035203541d0390781041d40d03c8110782c3d2161140031140c480d07070003a100d80c65880c00380ea81e12000c015140c0b001d03030002c3c8680f4420780a82c40d40098103150902c100442140c0c00644801900410322015a050308141c10000 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 469420854 1250 469419604 469419611
    0x50a080601201f06050301020306010c06020d18120216120204091109070c150605060702090603011508030c0609160506070302031204060501030506091636050906150607020103020a03 80
    0x10000704080c000c4109643e20200c100ca801004202d2000035a400d50b4480c0c3d009901c100300f48003150f6031010015500641003100581c3c2d4044607040c10008001d03543c2078202c2c030340c0b0304030f099010401000d513009035002d0355900315950905500701e812010420340c070441002000520110f17006003884d4100d400c01c030f40100d0603907602010550110b040e0510031036030036001901845c0200200000065a01c5000365140f4013082483c2c00d04010a0781c038800e411029215500d400700240d42c07541d00750403000191441107034000c10359583c0d4030404c2e540e03081110160a2030250f44009100c000300051100417040c1c82c0e00c60f000303480d0702d00f00c1400207560084070140c1c114002081959003400003d8030740b13400360b44200c900184a41c5503050590400801900d0301c982500021042a502d2099040c001c040c0d55015a030307040a41050010140780c25250825150400040180b1030180c2640381c3c05140b180b0340400a4880c07540d05c08065040d92040100c7d1168001010301060004d03500c01d50103030017426028140003 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 469422104 1250 469420854 469420907
    0x1f0e12010e1203010302130c020303040209060409050106030b0601031d030306060f1213120e0f21060906070e062122050d0e060c06010909110a06020706020d050a080601 74
    0x12800c0c0681d120240608602c0000100110305050341d08402294050304108141c1000342d10083d104c0c840a80040d205503244808115035690307030b621400f00d4a620100800100c1ea40e841c2980c0c4481c1e0884079079012034a040b480c103140d08a1400c0b01d4048940383c0380038510315900c50041058540107000140d010f21814000e04030046000e0754007030b0007007142d0301e404200601c40d442c2c40f10320384190b0b2440c00108065580c1c0c000e200d0f10303240300180c2c40f98011220646c100d03a44206c40306207088261031040c1e0038480d403428002d00800221304140618099038612480c421010140012403107803440b100c2e51340d2209107900084080740c01c0040e0b0032081c6083c0403080c50091b890130300002c10300c0c84015200303504004980d40700702d42c000e83c030012104000c0d5a06801c1c004010300c620b841304414402c0030300c001e03200d8050504002d602800e20190b59402002001348549948000b5034810060240388094070030706028221950003a020350798260030030b6807105080c0e620400116a195101c0505100480f201c0c60718 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 469423354 1250 469422104 469422131
    0x3050a0506120c06250503030a0c03112b020703050909010e040b0411030a0c230109061706040f0603080d060605090d1b0306021b1207050a200a06030207021f0e1201 72
    0x500b05d0140204025500d0303045c00c0c0f00480031181b4400d01401810b1070701044441c0c8041c3c64050310000a40700c0e1001d01032406104004040082a0b143c001150f8400034400c8201a0820007420308250162402d10440e0703207410416481000c1910040e140341e00803c006000a0080340d0110454480582502c4040c4041e0755085603032a407681007110f005007800181000b041e4024003441d0b9205003480e04582462030500007400701086401401004c0952900041d03642e04c940c1c000e0081812100402c0210b15074034100416140c01c5607400d00c00300f505100000551a2241041ea5a52030008100300001e400543d10103c6074009100d400c0c1420020b01d00020100b60700e0310182c00d04e031140325a400c05078070f030210100c3d05083c403200301d0007800081402410049400082d0b080d00244e0f01c000d8041c07055035018110100505d401e032200d54030034070ba240045003459054000d400c1c5944244c1d1568149408481e20080c0c04805c210700c05c0c0002c503156a515602c0c078040411802a452042c00040d401000b86078 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 469424460 1106 469423354 469423417
    0x9070309030915050a18050616150e06011502060f1819030c020406090506220f0f0629040902070c090c03050a0506120c06 54
    0x241241058000c0100b4006000d1074003400043c02c181d003100600700e9020150541c001005d1a03800250002031110b041c0546000501c56800c24160722084580c418202e142a1641d80e000d08446101200e68440c91f120442824082c20b5650306141c41e13452000d56111445045500010800540c03103d0110043e4101d20300384240c8003400982d1808903d0b01d104a00b404001600c05101c2504050b001410b2000c458801d03107052000558804010003161412203a4940020f1014580070107541d0300c00c008c1600740307112000003400c018108140421944104a010713150b540d00d03042031041c03000c00c024004400300c040710b1007001460106241041e0340100d10824038401c0e0040f40c1d030010032602d2107410028080c00300c81040090b02009008015200070381e104440e162401021075400e04042d040041703020042e200030841c4506174030038080d1540c01400641148400c0c0a0017400e880380b00076 = true := by decide +kernel

theorem cover : BRFrame.Cov 469244604 469424460 := by
  have h0 := BRFrame.cov_init 469244604
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469244604 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469244604 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469244604 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469244604 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469244604 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469244604 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469244604 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469244604 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469244604 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469244604 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469244604 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469244604 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469244604 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469244604 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469244604 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469244604 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469244604 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469244604 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469244604 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469244604 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469244604 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469244604 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469244604 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469244604 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469244604 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469244604 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469244604 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469244604 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469244604 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469244604 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469244604 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469244604 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469244604 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469244604 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469244604 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469244604 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469244604 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469244604 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469244604 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469244604 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469244604 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469244604 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469244604 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469244604 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469244604 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469244604 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469244604 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469244604 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469244604 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469244604 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469244604 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469244604 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469244604 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469244604 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469244604 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469244604 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469244604 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469244604 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469244604 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469244604 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469244604 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469244604 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469244604 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469244604 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469244604 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469244604 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469244604 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469244604 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469244604 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469244604 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469244604 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469244604 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469244604 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469244604 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469244604 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469244604 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469244604 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469244604 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469244604 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469244604 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469244604 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469244604 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469244604 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469244604 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469244604 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469244604 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469244604 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469244604 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469244604 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469244604 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469244604 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469244604 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469244604 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469244604 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469244604 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469244604 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469244604 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469244604 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469244604 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469244604 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469244604 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469244604 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469244604 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469244604 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469244604 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469244604 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469244604 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469244604 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469244604 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469244604 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469244604 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469244604 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469244604 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469244604 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469244604 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469244604 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469244604 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469244604 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469244604 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469244604 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469244604 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469244604 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469244604 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469244604 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469244604 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469244604 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469244604 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469244604 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469244604 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469244604 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469244604 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469244604 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469244604 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469244604 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469244604 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469244604 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469244604 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469244604 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469244604 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469244604 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469244604 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469244604 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469244604 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469244604 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 469244604 ≤ n) (h2 : n < 469424460) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
