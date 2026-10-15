-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5476
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T15:59:11.142985+00:00
-- url     : https://prove2.me/submissions/44a7f3ed-7fe0-4ac0-b3c3-3607bbe4f62e

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 984712230 ≤ n < 984892086 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 984713480 1250 984712230 984712283
    0x50a0b0403021f0b1f1101020310030b0f0421021501080604120813080310030221010f09030e0d020d0f050c0108160512360f0109260d060e04 62
    0x1a80004680c0d020541001005e802c0c521501e800d281002d00c0b10010b0003000d099070700c180c03402c06817403c041a040050141e00c0c00c0303141e0007506880c1e200c6440d0174280ca558107103551315410107200c09050440340c0c01142c000c00030b800e10440f1a06a4070f8803503a42c1e14400d62500c0c0111402d84001d0030300d11030b5500e424442c91103035100f42180300719071000030459200c0703035107070340004081143c182c21548010025a5407629031486e1595144d40c07a80304a0b10601c006804d44000700315000709941424402c100090b00280050b80030503098504030200c4e106800040c80060505402901450940000005004000c52002c00c00a030a8035090020b480704405120000007500c100743c0002e20600604407070000f01c014080d001a0696605c0c05003101d00740d51a5004a030111f12010821005c62001216010920081c0f0010100000801480b540c80d03d540b15aa80c904034184251200200480c04000ea50020384083c06042c190400c581303911407900c012503e8045e030b400e0743c070f002c00f05240102a45641090 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 984714730 1250 984713480 984713501
    0x40c02030d0903140714100506010e130612050f2e0509010b061c0501050402040f1a1620041a01031107060903020105180604050d0c050a0b0403021f 65
    0x1146050011140704004100385403003141085141640c464000c4d0701c0c500946030140c000d800f414140c000300e000a5203440b0030f01c2c2c0c2c030560706801c14003040b18030303a04048594510001514001c8090f2030008104000301441c2e00302241c459070f030403c0c0c58140003000802890110610048800995041040305403142d03020b50002100341d0701c0c0c0c0b46030020b1652a0005900410343c00700102e804003800300000c405400014031208a14003030320b80d07070b905418103009e41030040806032001c51030103040c411890003e800d14001c210300e244c3d03406030310350034100d40408031500340480040990740c41c0c0192030318030740c0954144402380c400030024109401305e140c20f124403d50716048034907089200026800542c09000519a02e00c40940c0a20984000ca04140241504c06100342d0001546143c4aa07001018022044120781139612070800c01c000914001082d5020a100b400c4c504a0400716141c0103140c0281c030b9000400d0300340c004090000701030300084c40600c031342420031513031641c04108140d440860311507007032 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 984715980 1250 984714730 984714733
    0x303270203030f0706180506091209060d0c0c060e0a02090a05070f030c090321020105101d06060c0d031d010b03071202040908040b19080108030d1d0709050a0b040c02 73
    0x62001c804070f4000100311481c0304050202d1011541309842007801500d01d0261041d0b0865020403180410500445881d40c1c0081d49190a100725203001c2211400342d40f001520003940c030704cbc18005c0c560049100c240303404e620560901054943d4240c103030319018415000c81c0280425004078000e041d0070300030b0b50300c03a0f8103e030340b030302ea4035001c0c03000c100c000e0071030080c401c0300f032220460001c40410f0360708070441c1c4203600c04090815034484583c0001d0850f0001005c244100c280355805110384034070038555800c001440044110552520b0300019010703c80c0450480d05031085865040602d0f0305500715003484140a000345003010001c2d805142a0744072274144981c107800040e01070020010440090004600242000440c0c1c2d002c0c1c4d68480095201e03070000395210b040403402980c011481183d0f800031380018500251154509612690b403801a00b85550301c1a4991007124092861000b41d007080003064030895090300c0e82c51200ba402080c00b5154206c09504150701c0601c00c1c10140143d00c2500d200e6070 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 984717230 1250 984715980 984715987
    0xb0402090913060b100c0209060a080d050a0306091d0c01031b110c1809190b240618090108210a121406100807142104030327020303 58
    0x100202c0c1100d110360040312010750f1107401d135280ba244c44c1c541c0300800307046440d1005500e82c2030040100d1024010b1400d881350b00488814005410081903e9007040890300708161a05003159044d009441550072404205140041e000c2e40c00707401a800c1c481144500041c4c550000650004600340c03140c41d290000ca84414403140305003644100441c0e60840c1c02c0030709807031000181e80e0004404000201040c103040000ca81488420641444691844812105800340c085503e0307031548502c804c014404d0300041d10340b082040c08a46081203044101100900c407a0343c500000ea00610280040c0560364080c181000c000708004400142498051250346110190502c0e000c100d01400e5000c00d407004100000c0e01ea04400300405401101000c107000e056a4501d490324105201104070708040c0d410420401c1c4003030000160700469070000d10f02c0240101c0399038003900c034000448441104c6040000005480800003410361550181c010810f030024a00285040609a140910b403003460280d407540080 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 984718480 1250 984717230 984717241
    0x11503022d270a27020d080c0c18060109060c030e21010c140d090218010909030f0206070c1e0c090204080f06011508100b1801091203080402040c050c0607030b040b04020909 76
    0x501340c0d008600c02444804c5191003550f891401d9040179604203295445014104a9032900780320359100c190807121608401c2c903140c00000c141071424402d6605010200c1006001d02d0301c6424040740e189006414100d13640c40044000900b15454000d0b103606520340042c1c1044d03035204124034015612501c0c0a14104044410288002c0c035107808226440401201c4140604100c3c440c00e90082c69400c8001442621509010b0001003411234010219009802044103982d080284942007540040840c0403204518844030104048550023404000d112180013508a0b0b0381c3e0010410364142c007080d00c1c103a045a0700010360343c030b800307002d40800e03880c1100315907050354460002c00d41d201c121244503659890740c896128280342c0c4030b00c0d01c54840400344588000d8a58020b00c1c00402807001d040b040c00c00d940c50352030003811144007401c020712aa03102c51103039131114810015200c1c0210800305644c1d40d828031460207801008691406c600540c10f2640401441c03502c0e00c20388810f40c5024241c01c2e440daa81 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 984719730 1250 984718480 984718541
    0xb060a0801300b0919150f182d080d0b04200a080f0907060509040b031c031a09010603150b0d02070203011503022d270a 53
    0x1082160641c4061040201e0344010090082c0d82540d4016000c04815043c800380150030480c09044940e41c001c2180d401c0b100040300e402d110714058411103400501450281d5a1002808100341220703200002c5204034814044100003c054605000401e404002420b000642c0301040e610b0010b0404c034021b00442c903543c03d85402c4030404c40001070000407040140300036000d81d06220320000800c982d0100e0014002500120a07d8002c403466001c01c0b00c038903002c40b0059485420b40107130400c0001c0840c00c2a140d81f590303006a5241080141650590380c000e855035008003100f030a1000009040c01d0500300d40121406503d44001e0001e8004000c0768288071083d4050000340f90409003d050846000541c001300301c000d4078948400c000c026a890b0341a004260950758020340203180500e10280c208016950b04c00a04298805080c2030710301390000e041d02d49241c2684000440c0c0040807484905001141503003032100c001004401b60702c9070f8407041c1e0034004640055802d03014080c1407803c4103c4031800d = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 984720980 1250 984719730 984719759
    0x4050f0106080c1201060e42040b04030b0f10060c080306011115060a0f050a0e180106080619090308010b031803280c0305090d060b04050414010b060a0801 68
    0x4a01004904d490503800c0320303080d0300d40300368000000104c416200080c80d1614840e400c419940d0340c0b402c148407401c1043c0d8481c148820034103202c1449100d07100e12140441c8482520003c280e1a84610b8481d59641495440c90000301c0f418800c0d240072100003608a07071428001020f036042039481c000c107a030f080d5485410b1548054001e5051082070314200e514a08204803c1d4010419100c1654580c00e240050010010b07103504094968a0015401d00c00e9861b40d0148200b11181035607800b13650389941c3d070940301e01d8480316244165942005800b00e0b800200081441c0110200507000703040340c5144d102041220345d0440000c0004c0c44c03003801044901d1900c0701541c1c022108c080140010001d103195186198421026842200100000b00d0000e80b08031214025800e080e0402000801d1f070b59a00030068416640110320485510707080c07a05009041d444109040005001001141032500b020000008410300381e140d41d40c00d0608100700c50820006403080120180c43d510444d90810b0710041d81200c = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 984722230 1250 984720980 984720991
    0xc0405040312020304060b0109060f081b0715050709140603040b04020307080a030915030b010507081c020304030509030601050a050d020d06141603060504020306101d060c0309040b04050f010608 85
    0x140c2403101d204903550b1440214000c500c950400114802414009004415035070310210500c00403110212555800034042580140d40800c00350310b0314042c035440703003c034024008068109068000c3c1022554010b030700c010302031003540d240c409015035140c040000421441c1c0c45250400410300103e000644007100d0507820a20003000d03a4042501c9210303480c585000c3d035106038001005550304100c440203004109941c2c040d5480c044c403107200d0000000e03002d41306945004241c4a4000707000c1c80b01e08258040d00e0300060032684150b540e030615040040003900b11a01d124440d010302d100018052404003101012101c02a180c0c2240048980800035003242c8070b41c0580d0402c0d12008000c40c0914591002d610134400c3d00340340400000c52240040403201e09030009409584104103012940e43c81c1c6454414078959490308a002005c080c52104680400044032a0890f00100c0c0e9040808004030290560000540c0c0c20040d011100c01004191a029500711210ba89104010700010380314501196210 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 984723480 1250 984722230 984722237
    0x1509150306170a02010e0306011d0415060f061101060501090b0f040902032d04020303030a020f160809040e0102070f020f031e060a180327030501020712021e0c04050403 74
    0x2596514405401041c090b01118100c3d0880c0301004110f41c0c02ca2003000c80140c0980040c18250304000104818516a592910301045050300080c00c1120386500c0d0503c01000090600c846a45c45040501d0741889001d0301e4003003080480c001000383d905114003001c5410580d102c81c00c66203481000103169201c49544038000c4001c10010640c0c0c0c2a43c00210301408504c5104002404080c144942d920111132004591400c241d00b48030160341c0000542c5d030002200341c0010f9440f9005400000188030300d4442040215210a0700d005200d40b4001400f5401c0041c2c1e030501c80d421402480c0c501300c1c80388420091078605e02d1500c90016042084c41c01ca1280e80140498486441480c0180082d07003940d60000c000d94041c0040103400e0a803400f41c03041c000c00c1e05807041d000c03c0d100e030740181800300301036411603d81c00c08c0c80c046011031042038002e0000b150450000c643e14445c1b400c095865155044841d03002d03114441074004883e0041c4805d582600520018101c0804807000704006041c2c080c100740c041 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 984724730 1250 984723480 984723491
    0xd0816080a150b121e0106080f070504050306131b0b04030602090315010306291f1b080343030609050a0207051203190b0a1203170115091503 62
    0x2a000300c1000b4078a07034020021442039894003417482e440b40c004103242d802214043c580100302c990303013040e60540c008104010f06a0260f41b400800c698600441d48640da00d403140000b4004016138102400008500030041c040400c941d109110f040b03880188140309526800b00f1040012400340e9024100c60503004042d100c9192024020a800c2c04c001e81042c1d424030303514440c40c80d100b100c0d48070289803410707248510900951110300080400e0b2a0a89103a039410748440240707000c40c42001c0d0003080794181044000956a24104125103800403501544040c004180303007420b0540d04001e541000800d42d02c0b40705850842102d501c0954201c40e800e20a044d1640e1001c92400524003459102c2e402d05080142c46081c507003030051900110100d44581d00b0b80c10402e1000c1c2d641d41c0303c2c904c40c45465240d00410064031980114049030000e51203411440c00503a02c080405900000c0141d0001e56541020300990305c0c1d850102d000c5070f00c1c491003008980155030800c1580c20105103200004410300b4001503 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 984725980 1250 984724730 984724739
    0x5010e0609060702010c170712060302090c0c06090111030c0c280308070c0c120809040f1b0f090608070e0a09050105010201140603070509090a060e0d0816080a15 71
    0x15042007928a076410790010020408090350921034401d03412114903082c010400901503490b0503500103443d03141003010105098221141c2500010004c641c040d0404a06107802040542207070400c8007801464084c400200340d010005008203a9404041c003412440c544a181c06c21580d41e0000e4220f42260160844c140e20500d29050a40c44454a400d01c1104075030052038000e2602100a10203418012900c40060200301c1407102d4030306803034012104040914250805000b40d0240c26603d69200e0306117003200c1180d090036046003211112251001c0d6655200b103109841c0c0710b0390281036000040720704104004042c8542001c0b40c2001140c103000f20400c80f510b0100d0341030017150300030564483c0c440300104001e5a09100b601e2421820b031641c132490303080910000c2d072104018803c85110314007a202041031035000703014200c60b1940c070110070024002040d5a040d1103124280c400d901080d18803000031450403951046052854082e9200e5000380d44100c1068020444040040150740381c680c001714 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 984727230 1250 984725980 984725983
    0x10506070516030c171c1b0213090215070b150d020319030e040209011b030912050c090105090405061620010518010b010c150212131718010c05010e 65
    0x1c05140207520b000d4005017040144820b11000030b40d4512140d01c10311a2014004031340d55a02141506460000713190303e10300d12000025920014007a40c001c0c0003614801e84000564002c5803198401d85410b144e811102035030300414054607801070101d06080c0e00080180a46003000f030524000104502e0540255801083c40d25000d00010100b003034180f0700351800d05800c42210442c01900716419464000000002411552203500420101640c0c0340c2100403d4060366440c0d01409039640d030030341480c00ba81030580c1da03410440500d5006895030780001c10076081c42817007a0f100f590468010189520b52820841c1200159030700344017080240d4400740049081c960002c030b8901d031910008601401d04098061090b6844001503480d07038500000d102c4581d80000c4001805a0840c543e06121800c000091380030f40304075040403000000400c10000002c041c1c0403400421806611011102140588100d5651041c0079480b40550301942544200b9072040440011051103000041118072940e40076a = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 984728480 1250 984727230 984727273
    0xc05060711030d060e040209060a0501090e180a0f0b091603022707020f0c0613170a0614011e08030f090d0501090605010810150501030506011b0b060a0e0402090105060705 75
    0x1080345c0005000e10065180202c10950016422a42e4000301c034078000c0040c1c94604c0501c11484c01c0319001001649200c0c0c2070000e101107080c01410740344a11442d01e0001c10203406140200c540b207142002042d6103035000a40170420301401203480c1c03100c6040d41c0030086110110701c07410500d02003039280c2507802c1c0200c0c1441805032840e900141a407002041c1c41d02d013172441d4108000c2c00b400062002128403100303103d07440c0459032200d8418229800000d01c140c1000e080100203000c0c0e600707104000d02001a0348a03024100c5281025030241000d2140c1c0707842507841e0344e100c1e0307090560081c00200c01c1104000010011100024151840c4031455030310b850030743e06107100c140c07a01559940100f00c40c3c40c05111350244440300403401c00a00903080301400700c002603401458101591a0000344103a40a58a0440c0c411082810a46444028039213040d1503601298031500880b040440010422201500c1600442e4002c0c00907017581c2c02c08042c130040d40c200e50340c00d032010301c6a440d5a40c0c0084004001c0e = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 984729730 1250 984728480 984728489
    0x52505011d101b1107170703060606020303100303030b03011508010c08071b0f0f08070b0613090b161701060f0806011b0201080403090f140a060c05060711030d06 71
    0x40060707000000c8666090128041d22480c00b070b03042c40d255540e0070210680c1e8207240c0c1c40318140344900c0d42e80e840082e4a8001550401000b03c03c0d110007103021031800191103c00c803440381c2000d2002c0e036202d500403a10f0707001c00c0c0c0c0c103d011401c1101c4180b0019001ea0400d43c0e10000140002a40b818078005102e003c104603885060107942d94101e000003154440c00c0c496200001b030030042203161000b4a407699403030241034050324a544010b0345204010017000d6400c4619008982107444070f401e410000003004082d030340786200d10401c00c0303152907540080c042c030940950001c0c100b000311350700c001e403000b140c8142540b00010403107407220a464801d140700550340a000103554850074042010b101500102028100c1414080c0c2d628a42c1002c485014220f03c08c2607081c603240200c0e84803131406039503949254010202141054a022615207007203403018004000413650f040d8126550002a20150521a00680036030020400030b1a100c0c0518002040c4400c1e9400310b910b400031400400b400ca603800e400 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 984730980 1250 984729730 984729761
    0x9021f020c19031a01050a12050c040c030f0501170d050d0b0301110706060e040b2839020c090403020c0d08041e061d01170411190605250501 62
    0x2030900031310000f4118078004981c045480c1c03407154140000540b13071a8640c403c2da480303024407411600400409101c142c0031004040c01c14050786200341c0f0040c0c06440d000180440c0c80e03140c6400020259050034500101c425150003603c004440e9083c100c0d003aa003d10400007803e5104c0300c0b410742c2510309100354a4a03c031080050768039140070340b900b541580c40c00e034041c1c200c1a00c0c2034207110101d01c82400403900400305880c442440c0350002d908134010304045001d4000d062030004843c0c1101c0c0c01c9603010040031203240001d08440b0b071803450001c0d40540c507050a001607006919548442c18800ca2260b001402401210301d1203014400143d120100381c101112500c0020801700441c2003500307038115800400c12080b255242c1032100c014451212100c011400c04100c0011340002e90181b60700300c0d542c0803103119480321440c01f420f00c40450b05807400d0843c01450180108582c2d40c52984181c4190340d017a0780d07241e01c0c1c400001d5030240f4080000e2810300a4404030320034100020310920891100100400 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 984732230 1250 984730980 984731029
    0x1d12011d07170303010311040c030902041104090b09100314190c38160b0c0a0f0f0c0219170d0e040b09011a070507060302190309021f020c 61
    0x141c0002c1882e290540c074400c107070300a00040c0300060903c7c5200910850940d0000b502140050048020b440b004034080e400921340407403484654002c00c010800d85048dc40c0520000c515041403040900040b43d0303e0000e28a007107030500028140046510080200c481140c0c0401d0390812661a04412890200c0b103451503c541041202e0301582e01d03c5038031909182c000008904420048440132041c0d4071001007400000701030401e50303d150500c00c4900d4100c2d403e03c0c640d290500101265901420100012800c05010840e4081c410000803d042c980d41d907404030700318540d03405d1000c3d5505804484100c901144800b21703150035250354591b804e2204030000c110703403559403d0191106801410179809282010440c002c0b030389402c0681411a400780300c5050361880b140004003103a000b102e40040090107010000149280d140c0c0181c904005c2e4010001e81d250441c07101602142c0348000021f41200101c00940c00e40999071281c641800d80c03078019940b292540000082d400c8480f9a0445045030b10700 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 984733480 1250 984732230 984732239
    0x170d02091c17040339090f0506040b03070e250206180616050d02090306130b06030c010c060e07150f0201050c0307081b040513050411011d12011d07 65
    0x2c0e1124184204070704105071400341035450304100078106070301140040e100040c0c4010740654030f401415070350401c0310211102c140c40d585500301074486207090280550905012036014507040c42140404100200205841494a08500f000710002000c482c1c0e600c84c039200300c0181200691024180035066400307000c0e01e10303002c00940300d203c0303200c800310358180d21503400c000000600d440240e4411600d41099510742a0b1005640042d00c900315420350103025500510026000500c45e40303440318454a40c1000d0f0395580418140d58284080906002074940784080f004034405910a41e600b03045e4009580b81c1507180c01e490100700b0700100f200d070001402c0c204c404107065420b206094204c0e40c7c0c10f030007916600300110f0003070200304007519030f0074681c07001e41288003070544141c02c8400a104c051300311880101115a50710040808850544400c90075007403107052580300f0f99005104d2045800446d110401000500c00c10062585c6050620b645c0c0f0344a90305402030340d5506955035500714000784541400c0 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 984734730 1250 984733480 984733493
    0xe010b04030533090304035c150c070806070309030206040b04030c020307030b01090f200307180b07020f04020c07140a05040509010504060c0f140a12020307020d0f0903170d02091c 79
    0xf1007030f2010a0f18803516000480741d03030095031000501003c10407060030088c21000420545414040d45001c00740045c440121140105d480030482e620801600c20325a9103a4040d410f5030f501110040041e040f04000600040e00e0001c0d1941103400303407a098980c180c0c07a0b400319141082640054442d60200d00040080c6c15181c01341c1c03081004560703410300c02d80c0d60039020801141080d1100a00c4988048002a0318030b1107a014802c0004481620b42100c5668254060b4258402c2806038007030800c0b46107000f068185802101d9200c00d002004100c4289843d410140c41540050055404000e11100290541c0c65000d0140503924020002540341403515110084443c0700b00b15400380100b01401001c559003195018950455282d6003996841e9200001c43e040c1d10411104050144040140901e980d40019000e44003101342c0c1340d02c143d14800050a8445940c184070040c4245120545035042c03041800152019044604c809403d000350b00c00050f481260b690141d40015021359915030a2005 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 984735980 1250 984734730 984734813
    0xa09180509070b0418020703020313030b15100806040504020301110708180405040209040b040201021903020d12062111040c050c12120f0405070e010b0403053309030403 74
    0xc0c00c561440c10345080c18001c5034a0810008090569000c03407c1400e2500910403130f02c40e2580600c01a641903140c0c0f0340803031100c00c2591003491003200507496415508008404d0f400600b02c6441d20440355031614200320181c280100101c0c2c155403118000b490040b5564050600c15215030015034507484a402a140e03c8441064201d2156052809200c09611202e0200e9041034101d10000704642e15400180e06c6c1c850110007031903100110421540c141a4041100014490603540722040240c5407089034003524854000d0100c00004200790340c1d910080281e420581610601e881d46078080d40c1c400085c1100c0009480f01e0124000103400900710b0020310a04015040c050903040c01c01181007003035901c0301c5000300748041c8990302c6c0d400b05090100c100081001000a94aa01d02d903603168007110610360001d1008540d140702e00d06c00303402c04869403400100320f10071a05501d101c01c440007102d011840c8003d025046240402c21021006c41e024954401d113004810100070400d150b4031074441940d10 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 984737230 1250 984735980 984735989
    0xc0c050f030a031a0f06180901030c0306140105101b06020d020301031a0106050a030e030928090603050a022701060914190902090a080f060a0b03060712020a0918050907 74
    0x4407913030036110003641d4100e10100307100b03c1500c0440d216403001c1d01c489001c40c0d04072942c0da0f1008034000000100f01e0b0110700700054030322940090100008140841d8180b8600b8091540d0090240c1d80503000580700704600d41c1c01291a0045400504194035070030101c1e4021010984016000001401880484031005906405908401400390b1418000030418058444428100354071042421107440003041503401d5204000d141014261362845040e10403400d588000246051201001039490781c41d21441c81120340000140c6000582c540c200b01038001038141c10750084810300038200c0342c1140c800c5c0060203030200f074a4400500341400c201c0c032012001e4000043c45006482040034480058680c502e040750000d540c050f032240c420200081c400c5409400c03108580c440c010800484400c001625030064141400070845407000301c0c10b1603200d41e003c85880c4003196144041d5500b034401036001740394250321440c110008503110910045144070f0f00307100c820038545a005021807034030180b055a0091 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 984738480 1250 984737230 984737261
    0x1c140c0303070804091e05070c0c2c04020301290307090605030c040c023d02211b042403050105150f0f0301031202011107080306040c0c050f030a03 65
    0x2c0096540b410240b156001e1408120746841c0034461700014001c0742000090b110b40103100d030780b801c6140181740400048090300c5072900250000f504845544a50820304202800eaa43c5055000c2040542c000d01070012a0199600c00510240c840c040414403410f01c40fa055081c1d44000410070189080c1c0107421800099103402000c02c4503503000038428200b080d0a4402150310490100280e0411144070070091602c2010204c070440b000f4070200c0100c90281504400760801c80c0300342003000b24011507504990580410911400b004911030f07006078440703030115425a02054081030015150001c0d44082384ca203030b80c800c00c1c58140380d0245d00541d0f051820728041015601d0f00c000113030f01607101c21030703e183c00038002020061504032004540e52200b400840315a80d5940e468010392030360982c4180c00c011f52806030f43c0c140b807465040446005c80d400c034605038290f440f00010000280104031605085c810140700c0480024001c0c8500c85000100c10060754881140040140968807407100400c0750 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 984739730 1250 984738480 984738487
    0x3200c100c021912020a0503030a060614180603090127050606030a050c1302090619090b070b01050f1c0309060f020f0d0516050f0c010e090f0705091c140c0303 70
    0x3c00500005034240c054014608042c4607001c500d050742064401c1c940904039010000c1001710004041d0060b404988240d039601c40e800c1c811614280190040e0000c0c4044510590501215440c21030701450b0001b09400000039080c031100c2c110400d0040000c0c1c03500c8020544000c8a092040500c00c85601043c1a405030200c000c40740e40e020345540038500b01501c034012100c41c1000220031503041e1101c10304064000b40c1d4035410044c0c0d10090749074008004001400c000c0c00422074800326801d8900150344500b901ca496400c110400031902070401c4041d40081c0651580b01917802201d000c01f000500907182d00c180380d41420030041070284140c109009540c0021002401c001e4001790b8102c02171003070320705551601c41c4962003d00d45c9160b408050058864248540b407160401709141d80031307802c01d07203c034074030000da20050145d142c000702c54840c0c1e600c0700e035800110380b103010302c0c010b18414100500303425030300021a0b440741c00c03039010344804e8541c3c42500c5010342104c50300308458211103004400035810b = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 984740980 1250 984739730 984739753
    0xb03090c180907050108071206080c121b0d020d15091103010e12090f130203011509080c040b01090b1813021201150905093d0603200c100c02 62
    0xb90340c0700c24131505041003001e4000a1000384203d18035030610100b2001400100da990714940c0e07a41c40d0300360f415071081480840069904c8000540b000e8271644141c111140c1d00f82400800c89203104010341680c20410a040e0640010802121034902c2100140d0000c0c04500508000e000c80e410509281d01981c5002c842c84500000003440340c020044840c0081d5403010f040004c1100346c02004d41c0c1640003140902400e040d2400c98016506a0b146041d200640c548124021580c04407a80324250039030b003100e807030760700e0908051308446071013074041c1000e42c0d55035038540300845503600055102036500075034150442c043c60300448049454414000035803c0ca4180491040e001e10180b2a01b107960f0024032109012038010034005008140c020045001480e0650384080715400042400c1c804880400640e40340d40d60010441d00e640d01d1561880d48404d040c88020f40003840c05940c40040841180b547c1550400610003d252004e1410081c22400b4007241a440c1541c11400e217140564121468603074 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 984742230 1250 984740980 984740983
    0x4031206060512041b27060521070f06020f070e0408030c030403021c032705061807091b180b181f03050615070521040b03090c1809 58
    0x10894066440c0c48140c44c0c5561824803442050380045210703400d4803510024104108071803c078012504c180b0000d480700024002441120343c180201944110040f4948007102c0c080c1401c070040794600c0c000c9450b440d0b1540d0100384100c0c0680d20541c01640042100f00e410082805010006c18113101000042c0c142039560742c0150200400c40c455151005c00007030f0034503200700000d0f5a4420301c988961510001340d41e00a020385580c41e6038110b0200740d41800e440941d02401600d65007134000e0301030050b540701c8804003051607071000da90645500c940c200c003040101e0f141c8100040c890490300010710b400302842000d014240510342e807942061031980f04000103983d0f0b070111819075180300384091011540c13800050004150039801014824240c05040013141c140c2e00a90040204a44a0b9041c1c100100410260321400c50000c1c503a401c00d40c28000c229160610704107000103075a14450400e600c0d81402d00640e00119107020290b030003010550358505001d03c1403a1a5584c920214003149482d01c4c0c0c09 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 984743480 1250 984742230 984742237
    0xb04090c091409100b010c1b1505030615030601350f07020d031e1a090c072126100b07020618011110060801050f040c0b0702012105040312060605 64
    0x503080b04d61541c0e08160143c0c41480c200c1134640d405003140448003c50110694610701c28043e005003c0c1e00081003051550188050fa80b042c18001c040000c1741c0b0019044000740e410290405050110842802200e406c541580c45415162141c140102441001002203c02805001d00c000d034540d0030306001d8260b901051100e8480c03818140401e042c590b801032541403003c3c000c3d8201c55117140c4070041030364142e00881d601c070308801191024929251005400303030b1840385100041000e50900c0154a034030002d042152207900050074400302d10000c00c001e401d0407042c00c405c60a102c450080c10001180c50001c000005480c20100d1181000901d90108200c3c3c414900d40460102442c001010160301c294900142c4040a17000d0b5400c200880e03590f10042c02c07440c002c1e00c1c080d50801000980300c10152442c0b40c8a650030a2105d08001c0c60a28a8040c9501c99042a0f04200001040741e4402200301c080c42c40b1300c1d0341179400007868689401e008044021328245901e465040807410007800741d00c00150b = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 984744730 1250 984743480 984743503
    0x1060f1205041b090c0e0604290708160c0b030712050a0617341203030b0a060801140916031814030a121b030e010b04090c091409 57
    0x30140c8071800c00f03003900ba80c208000080084110310104d10300146400c88407207000d8035118580d000b0312030000c00c8242e000350701071015000c0310074a08100141940c0309512210300f05525091416940c0d450b00c6c45550b10520404d2210b24a651541041083c1d0f040b00700001c01c1c96002c05415420160401081d124030043d072581d400380c8520105141c43e1869208a008021006079150524185400315803102808205401c9243c6d200102030780940c0c0c0700000300c0313503010320ba0b011036941801c09611044440d8a041c0c00e070300700341d550f0340082e90300d4603019004000380c81140c584501a42c0351010480c001c2c0342400d501c900800402c424410024081c0541621003d228100843c000c1c84520b40400b41d10740d0004064106901c0c4881854003071000300081119400b127542d0038a140c0315503010a0150307201c1c0101c2c0f1101842030440703105c52900c203030711400c91700e0380d00400031810418401c0004d098031544101541c600018410400c500c440c64803e03032000003d00302001c0d0311032819031400e54540b400c80e102d = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 984745980 1250 984744730 984744767
    0x3050d0911031507030b0a0506161a04050c120c01080609090f010501091d0a11100c051006180b010e0d051f0213090b0d150b0303160b01060f 62
    0x1501010021100701005200e54064100d03000340036281c0c107191121100303548810220b032500c20080ea482c10b001d000704040e184003408452900080003202002c1102022050322109a1603821440f001c811644450080303000d02d0081c80c400d184002004010000e1480c219200c0e8403e0103000d00036608501042d80c0102d040f603002c4841d40e241c920b514208880c0702c0d0420750552074100003180c207141d280d0041c1c0c1e00c180440400c8840102c81072655035550200070000d002d140b0058100e003441c1c58804500c500070300d05171402032a01e64003544c4851501031000542e00d42e0607291842030005441100c06045503103003c207010712101a5850010307211000141005010b00625050f0310240401040301440200340c405080c0d14056400000d240203400184c0076645006d40c5480c0099516a64096110401e1004190720082c000315507410741c0c0700700468240c022003a218910700314959818405005624186079040310070900f10725000709002c0f0305803c043c003805010040c50b019141e1140a07000c074000d1051 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 984747230 1250 984745980 984745991
    0xf0609030210020a02010f0e0309010210020a02011104060c1515090b1c0f0b01080303010b0a0e0a0e01150306210f06150311090f06150a110307060b130903050d 70
    0x508900b0a1414940c03840501d000107818186580e0552041506000751030041043e1180d1815013510381c8645a01e490050344824a01c03110039406500070607004100e4000090002484c941a030f04540041d404400402c0c00b134007062040c03064244012851580b003500c1004001400303040f0711159400e501522821942d1101915080e03100c0c5d51002c072103803854107603d42b0054510f14010b482c13288080000c0791252102000094000400000d6905861415240c107082c42b108400031220b04001e80116580903007180000640313200b03c45081400fa001403c04a8086c480e6244081d0035070381c2c254003401c2400c01c0501c0b11f9400c07400521000c020180d02c06002c2e4048881e40c2410009080e2010340c0701c3c1815a041400410058502100303200e03854181c0c1c0d50440c030f64074044c1164010f0000c444450f00140741c02101e08007a460403000703100401c0e15081031800d20020200701d900e581c12501e41190340b01d589000c409510302c2c1141d2030601044621a00380145d0440d5940103010703000e4503041680740703074070781 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 984748480 1250 984747230 984747233
    0x905070605090406120803041e200f09362805060f0a05130f020909010207080309070f0e0c070809040905150f07030b01050405091e0403020c090f01030f0609 69
    0x2c4e00072a0042c1940003a851100301c450400c1310321640305407021116620100c0711083c82c1041480040300f0144c2080d106100c0ca034040d054000c2116510100c00e0303120740015001c0c0010303528900b489015040c10001039401011442000a0244130204442c034118100c845200540d000000d00300d0001d409030786146904010108104150100420010f04070700580c03003040250020b21010520a03c200c600900c03064440400e1001c0640b4a0600903045201101d40c0f8000340c100040d9440e003043e8841d00051800509480343c003070030f0300140c030075100940001504112030141850550060600c81c0c2ca90420b5041c82c00c0800b0051261a4006050081c080380644507955540d100e000480d40040640b0760003a8244910a040c6030200d031314141c001444004950014400d10503142552010784445143c241400d00b04261854010210344003000d07651544c1070104c003510000c501035842500280200d104180030080c11403001041c000c04001d03400010004a00100768008940e0303044000090200ba46 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 984749730 1250 984748480 984748489
    0x5060903040b0d0c0207081b030705042c0c210d090602060a090218010e061e03070303050f0403050d1e031802040b041418010506181815010324090507060509 69
    0x76500a88a034050a603400e4900a181280004235030011415140000c2d22001080125020300401c0750150410300d00e221009a1349160012560451000700c903030f04004140000c03030711204038100120f03d44011413105c60260040240c0300120995042a4842da804c1c03d00c02590760713200400300c00310507848000d1201991104180c450358100e92644a07591503865000504083d4400d561440c060303c0c08060a0350111a000d10815880100038060030750289181c40c00c03103154203e8190081380d6041080008002103040050b4052081c05440b0050030041d001920000000d180c0c40034400d050400c9111070f8070031041005100015412940010718000360300105005001c5115504d5595031040c00340004200c0c0729203000340d04a0868003c0c400390b43c4510501c40b44015a4440740c124050040104800c04003000640800e401560700300c80c06190034440001200c0c0c404c0c1d0080d0b0b82c40c1c1c1040da202e100240c66901002c0b44816010b000c5c899410150b0310150380e07061030301c41c83c0104000400c21102da0750300d = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 984750980 1250 984749730 984749743
    0x303150b2a1507090e2404091203090305133f1416090e010c02011a240706020d0c1b02010f030608030403050d020d02072301050d090f05060903040b0d0c02 68
    0xc00714400d401c03920381000d9080a900030406189010600f9006d60001480e103802003041da541c1c0310320100c607a000758400c16400b138220003504806000e81030110807007a0b6055514000100503860b4520a12010038444a080d0602e16801303006500c02410402d90400e0000d80a0517a03581c0103038840301c0b200c0a400d2a0341440000414181d01c00898080090036a480c3d07005800000e00f42c41c000c00413880202da050b400c03220301e810301ea00d01e41c004445c041260716100f03508881d17080d0714804018400b04140081c0a0704c0c2e002c1c800803503003240d020551174000f40240c42030701224400ca052080000b081c0c1066540c440240810003810450980340880d1104c1c031a0b000b00008000002c00c40b611103840307150082d202e10403441c40d00c0061103200240b5441c07510000e00d4904480a13152030200c14600c0c1030011003400a84030401d03046c001c0c200508418240284500c1030001d004500301c410070116842c295003440d02c09081c004c85035009020600c03844850340b049854490b00c000380024800034106e0140d00b00755 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 984752230 1250 984750980 984750989
    0x60605041a03150d0b0106180303090e060f0604150305160804060c0306120c03210504182d0c1e08060d05030304080301140306041e0303150b2a150709 66
    0x810142c4c1110420810303001c2c4c94141c9156458075040341c034401511b02091041031101800040900400704000a000c451032500207001400e01a000100381c00800c000b0350140e8010440413a0100e5499a4079a0603c03520382c108070724014002c01d03960070780d0001703200c4030000e040500225a00c5409500032800782d40658000c00003214031a440100505014043d9096440203640c1048ce003045a040c8080c0c1007060a06014291940380c10242080501080404854801018503582d08903801c5024003402000c03034003d21070076500045a00410301c000070745900b00e03003e0b814084288201840103441c105090b48504e282d1038204c1c000e6a80c800091001c02d03140c0c2c4042d0007404000140402d00c14244025030503941038a044030391601d44402855034445003114082c040752010720700d20f20980308460320380a510b4080d140108a0000795400c0c043e061603e940942074180c0001951701e0000249801c00e01800301001c0b4600214034001810b54540c440340845400028038500001c2c4e07038070300440c40d80c1c1c00b80 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 984753480 1250 984752230 984752239
    0x60c061005032e2d0e060105090112082205040e06100b0c07050904050a0b07020a0203060a110d0c02070519050607060c050f0a090501090e100e0703020c0a060906060605041a0315 78
    0xd5400060302c45900c86001e00c0a04c3e82c0d818480c40544000300000c0150403100054a003000581c6056154504908118012144032a04101035221301030008008c00e19a200c550b000602285002e040000726844980c96241680001d4200000c44806a101e001220381c5010081e94500f45001140d0600300740d03401442c0d02102c10002e02007400704c00036440841c82e20400e220b10a41d250154180c2c1c2d0360040410095240d444900001c03080352080e08100c048520008070941008071401840081d02c1c01c6125840060340000da04209616060000c00c0d1204d80d803032400d01e002420080440c1c00340c4a401c0c13001e0300e1f00b922185000c416a10076021116a89911000c80c1e86401082000400e40a15031017060b002035042c0602080c8604d0311103115014500c14a05c0341007061500c01800c00d105001010b000a2550034030490300046000d00c282c02c4464032808000030044403c0c03400401b02e80498100d4010050148010300180b9078400003400070b4040c0c1105251607035103100c8840d040c41350010015410 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 984754730 1250 984753480 984753521
    0x80901050f180f300c0303010302010c030e0907080708150609040b06040e040303060f21030c0309270c020c0a0905040602090d08031506030c07030815060c061005032e 73
    0x194841a41385561203c0ca200c07081501c0600d4100000c0340900c610a40c529002080108010741c02007051100b160300c00c2c00c0020100c178603040020565441220008041a0b0100c01c0100a9900c000c00d164010100d5016900414400000c500303103018420605010f666521200825503940303d0a0300c00030240e941840030b032842c05150040c06032901d4818009140010f22000c551045030802103080034a0040c509001e824050b01c003107612400c1e5000650500205a03404541c4144401d10105070002c2d1078039003000100007200740d0084400d0150039804641102c100745d02940c1d5050070f60b000f01c420b5100d021903c0c0e106ea0400e90b00a21034180403c3c4c0c01941150200c3c10043c0c8640035510031038280c02146680b206401c180a6503110071646010111003c01024000078001c0c410150080b88248512181384480070200b0125800b285440050b03a004100b001042842011940e001d45000d4014100d07901d04042d100900c0b84000304015459000034101021840b50303544540103421803110084003 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 984755980 1250 984754730 984754753
    0x301081b030d0c14102a0905090601120626150c0714010e0d0e0102011407050d0f2c190302030d11070501240905150d0f08120601080901050f180f 64
    0x255400a00401d42207429452200c541b000d002e02400c104a54001c1d054241d207949500046403040c0c400b10700d645040303540b40804550f0b1800b01c80c101012500341d0ba40d10500090b54603031726140c8020085500c004902810030008082a00420303602c6060317202a074402d1800a40c3d4a0301d000d844032014503002440740e50089080d080d484003a140300d0180a030020040d41c0d00d030318440a2040804c4a141001c1002084200e080307410350b0b40a200c0a0101100001d6003c00c0c0364030403075154170f0020302182d601d0180c00c2c681400c85c170144130380c400882603608203490050450b40c019443e4000d0701466803450b0756901150740305510540c02c0360360031380d4071070020002c468440e85080030070041c0042c5100e6240d030304440480c000b203030340c07040b03070300540080030727101200c00e1320400f0402500c3c2d41084c111680d42400c008000002d02d8940500409405409030f2089464090300040201170f0040c03242c50560b0410341070000d4040381e800c000d5000386603107a0860301400c2c0c0711182c82c5170895000c2d0440151096006466 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 984757230 1250 984755980 984756011
    0xb0a330503060907050c0a170c03040b120622090c050612010e060d0f0b060109050a120317040b0402010c08041806090e012a140301081b030d0c1410 65
    0x10b100315802c6595914980314200212424014104d000190360300041d1446d000ca01c02140f007000c0c0a60800c50a89008a0039000905540043d80184240365001c204260040751a070b2842c0e074016000c3e40c00c070400c244949180c50135000a4241d14489980d41d44a001c00d004900308081e000c0c0030f000c1d00003661004140032025200f802445021410380e141d502184041c58072056030041140c000e0424070b402c45041d00c501e800b802020304510f0503c0b40d58034002406132507078101c040040940054030000c60416003400380c048006a0131140540c107282d410400014401e0048540064080c80d10780c049a80c0c0d032401034000e01ca9500141d8108054101c0001c032407115400680175260125010300843c201c40c500c03d42607419481c1150b10003110010321075801c01000700b1591400409103029185a09030241101e0b20340c2c020f17042601c3c4e81d0803441c07049030540c080356030104070034605070010480310340407801c020a00320581c10020401c00880e0b807020445441000f150800c4901d2040401c105040c154088 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 984758480 1250 984757230 984757237
    0x24060f08101b02033c0c010e03030601121802220b030c060318010207020d031d091b160c060309052a0405280b01030f0b0a3305 56
    0x1e9000508045054060362070482d50103a4041d8240c00450900c1c3c0d14560803141c041d01074a03c994814070b640030002440f0030545039000e0764101c0500c03aa640b10000a40103081d00c1d0740030380015880d8010409e1000699205000008804c0c500303500050300c0c9140211903880402070a0702030b601404001c502c080c2205146401c100120240d1000c114440c03041060544403003141d07419550000007480090781c030040d0080d0010b0301101580c0014070703045d01c944c0000c0000308600d5003540011200c40c6840008103040c50501a01601200c02500511b030105600300c03480300b000004004000003107130320790040820301c100540c082c0d0700104944001e134840d080207006001c0020240d65501c6981c5101c02c455001491a41c0c00c40a80400c2e9a080c60410051001a00d40034055102a0303035891400400f4031580c00c0c140c1c440c1300c1024400f01e25001c0040004094582940a40c4403851500b61800c049540325101a000c4030500c1c40b80c10711140c00300440300484401e01d102d40140c501c803140c0e8604440e9008004 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 984759730 1250 984758480 984758503
    0xb0f060a050301410f0a2a03020d1812020d0503070516141014060a05030a15060b03010314010f0902011704210908070e0424060f08 58
    0x145903260781c40040509075543e07090780e500a0a140341000080440300054004205210341041505141c0e02c54026541d00080b280c0c2c00003c000d181c02e02c414042e00303004050984c00f00c22800844070307009802d1034044200302c0c0030281c141079001a084000c245190402848450540808210f0705d01d40e0030600d03c860300d100035a20040c055008068030040c098001d603401003620307944090030b214103c0407500c0502d040c61000d4803007500d4402010500c0c1c0302044403201110440702c0110f5000050b1081c0302800e00003070718007072242d6400e043c00d0000da240000c81100c11900034100010001e48400242e00402164121000001c0004000700074807403060588a0924480c0008011815000c0051000c5407050080280050500210b00c2c011004032001c00340c020303000c0d620201001e6803910001d0783c0d13214400c0c1e0407000f045c1c0d08041000b80d480e00784124002801c4a01090405217000e5807840e112544842c0f07011141003000311f0410348074481d80d1000000c0d011300c1c22000e00664540c0b80c12552880c0d003160303 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 984760980 1250 984759730 984759739
    0x92111060105091b090120010b0306010f3002100203040e06040203100501080a0b0a0609050a050301201810120506030a0506071b0609030804030906020309010203030a0b0d0b0f06 78
    0x6150808800d000c2c802c040a8004d07102c50700ca0b200d0714141c0742d400001514104000342070512100c0350703000003e18103818400300003e01c0c1e0100000b0305003003450581c04180c030034003081c2d0200802d03108903c0280f20040d17580075402c0c142c645840b001e000f002d0100300c06508042000075103000c86400000400c2941c50510000e134041d230b030300400c1106070310088441240105058008015a501552400d50008107010002ca07246108038045901d004044c9d0000c000540b100904000c103041645200300500750581c0207000009169201c00c0084010035140c140040380003e080c04a0780100d803e040f0304210003800205603040350346000f4070100b0303800190b449292500000c12224940020304442069109003d00070b10342d10010244d845044201e50081c5002a900c9800006a036520500d10068820344034040310742801e090080289000c4d81161055500800820b89180e800206aa07031144003a03401081868820000c1864003142c1d0320000c4c40c80e0130600522441c0f120824609100d034074140c8 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 984762230 1250 984760980 984760993
    0x30010308030f0c0306010507140123241020060906070f030c0c0201140d09061a0909190f0602030a0b011112030415021c0b131a0103092111 61
    0x10f1501c000d521095a145000c04c10800c04a40001c05049032592200b00d40d0000261f24041001864000403c0e80e400c03035445a032543c03c05c124260a00c0b0081c0c40d12801c0000c0344a505000d01c04282046512950704060207c0b1200064407818420700c5020310805030000c1d2116400c110316550b80d41d56041e588280403d41c400d1121062510078130030545841d0362a950540d41c1101d540055a001d1201c01c2d4120103890108079103480100f5070b000d100d25103482200005000744500c041031114903801041144592110404c0c004440c000041c2c1c0740401d607819000f12039081e280d10340b400820700d22180046c00304e8000310400c05c05000503801548031401c20707200c4a0076181e008a1090b15210b104241c802c1d1004140b0104005ca2616519503034100f00c0000c0061818000506416140e940c0f40c1d0700680d49500c5070030407082030030890500600781202c1d68052200c008076011603180740100020050425607603c00c142d092025070200c0421440300819140c401c0c13090000c00921000f070404900346e80d842401e = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 984763480 1250 984762230 984762241
    0xc010902060f04361d07030309030b0105040e3c0c030705010302040614030405030f030c1b061b1305040e0c01020f15190f0612151130010308030f 64
    0x1401d01c1444c841e40d000354440c003104095013a0f00800100c0c480400450040c0b104a03e40e041c00c00c0000e000c1d50007070300c1c1c104002d0326601d0801c14296050700514001ca041008402c518000020b109007042121100700d848001035600072101c2c0303420501c210782d0002803110f00480c010008111282c0800003501502c2d03e81e0303102d200560076803089114140000d001c072462544036135502005181c00c9440303541900c0c0340c9805015003101c0c640040e50a0302e0010800941c0b01e0140080b92600b000c0b400002e4083c141c41e140c41c503120341142d8141040d01044c000f0000381b40d4100c200c2840c58a0150030014400c110740f2455140f0259101c01c4200c80b58054450906480301c42a0000b80f14940700902d01d89040e51a500c0c270910740c40c941d69048160b0794880d00e407170104442c60228064100540001c0349403280b01e88181c20312200300180361000380c88042c5010f00300c08442404004a03103442189580050b000300c0d03101880084130321540044212034030010008001c00031408000c601402e00b0100c520030a4544 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 984764730 1250 984763480 984763529
    0xe0f060d020102031b150c1c060b040302090612010614030c0f0307050f01050c07060c0317040b0402040e0c0a030b040309230103110c01050702010e240c0c010902060f04 74
    0x5000e010740564014840712007049030f10a02001101007510030b43c0d200b1903d81c0211110780500f80c0d9040041c443c0850b2642c107a0503140d15a4044504000f41405642d1424011854030b12660002074081c40d201000a1034a07100c604440c0b0180d0003142c020008c03503640d9000410004108001c0074428050180c48245901e001041982c0c0b0000003400381411078600010009400c0305c0c00d14041c1880000d100100c3d5003d41806458000c02c803507140c4000150b080d140040c4004c000310340c1c800c1d544075038400340070200d0f0300c04008036489681a076000136844020b070241d503e01034600c0c00c455400942c00101001b005618640b860040d4825110840c03a50784462201c04018075440f25041c40304504201112298440d801c504240504c034107141345091030300c1e4500c40c251131040300d0300360150791150310004c0d0442007040200d00752110010004080f180044480301c586502808120a420300800c101d1003280d005e501c140320140e4004e01c00c5035140780280c4c503949103410500c100503400c5c1c14030340c06c0641d0041 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 984765980 1250 984764730 984764749
    0x506010318150203091e0c01020d03020414011812051506030102071e08070b1e01230d02060c2a0307120816050f010608060a06150c1b0e0f06 62
    0xb4007209462030000c50001210007500000d01108282c450310030303031881c0c4140d0200300541d500850800b0f8060001400006403030700010304822400c051041004100d90a4440700d4030320f00b28000d180c65002c010020001c03450080158101c04a1805205c00034000c002000a10100380c1d0202d030b482e1340103940c51200309800c03401001170107440014113903081a8120307111440c480c2e0042c400c00355a410901c0b0758441d900704100c02c0741c0c41c00c2c0590744002c1454024103a4800d0600500089071074100001d145824003100340256030312140100012a5a6400c543d64282519014080041185c1b4034030800c2e19540c41c1c801404071124007800c40300300e21000342d040c0030950f82c1c16291031014107405a005540d6501180d44000c80e904001100c503105407000420034030141e803c4070081c5001182940c2012500c80c18114054620407001d85454000c006084641c005003c59056904142c010310400d400e204401d13451005250b119903050110100b402030001600b58041c400600995509035030b8502440f881d81c0 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 984767230 1250 984765980 984765983
    0x621020f0403172b050604060f1502120f091206060307031113140a060e060906150d050106020d081e0c0310030203060405030d0c050a0804060216020607060506010318 73
    0x4504000c2030003c140c10200003d00800500141071038140c00a00600d18488000343c90400000250b8011140704614014582c00005c01c50701040300e1491f080342c08800701464461101c108500f0b4000401650091101c5081055944640c5030354401d20014021680c1c810382000388650f4141501d003484001c00101c46201d00030160003004228116102c855042c01d40390000e076440301501481c803180c400c603402102c911000101000c0d8203418034541c500c05807801508110104041101005030781c1d6688007940390056000c0e20b901903951246d2101d00d40522440c5030314000c6604203000001d400f90f00081c400066230b01981e8940407074450356001c50226220110036103100c0c03810700204441a58030ba0066401007403200e0a0722001c1c0e900d80c007103410914100d40680e01e035007000c6510b14a0080c18001d0300025a41071411903d4402080d0b00682210005840684011780c007140171300148001150132400960010300392904c4082c10320303041c005854111440c900180c1801e10080780500000c0c0d4000126 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 984768480 1250 984767230 984767257
    0x1020c0402070c06021c231605011409030f07060b04181101080c18011809110d050c0c06220f0f060b15120603071d01080607080f010303030b01020a0b01062102 70
    0x9024900004c0910584c0e1f0000500904c400c001900c040c008480004d003a482c03092002040350811882c0029040c00d009201490b150010050090040d62880031540320942c00304c400246c00001030b000c68002c00b080c4082c200780705002c1220f40e0920a40c01c070f81035450b00003680e500081d0b0381c038102490650301a842c2680c4045601000d150039a43c0078241c070180003010500003000c03195860303c07140c042c2e03918040b01c4c000d0140000703410f41ea490300500030a5844181098403614005020303044a40c0d03030200a02d000d585203079010340744561101c20798426103a690000380ca080f6024036428072103a07070b0303100b854111091850321209424600340300c0850549905000c0c903c0382040f00c0004664852107006040c1c5030315004540c40406d040000341c0c0c034089800000d400d1819207604182d401031030040b000d400242400015420040c2c0c00220411450560368549400304201d05001c0041c0e1400001e14002409820400004540c1c2980300308110080c6200100c10340b02c3d00740015044040388200125402c14 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 984769730 1250 984768480 984768497
    0x5160509060603071106100f0504020f1b0307052407080601081b0d0203100302240403060c030b10030c020706050f041401090b0f1c05160e01020c0402070c06021c 71
    0x41c03902d031000e03560080c0c0740d09100328003001002007181001c1d4100c8040c048640c8846013071040b2905490a000584000d07241189050540d0600700f0203805521042030b94028001480f103c0488144141d41906502000b2140c5002444500e1030451040151000003143ca11002814161145150a0003540d06840f505100d44070f110002d0021500001d0f54900f80301c040000300d40740c038458401103110b002184017804805046204120254203450020300020381d1118040d818920404104d500f01c0f0781c401c40c0090301c030704610002c0c1d003d480fa2240d81075000200b500c6840284d0f070550020415050725a09980d20319840301001e49943c018268031500310fa07024081488010360b16071581090700c42c14100a00d540341e450108886c140c0c4807480501d988031000c100c44907030004212000c03003015202c41050189180c104810726100d01084041410410040703c1d0903008e034020300441c102c1c0140036000f5980d0b0900c0e410000c4000420b031040100511410142c6400440064080d40d0a503645582d1660b0 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 984770980 1250 984769730 984769741
    0xa0203040b0105040c18030b0703150e010b071e0c031b1823040503190e130b060405040f050103051509030d09110a290a05040608040c0306060305060405160509 70
    0x1454001664428071480800c040140000c901401c0007d51090000703003c240b40010f00101a030718584027224000240440c240140070480349a141540c0e0244032542d1544043e08007141c4400d2100b0f051030b500c0181c2c49503d828004111038040a4902508160f64802000c10301ca00908071a4892140d5160340814507044169194100101e041e81c00c01d9441d40f880c540701c58501d40340000361011a80340e400055a60000e0840000084a614003403d00703450115000e13020031358000040d40c0600c669075551481e140305646810039500603160240003041945440130342030008203801e0009a40b10311518040c10f49040480035100c1c4910035001c09141007032641d8101c2e02c082c209010b01150308041200c400080340c1c40e28100c00c0010403000001c107040300460399500300708940450030134200704000c0100c02800341e042811607045560625180702c0707603603da082400b00c00200d138100400c25403c0050000601c0800513200717001c2c0f4000c1054078030f9844909800180c2586e14400c168009922800059 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 984772230 1250 984770980 984770989
    0x3010b09040e01020403050d110f2b021f091403070f080705030f0307030902190f0b0d0e030a0203130f050916030e0105240d0c05040507020708010c0906080a0203040b0105 75
    0x2050110700000150405d0f0302ca07940c1078201001e0310540e50001d00031019500c0358a8041002c00310100954000d01801c4158500300310b540c015403502201100000c1140d001e03030510810184450320352000d00c40c00201c40340d42c440809411400825103100140040c01d000c0c403080807007143d10807070f80480307070100308445035484140c9a0440301d030a5406000601c04003210720000c4009501c074415950b00040c0102d81c910401c4041e0300220402010100c40ea0801d008200c2c2d007443c9441510301800050f0340381c2485118000c0600069031503641240408180a400680c002000d4400c001c4000c403400c071101e032942c81d881c6007101c18dc80351550168600000c0741c0c4881c00c04010495001044ca000b01700c40141c681d046007075032000d5407500c02054241064401000280c0f030b00104c00030045071414546200b5494483c8446454064184103642c1c0700d0110f450f05008100d0000180301d42c2d0028841441194806404081a4807420012036030340d10014161145503c206c900c00c580c02081104181d08203014030 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 984773480 1250 984772230 984772241
    0x60509100c150906090c06022a220c170c0406051e03100602010c02010b18060d02120303060405130302100b0103060915080c27040203120d0b040b0603010b0904 70
    0x654003000c24045207003030085140900c440540c010f800c003141c1d1945d03a1504280c0d081e03065200d002150040c211080d00c04114045205241103450302c84140040d02c80c000070b8246101050006550070020f101001e0100142c000b5512403409441d5182804c1c8080c00c1d205040108940c10710864030b00b0001400314501910250415040c05001c17405c1c440001c010945080c0d2007510640c01a0700903800c204203060782406010840702c1700713200a000340200d103000f240c03070b0b44204045500d41505010015445840700114084800d40040c030500540c81d000420076140e03071096a8103030150342480002443c0001d17210640c100940e150b40180301c02d644003001040140500d059076410140c56600008404a060181d034185c07001c50551084140d1a1610042c5800305001101e4002c0807500e80c03243c1c64045541408845a544008000d11682d5030300c0006d0400c01c0e005001c01420002060350a1404403543c07008002c42020368040000b4003500c020055280002d10420180c0304080022100605090f04003 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 984774730 1250 984773480 984773483
    0x4031b08040504020a3914100516271809021203040806011202060a11010e010216291801090f030503061f0504050603070c0c03050d0207060509100c 65
    0x5403420070381c42c0d00003e01640d211988800c00510140420620f80803440070756a0340d441004a401054034181703142c50001d0421000180050300d5090034460886011f0241c01090007114504000914000302c140031015103100256000510751000c500c0341c50410002112940c4d41c0c03c0e480301d0902c0c5051000c102064040102d0b070041ca07255001980141c50f01d09070040d000c09254003443d2651700b0041103a150102c164041042e91115004920250311804100c40c42e0380e03c54503000c1454030700c001643e030140c00000c046070aa90710015086440d400107403c10038010344180003170f003000c51948107040d00b0f0340b031100d00e0480100450f601103111188054045804003441000102d0841110340351460710104141003940418000000c20a0a03d041801c0e602048245500d41c0f000080011000300701d80152302800303014540c00030110301024052965009580e80c01140f1842c1203841e0319141d511440c2c8080e154004d403145080c0450a079000c0c1080c5c0350a00006012031105403a4600122402c90301c03040b0 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 984775980 1250 984774730 984774743
    0x1a010e060d0f14100c08010b0a08040813030f02042a112a010801170d0804030c120c05100209010e06091f23030103020112050c0f0a03050a1404031b 65
    0x8100004520010300c0e0707150f05905020780782c010402210881039441500c249401c02204000510891380542c05803202c0858070700d00700c2840e0780c65260500382c034413410400e541c3c0001403440010400071003d140e880c01c588251020700034203546500256003010283c114885070355524407000c1200384150000c0354041211800c9809038111640782c541c942c070101741c50703204c44c03100940c01001550b080140a4010402d2000e01120080581c070a651515100200030040021400100301410b00c02e80441b00c420360803c44a414011441c0c4014090444486d41201d0a005440c0005441c1140f4400d4544615043c1c40c2ca9400d101c9803070410685602206815170700c8840190f1049007080004481008809140c035000d10501d901070f0070a03408203001602200e06d030400c000520040c3d905c1003600396140148100801d00361a03184042c072060040c1c000040c0c8000340801c0404607030340e041d04118007c1c2c200107010040720903d02c8601d840030170700302c4000c0d010854401c2d448001150100b010144940183c2 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 984777230 1250 984775980 984776003
    0x60507060906020d1410060503010302031e0a1a1506090f040902040905031209300a140a0c0212070308070b0c0d050f010302090a06050307060f0c1e1a010e060d 70
    0x5564130454020201c00f080c000d10600401510b40c03c221071402c0074000c0c50814608542c0355500083e90b52003803c4034489858000483d03542690010007442440307552002c0d01d14900c03881d5075100801e40c00c02700c4004100c0c11020000c8080c0e0308040d801c849200c14068151100e00c5150300511019280b0500d00320303000755544210030b0104400344050810300411040108070703420071041a5107081c05000d4021104040316041245001070b162810b052000010003071910703011103050a0341c030700380d900aa94190b2040002c001050302e610a4004120714800c5071100354880a1010041e80d5141c00c4c08000d080410812505020031488d00611303503c0f0b030012000c1c2c2d150400c0e10319a03400780c8506544840c4007a998200600c21403420041c0340398040c132502c1c4100541440c0c00e000a5581905200d20420b126004204101042c0300d0042d00314501d030007540a0802149540d032280c24a43d4401c000c3c0c800d0301d4800c44204032045148000ca040f200d01c001000f00396140c80e000c02c100400000300131540c120318030 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 984778480 1250 984777230 984777247
    0x15080f1501090b0a050f1b0f030909071b02120618010212060402092b02091e010b030c0d05090c0a06090e010509190c03050412020718050a1401030807170406050706090602 75
    0x45005142003113000d14091440c87c2c40050725440c100304002c03003100030381041c0710580c0d840d220342104a5010f45ca40c5030250000c00d00c3d0344402c1c0c00940300c01000e074006400034082c450704580018010700405081c900710405c8201081080e00700d005205040c0d80051850010900034a401d40281000320802001d5000e440381100600c0b00000c0903091b54040c030724910501c03a081d440e180c1a270b2a4001502400301075201d0198049200804c0c05021315403600f840070000c904030a2281069840034805103504200c10309010700040d80c0e8002c55000148180701c000f80200b807040c410301d544812580062864030499085c0000c00c205518000c003043c081014186180c00d8100d064050035040802d1782d00e0020b80c600306410071800b201151955030b010340d880503c00700031000c002035000f10600011706002600da120030581300040c0c0140503c0d03504d52080c0380004014011301d40b0041c2640340c03081001c036082c51030340000c000c1507018501c1a030000c284240440c1d8080340c0f031741d0064082c0300d11620f0014505100ea = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 984779730 1250 984778480 984778507
    0x40323120408010c020d0503090303040b2206060f06090317030405010230360f07080f01060e1302010513030204110c0f06091c0915080f1501090b0a05 66
    0x141c2c0a218141e4450550303121107501400a480d0002c42440c0480c554508440d07002daa920010740000c00c0c1c07000d0000050500710801c480421070380c403603a100c0a440e0849040160181c0030300d010b0380704042c1c5c14100000308680640c500c2c0c000c0340d81c48803000701581d4640e406030000750402041981c155408010003844020b0440c99421403100401e2804680030400032840308200b0010141c02c103000481403240b03502e4070030b10907840180740c3c6c4100e884040b2900500f0241402000889218503101d03480c40810a50408039030f041180320050700030030456a5401c0403c49502040d68050f41d01700780108100c0141d4481c0000b400254a8191402c0c0d03919070f0380c1d02041c101c500c0005500d2200d007011900452541040c080f0504000c10180103201c1814404041c5803500c140340171106000001454031507469000d2050304008045060721b0300c506030380945010b4441c040403654514103405c8600024401c044000d01180001010f03900c42040c281025034501c2c0d20b40c01801000107000d028040301c200c0c001c6 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 984780980 1250 984779730 984779737
    0x180209071b060212070c0b0c0a03090b0115110a0b191407020115050607080f07021305010b2809091d010612050c06030f062b050616020304032312 64
    0xb0450005a0714180024141030100300039001104100110017028046085540310316000318030080304c0c50352044248000d034010402d8110080c24109030000019100c000740102c021100d0058a44011071440000030b5074070341040740c000030610110b840206592609801d10004940142a80003e01100880d000500e2100849010005039103a40010600c2561071361350000601040e55902d04141855403140f5450142241d0322043d11804114102950340740222810048a850300070002c0b9610780d00214407503806000309040c1d584810b01740d02444010b2084d4010341e0780c03003a07130b8458420307040500203405031501c10519601802c1794030600060500c03e05c0b9240042c40031705440c01c00c1420034a00982800c2d50415845e1240c80148100303d02034642c1d10103280e02190455075100d400400b9080c0c0e000c60801c07001c2d4640c00c4a10f00c0c241c1030030041c0002e041c03030150f0a403101604082900440403640c0e4803035400b0041031110b0f08122029100409482d1440300400b803000d6600760800512200180d40 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 984782230 1250 984780980 984780983
    0x170405060402210c09060f090f010608010b18040c020c03150603061b0403030302070f06140609151003090512190e1c020108091203011215180209071b 66
    0x4000e04180030440c40c00040c441d1443c44081a405820b43e103641116444000d44044140100403a50002e22607658414004401c8080148071000c0c5051800c0d000140c00000d02800010a0451002180d651121015184020580115400460040e80500010703100080703010065129190b14031240c0c2ea01840509880540030403d0802460500f00f0117181600240c040010b107a50034485c00040000c05084506485d01030501580d034210703d02d0162040304800da0701400e07072840c01c110003001003008500b15018000403640100e468450030001c1ca600c1444c40e40003580200304039000c43e00d55000e60000305203207005a0070385600c4a00341c0381d08100396001c1e0781d06a6a15410608242d40503402082c111030002c0162001c5a0b0482d840721030070990403c81c00064180b0a6510028200241c00c0141d14040490088569181c0d40d6a21503006c10706010382048400e40400003a0507466003c510440300901002251901c080d0826001e1091300d440c0544100d04126802920111405801c0450050389 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 984783480 1250 984782230 984782233
    0x10e04020c0a031d03060121080a0f02010c030c05030a0902030a020612060a06031a0d05030c070315060e0f010306022109100b0f0d241112071b1101170405 68
    0x105450000e16440442c0c1c035030401c846500e0740513801c9860014401e81540c120400714420032000b070301e40440600f0408001050100006001c82007280d0058111440e100c0c076400070f000f80e034181030094042d1080da40c481c00c00607c040c00080d00c05c0d0410340181c0a0750340083c0c10b90b42c82200031f03000f09850b603000c1d41094101b00a40720074499541040b02040e80202103910307041050b20031003130081b400404c1407070302c80d80304a140c2e00310001071120900c102c800d484040011a20295503918000b90310004040348000c2e240d141000000320001c080503813611071030141001d0b4205a081d0303603408000350440c100b040324034218039030a0395090480c20507140c0200d40ca40002c0030349505802c0803805540e100da11160207541021100c1100b9103907007120081d000e9001c5c135032058605240e0420000954040c1d17281041a08001600b046640420b0003803041901c584c101c48116070b1041403d03159904144099101d840c860704156022481407050801ea001051611007000a01da84170341030f032000c0581e026a01d5 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 984784730 1250 984783480 984783493
    0x1314121c12061e0f2702030601030216030809010f020f040512010e030304080306030d0c1a1b04090e120408070312170109020c010b010e0f0d1b0f0906061b060902010e04020c 76
    0x107200003006130400030043c08104400607850030400c6801c01e022400e01d04080e80c5c0110109216a0094059920311120043e103180c40180764100104140000c2d900c041c3d0701e5103440410301e49450a402110760b0114a008040c0c50507103441c1c1800b000c480c1310f10500025540c2c441c039001172540148015030040e40540115900d90401c40f04050405005841c41000d0000c242070740000203040c00c1805046500300c41c600140380d0380b021384640c2c108003501c00103110038100140206203c1159802144240a00801c507a0100200d0794051410704c520302a542841e0301100003040014000c40f641c0398404698907000c00803441003480024401c10a0b003000a940e500803c03070300580c102c00d01c1345c120014001d280c018000070300000401c6410029080107801480703415404400d010b400c04515a85c6088a400c0d490440e946a00c20400e4960500496400d2400c00000241c01072089442c025402e140c60b00045052410341e880400400182504070b0601048803440d2030b842e5158030262075503180c0c21001d03252 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 984785980 1250 984784730 984784739
    0xb0f0108060d0602162a0b0304020f041e06050d03140a0318060b031009200d20150a021b01020a050d020c040b090f010e0c1314121c12061e 61
    0x4003441e200b035101612040d41d8032541d6801c004240740c00c04841447c0003a90303482d01c540c004290812200c01c0840d401c1802e10500405645100030544079001030064204021900d80007081101c04060380003900007a00b10101c1c46008040780700410030301c001c9040004040e0752160710480000e810b01001e82d030240d598880c1074030b10305060080c1366003074450100411030380d1400d035030b06031449003011840c501c0c0d024204000007080d00c44944011381142c0101003150703000d5200d003100f900c201c140c007001400741c0c620950408248500e003094402158081d0042c03c1c03009003111505200c0e540000c5014114800d00340090003094061004003038040069000d8400c1000b482c05010a58800410035030003003074004104250aa5101149415a581c00703821580607101c921401d5124001d100d106640491074080001d6180c0400180300b80580054800d02607901c22181c00d1521080b1142541c078041030569a000d82041c481e06c00000c0100c003a0030005525900c500400b6100850a040f006184401503000e00 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 984787230 1250 984785980 984785993
    0x10803041505030910020a0207080307080405040e0a0b04060903091806090e0708150403050714060910021602040c021e011409010209060412062a080a0b0f0108060d060216 75
    0xd129040030b060041c61801c1813a0440da44083c2052115002030340890001c120340d10034405400100f400340101e940300e82c1d0505094485130b100d441030601c02c0c1e01d400d00c4800000c20115aa40086420501f0442196a90b86401020700300d12030342207041040c04a40400c0d59084041c3c146055803881900013a02c40c2001100c2c0102e48114000502035440250700300401c110001d85800a490140036800d82030311546001d40c0c50340070b03112000701411040003103252a0740300056031034400c41c8020100c030881c10140c1c1141c4224480e201171081d000002d10314031405400d10340c004d02c040300600c1c4111641241a00c803c0d0040010020110415035141c49610034400025003409420255043c000c5162607441d0380080c0951003148036200035445074040310070520100d40d0120710003403800e6003180c3c00030f03a034002a0b044070368280c9020401300d400b80e0082000e100c914411048100f001074104850b65500e60015680c2210050866a200304883c1e140c500180040c0082c0c42c4000c0280143c800080083c60900d = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 984788480 1250 984787230 984787259
    0xe030a080108120703050d11270a0303090308090a2105011a010f1202040902040e01082145130c020c0f1c15060b03060f041104080601080304 62
    0xb00241d91008102103403018500044a08139545810060b54403d6800700c004050040203185100482e0045030514003004848801284516614003180510810804000c9942250b00016000400001c814000580c8050003040340050007064001c0169544060002c50340c200c10071804145244030300e0b0030070420240903280a03400040e110031a0001c0e15400200014648050340040000c496403182d10000e040d4100c5000d030805800656885032108401c01c06140b084c8948402da102c0e21403d18070006050308245102146d14404914000e003103816040070980114466015404981c1411140b20f0122121314850b1008100c00500c0900c0004001e00ca00d00301d0b0840b04500c1c1081400c14031503a005ca48904200c0c2c1c202d80b922402c01072200810b0000b030510320030300c1c3c10481074203004c824041411890000c0f030b00c03080414000d460302c4141d000082d0105441e0190400d40030500180c41d8070789600601644544201030b20300309540e0b01303102481c0c180300382c4c03181c040c940001506004c0303c410705680 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 984789730 1250 984788480 984788489
    0xe040c020a0b161403010b030f060d02010f03020c03040906180501060206040308011a070602032403010b0612041403040f08121206010806030715051c06031203020309010209040e030a0801 82
    0x25281400303498480c0c07260510028400864000d00040d083d802c980580c8000e54031110b960b0b440c40e203a42c0c440d10b0800c0550310a5a40c4008140c0034400564070349045044030600c682d06035242c00018503105400c0e4007179081035a226146000502021600710441e1061500801c071189400003212030603d0b4600403548103030004c0045420600810001c44d400a030524111075a01220840010160301409200d01078410000c0203940004203015009011002401036582055180100c101c071880406089441605040da003241080c4030000000543d20089039116004407000000d41001036034241c1035070302031707000420040c0c400314007880300034010840e6001c1c409000c0301c01c03850080d030704281d01c000b540e00420f8a41040000000a081074800b40041c0740140b60101001d00d05030340d20440644280c001514004010220900c00c91250005005035030450b900031502000d2841e9180d02280654401003040c04e85640800420200e078490340314500303c40d0111800b071500d130410204002d00c940c0041c1d01 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 984790980 1250 984789730 984789733
    0x31f0b0102030a1707050906030c030906060303091e120a0b01231c03120c030e0c1005091009030203060406062102060405131515093501020702100e040c02 68
    0x42d8405075a0058244502c14014500710741040d5031740c10045a035482045485a007040000c828860740100c03005c00340d40919100130517200d003a921182031640c2e90194454a56021000c1042c100b104212095000d6101002400c04c07030301170100503002881d18801d04012652003a0300401085008000784010003010301c0300014038440100b103000200201c0c40100018003030480da040b01e90425020b2a0200030324404071005100c07629010f40e01030300a010300310a44041e4094448042885c2c0391030500180f0f4485070b0b840d180d00f44141e000910081d00c81500403413051007100500800503035001c1118a1003a0310070720011421a0a0642c48100c00820b16194600c1d009251010380050361000c0036142900c0c01034841c45001710050303052074003400d002d000b611a141128080841c00c86240000319045098a8640c42404d0b40d40340c441c40042e500b00d40e01d010001d00302c225443c10604405108a1120980000240c00c01420f07400040c81100c02d88001c40208910211012050a140c020340c00420307061f00 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 984792230 1250 984790980 984790987
    0x20a120b160c0206090f0607060e07080f0a0503121803070c141206010605090a09020c10150e0f0403200d03060902040f030f050f03042d03020d0b04060b031f0b010203 73
    0x80c0819500e0041030017a0f071154a807600c18021648070031055412040d006102408901c40c00e4001e251155100c0c06690424006c511402802160014a0006c0035138803100440ca0442150f0340303070500c207402512064100c140b01b242001d01c80c4082018010306801181c80302c00003407808a030101082029002da50080d0401c0854043c001008100b0504440c200e040c140e94404c1c0210000d05ca98803203811425050384040b4003140440400030344070a0004c0b440038204514803030b00744c105030a5241849054040e44050001031000100c00b04a20f800510a08010200c4000009009001c0f90503840d200d4195005140341c0704484d5150107160000d002060003189010b003040103c09400700b40e400050015a2007001100810034204a031241d03088407402500e03103e80e199000007280c2e9001c013200148641d41942c4100354200d00c08030500c100c0780e0080c254801000a0382d101400c03441c0081051310156075131342d981b85140c0c409011100e111030a15100310102000c00c100c2d02d0131980b00c02601c90443d401070 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 984793480 1250 984792230 984792233
    0xd021608060a0f060f09090c0b070b01060e1903031e050f0d0e0c030f03040603050603060105100806030a02040c09030201080906070c03050d02160c090f090b060607020a120b160c 78
    0x20852942191860344041500303849410f0030005010740c0c1d408044d02c5141c404002448080300d03413181c07004603c43c020b0081801d903a80010341c21402500340203080c4080c268010002035000c1c103120004440050407544a60307001014550b41c511309079000394003040305854107081e4010751a428640411250414a082051540404100380a41201a1045659500a81d9610504103c2c000c003901000b000c840c03032103007000c0300141c0300c3c2c10a01c00c0c100400d0800010890510300400c620381a1080903154010008c1103600840307000801820341900350090801510241c8ca450107281400074158840000c498a188001810903074028822085c1c1d402500600c81000c0d80404400c003003640510b03005440e10561080c88009104100032210b04080710703031103182005240f0640c001158039008080050301158810481503404406005120400000c0001c0340c0b49040703c09815406d00180c0003c0b0070301e8480314245104030024078150782c038081000406c50901408030408495180e24a402142225207 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 984794730 1250 984793480 984793483
    0x240f09040509281505090d02070f0b0d0c051902030319091709130f05071205040308010b0c0703020a120b070c0302030405010f0516031e170c03060409140d021608 71
    0x8100c1100801c4003500000d9050020b100b503c14075618418000304900e0a00b804041c0d81d83c222441f580c1c1c0580604d24000a1062600e01c42d0b0080300c451080072450800c401c1450001440c841000030280203090041500c0c1460801e200c000181882e0011643c80c200102c400001880c0c0c0189840c0060400740e5840020b0342c0c00c511085030000f01b40707000c3c0d02c4000e150001800003244a4008500c1e9240070440c1041100980106004d0720007a03c8020350703040800a000140c5100b03d5000d00030580349401004100030b03480090021600d29001c2d1844c1030703103c0d030010388103008603031000344c410644120396810721800c401d645030411440e003007044003071303540f640c0194990055201b02818003203151a800c540f540110100d60b00c001400e208881040041e19000e40903031401c0980104401000444d600814010b001c410030400d50190103c10a96880030340075550380c00207000a42180e2200c401c00c00140189404103c080e100e10017400c3c1c13034404001c000303241950a1419004c054107a00c1d04000c800c00 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 984795980 1250 984794730 984794773
    0x4090207050316051b0d08031801110a030203100504141617131a06010c06023a0b09060d1401150b0c060c0414240f09040509 55
    0x4000005a29034155081c09401c50007100142c4000011454048041180c00b10b01c1550612a0702003160a88902d002800150fa0100400825140c1c0410118000404c1c600d06008440034440001c103e489001c0502c100c540c0000340b581e008650044103001c50840400072410181100340c60800030040030f583c00c05030032000980480c507880030050441c402d43d8490031904600700e0160708002d81e60701300b982c243d42d0101c10302501a02c118040d807a038600c8480d49030041500030340050392440c0641d010b5442d8070b0020b5000a410101c00821805001c00e103614032000c140c0d6103100e108285d0000004000b0b15020794040b9030307903180305030002c0d01044481e0383c0340b019016859410180c1c042c61104061052030042c441d0305d42104400c001c13550000b44960701d44000b048101e04560545500d1388640c031500d08940140d004042e04031110500c02d8015092030a030741e00d05e08807401482000b0103000071081d1074517448520800b040380400111451681068064903400c0f01e4060010005081a002c4113400c032032 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 984797230 1250 984795980 984795989
    0x206041503090204052401180b130e010909050f06040209070302031e0a05090f010519090c12060c110a170a1101020d06080106050a270f09050a0209130804 68
    0x251654140c10000d40300e03a00541d801a800303081040182444e82088045140c4d215045c2c140c4201e038a0703c200203520403024100004221103201103600d0034024031084175044030001c802c2c0345821703000c000b501d0115190301c14000d085400001500191b50308145051800200e143c541c03a03400f1009000040e02c0f4144940d50143c0780386401610780d2201c0c440d2100040880381c0200512154070140700c1100c07019401140503119520403a14003038403942e200c60070f03038070121800b07070740342c58680f0089034010040c0c1c0150b201d0502c01c01d011403142c0d0302c441ca5040c1d46048202c05803203c1d070f601c5c980f14000c2604111718000c4810580c0c007c0001d9001035448038003450100300350001c3c1400201e01942d4a5010300740b06490084400025500c0c0c0c10088003180041001c3d01c00d9142640c20f01c140025181484002101a15543d0900b41ea828076070009001e042c8087c03101e03440e00350350b03074540103000e041c01c6214035150315200303d001c0c0c61000d81c01d0040001104019199041c82c8501400080c0003403c0542210f0488 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 984798480 1250 984797230 984797249
    0x506070f030f0c0f030b030c010503060405040c15020f0106143a140d0e011b03170c070605090105070c030c060f06120c06030b0a05040e0a050d020708010b0d020604 72
    0x10640144200c0203000404012101a420180385108113600115001182e08142c3d60812180041c002055a502c031820787c4203002c01e0080000c221282031a402c12a44217014049080c106640d0b40303588042280901032560050304000c125070f00440082c000c0c60000c000c20704a0580d070040000004070b0200007030f40c1f84e441050102d61512800e054401d940c030201c803941c0c1184460304903541420b9510044004400405d0b001c0c1445040745c2900a42580104400682d41c401302d02c0b1092280e00078514007450183e090045078030b14a180f03101a600e8061041001041d41510303000c007803500006540001e440340f0341c640d0514080141c40e5520103d5070650a0301403030038240d00802401e02100500410510024040c104900811040c1007143c001015602c0352120001d220350340c460840440c0c140f59044c9a020b00038002c2005180380c44d400c0841e078143c9810036586042d103541d5840e850b00d0003a82140b009a0040d000030000070301d0030321803030036a14003e98400150b5503059001514502c039070f00800194 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 984799730 1250 984798480 984798497
    0xf0f0105010e12120711060c06040201110a02030a060f0c0806010f050d0f0e0304170304030206070602371b02092a0a030203060901090207020a030308060303071a0f13050607 76
    0x26500c5034940c0f408180e61109507400403112600d50380a40c0d00c501000d417508885030141e01510701300034086549944119001d0000c2c1d498946c0111440301d404e8404541e40e20500340301d0400360b81e003401905a898801d2400089902c020352110050324200f00600c020300400801f041420b036003104031845803400519065940d08048202c00c0c2c000d203000780804503018500074401c1c0c0800c20001c001c0041d504133410000108c1c1400d0302543d45c9101d540002900b11100340034034000103085802a1100340240010414044204101411480e4113a10f107c40d10b00c81a100c04101d003a0803903461200b48008040c461030040d800c2d0003044003501c020b8095007101c03404944c010b5045008101c110fa03180700c1910344940d201d4400c0e500030040e42003036500c1031046544200018a010051089647c11a40078151114440c9941c500395000200100b1954240c0010850f03040058036100d03591604c8901884100c1c1d81d03003001c5668285000c0e00034000100c40d06c0c7c004419001c40c000080c1d0f194042d0441c03400404 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 984800980 1250 984799730 984799757
    0x601031202010e0f0a06050f1308071a07030603061a060313030905060406091d2a040906032009060a0905090705040203180d020c0a03060b0d050d080406050f0f010501 73
    0x10548010840614090b0300707100480d10b04c0c04204036500c41e00410040c0069190440240d41d008016940c0711b80c80c03070280c040c800c0020a14409410040d0140300140044d00c61075000280044081b0f40020009980b100d09004003c014803030701c40f0054105030320200541d5a07001092040c8000703403c1c0e02400d040b52801008061048600c81c02420000c2e102c2511035591b42c10181c8083c0c2a80144841031001c00465080018960191486200515406102c600c580f50300030701e000c0348001c18039003d410304210225101406010b808020361088034a0044240ba8402074403403090210b200070311403903611090240c503568000e0600240c0ba0300140000d2103498041c8510b2030200d040c0d21a5421500110412400c440c80280691110b806076081d034481003a4040b0407a282c0d1003405445038800e0005100b4004030389a68004210f548011b885c48502c5421a00d843d440c3c000030810040000b0b040c0c0f801c000400180703000d031640107440307040820000d09180c5038030445090140200e6041020701c0c14150b5 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 984802230 1250 984800980 984800983
    0x10816200109210c1509080c0616031b050309010608030415090f06050405090c04030203191407030210110709090b0619051c0f0204062d0e3c040c05040203090601031202 74
    0x6031b0156000340100d0781c0d0800580c0b5592118400c03510030030408075070010480c006020340200c5581100d102c11080c00311540c0181620950806420703582e25658840c80851055402c0006101600a40f06c4401c814030358020700170030201c50341c2c0080d07440c5480c0c20b50800109800c0320542d030603140102c84000f0701e80e03100c00c50403400d40a40d81c4040d43c184241044020340000b107581d50400c3d64001c0c032111f14082c0303000020b41c2e900c034047d12000b900a84200c02c031025007845000b240e00610440001c1c0e032001c0c0d0b502c05896054400c560700c00d40701080720105101c980d2400342e1426014200c0d0545044580e031400c000540843d00e18040d401c010601804054208070140002440c6903500400c200801078407030030490344134011050305614103500080700f12540c80b05030414000710740e28201000c0c01507031410740350841c84075000001e60b092244082c0c0e821701d12100c1402d080c180d8444601c2d41a16141c141880a0320007c16840640070380d10400c284030b0045d4010a401d0705503a0404984400c2800200d400c0703 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 984803480 1250 984802230 984802241
    0x602070f051f050c03040b040b070c14060a062903071b110f0409050a0f080712030c03050106050c151b0c030306030f010b010816200109210c15 63
    0xc186010b24260441228151010b030000301501e400b0400c2507a5910410901c00d10041c1c0e006815003841400090002d403881c000240d006600e4034180c0c42600540c0c1d1349100d01541c0f107442c412150011010040038640c00d00c61000201100c000c440d0300c0c1460042000812241d5413010b40c440500040094200360050000325580f04c1442100c000314041341c1840380e1800800701036280300340348681c00d640b65442c090040c0c00c22240c12101809001c02c02c1e90f00d40d46071041081d801c5481c040300f8000200855000b807581440c03a00e0984000c141d150741c140008040b110141c00402c184030042c0032405074a4000a80f112040102c4855140641ca4070031070803031b04100110704400c00310700000720ba150980000c4040c6009070425800c444c0454425000c4a0980d0744040d10580040c0ea5070700010a5040401541017419245080c0000000740c80902d80034005010103880070a43e458484000030000c0e881c0852003114086001c0717174810031840034001c01c0b603000c1010107465041c41c003420b2200b80710940e004 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 984804730 1250 984803480 984803483
    0x6050c0c060d14071d040e01060909081b0a0c06230406030905070512120d1e05062d0d08160b0f0f0c0a0f050903060c041e050d0602070f 60
    0x10151142e0340d030106100900600200741c00550302c071030b022a0202d8003980c00c1c0b010f14030000b841c070700c1e103007005106000c000c1480d0a0404010f41d2186070000b4403911610400f01c0d401e00420142c0d03940c4c01490100c420041d00300b40c034508190701c2006004c0c0894840200780050b81d88610340140e60594114226111425041c60303c1120000003d000503510b8041d40000354041c4600705948400340d4400c10001000c00d540002507071500110b03603620b004c01c280c10007000f44050790180080d0000044110b11040701d078240c9076000c01540c0d482841500d1070074a81841d440c0c01e82c894901110b41107030304400d80c03e45a8406160041000000507810020320900b030343c1c1040501e0301c9146081d1814281aa0072032002c2c1c511911181c008008260130114041042c0d11a44c10300b1a03d42c03500070504000c507000091807003a40208402440118007607a418821940115115054180c45500b00182d140764080d161310443d5460000041c1000641c0350408140c2d142030b00b10b0703401603c4c0e0320b0a06103490740513001c400 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 984805980 1250 984804730 984804739
    0x402010e180c0309010606091406090310062c0421090305031210060203131a040504090f060e01230c070c060207030309060e0105030604050a1e0203041e0b0106050c0c 73
    0x4202c845481c582c090b500c22002e0800900545540d0041620584c105018240702c940c1048200c40d1641416002400c510102804036084034080381e28210446a89801220032075180f082800c0306507280348140c101d941c2400142941c24140303a40c0381c40c0881c146200c960344124050950040403401003c0c001c0046030483d098941d00c4900c0c000c40700c0889411244400710611001010580d40d01c00000d81c0d0b1400024000c40104600300601e02540f0107101d01da105a5020410003c81c1903251401007130075161141c0307201b4100c80390398501081a07411050f007506d46607144c2580d00e4a021400f011664410085203462501c0740c62300075a41c00079109205003d4102c0240c0000000c4480d07000440c40220790203940c980e2020344c0c44010846283c40c4140742240010018408140319180c10740c4030582003469141d00007500e45241003160304112007440d241c0c440aa01100300018405030070380440c0c02110320801c41a1014043c2d039030030740808060080c20f0030400302092062070003504104640d0310b41030050 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 984807230 1250 984805980 984806029
    0x702090603031b0604051b1509030307020604030506070806040b0d030305040609060c111504120e0d0c091a0607080301060c0602130b07050d0e0121020d051323060402010e 75
    0x52a69135560b03020f030303002c0390644280e511540540000319110784040d4001002d1a00c9000100032054964100f120000c0c1e16020401c8103400580d06c2c1c80041008501c00c00141820341303440340d00544072400081032030380a00d0421602010742c0d92802e5400b42203d526040008003520340e410604000c00f00f070040141054a48000782034400d400c0100c0c0800412803078221145c012400640201040c41a940140184a030680320080316004e201040303844207000c0d0884400200944610101100c0da0b030000003081d580f12010b001030140da00590060100c02d0324010301d041e24503903c001051105128400070401019505010090142c04a03400b00d40c02d0000081d001d40c448010340d40e03c3d0b1100d603044072644100c81000d6132050007000d0703202944105840b22151108070f2540f0034070000242c0407185030303c1c1d801c112801d00390f5090300c0380f103020b10040280c40801e2001460544844610750450b4a4181000d03260a00c1100001a007242d00c10b50a29040281030112000309421a80e030340d07011442003a010 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 984808480 1250 984807230 984807277
    0x904020d020f0301090603020a0614040522050a1d030c03090910030807031e0c020901030b060307080303131214070f020a0503030a02010b03010615080105040525050a090608010b070209060303 84
    0x46e0481400d9034000c45140c102e8a40e224010781702c0428500d00308001680501c41040f00c1e2610300304404d451403140c1d40030b00c0342c0b8140401e41011a01d01729000070f40f86503600c0c01e802c400441051414182004c0c08004c52500905003062a6a4022030074524450340c048400541542d0004a1040c015648a002107848544500d0080c007001d85c0314004101c841084804401d41e2442915081542ca4001c0c20030365469003103807140240310100504158041c816041c1c0020301c1d0004200451003043c0300801c00d0056286850810307191040e41500c00304104980710040b0415615000320f40c071940d071202c00050018120b1000c110012819400203600d0702000c1290500c807030f010f402c01200103c1c2240200502c5485495219030211a1000c074400200c40b403005200904081d0702ca81d40058581600342002d02698404d1154001e40304201c0002030400700c2c0000600380c0014064002c1c1c00603050540ea5507040104114050003681030103442180c4182c0880c0c00342d101402220802035a40854a8006040 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 984809730 1250 984808480 984808499
    0x50a0e1f1d07171504090204020f0d0e0c0a1503020c0a0b09030d0f020a09121401240b031306091103060c090f09011a0a020c0303190e01030b060904020d020f0301 71
    0x84440c1004104212620342041000801451290380144c01d1031900f030780303903005100c0140308621080381c01582c2044042417600201c40a09444101d51307001251040c001103040e410302500045a60141c0042c00050220f04020101241c1f98146803800585403088110914940154500d015280501180c24480d0606011000704810324407890203010000c01151902c00700d110385070b80b881c00a8503e0308103104825111501c4680c4a00030b0305910300d0508080b89032421142e503901c0c001000c402d46003d500c4040700d52080d4800a000846a1900354a0003104500d456402d400c002451544d45000d56070410400041044a81e84040c080b654070b86031a4450740c000d80d11103403801c0d1080c1000c9580d01320394902480c40e18140d03035540030f04480500d0342078007685081d0442501030003540920341411b203581d142040609620200000300a4540d1a910005000100c1c051422410503040400c20303019a2660300c200c40d40640103490060707841c01900c80d000b00900031000d00c8100b40600100001d11300c0b14 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 984810980 1250 984809730 984809789
    0x803060907020714010c08040f090b01200d0c140d08100b13050402090a0902070609060b04051b180409050a050f03030f06041a220501050a0e1f 63
    0x8094488000c41d89804100b070303945071264413401c030510700703403840030352040d4459203800340260310818005040940340c620420b8001c2c40e0b5040580d20f1550f4505010096a204826040035042c403116502c1240d00003d00e5511a19000f903901b0610131400300f01c01c204804640c000c040700c403805080c0c03186440f420034000c02801c0c05891641c41000708680c0459600300100845036100900c020008039030b0300e03103018040039401c6007105030781c016a2101c00045990f0300303000801d0131512a600000d0594040d280030001c0315240c54260b030082e4501f4042149684980c0700d400301c3d00c0300003810070343c50b1040b0070513509040d07160503122504039080c005607204002c2c0015103503458510075815107103091515000a550790004440c0003005c00c1900700440d000782400d60041c00c10080d42e0352440403003040f48021803403100c1d19155003180d80e611034940501d40c02d182c1c821035025060440d01a10f83e680f619841503000500a0700c204940b009820005110107005410b203401410411305448089543c0d2041452650 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 984812230 1250 984810980 984810991
    0x30c21140f0c040c1d01030b06030109200705061503010e15040c0605030c04031205040e1906090204051513081c0806010e01140304050a0818010201060902030c1b030d090803 76
    0x1084119414083c0303080e0145407400402540d4418034206140d4003a01c140e5002c00200381031550703840c4885140c6d100c020003140a020204004141320b940940c00122214042c540050018000d0080c80c00096020800c00e811460a50840844c4040700b00001e00421182542072020300c607007060010b08451602c81c052280780141c9000566958030002666244411a41e21140d848104010b000065440d540c207281030300646040c50500e03481d4110318600e500c05440c500011039885e00600c06440460241300060004201e09504052401c0041b032101020b130341035030525107030100e40c1e2480c0e080324245840080c803461007210100c03042080700200c200c1c1d01c044894000b0341c08000140d83c0394040e0310104030300541a59408080c0307404c100e510710340b500040c0040b5100d02505030504042100d00010744000c0c0c2c1d4411083c00c82c41220800a8211031641c2d2004060318014010016a070580c42c0540790035980b402c840a00610f00001070600b188039001c00500303450700e01087d403010b01c680075001e503120380d = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 984813480 1250 984812230 984812233
    0x2f0d030e0f4c08061302040b030c0711030c01080105011d09011d0a050412050304030201021b0f070e06060306190e07050909010501020a023708010b030706050301030c21140f 76
    0x485204002c4800d68008156050100d0400300100f02a81400304030107141c00d030007510060420340c039180ca04100394401e65000c3d0100034081042d81c14403c02d40144a810b9000304c00401c248000000080c10111052080038184114000b0b1120491a002c52802e2007040013021604d007982c441e81c07880c11b44051a03012201c18040c3c100000c2000000f0b00c200c034015500424009101030300c8010803512548000d1044003103540a0086410b4802000645401d081d2180d014011008020f2220381c981041030307005036402e451a4041c030140d91a140b0442e90007860641d540d60712a02302e0041d804c2d1b07011242d44013000c1d28070f500007007001c503560040103800b280e04100d9180a469a031100120f03581c0042000295110200401d44c00900c2c00350442c8904691030030754034840c5581d800e081800c01702d0a56000c0107042e516140200014902880180007800c80360030482c1c21541191241404c80d0524090f04148103082106039128128100c04840031030380c4501d004e01c8a060001c42581ca072700c03a210940034a03 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 984814730 1250 984813480 984813589
    0x16120b062a0a0503120c070231020a0903150b0a030305031b030603100903030b1305100e10060c0c05040207050a03030e0d0f18032f0d030e0f 62
    0x2403040411804801c030f41000007035040020112a24104420280a10200380c204021440041e155141d51008650310304081c5090411140700809450150544c800c1e50607104001c510806a08a41404140d0b40c100e001d14505043d4140342d02e009044220300240c0c8032076510400030801d58000002d51140c0c400410003150382d01f4070b603e141c0850100344d407000da1541101560112103400c550103012558080d00d80401c1c6000544007088400e0f06544940084c035881d1404c02c01d00340000340545004282ca01502c90040c94503005483e40701040e805540c041005e04401c1e042400030200707002e009000300500031541c6660500e090341c0e0741d04070350900f100807d0030300711049441000413032182c805140903107615510f04100402110101402401c00c4000014000044003050f0807540300001c411400c01001500700482502401400c1410b6015106940c083c201e0b000096000900b04244001030380e00440600220001603d005072901801c441c01480710b0710a40c2c902114441800c1c010036041000302c0 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 984815980 1250 984814730 984814807
    0x72907080c2104031127010605070c08070303020a0b041a1510021518071703030718080a030e0d050a0b011d0402030316021315050109080616120b06 65
    0x200e070302452001522035a0290200205ca041c542a640b903286642448140841c00c0d44400b810a40400e82225002a0000c14041700b000003a95281e00a040d05e2001000d50354a140d8000799900c230741c2403008051240384004101003000201078105900400120b11015103407140d000400703051791210461085402c851070b5401c0724004204011f0442000302100b507503607180d0203806200150104031525510035004005a003001d10216910300f0b000302d034046c3d40c1d00e0500c2d01004041c2a0003401c03056000c140e10404000036100021200451a818140700208400c8240041c2035580118409440e43c02558148802c21403503014450684141d11b0788644031640e2426005008001224000e40580c41004040031062421420110142c40201402c0000070580f03d00402d90300518a0307050040c000791000d00c503560300215150060074800e40102101e140403c0e0a08021803441020410f000c8010743c036050a51a54104800051026007045e560300081c9440706802034034a040361a426000342da8088 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 984817230 1250 984815980 984816043
    0xd140a050c01120e1e030f030c0909071b1b121b090b0a0509040203160b1801030506060703080705042c01080715120b120307050d02072907080c 63
    0x146211504002003016030b00c03c8540f00302030b0701174402880803803000340180d100d6a090000154464400c440c421303901c2d64008002e0220015000e480f910902003c00601545681c140e204060a550408555058217005c17005c1104030600542181110241c407058000c10f1003c40b005400200451514000c0a259192131040c105d519110b10f0f5548006d0440042090740340c681c1d90190010300044c01d41e009580d18104d003c121040a0f88044001040032803d5803a603406581c01035030402c02820248468a400781c00143d1034030504000800340014800440d54403840b8030151809407540718940c808110708645020101e00721a415811414009000402c404a0109401c4115071614143c1c901052402005135528403005416a50140d5110700c3c4c80c03600d03500c0343d018005240c0d980002d15030320043e070f050140c200210351004c00150350004004005505088100c094050408958140c04904c5050f000c00c4511030039201400514010032031120701200481d8074202150124501d0103d54030801c0080e = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 984818480 1250 984817230 984817241
    0x2307030e06011406040b07050118050703110607020108011e081006260d050f0f0f0a03230c1b0d0201140a050705040b0c0a020414180f0c0d140a050c0112 67
    0x80c0e04600d0170302007041002004006845103d00c1403001150b079040c00800101d07108020300069980d648013180800601c40c0480030108080402e560f040e1034141e880d00080d144070303010302c6070200400d8903d80c0c80501c2008101d1080c0544191000e41c3e4034800300150000103000713903010703048210109444059a04e00f20480350700c106650000503000580791028241c4207030f004200b6105035040d003000b110034280b14600003042c504840d1003090707031540343c0c2200060840d090340c0400c514003c22640c2e495405004801d07200d520001c0a61000c0ea68100b244100004000e0355441e1017491040301101c41025406400024145030760b01d00888056441011000a4800590300d06c00428800c10041c06040716070b00c0103120b87c588401c01c8441d00c42c801e40c0450f003120801c1200071140741d540414401143c07628405004881815401010689500d04105445031808847045115282c0e0740c5544041140590840c0f51007030031801a83d0f403180c0c89040003034448090403041400034800c600000c0c186000c92254 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 984819730 1250 984818480 984818519
    0x10603032a02092215021306032c0106170303010305061b03071b1a060108070c020102570405070f20101a0102010504020904062307030e0601 62
    0x30f84544880c143c500c44e030061842180030345800321a05002054801d01c0d441c001c43c400d900c1c01030b590001c250004140c868190819401c050505c4150101c0459001400ca07808d88502c2c00000440c000503034250050400e50311000300295105480c5111405c084007460490b4084e40c03d4441a03592410341a02494103180c60203d03124050020540444c4a056209208081e004549106142c50b4550303c01402c00d8810f60303030070f11007244100b0884c2d50380024419003169513403c1c0580c40c07025a0340041d444e0b0a01408c6100719210400502501003403094004007032146014141902070002c44002c00c3d00e20001d07250b041d8400c10304200b50b002d4141172054511556559071003001440c4490000c035407100c9040b5113170061a08965200d02c00e4041440046000c0d00000030001d1200d0642086405018446802d039055903d400304110160301c2d16080168401d0f0300c9000011060411380c84805400b100130990380c0b0712000402080060368260b03102403650f078004070469005a98400035980c105000b1a503 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 984820980 1250 984819730 984819739
    0x308191505091b2212060902041104051516060e0d02010b0d0b060906011413030b0f040506010e09010908030705040504050a060302060901140714061b0a02061501020a05010603032a02 80
    0x440c001c04a40e0410f01d1180300c50b0403603c01e20a0350340303444c511950441740c0c0d801d80e40e0715902c044500840c81d2074840c0d03c00145a03403800234240b52030003002403880320800c0d49400303a040d0300045109101301501070ba0313030f0031039071110b010401000c0710310000b0342d1181c0a0b202107002d5864039500304c2e20740c600203400c4481c10303511603034060f05a0b850400f402400700d400350105045c0581d2500b1400e82114003000381c03003080b146550184503503144d424840407800c4058044170f10b488a6206001c0400d2002c82c4450644030343d409600c0032611400481c50051107140b50142080102000344110154440020001c03175000300c80c1881aa1501450707502101c00d580320080d4000e600700400f00c0194050f04004001c0c1d5140c17003500d4241403081c0c4030300e00d40e00c04c1d00000b10001e400150070040d543c15a112580310034007038220480e007480140079019555140141c00c00b0003003080300072030030035076842000017010496015000b4000c850f0b4070703d0090001c100c0800c1a600c140401c0b5030a50254010149070303c3d440350001c0 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 984822230 1250 984820980 984820987
    0x7080405120a0e0a030501020c240103030309080f04090b12010c12180209010311120a0f3e0a0503031e0d0e120c0c0406050105070308191505091b 64
    0x1c1c0c2440c0c603800400200c0a10564400d0600c1542d1020700c204000c43c0901c0016a03581d005810341420b0041000d104054082680d410780c038400302051045054035030500b070000300348925060508481c007030080440d03401c440001c4c000c40c3c40f801907005801e070302d101542d0040007601d015440c1801c0e20061003801c2d0001c0e00c00101c0d01405003041d040010038040c041d524250400a07600482c2c0c800e00243c00644070104402d25050807410241079001c403604041307014003c1803082e9961200381d202e10742c0019140c501079100c611900060110b1030b55141c2030044101405c04210034085000c044041d43c95071082045103000a00750902108071040102400300c4503240d1505030300024403075007103c0c1202d010540e840c40310304000700040019101d14045444116221400c1d851014502500c10b44500c0c016400d0100030000359130080159032685030300d400c01442c10340c0d40c5d01007405007001001801002c581819412640c3c1d010440c456000d6520a40300d074042965412000212000c0b10750510038140002c1 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 984823480 1250 984822230 984822253
    0x507050c03030703020c210328020d0219030209130507200f07360209060f03330d031106130b0c16080703050904020406031d070605090d23060f07080405 67
    0x80000c0018038180c1140b0503000704032744c40703800126000301c420030f65031035070004000da0b421f0b401c12420462904075150551428140c0c0c008108088000c20705030200c0d0741c8032400710fa069801554500042181407002510044407200f50310390300c88100b42d009409008030030340810000513510a07640000b04661001c0411b000d1403082d0461030541d0600740c3c203440c0d030a01038090f0740d41e90a00244020880010010740303a04040241021804e0a81d044083d4000c1181074030a130000c039441000350012003102c1600d0752400038101940c5440902c01001520301501c4100540300c4981f038500c0082074000c403048213540c1ea6182140b03c8900c11780d1030f9a00f8a00c664050301c40011a102d004244881c802d1624900702120382c0b020800343c7c1c2050f0800c1c0b000c04e0319100e200c0f0445500d0310b15440500c000c0b00040c8049803030174401030414412144e6031805074103606c088000f4441c0c0076400350401c88900048a20f45031500b41180d440300b10903180a401e100440010440140c4078000e00c0740100d81040180c080c50624 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 984824730 1250 984823480 984823501
    0x3140f220606140307081c080c19031a0303030f280e0105060f0f0d0b1807080c190605030106030c110d17010f060c02040507050c03030703020c2103 65
    0x1891403a9090a8240002100240050148400401000100c0d80309182c42c1000c250900015410000955004800c1950060039000c0c6143d40f0404909008095494104542711144564411100314880b4845030040302d982c980d100c036030101c10941888007120a607104040c1c03207200c00e0301d191403c1101180401d10001c0a01c0c01a043c1603841c1c4810980590052195410780f400c049000c0026555407040213200d00340413008095101e030858612040300450000181d4004403410003410b00c1c0340000001e0183e2000804982d1000c803094222602e241e80c4001c560398410200c0c0001e800780000b00007040203001da440f041001c1e80c1d0203845090560b803c2c0f5004500401001c08400c0401c0841500b81c065a102840100d240d6000c1d035581d042101e1609984140940041e4030510401041d036001308001a032049008000503411100841c454891001c2240d06000f0440da0710280e000c000103005480d038040c1e000382289141101941c1000001d11203c0601a1040003081802c541c100000b51150341c0 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 984825980 1250 984824730 984824761
    0x10c0507150b010c050604110a0b070506160e04061415043b04030e01090b031006050714030a0908060a02070305120a110a03060e01141804111e0103140f 67
    0x41c5070850b401415912140d24203031b4287d4003601c40d40c1d0522143e00c200d04103807206401a00a580c0001d140441d181c2c1c4103035407510010004021140d1103801c00359118030503d8039142d010340082c424041b540e100e100c0d240c07007004444001072203104050002081144c6c448244d074100c5241c050700704c0d110b0400c561243d0441c83e280003114080441c0d00c0c00c41043c020700c441080e018034080e03910f0345402020b100025045d65855044008200000d00811a0440c094081001034400da841d0158460041e8503050b028811011003503103140c08046010120607601074000ca003220641801c13240c09490700d03070616040b4465113001034002a0700300560040c064280ca06a900301c5406072001402c9080782e81e890405070040034005001030707282c0e9410402407076080030843c090030880c00405100350420000070282106803002c10100ca08460006081c083e078191124244000a40350940a103980071070b000444c00398a800328040780c40c048070305c1d9000c100c800c0c0c590b11410b215840078aa13500c4a0506030704185 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 984827230 1250 984825980 984826001
    0xf040603020d030c0c030b0403050904050f0f01050f010908030a1110020c070302040b0d050a0311160e0f0705040b04031b0801021c0e1e0106060e061306030b0105041d09010c050715 79
    0x8000c100000051f00c80b002441c800d50003581d5081c0c480800d80100400d03030340c0c0503040300a1090b4040a105c01c88510101c6c860456030210f42c14101e50500c54010f992080b000e612400f1240804500100e419402c0300820182400c81c1007564820009031541e441280242501000d160b40803500500041c00c1c40c0e4041990a500100b17100c0840318a50385640c82c0c1013010100b2400103208a0080f002110100301480001c8500258100c5071820541c007100b40881c0200840d02c007042a90202e240540a4400c88000d00503001400d03540f2034407400c040002030f04a0384c4032000001c0c90b50001881ea403041c420744642c00290024580b0003070300e0141072805481c1203a55000c56000e1203031a243c4280602184104580009001203031540c5041c0018091103400101680920030030044d0040c4500306042030400d452040c04c001804d0341d040e00c0121070038026600070805401000715840710403e25516480cac40741c00d03094001d2010084242c81250640208034004000203100d0424900c1b090b031540000c031809 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 984828480 1250 984827230 984827243
    0x105030d0e270a0b04050108070b120a15120c0b0a0507060b06130f23060f0c01092405010f08070302060306060d1b020c0301050f010510120509010b0f040603020d030c 73
    0x3084080780e070440102050701e6600d0f803560398640703c004c3c506040c01064010302192024100303a0385400a800200c2c89902414008155034100040101c00d460f884040c5801c80c00350060729050319001d410b003031250484005c3d5604041c100c40040c0000064044a082e044180d690a0500b080356136040054003500500580c09030b0305001d01810030049648940040444c4501c1e400d620b40b40c0b034407101049031022000700d030810030355407008855111101110f580e050720a200650b26900c0c00f690030700410701303140000c00301c0c964030511500100d00301c462440a034240500130040740c1d90312004420304141d80d01c18030342541c1100d103040015142c580041c42e40f04d40003601c068580854007440004650441e0410f40010300c0011580d6a4950304102050a00c03805900070010f900707140c9400712500d14144142d074850001982040718240c42103584500b03205a4180501003820101045806048051481ca00408031601c00a10b1841c0c5401090202c903006495664808110b44003160349a00a0fa0140c3d4038 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 984829730 1250 984828480 984828529
    0x2250905010f031502180f1f0203070c05060f0901120e0111070209060316052b03020a0b07020c0108040605090c090405061b070f060213150306090507210b01021006080d080105030d0e 80
    0x64523948900b4851042140c0d02440e941c4c00c5900d01454400c00c5604120b00480f01030114542e000c0d640d1045481d03003442400d00b841c07410022030107080504075411091201d542040b0182d8144210704014001c00c1d0b1088400118036551401450341e0344108040c942ca0702d600104081000b03042401c00d040e00d00d06014112000781403404182e4011510f400002c1300180e10802da400103000405080e04c1c1c00c070240d4405400101c3c94540003e214480c00341000d003020340d9032004034010001c2085040803c0b80050300480061900d424441e803190b0085804100200140c6296041c0c0c0301a03100f11914150700040246040240c1d44039a0005e401a003440c0090304154800460034a0303d802286182c0080d03580c002c0707403060601c20103034103440c0301510708018008a055003014000408045000d07103000c203440040d503151100c004038600b803042071130141058603185012400002c003041d0104200c0e4a074580f11700d141d81e503109040d40e884014001d030000134100c030103100441c901005280c072400389070500b030202d = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 984830980 1250 984829730 984829759
    0x90a0305070e0618090604150209090a050115170f04230d03060b161104110f03090d050a091a12010b030603011b02250905010f031502180f 61
    0x1804075142c018915903a144003c120300307031815881103a14402e0320751402c250750818018150740e40030060002805a12503ca03000008403041d8140d60020f91700600403402800d1828907040100420b00038001d084600c441000c0d8542e0049240800e80f090303000391056903640720340280c00c0758200035004451010b0101600850035601c04101e51741510f1030400340600803c0450060308840b5143e029400354401400151038a0350707845843d41200d030300300d50cc280201c02c0280005006220300c1d211200c0500c0c020401c4402c00000320003a512500c080c030200c13040c4107400a0184d8081c060401580006400d6900501c44601c95901c0745500d0035040d41c040b424030300301382ca40c1c0b4181d9009030010703420000040b0403c0154502402062486503101602e05140b454994000b5240c4a00c5920b140d000d4120202c12aa001200108440200180e00e001c02c403558440c800030001c3d0086201c00c0e506d040b903401d04400c0422040c0700710380243e540117100d40000107403401840034050b0300d40010350740500040d40d4000b = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 984832230 1250 984830980 984830983
    0x622060f050c030f0603191202122703010605060f0705030702030109030305040b0f071e0207090c05040302310e010906140105130911190b0711011b020a0308090a0305 73
    0x9000b020b84450450302d903c0c240a104c0d42d070b10300003401d15110703074404629940c2403030460700082c81c025007248001e101300b1a104003e07403601e56100403502e0f07203c0000403c0711030300c142c0c0607580c044000c0800107614044a02d1040500b602c640d40a50fa80c0a6420850700080c4420b400081a040c1d00c200190ba0401210350006400c441c007500003600802c0e1901700704020000e80c0b0b8145c99000800c25000f00c00303401c10303070001490b6151031460744900407048582d0407841ca000b0841da000415a11b2018407076140d00c1100180144c001e03200c100c0c000d1880c0080245091480d04186400480000103d000040d07105104000340c060303522407840a5595100c074401041160040c2e1507030325405040c9040c10351420041c0701c4056142814a030342940760064000000d55112030766010582c1c2114480130898851800d50060340e01c0b9403000b090080005089000c001d07085c030480e0541d08007602c40c41080220f01105602071440030314001d501400c6007605000003424600500f4000801070940800540c1300c0da10503 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 984833480 1250 984832230 984832241
    0x110f0a12090c030b0603010507020a03030f06080303011d0708010303020d120b0904050d110a020306061905061305090c16030c08130e090f1917190503090c030622060f 73
    0x159840342e0400c03424000d04c00d0b28600709400280a500810592408150094995101c02d000800b01074903800303812144510303500400003030718084c0c050fa40c5d6941d41e002428180c0000e050141142e8002e0350002d088140281504c030b0499400d074010340303000441c181c0704460720b80c9104070403240706a40310785050881c1c0314400c846d80320718400d83c01003200307060351075010b0003a091400440450b641300b0001c9200613100800c50700e03001401614074103020500407004100040c000c0c0c019540010340441c014903444401d06c082002ca8600395030481c800c0d25000c004107091304c03810b070040407950800042640081e00c40e4000b02c120300c1c0a61100340c14804024500e0001c07860580c81b00c01180e00040500150140a01550130758000240041000b1500c00104000b064000d0802611201d00100121410354015080741c0201c82e011403543c1c8010000d0b540604160420394101e803a034800c0e80340951003402c00043c1c2502680e58129641c1c101181c8000b400e101080608085900345e480e0703400400c407101c2c14082c0 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 984834730 1250 984833480 984833483
    0x20102060106080a150303030209010915140702120f07030b010b04121103010f06090e07090e19061401060c121103030621070b0406120b010909020a17161101110f0a1209 74
    0x769650b151000010200225a003101c050408a501c0c80500e480e00001503400032401142d000e515007819000060304450340c2951e0b4680707401804002e400801021450b41c058900c144000e84483c0d881d45400176440c0198025200c41500c0c461504002c143c00441c401c00b0350350010000b10301540d980d0400000d440c0640d00517001c4a0b20742b25101000d100c107000d9007001c0c013003540c1e003080914614000280d4811301c6070001081440301c20605014402c4d0b0381c00c04000707043c031004144255651210010507c0c981e0040581e40041c0e0a80604200e9200d9805c8030340c40e855080c0118150345039001008240c403030750b5803140b0041c0c115a03003103104404203208007802803030070206681c1c81e14500407018105000420440082c13524100544a4580e002004401900c8180c10b005072a1002840242c583c04111038180140e264807a0801034079002136000d07140034204980e80d4200c1000c0c540c262a00f65884410301107a00ca400780089107800002c0800381c80140c0309442c0804c6816003144000080340e104480 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 984835980 1250 984834730 984834737
    0x3050724120b18070f050306030c33071211060f071b061508160905060d05030d0501080c0a0f150504030b0c0a0f0f1b0512040e060a060c020102060106080a150303 71
    0x208120031707400606041c0310704501d040c000c3c61441c10100103a00c0341051405507106010620a8030245926501d92032070240d40703801446040d01c16010040c440390403c602c04c44048d4804106c901c0714a00c0740c05030b02c10200c00d1f04010300040d11030500805010340002c200000b00480c400290800d207140000c88080390703024800004101c200d40102102e2035403140c04c840c4c1d41b54040c4100c1d074840c030400503102c012102e0203040012503407500c1d4002154038089210250440c030000c030b800d8000d40860351045040300d505904440c000512402801030380881e6109414040350f82003010042003500881002541072140380c8031346403684030f40d1034500b00307007068910228429020a0342180035402844400c0e404055040c0103540949000300201603241d50510000e101c507403400c0c810200401000310300f0080c00c25010031515203803611303060409501e003214018880c41c200d0302c001900798042c07514018001c3e01030340944920381c28900d003902d00c8640034007622030003039540307002c66912544901013001961280e80c = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 984837230 1250 984835980 984836029
    0x1021909050f090408030727030809040f1104170f0d18050103090c180e060702161712071b030f0219081b12150103050724120b 56
    0x510004456003400b150080003144144804a0351203000d0ba9404941c03850951000103040d00f85d55044501a41c0080010550440c08803c00840c1400b400042e4801d603400c0104070188038420b0256503001c1c82c042c2c460002000280021107002c10a0405110384608a0320056904606980f5044100d141540011a0358075402d100f10000e02d005030050109283c14000241e10351903441c452015486060a120748031420001c01c208560040050034560300e0684400345800c90010b5121500010b4a520b4294203042c049209055441510750b061110002481c040040c155081403e50001c2c0302035079900c80c2e18441f40300400100d582c21000d14800c8060310748004140c4140090348950300394400c05000701501c140f211200020f1040c062038410080c017030610540c02c006c110750365522040203065004031070000300030504518550f4101c0740705104a0b40d0050703442504905401012844101c3c5420a000c0030107890b21030818890342d414000c8000440c80c00d4070000901503401c01d0340503440b09a051 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 984838480 1250 984837230 984837239
    0x140715020705100b0f0f030f070303020105160c0b04020621070210050a0506010c110a03150c1107031a060a120b040212150109050408132304020a0e090901021909 71
    0x140514001020b00001c144841444100011585461081824001d86c0c1540108520342e40030895001c0e10001c68080e64010350310790600a010b4141141c08218900148082e800c1f12407084080c140c406801c20409800380e1541d0f401c2108a0740240f42c4081c0c50841c42528410580f10600c02074000c0440360028100034035030030710701d800352074004194800c2c0c545000c0c01c0201c5030b43c0021f031051642d5031240c4c1116401e160368000400844e02600082c0a43c03001d9003c0b542c1c0800700c0c2e4840f4200301c9154450640400781c0307411a90b0760f10800c0c04010016113a4041c5040c46440f03003c0b005400080c000c1ca40d052090301c50341214220703100302d05c059425a007104203010540c10244c810380c0848100e6400b0f00410481014122040740301840790703d990700d9443d80004c0c10700040c0b03800c0d1a0b034202c81c010340c1401165610180c140b44044d5040060304000e5042a0480c0b9140606c215004601c940e01c1d0860070010407810003000442c01403001c0040e5400f00402d401d1303c007071072017008440c1d816038441103003581c01c0 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 984839730 1250 984838480 984838483
    0xf020c0a081510170d081e060906011107060309020310020c030a030506040b04020c0c0a052b14010e160b03012301020703231e1504111801060e0906060a140715020705 73
    0xc0c7c41c9010340710000307a010b44203840360100e181c2d0003e4255500b010b02d4440c140101d0b8800101d125001c028002c0c1d40c00403482c00c1e81600301940c000c2c000c408079142e01c08c1010610301280b046881f070940980c010800f8000881c02600529800003008000299020310000854142d074080c07601d041c441e41103045810790615000c0c0c1072602815099949011502d010454004002600c0c5100d81c2d4506010300d54000b0031240c0c5110380c4504003800c00911103185514035a40e40d90340740545006800b800c440b0046802180c82d01528102c0d244c0303424071090720000a41d411b2402002e1040c890440c0920703040031010a07c9440002800344054012100c0c28101c01c510b142000d144640c59010f40102440001d40d845e800120b0095401244600d640c02d03840b14980844400040c602c400c1c2c00443e0704240308001c5481d1600c241c105c84440c0c90758000419071004202081c0011110b450f4070410903c10162140d12a841416038940c01900c4241f5000c01c5444403041044441a24882507400107100e8041060 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 984840980 1250 984839730 984839747
    0x3060501120608030f0d09140d020f03070b0c0c15160e01140a2708061501032c010b21010b1c0204050c190f020c0a081510170d 56
    0x103000410801d02c0d041611a9850780718440300740c013002c00c0205c3d2000405080d6880550304550091504c1250304006175000e4860000721014001350091a681280701e00c0302000b1100150343c04601c011140e505c04914100c0e0f5045244040030502c1001d111110392003810341c030580100e00a0300c0030381e290051014001d110303805207000b180c100080131081a40900021050f2440a541d9047c1120500960715084501261040b03400a80421040d00003921640104080d0f0244996001590350030559800550540f100a080c0c1580d900c1b25082c804119124044d680040281c600008581c1c01c840c0380001c1c10109904840b800710360440e10b034120481d44244900ca10280060f50840044980080e20b0b090691030319030041c1c05240ca8400103001c040c114403c641d000e8130444401075880d194564001c0c00c124100110030050b2085002c000640c4c549030854800320341104c0700800154404104018981c18040c0c6000314403100c3c4c0c400401e91000c0311851451000d2080024500c6510a04004141e9203 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 984842230 1250 984840980 984841007
    0x51e0601030911031929010b16020d0807030801090e0a060c020f1b0a0603060501021c09030209040b090105060f0607110d0206030705130f05060403020607020a2706080f030304170c030a03060501 85
    0x401b00340320202d1100201c605181140c84a0b10103030f84402c103003250382c045544c403140c0c000c2d0720003500c141c50402c20007650003804845001e0b94030301c4041e88c2c940b20319800700c4101c6070000c10310381e100d21844e01c0026015042256008624410b4031100c08168070254035004204400b001c15048101840195052903407c4000804032450180161450500084d444100c0400c07a03c01140800760141c102c203001d4032800c00250750140c82145946407034140131091610940340b1b610b42d5400c100c0415420b10b0052200c0c2c80443c070040100e0319060280d911a24a0745048140f680c10000113074150025a43e102c015611516a070380b1003542c0c94046070146130f002c0304250840d00c1118001b180c20311041d00c5200544092701d50555907280e03140c3c083e00001d45000701950116903000307541c021022144d54200003001d0f503140b40100c00d21200d5200da03c0c01d41c50306441c0d003500d00642d0003880000d0104c1d1854542c50030410380400300a00d0030104400803425544184840d0005c81e403103000800095074400c110341406c4 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 984843480 1250 984842230 984842273
    0x171815011203050d09120309210206070c020312040605030f13050c04020d0209120f070803032401120504080301030c140a15020f100c03051e06010309110319 69
    0x1581400c01600361a107054402404004001c07442c0940501183e010b2601d0396040480305411005489004010745105041141e94003407402c05d686a00300d0750402922622165005800188d68028007140c401e0600241641c1c58440c0ca400c004486080c04000c3c005000f01d560745036500d00e400300143d460f0303c8018214000742e00108600c040031034030101d100c94404804880c00f40e0f64000340230260011713000d043d0009900015140314442d00c042d000403030070983c42c13a45066a03442699450420f0f140c4c003049038000d0140c400d2001d03540031f0800002d28a00d28242c1418851403400c0c03503c0b0b541007240c408071800c5910807800401031080c81440c7c8002c000401079681e4410206440340f01150702d0154901c190100402040e0140300402e0003403014100701c03c3d0500484003a65005050203000e400300141500c0842d20b0600450700300300c001c0306c1c061441d140c06883c030412500d030a00110000c1c45800c505490510030201c4c14240791b5018000701090b41a4400300d400300901754100b22202544500140c00300 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 984844730 1250 984843480 984843523
    0xd0807020114070f0209072a120908060a110f04030f020f150702012f01060306050604050c07081305041811010509130905100c080702010c05130e071718 67
    0x203500a13200120003a4181c0d811442a00da64006641203210000c4111040e025854003109004112001d0071885004140303456500000074410382d501411405681701a801000c0081d549c2c45590f04071304260f01a1108080c80c2c81c1c41044804003507081a00f0480e0b0000b80000810700b5854001c02c90440c41d2002c031400d02200440c04542070742e6100b4078100030305001010a554040d009600900c10b20024203c9040300c0300d001a180300381c02015075020454040c0e10b0440440d406080c5407049038800c0a403c020503240624588032143e40d03411642c0c60b1103070a101d005010581c0e44641c05a5140700f080011503800d820680c0c604408001200c01c622410807609100b200d02c565200c251407500b016240200081c1c0c5480c0d070402a080184011607520094205070291242a600620961260220741d008210030b90405800701c034144101c032030800d51059918400e00c40c00421000300750b048070310340c20b00780c2c0f82d907000078440c0800800031503040401d0040340e0307030840d07900c6018041d0343c084088c102281c488 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 984845980 1250 984844730 984844733
    0x706020d0906080a050618090f0f280c050406170c180a0b0103020d0c111c020703060b0d02100207090b0108011805090a050a050601050a120c061d0d080702011407 71
    0x19820000c051600300d903120001b1428544400c3da01c0030b0f5042d510001c61540f0b00d0729819841e9580702640c1401e80522843c40050424071011860900d50764035622070112124040c510a01c200e942c140c4182d61035040381c20700003050b03030381c41c0329007001404610304240e01c80100320012818040040d200f80c0c025034405002001580d800b07442640d000840c034000160035140303440124001d005041002c00e03c0f516041c0c10000140d0004d00080f104600c54044a1b8100203a180211724852801d601d0800b5901c0013205000041d480e0304109060f02001d070445030745905030b4001900c0c0d06c0988907803401507001013600b409a0b110a00580000d000c2c00c3c2484103195161543c80d1000152050242a0080d521030100711a1902844000101c0703810004480c000a12400c00f2a06e400c820b208151050110480005041c10003030b00c49146203070000400c05050b464450181c03180c41c5000c801007a8446000341078005569070385e42560981d13010f404a16107a10307081c40050301c1c4201d05022070300c9000040c0300030740 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 984847230 1250 984845980 984845987
    0xb010b120138130f06081302040b130c140a020c060d0908030a14011202011211040b07060203011e0f0b0f12011203030b04021303240204080706020d0906 67
    0x341111150340941a806915a0940c281040c1d104000701c1102c0d00c400e000d405955502e00582035004491404001d0241c0e92014000f002c4918414a000f00318028009a00f44501007120240c00780090808a241c60841c00081c02e80d070301c4a49146c49c003030340e00c509248035503520403d07039010a5118200113140c515190406542d404402001070b200302000200c6070184001d40c2c01518401e90b00580d11074070f07410805040805003010408104503030b00a00000151414624940c950407601a101c0b01c100024504105002c0c0031607402d1400c089004000c0058621102d000818800d4040c042c0140c4950401d400f02c110301c00c0d00446954038003100da800784980f50b024a8400d00f00c0d2051681e050740c82c086250019070500510900d00d011083c510300009820350102180501e0074400e58080040788680b01c2040101d0003000b801c07450b40052a8020300000d0801009152140d44640c40d100c0003580d200f54034002d99206130000b40c01038022013010458990100310310800101c0c1c3d81002c500d450304208008 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 984848480 1250 984847230 984847267
    0x50a080d0306080c2d0603010803070b0705030f130204090b1009110406050f0309120403030801060e120606040b03010e011b090e0108190204090b01080d180509040f020117040f0b010b 80
    0xe80705075440000407074250170826003160541a0181950b622581d69078036081e180d403c01c10080d0b908444100010301c41c5845402104d211782d1701452200c0c43c079103d41c604c0444500122104a8206a40d4040b03075010995203000c89104000c505c261595860a00c404642940e0108000f42d441100c03d02c814001d1640082c1036403071500d10010826240e82e2403080da43d2810a94128503051614005004000c5c0355000d5400b82c161508c0f610744454070b0032050240322002100107284403240c0c0161010455a1400d900410b080c1f41000380003081c1185400d880718211108420b5403540316200300c0607044400d4008446200030085c0c05128007a139071400604070345a0104012442083c00300c4400c0504654465121482041c0c100c2100142c40da11654a556520300c0d800803040450300c00f4169020750218038981d4425214040e10070001c0b80c88941d1480303943c001141d000c0f8140304e00d8000441c141011031070464420b90044511840440c514240901c5000047c1c101181041080040040607881501207 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 984849730 1250 984848480 984848509
    0x1017011407053004030e0d030c06020c0c1905091b0a03110403080a031e020c07091815020909070816270801020301030c1725050a080d0306080c 63
    0x20340d030f43e0455640d0741501c42d8040001e803480c00d50070300540303c50400000d0700d1600c140e1080d2550826000f18208200000c0440c13170340140004c022640c0140000e0310707500a485a90101c004455110381d4403000140340003a10301c000d19841d00b0b4810704100610b0505080e54105403071a8140000c1047d807040070565205185880b001d16445150000222003400304440041d50851059525098400c3d4024050088110b6540d145c04860f0110314101c0e08038401c6540c01060310004000072403620701c801c0082d01c180701131058404404042d50020070301a880c0d000034015051b20041c0d942c3d0418042040d0301c0000350064040058040c10091141c240c25501c4109100b0380c1442c1101151a048201e103e03110804080c0024600c06000161400d054015506a910031070340c600307a8684441c514003d03071016100700e000660103403109069200011344515402024103801101c01da8442010440d8560aa80400c0082d80011000c42c201a418407801c8003805e00c010140c2080105000042d111100c013089 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 984850980 1250 984849730 984849737
    0xc0304020109030b07120c0503060f0f0a1802160c080607030605090c03040f08181f0e010f020102040509070f031805121305030a080a02070b0307140d020705061017011407 75
    0x1ca588540210040401188a50742c280042c2c1f00c80031008081d9041a913140c1c0c082e8001d01861207041c60102d2805010316400340c4080fa03030910f090b0358040912851028121031503801c00914811a03003001d06400c9a071f020b8015034a010745802c046a161880c01041c2e01e003058075020b018441a61800b40b1301e6007101030f103102c042c0c9903150703410310200300108460000d15001c0000351500a8903100e0014520720f41e41114000083d40d0301d14403100910540c1e030700b204001070104152800b6507016035603c4c000c04e135451000504060303e900126820f07410030364001c40030407d500b086c0861203605000300040c151440c0e17240010160305688a517a80d54452480700c0022a02081c152a50307000d80c2c0f800d50051400030f01300c87c8c004040f400c0c61011980140301d0714005005c1d044000c03e070400355100301d034041c0f6040e5070741510b20407903c00e4140c072a4020701c80c118911038080080b400420000c0080354094411100351072500c0340344c5054010b0030880303265180042d0741010a400401300d1508110790381f2113170301d04 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 984852230 1250 984850980 984851003
    0x1060c05070b07030216080c032104061b050d020c040506010509130c0c020a030b0108011803080726070905030d030b030c0402070203010b060309011b080402090414161d0c030402010903 81
    0x41d017a414441e510345601e01d040041d03103000542c103800041d01c901030807013501070342d0340020031006012450740b0801c2411100c07001040104401c0740b04401031112068240ea0355480441c991361100d0034084148480c80040e80312030244811442d052090607044202400c10314034065448011a0300d51060501c05084695550001d010f55801000100c1c81954010100401d0940380c0ca04040803074001e0046140341e40c644040a040f200310402041e14103034041d280c004003682c1ea038001b111164001203a4003040500c8060109215840d20000d078040d0a15407a1130a44900344014549005040060354003054180b425401c1c26850106070050302020944004d139444884c2d001181c050300d00e1403070700c50700080700208200c0740c642c0641c003100c030500c4942c200d4103241c290301c070040b03a10400640d4045c4d40280f0086c04603000500742040440301115040039580c000c40d4030b1200c0d0640d040706a114001d014400e030a2014604489040c031640320740320710b8209040d400c0c41c0e00024451100da0100402e0010947d = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 984853480 1250 984852230 984852233
    0x12403051515070507090504020904080d020d0903031a15090f061308030703081e06040e0a140a020102012019050c10020c0c0909030901030c090b130e01060c05070b07 73
    0x1c480c020500a0a4408188400074003032016074402a020b03900760203013850108003500d080c000e07280110b030003e1034009907441e03035110120340d6444408800711f110f50030003004041c403a0700d00400c0304207802174800140d201c00d19151303089058200f004040c0715112560304981446055425944c641506542140800c0409004a10365100301c4140f03560710044200e0016034800004000c01415102c3e0365051a5a15a800580e07800040d8041e20030000b420840003c03031a0030700c1d5000d844104084011071b401900180c80d2680298407540c0810b40c10381101b100d9001355602400744d0100d0005c02204008a0300894105061600612100c0b01520340d06d0410300f190a4460400e0b91000329003442915000602d0030080c4000398031a4504152a0151180d0241d03d850b04161161041c0803080c042d600d446c4608004600504030178040a05000d06440c0208148039080050314103c0c80d0450700701e031298142950701130401c5059018404207e0540b076100c0008102007141000ca50380c4110340750300c81005 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 984854730 1250 984853480 984853501
    0xb0102010c1d0d0615170d09120f1209050102150f07051b010e01020a172a070503070b0406050f160810120c030309050607030504140301021b0307030801240305 70
    0x100034024144c2420182d002070f03880c00c2140c0250031905044101015425000c4c0156151544510f00401252180c40d0400081703c03400c41d820002803003401c10082c180d40590300d100c8941c900a0914001030b40003241484196010007004842403d840201c1c1100c0c03030180261740411800403d034508011010a1031000401083c12000206c654000240b01000803084464000e4018540200004200000e4148411480740d6040c0c09a0b9107617580740c80c90380210000628402e40001d20044d070600c200100404210b0a001808540d4403ea02c0b501060615007480400c0d01d4028042042e41180c240502100100d070781018221607966042c1800c1c150b44412a5446260007139000000c2d0145001c005410042d181c11110180c0b80f180d1920704110341c807401401894000c0d914020b000c2001004103022405400c01a8008242c004001515142468099002d030460003002c0b038506030b00100e0280d0130580c1000c5e84070301405140c10440d040d02c022400079103941c070810b00030304103043d40d071400714045440 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 984855980 1250 984854730 984854749
    0x20d11030307150e100507020d0806060903010207030201050a050c09030312130b0c0703091712092b060f020f03072607020f0c04050702120d021e0901030b0102010c1d 73
    0x1c03c100c030f600008000d1920f90020302807610340791656000343c1c0340c014815940c07442154018052a4010b105d011110b40054490750380c0a454903610680510903240c195909000610480303109500108950402c04000c00507640043c0c001030614000344030000854500109456206070300c8441d1104030344416100040f00f407070600c0054840d600b0788080000c85003a40c2c00801886109540b0360340d200340d03288240440751a011018801540007001d014a00381880310181c0340381c0078000c003030700c403d05000741f0f501450ad02ca00103001e803049064074071541402070500c210080c240c241c420640c41c109290303840c0c444601c0028150414062030002141c0c08040100c6418541d90106000d10424108088041c0d500c410f5a00084518071560039007480504240c01418055040341d0010700050005080c03200c029004001c02011480d400d0126405d07842074440501c20107040040c200303a036002e0110004050310309030002581075a05002041c066982e12070258812000b00140d0030b040496804000b0f000480c = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 984857230 1250 984855980 984855983
    0x10e01080c0903030301060f0e03060402030613081c0903120207021c05010e07260708060417120a1a040c2703150501080606190303050f0c16050f0a03020d11030307 72
    0x400480081845504421049000f1f04c0275150200d1440340c1c0d50400d03070703984d4040b98001d400d80c00544c0420b252603101d5804003204d42c4150b454134140301c0000da20541e980c158201c1d2a43c013584801e44030781410340021400e10003a0403568154030f40b00c0707240c0204090140c140001006440d80d0781611051000070340c40103111044000c203645400340c0e1070110080345400e04040c900c11040031b40800c8550200083c5502c1201d0b0480081c1c04140e0b00c54541100a81642015292182042025920f280301001c80c45114040040c1c1c0050b0902081105480c86801c40d074040e030003035190103130105886802a0582c880348a54016144441003284a241d494214541c00203210010324007480020b0103c41e0011411780b040c0b001100c5440c0e0714401002502590740e400c0f4403441c800f010b02070000c80d224000500d5151140e205088c82c000c0c0340000d043c0741c02007038a03440306620003050060015207080c0780000000c81d000c907000c546070350039500020710603010f0350310080a48818a40911031501e0070310070340ea8400e = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 984858480 1250 984857230 984857233
    0x906040b0c0a020a0b0406080c0706141801050109020f091318060b13020f121e01080a1103011104061107030b0915010b0310030b06122a060405010e01080c0903 70
    0x520700c24101a58420803071400701d00c1601000c0010038130215803030584c0c003128015584c401460301c900900704081c0d4440b501c241c44194540480501101c0f502c3d030820f00a83c454001c0c030502030448456142143c0d0180c02c50f44444d801041682ca1041c80b0000b90303685907408940c07415104410841041c02000348444103220170010301c9014060143c59800001140b60680e8901d01aa061122101c120312504d10a0000200300388401c58442d6005040300b6071080710128141a02a541e0502c588824400d034000c284a42c0320350182c1c010001e000e00c8458400c3c500b90000d00409003c0e03500c0001d14081d5015500c10060107184111070700008100c04002141c0017050755410b420405002a190240c403a240d0b0803810040000260911141048030b2041100200c16903155040d0ba5855105031006400d2030740c015008d410f0b000303030b8400511001c01c0f508070600040f0307568111b0000740703000c07059155900351159005000801141c0d8001c10807600c075020034602491140c2d500300e552201e0703026500c84182c05 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 984859730 1250 984858480 984858487
    0x5011101060932043201020d2406080601030f060b070317011d010512010e1c030b0a03081812030706061d040c0b0a11190c0b0f030c0906040b 62
    0x280450b1402c40704801c0da000c1d1060305102050f1242a100080030f031401041c61411215031040d0070003910443c2c0e8030700100e100c1851300400b030301c02ca1400d981065680c108884e6403910020701098081d002c036098441e0709894005150714019015180c100001c0c40c81e0705158540710115521703420703580010050100300b4200d5803200b071241002041c04c0c540403440c410000360480046001c00f17910b80088241c650a00926416a0804051210283e01c40801c49102d41d06c03144250b03140b81c03081c448020020015190a1541d061a0b0001030664002c07111090103914400014804100b80720304079140c0c0114028101a41c40c1450007041503c0d004101810550001142080800149810000844864400704074000801d114005d4440e0b6090300e00800009030348508000c2c915291001e80450f81550405541031500060200e04000c0c80304c20a80009112043c81c10802c00d5144111001e0103d4440141c1030484101503a40d0900c00508180c28002d0701042584840e5500f5040b40c010342011100d0702d44 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 984860980 1250 984859730 984859751
    0x30f03090512240c091c1a0c0723061306180f0609020f090106020a1505060f04050403090b0409091401020a020a2012010b121b0f0a120f0308060406030c050111010609 73
    0x10441000204482001d0461100c3c07c10200c03400c80306015401c5d4602680c0b41000503550042c10030a540554603900422903140821400140001485486a0103c03a590b8061601c1c000301118095107101d880c8860214011000c03c1d2203070114262594041c40018803a60f9500005801e4003072502c3c51503000c000303403001080b81039010a8001d00c1c184035113280b206600910060b4010303500201c41c5203400210401da903c4d170b1890280c2000341c119000e41400040c2c2522200103c102d0b50194000e8020145c8075031030201045080c0a05000d00c0404000843c20000910002500d0f41944800940801400a0b8210004076003903521a001c1400521080701e03503000c1103c0c240a0605410713054414800b0b8055552041070124290400d0f00d21401001c44404c0d0160400c6254101d040c0341c1e0703030400c1c000c400c041015010740c07c0c0303203e025004102d000c3c007513400361070300500e0841c0003010709001c0c0342050020400200700510f80811f0768000d080c460003044070355034024010042c0d58081000c150600d0807008 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 984862230 1250 984860980 984861019
    0x40609052b0326151003141f0e060105190908100c020c10021c1e020102030405071a0304030c060902030601060917030408031204020a030f03090512240c09 68
    0x1541c456907034181c100f841d0044100c0000c0c1d800720344450500030311000c6280e141c44d04000322a07100c5460b04001031038107009108803038a010704039000003c130003011811020034115001008010214080480528900354000801a0003140240400c1040210491004d140100915405081d5950880c0c1e0085040004003000d005540320180c0980100c4094100398141024411820381c00b81d002403a5802c8109280c0d5a0480d15026075000c0002410030b00344141104010158086102c0e0b001588a041c079040403800c3c4443c03075000001030b44104a00c49005206001501d6200341c00d814040029601418610080c04105100035450f0154000100300f481d0450024020380d00c0490700a440501c0402d55996244150b0243c1c0e020303a803060012102103810f40c0782040e400743c8082c21101109641ea956150b1400300420b0460200b00c000d202800706003018503522350303c08070f510300804405070a0b0110b10280102800020540e03554540040c105113002c808440c2c194102a01e803052040c00303490190f = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 984863480 1250 984862230 984862247
    0x15080a0f290a230403050903070e040c061e09050108070302070b042f0d0f03020f0703060212160806011206051302190f1b0c030803070e0a0b040609052b03 68
    0x4185285003110f043e80c40c4a01031000da034480030200100e8815103840c1c60a42d8960041c106e0523605100c5c40c8000f080c0110000003040c059445110b00d90340071404c20700041e10108500c2c1441400d4001c0340ca440a80c0c645c88a140c0084a40030f0a1a071115200c0c1d6070110060710802c41c0162040200c00d05010801004205107040404134042e264501c020b90140e040c001200c1c03c2840e940180d445071514041200c4803060901244240103c0d0b40f0f4a000d19001e07810400540d20a8546542c0814131001c0640d600307820983c44496502190443c0444003009010302e40b020701402e04103d2440010718a03a005503103c0d001038a0300411703c00907039200b5000d00c800b962049190720075000300382c410010f03058001c816601c0055070b00d4490566a501c1440ca0124004401e00250782030400d444000010030789050085020304103969a401071820f03c10140318480700ca0307900140b070041d410030040140c25488281c01d02520000c4503a580c400801020101d041d004901201d462101d01c240808101074001802 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 984864730 1250 984863480 984863491
    0x10e06030a050a060e04051c14041e03021504080601080d1e030b040e010e011103040b070f03090605010f08061b0913020c0304080106030b09060702060a02071a0106020d0315080a0f29 80
    0x1d00c0c0b08c0703010a0403240b1007990b40842101031001e2000380901901606e04103028402e1034940007019590ba00050041c2d0044d03420703001c000c640001d0600c4606d46c01d004150141071410700074000b007596800010085403840383c41001ca20303040c8100480640c841d0700f003092320300b0004005110b80c1500c00e0003d402000b021804841941ca0000d079070b201c41c100c140c1524411178006d44008801d54031044107855018910030140c0816035111105000a90305100d142c0c040c0551420020480d41090703140c62903c0c0b00608040d400303041c120235106032400010101c504400054601c1c50175006403041210281c050070159804c00d0001280100b80070304150b20503c1101c1c001c9d10780031b010b030b21440c01060f02c030030703041d5224130040c0c22400c00221707813a40e00e40080141038801c0d51060200d2074079100314201d6820030303004000160028224001c096505001d040c81e180c4603d10b500391a03c5c40c01003000d50700d01c072204000745404250100582440200d0302d6840250200541c41101002c2c441c05141040508942 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 984865980 1250 984864730 984864763
    0x30318120d11070f0305030405010c05120c031e120615070f110405010b180105090a0b1b06150901030f080f0c01060f06170f18030d0b040605010e06030a050a060e0405 73
    0x2000142d02c4041c4d52458200e0f03400502651500d400e20004642c0c0b8900d842003a00c16210f00b400c100002c031410310042900b15160300c06143c0701d40800b00181c2c0b0b600049008459014018099546900a40010345401100803140c0105070304240c40d403010140074041000d8801041c0701c85050a2240d00401101d480c60100d404000d03da0b02c4038580015400341c4810280c0449801e480100341d54014802002c54020040c802d8070900c1e510107540100e5841403c0760910b1000d002d8250b10004010030005400102401f10090700d170185201064007500141700150a9440c5c1c92441014802c5c0d04007261101c0e121709440e182e03600140c40000340600a01d108138032072281c8131680068600d204401100030074a108400c030101d40c5500c030141617240809442c55900000b1100c0b000d81d080300401c000c10004211003000f10380b284240c01000100da885501003814880504007141465030f81004a90303001240040001d516181d2600301001407440745c00032405045190184014460001030380070201c075a100 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 984867230 1250 984865980 984865993
    0x1e030304060b061e0d0f0903110c120c0f040207060603121101140a1a04020310030c0902030405060103030f18270b0f21011d07090506030318120d11 65
    0x400340281c5114a0f001c40c030a40d00844001d0b84c0d100449801004903400030340d00490010b104c5030503401211700707990045000c00c440340c80c00c0f1202681440080b0401d103044070b00b1a0315071082e50300107031a4803058801d5885170441d4081010550749681c1902c070303210341241c4200251600c1c2d1a00c003156000c440041c0300030030300010805000d14014041d0340900740703103d030102d0403036220120518060301c980540c0185e203607039020201e0307807a0f100e502c041c5100c1c2c00783c0344040d02c1c1103155007024420300700c0541081d06c4803801001008086500000c945045035814030342003644840790f0608848014000b805d04451025400e000168100000c0402c420265041c041c42a12407080c1d107481e080311304180380c030340d081a20781d4400100d900c1e00305e0340b007188601c08562000c542c0d40820181e9003112114004c0d1103c8611401c6200614002049140b02500b070303c0504010038107003100082c1d5a030141c020556006441c50511014035150300d009100b250105c00216011000140c030081d0044c404664620013521500303 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 984868480 1250 984867230 984867251
    0x150409020c060121030c030c0f0b070e010c0b06090c0403050102070602311a0f0c0708010e060403020703150e01020705060a0b0d08190207150306030c090c05090906031e03030406 78
    0x11030394500501304003400008000d50303501a01c0c001440b9030103400703114110b45200e010034480b82d843d01400e88035910300f80c131714175020801400392038240c46620704000409d2081c0d400100003000d0260046000c030742d8201150744a02180c00300d4031807a00020900d50010030404100803458000d0705208031020b8040500a84074041002c10a060030002e048009140700c04105401f0b50119105c09521102c500d540b42c44d10608002c4001c2d48020400310159225110821401900b0f200c0c11005040d403401500c0f03181000c1d00d000f95036680714000509210758003195164007418550084107040d080d034000b552100040d0500c1c548070582201c21070219030a100e0604c016140200c0295405603100c400c25080010000122a204907151315600540c480c1ca00c0100c0c2c03038070b0301c2009402400490382c0d012641303e0952412110513440d551040700d405007071030340441115805c00187c80c4420b9054800b40556610080003918010b620b0304c1044403d0704082c19244034000120046100301c0c000c031003d00801d03060 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 984869730 1250 984868480 984868499
    0x8101406010c3309051b04111909030c03030c0b0c031b090f09010b0a090902130501030e0a021005070b0c07080a0f02120a0c03030b19060c02150409020c0601 69
    0x452002401d80a03100100d2030440000f00401a203400c501400441c01a4a540030508440c00307100140c885074401c2032641003000708000005c42c4030100390f9050040c481e980301d264150307000d0045203202d26050350b80e00e103d14500c1803590070011500580032030b01d002c2e501c0c1030141c038607102c90000b41c03520203900001803480c9800c602200c1c010140141c1c03544807241120820022600f00d4600160f004500b0309854901c0c1d41c0300c0c41c0070f070702031705031401215601c10701d508004e860004203071b1140b2441801845252058006820342e00101e400a00300810840c0c110603c090402d404510000e52140f540c41211a0840e4000c01400d19503100f060a1002c5031a290054015030042c124000c1903000104900c0980612909550001200d240100c0700e140903402800f405d50f0304880740780c400164580880205155060280361501d00090743c02c3d50b240400c0012410007202c05009140a010a1b50101c00841d207400300e156030240703100700d0000d803196115034142000c2d49c084a1803010500c103e00010450105 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 984870980 1250 984869730 984869747
    0x1f030b07110a0816020f0a03240c020a03052206030507032304170f0409020a1d0102060703110c070f05150a0512060a030203030a0206010e090a03021509070810140601 73
    0x200004002d003804551075188038010400c0104a0b08041a1520102151079181b618000303140b2511084040a1101207912040820030001002c214240481c3c682c0190300410889005c07605493b105945200b074501d0030b24210110083c84803500c14204000031060380c16072000f802950b040d80c0c148814030800300c010010000d0b00c40344010151070385001c14001441309039000172402d000d81e2141d0034104050b01048142d006036020140c80758001079a2101903078800489408451280d94056a030844a00002d50b1504000c14590034542e0b154044441200040240e0b6000c1c00102c0c02c4900700d507214000702000c04480e1160601521031604070791407031070041065030384480300c3d9030340c090515200f440d10044a9101401c042d80100c0c00c0040440940c8050004210700e0840b40c0042186524018000031711840040c42260250003070141240025808900c29440c2c10281000a40d1911014102d605014050b03104000c04e22581c1028111403d2507006603800c46207100c0050b103c0d6a4041c015030780c119 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 984872230 1250 984870980 984870983
    0x1140a020408060c0a030b1009030c0b1612020c0d050c1807050a03020904060302062808090a030c0c150801080d0905150307140c0703050c0d08030f1f030b07110a 71
    0x20001400030301c504108002801405d4841d1a0104800641c0300106030080c0c0c101012a00141e5200760a000f4020641400001401d2000d8003a1070b19490262003c0c4003c2c19406c01071004982c0078034018024070801035940344040003400b0f010381c440300e45003190703a03100e540c5102e500400d4a8150001e004ac02000114031850403a01d940d45004c40000086009500000400d41d2050b51040048051703200c0402525008990300403c29a100944400045258601501c0b03010405007a082040703296020030306444c4550715081c0080f4403886483c0041803451030f038101000125460f1100e245803540008980e040b100450159004441100011540a1418003c01c0e402250440c0681640e0513903d004603405a424034100115251038581340056601904003941c81d5448201c040c4207102041c09081096a001c80f2005134400040c1e41c1d00c08075010041104020700d901c81d00195081d810101c408094010b115201840181c8a103401c402b0780c2019903400c80054034520000070184800102031f000709 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 984873480 1250 984872230 984872233
    0x150e0d060617100f061401081b040b0a120606021b0a0b0307050703120507210e06150111060f06210f070e0106170a0b130e01020c0c0121110f070501140a020408 70
    0x781e0346c18019035544801600742092003c0c080c2d030491840790a0b9000d4405040701031b040941d2140c58080c020040c0402408280c030719441d003901040a90340020302911101c03040d072030250f6841d0042e000240040415030208140850000c2044400c079401402004c2040c481e407925011425442e020600301e0b082194003001180080c0c0811103c4006000c001003121611040803c05030244c588060030300b0802e8034600140b2504400d50030040da0011640208031035410020041403410018850070808060800ba000310151540c81d10020380c000c00041c0c00844010407103e407003540300091941c98050f482030341103d49118002080c2e1030712400540640711030790321101100303403101303196440200408401c055001d4590309000ca4100c2c40390042c8d095210f02c1000042c0c840644840e003d0428a0112450381081240394100302440300c01001825a03404140340050120001c451226603440340d540700100080780802d08104210b01504204da500d25405000c3c41640c540440c04401e0307004500900905 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 984874730 1250 984873480 984873509
    0x52a090a0b1c020f0d1e0507020f07030807030519050408011103040f141f05090106151403061c060b030d020c0109030308060a09020f0310150e0d060617100f06 70
    0x400080703401802d0813090840c0c605103002c3c046194503040320742e8840e15549610039051404504201c91103016445903840c0090105034102403040d98551085000040c941d40001c01c001e028548204140c0300700690b0410580446908408041d0443d040391280f020603609148042c0c95101601d01607900595200c980a21411441d6496101060500003d041e2070301c1084050740e108407a021042d2000001c10100092509003011483c0c05e44a29400c510300742d05d1100403a00c0301d6584044141c0f03000d059058070750b0712a2074000004804c407080c1d0b240385502c40d143d51105000c3c040c2c0c42c0e115403a80f0302d00b1022580ba0b41400101a615002040665070200e04400420400b1034020340c1c429500000090801030219228003482040b40c200c2c04d80182800404410061a1031226031040058507407681103004641402e203000f0522454601400d014101500d2072108100c51a000314014080c94070020340c8040314011300959030381043d500d2080300c900302a2820448101c034860030081d102c181548610 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 984875980 1250 984874730 984874777
    0xf020c074115030a0e060f060f060a050d020f0d0e0705060301150201060b031312020312011710090b15010c080703080910180b06030f0c04052a090a0b 66
    0x80440c4140d01c4207030481948541504500d506000540c400c400c0707100700107511546128403501d4510000d015030107403030300b070810b20040c2d5480320f0882c01104d20444089940305075082c0220303501e01820103008403607800803c05890282140001d0710f04440041810017911a0700340710103a41d00c0d1a0b10030359030446000c00040c4002102d80b251a00d0100c00790001091742991810510250740c400c030b55040410845c41c0341d12007007182c40c001c1003812003282c0c8010341c00c04d6000076000c0c50140b01071290340c6100c10407104083c841441807140048a00d010081040b48803100c3c1040304407800211000c0030990fa030140d0800c0306600031040650855001102141003249030f540aa8040c2c0c0302411034119403103030608200013056a40140c0032400c40010032409903c54030f240c100180c00001d0000d6210303822800380c2c0a060707040020401100c030380486000c03815440d4020040100700703401d000c800d40340c05100d040843c0c04411100921070240181d4400c1412542c5914080d400c1c010f48414081c4900307803d50300c11 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 984877230 1250 984875980 984876089
    0x3020303041203021c0e0c061803070806012102010c080307020618120d0c090b040f0504110903031615111b0106030818210105060415060e060d0f020c07 67
    0x1b240c0c080c10804803040c0a0a0301d0002d40f0b0f070340100c645901c3d00034182e10b40050902301031002e400280000300003002e003941001d98010400802d0300070704500d826804035100c15607206903032032108281c10080c41640c0b0700b03000c0b1300251981e0003102c3d40410019490b01c6070301c1d1044005248001002d0f801c05050030117082020600141a80c4001d60041001d8100d011070044540c2c4000c0c4004c03c8990b510008a918120a010503034852082482e8101014000e404460702e010046840102602050344584282031034241c0b03020000115080d01c080c50316a03000f059411000050080800b0306098813100d40c0c07698407045c241c52503404000c0c2a0401481040c00c0c801740401d446144600082907030942010b482c000005c04a00e40100316401c1c0c1d100c0d03041c132400b4203040c4540701c200f860800302c041c80b950412401038822290352001c1c034000c080004429180c10003d03407042c001608052410b65031041d41d0384000340d44100d58020364483d00440540c0d0080e1098580c02e005801c44642e04190a0324035400560 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 984878480 1250 984877230 984877241
    0x40b030103062a141b0106080706030e0a0b06060a2003041a16171e030121171e03090c130e060712021e220f0b0a180303020303041203021c 61
    0xb1703480c6144c151030001c0c06003030038042e171006040c00f800201002c9140250044c20b030744044002000c1500801c45040209103800c824030b50148040d1107035652115190802c86001c5201240c4000c0e1030481082c80305e00c1c007004030003041141e00740602544200c901480040441c4107011580c101000100624000110118042e0200c3c1004100550420700764109050380481c550039031811812001005100b00002c4c140b1103103040c4c000b08441034049c05a5a90546075008408034008000400310f20009081c40341c1800d00941d160f0b02c8411612820201c9d62195136109144220b0310544105840091192543c440c6178015081075004000a840318401900e1b504261424042260340030010f294913400d01c000100d801c600c52890069071982010340c804041c0224415003481e1103001201001740050200b148019111000d81182d82c40800d881d081d101c401210140080c50a8210400028190003001852045025101d42228041901c030202c0c200e2003001241d24510440b2200086c40a4150780017 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 984879730 1250 984878480 984878497
    0xb090411030a0b0a140f04020f01030513021801170f06060d020d0210210209010507060c200a05011404031b08041e0f0506040819020303040b030103062a14 68
    0x588403841d000f52941c581c1002c08840750b0074415213500b00349191860311500540c0c0301a041c0046403090820f5800201c4044000e080c00d8101500c41c4045003482c46415034580050354000c084400c003120791811283e22030001d1003404204007200c910301c0341c01400030030b040c0054111003028115a60f540401c10184c82030554040e41c0008c0a03580c1103005031500c02616650040076150394580300c8001141c0c1c0c1c91395500706c039101101c0d030040c0315402071079801005480c0d01550000010903200105182114907500400e051250094614940740031081c001c11680c003141c0c041c100034002501c00c032140700d040d41000d6a0060004440100c08800040da407a66611560300c145581c41c6840d1351900e00f40f42802000c01c444e10441c20044d42003000501c40c28100c0b00504080e14041e00306403410000b262901d440382c100a0720610480198403c46d034091040780c0160140400d5076880703584a0038610010a6400810301402e00ba00081e0341c03079191090304804001a43c0c0d40c4d84020504000a080c43c40c1d0041d454 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 984880980 1250 984879730 984879733
    0x207061b060b060d05060a0609060207090e01020918090d0302041508061f030c110d020c06030703020706020a090920031918050606090f07020d0f05090d110f03010b09041103 76
    0x2c122503280d55a41c028249000d00c900045550b0030701c0010404c074030405510210500c55000400c00400350042420404c85043c5e02c0001a800c0d80d41c10304030f01a100e210300095012860410001410303071000c3d8080d00481d2807900f200e282400418042d001c0b403046d1300401c03100c0a0851400b0301c0c0c0910030561a648180041e01180e40301100c569642c41c80c0040782e402c000481d40700c0582d035050b16413001c1c0d4400540800c0c03008001c85400418044d40328101458035901641000002814980c0203404903400c080d4000c00c1190380318210b1200030b1111089010b2072011b50b050490046402c003190700d0552148005d00303491803071174a4411800085080d80880350300303200e8403104e800c07280d600c588a00c1118107000c2c0002c0c0190b450004100860820018180b0036420303104010b0006845d400600c801600da1036040201e48800010000c0c0c90b81c0c01445110340d4803c8c0c0c0780800d101040f80c441018808070ba0150bc10303241014000e010542600c103c0d40540360003034220300011b03000c900c10713002c0301c84244d50280 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 984882230 1250 984880980 984880991
    0x21006050d120e0d05101112070e010512040c17031e0d090203010f020a0f0207150804031119170708030c090f1503090c0109050f0405091c0e0f010207061b06 69
    0xc514001c2e01307407006959a420685040782c44c07194034021030101c2e06208964516060080904200d03420000e0300400400021070804c030207590044080700e1416035085800c8100f031802e446c00c0f80c82c0d40514050500090340e0031500034007103500042910400a14034220101100400c401c8101c103400c228082482c05444100325005618203101c1c480380020604405641c1d54a654009800b00030001e19070b108650200704208043c0c1e40303a44415130585000c0ca0030400d192260b0a00b11400c005001e01500240940001060000d00104081d01036603c14036001a0711001c0f81d4040096010300d1102810498003007001403114100b58000b060a210010000102111101c0125280b8a150f5850755800d007800030600c000342c2c108100700205003c3c2480c04d0680141044c0208103075449211101d801581c40b440882d030100c1c0144032511a007442d489150078186082400200746011189000740170344040c50086403194400b0845809444113a210011107071000b8201d41011012128241e03445562107 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 984883480 1250 984882230 984882257
    0x51506040b0733090501110c010507080106050a090501030f1d1e0a0f0b0402030703060c0513080303060a2102030709090203010506030604020108151c030c03021006050d12 75
    0x114054000341c41a1140d0544641c0340d407038003c0d80c5207000b06000ea4202d14640c0ca181d600380031020500003038100010042500011850054054081c14810104054021900080704541540050b00c60b180ca5691000d050341c0e9208103494501c0340001c400005030700c8460a1000b940a600007074074102280000050f2151080c05842403140d000c00c40525a80007500010208445802407031034044200c0c0c00b504039581980d85540c1c1490881c00b000708114003030000a82035680601842c00119005041880766018000d001465a880744c401d5407142000c40d10003080c4600c000051364403580003d440300d41e40b541482d40514100100b00d14010000709101c4040c1c0058409012286c0242440c11000c01c9844040c4101802e4440041405000364458000c000140c1ea0010486801481051191480140000201c1c0070180d000041c000025081006071041581c0b000c000b600840c025400c1c1d95011041d00c05c1c10b420740d1540d05c0303500d90111004c8541d0011810600151103400c0c02d44c2880440c20303640 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 984884730 1250 984883480 984883489
    0x6091a1302060d1812020d093615060305221205030c040f0602030307030c0f020606010e0307031e050601080601140618041505041506080a050a02090303030f10060e0d060515 76
    0x5c00c90038401a080030710f42210250700260190081c00d031500074940404a1420342950100e01c520003004401036040c104968108280e20100082d80b00d007034130811007516000040e028100540380300c0d85d96a46001001d1003464000880e040c0c160b4001c0c3c0000c030a8949100486041d0005400c00781810020000000c0d85810030007280003c00c03c5c2d4000d16280d2401d148064100c44544561005104107040c50000d0140e0120b82140e000009007440131650045c800820701e4000c131900002e1030bc45041006504010b00c82e245040c3c2c00303101e0400c88100d81c0e2a110100d44580b000c0c0b24048109138620085030403450800041c1941d00112422b803603191600c0300016044c2d0b0295805400d50403406c0030700340240c1c00d160103801c1c89042088480214a4580b200082180c3e03c000c009919007580c0300081158001c07140c04540110f080201141d890b8100350595658018065400b504504810040010f00c80d003d00c601c40c0207000010300380400320b40b8a880d80320103408001d0050320042031030200e18915648 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 984885980 1250 984884730 984884753
    0x3030b0913031701080c010c0302120f0403060b03150c0c210a09090c09060e030102130608100909030509010516050610180e0c150706091a1302060d18 66
    0x24040c03032110a041d410050924030f8111001020103c4440041c02080d4000820301031228003843c1c01c0c207903540c1e1410708074205444c041c86012614400207a49034100320100151040d2401030300100040c4241e00101965600c09150300ca000d80d44800028072885590030103000c2d001180410364141002611480c0710110607000d8030726507040c0c041108140c0760741c0400140082c0c8a50142008001200309014085038041c2c8160020002c0e42d04035071025807000e405651032480c00e9560703200b14036152031001e800d050085400110449085a00148030b903040d0060010303c03505900d8642c500002003004642d9680030110000c2c1d10741c20303202101c0c00100c0810a541c410340840c2e0a17064503070700f4400303039101000000401082a0b400c2610401c9107a50110710050500740031101c90146090b800480360280c080c0340301c00f401d0b051400201c00248001e6003e45201844900d840c51465502c50900c2060352568000c00b0390440028828960f9003d02c55112050413801030350140711010955503561400407 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 984887230 1250 984885980 984885991
    0x80607050d1b050a08130b16200604031107050f0402090d12021006120506060405040c09021c06061817030c19060b0603090616210504170f04050d03030b09 68
    0x11400104a01001e82c4005c01e642c03c20034103032070403e8024594403000b456110103887c11908030740440c00d485155000c0c2821181010a020302586050504c952154507000100d0f001c1d03000c00d4101407419404440420481c1c03e03580010940031064140600b03000c0250000348505420202c5a80c01001040c04912813070010081c65008104ca17a5400308400b01b651040d0f800030440c17024541c208400510003040696100340c091314001031682c0c0e107040000716140c1d180d0200702c04a20001e9944281c9540c10f03200d0120f007400032818480c10395544421110894210103502d030702080103009120200c205078543c1d140e48040340c104c03420005048501ca0030a000d03807025a03991051044500200305150080740340061085509900718584540c0700d81c0c44e900c004018031300c1c00c904c1c0c01300718120038015a49641c5010021550312a000e0329074040c2d5009103015601902c181302012a1000016007900495104c14203420503070342002d00d840d06103c0e00300644c0d8003c5051645800130269640c8409450728840c2 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 984888480 1250 984887230 984887237
    0x204050418060b0d0302120d180503030403390302070510082406071121011e02090a060c0c030212060f150607120c1b090f0204080607050d1b 62
    0x461051802d04125100202c160b405180a0003111001c01d80108509841c10b0345110f40c0f99031b60001004000c002c10600701c0c21011503510007103000511038000043d40c1705a1184e2a240d203a0303c0b01c0f000d0184a0700c46c1c10038140820240a40501c144044501c002c850680300380120b035460b036114000248443c010840fa9030016021004001c1c0d840f0391902d100907012501d4411104503094840855004d20488801600130760480c01000c032a622002401d0410000504420008030107000999000e010410400c0c2c000781b96402115421480c207200300e070558800240003984003403416a0586211400e2303c8107480a9508070b10000160b1100a03400700815044005094036251109296140c04000303402d81070181c5a6607200e51203601c1d0f030710031541e4140c1c11102460303c201305001e003150100e00c40440105070314178000440000c100c01140f03d03401e44409030800c0c0705125100403200d04901a501c90b01d001a40440045050280240b000381640c65500002040005156039054405030001032082d002 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 984889730 1250 984888480 984888521
    0xb09121009020109090b030601060810030210030f1a0f0111100c02070608100e0406050c0c0f0c03121c05092a04050c19031d0f011a12070905040602040504 68
    0xb10740c0e00c22000c101600c0ca000c010400c901070100030956620050241c001406040300c08140059105400a4000c43e40140401f080c07000c41000200a499650440c152480c20491203407812003020b0000800310f4000352015040c1c41040004541d42d1030800880c45540c02440d100030046001401804030070000e40e001000b0b0549000c80c010400b0000034950f0302e9889294905000a0707001e800417507001a0031440208103600e078400c4409481c0302d105130780007062250305a02d4021030400b00b1200b141110450940e080300315503070300443c81e91049a0b5410300301c241d20141114040140d0740110303001078103007045032a01d01035006180d42c581c00a40080c6100c2109014400c0c0514103401403680c0400020201c03402d1001d104041c102e200000f84000c400d1540715011400c400840c0450f031030000c041130b411940c405995440c0340d4001c140315844945c80d80d04a2030042014201041c11543c6000100f00402c1500d03e00f0110a0052402400840e1804d8080000049aa07194000c1f00c54a404008a0030f40 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 984890980 1250 984889730 984889733
    0x20906040c170c210412090e190b0d0c140102030427090506010f140604030203030d0b03030d140a060b1c11040e04060c020d0e0d080d0905010e0a140304050a0b09121009 74
    0x41040000d00c5402000081e00b001d1083c0f9414803222600240017083e640503500740802120003030501c074030740074be0010142d1040d6418800740e41c0c0302e002100c0680f03a0142c0b000310381d0801262248a140207240d885102c80701c0400010411a4001d81c2c01c001c8900700082d02001942d03001e0410374203a000815118500310207008a200341d01c03983c03d5060044594502e0b2a01c1c40d80403d441e4029940304003203031691440d0413000c41c1c80a1048074101e410f03d0304204285602c0c5588981510300c2916040440e034581031021686034003040845112851151158410400700b0301003901401c11050381c0c103c03010043c031002a1300b0f0704048030341740070b14411030b00072070300701c00c9000700900c0d2082010030304017003080c002c1c080d45d8079451305100c40103042d40006140340d98400a80b81400940011b0f403005150b5880c20b8904001c102c800301d55042c0d400d2198094040070340100d00204d550f0302541c019590b000d03581080070044c01d0401001040a07500207003048850000200381304d410a4100c09101590584401c100350 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 984892086 1106 984890980 984890993
    0x1d1009020417060604060b09130e030a03060302090f100b0d02070c060203030f0c0309030d09031e031b080c0307180b0a0c020906040c170c2104 63
    0x103555650354405070741c800c034800c80409080c2c01000042103c4e40b8007406101c04036070603c200c4d64280b22000f000c001200510686850040d50748008000002d4014400f0344600307101034400041c12407943c01031181060004045200c044115010030607000c1109000b803042e10f4030b400c86141c4072010100024020300c1102006420700c1c400b100d0015040b030740000150302c503441049048059032108140d1061501050f100e40a480d002804001060b04103a844000d800780a8580303550f85a17480300300c040c2407140005810001945407620703401c0d081c240040500072440c152409140e10311b8801d4030241da0b0300018003a00100190001d8410544400c60450b801604100714515580c21103600042c02d42d00500d80d0490040c0c441c08001001840c00f0300c1205040070403604e54a0303503800a140000c03103000004100407a855000e0041582e40d0300c10307000c2036114088045400c840ca04081c140107 = true := by decide +kernel

theorem cover : BRFrame.Cov 984712230 984892086 := by
  have h0 := BRFrame.cov_init 984712230
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984712230 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984712230 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984712230 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984712230 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984712230 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984712230 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984712230 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984712230 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984712230 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984712230 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984712230 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984712230 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984712230 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984712230 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984712230 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984712230 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984712230 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984712230 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984712230 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984712230 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984712230 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984712230 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984712230 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984712230 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984712230 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984712230 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984712230 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984712230 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984712230 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984712230 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984712230 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984712230 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984712230 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984712230 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984712230 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984712230 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984712230 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984712230 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984712230 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984712230 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984712230 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984712230 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984712230 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984712230 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984712230 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984712230 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984712230 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984712230 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984712230 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984712230 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984712230 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984712230 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984712230 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984712230 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984712230 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984712230 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984712230 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984712230 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984712230 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984712230 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984712230 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984712230 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984712230 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984712230 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984712230 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984712230 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984712230 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984712230 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984712230 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984712230 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984712230 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984712230 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984712230 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984712230 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984712230 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984712230 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984712230 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984712230 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984712230 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984712230 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984712230 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984712230 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984712230 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984712230 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984712230 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984712230 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984712230 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984712230 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984712230 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984712230 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984712230 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984712230 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984712230 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984712230 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984712230 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984712230 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984712230 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984712230 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984712230 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984712230 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984712230 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984712230 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984712230 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984712230 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984712230 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984712230 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984712230 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984712230 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984712230 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984712230 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984712230 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984712230 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984712230 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984712230 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984712230 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984712230 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984712230 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984712230 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984712230 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984712230 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984712230 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984712230 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984712230 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984712230 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984712230 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984712230 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984712230 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984712230 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984712230 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984712230 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984712230 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984712230 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984712230 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984712230 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984712230 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984712230 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984712230 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984712230 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984712230 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984712230 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984712230 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984712230 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984712230 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984712230 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 984712230 ≤ n) (h2 : n < 984892086) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
