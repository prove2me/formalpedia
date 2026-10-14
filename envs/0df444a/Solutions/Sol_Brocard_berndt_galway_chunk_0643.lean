-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0643
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T20:54:23.46478+00:00
-- url     : https://prove2.me/submissions/246bd7fc-d118-4c09-afcb-b98949b485fc

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 115467625 ≤ n < 115647482 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 115468875 1250 115467625 115467629
    0x20709051e1f051203030a0c0c03080c03090304090f05040506060418020603180d08040c0501180b071104050106020307020f04140f0c090a0b0406031a0108011e0e01260601 75
    0x480d08100000564400e00b504140c0c1c520012071000c8aa80b58603036000405140d000c010090003a4408010031a50002c5c074018221030425609103440c0c818010344004140c050001e084060390400007010550480c000c000710b41c002c2c2a00e00c800c1280d07024030021900500010344090301d07148100000706c0d80c24038091195a020f00070802100290606550074401c40341c00c02404500c03908010854181028818444d224040d580ca03540c0d1051490245440b010034100f03601b00504010391801ca2801c90000311444005881410160030307210f11192522341c418602002202d600203043c440001140344c1c00001401e04035100300c400720f4603500808103000450722a401807414519180d8080340040b0003c80c50540c00070071090100e484d1002882c0444c1d401300280c1e01c40900586c0009041048a50603c00e01c03103170b0394520312000ca200404100003010800c041c00752482c1111140008041d140002d5034000c02028070400b04481da694030300c82014414820b043d12180707480340404c01d0110010105000741 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 115470125 1250 115468875 115468921
    0x8090705030604150c08150f01021203130c06030e030313050c10030f0c0c050604030806130903080414030a174804080604080d0b04020309010b120c0d06020d060b04030302070905 78
    0x7d0103a8000c20481410002104c403030542c024252903280c503484000046106da8003901c016403000c1e586d840c004c1075030340c426403201c0100f500d005a0303d080420040100e07600000c400200b290343e5040b0b0b041050a107001d0322501c81c0e0080d1030300c1003c1c3d000c1c4d4068201000070203103c1400c01c00d40250440a0781e001d50300036001801a04154001400240500c3d0104d40007140605440b02c081500c0348840d0481d25004002d901003160368007088108148100b1240100b82603201450405031140c03030141080c1c6201e2001c0c1c0320821081d000520600c81070610700000e902946280e0400d03c481c88100700d5030755018030380103140700001d841005040041800c032030840b0024401000035070b480ba202c4102c644c0140d500e11507429141e0004510907507503030003d14081c040380340001501000c071a00b0803003424000001c01220350411041e59485561741d032f4400c4002900080c000d83d84001202c20f400040045402921001901040100515900050f00b01c251810900c00b0821a19105184c1c0e499451000c0070309 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 115471375 1250 115470125 115470151
    0x130e0105070e01051b0c10030906060b070519060f02041707050d051c0c06090b070e1002120705010204030c0e1b040e0402040f0608030f0c0106050603010b03040308090705030604150c08 81
    0x1217440d0755101c00780b040041034442c00d0000d100001c07040c000c200f01400001b505c5001d59418801e02e40719846c01800000416854415175a4800e51220f034082000d040c015052107400d01801007940100030500c2c00408110b40da41c0c6c40d043c440440f10020b02c10b8030040c3c4074882c030200703190030286840c0007059040402446101c0d481c3c0c0e08011044d08074031020040144984c8030000281c2d141c0a07140700c1c41c1c4500c603030588610388460010617042c0c911403801c2c810309000243d003600030b4020842800488446540c00e588020074100b1501a101340d500c02031605108c007100003116175034050f4140c01f4250144c2d0040841008011a40d014040c500a000380b980004e00428010301d442e0b07000c5d50301c61110000c0405c400e9900d000c40c50564100300319910702c0040c005883c90406074280b050030041d0030216219401c0d54108100301100d4000107100601f44007801001c0b0391130031400c104102c01020000c1c00c0354024545480d10034003914000d40c00c1562741d4149108404000c2c0100c01c05481140040542c0c = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 115472625 1250 115471375 115471387
    0xf0b030309013606050903060a0603080307140c0a0c18020309070506031f090f0605030a1109060d0b010b090111060f04060c090803030a02090f01051305040207030e130e0105070e0105 80
    0x10344480e103103080e45030340c0180388038840c0c1c1c641640d4080d8410007080640c48446d100d081080503d4246440200f4031100140340c002d00348001034016060f660000c5551070030504481819203851407a106d800740155840c800c00741144100542062440181c910044464000c2c00059000724143d000c145d640c210143c111090a01550503c03201031a809600300102c08005419070034800580b59054201d190401d032560f0300001c511885001c2e00004080aa000700501003a035120454008003125500d440b410f460404034406e0341c3c50740400c41e41c16410154206495a42d04900a0700394410701c0102e0200c0c1c0710200608101d0030103d8400d21400d106000ca814541e038580e5208000c00040328108144513203481c01040401c81040914401c840700d01e0011784c0c0b01c44440800400303c000d584854108402040311004180091115408a940981d0050f071a000a0702c1c0c169180c0d1840002c05070840480384444d030710704070a40c00c02603200109d20020481601c40039821a03c040d02da299880c0840e03020003031 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 115473875 1250 115472625 115472657
    0x50108130204091713050108090f1c020f07060314010f0501020a060e1903020c15030601020d1202040e0a050a05010911090f0411040803030a141506070302100f0f0b03030901 76
    0x80700116a208030004c4d0780c8140481c9100c400b40d000080304891401141310103015035600700030481e070490a600018203080041024040d6102514591011220420103101248900070000f00d20140c0d08001518403007502c0702c030000c2c01030240040048410224400000e50b01c0c03c1a5481e03415110103a000e030107200499252540074110080c40c0b00c0051140c0c511030107680c0b00c3d43e40340702c403824425030103010501450401c00144000300028601c1041c010024010143e8000400201034080c60038280307440915030000d035000340103580c0003501400c286c40c10030014a0b44e6600c102e110304000c0c81c0401003a40c0311740d081012610415a400d001060400880c3c0180c5890060300100d40c034010008074036800049490303034080c1c115602181c000c4c0c0c4040184246600140980c1000312255200c4d0741140c60808019604210b6800c0100e0066100141101c1803600c24006042c032641500020b0151307081d05031201000781003038804a02c9192400280502034900401210f008003016555000c1e00000f4000c = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 115475125 1250 115473875 115473881
    0x40f0b09010e10020f010f02030106020d180b0d0f0c0804110d020a0b0705011b0f0206061002010e1209010f020615040c1205040609120503060307061b0c0b030907050108130204 77
    0x90564140281c0d104102443d5452082624043c5207980c0034114102940404a0a42e02d03449540a620750050005101032640011440017a078600e180c40394151144130500c010105031a00325082e090b90004011035403030303d603420410f000112a002001a0703030902c0b0b011185090159001017003512503a0400b2800d2a101c00300b03068140c0003c2c10b4507511a601e1031414240e40c8801011900707651512010b0f003011500c1d1b81c800c402c88020303050105081003c00320017500c98100030711880c801c000040100256038400d5000146410202c1d04413450100c1041000320160400c0f04039a0000b400303840c202001d10320101d000390003000300340c144407449811642000045e02818021004004136600346014903001c0307006180c041c6000c0c0100103000344841c02d0615005003490300d11014080104280446902c00140c4031088600d586041a1a404a00d50440034800101006031203103500070300c0465a0070a6600650041100c0c0040715071484e039070401981c03541011144070b100310303610342c8155000d400e140d0 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 115476375 1250 115475125 115475137
    0x6060c0b011e06081509010909140312040303050a090212070510140717090d03120b060a0c0605040c050a030605091006050a03120216170607030b060a030b06040e1e070302040f0b 78
    0x40c002c070f09040341c1e603000c00c0341d51600b40d00402003e030b1640108010310040b054ac54225802c83d0000c1d44c80c00c00500055081d081d07001c0c1c001410907903684001072998000394032140c0c0081c0e006000805910b00340b02c1503aaa0b4150b406007034451340c400c0001225980c05078800300182820115030340d007400099110003a03012a000c86080c480740c81000005520798030b06c1908000648a5110318000d440c4816004007140d510022040c0102801c110b030f90005038111011548207035000c80c0110b010341d250f14254503c02c0090f403000c0d1300a88054004810414103401c814800c0c602e0b80c0c00c90710f2101d0641c0380281030718400e10605070001e814a0303041c4042021608140c61010542c01160154003e95181c07040c1c0114640c00210400542c1c40c514014140910500f504a071252405000d54004040003c0c0030b803060002c1d0b0b8041c1aa82e40b100826500d6010543d0000c244001e0060454500440c3c0007800c440c415103c000c2100c0950009400341c0c0c005d00c290380549907014045c40c511801c6c40507282c1c10340c0c805 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 115477625 1250 115476375 115476391
    0x80c010e040905060c040603060501090b03150a081911090c0f0d060506030a020c101401090f140703090209010e0403090311030a0203100204050102010b0d020f01051c06060c0b011e0608 81
    0x9640c00b030001c110b0401c10749004d030485840269980f458071030001c08641480c6c00c501e0402c00d0510301041846120416241c100c07082400001800355040c001a03a000030341ea10040390340c01070501e89500390701c098440d504601e0290341089114082c583c00c014907603008552a0005100500040344030628207000f40c1081208114001880c507164030001e513454004035031002e0f00b950001404180c90703030140550080e6540e00c0c8010311100b118103000c403800e01014000c0d080f809556801c90910003103290009880c006031800c0103003590820f0540207006c0c02203184207a008241800001a041c0f00f0b4000041c0300da60180d603507902d0340c1d0450361203241c0401c0c10400594184204141c41016a0742408520400d5448150050395189800006801c0d1850090b61a00c03030541502c5503030142c3c0f42c0c000c00703040000c0f007443c0c080e41d581d4030103840c60020085074503001d031007528280d00071039941d401221140805016100042240e80e0b568524000101c2e56240300710164041401040494001c060198100c894 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 115478875 1250 115477625 115477631
    0x130305060117070b04091d070f0504110c0a0201050f0d0f05090d020706050703050d14070c05010e010606120917070b040c0b0c0c0907110d0210050618150409080d140907080c010e04 79
    0x20b025001f03898070099400c921012404850104000d240601c40c3c403648485101001d4141201c0300e07c0903440f42845040a4184200060030f184040f0760301084800c10300030f548080000c2409031510310024031044507441510b01c00c1c100d030320a16600008080e8210342403070b40c40900c2c1090598040301d10f60801c0989288680c0c44580001c0002030f845d80315403003070f8035907034070745160701506c0c2003203402e4620a050311090350b450403005022180e8000c48030812692103080205100e001e03071a10f00610301c0d48209290a030000801c1714030801c81d02410085c01540a080d420300d21544414800d00b061241c983d000850b5030140c200c404c4076017012001c56900481c42d0420b103030940c5000c0f181e0f504050349800076500580215011750303e80f442d2407140a40148059030314031041907046081d003041c000050449940014410301c4400d0326aa55000403443e03070390100b041611041c9100903440034010306040740e6030880d01a00016280540018800b08483e5050010014140c00000641c1c00c0200400300319081130b1 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 115480125 1250 115478875 115478921
    0x12070308071b0521070f06020705010c110603070504030c0819120306030210020d0311030c2b1404020f040902060a03020903030d09050601080f030a02070501050f130305060117070b0409 81
    0x3842c04400c134a0401c100b40b14682c03050700001c0403403e02045802c01883c403144024188401a80024030006807002820145e0780d0390094140011052130343c68620b503001c1400002c2142096100d0054401c5912030038080306010345905c070407600c0d08007046040402440340310290f40825a0705844c05541c10550400044442d1a50040784500945032121009070340600c04000c207569151140d041d50001802102d401d50810301089000c5228070540414038024035440840e400311100054248003002400400060143c00006070340711300116402e074030031100311403010040c0c2402c0c01150006c95004203031610303145031948150020340001c613403140c0610040c084107035124111b2040e04419805680141a03d40c9401d0b907031071034035081c06803928254100b800001d4550390000387c241d0644a0900b0900c4c1c8844c0403102d80c100714024201180c6491083d540000700340309000c0781c140d0503140e1030807000c03000120a4403819030712182c81c480c03000503c001700005c00c80c00301c6543c41511184a50000c1e0307403281e0 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 115481375 1250 115480125 115480129
    0x3090218010329132a06090918050d2a060603020406080307081e0706090c09062c04020402070506070806030c0d020d030c02040222030212070308071b05 67
    0x2109810440381c41c1c41d051000b805008201403803610452201a43c40741500c1c000ca082c0e80c40400d0003000600803046400c0c5509090844084600b16200c0144d281c00c146030740f001c00038903582c5075125000b11a0b03d000451403030041401241007210b03030010018503800008070022680284072040c820f094200070180c4070305184843ca103840d0407034040c61006c58111b007540104007c840c000d41c00700350160700070808080007aa02c201074030f10000702c0030040c044480b290802d58080344140d903c01030038685001220010400d9030141c0000341e40090300d0801c002a210950310324581d2006100a07913000d0b041c84030f80e0380050a20140303a803040c4058030150408180760740b01c0b442c3c04401eaa807407000c00e9039039007040501d00b803c11400ca14031030115a03007070807210140c02140c20075900ca04040e041203e0044000c056440310340460740030200d8501c42418103905440f02c901865000d0108911950b07030700380313482c82c3d80100064450540703400c00e8203240340000b20340e070f41c04140d02c07115041c5510080c1c6242c00141c41e = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 115482625 1250 115481375 115481419
    0x40b07030c050c09010f0b03090a080304150b09010803340317070e060306060702120304060e010e06030106020303010513110f0301060e040c0e0d03030b041b0809030c0d030902 77
    0x110310a07100c6004800075403501c01c0c10046a115001c0c002c0b5140e0f001000016282d040303100444d030040d0310356540d945400002c1c50800040d4100506402d50020611082001e08032071600f0030016488200044000307a020080c00020030321901a8590082c400f450b0402004c08008040450705c00854011900e0840c0420b401045103000342d02083c198401c8101c810241c0c030710b07030b50701440d40e10384140346026a000203150350001400145c0105030100b5010215241c1000e040003041e00002120b85699581c84014100c216241800e80006e407400d800382e50311304003001605c0c103954a680203141180e08002c00c4c03041008040030287c00f01500e40300e400d03074081912001086100d122084042c0c1e2036040102c0a410322040c02401c500851070044190341c0903078042d00302c6600301000c940c1c0d40c04800e214101200642039020100364410302c0c08a4601e140400703140380345642040d9480d41c1da11135031803410458582c020f805451040c1e030005040e0601d558840c1e4010200c162004010b940362140501e000850 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 115483875 1250 115482625 115482637
    0x5060106050a0f0503010b04030b0903091203030702010617150714040801060609080a02090a0f06090f05071404032006070506090615100c11040605060a080411010c0203061605040b 79
    0x440c10000d10b142800b40d1209407a40c040c2c0290078020300d10351504440744c80900c030700d100107071882d414000840c00c107440620480e6030010000348213607200031805550b2a00d99100743c410b0740c00f542c602a00090b000094104102c01c103c4c86402038001402103158182000d40010036040070020110600b28a64400b900500041c4c600c003c00018411704120f00506103030007a03002400c1b6030307024182000040e41d03000d2080da4058040080418101c0068400ca005885560050070203030b420640304100014a550102c0e03c134500d01d030b980494800d11b02c40705000b9442940000341c500c0c00c5280140c1d810b401058030350310f641d031b070040c203080c1c94208151203603030030400140c8210fa05e90b0401024031000b08c6e07000301e241445090840344501c510213101c002811080f0500c80040103131245650103c90359849902c000002c010261000342e43c0c0d4121040240440d004a500b2030b2100f44000c0e05007550f51040c2c001804040c0e001d0010410b64413600c01820342c904000031124200b20b420440450000307941030107012 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 115485125 1250 115483875 115483877
    0x3011e1a0d050105010c02220209060c03090406060503090a0602340506010f1d060d021f0809060103020901050402032e0e09010b280e0124020606060306120a05060106 73
    0x344445441d50124107503079041c2d00c060304000c4902050005a82c4140c4441e20f03000d2071805100304840c40c01c1000019019494070782c0c0d4040c1c004581c0c9110204040300521101408035020040642c40d5501a90a03000603a00030b0955800fa14130040056802e90040101c0c10320420080036207650a140c50358409031000103044031052080c24603040040400040c0d001d00440740b41340030007074140040d60080f4410541c146172003a0700c50010603416158180015400b40d005070100300001940f40d980046015400c41c090300040341c40c030000700807a2020030818107a9900503c45400c603483c0c41d04000280d00007402160745220010141403802c04044451001c4030906440006c890b86442500c9512820080c902240d60341030450054040d80e0790303400a003040c05c440302199030321071010318503041c00c083c035411070341e40ba8a0203000441c0d4140c0c082d241040418280c1208094082d01c80307412600d41109a80182c0c11203018800b080c003a00e040385540030b01d606c2460840ba012541d680322186826400c0e80020 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 115486375 1250 115485125 115485127
    0x80a15090b010f0e060d0b01170901050108100905060109020904180c050f0402031b0f0712030f0c110a080d0e030d0506100f0816090504020703090906050a060503011e1a 74
    0x10002e581001c00200c2954035424040c610580e02e0004c90f01c2841040c42401d041030f0f483c030b48500300782c0c0281343c00440c41c1078180451071180b0704061240c1c001c2c0001c0c042d0341020f20407202c807100800481d0089010541c0d10102500480c2d10b8290407101039000070000d40d50140e00e85400d580d9481d20718981c7c0b00b5079800741442208983ca808144030414100b449114066801001040034000b00744502030b02007032070011144d83d28078549032561a50b000700780c401020074a16900d0219869410f4102c4008114001400c101800210405603040000021410310b01e4102c1c40451002c1070160014190604000a012480d0100900c425007554070481c08600724540d10400e02c2070705e081c56940001d4250003401d00100001400c1d401174007181c4002c018144c1c0511000820038000d100b0002a0010100503005540300d02e001d1038003428a186034000c03840c500d89002c0c40041c1038a00400300f002203680d40d07220b05140d6401d105070308001c0849064000488515060001030f0080b040414102000d4819001 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 115487625 1250 115486375 115486391
    0xb030a180506100909020a05060d020f041202090a09031704020f04020a0203120105030307050a08070303150e04060509030a050703030213030503070b01080c0103020a05030708040f050706050a020c0a15080a1509 92
    0x1c5401c03c60309812210f40035140006803401030315140d6240069410403107072103031a2203080b003420002e84200030b0310002030103004c49c0000742200c1c00400900c145100300e0321181241c1d50b64195400310741c0945e401a0000d16070180040e003c03010010a26000381c0090084d154007000c5c10702080130b9078081d03501000103a000140c2d080c01c286503055071030b000d007034103e0255203400d003107440d420707a24100000c01034262000021120300300740c066030150700c40c100c0d21080c1d01002da80d03d0f0710001c0d105900302c80035629981410300140c06041c01200b141d010f440962500340c107003c01910b0813002504041024203010503918004004200c040000e004081d110311000401903041a55190803c0586c184450506d401032251564143e00070080d0303503210460b4503014440350344e06d003088a81640f00040244c070714044c40d1008143c0344d85c440c1c02000e00c81e800b070702106c0c00003a81409200d11040c80d44174000b0031120464010320100c1c0700760704054204054a2000c60720b15801c204555402030254003100c1030903503842c0a = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 115488875 1250 115487625 115487641
    0x5090304081606080c03070c0605010b180a0302010212070f0c080303070f0f0801030201110a170c0c0f13050405071e06030b010c0c09050c0c010504050d1403100b030a180506 76
    0x3040380d103465003603111804030f85010800703041440050010550400b0100000d01c01d503224007880c1c002c00c0c0d08000c05001c4d40d42e4408134021141d1009180c0c0307400f04582d1074a5500c0d8101104420100c030340c1a8020804191a01d480c0c4a1640180300101c0f40120450042004101d41d03400001c06000b00b174000d95920f00300b02c1e0300500404140c1340e5003014041d0490b01c556511782c000e100c02c0d045940a0902e108114150b440325800c3c81d40c500d00040140b401d000005100100100292a1015040c03040303a40c440301c40c004000a124680ca00d00c0e0b0b110041c4042c00d50a02030075081300342c010f8440d400b00c0702c100391183d09016001c81c40080001030410065010003d090303041c054404694403e0070500300300311090b1200ca1070f1800c2805100c01054840c40481c3c81000850200d40b41c00020718002c0046040620341141c4400b2500c001c400061601c18207908041084001c0f42c0c01058800207106503249045c035490003982005003060f1205607a810414a4204010681b2100314411000b030882c505c0c040403 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 115490125 1250 115488875 115488883
    0xd0609060e0c0a060203180d06180303051b0f0a2303250804030c0311070b27010507060b31060e092e02070f1103010212060409020a05040509030408 65
    0x10300d10340f0800d143c0100300041d5801104449036a03404480c6507911181c0c0300041a00c258403c900202110700e800391001ba100742185241b80d03614401c1d501803200e51500e0150858503a03a240500e0b501c400d0030040c507510082d07414014200304106050505c14030484141c118aa8070039403801c80b01c008400030422400340c0c0495002c1c2c0700c05150191401d842030074184000c10071000144020203100c560308001c820315001c0c5044149001c418411541d0080d01d40f943c0f0010b81e00410907044140301e21118409614055a00107440420180d40c0c990500a0035102c40c4060103884024680000d134503c400002941d10303e6065003496a10540885004544000c1400700c4043e540f0a1440c44042e00910021001c040341003020b100703201c0da0402c030405074035a040d181c03200c8501d410303040b19100251000404c00720209104e44c590150074090103042d00c40c400d1500741e104189403200503281d0080010300e1850298055504580083c081c862069107441c0031804480f01030b9642131040d030000c2000c0014090800c = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 115491375 1250 115490125 115490143
    0x406090611010612110a0b0c01060303020c0402120402010804240504050606010804020a05060d06082d0304030b04060f140705130506090607060203060d0f06091a090703060b0d0609060e 81
    0x24000b00559403030200000141130320344030001c0180e41885030a41c41c42e51124900c01c0604030a4000c0c80c0c1d500e5910342d0f561300800f003d10049015010726174123030b0780514280c400e0ba8400d403840404001c141d500e1713500455140000600c1258089641012845800b1142d01c0e640b61059003010f002500b03040504080b41f40100045c611410003004101300700050f15205445d400300d4909542c105d841e400505034040145c0a15080114640b08400400703d0181005083c600722801c800c03941c881d08407945404684038801c07400081c080b400020003050000e1810341c03115904455605001030b100000950000f43d80e1800d80740c7c0720000c1e1020803002441c600034400c0600500f0110fa0203841d0044a00128203d030050010142c4525808030026903151201c001d46c42010f030340803568605540c024603005004204410064030300b54807140d0303840260044031042e1401410038100034468545140e540d0405031032500c1c0040d03000002c136481140050403d0181c5603405100303800100d00c0512401e60685800110 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 115492625 1250 115491375 115491407
    0x1201020a0905040c23070c0605040608130f02030a030e030606041404020f21070303080a0203090318060d2d020304020a0e07022406030706020318040b0406050604060906 74
    0x1001082581500418801c045520a5501050039500351800f0b507850300401188050b018800d100c00c2015882d032200816402e0b20a0781c2542140d40c941a08440c6030041c1c5c001c16000c40c1c03134480840d11402a0070000c5410030310401007823401c942c0c56400300e07060010050040b03001c14006440c00d111450140a0203a01c188269820410611104219038840001901c040c0c0103540001420308a41c031018070050702c000006680c200c0070308001512690341c0555110580001c5c1c003600125000b05494005c8902400c027a600842c20312180c11071403c800e40454080c5944042d08100ca94401c0495004900d06208041203005154040b0030340c10080030840c40391b900005104004102c016905c0c1c000d0041a50340300f4103100220340e078140e0141c0c034210060542103d1840300381f2000c000c040c400c064041c45014150103880e5510784e0b410080c1d03921b004404141284404050300c842ca6410103a200030808007000300301080e800d40e03c40c041a400c0d44941c00140004081d010203104041e0060034942c44c1e0440 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 115493875 1250 115492625 115492627
    0x414070b040b0910081b03060f03011d060a05010311091e0c090f03010605010c1205070f0b010501110706021c090f0803031b0310030204020d0207020a06030b120105010b0307180305010e0606120102 86
    0x10512034654518801d102c1b8196042c0c000c008198562942c0301781010850014008200c1c020700c9818010502c69841610000d510032000003840c503005500846040720b500699110003400d006080010602c2c0080c8051044101d49101941690360004214010280c0f0000399030b46403250b2040c051440c60401c901c9010340e0406200f008581d90015500c0500c641000c2110709084580c2000c4410b44555034000d002c007604079410b0000e01154a010034100c0e0000d0700c4e4010500590700340c00c0e0301c1e802c1ca88540c2e80581c00045044a00d100c0710740e0741c032800d00303401c0c58000304254032011007244001c4a03400202c003503840441008a8400c96004c44825281500c424504618000c050700000401c1030100034001e6402003101070055000b9010b6a102c0c5600034500003000d0b4803944000c0003410405441485039882811915020b40103224030340c160f86000c0215031450361400c1c42510200d40202c41d41c02d02840f10034000020030403c0c82404912079040000d41550304140d410441180c0000c0324082c03103a44 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 115495125 1250 115493875 115493881
    0xf170411010f03140610020709090303021c2c010e06040b01030b07050304081c020906070b04050c0d1a09070b0301080c01030c05040806040f02130e01022701080414070b040b091008 79
    0x2503071000039071748503d08030b551492440304440101d04085803503000714074045c141100c41c0c0405805030085c0c281580021081d407200c0038820300d1001611404017003040d0603100034040d00c03052000350b450202e03407012150000c24000070a01e006841c0c0f0340112400e4490110660040c030403c02c0c07958400703400001c1c5140c11411410107441b405078600c100c440e83c0003126000c180ba4029400107405035241408000c0009444162074104080040300c1110300302c1d030702c1c0100c080400207480d000b0801c451454000e8001c9542020007690051000350180c0158811301c1035501c005503d48405008501901000003c0d103c1c0d40030074000501941d400012031802c0c031100303200c180550f840000751103034810f030014010140c01d8014000300c0c0c41c00707444074892003400d41440045000c04030150020003034007014031805180070041281103d25107020564681c000f804080214020400343e08491800600001c1a251003e81d155a84040c650080d880040f030741c000400d250b95240361400e81c541e0b1724101420140c1c083d00d = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 115496375 1250 115495125 115495151
    0x5061002060105060313031b03030213060305070509060315031204080f0c13180210020313051f050d020f0403120f0206010e0604020706020c0312010e0a09080a0f170411010f03 77
    0x40001000769070b2000c80d1006c60380034984500c514201002041c0c0c1c10920041c69820020042e40c01394026031201c031402080000d0103031180c81054403450075076844078249240c030001c012a41c3c1c03001c0d188080c207802c00e8000902e2503906020040040c0300c42d006666480340b90000701414200844800700781d6070088802c41da007548850050301c2c0c0c2d02c5000c88001076880707001d10300e8070052442c3c60780c081c0d0440704d040100d91070503070000001d10400d6544800c101101d0703074035000c00c110301d40d440c02440d017000101c1102c03058150113840038105d1100810b6000d81030002c0d003403480250b60482d034426100d080c0c606501052a0741c10a801c0c60950311244040d1500d503041006e0a0030395080031780402d0040d80e000842c2d6017405440c1c1d0545071807a140c401525960b20b40c0040040b5409001e0040d410402c04400200307098030054403031070240c1c3c0e5200c100b09003030000d250000e40e80701b15030400d6201400b0140c00303181080300110034807501c11480b4213040c9103008070742000140101180c1c81c11009051070124402080 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 115497625 1250 115496375 115496377
    0x8030a0c0f032d0212070c140a09050a050a0506030102070b06012703120305010605160605070504030515040516080703020f0303070b0f06040c0f050d0b060c07090506100206010506 79
    0x15040600d031018107001d4a0200ca03041c0020300c5079108907069250000c2c20075580d0101064800c503a07030031111881070a22000501d849001d000420010000b80100800e05098101c00030f01c000041c02008183d82e2464990241c500440d4a442050b68840400060305840e208550708450164000c50401d401513850441c480f034080c12090502c9030b0b8840c0c00f240e915000c540e0012212900701d800003216034914083d002c81031088903450200f1300301000855401e00c640c05440000e00c03003000b0049110602d80f160750050601400031b03c1004410071010012030020000e0b5162111040c1402c03010349054140b05051000000c402da0280151100403c046c100006090066940480f80b1003201000070300001e2841c0301c4c0e00030003080c0f102001c0400003c50851581d00d0300c5030209540c00d100600304800d0071643c680c0620303030340f01c00304070140501c105403c010b5001020b8120054201898401e00380c180c54600f000651004440301d0b2100c00300191800c200e419403100c0b5500303000410083d41840b00289503 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 115498875 1250 115497625 115497647
    0x30b130f02090a020409020c011a030c0a03120e0402040815062403150d0506100519270203191808040605030403090e01060801080d0f20010917090a08030a 68
    0x100e0300c048000f00310081c10650450f0000e00000d40111341d1400d100400301d000c2e01c0e11036450300850006032054503e60034040346050707455070002c000660b200e0031580e5000c0c01c0312407882c4800030046a01c0c0c160300c00e40c07128070052004c0d109000003420b843c82d0400b203503140107200500b518065900e1b6400040010203048071a401d13100c4d500003240d282c0c0e480011410034400c420310356603841128115180c0601074049601c6009029600401404680740c07014044c500030b030b40d004034559043c0c15104001c440000e40e115210081e6000c100b402c504441d40014090340c000340c65071006201c40c50b00303422644400344503641141e52100c9074440d41040d16100c00c0f00c6030049208aa051181c0040040c08040c0300e150038002402c0c0503901d05583d9611000300414504003402028080d12420400c1040c4030300601441264001c16501c1246405032022500c514a041c444918000d6403184614030000f451028010f26403020501c0326034a0340400710800540034820351107280e40350010000c0e544025884545080707 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 115500125 1250 115498875 115498879
    0x60507052505010e0d1b0e0919120c06050c09100c0812041406070801051005130b0a020a080414030106170307020f0a05060d092a03140111030a0204030b130f02 70
    0x2040d00039200105d44050200080140010210881e13030004110b910700c080182d0b81c1c070254001d40ca0795217110341c6a440030a900300080412100d0765250000c0e1034a030207444140d042d8903000e02d08000c0c0366100d00503a08203594601c8492408107400800d410811030100f282d20352490100c01c03c0040b0b40b12054a48254030075002d115604100203000d010503050f0640351002e1440c201c1c1c0e0645031640d002407440b0000e01840b446a041c83c80c01c0540a4852015212400d5030b940380a94030364071301007800c03d841d4082e5903000154022001d0500209840e5030252004166450710490001040e504040c2112515001301b14203030080044000c00c84400001c0d43c1c1e00340d9054843c02c80710003100c00003401c8800c060f40110780c0005c2c0024003946080301500984030043c40340c4001500d4081103070f40310810095402c1d0340c070540d0600c11000c00119184030f9414520118240001444007100004000158001c4565141c00c50300010100100700040c81d00a80c800c480840d58041462103136100c881a90f20f0042c064 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 115501375 1250 115500125 115500137
    0x6060801360308270307030c0506060f060a0e030f0304030501150801021201091e0501120213050903090f0a2c090d0f0e031005150a12110603070207030c06050705250501 74
    0x2150074001d058104c0031820a004032030719003d6600e002411880c0c036240031185805441c0110750300e41418440c0708a20703203005044074102141c46408441601c2807460403a1305100300040032101001c14402400134601070000498010090700c0a10342c080c405030300408080c0c1c0304220507401c500c4c3e20005141510142071000c0348041406a007081c0300b03842107100700b035990300e080000290702490061007030085200340e60081c2a510b22000b80d03411200d00302c500b190b154004100003640d13890b00e02c0808a400000034036200c042510744201450744202111000e140085c170340103035841100500026648164000020020201c6200c1c005200d04600c080010034081e050600c014255028481c0c0e590b800384e9000100107525245032800350802004030b00078002d90303800c140411280d4842c6041c00c091030300220b000700051070782010320046500042c0120110301070b101c000300c00a4229500c160040a86654145e10f807000c0e03040c0181840d0001c0a0032582c00e00030b040221080418060400442e0000d007040 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 115502625 1250 115501375 115501411
    0x20901031407030501060b0c0d0c0308160302070f0c05330702030f0f01020d0b01030b060406050309120a0f080f0601021218150a110303040f0602030406060801360308 73
    0x41403800100f5000101294204440450900c00c001e024007041c00304039084500012170400103441441441c030780a0300084a18001403034164000e4544052034805203001841e042003916a121905035038402104d00c542071500422180c9401205002c0001400100d8061030031004844a040240e0301c2803019001404109031040d9a0107119003500c150307100c000c1d034280006010b403c0c0d000794403203422500410315000c0b4a041c9540320380f080e8084144042c1132580b4050400300107131819080104040303800c0c80f84000d0410b402104101601c034808544d1180c0c5401d6482050103820480002c00c00819140d01a007040401e030b034000340c0c0300769501c061000c0581e5468401030320300b104516507000c0d5411181400003007000840b0302000b0700c80c50040e56900b0324101121051142c580c40242d41c00307841c043e60680c4a07004222194020354100f0720640001507101e40c0c1d84011401c0d50040711005801700341f404901312403004032690904224054002d000002d406564000d032803254080e0108030080690310301 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 115503875 1250 115502625 115502663
    0x160f080303070818060a0501031b080309060309010209190e010e090307030804020a2705090c0310110909010605090a05010203030108032205090f040c050a060f111015060806090402090103 82
    0x121801080c080107841d454502a441c04020708028403003103403040b0040cad034600b80f4000301c14081307800e44090001441c0382004031420450540c01c041d2542d078281d5420840110655031380b0044000404d01340c03900c4070005240c061094034214059001d050203070043c00070000c2d0a003010044400d01c55040c01c11072055108c03800071441800494104080076901d9418214516401d0051410b161070340341800e201c15a81c0a158a4403103891803180340d0140c0c0910318031100142160800e0843c151b051600905101d0302c440000c0503040c0c00e9000a000c5030002030700b041c290800a00f440c0c00b0340420300056141d54501101036036284200d122805403d02d00c074014a810740f914184000c000c10004001c050380c1c2c1000352400003040741c00da0b411582807505a00004090820001c4030301151100c2d114110045502078054942e41d40502003903a0030301815100340011250b0307100c1c3c0b40c000f03880c40d14051003141c00e0130320240000b040503028074480d000090411006941e50340c0c3d0541526408002c4400c1719080700c1d0 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 115505125 1250 115503875 115503901
    0x20d08070615060903020f0303070302070b0703031407050a11010605090c0c01090203070305150109060b030601080c09100302190c0c0b09150f03040308180a081303060905160f0803030708 82
    0xc2d0000181d0060b540000321650f1007030800054900880310101803603046003c140c0da034800e0f410002d0141e04101307001c100c1c4108030409070140900a00f400300f4007600340c0b032020035540000c03070310603001c1440403c001c1400c40d40f081166070708a86040003041304034102400650088030062180007611000276000221403001e40265200380e0780501190a5240c99103070503030302e0f46280d1004800c407003804000000c1380c2c0124000c40c0e003111080e008842c603503140c0c0001110110303001800d00445520030080da4446459100e00001c051405540050f1220300401400d1001d4071a28011410007181d60f550202080b04040d01400322000d04075040d9865000a0200e2110100c241c007034051240b011846940c1c0324190001140300c1d40c442c1d5a00350450303840d6502c1c03c0c0542d844200e0500d0355032141d503801c80018426001014105044040072042c1940c0740c0c1c0c0c00040e101d1090301241e4682000740320074007100034201c50401034002c03107200c21121810706402c1c0c0d54a000007405141004250f07008180c2d0204090 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 115506375 1250 115505125 115505141
    0x90105070b090a060e0d0c020f0f090f1014010912020d08120105100302030c0702040b01020726011b140703210b0111030901020a0f020f040c09080606060403020d080706 74
    0x50008000380c42c1107003820741c440f030751007200f81d5010341440038036004204081a01154402d20b615017800300b09080d000c3c480c61883e0b190485821000100031248555605401c451140014481c541c12038036001d1a2041400b202d0745c4003441e000341c855020b2400e40e81189250040d82c0402641c51840e881c07600000b01e00110b40744020708003000016485142c5c905035011141a01c0b016521481400a0b201044040f840101c0c3c000c45808414441310005203019000461101014411144040d4482d20456851420741d1900087c100c0d5007000e51001401c28003480040104600a4843c110960b81c4040d001d160341e100c015946d4040002c5036030425020342c11513400c41c41c2c103200802449101c80e580d803008200c4032040c0c60215980300303090704c120240082100d0714010f045c0d001d0f00b80c1484a5840c0e485425800c2e404990048a01c1c081c0c00c09611148076115695455a4a4071002c03403905031450700f4550043c00c143d0140a08000500158075888070032900c403503014010341da840304c1609003480202040 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 115507625 1250 115506375 115506383
    0x705010c080d1b0206092103060f0d05011d0616050901050706140a02040611010501140d060902031b1c02010203120c07050a05071a04080c10020f03030f0f070f021209010507 76
    0x40720f02c3c4800da550014144c0c2c41403402c2d0b000c5603464900103c119024401400c0d0a41414808000140302410000302c914010742000d4110312200584d80e4515007501ca0002c2140e607180b5640000031224501084201c0d0000c3d014410480784080a802c010700d90700c15aa542c60500100082410070040194840c402d560b0f00083e20b240783d400c0990b00d01000e540540b08500c001081c440c21900300c0c10f01845080d040320000024000b201d0715a40a0040c4480c0c0030000b990482d940b600e0003405600c0c28404103c0d81e098a40ca1030b104010078808005035030303e124094801c045489007821300180d8001007140d0310741514582010407079640c00805a103500c181c14004003540110417401c1f0410000044102c203a821140107884105071030007241c039140c050b40c803034058940d020b058110007170f0600d4040555000c0292060390300050002c2c02503032459109a0300d10b010401503000f004004000001d0007070f04200b4520304002c050310300043c003e64402c10200e524524403000518400d01d41e00590442d03415540c0 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 115508875 1250 115507625 115507661
    0x305010507080711010216110a050a0902030103050d020d0e04091e033b04090204090c030c03030f03180b09100e1509070608011a0f0f0a0f020705010c080d 68
    0x85103000030440b0106443d0140400c40d9119280701c81c60041c02500e00c0c0c0e00c220248000503c8542d1a0805070002440c402c0340c000d1100b0b0004101516940440c00181c090b8070009030707a95141d031034264640304e6105c40c18400c6412440c80f01c031b582a84100c0b62506c01d0011a80032804a1860410213500d02c801e008001d042070030203000c0000c068101440c014a41241d001e0b8880003941d4a403180d560350b402070a0108185c0140140301e54a2a1a601c1a00c200d40052300008100015079605021008150420b0781c008420000400405900081e0b000201c041840c0511000c2c00f0f512020b2400c00078080014890f156400015403200f0081100721000c5071928400c0c8184110282d041c1e0300c2c3c1e4281c227860700e107a510b9400050481040081d945048074075940e1000200d07031070b000007c01c00a0b89e280c20654401d80411001d1014030780c2c0d8001c0d0009808a510081e6075845401d400b50000c0c00b012a80700c02d6400203441000b1580e0070603000300c0d01d580c021852030758400f91514800001e00f0044202c03440070803 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 115510125 1250 115508875 115508881
    0x6060a0c2f01021e0a06230415060501020312040618080d0e190f170910030606020c011e050c0a08040801060317030118020c190303050601090909050604030c0c03050105 74
    0x160761040d030400c19400e8081e200c040b02802100130f511000400114920f80c01035441c00e00003003107640600003a569000300844240b01080500d82a5032003560103a03181c8540c0c0c11002020038651107100003e04090000358038004220044102a074401800a03103010b5941e50600c21044070f084c40003031000da203c04550368030348500044900030105e0514a00b0b6500c00c2010a4800c4440311520540c4a0303086020740b07551441030b5513015003401e4540d10340c1e501500c00f03112220254445054031003a030400f0303442c0440c1d4103013460402480c1c40c0c07414a21a0400c80840c101881c0000308003117101d2010b880c0d2134056510780c2c00c66400361078001d40080c0180b00860000780044c1110701940000240c0c0e1040d040130f01c17117035090258801680400e00424101300c000c50240c01c0740009503801803220191960943d504005044a8a919450120020350109031201c081144030360b84584928043d042c1511704103e0380c2080e40341d6541c4d9902c010002070030b0000c100e42140c280403084080b00010b650100c0240120b00d = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 115511375 1250 115510125 115510193
    0x1020d030e0703061a0a1e080f0c0603070c0803090102180301150605032a040f0e040c091a130605091602060103020616150c03050708010e190204170610080606060a0c 73
    0x12040d81c8100c011000307c4070006c520821f02185540030786402200801c0350248a50422500354000ba245c10284541807101c0400036414802031480f528401c000148c6a5140764134000d010103940f15428800d91400c10000825400d0245220540d84e16280031078032996560500360140342c0484180b0351020044213141c40d52040280104240d48503030024843d06560340150079a4804190303801004866402c1d401c0c000038120fa4040c03003c4c82661181c0d46102c0c1c1c2240c01007041c4121071402420000d484003400d104500f0840c100c0743c1c205980c1566080281d0182000a49410040c0002481020009403c0f448190000300080510390018100c2c0c01040030324183e90010711000b4030755000719081c500010906400385041700d040703410181129149580f50666000201018009034200c01d0b4280004603650020f41211790f08409500c0c010801410840404402c55800d60b201c540c1c0b0360721804c2080401d480307020555103820064141211040c92b945004011801c0705840a0f04901103001646401c0c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 115512625 1250 115511375 115511399
    0x1506080a0c090c0e150a17040303020d060605030105011d0303040f06050c0607050304021c0203010905241f05010c060e0a0b040209060405040507050d030903020d030e01020d030e0703061a0a 83
    0x1180d40c907000304100b800c915415101c15011100313031a88211800d84a1003908041e200516044461740b911008008040151458002080d0303410b40c0000d81c00300707083d0800381c400e1140030058006814050304540c94070b1300003000c44505801d0102d840c40b645450210b19281001510043c0c600c0c040e2000c0080d0f280c40008080703030440100552113105800100e41911300503011a409250054043d2980d8a40e0403009206484144800c90701507603900001008140144007080035010455090000c903003804482e40440e501c090302c0700c10300300c241c00b01e00b0071184408902c43c0c04990007801e01c00180013071030400b00c00401002c01701036110b00078410360101300003035203000c01d210307501c21551150182c0710748050204440d0203d5005284c0c0e4000f8174180102d1900501d0482d145200703190081030652070381d010589182d0780400c110081100340c850425a5078052010051700001803408000d01c04003110307840d40d44c50b060310010b080195202ca410414180740350040ca05140041d041c3c1420795518901c04200c = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 115513875 1250 115512625 115512629
    0x906180302030a090603020304031709032b060806190b0102031204080a110f101509110304050f0307031b06110309060402150702130b0a030c0312020d0e09041506080a0c 74
    0x2504c0180110780c09029100b500e0086415940e4900501e500784201d842c008000341c0303950914801030112220180c2d0104e125800019800308545040302c414181c10291000c0390464822900240c0800009070442400365090404122011604241c203e0040c1d003540300348043c06842405403020041030009090040410001c541d941815045401901c0c54580c0c0407082c190125810510400746a90412f0300301e25a03003042035480c080a0340d6120b540100b11841002440807c04c804010002401030038080e40d00c1110441c07010714980350150390020a000c2d400880700d641900504d110000380071181e40080588010544e28950f00d017002038032103a8450741101c089201d1703031a80d03501d00c039509004020381d800c1a9028213480d40c0b00d4084152030016020703288500b40c1152025100201141c4070301c040e40c0040d80507056540c441c08003464000c2c104402d00740e0080910002c1c0400c0702003501c44442e00e0346d2044d0840c6a1030b50402e07000020301e010305001d502000c4d05105507405078007030099220800003 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 115515125 1250 115513875 115513877
    0x80c090a05090412021c050304111c06090204050a060305030a110312010608090d11070b090301090b070503040b1006050406030c090e07121b050406180515030415090b06040906180302030a 82
    0x88540046d030182035030f8a028031890001890500101d03001aa11034200384100d88010310411594101081e0942203040421040d00e80c291142c540b6015070a0610406406c1408140309001944c1151107450740c3e40705880a040420105401158420400380300703494004061507000a00307035941d0328000302030000a8440007030b0342c05482691084075000e14a02082a40f051b0050150740380b9080e00b1011079003001e44419015520748112900182c0005a49489455551541c0303440b400c1c10301b411840b2130070051070110590241c06040c48419000700558084402c58038000c128200704480860b030388a241d07131202c2c139104074074014450515003240d052981d4024010081081d141c5038240c83c46001141840130010900802c01441081c1c07050100141c81e08500c0e0781d2060f4969120007051084003030004d806545000401032008116a07441250005c40c20340130705109024898690050303003900546018440c6a44d00e0048041020350342141c0e200c880740c2442154400c8071401d010b51203a00c1402244 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 115516375 1250 115515125 115515133
    0xf06020702040b090601080112080c060403081006020f06060f0d150b040b010302091809030c030d0507140304020901050603090a14010e0105011e03151b11010f060303080c090a0509041202 82
    0x40d449090620541c1d10900c0140d50740042c5900e41410700c540720302650026581007500304140503d0200c2000020300071443b9582d10a418a00040c06c40014865030f0422011034002c4c01289685400014100b03070400c108444d85c00c000f20001d400030f912075012900050040f60781043e80680c001c025800010460400e440c00d2280310344c0540110201d1081e0740d00c01d6441000300320400024410312000c6c0b540729007000c080760300d4560014107913481c5400414061402e551510208008036502041e01c2e5080220503040501790b0425500280d00200140240c8c1d0042d0000300004031038a4081290b4201160448100805a451001c956003e04059052145550b017480c000040584080800c601c2c0400031707242c014442ca0542c1e0f120282003440da08480c50f125180c40b14034644140c00c14540035210b4003500c41034040c50100780f0f11401c0d107a040d404103494038900710b000c0000ca5048607490b6400995895110380d108508400100201426008260440492400c0208010910442c0c00041c0005c0e001c035 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 115517625 1250 115516375 115516391
    0x10f0e07090302042a03090203070902090f0a030f0c0501080712090309050a060503010302041515050906130803120c13060e130c050d050a091a090106051c030306080705060a0810030f0602070204 85
    0x21ba05840c5180802034060740250803c004003e9140e01a01600704024005008089207030300140b40300364280c0054840c54070459000c0100000084520018102801c00039060701d080003014020420403050449842d403607140c00390425104d03903a40c1002e080014015101c45480e080010078940090008a000d54540a030740e8132640010b011101c2220030b140c40220581d4540c0c802203829030444400035400000500501e0940e6550420110183c01504020b50300e449404008040c643d5001d4070807042c0580c2080b1b6965182d8851160405607001410484035000e49007020481d003952030aa480102d900d0405039000303a030b5102000701084020390005204a403680d4045204a4002480007001c0401c1549425480340001c0d2960341d000701c000c0000a0745660350008190080603214955041c04200c025000801d0b070148215400b425610009168290803c80411001d00c42c40940e0b50034401200001581800211941e50140d179014014240c0c0440360314052002e074100c00401c0b44072394201121 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 115518875 1250 115517625 115517627
    0x20f0d0b190501050a09150305040203010c0f0219080f0c071a0a09140324240901030221030f04031e020a03170409051006020607020303010f0e07090302042a 69
    0x8030140ca400c890704803848961a20b0015101c1e40d100c8059030b403d0046442c000950800c090780718620140854602040d14a0320344101821585200000d030144a0580d044098056000a41030400001c40c0500380c95251035080c00c00460181250f800c02413500003034610410a400304107941280c503001841b0f8264001011034a005015085030303c00001e034402010808004041c900060420002d0280d404510f25044170210011134102c806001c41c00d0701d014410211008202e400d107404000d1140301013001004001406210b062201900c160140c0c45042c40e111040f0381d11800110b12142140d58900240901a00c1038000e03120a031844614944a410045060440f4610b030796801030001c550641145d80f5001950801c0a1030710348924203100100c0d018450344140c90103104101e1304244540d1500000030303d44600108040c046410500c01002840050302440080d601e034102000595910040e00700c1c0c510700303c0d60001e5403050401445094818038480c0e0401c1c0c40c0d0340c403140c101c036440c56810 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 115520125 1250 115518875 115518889
    0xc0109030806032e09020306100501140c03030a09060b030a0b04020a0603050705160615060903020406060309081602150a080f01170d11190506010801050f070504060804030c0501020f0d0b 82
    0x94044e190240504602d00c012002e01d0100d45a08034440c030015170300c0c1140d00070070b10b401c10483e140150019200303024009580c0018405000c1c4a0640aa44c03034080440c401984a00000e0328200040340c46600b02020003009030001c40c140300300a07088540e50905400d0a032194401aa01640140c030404004105688240509407181449449580c90a07841040a00710814504826070300142c1d00c00d0010107400c2245c03610070050406689440619095004000884040b907105d2400c3c50320381030034100060300400aa8a59040307008648078040c006001080170358089103040006804c0c00103810305865004401039014840f041c9441a66070388541c02e111444c4c6803086580401c0d03101d5010807280b83e10640e8182c408000120540d0740c0d07030450590201c16090101801c96482d04840f00500ca003410034411141c3c0a552030041a01350305040102810318030035406040c04014100001405150003041e01c0128654000002c550703a5004494003006c64002c00c200101c144c0c01d002001c889480c1c908 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 115521375 1250 115520125 115520143
    0x50f041d0a18021e13050c0c070b040305060606130e01030803071b050c0411091504080d02030403020f1005160b0109110c28060c0c03030b040207110f010c05030c010903080603 77
    0x1a02d007010300403102111400c18040c0c0d913105607100343c040444010f21074550180328010b4103038011943c0c940c98081426401c2030440c0e00038401c03116040c00100041400001d003e07070002c00076215181e662110300c19044415606400c01d103a080c0394480000100001a00114402e042e40e588504103100a00c603002d01c42e410504028009600c1203440e02028a4107600004000f02500860b5140141c00d50100e01142c1100c4840c00c68401d011908110640d018040030780410101d01c05149010300399400518881d419034101c5000350320b4409031260f00350003041103071780320802601c4109402c2c100786403d103a420300c24064812900d00703082850b890715612030150b40d250f13081c02000e0644541c407480324003150003054544030150180a80e81d00701140d024854440c40b161107503140e020088040c01d003d000d8a90351200140035034810001c44011a114403121807607401c1c200c40d0f401150710510012180400d04a2002c1c003140070004010354540e40541c007051060388a2b0711600e600c0d1b80d4031030415480b04148 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 115522625 1250 115521375 115521379
    0x30070f0510050a0510030305090a17031b030c0d030b180a0506150f1204021809060403030614130b2715010c02061213120201021206040605030d050f041d0a1802 70
    0x171030014030010f030041c0c0203010300200c0500b400d6901c5a030340c40c1060400c26449003080346500005030b416135424104201c4681c1c64089002140b0f0111114005692250f60070000c0c010035540c0d031040f000558410340d032455102919410f200b8182000c00c5400010403007034640500c280c0e42c0300c04182c0444000001d4510031880d41c0051070070010040e2506d0070411008004a0b4072941c6400031001c02201201098041c8004c100105080c0c07500d8900601254440d400105810008100108950b42c1d00c001c40447c545000601080e1000080041100000180c03c0140304c11a400180302c90303540b481643e6407141c20301c01c4013250400c00c0f0100544448081000194100b1030400615a040072008001354010404c000c400c41a6442d035112050b03118811105800140d400040318078545805d034140c1500001c04039000c0242d50700d040700203561115629401001e0041c0070030203000306114481074030004d140800b040da402802c1c4214100d900441141c00c0c0a1700c81c0780058003403000444100d600c40705580 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 115523875 1250 115522625 115522651
    0xf060602240a0209040212160c080f0a17010602100633050405030312010e1b190504030602120103020315040503070201050c0f010c020106080705010230070f0510050a05 74
    0x41d01551020500038007040341d031a02004440703e01c2c1c445200a02c10800001903400c1d007070410340304a001554a4140c80c0c010003000d0f0800c100030030f07440400c50703680741c8180800340e2752021064001c0c1c81c00594440750a41108094000050564020844008007040c82c0e40402125488140740911003221844042e440a401c40d5680700808a2140e0400801900d040946c105969140001c1c9140d0101d00030fa4074001680c0c00422207000c05000558115404081d00c040c12800020340c2100e80c00b4080c68071584410341480d1424003809001202d01554116001707544d00c80100d0f45800d4091028030049001c2d105000c181c114051041100728021036002010b1031401400340c004507142e8114210b450602e0141c51f14140d03010000b489200000b01080d00041141458000751900b403111950016040d500718101c030703049c8809001c030100d0154058450400c5d80e04908001000d40d8060b0305002000c4045200d07019091180010b1211419141802d00703000301d036a44003403803054a505070388054200d00 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 115525125 1250 115523875 115523923
    0xc030109090203100203040602040e0a02090306040b06010e030f160f0612052d070e03010b0109152c0310061202010804030302091305040210080f010b0d110406030f060602 75
    0x30468120025003070005045503940b51864500781d040b80e009503000c0b52140d500040400003001803c06880d8030500000007103050200c50804652114030040005015681840000d40b85a02804a4103408800901250121415400b030b03643c6d41c802c0400e40b021507048280300040e040c60442200c0003910b40340e81e41c409802441c0070040001e000051300028a1024480b1080801103200c1070a04d0b4000340a245041c60f420040c0700540b1104606030f2680c003e9042510480c6182d030402444421600f0b45010340001c0e102120303080366070400b54000380b043c2119044520180e051903171003210b05010b0441c2a2062601118582c404a4000d441606031500e040b10010000d5030144220360703405402030401500e0b1804c0600025810100b4402038903081b0b56441c10b100560819040f0341010901ca820501c43c2d0b41440c000178288140c052080500300c01b00060350641a80701d80d00001400c58402140341d864580f01e113000f40c0034009144821484900e08003000444a20000d2810101c00b03000d182c6001e002 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 115526375 1250 115525125 115525139
    0xf0105060f0109031203020f0304030e010e0405070e09040c121a010501080f010303031805010e0d080a0603050705120a0f0b1909170c16030605180705100509030c0d030503100902030c0301 82
    0x400c1c2030b802c010306d41e090103800e80328894100214491071203503032143e10700346039080007400f00203490160780c0c001c2e490042041011070b08400c0c6500c50501c111038154440c1d13614540b1080c0c1c0b0b00150050b9100e1800302d400f00003000740b02600c0c041000e0460612a19a0380c03503400441c0c0006040720708001c2601c15000400c0828080d60020840c0d50100d407030b9410748038407921158290741c101d005200690b400300d020050b90a030f1000c1003c0c0c01460b8981d090000f14559225541e8800180c05020b2013110b009810f10800842000681ca0301540701f001d20b450005d01d23042a491402d8222818031011031131102010400c035241c41841c540340e17801402c221419510180600c42504200748203400c5118055940e101003a0340340761240190303c11280810729113071104081c010314103014441c0c04c4aa21080f414010b9940b24a00017500c1c24461400350703251500c501c0000d241c4044400319a0b0000340c24203100c1d09165010b4021031081c443c4040190a0340d65503807002c022484101c03808040c1800a1006105c14 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 115527625 1250 115526375 115526393
    0x6021b0103020d0902030706050d0e0106051e0102070314010c0e01030b09040b0603072706050604060c170405090406050a0507050a0905060307030e030310080c040209180603100e0f0105060f010903 86
    0x42d203c528005110724060340403070b181145a0700300034041030300451102c220803100d0154a51468811000780502450b200c0420405003807040d41c040c0d052914451404d40e07920804c600320086412500c018007c03042803003100e000340503900260700001d0791017441722001d500078040c4808842010b000c42c191075861b902d5170144540050502d5500d406441c030001007407200b00110740c0821400b200c40d464101e4807240c4000441e04594421805100300f80020040d130f03a0040d090b6419160030640c1e00260840d0011806120310542d08410783c00036800040c041480f8080c6c0c0440c0c03040c03140c89000c00854580030300941c0d0078061558000d000540ca040d05021a04004004c0d64000420f4100411354034601c19816045410840e00c50142c0c90214108220124080041c0c502c0c180d41594210328103031040300441e80c08c2c403400002d014848800030208002e030324200a0310b403944d8000300c410800c41014a5a442c0c880c0c2500c20003403e10343c202408220246070080c4241541e1105031191404146540d42d14000 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 115528875 1250 115527625 115527637
    0x1a040204060504090501050906070903020109090203060f15030609151507020d06090b0907090c2f0d02031305030303010e010e0a02070209070f11010e0606120115030c030c06021b010302 81
    0x15250100040c20351038601500c4c8105119000209540c90319180b491300d041001890361081103401241040984d8101d160070064940d10b5202580da507030391501144003030444c0b000154200c0b1401c190301300c41c1d1003614081d5000b16011241c400712510340117402c41884102c06403090784070b408141d12f0303400340503000b0040c404144054088004201251200c80c101c070016041902c0061400f010450b01500921140303001d807401007010000c3c0038580707a000f0500c1d100c04030428040b0305540030085c001603440044084401100301119030119132060000d4494110b155004c4407000e55007c08606484c020013543d040e5140440560201d03071a14030345006070355010340500c0f0b0042d820011103015880f002405803140f170143d280d944641044503030040c807203000500502d00c81d902d4080e1903d0824004034402e6000442101c2c0c602c1c0700240c26604070b00502d0403411215200f82d104400208200c8104c201c04200ca024801c2480070550703030034081c0c0c1c4a5000b1644c0d00401000140c607851158029800340003 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 115530125 1250 115528875 115528879
    0x9060c020103060b03090c100f120b0607240b0301110f0a120c0f110f0606010e0a090618110a080103030302030c191d03010c05540d1a0402 61
    0x6100f80d9101107164044c0c1c41070b01d01d1450303500500e181c54800d04000707400810703103a018030300410300300030041c002440c0d8820340e407100550f0341e21010300c00d566966100179034100c00e8010308031040305041201c51501d00c00607148191412420013424800a02d0184603640c4a00c4800f1029450b000381c000e000e521035800410395005001314141c4500301c0e5205032141c6003011038540c03108a000340c5c41c40009080550141500300146c0d0203001c5100b1701038400b14121380c00030400e00300f040c0048410740000359030b507640e034010340521480d215001918107007100d00c18071540c10623007080204440c1601c0414440c415140b80001043c44040104002403080d402107602241104959081c002c40e0200e02110a0164004000041c5000e0521401d45164036841c00100310480003080300c41744804026010f0300038021040d804e00704844041c0c0d5106000d5056817a04442945c42071024600b41104035081c18045d0070b24201030322913503030030b0307049040c00280018400d80109a00c030540c252419081040700005200b01d07 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 115531375 1250 115530125 115530131
    0x408060a1808040e0f0f090c13020f0d050f0a05010e181504050105180106050d0209180105100312020106060801120f020a0f033507030c1e051b0109060c020103 70
    0x15010507186000f8001810398a45400030758103203c02110032028014200e40c0400104406000f0030340d1001403581c000361001d41d00305000046101c070b000700030300426070b50301030b40c05c4000f51704003181c0300542c00180316186010f2010300c103494003c4401d080314403d004004039108144081042d40c0c52901002e242c26a04000303d0b0005114070300002001072003620f01b1550b0783c0d103030030504c0039802c038400080041c010520002c00c203075450400002c401c11516031029008000300c42c0800c0e15844c01c3c05141d000c1a10341d40003405079003800c602c4404a1161484180e442c042c0661441101a10601900088a550356110481642010341d400350450413000111080e90404a1040058490001200041c04113100c46103e031481c500f031194402d242c4e40750310020300000c0c20280c010b1051407500071000c00c0701c0c2c00580361556102d2905036482c106d00b0501800c0440c0000c9140c1580004000c1c500304076101c2d10030340c0d0202c02c400380700044502841103c14042203201c101400502d01c20000c40070b220780145004 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 115532625 1250 115531375 115531421
    0x90d0203070b18011401051c050304060507030905090c030402100f090317120106030606090902031b0c0f0709020702120f060610030b060d0605040e0604031202130e09100b0102030408060a 82
    0xc40d003100c0c152031002004001120040113980f51040c86580705102210400d61082d0f2300369035840e12849103005003010300402042c86001c0c54031a0b1181030290001514564090500f107070151410f8004540480c881c01e4a10b4103a074810348980d914038084142c64846411300d0713040d5590400e0f1043c50b2490307503503c1c1e80c090040d00c2c11600700c994002c0c000c00c010b0300e000981c141004001410101d18ae04051744a5004209100401901112541402d207040441c2503c400c1444a02400c1c0f00348140d812801c0d1207401c4c0c0109440c02c0660007031030010310807070b00440358451000d00103032544c4a4603003845003600710000144160415009100401d00d1620f00005c00354410000225a03800016503125203a44e43c04090006003494400c81903414200c0005190501d4143e400034852120284c00c0c080d40d41c0c0104010b10020110440d400250014000c044040d04e401100030b0758036000008035820f1903007014010101540044103c4043d40c209402508581c2d55880c201e03005003140390040c44188058a080b = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 115533875 1250 115532625 115532671
    0x60f030708011511100c050903030c01021206120606040f02090d0308040203060a060b0f0715022205040c0c02010c050c0904140f06070c02041e020d0b010206090d0203070b 75
    0x8510490300da45a10169504000000e40071210380c010803024460861018154a803002070088012010f1034008542c000504200701d555020354503e05400d48170116090400003019006054101c84c212001100c40d50307104100201046100e4401450b81c00c07140c0070940c1405c0c290000d1880d1901c041700940b42c2040310010484171030b940b460940c0000e081005201c210715007840b1140d0030004102c8140100d5042490780c805500c11a0721280030480f000402604004401d02c02c108240980741e000c64940e5a00c40803801101040540c01d10400c1d10740001041a1800b84500460840590b40b0510a00510703030055814500d0400d042d1001c0c03088521051559851420b40c9100c1ca2040c0b0309442a1840d81c0a060310b408580e0703100b074080d40c1040d000c000c83c10750f1107000880c00350340440b400300d0b05d10300c0c0c0003540c045403000c1040c1c486800c0c0005100740041805402120609000ba0b0850310655103811015480b540c49421420040c2c1041214101244c00003c255030080b06402e80d1041012401b03027 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 115535125 1250 115533875 115533877
    0x503041106030903041d071407060e1f0b0103060602031806190f1106011d15030d11070f03170705030d240617070305070201060b120402030106120507060e060f 70
    0x51800c295a0001074140011084070080506d1580b0b52400c4004a041040c4090508582000105182600444c50100340314054110815110080742925550042e644804030f40c4042d1440c00c40445080c4000b20100d94032034031401d0121481640a9800c0c02c100d0b00f842c482403d1035017201751b40038a05201712044542000040001010141c45014100d072110b00060000492107030004455040b10004010260741c01400300e0040400d40d11040300c50707840840501408010058882d010f01c00c05840c90041d6030080a9181c2c0c60914a00711002d02d5500c00c003d0608414900001b403400040310b400c0c0d950210828040e20b400b511480030b03a03050000c480300040480d41720000e840b060b0128050f059143c0501c00401a0180440f0316088800c8401040030300304480d0003528078020507607a0800241901d1003075200c40042c0c5145880950345108210044400407c280c0b0180e210703510308400043d10317106c1a1086100f01d58071001400a00e0300e0404161401118480342640210041105144404c0544 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 115536375 1250 115535125 115535131
    0x5070c0501180f08060f1b07060f0f05070f020f120d0908071707060507050403050c10020c0a0801200405010f0c06091403030907090519051b0309030309010c0f0f050304110603 77
    0x80101664a001c2d6120111b106e8007074000c0540e104481203100130550000111158550040408a003a807500d2961030000d00405103561480ea1400e02400754041e400007190540b07150741c0d402c951fa00101c000143c2e4807044000205140144200300034802c48107240c112060050040d00c0b83e81c201001502c0d0084107406190804920303502c001072201c00c00c00640b044079006025440c26505107421552140d5131b0b84507103001303d441000000c0841d41d80c24400c120b10311001d140680399603070f00360303644034550f010345541408400694101108060040d07108030aa40807208144e6035a250717480d1185090740d00d80e078121021748040e600c0b001050003080610b84101500b945000040d66285414852641407080503040100942d00700000e102d00340410400081d881036000100080c10780b6102401c515070080b40c002c900760502d01204010805002101a511a40d90721000f80301c0946502c03011207605844007124404141282c021001051140001e1903105200b4100342101d80590400140550012 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 115537625 1250 115536375 115536389
    0x1e030304081c030f0203190b0f03010606111506031504080d0501030f061b0e0f01020c10020312010e040210140705100b04290d1a0907030209060105070c0501180f 71
    0x4030104440c001c0d0b00d88109084800c440408600311f05010303542c6902c40300d42410040007035407504a24580d60742c403441c084011040040080200355518071004d00390703038080102c90000d400380d10703948070080c00010751403441040000d02410041200403116226010068000e543d4483d0500038078890410b01c0c4a068007070350080f20b8020a0300c5652401c90107884000c0c1c2c007240a60510420765070b681782c210100c201daa503030884003d807401d64001e0040749400e0020b0704295028a44440103040c50f6004801080b1114915101180e1070782c0300d021004481500340d500940000c03101588411303c80c0f01e024406104207007815614503200c100e4895034506541c480000880c140d4071500807041d481c1501c6900340c4403620301c03511140f00e1412064516104241141c80740520700c42000c01d000c0011803640c04210b02c1000c1480c494500740384003184c1c0d64030f039a80000c038007404c1b59101041e041c1d0f00075001d5414032a404010440d000d030600004403140005503104003994500c0400204040030745c0ca84c0ea5001d4880 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 115538875 1250 115537625 115537663
    0x110d0801030210020c0a170a05011d01110f0a0f110307150c0903020d02060c0a02090c0406090b030c0d0e10091505010b040302060a0c0804030c060e01020c0105091e03030408 76
    0x41d4010003950500c42070080d01594041802400c042c0c441807130220441d00c011390049070500203161170703c2c1003004c0c2c40740c010950752030a1900c02c1040b0071013000b00170301669000200410200c207101200382c0e1042d08141400305905100101c0d12174443c000c0c1c044105c00c0340c501500c0782000035040510307581005d80c00302c2c1c00f0701013906120088078088c840c03652444070501c1c00030089407541d004540581e0000902a000d04070001c5d1f5204010b000f0488222515806004840b0341d1074101c08a8540f82c20234010300c0006004020000b500130b02c4030040d6030044400381d640e20302c1c25a4001e6400c0081041602c0941c2c180114103c070b100034030302481080c84a0f030180d5010219030b024100710b04110340c0160803444104070180000d02c050f845810513695172804a0800d21407024860034101c141d03000da9800106952021003010a190364004400d48800201380c00315011580004010f45480c003504c281c954001004a8800c00b800041c0324580c82440b8014060301e00d05500c0c0d115140c20a900300c180c101e41858 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 115540125 1250 115538875 115538879
    0x1603030804050c090c1c2705071a0912100c030207020f0a030b040308150a1202040b010c08031302150427061a1c0614130203010305030906030403110d0801 68
    0x50603c80e0025000013152042c3c0303d0b00d014480d4040342d000d201030784144007a15500f600304590b860340c4254441d42d00d01081d600c0e9020b0203401444404520b60301100e460084560000e5550708600c18a81f000001c10f4880781060404002e10041044051150805100c0c108045490002c103218101c001043c568003d6030b118102c3c0140301c010001c901c82c80f4098000303500c080012404e007203251500f099151070001314a44584101c90b0903c6660090b440d0b02150305000042d000c5081082c2c1c000491080c5d40c241f000070158001560145002100580074200810003d59252006100c4139003061005010151340071056003100c0c1c650b00135410200032000340c24030001608032041d0f8804a00020000c1c10701c54a41011181c0041c042d400500340d800020205500005e03607007102c0c0900a4415400e42000304a03a542000001e401d5114080d900038a03488201c446441c406000700d074140c03904400214540030406051082903440140b0990401c44e10202e008410502400000406c00c043d98450138030354 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 115541375 1250 115540125 115540133
    0x302090429060306030303040605071106090a0b0a0b010e040b03100501030c060201050906040507030b15041517031303110411040b0a031505090610110d05030901060e0c040311031603030804 83
    0xc0c01903068980b0a64050040252981c2c0c004122070340103604c5040401e05480b5803c0030f036070f2003540b2040d900342c500560041004540c00080c0c030b11079890140700c1c1d4482c1901e40054100844210b1100d50340045c01c460350401d21400c1580000c01c00c960094210780b042540c10414804407407007038108803450414004100144c0c2c0c0d0900402e03800c03101d08400703413256040584d161a9203940d1840b0007041d4041e0100007422102c4c00c10104c04500101500034483c0c4070050750040d080341140e0040c0b41c031403c1c80b581d418039200c20000580341c0500540b01800a12410f58813955101c00012154940c4140ca42410084078462140a8030080200248940d100c0140100140a540d00841c0c400c1e081c1241880400a555640841c039822441c15241c032082554a03502c201c0e5100361014118181d807140001e6800916442002144102c080b04002c01c5079070740b540d00590b98080c0c04d807142d100c142018802400400c2d007116904122440040031505a01c10300c2d00e1079080081c15902c103401040318038003000240 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 115542625 1250 115541375 115541441
    0x20403060e1b0d0f0c0e0a050702011b021e01020409020a0206040c06030b090c0a0e030f0a020a0e0708160c0506010612050906042f0d050303011706010e150103020904 73
    0x500e40c50310702c04520072400c40101c0c3d804400c0c500d0141544404015035001d12091420441c06000d551000c0d42d56460280c0f1a90050503040d0750500041d813a220b201c03484c00707001a400c41183c02c200e034007608039203080d18580803a155055201c24404e550800000960080c144010660001a40c024202526141c289a03042010b594001005d243c1801c00e100001c1d80c440d00500d0f03000059291598440c010204119071580c0f0107400181c05104001a00c102c4000c0080c2403844075101301d84d039110650302c404104001c208140e8070f000100e600c3c000030070102c4101d0022041c4410301490041921040b9407a1035190180a9004501107002c14205c004800701c1c600902e580542010000c00c20350a0654860582920042540c441880c84400c68080e07140c1001170391081d500000c0c001c1820710428105642ca0340d10a1045003070480c1312400c03001c0c0300305001c41c0590495030403070084c503101d50f51894110860401001040e04040e800c01c0340481643d21807240c860011201440c190341600078000d00804 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 115543875 1250 115542625 115542643
    0x61b0908120a0917030d0e010218010309050a0204240e07090b09030604020108060117091510140907030f0c090f1a031f0f0305150a1a120709020403060e 67
    0x700741c030421a9148031500f01035142c0407038079a00014002d6541205513541140900b1800342001810081300c280c24082c150094104100702c00350300c40c041000d81005504658102600a081e9000741001c0c4000d854554012548030006611000c012804045400c8050740c00d500662005071210050201280e84040c980000e8005003601d2031074070000c040000c1c5c1d20300c00104002c0c1080f50400001d80644d10600400140041d52403416640d4240072000b42d40351031441850480402c003640004020b50b850303862040c219070781130312403104081420b020702500c4c000003000d00c0300741916004000f0102c1f1042c0725030b40012645698103140f550800c01240c00c55807840c1e10401e031503102074003030100b12902e42080304d4110184100b10b0340c80321011140c00d551807086034400301001100c8000003003400408914442143c20324003602003542c0e030300d40b034180407901d90790b00c14001d6968815804040d4101176000c80086ea802e1801c59034000d582d01d248400f070380d000e5081100c4d0f851301c0ba402e02c0440f2504104c100e00c = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 115545125 1250 115543875 115543903
    0x12040318030203030706200a0507052e020a0c0b070e03060a050c0d050603102c1f0e010b0a06020a0219050f0d060e010906020403140a02060313061b0908 67
    0x30191654000a540b400b8001c00600b0702030307071400701b08090140d910b280384a84041560031500c807260050081d00c00e0b08841c0c401d940b980036030040349249240151511500a010030305015086500000c40c00c02504044428801e2058900404c00401c80800b000303032180c0d030b10b40d4698085500c14030505090800141c01003012506003000e020014080b1420b5400c41d0300c0f042800541caa59000000c0d203030424500344070381c40c64030b031054006105800c8402840e00c40e100400300140700725640b0000355500c20409414100e184107c140702c40c0c3c5026a00701d0b04864110b54000f081d030b50101800604a081140e00c0700c03000d41c0c000c00b4401d0860038003a03030311486100d20070503d40c02c4c01e14103000b1803105888540418840c8009149040410071035501c40c3c0044e4000d54000c00c201c850602c1d041c8020340c004c5c00203030b800f20348400d0075030762030440052000802540505054250744901c0301143c1c103c00c10b00d0b0100c40c0ea60304da502a1558076284d440c01a08050b882e40c03541441840d01030080d04155201110031 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 115546375 1250 115545125 115545167
    0x2030a140907061b06020403030f090f0b07110414090c01030c0305060a060804030908010c0207030c090b0102100b030f0a15050907030b011203030605040216030206010b1201030b040512120403 84
    0xc40250110381c2c0c008490982c00d00310b044850441008410f40f69080f4024055880803030f000c002d04d82e02012a1100c00c2d1140c17540c00c1803940f651603000d01e40d41e80d80305528500d4801c0140d8400144240804402480090000705035044112100780c82842c3c126010315556000300c5a04d41a50b905000798045002181010000d07414007001054010039680078210500c0710004c00302d030030540b094040a00a1904100802c088986100c00070340f030304040e10003501c0400034840f011071101400d1040001c5400140c0080c600c105291200c10007500d0b01c032042e15414025100c0c1644040c50600c0401c880501c0745101c8180450082e0a8000300e400142c551007090303008107003c2c400580c00c0a200c50550f400302e1001502d0078614a021400303030900d40c000d260070a0000c08d0b0903005042c810309008000f8429003d0381e105a032074801c9003149000d1195500300c2041d40f4001000410089105641c2003409031080d101c00150300300b03c0c03101ca60b1003444510030311440b5404100605038004050740348c0154288001c = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 115547625 1250 115546375 115546381
    0x15140c040e0c0f130608010e06060c0607270602150a090b07030213030204060303050307030e030a0507022b03110f060c0d021308070914060a0303021213030b0a02030a14 74
    0x9901074020042c158003200030001440b00b9440c0da000c00352a01448210910004107848010040521200303101361024001d814012904602d865019943d041c180c2030000c00d52983d03034a60846158030300b120a090b110599680c400004c100030100c00c005010f01384c0051000c52011101000000e80041c00b42d0100e5203003c00740c40c0040d0340c814070705800007131324039002da128148114840742c610a1584003d50161414074004109600b01d000303107110b04060b1f101000300c00b800c0c100390744e00da205154500c80007131000c028400051901b21881d0800030030700780c106841540c6690362284500317001e480580110742000041200761100300070340c042c000d5030302c005045181480305000e400c078003802d21a0514942c01080c4111102c0340c2c01907100041480c0e904440905541e031031007100421241e201c02114100c0000001d00906204d908141240c0e419801028001c2c2e08000300d001c540c0011440050391708041d03400001054002010701c0c01911801d00c01030340ca040501c441c0040351222140106c07498199010 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 115548875 1250 115547625 115547639
    0x90e0108010e0606090a0608060711061003020a0605071b0b0405030708070608010e040809130506010f080c0406140c07230405130b060310020f07050d1704030f030915140c04 76
    0x381139040325003170f00c01c0c2c134140c2c852a404001a15107900950f00b1486810100301e03055074030400160b0551003a8043e201e49444156941d124651640006074114213109401c00200d881600188040f6000d8240130041c85c82e10000402d150303645500c410000100842d0a001720316007070080d90010007454004004261602d103000e004000e051140903820300c6403600050500031100200c40700b040300203111901803c903800341e040003400c0c240c0d2140d0020310428659101d4034044d8886601402c2a40c6410f400d0902d0034000710340b64440e041d038030390943c03409100c059400341d0100b02c40009807a00a00c0c1c050a01d01c0d0000100204649420741f0348203508003818400c50f4241e005210356500d4000e0303011011a034818000c607140090103208038070500d1001440024020141015082051260080d282c461100410407510500c28074100b92140801c50b010030f00190082201001850403030402261047d810f854040c0d0b800b0007040c10654076a02d46011f0356507810085403042c1d00c11801400d01e4200303810140 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 115550125 1250 115548875 115548883
    0x60b031c09140406121a010b07050a0f021f080a0f06120f02060906070b19020a120207210c0303110301080a110307030b16110307020105090d031806090e0108010e 71
    0x8140319442c0221420400d654803a41c228802520b98810131a00a020615102003d007058500d007161440743c100020a07143c0c0510204c4809540042c02044111115140e24959113600034040f81e004580b030190304000c0740c0031040d074100d00012b40c40d841c0d80351a00300800000d941c1c04925101e4020319100c01484514402003000f00010f801c048021400c49080c40450018410800c002d5409030f00410303003404000391152144c1c450500c040f0140400d03d030080c0c0d10801d0303002e5a107698010807a540440030072000c40e03902a00c10300303000e40b10010000c1c14140e40000d00d820600780c01030000d002001c02742d05050309400352250b40440310f100d01d40f03198503000c0c2990700c400100600429440300100c55103007660701088800007558001c44905c10a0034620045003031040c0561ba000c020403013400b0030400240c004010307258444c0d0107031250b9190156000030009803c500e214201c0a00c2020002c110501e0404180340e0050401e40d165003c4450034610590b5503100140c0c44101a0780c1000b811030010741002c1 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 115551375 1250 115550125 115550129
    0x303030e060402151e040f08010f0902010c0212010f0f05040201030507020706021c02070519031502041d060301021c0605190b040b090a1205070f050111070e1b030103060b031c09 78
    0x42500341c0301c030361000d05456110749142c420098440f0201d00407d0b10007401110f0700c21a10344030020044101d00101c40d1003a43e07482c0d0006400726507074406200240c200001c088031365040c0b0a00000d40f200b0494a07040880310310002c82d00050b6900c1d42000110358041c414517070045114002411001c0ca4420000d60724401c0b40385050501100c20b080c03480160082100d04007801c0010b241040c410000d285040c83d181051001b6200801480700c55501b942135071007240c080d2024400f0a00e40c0c41001c002030140c0c01c0000e0a590341566082040c0b040c040d0030b50088040942e04c154000c510700f86008100000501070084008141c00c2d40201007105546902c201d4040b90b0b50f00e44620340383c050303020004100c5002a804040c4000b280341100c02007040100e4441c2c181c803a8030a40400d8141c0b654011210790882030030300942a841681c091100401c60081e50303500124a0341042001d1110f03569602c2503400a0b4012542c10340c507000d0403c8607180030b01c201115040601c0b16201c1e030940d403ca00403d990564 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 115552625 1250 115551375 115551409
    0x70605061e1e01022113060f0206070e0109030515040c091103060904031707032009100309060b1c0b070f080f07050706050c0d0501060e030c01120e0601030503040303030e060402 78
    0x1003602030070b581d00900c41e001c3d540c0c00c20100f5440119036015441080d81c020002d50700c00d283c0348040856254000e158129465031240e00801e079550320980d041d03402c0580b0350b00c02410700c00006000000641c04100e4040c005210f00e500e0387c1141014a85042090956040045100d0403d0040c500da1070305002038a901c0581107030323800559252400d00b561000380c1c0b40462500c0300050300800406a030180c000d105160b0220200300f503d90f12107000d40360940650940d2035402201c5000440303c05100b500512145401140009402455980055400d49050344018290510460405c061148030b4252580c091410300300891034442c0c89400905000e0001e05442040c16000e010440151142054840036035014030308000c00c0c140f8941e06030760b0b80c000050041c001e905000000c01c00130720400c1d0500c42d101010b4005e0249005490056900380600e2801403681c0e49e81c0e90050300d03500b40c00c003e01ca00941c061409503a8480c114140201690001011921194041c4090100603250103640c0e081e09254 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 115553875 1250 115552625 115552669
    0x21060917041211040501030f06020a09180c02100c0903152c0d0207180c0e150405031212010504091a07020705010e090c03071b08070605061e 62
    0x1651400301408003102001500400c004680422698240240d103402c20340241c00d05072001c0b48400400007540c03000d010040250442010b6007001502c02e80140104035614207044200701e80310301c841d20107600c2c2c002112058640718090100c1741501401540610001c02e41d051242001454000d01100301602c0018400000c031114042e08020b0740d403003040310480b08000101c0c0d420b0b589144e0300d102c04815120a0071409000c1211100600007d030440843c1c1c4240002d0300202c013028801002003490341101003d0000494498003035580c0c09000305102c85003c500c66803078034101002c3c146841c80b04d0604400341e02040003081003400c5c0d02034a4504580c030031200450740f199907160900901403041c150034644054581031101c400d401050703802c1035a00a83c0c0301102d0790302620401100030016204940142c0702000490062446500c562010707000161030142080800d075500d403100d40c0a1041690044d80d11801c0c04618074010f00401c148100031a500d01d01058140001544400845030b0f81340300b010 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 115555125 1250 115553875 115553891
    0xa031505030a02012105070801051f0c110102011104080f0c03070f0b09150d0605040c0201150e041e0c060f0f050306010e0a1205010504021003060e070503060123070c2106 75
    0x1010200b00381111030440b81441b490030b2100000e40b07a03000a01072144a00c40c1c05040c0f102e0b0f56048180c0400028140c0d954030300303600e460344810301c0c0001803100390390455488901d00c505100802c1c2c000d10080c03184400401c00d4441001d121410869111070042c860f8020003010800003c1031070a0600740d51a5000403a56070a010f0000b030b042d01e50783c42499030031060108503801d4142950f400901202c500781c0d03003408400e1010760202d089601890102d1440030f000351041c0030700c00c207151a1582c49489841440c07108005072901c0064850740700da04440d0100700c0641800701c01e6002051041c51922030500701080f01c05094041c10310b00009210604000d040241b2038480c3e07450740c3c1424020503508044c9101c801c450b0030618060481102c00ba80a10410303c4502107041c030a1050b0411a0740010f5015100d072540c501c205c8050340003409150411100445495074064080504116042d0500390140c0d203800911300b1409403070050740029808040c040e2100030040c41c00320341c41d1180c0e03805000001c12071 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 115556375 1250 115555125 115555157
    0x10080711070f0306090b0601090f090906020f0c06090d02030a120b0d06020d0204060216120f1110090617091c02030c0601060c0308012106050703020c01110a031505030a0201 76
    0x4001540140b9100c1c00c0000d001041c0001680003a105c1c40c0580d00041c1c296954000640e50720b890b82c492140c540b10340c014100034030800f543c0b0488030340b0f10a18003d403400315100070f9016213030803010004e440ea40114051003104038003080450180302444c0069810a848820003616070701c8103209605185480729080d44007a51521103d5410680c03001d800c40d201c11003007002000a400501818015104045100d00480c0f44814060121003402a40000400c0c0c15500c50300e03803015988080b900994000c402040300d558109221003c984a45e40700c6841c07524049000740104c0e03800d24008140401401071040b915000f01d1010400079003010210415080003504031715620070104564007a0190100200d10703c1d50040810416034000d6071110240c1e603c0d102c103030040707040254604005c602000c3c1c1070701c00542c19400080d809a0903050060030030103612025420740341e50ba08000110840010755040c1141c00d449034080d60758001005400c1c1509200100f603030713000082c801034184580b0b0b038a4480e00c1 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 115557625 1250 115556375 115556383
    0x91f0806040e1c021c0c02031002130e0109091110080a0c11010e030c010e15041101170a0507080c0c25080304120606060807081f0506040b03100510080711 68
    0x41911148603040801040c0094a814419903170310341414108130303081281c52207207070a220b07881e80007405480800c001c0030710500294000110526103000070000081d0409803c0c070000e000b44040740700851450150302d02068101c1c900f1031518032441c0c10b400b1100b01c15a110380c08590081c040400002e900034084030544039141070000800c819800d00139447c1e080c0c840400608030f80400b0034000e1100740d00d1480744030740314190260400200c40c100c3c1c001502152800001150018040c108024000c10400c1d83c42c2821901321118015079460b9000d00060130703482006103510041c101403203420480d02821103921030706148a004507140c0041402c0c4446001d0b00521001071840d202121b030399a5407480c0c02410301501c07210950343c5a25080000403124000d1805601c9014140c0e1540c02c41d070b0b00c0c1ca481400710403944e032075007140070480807000c6050b4803034200410180000180c49601c0785801201440c10440d19004680500c82c110218200c180e000507541d40c0014090800e0510b404010410a2030 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 115558875 1250 115557625 115557643
    0x80712081e090316080c090405030a0e04060b0c01051b0301050a0501051b0601080d08010b0315190513060314070b070305030924010302040f06060e040209030304030b0705091f0806040e 81
    0x4103029090307041a00707040640c90315003114841701c04d50b220300341054204004442c08032005803464000704940701005200310740107003801200030400500c2988a00042480350072070381e40c2c0405ca0395180107121202c6030303400110075141d02142829140d50704100c040f07000e12209228141c1404008030318541500018080aa00c0f408044121034440d0781d20300550342d41e6000b100304c04002c99119000442c88061540480c2d125a86040c141180303188910140181c41c0b03003800483e03200700c1000c00080351560700c1411301c10400d00542000301303019003503051115404640c0c3d40b14455550255200f042064415001e840f480c0d501402c6c8a070302c0384c1d5404c41e4107003011000540a41c0d0042c40e8901074403030711172018005059a0007079408110b000c600d441c0400454985002d81c03408560a8128550070785444d40050060b00300190030fa905050703595944940b070034816605200424004a10182c043c208031a04152005803901d8800c3d400c0c3c1007e002074101d08000e804540542d490340310301071002c8010040c200f0 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 115560125 1250 115558875 115558879
    0x1050a0f020a1e140303270a0615090b041803210c0215061002060415021c02090f060f04050d060624020c011103121f060207080712081e09 61
    0x1580510f500c400c1049840910001c450601c1901e030b9a150700d540c00070503240724566030982454060081100200341c480c110010078045d104104400e0002800d5000d480009100340109901392410902981c0554892a1106008504d4003400040c05244450300082c05501410b001005545224a031040c0e4016422640c02050910066141041d030014415142e00e4549034120540d444034410040003103544120400180d1210307000c00c0c0400e5003035080c03418200402800518012200480408821503110034999050b0301003542c003441c0c24441503840111204640c0140b5100541446134010700460080d603000310804800d070420071049a03c9500984000d501c200d000c03140318880b010030070141c0d420180c01806040b803c00e03400d5004101004034101d140380958103082581200381108400101074a03514480410646444151240d4106c043c04140c0e015040381820020003902d400c6950384000c0c2c0e000b045904410101e8100707000d80301c1e810f4104811486000d90b0341c5c0701c50041d00a09080c2c40d = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 115561375 1250 115560125 115560143
    0xf100b061603080906010603061d0601020313030308010806060d03050301090b0a0b0301080105040c051c0b0c07020405041203060b030c030420060d1406060405030619090c030b04150b01050a0f020a 86
    0x509042c3c015070010300c076409000845800c1e07038940001700d099804502c0380c101b00c81c04028901c683c01140700b41165001e80b0620459041c5000128146803092041d071080c0c011465050040c050140709101440d800381050f16841c1165a00750f4004220f44014811880103c0d0f42c1c9501038401e81c0d601c5202c074000e0401d21085a160b58480c10018003c22046d20102d541401c458000145424104580c3c00100703000d000c00700c10901c0644895013401e40051040d1030305681000703160300503a01c61041e01d0040307000c0d019081041d82c0240b000b504503841d5400810801e8001d01c04c100968416504881e4044d41c01410040b0f008501d1849801c0742292a0311180d0000010403d107010f000c140c1d0022210b00f4090010182d1a12180180010f601c11401100e4154014500082d18002c02941200c1c1e401010100056118a2a160341c0c2c01c41e400e0740c0040340c3c0050140f003413105110400f1600c01c0f820750b4231102044992542d0002901c04c0c456084400103000c088244002414024401c1403034640e0044199 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 115562625 1250 115561375 115561417
    0x1b0d1e140a120b0f010815060f040f031709031b0103020c070e070207140a0501050c0f0105040602030f0105041a040e1002041202100c08040909150e0609010e0f100b06 73
    0x64150041402902e06a40c5402c040b40d10900e000a210410590306848022441d11015010340880c604410345036048241040f011840000501c02000103080d0030002d032039100d0441c80e080010340605803030000002400d0002110380c0d50042002598625104d240302d462440c5100140d01034002c0d0300141005010398500001c11b4590350050612980160382a0751f8000d8603004070040b107006040f856034000b0701e1040b0a0005502078001008800c101804440711808000d401c00c1c29900c04a404584c8103401001f8000740030040005a0f0140500700c4041c405c1082404e0099411090750062902c15601c5a1214860701c10a000e00c402c00e08a1780d40540d81c480c0c135410315910750321308003034128004e9209140f0a910a03102d840801c103110782c4880910b10741031078040008090038201c0030544400d034441240d060040382d184500280000380c9009003196140030245079084501c507400d4071000d904241d98914203a5000700d00c0c40d141050098001171141400404204240a4020452003c601003021 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 115563875 1250 115562625 115562627
    0x40501090215040803030a0c02030906040803180603040b060907051e040509011a030c0c0709230106110307030804170a12050901090c03030c0302010f111b0d1e140a 72
    0x569403078000d0301c00724240040320b03401d000d80344514460070304250000c0c00800c03000c1801ea000f094601103144110303814800ea40002440e141e1180d84032014a500000f45030348034040c21410400c0c01c46040315514194640b94941400d05680103145501c40d02e08500021103187c014825640042c170741c510403200c03c501d0758484601560050080d144125079142c00003440d02c030311503114141004176010341401c5864501d10440b45802489440105000304000819444168410354910f00d03084c280c80c8800c030160280ca6826901e060308076000300890b040ca0180810340010403180c4d410383c180344c003c665a40b0340c202041280700f14081441ca210002503816281c9500c5103010a10452100c1c013004552a000303003581c00c071820401d00a012280b0720300200040b030b015120b00c0c108a802400046628010244010215090401400200360b4007084048909040300307075880851580d01e0081268408a10b4007800042c030000e0030f00120161544000d00d100c0c410f200300c50154060850103519140b8041c0 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 115565125 1250 115563875 115563881
    0x602030c010b03010207050703031206270c0e090106140403080c0109031e1b061d010e0c01050f03010e13240e06040b040b070c020a08150c132903040501 67
    0x3518411560070141c0000711031406108942c0600d601a0040441c0e910310350701500c1000400d082202d907940d481d140042d032800214502d00c1c085409020050064500c0c0f4446d01c00c68a00c208200c0030003d550301c03c0002d98465080003419904e0508100c044010003e085e003006203c1c03034100070a085404614040060070540007010006e101361290f84130416001180b5241014001d40a00000c12150280300c5070010401550a01d0703010340e40c042101d401101c160340b03444800504449240c3c0d500d00c14600c1042c01845440d84074202481d29601c0e000c001c090300d040d10b0106009101e164241d000108604981502c000303206240d2240c0c1040c502c400108085c44000703014100141c2031030030010f8902c1c100c000402c00a10440d8800022240c9803a5034403912000c600080510741130009408200000d0399500c04402d004142e001c00501c410540c41c54410383c918006811403d00f42014019000c203550302c9408801038810f000c1c184c070300c0d6201d041c1705c8107400da80b40b2602d6080088000140000d008040d0 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 115566375 1250 115565125 115565137
    0x305120d060518040b04030e1002060a110f1b01060e0403080f060a081f2309070803030405100504020105070c1418060a03140304080d08070f03090305220807060203 72
    0x942000031503540d00c24002c2030300c3c0c0c1e484160400e50007280000e0015044030b10407604a402883c0400c01848181c001c03464602c02180030a0143c2d00080400c02030b1440b46c0149013154410035142810100044107400239800740f64ac503603e80805407800c02c504903070300f503224000800e59483c1c448401d050a0030b01400c1ca0b40b054482620303404440c0c00041480c02c18080b030340b007140c00c58030007400119400415000320b80001e50b0f407400e0302c0d6102d1030741d50b003000424003c078601c05100c0d40488900e070030644035407450105694440c00c0290002d104210109001050241d0034114405000c100e0796510300c01214240f042800062071b01008280114100b11150700e185003510050340c0504101c070b03c1e1400c124a0340d400b1680690700031b804903000d1000410010040d00c10440c2401100e0805803224450340c20402622103800c00070b540303030f400c0060195100b020840320f0519402c08100c0a0f10304d8030018194841da1030304102d03100104071312443c2c2c0034100b4810f20081045605075600c240d124200203450754442 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 115567625 1250 115566375 115566397
    0xf03060503010b0a031b08030316030608060408030c0315040615020609010506060d0b0312070f020913170c030715022a07030b07110a050d12020304200604030512 71
    0x5010400381014810320703403c602c000f40750349075a510f5640c882c40140240342c5409100c00750f110000410300d82c02c0006d180101c10601038028a045032403002401c8400c59803001d44541d00100920000c40c400d881160f40001060000c00e6999030352a001c0d804001c580441107030060300d00070340001d002113501035170300110907180d0944171151900c000140c281c44094411943c484800c01c0f001c2401d9803a540601c09214010b010390b800d2058000141810b500102c0040d13a10111060440341185012071800e588004802928040c01d6000d49568440d128000581a210b42000034a2080e450017001690307411548061301e202c51801030864440a50072000340020412080c201d0369208031301c0300200000f049030a00040c04401d10f107031107201d00c140000d0304d20350903c0760043d05200200028001408440c0c060401081d1001c41e05100601085003560b203070700ad6500c1801400001500d41c01d100c242c0d88024000e03001c004804000050940c429a40000d2241c401c50780d41242c08624100030b400c85180b4 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 115568875 1250 115567625 115567631
    0xd030c0809101a18160503040b06010804021c0c0f08030c0312060a0f08010b0306070c0f030e060d0c020105150406050108070c0f081828030b06120105070f03 69
    0x20280003a222450140e030105070310341103441c0c1c22802260030392045030b9840707031490700b0b40d800c05000010451103800c4400b000da90741c554500708605020303030702d04a0248500c0c80c0f0b00140380d03140648440070204405402a4104060300e0045070030b569841008420300b0b40c05603282400c09000b440c0a0007041060b120311540f02001c03980016140c54040b060366010b0b80100069890240102e00d100700c0304400800d090b602590180c00882d8481032441100042c02420b4000644807410008041c68248014000c4e402c0003240080500007a003030040000e5160351606020103182d03100000580c1500030584450030040c40d1180e01c0c000c1c1035054018038011107074003004280c041c10003001c0c070042e101075024040c049a40d007404164900d00c01c00c20341f242c260080214255203039030b0f90346005080e0302806485208108500ca83c40c42494400030450a012704a9050417156178106002e0403000401e1001818405525000441603107820560b8a16880e404008010914084c140584a07080c004415000246 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 115570125 1250 115568875 115568891
    0x60a080a0f0e030406050c0f01020714010b0f0109290c070e0903030402010203030c0a090302060a05031e190c110a03090305070b04060207090203130203060906071103092103040f0303020d03 83
    0x45240b098240c02c0c0e51540203986014103141c0280c82c10f511140012850384203460404078245420f2000d030601600c070390300d449500d6a0b04c80b403860a4546c5401c2c0148240c125840321103c507a0007054000459000c488202203040000d03514018070b100d044000b41200c0e8000601d030030031b4000801d8280c140d4000b40400e51031901c41a02c5503940740811200280036a00400100780859101c0020700383e52141440c010783d03141c4d225804900107402c1100760303001082c000303c2800b81103090307802c0b80a14050940503030348243c03070003520044603a414841107402155a035229907015610845c0c400d11361102600c00c858022140d841c00916142d00b40c4400c0c0c031540901500031a01c05074007800c4a04841080c1e006007942400d100240c40290700c050248081010600ca0441c0161014080140300303010482c0034241e5803401c1e0340098030000c881042c3c80d0054100b00034055256490381050141e40c545021140a401003804c0c480745544119084010088010301c03002040582c0015945142d0742d050703800b0722a40c4 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 115571375 1250 115570125 115570151
    0xa2703050c100905280c0b0a031404171602040e06010503010b03030a09060f0504050904030816030c020312060a1d0103060b0105040509060f03031b0a12020705090a09060209060a080a 80
    0x103443d40000030025008002100780011801d01d1801002d2901000ba400c4d4078070356600d66207074101a03031003141c07003d2001c80c10380c0e141d42c1c262003042d00d0080fa00e0080800741c90244c0e1121207500700300000140c80580402e16100c000c40340030340400c0850703000e0420419000038130451603650070700744213041c0b0075800e00f000404181004015030f030400c84a5120120200d0600b241038a590840703086002c2082801d01c0300113419075480b84040d0042d402603c4007140c40c00c01e401c9a0001d82d24408600007410305000003a5411940001254100d800c4104880c80301d40b070342400121a09003561160294201020352070b410020742c89110750403a4410601001404070150040d209070050b031040a42c807481d0540008d10901740108066414103006003a68034015110341c0d40211705c41464031907089640a1800107041002110400d1558202d900040c11110718040000e42020710090a411820741c581c950351003006001d13015240290001800c00762140750b9850300800940d02144d4442c015400c000d0000607003 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 115572625 1250 115571375 115571381
    0xb0403030504090f02071e02011808121602041b030c08060609040902030c12070503070504150618030618020910030308060d1a101805060102060a2703050c10 69
    0x100d40c140c540d541403d1074007400d88000d00744c0030071120040d0340030061b00c03000460340d0390f10030075489901100c548684043d0000400703d00c00c030400c800b160311035102d0a1004103030000c0c0001c2650300c0c038001d00c3d80d1000d689485003410000010f0080d000707403e085208000c0d8048e0071740c807002c060380c65500b005030f400001003c076181d803004d407401030f00310508000040f442c0c10560044400e49001904540c00010050013207204007040314400e02070703500512400d1080b86818807203440209000c440038840407011019070701c48010148100c20a101d6580c034240b51041c04107480c2c00046810100800c5490b0f141d4401d40e190148444089200762522000170352480705020000d42543e40607940e046041c0e82d2a0280000c4298118080e560300840c03054400100300c2d800701f50f074854071805e0142e284961410040c110021603504a402009041400308080c0740d90000c1c040c0d900134609480490852002e40c40c8040400340101441d07045149401a182415000001000c1203a8000700303c0358001074207040c010407 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 115573875 1250 115572625 115572629
    0x80d0503070f12140903030a110c060109051308040305070e0109020c060a0513021f0806010c120c031e080103031b030c1b230a0e1905040303021b03040305070b04 71
    0x1051515580016040c0700f0f14114004941031000061004001d031071115040d14112110030455200108215507a90640101c50482070b00b40101802d04156139052900c801050140341400c40d40c1c0d42c00113810028480340d01c0b90150700044920b0b17403541c0f2400d00301e880c0d0102c3d0241c080942d95000000491611600c03c680d46180c55802034515a190007400704082c3c80007500b401e00d8004590540005a5500e551a0907141c2c0400c030784000010010201400b05500101210705000c0d4003580c43d8080b4020312018a00312941d85814151210f031440d054400d1502e0306081d81480e6000d0403106145a08080c40505032406510340762000c1301d401c486140e43d2204024001c0014000c03051000c0000c0301d0b000403600d801204018009c40300c1d102c0b01c0c1851056041004c1c0508d8000074081442d1604221007003c002c0d0901c191131078081e19003500c011b10340e1071418005001071035490001a05241c800e40c1520345582a48008546544207148003da90390041e00040d2298000c03280c0001e00828003e0488003 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 115575125 1250 115573875 115573877
    0x4050f070c060e010605180906010603110301140301110a0c021201051513021209070303110304030309060c03030e0d05040906080c100f0203040f09020318150606090409021207080d050307 82
    0x280c40c051a030b1030700003030043c400810205640b10000442c66a54043c81d0713102800c001040c901c11403909070401031070007506901803800d0500d003444140c20224114112410745801e0961424007180d05408079004150488000384203030b80204c0c10380e0005500c020500d2145000700c42500d18000c116980d50708071441600c042507010051806108281454903990f000fa28500701700504001a404202e44002c100b241d8901c5e8542141900b402096082100c5103504042500298149800c41c0d40190044182d8001c5a0900280b1841002018030035080705d4400d0078854152030004219000c040c04540150040000203404d004010a0515000400042c51074009120a205005580341941c42c85545c500f080c045000820000c2040104902d0a4004104d5007900590f00d103042e820f403000c0481c158803010205d400c550042c8451004503580c0503005002100c2e140c5e0f030b6008000020f0000c04042c0d60094000c0c50351405480c00b10004500030045a42c07034426103541410501d0304880f00e01c401c90b00c0310 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 115576375 1250 115575125 115575137
    0xa050f15090a0e031e0307120c0e060322030503060102280201180f0b04090b01020c01080609060613030609030e030706050d020f0408100c09050a0506070807030201110307030b04050f07 81
    0x361050b078041e0003458601c004001624a49400da20070310b4104400e2205102d155135000050180407a40b021030095540034260041024003070502d0010900c600c00d204a510a074000300100d540b1100080d444241c04401c401d44404140d02440c0150090f0800c070b855901500640780e0307075140c070000005842030b9080f004c1c40c100c480040c140e006455081858641c2d12403050303d044041022030040541d407003e44811802c860325a4681503c4905a0b036021121504641202440c015681d030031002807500161f0803124049503640b40c00c00f1030101c1c014581c10b42031441c1101e40000500c0f046038004540340d40207a4030030301904500024035640750894882d05001480c100002680000d007079018190300d6041070409481c00740e0301c000c42880c2410040c00c81081c00c1c1d90f0740034040c82580011120005007c1500e00014183c030f880005038403401007000c06004000001482c10815100f175014824a109148105407a400c0c0390400400130403400385001e006510380000300e03102c01c0340d18a0040c4603801c0c955410f = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 115577625 1250 115576375 115576381
    0xa0515010501031a100c02180906070c150b060c0a030503040204050a090b04060b060d050108100e0c0604060e040608030a0801082e020a030e030a030c120c0207050d030e090a050f1509 80
    0x2c0885e070f034038000f071880400418001c2000141d44003000c60044032a1a40309810605250001e541000b40103410320090140d0709540400082110301180805544140c0000d840c015805c08540948911013000c0c2880c01040c01040406411401450186000344c8041042d503444851520803540001405404441c80a001030b000032015013104200700b00152889007846031130010202030b61000c1c0c100c0030590300581c0116101c44118420802544c107050f0042c00241e100c83c3c0410801d1080f0b0080c0c00400c44800440949500c6941001c3c00030160741c006c5a1740c40402d0a40109010020701030504a8019a01d0003019020b10a1003241c0010030540d800d400100c0c1400000000d40c05940b50406154482442003080341d000c1c005041d000038291000b050082140034010310190100c011403000ba450001000b0724554001040c4041d1a429038141442c1690f0b828151082c0d0400701041d40d00244030801c0055030310329904602c1c081c000140d0031045544810004a0f8010108013460ba00040b00f8400 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 115578875 1250 115577625 115577629
    0x606080304060813111009050d0c0e0703060515090103090c0f210803010b030a0b030f010f0606080c0d05041a0103050109170307080f0703060e0903040302090106050a0c03080604020c0a0515010501031a 88
    0xb8010301106d80d0401203803136990b881c080303622114a0401070b21102c40031a82004400703c03d0070130390762001f01850100841d40c142400211007824007044404806c1c0041400406640640d0110860640154580e001c55546d0021442030341018000c210484504210520005030300c0000001511f6020544034296820300c180001c8942005040140e681d4a0b40316110017038809004a2441440c84d5001150300310030443c543c01503681580c0310074104500d0780208040c000d4003c1c144c81c1181c094500114113a100c60500b01c2040008040300c00c80c11114900000400105601007188244650f00d900c1103c00204803100c010b01003110204003245150002552040c08a030880d5880500d50900123109a01c0b0542025141000c0b41d800305540e00c006002e00c1940782c1003414500420403468041e203803541d0048010919545500c0c0242801904808918141e03100d8040d078205490f010100c0d030f040d0090b424625640e410708840d91440c5401d550011525520078003924688503000d1100603207040500381 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 115580125 1250 115578875 115578889
    0x90c030b072c040203040c0e09070e06060408070e0a1b050a02070e01053001060603051012150c0207030b0702060f090f0318130204080307210c02010e0d060608030406081311 76
    0x444540303031087d02c0030a101d2060030681e0b015158840080030785908010300346154100240000380300f1a8244000c0003036400000700c1905840000b0441e0300280c4610380000c0107813807101c92a034a024401d81700100d60b81c1c0c1c084050441c030101d03682283c0e03281f9502c840f044e07e02c44080c01a036070800c1c00e10841d4907203580c1c4008d202030700c40210725112004101c103458250031500c458001400281c0c641003070041041200c00b040026000c803122800f00d81d049680d0304207401000d65004c06000d13440f199201e12243c0280000c80046800040c00d2645182c00c820083d11032000300d820088540916010904c03040c1c1c000340443c410702d510401107140001440b0200c1c1c407003050500a0364040448110891440040d0020340020442a001561546000c0c50046280780c418842400141d0040c501a4884c9500c030700310190050302803c0801c41c003014440424040c10b83c1d40c40161a01d410003000082d281000401802102e8007660341d2016900c41e03200149030581101d402500d03001c4040f81010380c40c40c00d19 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 115581375 1250 115580125 115580131
    0xc050405010e09040f05010627061214030403020306070c0501050a090507090e120c010b0909010b060409020304020d02090907050315011a090604080a0c0504060b070b1801090c030b072c040203 84
    0x174015802e4200c071740d9640d0b400d54440d038002039040086003110f40e490000502078100c2040204100f80315090600c25002c44208000300040d0024041050344141d091007401250059a009000e030355640c0361606000c2c1001d0f0b000d030800c842c04c2d0320b400c00149410030b40c0d2040b054855408000b4020381440c08401201500c6005503601d01c038052412542084003803070000341000202d0758008144040050104080040e004108129990612210521039a0380c88215800d45001c003000580300e407201d0011035115690003c00a40110805040c422400f20000b220740883d00118200e50701d00c80002d0002c82c00e080300307120303078003841d01e905401519650042d1b0240102120260440d030900342d903101304a18004000d002541e8488101c603090203d07051174060741b0041c001d06e142917031410103155a0b001185100600c0c0e03080e90300a0492200e03080b6000c0d000450341c0c64102c3c038131030309031600c0381807141c445001944c10300045400c1200c0c1d010051090101414406076049030748541440d07220510011358002 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 115582625 1250 115581375 115581383
    0xb130c140a0315121b0e0105011d030d03050108011506020615150f1c060803090d021c05011b030504020a1e0b041401090609080304050607080d0c11010c050405010e0904 74
    0x383c1c880710701039502041044010559007070302c03c071411400d04142c00080782104c51412409801c107001e014115403020400e04540003840c02d007440031088030803400c00c1e01c1c0c034101c45507050203144001450185c0c540c0125050703c074013200811000480780c004880708011845400301507008800040c03c0c0790000e041d0310312002c40103055881c0010109040041680c840f0307070840f22002c004a00c0380c0c1420180e0500480c0d00550980c108509070400300c2e03880c5c2e00d0054000491280c040709a0300301c219201d15a520f0401e00c0401411145003003140340060107003000143e0854481d50780300e900b07100684079000300b5000383c0d0003401e4407200900f0400403041e06d461001900200d41c0780000c00042d5041c0324002000100026035000e00c41303280d60800146aa00c865000300c00300040203400f800044004800c6404a4104035252681c1d14428604110030303005d10608072400d24605000f803031101d90400f0310303525041d0001c00200108404528280da890055000e49030000b1150807081d11107040c0b07120344503046801 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 115583875 1250 115582625 115582631
    0xe1c020609060c060c0a020114010b07060f0e060903040302040b0d0b0c0a051204030305060306130b0a020c0c03011401080d09031a0405030d0c09140901030506131707060b130c140a03 80
    0x103c10b11180ca080c50640c0c5400d03041000107840c01c5010703420310560820801c8080042031551400c0b807001000d02482c0400317009983c1d00c6600d0844441c4580c40b80b0b603044850015500d0500d00b00401c640c0780e4100d40b101f680140d0415a40480ea0300c1d054020041c01a802101c2600d50b0701c3d695110500c42d000074141c402032180810a40c546240400ca805105502c030366408142d51400b01c3c181810854050603001000f01c1d81c0300c00f0000140100340003a8401c0c402d100040c1c444c3c2c0c2c80b10241d417a1078901c0c14042e400d5482d0148400c401645c00301e00d00d06803a403880854409035a002003c0341d240d06d071480040c243e0f01080402d405008407044956070002d0080c812203007090850000c500031150000d4422003ca001031408208414103504540f4428a00f15014800307585140c80c0c0a4640d0b900601d604004560b0409401c20019240848031030322480306802500d0b01d14a180c5403008141034940b991040018881482c3c3c480154001c09580254641d51140b24014044c0040501e4006003038240916031 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 115585125 1250 115583875 115583887
    0x1008160909030207091a0a09050f070509030c060301080102030a06060804080f090a03060e0105040b01080f03070f0212030f09031207050c040b04020d1e0e0d0c1217070e010e1c02060906 81
    0x2442d0b008000311b10314181c040c0240c0c101403108000c0c1c2d100c2c8130340c006010f5a0400c0c04001c200300704004107990003410b5050540e501c20081c000a410a02d05580e0160300c81000f10021500b40c0056001c2d5200300f02036a402c03c0390a07262007098601c8001260014403030b00c1c00b041100c641d081403002510000c000544082620707500d0340d0b43e04056407007990744a4256955002007200703000c149400c0c9401083d078440907100742c08035005000d450b8403d070403010b442822400303101c0b401c5445150000d4091b0000341c0c15283c0300d0600d00c40e0319502da0b0103403800a100b4403c4040819892540c20100e8065943c41401090b05103542001e0001a020501096074003540c2840810302c42c900c6401081b01c146422115042030201e42848441100c0c100706007140e041d8845a0070601040d001000c1c004943d80200b540b4140001c103110827603030442c0094071908495818414010559000340b061082071100f40c03151042a00740b00d041c0002070b10883c28801d002d01c00301459030090b0030000d00a060b00507000c3d040b40d107411 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 115586375 1250 115585125 115585139
    0xc01110c0a03080105010518061c1103160e10111002161505010f0e090f030a0806030f1b06131211010813020d02090c07020406030b1008160909030207 66
    0x381098503101840d4108110700c004140d8010740031030140c0000d08200317084c80709451070b1000b05070900704998015000090000003840c814000840380382e0b014813042c000c02d030072003003d54060f030010754580400310f001003000c00820340544640d0540b00405001d03840c03003030000f410803100e13283c0c00c50100c0303407030b01400d100c1c201d5422950000300b184450350b22240d22554480c2c90891041003207100340003a010324103001841070300720080d6058110780036802d61040d141c551207450350500302e8080c0150554400064524035042c0c120098a129413012015030b80512101d10049032214603015414020070b80d050500a018078086001d07041441c07441c5c42040189468005c020004403100c20140d4201a401d6074010710f541e4002d404503442402e9000c50904041e0301e50201c0c04400c04150028429900740c40090705016040b01655121a0014014816183d490816003110601521804042004500c01042c030324400940c0c2103031a5280d08200f5480c81c42e104640c801006500c0c821011401101d800003489 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 115587625 1250 115586375 115586377
    0xf06080f0402011107081b0102160e0403090b0304060615030b0f01080c040902040b030105030d020a0b040b1308120417071a040203030f04061107090c0f14040807030b09100509030703050c0111 84
    0x18140c2c240040203107080300c01000d980f01c2c1307c2e00340307541c119441240741e1001d121811032642e089480c081c85a140396210b5250946100d640340d04030b00500c2d10040200418400190031483c00c444100072407002140d07009d2411010f41d4400580c581c1c002140686113900c6501c81d03d43d0b01d9000034007040d07071410681c8820140044e03a01a5100c1c00a058000c2300500051909101c401c9410746a400280b41c2d40e411030341c80c401c0c1282c0007040640030302819000140840040400304156a5110010325075840c1c5d52551410744060030380b0192584104402c040c907504a490040741c00c440e0b0010f02c06114490001101ca0812200800c00ca82501003400100031031030000b00a030001c2c144a450b07a13100c030b0361a28151480c001080d4401c0c10752a0900c006520015001110304441e014280340060b01150090345032503880c4200d40c42180184a942c4001013807048078980b00740100f00341720a851007407000240710b07003d42e4030980e03110300389400c10490b0340b00081c003400040c01c0b1a0348180021840d170000240ac0001 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 115588875 1250 115587625 115587629
    0x27011404050c10090608070e040c0507030201060609050303120a11130311010302040f06030207020307150c030e0f1c0c032001080a0515011107080304030602070b010f06080f0402011107 81
    0x6984054050204000040c0040d5040790800c1e142051103160f03a00008003400c20710320620007400b0b002804a1f02040c1b160b400d80c4801180580281304507010340d04001e05d694002c071030640055182c49030102d40207100d200b43c14102c034001030065040501c1c00c080140003910182009105580d1503400b201c074580c081015104a60781d0003401d17004c11340f450400781190350701542180d0402d40704000501000c0444c1d0769440c04c0d1074142c680161204401d1001c280b402181e5003081d52034008080a008038154089103110016109544001e1440354400c2489802516900e080b54080e60701107d4074603e100342110030403014003503600e0210541e81da84a000595051505180c01d0f011100c0801c1403650300200303500d800880e200010000ca03d03012094402014101c0103250401103002c0c44003015000401c100e401808000f402e0383e545580d64136190000b944040f00c102c400460040c000201d00e901c08019804075039280d01c503500c880c1d6801c401c40d00da0010040c0124140480c41d4000d840d144020410380700 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 115590125 1250 115588875 115588901
    0x403021302071518060515040e010b010216050604091e0903020c01080603060702070312090305010f0b03011b0c0f0609050102030f0609220f140303041212050f2701 72
    0x40c0e24000780c01c040142c0c3c1d4a07060f12900c25410a084902d07405030402060001c0c54001c0400a050f441c0d4101e40c0503501c0710300e0349060340603090a101034078905040d40714010080b0240c007121040b032843d0880e80d01081d0700d8801d0760ba10940034042080010900d400007410340c2070500b80343d184001c07200300e404d00712010140306400580c091040140c1c5560069100c641194040300280960315040b50000e540b041c1d00d0100400c80301c2031700c80310001c02c3c0c015071083c8042c50788540240301816035404d07440014200303440342610a60800035a02c4400d01e040a410600301e265681d2060031079800e0b2504444000f401c00111140380c0d845043d03802184082c80030b14055081820000e10a042460820110352400384c10180900c407e80c070101001c07040c41c442000030035403140d40c2464203003007418114114201034040800a010000402c4100880100f0209400328a6180e4641d1036130741c0f80e600811204101d0781684281801c02c00301d101601b8400880000e80703010f1121034100d51400190509440f429441c01c0 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 115591375 1250 115590125 115590127
    0x8040306060f0b030105060d0902040213140a0e0403171e0c09190b0405090c0903160305010c0206010f06111c0903020312031b0310030203030a09080607020609030904020a050403021302 81
    0x301903036202c4a1440c00808410b0b00c45800d5504000001e100b52041e01240e0a1656480d03400900b15111601592911002d4040c0441700d1565030318113018000503030410300d03c2841800c5012691a03501d403030300d038007990301076440c540440e80d010345588840c3c00240c40384142c0890200526005842c0f480c55911802c10140c1454803500340034284507585e0350f00d804103103540800c800b05002ca0750b0000203607000c458040300c8420007500e0740c0014001520407060880d40600400201c07035848020408150200ca200d03100800011900790000c80e2998000c0c0205003440071a044200680c600c10714038840d0340300041c000d4803616800f207001031040c021400910b40c041404480c007001545014450041555210724041d4607518200350022040d14070394070140c02002c8084041940344008591007030180d42e019003101c0c0d940c030400c400a441004144604043c0d0300c40c20000a9081e0310201e0840c1c020b20280c2c00550422547c141000041e4000c021000304000e014000000580d440341c0319542c0c0c00607946401 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 115592625 1250 115591375 115591379
    0x190809010c0e09040317250e15090d0f0803180a020a15031506020f01110f0912100f02070b01060309050604021201110f0406080105010503070c06050417180a080c2b0804030606 77
    0x100300517490307124547d03081c010544080c40751030701e0303065282442032003481e1172030f5849c0c4080700003a0340a40c0781400074282c4031a45030b4110401580d58011405000c907041315060001080c0d03185580ea005054009400174500c1c0300401800004544a900e0948541004aa0b04030141501041e211903a402400141c7c420340070b01c003d5140a100c1e074a80300c3c00d00b4482078034210011049803054800c0303440807030046002841d000840c0d40244180407081c9500309003800003049100280001c2c1d00b100b01e00303803118040c1c2000010494000d12421407000c2c1c0c0000945681d6685400b00000f00881c1c01c05485603540364003000e919038600e900204054500080440d45580c200b00c0010140381c0c0507049203040c0325081060207001a000220200d40d694000404a100d95407032803c1030951480303951400318610041103104052110080251b041c180903500f00c5001da81d581506076036540c3d0101295007280301000ca40069569801100d65021070182c450f1818079695a0380b9011a07200d40e0064403103554900007 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 115593875 1250 115592625 115592671
    0x70606050907090b0909070203070b040b060f09010509040b040501021e04090c02030405031f090609030c050c0906130b030708030a08010e010506030402100e0a0b190809010c0e09040317 81
    0x2038000c811850540320080c10154100c01500c21042e03030303501c00d4801d08001f400b600d2080045800031076111034083c0305418a49080c510726031007902c81d20b03c2280404400c00940c02c010303607024100c8000400301c20080d100c43c0c5400c440380ba000781c01aa10343d5000c0051000348040000030031001030f40040070300d5595181c82000005c4890744400142150000c000400c40c036039000510306c0700346c6400c900b00a200e40c00300004c030000f040c500354006c1c4900d0030400b241c0309054001c4075406071640210700b0380c2c550b0307481002000040c1c442200c0881d400640e2820503100c4208035131040b42c6580c00076040318031154803005028555004440d031000000c0e07000b40103000403448840c04070700505050700c0b91400d50505078000340409151018407800c01c05000444011070f0350f0b110a00c00104904060203039103100303a0352030b02c0c0c2e030f8800d5031051804500010081a00800144910200440580e46441c1c480700748004010b003040c2c0150042e41000074000ad40d040042c2c52501ca580565400d00301d403d500d40007011 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 115595125 1250 115593875 115593889
    0xf0c02040c092303060601050a02010603061b0e01181206110d270203070b180409110102150c07080f0d0f0504030905030309010f0e0d05030c0102030106090f120803060d02030307060605 81
    0x4403440c41c07240c0010f0f0900319034038005001c1da0010307000d00300991106403400040f0b006182c0d030b40c0040c01145c208030700f2260301c0c8142005a01c1542d611ba80b09030203427a0410040d070700c412075040f20890318000d0000810031003500c054031021152007001d002c90010b4580384400c0240e0080c086e1a020f05a17906461000c1c5000301c4490410b43c40c0d40d0203080b01e00c1d02240c00203501c848030b500c0344501401e40000c0c2c954001c98041c180f83d4407010014020085004036003440c50076101c0c0c034098280948034000196400201e040340b817910482c0c424100d0340ca809441d640320140c58108000722082280180247e00358400c0c00c0c00362141c2c0c21802d9000286500d054180201034a541c0d5018602a400801c0490303080e0741d1100d101450b14003a030070802104003404e4082a441010300c42c2c00b03003540c0404a24441102010740084d0304071952550384c25071703458590746619030840d802d105102180445020402c005070511000d141c3c0024001c0c250003200c0d03800d8004c01d0031684000c000300c0c1d110380e84035014440c80c0340c190 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 115596375 1250 115595125 115595159
    0x50a140405060f1f061b0227071704021302120c130603020903340b07060501050103020309190314040902030f090606101107030c08030a0305060102120a0f0c02040c09 73
    0x1c80e90000e80c8040310b401c42141404d0f0700a40c1d0802c000c03140b00200c89201e00d452a800d480d401b80268030018560540144051521161002201780800c08208120320902507070603a00705000e0341d060315403079a0f4200808050300000000c8516028032240c4002c1d103403d4141c41c403c040314600e80d0b0b500c0320020300c09401400640c00c62414903106200091942e100002e401c2c106101c2041a5042c0213100c401200d0b040301c031400b80c140d2030042500007003511245e5102400350103104034400d10450342c980c030040d000d0780030450342c01101c2e03484951201c1c413141da904e10f40c4804500a0a14006c507504882010441f40e00941008500a40000030301140c3c0000ca042a42d00c054110041c03c85400d001002500f104a0054840b08200d5401440707040701d0700c2481080029580005181c2c0302030b6844c20501e450350002c8a411010074a00b0002801550020900751444681d2101030391405440c0c0d00151202201348824508005298400000580712803023603400801e815250400d22914198207038210b52520 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 115597625 1250 115596375 115596391
    0x90614010f080a15090c030501110a0207080607080708100f0306020a1803020a0b0f0d020c01060609140303030414030c0142090507141204121106010504050a140405060f 74
    0x82c06000001c0ba08000d108400713412500d1012400c00d40b9824a00301b81c48040e00094615441e007502040c0004805000b04440803542d0240e444155880980c291184011104d120119083e1400564402c0c410142075074040000700d400e1180c182c59040c0444900055003007283c2007540084c60b201d013160004c0001a21043c6080940c40c174609541c0426401c00c018401e48010f82400b0504500544040083ea590101010000c540f0b41100722500790181c191849030340c020900d610000f240041200c84074240580c4090000d40c5551030b1540c07250811400464842601c0c0803d2040c0d40001c1c40a000e9481029180051015540366142a100c0079501504403c2035084c10b00c110010703160503085001d011a420004c0c0010b19135284002030310104520b95600d0350301140001c041c0030001030300b507a9500840c003803041303c83c0c5445090016076414187d40c0302081542d102c0d5004114030700e05034200540c0079000400c0440c043d20701c1c0200094401040e03d04441d150050710410050b6081c42c9103640d4042c0607 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 115598875 1250 115597625 115597633
    0x150e0312010e0709061206050d0c0f05011407080d0e0604030909110a0c0821010f03050606010c230c060703050c0c03030f04090c09050603040f030206240112090614010f08 75
    0xd030001425803125071244901b400202803000c55031800f6603011038010b11014017004164103452400401200d054000c102c000c40d84a10003003443d500c603030303c14a2207040d00c183c0d852400c43e064542c28040d0300041014000300382c6414810101e030b0020701200e80502c2c400c4d15103005003414100c5000680700c00001800f42d030346042c01200e003260707400f504202c0c0007900160055a1007501c15001003d003010744940003402c8280400000d1002281e52012040f280240d0076640c8540701c1400454803d070408802405100308036680c02c60442803c0d5011001800380021505500103c0e03000c2a42c5422150003a00403031004948501c96600901900d081c0074000c9020b50301d40306202c040306905010340e002d4042080c6c0e540c00c1100e0020300680841e0301a00d1b0050034907450b898540352040752042c200c1000c80050081002042c42041c0520307130a10781c1500f001c2a0440d08200400441e007044400c0380d0492410f403220512404621a0301c5111000403081e590002c0030760410503048452002075020400e02c0c4d02c = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 115600125 1250 115598875 115598881
    0x80304150c0c0b19020406050c19020105030402130603140a020406050f01080103170d02040308040302040b0909030405060f0f0c0a030f020604080d0b040905100614030f030a0507150e0312010e 84
    0x64800b80300d5100d59031100c1668200d4032204001c4213a00780500d10304c2c0800f8030005010680d15040030280c988484108129150800300140e03490780010081c0c00203004c1901480820010f02c2d02110520b000840903e0014542e640c98413480d0a1820515034030381d0b140c0050340d0300d409504090140d80007a00d0140e80c1d101c1036403201000203080700d105100140419400400710400741c0b44201c116161201f02c05419901d0fa0f4480c00c000c070265000d403204030300c100c0c40c01d40c0031004c2e410700c418020b01c07400d450703c061030500f032524013481019030100035143d28601c0c0403c901e22151460030702410900d11203000901c1c06001174540138040100a004110544d4015010000010750314001c5449542c0381d05000304038100104c1c00301d005414009001800c0740502c0c006030100e40c141d079100c0c00894200500c07034200550044107060711915402044415a081008254085070184000f011038070702c40c0301d00c0107003141c0ca0303418841128a905100c9500da000001e0102108841003441405000007101c2440e40781 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 115601375 1250 115600125 115600127
    0x3011a030603060604021608030c03010f0e04020a0b0c031312030207120803011e18050f06120a020d11100203040513060e041103030f040902071b030c0e13020409080304150c 76
    0x11402810360f886070f500020001fa02400c1c031407400d400c0c2c5074018905a100e0500c5208403c440d00240108010100f103184006241e03480b221005020b1a00640042d0615041405194440c1c0c0424007010036840100100b41c107070380d0308590100062184822808034110f8034a402424568aa440b903820700d41c0400c081e0340031440903403c817811103840d21100d4500c2003011160702400103583e80510045440341201140310324042e045a44503001c2c1c00b440095640d680c208001c0e004c2c00607210390059a0141030a60300604210402414980c000c681002c440d80c03186000503201403a0561050068102142c00c0146082072021388260840b1040b00303100150078900a08205000180301034401c0c00400c000107042e480510440e0410070148450564658403082c0e20006948000000c550001030400509103007246c440c400416030740d201c4185640c2d1892f052000240c0f490107494440c500221070700c403c0c010396852250040003803184107501d07224941400e000d000080c902c886894128105404c4096103 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 115602625 1250 115601375 115601383
    0x70e0708100b090109090e0105180d090603180501180515060603060d032c0307050a1d040c080604060501050f040c050306010c03090e010b04030b0a021e1b07090203011a030603 77
    0x510840c034011a221066000103ca01102e83d1b8850a8928500040130129140c19040b441c8200b00c1e2075100c0310b0344820b040d41c0302d42c2c0f02d00307035040b0034000350310f200c02440703003d21030780050318118142d07000d50100d10781f9602e81e60308640342812040442c0034142c030b45004001c02031051101e8404180722103200303841d000c2e01068044c4001041103229000c8040c0c1d201c201402030382800045020140092040d103c2036580d000380f442488010f074403e01c42d0b03410000b50341c134001d80c0082c29a85041c0340a5032074030a080441203034510181044503404410400411003d8081080e5803003940500d801141d0742d4540014002950041e50b000c5000300d088c07544440c01c8540010459800100038680306400400c03078102182c40d18403540001940300700020000815070801d0010744166800303840c012101c1d8891500d01c80492040d0104038182c2d112189401d1348040388440904040001e102d44010680c3c600104282000c10030780007170600366070200052195842003441c510040c0c07000c5a000345942400c0d00000d44d2 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 115603875 1250 115602625 115602629
    0x160f08010c0210050408160503040f05040902060904230f0f010801020a0822020d0b1e04050601050d020406180614040b0303030a050903041d06030d08040b1303020c12070e070810 78
    0x4207071344581c0810200300c80d036002c54041c0401c481c100788101400b403174190b89a130300601c1000c010030090480841e180c41c103445940041940101907034070700042c00b000d002c050074242c00e100e890b030003e56140c114210041140c46202e0390301000c4c10406032416180080402d041a00081101d80c814090a25419000f251046e00301d1a01d62000c41100d030000440c1c48141b171200e6000350000d03815103641c03003080029440c039402011041c0034400c450402c0b10040c48401411035002e06245d000000410441c1012800b41c0c81d03840c005000400c403140c031904c01c0610203400b004c240c3c41840d074946c0c0401080301181c03002000341d1401c450a114801c48240020b54900018012945480d600c101042c200c410410480340280780b020190380c1440e01d031044140d012a0100c480c40c0c0039018208040d8189407007450703864811684181c02c3d0f400c07601c1c1e00c1a610403140c42c1110403001e604c1011400d650035901c10041255070718084000b03022250401f40c5010381140042c114a0a21400e181072100b0394140d03004c0501 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 115605125 1250 115603875 115603903
    0x301051f021b060d0207050a021507020a1401020c04061202030f0d050901030b0613060507060f02030f040305160c0f030302010f0b150d02120711011802091501090305160f08010c02 79
    0x14850603810b0004055110350452506800d200140d42e000b040004201150f4090003204d807100e05080d10380d07011540f40b00342031b8000c0d1f2203d203004080c40030f0f001d0300394600d0010b04184101c0d01c0d20305030303c03000c03400300ca03050303003009461840b070312180411032170100010210740c6000006804459181480945140681c50b88176040c10b40700e0102480c23607160783c0280d401083e01804511400c690302c00028004e648900c3c4c080e1a064240640944c0c05c0b617540c02141c9c050090810500d0380c035521a00c04407095003101e000e903000565600c8034107012803003810964001d801d00100400a0754903514019085442e51140c00e41400d0a22024800c160754891100c4013800710740c1c581e03030340d1410601d050074002e05c2103400c01c048000741c0c1c2c018854440d90200210780c800444800811041440d1600782a20342d4103420001c0d8841084000503500328807415459290038418102045002d4481d5602400c1504904004c1385890072503800f00101058550501c00500c003100c001c1014150f50f100c020b4441c501144415 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 115606375 1250 115605125 115605163
    0x30e010e01020a0804030b070801080c0603010605090105070b01060801080f010b0d0f02220207020f010e0906010302090a08031b1510330314060102011e0c0908030a03020301051f02 79
    0x1031140d009000e07031003d2030740c44070034556110707203031b15001c3c3c010f2005980010000c0c040e03500100340500d00150a44006a0080200e800e41e0b20b1300b0001ca489601506205042103020311044000410008038903001e429181c480e08044d604050100c1e291091500c1030082076818019403c2a64541422803a0680e030401d0000d4802c9400340040303000301c0111403402402e015809018460f0700096030241501350320880b8400c0e0b00314080d80044038000b10071409598401860008242d15602942c014003403007401402d072141180c0e4890b1b00c00d00b140c01c03600c0707299070200b011818101605020f0081260302c00030a4011907090404814904800312103019608100032110901e401030100100c06d080ca03881c02e4140360070112080c40c0010301804d0300414611240381c400740030401d01d60040c01a0460ba400103803844040c0b02c13411035544085c0410000100c240045070801140b880c6007031009000604083d01d0250366949040c09001d125404803e520f080c1120319a0b42801b140d81c0441c010038480540c4444c1 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 115607625 1250 115606375 115606397
    0x524010306050c07050d090501090909080a03050a0b120a06060b041503050601030204030b16080f01060c030e0a0e01060518010903080909180f0f07080a08040b03090703020429010c030e01 82
    0x80b180503c12001c003d0b00d688110103000b07500b02d07408649131080d01c2c42030741d070340d0744ac0f581d54000c0e8810742e001240300030f100403401d000d2080d506219521555002c01b00500100b0505d80c69000f00d1900310b24900207040c0c580001d030395001230003441d01500e8003d00950091078034183c42c0c030314030b02d8a0313a024190700b008264681d0b002c00c001383c1c07081d0183c07005076400120441c0c050410340c0411181c000c60300c01c0c81001c40c00060014115040c000e0009040f05d280b0f171aa100c59410039034049415107a40c00703886e0b074052429030001c6081040c641007540641300a444d02e5a80301c0c1c0e48221544c0705020412601e040001544052000503418016034030030340360a030346001c03a03902c940200060b00c080c262000c0040e8420780034803440090001528000d031000002c1601c51441c3c8608100b5191882c5101c0a0640380040008101c030385220030045030b10010b454252158141c5a900140079100c02200c04607070526015551008101c0d10a01c0842442d401d0070403224441041d600030304020000c0d26001d05110b140c41e20 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 115608875 1250 115607625 115607641
    0x8010618080709020c0f0a05070501050f0f0307030504170705070302010c050c043608030c0c100f0b120a0c050613030203100203150a0f030834052401030605 69
    0x58140503190840685085585460380a0002d410411700c2c1c501c03501c2801000741c0c0904010890120031500314024008041c10f01e4015a116481424050384101040014204e02440318000d18045d076500c2c0e81c04901410603040140100c0b0861301042c03100c4404000140000d500020038a08607942824010b0728001a400c2c07503800d10352035048154219052500b500f00c09084a040c4038542c2e00580c8030140c45030107000f00d4100211840100411304201000400c8149010601510408108108860ba188107003103041c4160b480b840c1c22500d030340d034032400314041524007001388090303c0354000024408898241c4942000d80001c0c0f05040c041d00000405181940c005514103001c1c41d0050222104180c094000c0d0f4002d600494814100011500502d0300714030305010410119009411840000c80c1107454204407075000407201d582d02150f48482d02c01001500c2001208036000c940c414400b0441820704906110700c60107141c04c3e2192049095204010205400341965007100000034655a8040d03 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 115610125 1250 115608875 115608917
    0x1080309091902070b040c0b0f120a06030f1104050c0c0a14030c030f1801020102160b0720060703050106020c0d030c330b03060c070b0702250501110d080106 69
    0x800070601600000340392051122501031170303000d10302c1005002c42e025690556a92a03025580000700d0390001002052a80c1c0040c010385038110602c40d10025015075030303a840e40c1c005c44241500710342040c614055a03d6502d4070707200b407039403122a451038685004240500642c80b15103800380188903404c440c010320702007801001680d5000b8840030440744d0b00d84030318840803509c0c4c000701c61840c0c80e41c8040c1e01515043d44180251145280c0741c001d00d00c40b03a12565220794400388020002c0d0108141132610a03a142242026041d00e0703500503014040500b0440c0d801016200b05802076010b540c00841d002090307840c0c0185c80d409040d010b1901c5c107a0b2065501d0302e05003052840565100c00c0c5020f140b00c810030004040c4030a00321580440c00c0018045100506468800440d00304031408000e11410021076a80b461041c2c0c0a041807058816100b621998080c0c84110864020802c0302e000381c00f0300041d600102c001ca0340301104401046c21250080e4000c049480502a41d410459040c0c00d0341c4220000710 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 115611375 1250 115610125 115610161
    0xf0504020a0605131e0515040e0403120e010507031a011e052d191404140102010e06040302060907060c050a03180b0c0c01030b0d0b01090513080c0106060212030108030909 75
    0x140302c170940140451030307140034403480e0140604c1203400900100101214904440407100100200d4405903150b8a050300da1072031141d04c288215488030340c2154403000070720949100e4440c9442c001004038400c4200c1c1c140a0320901c2c1c084c1800fa26184c484110094441c0b8098034084d10715001da40c0d0034040c401044042c0490f9007045000868810040e5020820030141076030305d030212098030050b110b42c42c00710713040c41d01e942c0b21100d041801c000178002c8808098850b41c0d00081800081000d07102c988000e483c0c204215019001a0054010302401c030344140022401002d2900e00124100b0380350f00d400d500c5071007900d0001c0a10002d440340f80d01d402e44038103404005018400b2115251000381d5a5140c6a85039408418002407030300042840070301d000407010107a550072007645401c903801c10b2041070080c03a016080c460308003811100d49000a50900c020404c080b038000010410300e02c5c0401c00380c60304c40301c1d04098240c0c400a10060162150000c1500d0f0460381c03c451400c1c031521911580c07580300600c0 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 115612625 1250 115611375 115611389
    0x403050f0d020f0d0801090b180f040209011502030d0515030a06020304050c060a120b03012405030f010b01050d09020a05060706021b070810050c09030f0601090f0504020a060513 78
    0x90340446480d484045807036900400c59409480548003c0c02050340c0701c4113864003a1004c0361000780180101242c680c003c04004201030082040441c400c10401c2801008071200485031500c00200001c5043c00c58050b40181490036001d0303841d0076442e102a480f801359840c600e850725500c1000503c605140072681400c140054150303200d00d03c65007040703000381d4030485095440d8414038041110904001d0100c40d075046980d951400d81c4110388901c4005011042c01d51981907481e091065006442002ca64051050184031400d1282ca00814103040ca014622464040d900d400d8034031415907008401c650314200d00c50030015451600b8400500725801580009410003404aa074108007c481c5e0300a108040031004d240d41411900755013950744d084035000d11026900302d654506c0003600303645c2140c2c0d00403a07041070003428400c1c80d03804280b521035039500c2242c8940c40200100401e19651042c00d108000c00c00050001d13181030b4021079a0340603030f8421001084000660180d0500c44c4800b444041c082ca = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 115613875 1250 115612625 115612633
    0x5120913050a060302100810150f030f0608060c0c07080118170d09230a022103091008010e010e010e0f190c02011d010501080c06071b1d0c0a0221040305 67
    0x1680000c0c031f1020215261003580c20000303808500030fa13860f040105c0c880c9241c2d807a040762900114080b0090601c3c80c003440f412a1311a81d0221f0040024403030715200d001380320701113901c0e030b258901130501e810151b40c420a5181d00d06a0b1200d41546840007110346143c204410301d00602d0984010040780c030a5000120405180551050410000021500300c92003018035a1003005140d12410b078844104542c020342c0b05101207042d0000540c3d10400c0d000340320710700060f02c0c203100c82c13030380403a42d10884030b140200007800700001480b807111070702e00c4240501480c8605031070303a6041000c06110340b84094802c030242480080044c804580a852003180302d5406001405040c9004034064040d20300d20140600c3d0000c2d4550340d0a029105100d440d04035a0700d030000b00000340002c018406146e0101c00191500c41e101c04925009483d2a030150000f0043c484070a080f00d201c80091034016032014002e850a2501001888211540002d50b030040c90301c10008090b0000031569010400d200743d500c01001c0f401 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 115615125 1250 115613875 115613899
    0xd0c140a0e06130f030b070f020a021c02060403080a03060614120a060b0d0506030613081909031b0905060607050c010e010e04062408090703030509031f0905120913050a060302 77
    0x10702c4c182c0000840f40b1071031500f009074a40310401d0361188400301e081c90044e481029198007610300924100f0490a840c6440c1c00654860b80210b10035074803941083d2191000002c04180c0598944a194010201454036005808030b20303000c118544103620120741c030100a28040303003100c02c180d80f2480040000d00c9107603a482a13103d2036407001e0141220f14a111b4001d0000182c00c8161400d10780000550004040d480e0a5000700b541c9100504c40c5014801c102c0d142d90040001100b0410003444c8500c8000e03814611854011600306403078009020320f019180a0000d9000107400040241e04c0f40d5090900c0e1200984401c0102c2d14481104403a0b544941000000a080600c80750010010f1041c4160030711103225801d0705641034202543c0d80c00895201d0202040030900c07031006410030100c020166540580d0500c01c04005081100d14001c0e040d41d15561001080f0b8200b014968402c80c035134803282807040b03d900240c1004036103055401815110320009003407107060340c0810003a60340100b040d03075400 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 115616375 1250 115615125 115615139
    0x5030a020f070f050d02030901140c03191706030a02010f12090519110f0f0904140106060905100206070801060f0e040f0606080a05040c18200d0c140a0e0613 69
    0x101c07801d0010703501e50045c400000311a9202000301c3d50f0040042c0c442011113a4000749401c1b07030758000500a00c00e0b0200b0702004109444002c000c6603240100e035600e00500c018031000b03da100e00e000c0e00c0d41e807080c1d00c50039081c0c00503600720650280382305960030700e4040c0c01141041c02014100d1000014100e004402842c0c10f01e01e84559100f11031409980310200700102078042c00458804151425481a0b05001c0d15481e031420303840e429801403003641d4a80031440c0801c3c485080d0b82d9241c01450201e491720400313202609003000419803050440c402808541480000900100010b0080104022410001c001914012121058403c501400403c50b01641d001c10a0080500d030007000001211b64002c25102c0c1c0d86800340c54045ca4100c000b07440410325240c100080d8694074410840f91079102ca104200c18602c0003810030b0380d1b400c0030103040c1c2e44002c1141e480b8103c4164007810424450000c403080b50902408050710039060107814241404101400060481e00801100028046004070045000 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 115617625 1250 115616375 115616393
    0x603070318120201062108130f090b01030b0f18090a080708090a0f06050a03020901090b19140a0206011202010302040f060c050114060310050c0d110c070e0103020303030705030a020f07 81
    0x180d4154004c1100a81b180e0100c0c0804140007000200ca44900c5811000f10f000c1000801d01d2040040b24400c6940e510000c501d641880c0346e0180d060b0036a220714490655170035008050104038101e69000d00851801c2c0024000f08040c40e40346426490500021055082000305030318203030700301c202c43d51652082d02d4024604e0b03100c40d1005004685103140002c01480550301c240c00d4418036110305007032210182044009410035481c00d81049440312001408a440c4001408184e40c0010343e0600203005440141030444c0001c4c0301d4a000c02c04220401c0e449602044483c1500e400b002a03a262001a00040300079025903040a41400c929580c0000c0c0d083c0c2140c030042525100d40024444020903000b514005a0700b11502e51b0150001d48403004940610781c029a84102c0b038403101d17820300b1482d03100d2504540103490b640c14028000514400091020002e000c0240740c80c1400c110190304540c00700e912030001501c50300602a021001c01d00d41440c54064824070b0841500070358031b402c0c107400d040c591 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 115618875 1250 115617625 115617653
    0x70b15040f061409070212030603100c0203090316180f0207061b120c09060807022517060106050403080c0307060c0801032102070b0901090b07060b1507020f0603070318 74
    0xb04461246200400d424101306162007040355802803c9605e0404c07903036942580c40144a2985400b95803401090992548150390014507194011a200d41c000000c3c11301d42280d010340d149000010402c1000840991032181521180030700022560342100b62084010b0700403003400a0500d810181502030800c2030803840070003049165664914a5045d1034581c00701c400394801d260005038010000d1180a00400075550422194811180710700b5424840460458114a907600e0030786249104003d0401a1070081e081280d4a10280489500d80346015040344a54403000303000060104540d100e240c0c090056540035a0800c10a008181e038a1750000c00342c18090008550020008800c0301e500d070240704d600240e030035454009007851030628500005c507400141400381001842d08011030382c0f02085002d0030748107114200120302c0c024420100b2110840542c54041c542000703012319405642c1e050003caa50f0901515100e40c1d0b0745032650300314003800030503481c110200c201d0702c03c880401090400c50b040d = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 115620125 1250 115618875 115618889
    0x109021503040b010605130e061903060c020f1906150b07050d0807030e0d11030f0d090309080f030906030c0f0a0e0906030c03071520010b04050604050c070b15040f06 73
    0x210f0f0740e0b01ca0b003050310640125039011690311000711007403255064014196070041c80c010710b0002c42c0d59800740c0b800c82c403262030f420444015440304a41e910715a010012a01100c20101c081c150304114035940760340d56000c0c41303006000c0716202c44402d071510704c00c0303800800034000030840d040e03955001e070a04030303a16010882c000d4001a072900000d0b18680c801d202da806109005c1001e46401b200300b200490301d14030990040d103454041000302038080c8501c4002400c110f100c0b03010102d02c490300c40c28050108035490703000c03000782e070094041541c0780d000210484101c80c0c0211842901c87d11510b5030300c4094068082c40d0f90240a0000b620b100180d004144100e039002c080b205407080350390b03500c241a140c5103905030320354065101c14420300c4405007030206580e03002c04030f18080c500a10070562002c010701e984030b03030031409941da96842000d44c1824014180d1100c4107913402c0c00682009070f01d90070a4401d81001a224034145000f00d0400c0304160303145070702040c0040041c480034200905400c001c099502c1400 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 115621375 1250 115620125 115620143
    0xa1a0405011803020d0f1b03060e0c0a0303050d021602090106030f0b0f03100905030d0507050c060108190305070204060f09061805040b0712090503030c0c060a0603050309010e03010902150304 84
    0x1070102500040b01c40140c0e6405810304500c0c140b82d82d114038501c40030302c01c103c1d602200030402c1c0c5000100340c14200000d5005040100308007002003011401c040074541c001c0e001e003402c080c0c00d0010a03003110894030340115084006a41d110f10030a8580007c00b01a00294054109000060340c9981a044500040504c0d5810440004240c0402115a900d0304403160140c00c100200454020b182c2d100107103841c0030340c00707072450003411441c000116941214074602203040441c0381901d90100300045405002e103e0002c040d22030071100401c2c081d0003000350050400074009080030854546801280040681b07540030400d40d502c603000b04000e0302050160f9013510307495076008503245585000d010301450700b001c1d0725500303a20f9204003151100b0001c41880300700e41c1c9a10204000803030400040d44074130070f20030225407120340f45840d10b4109440904002140c50400c48288041a404030881d030080300c00342003440c011143d44010078050401558041d50040c81040b08009982d5031200031481288281d040e4 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 115622625 1250 115621375 115621397
    0x90c0d020304200f010f030b010302040506040906030506070c0f140313090e0d08010e0606031015031b021c08070207080f010e06060919020a0306081e0118020904060203060a1a040501 80
    0x400580e2525500b440d0000d601d1240c806d4403039019500860980c00113140140c50b20b515000811a185d01690100d401e0580e1500304105004041c00000e800c480d4500d09844400301d2500c030700e2000b54603014050581485050b442850504c20812100c2c108030079000554240d40ea6241000186440341140e001c600541420f200c00f140304050320b9050341c0340c607003424101d0380b5100b05010f900e820062140b036401c0008603010a10070b142020104455103141e501141020044014112400e200300005080d5449803080780000e48080d4413505d8090b030180380c80c0795103039600382c801ca01e8840e40f0b5010041c05c3c042c00340c128088000640068802d40c2100301140c40c142c42e600284810404112500c0403404503442540c5c9006540360000d001028040c500814229110319456003040b42c0d4107160880d001c8804080f403d0401c00780100003101070041400705000c02e964010408618000f03200410150780080041c80c0790340c880c80e042c000380c42d600c0c40c0c1e00b203421040350205006da0b0007800b0b82e60100c1c1610b115 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 115623875 1250 115622625 115622629
    0x3030e040c09141507150f180609020f190504050c04080307030c0f021305040203010c02060c0d0b030109051213090c050a051c020c030909010e0411090c0d02030420 72
    0x15402089255620000e585240c41440843c0c2c43d446112140e10030108080448281c0c0c1500c060018180508040444030f444003c41c00100d0710381400380760020b4200010900d605401801c4020096040140880c01d10035610000d040b003100224040d41c050f0245100e189452072080018051340d0b0103803010015903d0300da0426546004910900e42c04d64010001c00c8001782c4929102c103803091148060b416840381c0b41c3d001842003c8140421140180d85c3c5c0104015031030b0034020000e500c03019001420a904107540c000603107100b610030284040703442d441c182d003407a20b09602c000c5005030080c043d15541030245032a08002d5101c8540c185203c560400007180d58902071103000c1c05401c0640b26a444d00c00300e81c1c02925650000412403641402d0012160596a01e41c0000c0c0110400303040a035a40b5914041000400e001c1078004a9400c04404100400030b821074064441841023100c01c000c0310303a248504000ca40c45507000308544903001206110400c01c0d080d24101c203101d024400c00c5810a50700003 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 115625125 1250 115623875 115623881
    0x60902090310141803040801050c03060117040209241c02010207151b1109040302010e010c0311090904080403051203040c14130f090c0b07110603160e010c02040509010603030e04 78
    0xc0d11541e4070700f40c4004903220301c901c15400440b2040f0782c41a2070a1503a0346d00c0a9003101d6040720201c00c1010000208880340da844903d12000801b21080700c402400d0503008908004001415511004c880141c07052060b96001c12240310488028140ca0402082c45800c0500340161001280940b040500104820b040400640650308440d912200d552820340d01002d500b109100066440d40c01541d000c00c6130751590401180310328040d030004200711156011050844902922660816140c00312002c501c2c0d00c0d0900b180ca001008440240442e1554105903034148a1135100030480c1c0b09a64001c2d1480c000b00014502c40d901580301d01240c42e0fa114000600304c290400100c4d03008001c0d4039041c0e914515523102411320403500100180c1440c0c169503241c240080342e00074080381400400c1c000704010050000070803c090075a0602c0c150306002492600c210380c52840c600a00151051070803150740308900840046030010014401400c140b030b12507000b8419030009400181d0480070484441c24980 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 115626375 1250 115625125 115625141
    0xb0406030c0905160f0e011101050f0702060907060806041a0d030903050c04022505070513021804060605040b0706020d1407110c010210110409090507060905030d0c020105070c09060902090310 84
    0x912048400c00383c0f400115410010052428140001102c494201d223030248a510b110310b0900182d00b2050620410280c505140104480406e6004040c01c1c49401e074880e4503d40c00800c10741c0c02140c1c0000d00d80c4c18000038900c400c050f54105801e100d40d80c00345644641044212030060302610341c003d1180c0148416440f91754000c00040141c096428011a10524000302c07980c081c0c020f80300150b880307800041c01d20050a80c07410903e90085140c83c1251720901201e20070030303400c6a0400c18103140c4075003c0c1c454003491042035003080c400721300c0506010b6982c044401c0640081c20420088402d09180f290304002a1350b0500000c10f464440c001c04080002d5924903040160002d20030140c062110700c010300071003050605d07402d0090000190030145400b4a0801c140b003800904a00e0b4107207940140f40b000550b10080c07003503001c04c07076040d004d035046000c60651a4080ca0050395481c0745081140c40c07c56036603ca02c510b03510748400028110308990240122080480c25594041d5503003020000340c407072030 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 115627625 1250 115626375 115626377
    0xb040609060c150204090c180e01030b04080c0a030c050c03060c190207030b0c0a230a03020a0e0a090f0b090408040e040f0804060e090106030c021b040b0406030c090516 74
    0x160030305002540c0110122011184688140f04602c2800c00500c0d050fa08194000e07046680c0341c00c803d0703c116030030510100c0e00031018170040c1c0311540340558151440e001880050081c4192602007414445041d00311402c10005100300d81d110307440343c5001080e0540150f01514140500b480d02962880c01081e41c0d03000e00042c244507030820300c41604000c07200c10149482d0055100da0040000064805402948902c0c0800301407a03c411400300040e10101c42800c110f02c003826415100402c0e01c0038402074440626252030012b0301d0740c40301d46096401502eaa8001548920610400110242c0b141c21541d0301030142c7d03a041c0840e07962941444110041a10000c02ca08801e01c0180444062200880e074414040c1d544401c08c42c3d035036120405194403a0b000700002503450301e000384407800c1c82184c0c50f00418403490f041100200168000b500c54403800300e10784d101aa24560a9256500c40d0087c0c2c0f00800c0c010810045c650303507071424405d90041485064101da040c030300000c883d100ca050800d2940406 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 115628875 1250 115627625 115627637
    0xc181503020f0321190507030f1218151a0303070209070c020a1d130203060f07090512100b010c0312050a020415020607080a1808031009020f0409060b0406 68
    0x315402c11000e001e40880c0c00350184580600c1000713049030b40014940200056011176503980725640000c103103180e4540802c0510804200240020340e0258003a2914805482c03c1014424081e01d14005020041c5140c11581c8403500920284180c0c450110044242041c00b000b82050a401c202207440390194841d5140d001448904094100120001d502124910f48003042112030f90005101d04116048804084442d062503107400752458540c54000a009a1041c600d01556000a640d420020725141c0310400c96800304035000d010f044040003401d0f008005010000a007071289640e8181c024180c00140d041c010884a06c0d409401c80c01e8045030595203110954804c144010060800500140b40d0716908000018541d2050810007a21041503805811142840b21006110403005080300400d50324020f4001c041d102c10854088516520171007640e10703a561000c40c139904043c240d0050b480240006040f0b00c0e41d500d0380004000352080f1080401c00d654461303940840c240213501450004c101 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 115630125 1250 115628875 115628879
    0x906010e13060b03040302030705010b0109050d0f020d050d0c0317100e090f070b12060a0e011403030c0106060e03060f0403020c040e03190905040e030f030114010512040c1815 77
    0x40c002001100e4940c501c1c40492442e82d20803109803203500c11039007900142c0011500808001c030a008618460000740380100c0b80504000c0020b10003100100000e00700c0020454250440d142c501044001e940c1140c10b031010604501c2028103110442d43c8110001404034440c5414202040c01c010701820865440070f200303905040c41c005100002800c005003034410418030701c0300c0319408c100c4c127409450380c0c86000c2c0e280c100450358070800c2c100203424a4440d02c100c40042c000140c10189082c1103030038804910b025003a4120200f030440c810b040b201300480d402d04c500030a0341d45c1c2000500700c417004c0580407101aa90340c00c035152801d01056a0040068000405210702443c0c503800c1040c00101104c1034902d0401004294062a4401c00e50791001c20070740d800410042c602485440424100071001c5d604c1c00a4194440100c0c1c4014000d9640e00d8080007103420007644510269603081d1402e100701005414181440c1d10583c820384502c220000010303030200f2885046020308040071a03811400c1207418 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 115631375 1250 115630125 115630129
    0x1020307050c09040c0e010801020406120513031404030b010806090601320105040504050910050618010b0d020910020a112d01050f04090923120c0304030602070b0f060906010e 77
    0x120058019100c43c5980c0705c0100384a814280c4c400e00170401c02000503a101e1402902900c000c00031159035049601e40000c20070b40b070102d00415031040380d045c64522000340c50ba5070101031a0180390405031a00c00031304001b00315060005511400351503000c2c100c615030f80c1d844405680080c03c0850342004034010703041d140070315490518904040d084c1414818102a100c60115003201e0080303c040b0003562010200c480c2034410b51043d580c10141c1518200520f40e810040b000005606100300503034400c0015801c0106041c0340e0680301c40030001041e1000b01c401c0000f00945c1d1351803a140584a4088200040c24185401d0664190341403160540d01098081c03001c0749405000f003116414184041086404507944000c0014130207003180150020345403030742d81800d445250b03001d410b0444160100185403041500050907600c159400d90b0703c141e0360300040b4601400e5021f1030780000c0040d80003081820800080600d401e01c100754124801a9658598081000486c1d007035601c6030205000c3c4100200718 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 115632625 1250 115631375 115631389
    0x4090819050d0c0f0f08010b0f0d020c0111030108010501062c121c0915140a02101406090a09020906040b0a0e0903070203120901440a0b01020307050c 66
    0x200300399050950030702c0900780241c0e065907400301c14040050140b030300d11010700e50094046150101e107480d2000a40d81800c1c1844032a20855108205417100415842d1a501c4690120b5040031000c0c0000c0c019041c10b880c3d005d495800a010310b1a003942402e001058003442907a04081194000c4006603040c0400b5100201c0303404040540c603013141c130380b8200c021919070400a81c2c02d0803007032107039810001406200040c15001107401130b88100041ca079081c00035540c400342e001445071054681d2a982d007100d4105a2420080c0c101d07903500303182042c008054144a84880d6072054000340c40600e015a034510280c4100c1e400030f440258030100100c04a0002c0c24917500c140702080d00a00142c0b0100c2d2604411100720b2021641241c460303200051403c11400c0034050036407a4035015100b10b040a003c000040d00c80f100318001c0b95a44100e50180212280107100401c4440c5104a0324150103c0020ba2101480e02c08494502c5e00728100026150b00794400004c5811043c4c20101605400315404100510 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 115633875 1250 115632625 115632667
    0x103020904090f080c1203042303040812030106080603030c070e06010509060c0105070201150e0112150c0305060301150b070605041109010b03041104110307031104171506040908 78
    0x200b039890241800080b224900054540e000e20350303030782e1208481c01100785003207428000f0180500090003440001131001040405a11038140c100c20840d00c4807004900d54001c0b80d0011440303200d150b100f2000c904803040114141c4490740e230f03000e80917914002450394900c16024245034590004104002450388030113050b0300081c0526100d4500a9404002949a000100012066591103040c03045158091251040d0101c0140554510360700d0805101c0b804041441003100c441c40020480040000c00301403081c0ea42139481d000c000c100c8180500074028a0102e074900c4c041d40c641551264040c00c01c000300b80898461724540c074580030603a92124040c0c18007500c03c540611203500081625a20f000302f143c040c104a404054491030a820f16040841c0105041405286010305541e112421007003140e40c000b0007802c011510407034a04105100384290f078000c0d080c07520020001d400e01000401c4454051008500c081c1090312003104110440d40203060080c81c100c410483c04044041540403000f03 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 115635125 1250 115633875 115633879
    0x1140d0c0e06120105030d0e10030f02070b0420060c0d140403050303011206060e10090c1205070c02090901020f07030c030210020403060609051509150a05060403120f081501030209 79
    0x14141d070141c808070345180c00038044070301c070006108010321960404010504403400607260441c083e003ca1800f040903001c00500503000c15486410201e20f0041d5901140c5000d5442403814440b480c0a0408402d006240c141c541c460341e4101c6051002e0389819410782e00d40c08c54400141002c511500e80a4406c0c102c0004502000a0213002c000f0100300184040c500a00c42001c2c41d00e4400369500d0a601141c060b90062100c00c00000d0a02884840705030300d08054603600c0c0c0380003c900039010350a40c0c0c45030f149400b0072402030808081101450f030004108083c01e1083d00d13070006070f80341c0341c80960a074085d04144104001081c4202004a4490b032000040d850082c0159a007806e89010700000380e90080d0020344200b51a107108008071110341c41541d91001010400c0300304012048002807100e200035004e00c010b0300c81a00c88170400e959800d50000241401401e403a070b00e658a1600d20b00f0403004406010105010480496002d8000c0c0c400c1c5100e44009205410281060350040d0300030740050800035 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 115636375 1250 115635125 115635137
    0x30509010b1e0d0f0506090f030c03090105031f0303021f061d06060705010f1e0902010e060c010b03060103060f0507080f070c060f05070314070f0e0904140d0309060b01140d0c 77
    0x2011030040540304c0311150050780940301d5854000017161501c22601400d0711542d004200c0241800b0b40441030701d1810409182043ea81d4540d40c804580c07000c42e410000c460100440c80c000700309600043e0f00c05045040e1000100024000e5200303000b2959948100096400711494410000c00c0350f0507020ba201c04020311032400c00e038058913403e007164240300c500700e000750355000041c070700c0303464031f0701e21440200c401c0c50911600e11150300007000450b007800041d0142c040841d58007522142900800e801600c090b00300c410f036684d80e061100180082c1c0300c40309040c1e442c04001c01c0d0003506c82d0606500c5295070099201c1a07441700c5400321280b0300200026103056994100e10850045c840c00341501400b071076640841d250803089826180c011002c4d100303100380050b0800da40d03011ba0b00708404451701d40085644c00c1903a55941010030042010759054440360043c4480b6a81c180d8040d0b20965015019542c20449405420015203610381da5040e07001c81044140400140f41d2195084117000310f240d0310b824 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 115637625 1250 115636375 115636399
    0xe1c0306260f07031101020c121c0e040903030501051905030d050c0106051c0c06020303060310020c030702030613060b03030f090d061d0304080f0a080403020913020916030509010b1e 80
    0xb07030b410451560400c03280c004143c94001c43c20345c1e0420a10002000840307004100c21095045913565910441d66441700303100009c03040c003040b802141250003544001e0b00a211141d0103240c0240208001d0041a200d0341c0034109808160450312420000e441001d00148284405110143c415400c8803500d42080c3d9214040851281c480004984c0c1c0700d0070106820704100d4076864100325520154000008640c0140108030305944c00060301040060319400c01680e504486040ca0701350700c0340780c0010350517110340f2051158400a6154428110b8000c4004200220500c010180c49100d103291540e0101d00900020750726107000c405036484984110000611103d5200c0c1b049011000301c508518550000f140411011800b44000d0500c0003c81000e0014016031ba5140e078030601440c000a0700030781c001000214164060503003080302d81c0c0c000340400143d20b050380003850001040d40c0f1410001c0e007403c000c60b48241c0140261a91030b00011311226076418442c60a00d9040c000e581d036107038040703071400403 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 115638875 1250 115637625 115637653
    0x17040c0b041517070207120512031515090f040b0616051e060405030a0c03120501091a06070b01090b01140d0e0d02030301080a0305030601030f0e1c030626 68
    0x140010411180d0700300d00c08a81d52800341a051924030020f03100101801081216940480d0788404d55010404040c1d101e5007905041e480c04070b07410340c5101d50392000020701c4940e01e0700c80c0c2381204120040b2014a1541410b900311141c9024110840350010f0551410700780c2d81c50b1a0700240650310015190905200000d000c50040403901402600c6540100504ca18000c0c0c2d9582413011407400600140340b0307401c0694078035641e84a4684040d04100142c944041003520880c0002144402154148165611010000018840c0d824607211021001e2004040d504050050300c0311030b50001c5440549a10304002280034246601c0c130700341001204031400d00051a5803003d011044440e00740001d0002d5201d8100349000003200c1210155130050004000e90600003500d128600e606250140d1251a01c0005a01610256100084c11070900001c0c0107401d400003402025041e84a05078500001c0f0200c05404541d00c5018410510405038002180c91f1540000104006da2071021035105202d1084 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 115640125 1250 115638875 115638877
    0x26070f062004030c0b03040204060e090f1c02030319150902071506050d12020a0c03030203180406060905040216020a030803070f1d0907020708010606030e010f060617040c0b 76
    0x9412151903544401c2950103074000040349103001c26a100c1d0701c0c5401c0c00c2d5150128001c0e007511410084040000005046464a402c41c50040500050450143c200344c010340e030701e4a0900714a5045881000d48164070796540800c40c54000c07289170051480c5031940e4180c07100e640110103c5a4520f9221004c601c104417203580002c00070714010800503114099032810383c2558149e8400090500e0a2080912042e910481e10040301a800402d0845541039a030302a030805504080142c0720840450300041416008001402e1007070301e41080070750740e02ca0b42c4c0401044480c80d02881c40003845500d030a0046003000d50090002207240c22640300600340c00da00183c0f510a80da041100c6440000c014401120741010f031401d00c000490805105460380707a910f80050305c91380a6401d01c2400168040b0f040c0700d00901c4500d01a0503100300900c8003940343d801c0680902003d01c185032180d813800038400d070201250321500c402d40d0b0a6680300b04204224141807500070501800035210307a40141c3d000a60158820 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 115641375 1250 115640125 115640153
    0x61009080f0304080106090c09061209050a0b09010b090403020715020c06040618090612060207210203030108070803030f0703020a110a05060a062403020a0c0203100b100c2607 77
    0x580116543c0f82070089190030b5880d550700c00072041d41018030504003250441c12020561b007541ca8a22616003100300d428025011058000c0c100e80035029210091085280c000d03480354640d80024460b40c0001c105221b81d1200c01c4030050010b8005c024248880c0141c0265003a10050a10440b015041c1c888000b98250744154401c401003002d4500d03405102102e849a4002042101400c014032490060350603103199884400820907640002d20004022400540c0142c400c2c17040603020060000c000069541e42c001e000d8850103104240c1f00040740381000080320721031038080f4881100d60b11410004d4020b03400045540050001600944230000d0080000d0082c0e04d000714001c00c0f00d070510582d41e00444040e50400d4020310280b4410302d003e01c1a4680c00105140e29240060f541c00c0c0b41341c41120392a00c0c00c50000d61501824100b03900b1030708a034101c1000c01c0c5007102c100c1d0021aa00e207003a240c2c8103a00703d00400441e881c0d15043c1040784001a041a454031891400d0b1522846540b1665102002 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 115642625 1250 115641375 115641403
    0x1030c05150c120c0f1f0c1110020a11010f060302040e010c1403070306080a05030703080f0601021504170403051006090e07090903091805070f050c1009020604090c0801080105060603010e06100908 86
    0x84070411009800c0b070040e14840c0c400341c00e201f030341d000f0061801510389c1c0200841041050700021500c41d01442500400c1003d40240c00800114420b40382d204050725444c80213a00c280e00f0450502800b01041c8600e0403652000d0f01d8918100701450140c4940c3d41008103013006140c7e03204030020394008140115132100740310b031015503074070405031401a14150001d810701e200c06006c041080207690b0000b9103540c2c84a10160000113650322850954419000072010000c13441012030000200200042d11105016400109010380c90701c900059044880c1e549850741c0700c0d8810364003000090200e510080c1e440740645062400b050b1202403000d5240040e5010415081c3c2d60001c100c48075600000f00700356000189001441e048441034000d6407415045010f130750250b5103e00c55030466984004590040100800c14880c00824050180038280f0034800c0f00d0042d400e000010320140f0b05031040f20b058880d443c070804031503190141400341040c0c9900000c010b00c0700035000486d001d402004403054a800e4 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 115643875 1250 115642625 115642663
    0x91503040309090c08010501050c0f010e07140301150317070b040c15090b0f0a1e0309020a0f050a090f2315010c050d03051e01030c05150c120c0f 64
    0x10a250003081d40c800c5030f01200700c040c9004508111540c1c8180b242d4110f600034a0b005480d003d0341c0f00450304140448034500703180e610740254010301c0310000c00c0d0841241d0306c01025000355204001410f080e10510700c103411240100500500000b00e00b1101c0543c000e00c00c3c0545410007100d540e0310320741c0410540301035a001c01d90510401c8403410401c0c100c0314240c91494041d00351841d02e100e090f40c50140102a1000d0000420483c0d04980304180200781d92145031000036903070310702820160050112070800ea000c0e280342c00e404156138041030344001c00c4800291241207010700d000b41d000020804005900a0701c0d4527080901c0701085000354050b00d6505006241d1114202802d040b914101d0b05101c640c1031000c8040c4003000f082011901000725520390801203803d9849405180f1806c100d0366526440280320400841070028031403080302900e4096503054410400c14841980301e0260024010456100e20b180c0b0b40301a403c503018210000c0c00200b03d07451110203400302810401298441461150 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 115645125 1250 115643875 115643881
    0xf0501050712062133020406110d0203040603020a14070c210f330501081002070503090f010302211f03051203040f06050106050c12030c04060e0402091503 68
    0x80724030850004010220034400002c1500f4002d4280501506001c0d200074084091511039110030074172032550701c25030740c201d0b100c0008160a0300001d410a0146d14009541c20100910100c030000702c9007244010b6400441c1800e01d0907c00714082d51160040c5010040e941d54441042245140a02455846045c0f03d880f0a81005108545d02d4154480d80503040740095014003c40c005036040c11402d0b801141c4400010034007a6060f05d070b610158850322901015000d43ca600554581c4401c0c1a5100e240a95400c0b011078940b05d000c2e0f010305800904150000c0001e84d01c1807404124045000c43d040c103000d4109001104d811100c441d10002011800e004802001340c2c611360521105c0d800303004040c09444c0f0350304540b2550740e9401081205909424004082011701c268940018512a440030042c882503855403802032245e000195008510710400078030f1640c180d001c0055905c91500207000504242c82c0407412a0b20031481c17042640c22540c2004208120744407486440b0f02071200300ac015943e42 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 115646375 1250 115645125 115645157
    0x1022505060d0b01110712150617030304030f0903020a091806060b0706060b040e0105090403021015030218070206070e0d05010905030702010909140a0902030f010c020607180806010603090f05010507 87
    0x805001706501854000070f0060008a0882c1c12604210b0341280e4100350f07031254400e07600c00901450b002061b030103c12a4850032b41c404000011841103109035104400161259403d0780c200d6500d0100a41c0441820000d11000180b94043d40301c03603034041141100c003d0562507035412101960020240c5803000280702061148a000740c0c0001c09041070328501d03103450545503a48014043c081c06104110040c0802d003810f10070060520051070048080140c85140310300c142c46003040b88000c23401080031540c0c3c00d60102d4080c81283c85042aa0050920366540f600704844040368000360030740c00030f1040c401e000072504c244510801e0912034002140e035907a050002500302c8007036500110b442420501c000701080700039000d66030070240c4c080c0d0100c0c0d60040f0388000390a22210b5040f02c505076281c00c540468544d800107000d8020081500e51785c05440300c070305050a0446880c040d0b104198400c000400130244260f201d10b07400741c02069001c116614030b0392110b00391807003540c07040c00149485010019503 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 115647482 1107 115646375 115646387
    0x140a23130204080604021507050606040e1501030809040b06041a090f1008010315060317090102150a02210403080f0a020c0a03030213050103090201022505060d0b01 72
    0x20382d5202d20301d5603643c007001c590a900c0382c110501c3c2d2441c1d01040d032044913411a0400040d041c00d50b5903200380406000490306148a6104d400f4240400001c02c403440c41c060f62150501541c0d80e296102001301b030f100300030390b2584128402c00c01004014001e0301c200d01e055103401c800b1600c0b580e81c00009004000282c11a0350042c640c000c4003441c8682c410f00c11416284940312101c4c0050300d0040400c01c079556800020805110042c0302c0501c1002c00b400f406070381c501441181d280c031402d054280001082130f00d003c12030710b03004143c02c0d03d11050304000100040c00302003144258a00b40d24002d082180242c551a94002c0305004200008140d40440300e2a8814004540c402a800d2500070020340c0104100f0146006285021a55600c41c0c080d03c04226016402044a84590245020080c2200741280030020364000c001820352a40c10103001000850140000c814480390300140c07032 = true := by decide +kernel

theorem cover : BRFrame.Cov 115467625 115647482 := by
  have h0 := BRFrame.cov_init 115467625
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115467625 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115467625 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115467625 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115467625 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115467625 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115467625 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115467625 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115467625 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115467625 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115467625 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115467625 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115467625 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115467625 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115467625 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115467625 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115467625 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115467625 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115467625 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115467625 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115467625 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115467625 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115467625 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115467625 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115467625 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115467625 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115467625 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115467625 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115467625 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115467625 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115467625 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115467625 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115467625 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115467625 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115467625 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115467625 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115467625 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115467625 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115467625 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115467625 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115467625 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115467625 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115467625 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115467625 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115467625 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115467625 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115467625 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115467625 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115467625 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115467625 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115467625 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115467625 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115467625 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115467625 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115467625 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115467625 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115467625 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115467625 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115467625 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115467625 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115467625 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115467625 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115467625 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115467625 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115467625 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115467625 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115467625 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115467625 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115467625 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115467625 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115467625 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115467625 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115467625 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115467625 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115467625 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115467625 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115467625 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115467625 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115467625 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115467625 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115467625 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115467625 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115467625 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115467625 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115467625 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115467625 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115467625 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115467625 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115467625 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115467625 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115467625 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115467625 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115467625 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115467625 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115467625 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115467625 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115467625 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115467625 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115467625 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115467625 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115467625 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115467625 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115467625 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115467625 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115467625 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115467625 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115467625 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115467625 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115467625 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115467625 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115467625 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115467625 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115467625 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115467625 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115467625 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115467625 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115467625 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115467625 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115467625 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115467625 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115467625 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115467625 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115467625 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115467625 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115467625 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115467625 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115467625 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115467625 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115467625 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115467625 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115467625 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115467625 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115467625 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115467625 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115467625 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115467625 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115467625 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115467625 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115467625 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115467625 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115467625 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115467625 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115467625 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115467625 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115467625 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 115467625 ≤ n) (h2 : n < 115647482) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
