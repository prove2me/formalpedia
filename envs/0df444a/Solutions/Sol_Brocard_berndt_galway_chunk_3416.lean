-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3416
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:36:10.886541+00:00
-- url     : https://prove2.me/submissions/5766694a-a4f9-4144-bda3-8e2e50a3a665

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 614208633 ≤ n < 614388489 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 614209883 1250 614208633 614208671
    0x5030406030e031305100512100503010c090e0a020a020109051507030501050d02030a060c021002070c140303042117030702010203040b060603070e090a020910080103030215010e0a0915020d 83
    0x30002c2658828480380400b034050080711010f070b42c400d41d0340b0783d441510b01006403064016401c43c03d800666031020000b414031180028011500110000d1081ca04d0b10311060f1810070350307402090202d012140004040d00c000744c00402c192001391000040120b202e4881c207041981d0320500000d11072400e03051000c2d2135414002c450141c0801c5409285207440760740017075690402c200d4020719241e207960001304014001d1002103602d8400d6201590307200d11626101c580d404560041c2582d44500c0e0240710614200013095600f61049000b07000400c0888117050040700c00030103000c407007000c060040320300c2820100020314080c4c002a000941c07070b81464502a00442e60051003640100018820060000d42c00052481c101c94259000c00803034441d034008001030302c18030101c3e83d00000300464460a85502c941e1282c100d0b8000e0703081e00c0c1c41c25000a84498000313028440c203101c011013500031032100241640700019061140c00c640c0f01c0b0243d8005154140c0c3c210220b880c0c03d440d900c1ca2003d1034441c884d40 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 614211133 1250 614209883 614209901
    0xd05030408070b090f0904030c0b130201021203042a1e17160918020d03050a110106050d0311011409070f17100e0f010f1b0206040b060405071202070503040603 70
    0x1400d94200130385040441d03946000700d609288210304000108060500850f14030340040d42107000c040c0075241482040c00302c56489601280148503000e1300440944800c415a0b0007140d00c000d1704140038282030b120181d1003800400101d8441c1d4081d0000a88003491318450140b09900006984030790f15001180348551402268842c10b504111800d140c98000d984015050b600180e2000030409441d04211141c0c03803252600940010310302d4a841d00303154008029004e40c291341e03a1440407108104514a090341e8035803040580201308610080e000a0089060b00b6a00c4210000007a044904035801040340d40d055696000e99006064144072460280e00c94801a042d0b100c1c802000e150744038840c40c0d44a0056042280720fa03511540440185401e0000b50502e0010100a011030100202002d0080015494100a401500002007800ca0020903010310039034002400a4040da80e0505000180c40000c29400402801c91b404600101d09480503205490007200116201e5081c51809400c44020314 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 614212383 1250 614211133 614211149
    0xe060d080c0d0309030e0f09180c0d0f050c12030f0f0c0d1e0212041205240708060f0315091c0503010e09160b16020d0f110906030c0f030c0d0503040807 67
    0x1514082d26234580d40070f200d8020741d0404000d404840c0070701c130090401c050610420707030021010403044140024000c0c5101c81c24052001c2e60030420148003009051148841c80e0403494005004d0380c400800c020001d404200718491f055480d0a0240310340724140714120b18080d0100304c2040340d240b103165800040c81ea070100903000a102e00180c0e01c2c114038242c0228440d2010302b200004040d400c012050002c5208c2c2e140d180c0c00101100d00c01c28042039001400c45440300012014400504145051114131854a1004c0c0c00360445095540b07039120f00200c010944d85881c89400c0800e500942c2d4200c204030310442507580c0e03035141c1d414a8072810f410000945001d050390312611002c0c460340c031011246c00c1144c05034001c099480780c9494032460302d0703100c211000e503104a005448100f800681c81c01444030601c40c540e25412640c0ca00d04201110b03a040e20410341507481100d41c100355051070340045049181c020700b00c2e940c2d4010103000414400c003c00782280c982c3c1000c201046111380800811015001c0c407 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 614213633 1250 614212383 614212399
    0x901090c0618120203121c050a140f1e10140301020a020613050a0827030d20030d38011e210c0f090e060d080c0d0309030e 54
    0x2807810b00e0600c0a80120906820084400411503804001100320780d2050b0440e01d46900c4107186103c040140041d01e40e60050400340040c54590303003031117038100d0030743c40e10700648440c1c0b40c0b0074807500c1404000340b2483d0510601141a10a215000c102521555182890060580c1092031071500600c2031056507000c2d80c010300502d950181c0201e501c03903100e202135000f411085a5800e041c1d2500242000203841e0800018580800c1d141805000e07000d07980c415103260203d41e8040505960b4120010001c0001d55404160b440f04a2101000140c12800d01308690414941803558000c8440c0c1c070404400b052408100c52840158001032241d20320040b640130000c4207806030010781502d28014035000f500300c4071303e48208624040d1308880e140318141c500c2409903001d0305d0740160040a4560300140821101020807089501c18241002620725201b0120903d8441800780a0b1303441d80158115a644000c0c0050380e10074004000e84040700c03a840d42c022544004a080c054035018111707036035501400007 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 614214883 1250 614213633 614213657
    0x21905180903030a0b060d06091b0c2001090503011e1503210306081509210f1e03190b010801031e060b0d0501150501111e010908030901090c06 63
    0x2000c001d813584440c008101007540711100f800036a19103d0b00382d140881c0780c90240041820070032940590043c07181c4410303016900c400014180c03260010300e035005040150611000540e115140c15540c40032406060520704140c03614006401d55240020007803001d016082007000d508400d004140c03600360216218414a800d5803a124540811116003882004185010602c8d2521941c002c40040620006540b410600e580c9001e5a500c425156188103100e1607090140d40310186818403050340e0f03180c0c01285403451403090758400e40c0040c5071466901c01c00ba0b041e1050070034904002c600c80d0348000032050100c9919a40d850444045003821410011001c0050001800070304d0b103100e45007180101c0d500b600340c80e860000c0c060100200102d80000040c1c1c070380d10801005402a46200403c6020494850b495000458851110001d41041640000c1f5400222010340f240d8616260b001c0002041149464592000a40c001c0d00c0958031695240038103030510148640c040068483d51901000000b6 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 614216133 1250 614214883 614214901
    0x1050607021c08071403030403030e0705180612030f031b040f030f053d092307120f060e1b040c030e0d030204030210080c07080d020702190518 63
    0x10703a844105068560006400c1c1030280702c1054404d50b135805040d00303c0710401c0d55103075912504144c03801c50101303003040500007100201281c500240c41025050b80c8003d40416041c54142c007000c1c00c110b8008034820b424036450401480209941c0a01d041055502c1c01c084030b00c000100408106200700034020b02c014020002003418030403c80313030014000d0124107050b003000360504444442e1f43d40103454161400010800309801c00e0000580130022401850940340000c040c0e4000c0f240081281d0b01e0901680d14031081d841e0350b113000880230f2085603610f45c0c582c2c80f000c0802812060030b4881c1d02c003429054041065a0060744401000c0e40060400003180e4008003070000d641000072482941c071482d81c2004203110782d1009102140c0001100c02c084000c00b00580203600034003040c1d0085d0002200d202c1c910b4080c24105d401003250103c150314009468544900542201d030003181c0440c0c0802526016a641010542c41429101c21105820f86040704002007032030020101440400d034601008010300c = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 614217383 1250 614216133 614216149
    0xa0b09070305091b130c120e010204241205040b010f06030213060f02010b040207060e0c370302060d06060e030a08070b1506040311032e09032606090105060702 70
    0x51a84c840c03400b030703025040002c01c4d4104043e489000f29192140c4045280da008010014001c280a400c01ca118540c0d8001c509030f00c50f6009650070441c6000481e401c0340c81803e185280c0303000616052101003500246101541c00640c0c0558000828800621030342040c0503840c8010005420118a0300d02c007122000a0742030f151107800140000784d407c0c9004035000390000048072800410840d5103c1007890060014824084d11400714411103c6030f50345406d0400c00d0142600342692a02190401c1003401e40b071580807812440400c0304104d20010040e203c0310007600402c030a002000c2221410440c0081100f40706042c40c5109901100422003ca940e0008a51210b40c2208145125548110f101e88215a4903844150880c0c0000340c00018002500f01501180305c0882c00d55100003040d600d010741016089503034407080300411a13554420562a400000d001e4400d0070520502407043c60f1803488407802040c0380f84a143d024042118a14201a4290140c032080310000d040c100c82d500498028 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 614218633 1250 614217383 614217403
    0x80301081b01081f08012f120103170d06060302121b0a080406060b0319060f060503060d0f120f030e160e0907050d03110d030902030309060706090b0a0b0907030509 72
    0x1510a4840d0100d00941d134041d06000d09104c4000740316070750b20481083e00b20302c1c00d507045460380341d8904008901040c0320b408403000c010300403050f46071590035a02e4500d01100011049801c01c00700b00078070a03502c2c029008401c001c005941700180c0b039500100482d08100b0b0000d007400f01a03082c805102042011107825509090710920b007825140d6114a480001808180c100c1c160000d40481041049903040c20100c050307a00540041c00210b035030f1651000714a00a0003102d0200f10f0505c009010b034144800840340c0e0138041c1d80e036100205500c1d02d842281440c00b403081d50015295444441c03190340c16000d13030302702e03020b42000504840c01c604a80c40c2e08100386001c0c40c0511000880411010303001001100d002d040004c0c40c894500c2c0b014680a0b181d00c084103100502809400742490801c1d00034420310301c501d03070040d010794a012001820092182c2c0840c5c4102d5071582d540e00f100b004180100f004a10480200030000b03403ca801108000c030300703070740180f0b2201014101002c1041900000ca442d07803403 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 614219883 1250 614218633 614218651
    0x10506160501021b0606031513020d030c061103090c031c050a02120f040303080a021c230408030a05060d1115190f03060902130302151303080301081b0108 68
    0x40102149400342c0a8840d4892600304065680500450130350040340d041d010b00c01c2107048910400000e00c044c0415007048480c101c564449004910160406428580005200e0310340300050311601d945400c110751088a64070480c1c0000700402070498001c0054201c1170f1000c0700100401c41c040501c1510110340007541c6001c1060201c1c0740c0c51068001c11240030b61011030440c29445207080b40b1170840b290010b20041d000949040042003041c210341c130031248a1000c221001500f0922900800003800c1400a0a40c0710100d9080380d0101401d0210f403035004600c6498202e40d20704202d0740c00030a46002a005510a03640750004100090850003160800075003503c030500709a0401a080b92907006850646142d6050301703221000a5034004483c0030462140c1d00c04101d0184c4401400041303010384500000b0b03e59041c40c1c180058a0082400c16006680c41c40305450500840c103050b24055150723000300c50318540070006104010b0144004802000c4052510103402600070000b02074403400b40407149 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 614221133 1250 614219883 614219917
    0xf0115030b040f11060f07060501210303111c0f051e040b060604150c0605010819060203100f03030207080c1503070302070311030307021609022a07081203041a010506 73
    0x41045105180031303030b418500402064840b450020740030b2650313000080446035580b07040004038040b8642c013016080d42d4a424440d001d01c2806640560003003a1180c080d4010325010f224441001400381d050030f01e00d151002e0b0105180c1044e94010080d2180030304113109516948140c040158103010100e03030311035007240d1558070b95128040415054405c5401642c045081c5040034001580c11460140c2614070440040007580c3c1d136171948585580c04c500b025954504412408008248950060b54219050644a52506a56070b0b48280e149110f580110090f0b00329040800144000307101c070a01141050310721a07441101030401e0219444024510803c2c1139001c900e0708241841207100a0802c600c0f001240d07075900b4910400b965400d01006002120710380c154020803001064000d40700012108005151101c0c02001c451100c4075160301400b8040c4100b060004900c94200070300b501080c2c24180041e6a400d007401e220514410084031500c3c507071420001040552035000c2102d081c2808210542 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 614222383 1250 614221133 614221163
    0x31b0807121104091d01110318010b0307090608070b0301060512072105012607061b0515160c0b0411040e01060b030702150f0f1b0307020f0115030b04 66
    0x1c001c04210590380c406002c040741c0030448020a6015540000080d030b00521a242c0840c0c17200d003600c00c00c2450f200303915001c0c00841d5014480c1d0b44100c2107040407400119282c1042d10119240010315840400707095210b40707040006400074841c0502a1199070303a80c40c5190f05000010f0a140301d54000f1541e850301502c00542c8142c414410081002c0181010004120404401002506080c050800c07d00112140c8801e00c8e2050440ea8280032504005061064a03000d01a1000500c01400c500190740101c92030002410600c1319100001e0007880a00c4241440078072001c10001d4a0145020310180d00c00c10f8020440545120782e1144e4440c602000050000000ca4050466142444410740c200a004240003030607402540c821040c40d0300703c8210514500e44122080f46c15210f16020545000c041411701174107008656101d803560344070307a802c00400800150903500865006005810005515000300428040c000321b5405205070345005030300b10b0301d030300e146880040c1c03004003400c0c81c2d90581 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 614223633 1250 614222383 614222417
    0xa03170a0605100309030801050105070c0311010e03060f01031e03080415110c070305010f0207080703050702010c38150910090501121106040308030c1303120f031b0807 74
    0x54405048090911088100f4420010380078004200c401c8011503043c00c000324055110f001543c4245800050300704403185152654240700c0d2483e2110341c10868070014041c0c103a2400c215050154900302e168155640c550305106004c5000311070301d00c40010500800802295111000541140c1c20580301d50030304540c5d0042c1030041102c9201d4405195021840240c800e40c04100f10080302c0c00b80b0020f01110000c054110b040340708001000702641400d104000c0480d20a9002e01111407060500c50400092030b250740821114143c02c4194440300d03482c8411155010141c020f144d0350044410303051604081d0486441c002000040501400d1040d00082e25a0300e04001c580003002440810011540c458000076506d2180c801c2c142c03100c0041d401002d40604182003110101da030000e1009003507483c0c0d80303107031041544030b00200c4100c000c4443c4e005c07000c52060751040c84054032075102c0a20401c1c0500000e0159040c0c0d004c0312141c40031000003118800c0d04208031541c003d81c0741c500088030046041c02 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 614224883 1250 614223633 614223641
    0xb1003020a020705270c0405061905070f0609230316020a030c26030f07030c030c0203010f05090c04051e0c0c1b0a090209030a08090a2d06020a03170a 66
    0x2580e0f0002c4604c1105106640b5000c881d0f0a100003441084c1740c03651080340010280c82a4031440f030300050200803052581c011343e44050490803003407030064a4680c154581c1c0b9942014018140c41956841c240c030010001a0b0019170303c103103000081c580c0007400c03240a42c0c0d100d00030b144614089007495081601155038a81d403681c00f030b6502007502e002e41501d80c4443c01400100076000c9030050701c0240d0005407154000150b40c4c440144605681c0341042507030b003c03110300c8a040000c5041c0300004e0185801a50203000784030300c49083c0a0001564031302095002d2030800341a034224010307440d28003482001003012088503445081900f004843e9111032405001c40e20030704071070404502801440303050014043d420320040c24401c5a16000e183e44030f0408404a11035140d426901d0f9200c0141980000c40510190400301d200030f140701000e50b170b900501c5444a0f00300001e0040903a01c0514815012000e800f480098801c0e0700c0101004842c595000d00980c40301d88000346100d0301c40c0001907195a050700 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 614226133 1250 614224883 614224889
    0x6080a180605130204050a020408070f03080406120e0f060411010905180c0906040807050f0406080613080c01060905190905030f09190305100501060f091404060b0a0c060c030b1003020a0207 83
    0x5c100103d140a18113100250817a008030145070003200300c0000c01c00c404000c00421b036034001d170500e494a490414140da1003500b0310890500c060b29a1403042030000c5c00c1c010f04041e011480083e1100e8902072034590120844510b9090510400c07070020320907502e80c40c448030008043d840f001e07a815120074656200a016100501d42c1c400800180851520000319801040755401c2c1c03550064818807031b0400041c2c49a0307005010f5241d11040c00900c0c40d20910656860341750040f0000c81c54000b821500743d0954001da003048000c240c940e418451081740352500c0d20390160b1018010001e07020076682e01602c03031080400a140d03e40340420350021a650b0302220381031454003061403504190380c0b0715085850349068a400075100b0326281c00015024010701001c009003a140d0344400e0340d94141040004003260551800c1d40056960300c011807000710800040071992040c1e00ca050201c0c40d80e2074442c0c155142a8030b010200341c100800a0f0081c1c036040c02079548025075090141c1c071505460b00407460540e5540c = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 614227383 1250 614226133 614226139
    0xb0c0c15102d03050f0f1209041a090c04061d030a0213110a0c0201020f060708060d030c051002090a1a09040b0f0d0b06030f12040902030702071e06080a1806051302 72
    0x200000100f01300000c5440c07258410303500743c1790080d60b4000b00399156011007145160841c8104030300c040300d00c0e00d03a00c500c00142084011101e140714450114460000450390000c103001c00140034408560840c40c20000c0b00002c15800c80540c803400d021030b88881d00300d800240a0062a11030103054083c81d080324002d80e000020b0709843d5108c6483c020aa044480740c281d0240c010304c10240d26280700410003c2c820140c94803404900d07141c0005000011901000680801012801c2c40c40007610030711912015890894002d42c0351400790042248500c81c583c011182c8401e241006408070144406446140900700c400040406a44002c101000c4030481100d51150446059101f0051010303102406070006400326803048001d800301030355070120400c60003d501c105000800c51100950002c651050305c610540b11481e40e03501d40c034095215809400b0302c3c01604281c3c10b10045a22090407640000550401e22105882c14008007202c21740300f101070b241540721000100035800300200004e0495000d = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 614228633 1250 614227383 614227469
    0x18151524031803160c0506030402090106110f03131502061509060114120f1305071205011b050304060f0506010509042f030a0605060403120302070c030b0c0c1510 71
    0x7113801d240421070b0a0022204460001c0740410035007000400d481c42241d01403c41c280e2a401c00c10103507921000700948400902c1007440b030410000d03003800544081c03000651080348607402c02c4400722a141e00b02d0410421075104504100c0612440401c40030100000c3d190382406807a22001202c00120700624a81c0b1030100080740400680068200c51150029104100150720707828040450010000000b0f800c0b0340c020348080c082e40900c40d040c801058865000006e08425815212035600c50301523070a00454004010003007408030900603160400320a500c10070091410a001a100b4020450f20b903000c3c84d235442100c4030140c0c40c0200c1c03002440749000041c0604400c1103110303010303a004484441005090450005d440d0030003800352001d981d0302111074003140c107500707000310025007040009039505d0b00e400d20000301050001d01c901e80500000072919a8170200c00b1310381c0345040c44071900300001020500410601c000c3c000040c02c00d075841d100c204031503000328000300000104d06450b00708041003a = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 614229883 1250 614228633 614228647
    0xb010909022106070e0102011a0105160f030f020f0307170901090801050a0b0307080d0807050d14180c0a0602070b0f041a19020102040302010c080318151524031803 72
    0x2c009000c604c90720303c545d0392500703e1040c40012803d131860802a84080040220002410b60142c00508000b0180107008500c140742512035002d452201e10080d408100d1940d000c4030b07002d6051007200221100d0400030362502c0010f50306c1c2684402200340d0603001d4030011808256581c80780900300000d04091b0000d0215042c0110b80034020400c4804a910074070400d4030002c0d040c140816040c0581016483cad0450960302e80b0f80603201984040c1d40400c1465661501440c284403c0307408602a0590b9008010319039100c0d4000c5180c140c002d25124418076076640c0800c40d203680041d2181c00c2d41c40c003010483d11607144007140c5102e402942c1102074043caa4001001011010001815076540c4060030341c42d040d00c1c2094164203d1145000c040d00107401007642c4400308000780011754204c100c0c80c0644078818954039145003840b500001c06060b04550f042403101101200d10002c846000440b044250400c540c1c1c206a0031a05c5031081e860801e5021002a1441c5800352a641c2c2c0c3c0c21b0004141c2e980c0390b03a = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 614231133 1250 614229883 614229949
    0x1050a03150603061508090303070e0d08220b18040b01020f01060e06030706050c1b0616060506030c01020712060c020f03160c09090201120908040f140907020105040b01090902 77
    0x41a01412191a8180c0303c032651716441060010300580004c2d02039461500d80080c2260154003c0030300d503400003284800b81c0d0008400500401012480c90100720080821483c0c680a02201d036018000e140da00703000f94100d512426031000c00700e44003140d0018220150000503401c1c4600c145104a141d40780a00009007801048440d0744141401c074143d41e4a90340b5560140c0b4903004490702c4442941c01814280b04000b200140d031200b91000034031a50800005202c1e554410f0302e0a081100c0f01504ca80521020741410003e010500d4401d0000e000401d0410790314000c14451080c01400136501c41c480140103034007c1c84030341440d0760704005481d070301c0c00b50003110501989420b00c1140d0880b40c544000034881180d2203543c13a00c1d541607442504802e58850782201410010f1400d41c0e02e0740040000081108910802600400e0568607800101c82d10800b0801e543c40010f26030000e59040070100000030f0907141d40f2034150350366130000241003078260011900c01d504001041c102c51500b445d000765509 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 614232383 1250 614231133 614231141
    0xc03200f0111130b03370606030e032b09051605010e01051207022a0108060a030c1203050705010513050d111b13020f03071407050601030201050a03150603 68
    0xda11400034080004030303403040c100da840781c0c109685202001480074401a0346600085030055002c2243c0c0b030b021200c40284150309141c0500c145051411164803e500c481580162401401e09007810460020500d0341c280e101d00c0380107808000d40340007042034150702251000a0b40220a1003204020000d610325207a60b8400003018410150083c4880c00105588503d42d1940d902106a440c02c1c24840619142c040c0e0240c040c00c14415409940c0d00b80c10703e00d000003c5402e0700110001d070f02040b0031503170300050302c4601d010740158064040d41206002061601c801c450468070000c51803980303074815050446282c011440003c00039420103040c444c1604652251034240d6004209803442141349580c103941000c6038200c0200184c00486d11074031281000d1804028142c1c0141a15003c020020760000899203e4040010340703e1022040c02a560f610181300341d40701d80400c02c050b01d840059181e00355030702c005101c001d04210300040d5801c0c6d558030235000143c0d030381c85034030388120f4050305c900700036000d8 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 614233633 1250 614232383 614232403
    0x120f071403040801020301031a091005070e04110306180c030c07080f030a020306040e1c08130b010801230106050405040f141e1b0414010905061306030513080a0c0320 73
    0x140c0442900c01369442400440c07034080c010742c2b8020050341c1180803280c005010002d00c0d40d400e200e040c1c60358014079200e600854100ba4901c001c029a81c2c6003400400200c00c0180300100180c03416482088281ca5000b01160f4000001d80038450300c40780b0b245000d0380705105070311b4681c86841c404424451968000c3d0090741c06400304450510609141d110a181e0b9240000c0c500e5980040480484540070300601210340c0003200074030030242605490712600c01d404000c3e032090701d01d0b81d034940500e0301d14a2075001520390307030135900c100310082e5140c44001002030240e07010300c92042d81e4403a840a091000c960029080c0c1c0c1010000c0340c0345d0325100100c0134002d0b0f90f2540005c0001c1c02900040c10000e00c00701c088002020502c0752505181c2041c15050394280440d0070700741400140b4202113103c0c0d65401c05448828116417600104900f8004000e00343c0300054981148100c2440e080c0000412990030b03544c3e890b07030914010034403052504084441811207100841e500c001e501d442c2d81d884c440807810041d0 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 614234883 1250 614233633 614233643
    0x4080f030a020d0c0b0a050903041208121f090c09051018091e05040804030203060c0a1106070f3c0315150c03020a020a0e0103030e03120f07140304080102030103 71
    0x190043c403542c252007010709004014050214000060090f0351781c1e60000745c016010000b00c0f03081c10384403140c400c000c070090003042c0c480c2c4601003100070842300003015450303110641c6015001c80810f000c038040b0340c200c1203004451a07540c0b01d8424030354142c420b5801800503d4001c10103032a610f03240308080c181d1a41d1031600305000b150981b01040225043c080e442e4035081c1c40b8a001c102035a6a1a424004e1074060002c0b2541502004000050ba8080050a004075070000b40035507500c0072040003400004040481d084142c03c440100400503421010010850710181419000b00078402700c0083c08510008000c210a40f0301c554400c04030315480d888075410020798a080005002202981140c98218030619182015940d00303292214415000107000520070300403030303900300059030024895001c280c20920362090800010070034113921500c044000d4400350064a5203060342500942148a0341c3d180440c440c1d00080c000e01040b0512601d030590769034980580e5200c4e51030300d005a01035030080c8420740f4 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 614236133 1250 614234883 614234893
    0x4060b0d080319050105031b0406030524010f0317030a0b13050108010f050402030d0f02120315090a02030708040b1005090c0a03110a120902011202120702100b0306150604080f030a02 80
    0x41401c60f510510303050310310003002058a0001d0580c0c1901c0d100a84050b260082c1d111240040000c0d070401a56036102407000b0003c0c0070902c00443c01c111110140d01c18800342e01104400c101003842600c13505524055100035513030b65a16521600c02a200366140039410a0700311108040c00c49480e0f0100e41682d6100d40240312160201c94074805a83d0103542c040c2d410380001c6540c0760001d0250586800241d0b050064800906510860120039002280c03214001d03142c2c0138180d0050316000500940c849802e440460031414451001003140000400c0182000314090110780750400602261000f070900401651840c9052041400ca54001034032a00110f4140a600251070345d210081d00d4081c0125a2045004000c01031a2006003001c0201070341032044803401d005e8284d6560000740403030005101d0400b00c1d0b0030022402441c0079961950054010300c1c0040b408041d640100780e0580064070850303011180000600001c1003445164010381c00f620400c0021600c901012000e451503140c55001d81d0 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 614237383 1250 614236133 614236171
    0x1b03010603150e1c02010f0b06042102030f0109030507061805100f15030b1902040503030f0f13061e2102130b030907090b0a0608010e04060b0d0803 65
    0x1509031482408001e2003404a100303030008103030031035000400c91100a002c551003041040800780000c107085200c040103035107038400c2140020300d5009500c80444180c410701d107403500d408040e511000c2001028500380c001650110150349e410440b43e20306080d101c0007001074030072518004d070056005000854180f4100782e130019444140460030003111340c0020141c2400c0b00b0014010000382076051400c0c03503aa503074a04805a8281c81d20150019511480c048092400c009081405199940d250b18503607500401c800c1c0402c4c0c03400300c04d0301e001299094419032610880c203203007500d501884c0c40b401c40310b030034411001405d02d0340a007040240c3c0d0309440c0d8042590007482e10031194011107210762030303a110038180c00c5d0302190842c0d4020100c0c482d141440c06d03491a1144120500c2d0b0348103503401c4545074401c40040c404500903220b10300c001d110440b084100d1030315210f0003424803d414405d0350940d103441e200040c180150380e00310980211000f400d0390440403044c50845413030b41041e40c482c1c034000325801a0b0 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 614238633 1250 614237383 614237389
    0x90209220204030507120506070c0f0b1e10030206040605070f020402070507240c0f02191410020f0d0807050d0507170708131202030f0c060a0c0206040b0a021602060307021b 76
    0x1146d40702d407c03401034800c90303603070841c15640003114110803100d460048207103d000c10000c911242c001c2e8604000a003414030b100205460301500540700c074514210340f0608100698610f000caa00b11146403e205884092904001c3c00e08a40c86502940103800010401c0800c100801c1100c1900d8220036043c500003000d960b0703c0320203440b0808001c04621400c1c400c00c04685100c1400005601c010700043c03d070840c05040003603581d1075a014804900c11982c00d404141381a04103905c4d01c140c01d100800480c0da200118903a25120a900c150034440742401103010f0901c50400c841d9140d5004205201500b01541c006007030705030f11600200310405000200d800b051095210394001c80d4007041e5800c141160780c482c10b030f150307001c24420419488200700c043c68100d42e80015155010030480a40164074040040d582230f00c51080042085410150070400000c001c403d1541e00306c600322900580321110b5043d107079242411504065030251000c41082227080e07000801e1150040aa0305d50042e40a610080c = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 614239883 1250 614238633 614238659
    0x20315011802030a110d0c033b070b0a0c110a122a06090807080609030301060f1812030306050405060d15022104140303010609090209220204030507 65
    0x412004404000c0c0e500000001c90b00610340042e4210800a01500c190300c0d03580d00c5030700403030012207015110841203c490340c0520415010740a00d001010314400418402d00b0000d08031000700c0d9410b200300005043d007801c104505005001c2c4501c2003039903101c5240c0043e06441c06844200c410000251b0080f4050825160b100100c030840030100014a2080c1c4c2c900b801d48110b960300d45000718251207044603045d51840c1c01801824162a80740c0c0f1141807410341803c00040360071514041d4440000e01c003c0038400000c4a04595103864602810690034a00b10354099504820001e1101d9450020505907403600b80e08450b14482e4404100c501e43e54420700c0240c410445849030b100f0400103440e0701040c00380401d001003020018005241110707110000b401403130712082c01c071080440d080c100002c10041200c1c13541509030207c011802c5614244000784000741e207004030058543c020400c00359075240d2860802c40c4d40d40b0229058001d0000d10000c40081d00940f0003542c0c03622074244001501c400c9628 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 614241133 1250 614239883 614239889
    0x6050301170d0e090604240807080604020f090709030c060f020c1002280b090706080c030103170f130e061504120204020c191a010e0702341202031501 66
    0x48000304110200c0030800070800052506402540b25550920911103031603d071f020180030441d0384500e0300d082a98440c607280c0c00e9004000307903a00c41010300016a803000480071a2800407154280d5560f15000d00b1030301c000d800d51009207180304d140b001181c91138000101500c080070076401c64005100c00f41c10000f0340a5010541e90150300002e504d40c04100c4020307041c50403401100048041010507658500362800d085034281c0aa070000340b801e001460744203100c02d8022014003a080d085504503241c0c42c207440300e0403415000c03007000010701402c042d10590030b4805980842a41400c1503607124800c0020340c0040307400303902c901107410b0001741c00421001580c050320172102a80d0028a4243d003840000d6100f81250b81007480340000c0159400c0032105401e00e414445d07000c140200c031007100e182c90150f40c1a0170108039904850108183d4940c0042d009800d541c644100e0268803620f1618404902e10b1041d0200c107074101e60f100441c0a6900e15900e00215100f03908881c00d90f080c008010785c3c030030b0703081c0 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 614242383 1250 614241133 614241137
    0x51e0919080d060302120604170f0406030b1c03020106051018090e0a05061e0115020d14040f030b010806071e111203071215140105210106050301170d 66
    0x640040106108601900c02c4020340000000e0140d01d0345c002500480c0045002a0907900a1041204101650490340c3e00300001d80b446c41c0c04d003001201c004886c0d020f98002c240c201941c0b0b100b40301d015034a2030500588c00b103002d24a4070500100f420000e02901d901d000b40c82c02803040006034034840348180c10304034454485c55002c403c01400c0004d02c00260021200300c0e42c2e640311f40310b10030380840c3d000e10009010f46025140102031492184a40701c41da4816400a4503800da07400c22480b00d540c01154119410b0010300e002034001803100b103180340307502480e0400c0000604c001404020080c110300114140d480d41012a18079a94035603003201c200c040c41d03141c0760f1035a220270700d01d09255001e40841400d10040c18213840400c4205e43c0c1e81a800d810450b075000010340403101296000460784910401c280d585800d0010440c201803d0b01300d881c5211902d141002400541c044030f0344402c50200181c0e4014200070910355a42d4500200680c00030b000724901205003980310098118005441642c40c669a = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 614243633 1250 614242383 614242423
    0xb0c0f1603030c0f02270c040b030721060f05041d070302061e12160c17090406030803011410030608071208130f1401030b060f0a12051e09 61
    0x1907070300f2620448000e00441d14901140742c100016500c02c042c44d01004281d4440c01540383c0c1c3e01c0c2840f1125100903180030b01840b003c01044c00002454021a0750164441c100007624510180c0d6442810154881e544801407a03c1e40c04600c09105c132265a0444408960078412080002051282021154103080280d4803140d42000141001e4018144203803940b000140300780485000003c80307522508039000b070320740840d0400020300e080c00c40140049000f8540901c1e080b400759074100003a00230b0300410140311008150980c1580e12034012102440d80580d02640b2940d403581400b1005410008080c0b240d0119141e4440b124840c0c881d440c01c0302c045e0402400304601e8111030310301c0c0042c01c981c01c1d05d111204002c801106811950001c000303045e580e1418100d1450014910b039440c4181000504150500d172008401d0798035141503a01c4a210012516070b5011480320544d107000310683c0c080203403400d12040140c0e28100c03615070000304c01c0d00c100c41c030219510322800c1616a41c560000440741090 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 614244883 1250 614243633 614243639
    0x1506060e0307060e150a03050105011412010b0d0f0204080312090a110108040804031208040302011506020c0f0a120605160504050d030c1b03211b1209030c0b0c0f16 72
    0xc6040c0c035080c07a004c05080401c0c41703d01591a42c015a0100800c0004603840d4070040000e942d1000704068012a0b2042a5050100c6414298029841880361030485400450314440c6545298402140b05400103070456940c1c0d070750383d4469203a4001301e403043d1502c92001d000a58001d4080340801d0050f0b0f2083c01403080c00e4408005540500c2c0241c025500500107010100020313800340c41b4040d070000b60303448180c0c00b441e0901d002030070360704810400b14151403901000c105072a000100d15210306000c40d5450f0800012002260b601030042e40000c880308a00501c4070f040c404d5560155001f0500121500d40032900c806055920784198861250004d920030820b5010a10034291030031101e1144484c0c8000c00c40004c0490f010558a42044e00d03091404102c5616481002031048464455820450a82c407101c0703002131860a152040900a4012801403541340c03031042810001655000c20750094075900d5102d000030719044494521007512910302104920b800000700484440e10107265003a915003 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 614246133 1250 614244883 614244887
    0xe060406080d12020906040b070204050603030a021b0423010311090c0904050414030309010213120503030106110708061e060103140c0d0216111c0314160c031506060e030706 76
    0x9006219220f030b540c0d092142c60750603941c40c1c00410080000d100515114407190041104603007010303103100c0c4a507108010700304200c0e0300403032642d1100000c01d000440b003102d0032010138090054000c18090000402c84100007200403034441c94182c078010302409012007113507820300419020665280010031001d00c2010402d180c280c01080e400352044410200902c1c4c0000b80700e145400540c3d15845c00c0e5004989442da4a000e0709000c1d00904a510700001000001d071501900c3e0310040c0685000c000500f8408009084200402c0009104040803500645003010b0810740d540c5c40300000311031901605000c02e855601c03034001c0355000c2d082003648540a032034105103040c4950080c000309208903024000b9041c5100c0400401ca00240200c01c14840da0500508118046402e5507071440d03040b48981c1000d002ca41e020801c624043c40c40d8681560314580e400f2039114414400a00800090b841d45001c010000c006480030400038070340e0802d10400307403602030076220098a0210590103603c00389040000f0f078 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 614247383 1250 614246133 614246147
    0x14010608070f05030f131208180703020d11011106010b03160828090c0308190212161e050109050c030109110603100314030702130c0509040c02031308070e060406080d 73
    0x34170460084600f1b0955480c080e600e03804400ca90040354102003000001020300d039803540d840401c0c1d4050103400c0d00715070000d2250300c64144041c0912142151030007e90740a0380400c0843c10015080311015a542c051354241a0300841d00c42112640c451840f2480340d000724415401004841003903100f4404402410f204000310040e0100c0254659129101041c2d5180d04400518012103901d81e407410720038a1b954200002d514244215808620a004400c0d491001e450700d4465601c09a042210b2500704181c0014210707081813810041174494000b0814154043c4001d40e01c1038003562158404401014200c401219002c4c00c03e0401c6800599503281c54401142c0c0300310f4940000f0a0175860347c88110a55184000082070f0750b100182400c1580f51036101e4042900e034622040c003554038050401400e900884c03040b6030250362588481a2418024070076548030144d01200100055030780d40380e103a90740004d4400d01101c02d0200000c20301c181070038082e032025a511500103113203044c0100022210f20b = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 614248633 1250 614247383 614247391
    0x1b0f010e0301110a1107080c0102150c040e13020f0109060207030b19180c050613050906030a05010c021506030604050a1b080d09140f1e1314010608070f05030f 70
    0x195030703a0703072000030404009016020003480c581d1542d01d24011720001520f40211900107075050b9101012002a503039001841240c61880c0400a25150b1504c8545886a010740e40010090350310200c02c00c12404000e004003240d2074000c450303841400350044015103c002d0740303000e62401a00314204c14408600c4102c44c0e00e070028040ca90418241d00c69680c144215031109400d01d10b03030b15802c66000207010a0540364006004100e0b0403514082c1404191256071000c2c0c800e8134019098030300010001e61f000d010460a0b0760300710000f4400fa5900303c40003502d41c0f9500d00c11241d45205400800c45605000400d1031103a903104000704101c152546070200600d58289004014030003051300461140c5080c03000d00006000c80c0c0f5040111810b187ea08540750110006d01030082000348020711841d0f440310300b014034402913500c030b084890b229140490700c200c2440801c52460760038041e40d120003900d03000e08075040714640d6407030001d5074942001c216646055280710000258050000c10700c0084086015604 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 614249883 1250 614248633 614248639
    0x50c120c030109051e0601060804150905060421030204120822060903060c0201050412030b06070611070209061c120504030b07110c040209010c080f04050607141b0f010e 74
    0x2030001080c00190950740314100498071500540100d44103800c0340c01200918105541c0031307140c15030400200030a6007000400113080f10000c2c1942d800700f0041540300250340d5801c60240c0d9001c3c6440e0414100f20200401c5407a2080130b445010000544244260340a407085521909146000340c0c075a0480c2e0303044030240d07813249188e26200c0d0040500c48031191008060039180c0902c3c06d49941401011640b104e61620b042da4100703810480002e0184803c04030011160a0000b45006202c3c0480c540b80140b5500402c2c42c0c0c80c1c11040000c800c2000c0152031594400c4401160507078800f03061020001580f03000681d80e480e800c40f40d07000202200380d4070320481c03e10b142050406039280c580101101f001d40304180030406104580c008507106019480b58136005450562511030a100002c000502c28480a022010049525120b0103048400c890040200401c0e00b81c17129000e00b000900048054803000f0a032181a80410080c10704543e0741c060710708001d0003075050500110066904d05c0150000d158 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 614251133 1250 614249883 614249893
    0x60306060c19050c040f090305070327090e16030b01171009200a0f06030b040912050c0d03060e0402010e01030b102003040308090d0f061803030f0504050c12 69
    0x4600c01008000000c1103000c1c1c4004d16604607007106001c01c13920303014014004141450050000700350017134100d030b1105505150200200316485440641c20400a0b200d11f010b400303050001800d800c0980060360082800000d40b0004442d0004141e9507145a102c0202901c414500400200030044d6107040c03030181c1c03002a240c80e058100014011030b8800d00c0d04803040ea00008880680401c082110807844505540c2c0e51703083d03810b102001c0042e000602c0b40342c0815440d5202124a0b440725001544441e0b0310510101c0300746010b050282181c0c100070709103807242c415424000c004510034010b000860700140113508564032150011100f68401c001d82c02d040c15100c150055031a1281c20345682d00061660300d4890302c009140000c200515260050780882e4420700c410700c0803420400031107002c207404582c01030200400f80b80290401c5507003d40a0111480e01d8140f040c5040d4684600750064401e990070484449030401301d00c111f400c29107001d460b540c89a0460402810b040c2c10000603e41d040c82259 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 614252383 1250 614251133 614251153
    0x601120c0510080103050c0f010219050a0503070309150504032003190b010f050f1f2001020904050c130e1005190501021c020604080708220315020405060306060c 71
    0x10340c00b40305081e000300003981601c010000c0c06802d0113582c015903c100e40d40c5226998000000b951144044104401e0030300d00c1410000b001000c00c07103501d40680c00401c0d03a4681201e418042c00708a0b080c4500c000a00344101c10442080c4504100c4054aa00103000300210304666551880308103d011129094411840c400441641c840607001e07295214010400440d810b1030311171142d000e25903005500952080f042518982c0c0d8200e028481d8001d5099050010490700c81c0490b113614003a80a00d000b01e007040c3c2d00c250080700640062041c01c4040c0c4003842140c98004180c04284180c1d08020804103200e80244480d0324190051034200c19622850050340b80c485000a1701307411076400d03448929078129802c01042d41c0500100e8401c444039041e10208240340900651200d200400080442c4000103103a1308000080c4182c80b0f0300c10b00c4400410500d0b05140002da91190b660100745d500161280e24144080b64074001c0fa801c1c0d8102a2060f41903844610500070349030002c411224a901817050301c4 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 614253633 1250 614252383 614252389
    0x610090e0a060b031008120909160c02060c030703091418070905060408010510090504080307050918091f06290c0a050d080c030c090607030309061121010501020601120c05 75
    0x51401140502d50010170285810390591924001444074a00c3c0301d010302c40c50219580c0d401505a00c10b1021808040c41300581504981050740580001d511410100b903450f00c030302000001d840118801e85a1400b016200e85094540014529559912020307540d00000b0038400c55071220382025980c00d000200c10b1f126800540150040d070400303021a0b541d041003215101418544000908040c01d040090341010b407601d500c503100c02403080c4280000004e41082da42c4844d004200d0701c4040c0344503042241040366209803911040c03074151007044106907044441d0901441060b044a03580e044103000d1100751103d12511601080c841c05480d6424000190450000c0c04481d0869202d24041c10361002d0481010301450005404085007240c1803042050400b41d10044591080702110711607250381062804402425820100500b100e0500341340912030b20703042c009010440d20100c0c0303200e40013014900c0148070b04030074460540180d1203000100300080d410740150820900582525103010303100c03404 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 614254883 1250 614253633 614253637
    0x905030d0f1e0e2b0803040b180d030c02070f1d0109090b0a0504060e011d0d05031b030402030f010c050405150702010207051e22050610090e0a060b 65
    0x3000128039040a03001c641039000040c0081140328400200141800700740003450030700c02d4210302d40280700c2d05040100c10301d51407200d140e00a4408028112a07000e034509001c554005803030860340303800c0950104014031541c018800650700707018010080c03140032004c01c5019004104600040d03008002c0e0208025002c4110480640030403c0c0c000b5400d40f21030000040024140d101c001c0c0e543c5002d40f89400202c540805036000b091050011032140c0f100c0c1040030040c0b0900c60b40c0c1c4e0b03c0d9846c113140d01d2000c0a02d092100c5019040f401034506170085030900b07452034481211030b0800c400700740d08200e48108124020703642003400030b82254011006082c0386801c4030301c42c40c94000458008502001185011145601c2c07045800000c5401c010855002030340d980ba01e8042d140c4510030000b14500b030610841d00c07419200700010320001401f208840d006072200030251050007150308000010b40e6a00746081d9051442d4100c1d41c0d02c0c9646460030001000900025110301480354036100c00081d00001040 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 614256133 1250 614254883 614254903
    0x90314030406180f0308033d05010c0c0306050721140604020703020c04050a0b0d060506270a0203040809090c0d0501150c1106191e1b02040c090503 65
    0x20040d40d0322420140c0250408900d000c8960a142d02c0c54024030000f101d40e2440c008581e03200521540ba610b500001090074242c2c4905400705080d0a8075510001d0310680c0c400c0d222415010410391195200d8004560b0103100d200c01524880303809100304001906035009907480079852400541c00074000b500c5505601d0401e140308400e944030000c0d50009010b403503000d034015400f1242140780490b01d581c040d440340500000944502c1c0c0c2da8000880302006034101d0280342400a0260319480035070b25048006200c2070320038500851015240c860f00c00540e920300d212001d01000d10742c4450ba40c1d41c803040c1c080c0d070000300201d8070344200b400048096222545124080c00c883c01e00c0300e07220915103213041e04454050340201a90803017a20841072054104046001054100c0301000c501d0040d034002c40d805104e4200b22400d03810000c0184c6a00680c04044d4180b030035045c0301c02d09162000614211064442c032083c0c08141c04802c4809801460564000340005200c0d0400c4042140d407400002e0600c80000 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 614257383 1250 614256133 614256173
    0x30c140901111501170c1c0b1306060b1b21030a0204050306040f020f0906011d0105040b030a2c120c0c1f0f0801030f021014070c050a090513120903 65
    0x80d601e8426840701b4015042031b00c000341c5465007009040580c034070f0b07060200d0101a0160320003001040c00100280c00440c20140c01500a000840d034a00060725194001a290508082c2405290041140201c0c4a1414401d401c00c550444071040741e81251591001d0000850260f0030000050103844c140904ca105600030303a004c0d64000d94030300600c0b182d104240c0100c0d10460285cbc00b0001d25a80280712002904200d003500e22400c070811006039242d20035608540c0f80303410003008010300019160480116031901c4420080f000000c1d084583c0c044185000703000041e041b12019400c0c0310030480c064584e400d02d80086034210004400814107086407210314110b130040b1004050300268101c0101062881c04c3e2130710840562568640403400c04500d20000e2141c00714202094076240704040000400c2c0c0701002d65562450a4500b001c101180c82c452640507180d1a0320000e519002d5200f440d204030f4080303028080812041d698041103400c5009198180001042c3c04404154441d0042c02110158 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 614258633 1250 614257383 614257409
    0xc060f1b0a0b01032901060f110604050c120d08010b0d060b13030201090b0a02030403020402090a0f151701261903030f0b091e0901061503020a030c140901111501 71
    0x541031030010243d03860b251110b4440f1256603140103098040b04181147c021346020011498110411038541e1200b1880f64442d10a40051009002001c5905401c048080711040300b11180808515100e00c080c05145000c180306d1001082654030340f00041504110588000600c95110f80710301503950014101c4442a0039080d50031310441d41c0008a0314060213102d10b08908180c3d0703102009690f840703a400001c1c080ca80104907079410b42c40314800704024000a144042e491502c4032020700310b482103c0f00f107100183c0103088507140c104071101814140c41c0e04610b0040d031030942c1c01209d041c42c07032480140ca180d480340701094042c24902d0a1510703041840b03503034042032a01d1003200700c0c401d81e09000c040600c181e40c46000e01282281d440031501c201c1011600c1745417a5641c002c1ca4500404065000e05102d1244950322600b09a041d8000c2c0100310f2182c800704065080100c003290055003200c005a1103000412842200b0740c0111800107007200301d01d0442e4280c2c145180500d200c0d0f00c0c20385c8030261034840 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 614259883 1250 614258633 614258639
    0x311070e041406010902130b160204020403080d0506091e042a0303020c0303030601080403140405030303040b040212340503010207121704030903060b0402071406090f0c060f1b0a0b01 80
    0x82444520b0040502100039800c226404250070000c500ca803081c0c03602003100103254279a0544440305c0540c1150000c2045490b140d581c28418440e91191601076401403904000401d6860a036010320300030810810340169500e82c0641c1c3c8030f40900f0242c000d8850504440c1c4078a031195026140f00c4020420f000302c00702c018a54900646070196a01e80c0358440c1d04140104a180d981c03210100d43d0040d054503184110180003012409035221b04d410854050100104000c184154041c1c07550046109036840c51040e400c000000ea01c818280c0c0c14950f80307003021500c90308850306c22104003804d2818101000c141d942d4a4000900b20b0f882480100c89454030070f10241c458a07049040d1407240c9814009507102440e01c5e07a0018180f500c1d07804000d007850781d030b4280e11409444a6066800080d44603050041c00111298071a544038011540000c03144201141c0000704600456805070359180540480d0401514080040b035580001400c180045c4041c08031b035035141360130042005818011107488001c1c1d41 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 614261133 1250 614259883 614259923
    0xf1e050f0706030e0303061c06050108031c09110f010504090513060c08010e01050d030908190b0c2704090c27050114010c052e1b0504030311070e04 65
    0x405a00c1502030602e4044e03462403400000c012a0f902c0b420403926440c6403600c619507032440f407220490241c1180e182c18000b065903000000240000d55211065000c03814498106100340d5080c0c503c0240749081031a403121882c1806e021502018005040c02400d180e22401e110013202c1d0100c5811242e540804038420a010b00d078425200c0d0090145488446036050000e1030313620010610401d030003040c02180303580c2450320603010f101c0a8001c2400b80e40c0c3c03541013000f01c0651a13040980070703100c09880e040452286400081111902e00314040349c219a806060080300b540c181e038603a215001038580498400181e142d003000e0000e089030010441c040480d2140010303040b11150103411081e0b18000040c801d425080c036039010780b1103003480d04600444551402c5420040b403042d40c810100d40c4003621620141000901440e03403401f00c1d00c100010814000130103460340c0e04051f61008110100801c0c4082440741014406040e043c10403101c4166603941a0168417100f202d0581e01c0d28074a00840d20201 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 614262383 1250 614261133 614261143
    0x280e0409110d1a090601050a0e0402040917030411030105090d1103041203110f010603110d111c0201030b060a05030c030c0c120306120703120f091d040b01210f1e050f 73
    0x4c480c000c010800d0b9814040461390034102801120405d01c0709500040456640340c000802d4242d024881f1142400c3d1150304030701d190400c1e2011102e8054440304c100c82402c0501c00c041c40364500000500780d0000e00c071000d4420414000c5c50700014001004082200810b040c240a41e00d880395480310030001444481e00e0621414884443c13084e41414020000314901c00307031985d00400d0442d0058880a142c0c90302d60110071420018540003210b1075454662500f0100140a15038000e88003882000440010020980300750002400421001e0000c6038160260344007650f405441031207500e10304103441c4440c614041e0420152030914100000308500c0d81007040800e804210490010504d81e4110341e143d10300d00d000712151034100600e0a000112992186210350b00400a10300070450a000f104410a800354003207800b9900c10341c0d03650000503140901e040c100c1c0300030510070b4a4600c0003002d07511084c444030070000c1030f03624440400c01c0c014004417490100040301d114100801022144808072070a00c = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 614263633 1250 614262383 614262391
    0x130623040e0f070309051b030f0106053a24020a1d04141602010501050306251403150112090203100c23280e0409110d1a 53
    0x2200060000304101c05046081e241c0200d203280106100e075488140442c000c0120280140c414801c036410a032090034900e030065483e004c240c041c0c03400b40c00c00d403001c20700f6500f2030310030715402c0802820314030b0110489031858101c540088003840b107290303002c500101103e0b2005200b954030480c2010300b0300035003220004114440112401c03d604046100202030244581b001040248030740100c02e4089940e640e0340080100102020304180e00c1c20034840c01860104441c8106015618101c00400c8a140000d01c00c1d11582040d503100022074070748080130001c184c1c00c003051814044512660075029020201451003041d0061480d00d981240200042104d85142c101b071486034900719055025071004240240d4500b05c1040c08244442114011a11040d0034814a4100e1050710074010300307003055074010f0010810710385070802c542c8035a4044d11020344040d00040042041400c20759814141500002807941c0210762445c00c40c29000085094090f02800444180c60544003000f0240b40b1001c000b504 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 614264883 1250 614263633 614263697
    0x110d020f15011d0603030408010e0c04051003120c0611030103050a03090b0307090b03040c090e0a1b0e0106031a03191a060f12030d0612290c0a02031306 67
    0x1c1545409624100c208840c1c0801c0b5150f02c0c3c0c1c80024160351010003c69009281d484000c00030005c0c0808400c3e1070750704981d0440e00c581e003041d01080144408c1003150007525004404515200b500640031349042c4480e080c01c0316002e40b529a81803110842902542c02075000c3e002030310010344513160040c03030902c03142c12070740702942e0a0003484540c0368011031500a8070b506512440c0e90b038a132400d0000d00e4081581c01850707180e080400c0103206000110300d502c8214800c030704480c0e42c200514850310380300f0380d14050607002c03498142c01084000d1094000c80f0401c001002d580010002d580301103420864220080201d550710f989004040140510b203407607941488401060040c00d003c80058600e0f00030320f103098421411868000007200d800e0040392100d01054034104641e9680c5c05442c030b4078100c001d005940c0d130302011000300384460884240f40281148002c0c0006181da0f1846207125940240b8442c0301188401d001031041c030090019040d001d001c1c9a2205255204415000d030f402520120305108 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 614266133 1250 614264883 614264923
    0xb04060225050f030109060203041b0e01030308040b040f020a030c06171003020405090316050d17060a0320060c01050f13030e010e011b0b0f0a060806060d03110d020f 73
    0x80e0389036554003007054030801c454100b150480000068050300006201401a40c8004140020007201d1040425840c00c104d034251031480d96003039204c511031000d100140c0814201c90005001407400c2c031559501500c04d910030f014246041e00411401d00c00c40c1c20807206d4500000051059a4000003c805981444071080c1c0c81c0341392984444910104610000380201c0e210030120720512010300c107895036552580b090070b170445d54038100103070f80d00105101032010500603288070880c210340f180030714802d0360050a403d40340303407442e40e8009104d800f001625605400d0380f01c3d130500c0d42d610310000f45040042100007203903505140c440d085a220001e482c0c0b04032007408451410000b600101076030152071307007400c02180d03458070a001030300d4204180b18920f5600c00300f9580481001003482d0300c030780284800d0078400e01c10390358040d504040b20311a00444000340e1140300000c1d40c910b082c0c915281e06512034500500d00054804c1294a000350700d4040744096000040100d00c900e0040003000e0042900301c5400c8 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 614267383 1250 614266133 614266183
    0xf0703050907051f1e030245010915030603110f0312160602071401050a050903070f0501090203060f01060e010311040608040f0b01060c06050f070f050715060b040602 73
    0x204802c00368218444c41c07104044001d840c1c640260710040f100c90440700d603a004030300700b028020000d50004207000c040c41d000c5050300381184420849841c0e100b10707070015843d150302c0c1c0c101c0d2001403403400c40e10981000441d45001c1a100c1700395005041f8100b0355100070804500314a010203480014114031030141c1071403079140381c06550014a8102e211003100c82282e035040c801d072500f00c1c3c041405e4000b5001e44d0001499400f040f141c125241e0401e240b40d0001c2240e80c44011190003520020b8406003400c0e4400d0140c1d00c0811050014840814815000050b259000e0350100342407102c02c43d2080b030402c00c040d004002c0203821034421040c5d00703802d1a081040b00c0251008201e00d0042d80105010030429200007170400c11600310029145412806034640c3d5a074802c0014079150384800103d90050030140802d1035401510343c0d0074082c882c00c0c5c8424400345100403044070103030000f0303000fa034007100b4442e4000d40045c014801e00713015190700c072280395649050a0010f468020168140f41c00803c41c00092 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 614268633 1250 614267383 614267389
    0x911040e0d0507110303071505070e030c1504050a080309030d021203040f0320030307030f090203070905061306030f020f010e010221070503120105030c0a03030e04090c0902030f070305090705 84
    0x100c00400c1d03034103101d512652542001010001301105a80d01407000140d00030610043e144112607006114000384120b685108044505048080c101d40c0c00da40141102100e510b004600c020700c41030100140d5080c1031340c490000b55610400c2d4460850343e000080e00c8605401c0901613a208600c1500041c4008081e625243c001407000400207042602030400791000c2500c80e660200745d20b14519500104c01e00e400795516120791003034400c0340100c0d141c50029240004103010300d000854004025052040c078200902c405804000e2102e039000c007264041805851040c400d40c0b000d5401025031140b114a00e00c14062240d4011030600d06000c440030020300700303aa00090612132140f009904d40140c400032211200a409800700c0104a800701041c2411010140302c0294105c510071011a00044100300030b200c17103002d0a000c0600010b880440811050805070400a071440c032801102d1115507503001c1420498200741d481e5008110980c0c1442169076041c083d00b500480c0c52006010658a80000 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 614269883 1250 614268633 614268643
    0x610030c1a07060c26010501030605010c050a0b0a090c0308090103050c03060f010e01180924061209020d0609060506090f091b0604050d240b151303060f0911040e 71
    0x801084140c072110304c2002c041c030074040100c049a0072811a0340602254009035070901c02406000c0c00207140550000d034035071080070901034180d0883c01030b002501d900d4403000c50f135200c01440300040ca40c8800c03000002881e170012120007940038a00340c40d100c00070302c4001810f441c0c01900108110b4001c0c000d004059031240165140e1640900b014081c840c08040140d83c000c1d5004103218410324260030000d901040c2d50420300034034420210400e60341c80542080b81420380c8030700600c00040c142c083c401005d10201d500590705280024860701180c0859980c084c1510241c107c101c9038151940280141402d000d0140d54101d4800301b0148a28680703c0c2d0551303610b1020b64220784000810400c1e00c5465114070089a003d84806080c0705c01482442c10030741185046821b064002803642c10220069825521031720120210007448526602811100c0d614590085414100c880301003000020018540d403050380c45044607510007050ba00c040e414181042034281721000d0141e0709000c00758654a8000c10 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 614271133 1250 614269883 614269897
    0x60e0d030e130b040f0903090504020703230f040f090e0d0203030615120901020a120e0606130f1a010f0504120605180d2f0c0103050c09030610030c1a 66
    0x600242c0c110400c0b0640c9014100c80461560800d2600740340301e1000300107400c5005a1802a1030f06141e951307948080c441203208240b80600090a65010b50022210b42500c1c02d031180c103148800d42c24000c80b0500c405096009a2214940e040d03020000c100104490050301741d40751802016100c00d034801c001c041d40383e100051900d80306450105e41c03c1e00480e059801c0d1042c407040ca20342040c192500c1c840090003580302c915008081005543c0c0d5030080d5081380221039110b0141c0c0003608482d240c400502c0300340c50b1284404032509843c0c1800344040425480349d9491302040100c034500210a038000035045202102c2c0400812104000034402912141405c40005512080c00034041d42d0750340511102e0103503410410f04502940000da9041c5501001c00a10a49003000d45c1921090001075190b90a001c0100020103402204140714258001d50003a94807841080302d6607d04070200001a04003c0b048441040c4500c00032130034810700107000720050240c0800da540300c0c0701a940c0082107040f030059003 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 614272383 1250 614271133 614271139
    0x1005030601030216060603030e120304031e02030d081b0c070506070819080f16021b42090a090c090504020a03020715051b071b030b01060e0d030e 64
    0x40400c256074402d0381180c2005200040c034500c580f0061030084042d1400307100c19000182c0c0401c0005c507503d0711002e003400c014101c0004501e886c1c50740c3d40b80007088043d81c503401207001d0008601405030300c0900c10500081a0742d0703030380700e401d1501030f40c050044520b050141c80d0011041c00f05000c542400074114050b560211440f070384400491500102038400d10107140d40703030700c0c03003420740180d0b5504006d07401d01070200c0740d90310003041d640d0f005c0341c4429401d104409001684084402061408002d0700140900c002805441c400c00c0d0303010151007903000340107502035040d81030f00c068007150491407680800c1d8150500650310f42940312000890b41c1c11203000d2880c52523900c204490005000d201901c0040034081c0055407100c01c004000780c02504443c0040d2220f05400403c0f0101103807074031443c0d01c94a268030500c2c580041c5455901c1c5190800081261110101822080e05807403280c01e0100641c484c0c4011030066040480003400e502090074101d000343c1c0142860b00000c0c4d0040e81c40c00c400a01a = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 614273633 1250 614272383 614272387
    0x30405091f06121a180718180e0f060403050c0a0c0902090f030106030c1a09030114061305130602031e040303060519051809071701021b0307021005 65
    0x807101d440c41a080c840e68a01540059100090440d0092450301c1d202ca96040100246803401c019940680b00130007501d9482104d0000030712110001242058200c02585002146c1c1038010b20459101c801d0f0344c00148590640002c1000350081900410241d20508406003d58501010069582c4c800c0a040201400b10101d480c1c0c041e45020031031001515086589100c499540d103010000035400041240c1c05000b00440c00806814140506000c50381d0002120309501d240030303111011550300500c40d40190b6030812514069a40034010300071140700c4000c3c01d03103031420001c00b0001c03003810400b22034401906100401c640221f5100303842c01c00780c0c2c12040161752940c0344640060300b204442c011001c80c002c1c1409110034164140e2205c0b042d01d41c15a145c440e040c1000342c0d04aa9045188038156101c480f40802c074652200051443d0303040300d0042c0031107074801e85846400c02d12507540070144200360740c00b180c8507411a5899a03090170201c0c228000d1460701c4081d1300454054106505448140900 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 614274883 1250 614273633 614273641
    0x3030603012d110c1c0f020312180106030203030c1617061303050d1d01060b131701141515071203050907050607031701060e1003050702010b0a15080106080903040509 73
    0xb50310b08403070114134001e043d9480c403032803082d07042048080d14426500150303190f00d04152560001040300c0b180004004080d15a59911020910812100d0390428540d500d50b100000181c80410141c20b920300b50b000505a030341c04000d00716403d5000c9074801032103100c1d140100c01120001140d0660419503011101285500e00c0c102540d85124010816400c3c910303101248038410307144003440c1641d06050b0b00038810581c1d030b4186080580900003000420350300b030f15020044540e511400b1a03c545c2034000200700a00d0381d0300c03402c5810500b102c00906110050b03403c0602440c01d030485200150b15900c4190520101e61124003054040445600526a4540c049031107041c0400082d13008190092149507100340e20710b401403541c111003901000000c801c4c0000b00d586401411000d00306a0094286a110755003c001180a80b90140099065540e901c90110050b02d0b8803c0071800351400e00c502c445095000380d40284103280582c045002c1000100074000f0307485001c0115400c07524111003d00300ea4907 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 614276133 1250 614274883 614274911
    0x1020415090f121109090f010b040614010503060a080102031810061211191e0906030506070507080c06100e07080f0112150212180c01120f0b0a030503030603012d 71
    0x118650388a170744140075004000c1ca100c4006240107075035100701c009000507540c0713000380030503180c01740101c09100e030705001485017551081e03014580c8444000c1c0b18441c85640d8038101402c982c0305503155030b191440d4070f0300c408000c0b00420081d800600880c004101040c0780c280b01c0d40f201d040c0310100a002401d00d4100324500d076a0617050307107519a02d060783d6120290752103401700340408003a120684200707040b41e000100c90a09220300c00c116a00721001c0c002c2c50b6120f0004039050b6201e0301d021601c01c0c1084c40810000c84040014510501440081e0007100c1d0500c2c1c06a40c11060003080d42c01081845030402843c0d11040d25054111101103004e81c00c81030141c5030603408200450f000d0f070b84061000c10050b1080b0340c2e42000c2c42c000c0519654034120b401408401d00e849040b42107040d4007140000303090010b0060300ba800506036160820000810b040d07040d002a900710020b038001d444907400481406860700d0203103c3c1c4102c0031030441100d100031049803104030701c00c2c00d0500c0c80e44441d95241e01c203800b022 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 614277383 1250 614276133 614276153
    0x31b0d02190305060a0504140402010c0f0b0c0702090144011a0909031603050901140c010e16031509060b120607030b18040f020109090e01020415090f12 67
    0x30074448200c11105104110007801043c04460003489203031480000610b90825101c0c04024141744200c0004540d902d030010740d00c00ca940c030412220103448969090108240c407074064040c208501d00303565546882d004000e119081030b004011200552400001d05000d80d4904c1820789804c1c1c2046c03010f00e55222050604041d200320303400125400c210702500ca160080340d003891410341c101c2c0e09000680300e40300d445035613000d00080c0c1e0181c4044d0003d000007203801400506400c1c0d1051400c8001c0c284216400903094001050312540b9a44445429619881c00d00004115100b4004002801451600d0b0b611050f018020780b48000d035502c0f0000010b02405400180803c03001519a0000c03220035284035903140800c8444070000303490028003d029241240c00800c41b00ca517036001c415903440e40d0300c41d90403000040c5000c0381401180140082c0f014014015455504074203000184c5031441d0620507030760380010300c1140b4100441c6400034000c821003c896001a51500c41d140d40c3c81803103a151003221a = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 614278633 1250 614277383 614277397
    0x12080f1b0f0f0304151b080901091208070e010f2705040204080d0807020c0108280e03120c04060c03120b030a0606140109080706050c01020708071214031b0d02 70
    0x40200003181c078070b400c40b0440290f0080d17100c0e2140c41040404003042e0012100c55500031141e0005000c0d0392502c43c6c2c40784900c50741002d4244000610460259100341000d820350411102003040c000c204a02150003503484440003800303091003140c1d0000000002c0044048400003903c41100310341700300124200d51981c4010300009030045640756221035a0943d1039840300c0751040000c08100c00034007424070100c1d03c1c9610b480180c40350500e507224407056860f400c0008001031040c2c100401c011035040801e01441030344034a000061690f99440400e41c9500000007001c23120b00c04801c00c003c02200c0d500000303408100d07805181c202441704190b00303484c001e006000759241c0c0c1031103070722000014800c00d940f0042c101c44080300d2507214003105038010745455101e4440d5909541080f1001c02400740100300038518052540001840d08110b6920001c958002d0039042c1c030f0882c900080c2411f0150072a00090540110152140c1140b070860744070080102500181ca00701d840101c2c83c801c1348606501680d20f8 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 614279883 1250 614278633 614278657
    0x1a0409030e062a0a1403090102070b090d022107050d0b1f0e04060c0e01081603020a050f070503071a102705040308071b080f0304030c0206030a0912080f1b 68
    0x10100a8045541d942d04c8400303041e030703426102c5507000c1503821000080362202c40e01070300034240705483e292111034a90030004400d6005042d42010400580d24040c000041c0c51a0101c89428000c4d040c0b00240740c042e4603042580500081090b03000403a0203171160300c1c0d101c0c021103d01e8020502f8004030140319002c5920040c01c0c820120248020440650003c2c01d020101c0d554010844c1d05080044134140e100f80c40261802e00f40c0c515071206284242c0040c01c0c1d0346034908000785016884028a401c0740c0c001c91080c2d07282e4001007600c0003002244100c041c021180051800c01d642080c002c20384000d100c84c400d05c2c41c036030003840c0e86001c0340400d0025000f606510b64010070080c0742c032b070402800e007840c1100c4a1001031590707107941c4000b039841d0f0b4078004015001500c8a0a05041d40c060f58082d81c405001641840540c0c0c0c824001681e031000218171074413082201140300c251501d0b04004103480001101c0a101c08942007103400c80d07000b1403056120303c54405e00310b0a5951a410002c00e0300c2201180b0507 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 614281133 1250 614279883 614279947
    0xa090618051207020616031722142d1b0112020d060e0a050702150c1c0f020a02030409060501091203030c120606031d030a0e0909070503101a0409030e06 67
    0x901d07800450102c0c400d23034801e120340742d06d030b6482c0350100d8200c03018111074a02410703074082c0c0800314107110b850500c52007018003215150901034440280004010340c03a202c100c00905105407980b00c00b401200c400c005041040c1010980c038000180484590075040b010843e400328172408a02c5590300684010482e204000c0d015013441d03080d90000d440c0c00c50f4040f015105142c428050000d809045034800c0100112803406c5c9001c0d200740908a40800c1d04003002662102da00150f21581031000345000c503038540085980b01d240050303100a07281e00d40d2000741800711085007040014800440940840c0c5e25107800a007102042100b80d03480c071401c20040c0340c0140f030180040703045034150340040c1c40f1111400c24086420038808103140d42e0321540403000002180080e400b066420f0102410b82c1080445058a000c9621040440d25094016461610b1103864800c55180c00c0070010091032209401d503001e2200214a031005412041000d0f1071601440300062841c083d01e0000c101c2581c40001ea40f9448 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 614282383 1250 614281133 614281177
    0x3090f11030f06010501140904240314010e03091c061a0a050402070203030904052a090906102c1518060403050c010f05070602030a0906180512070206 66
    0x441458504600350301030b00c168801c40d0124240020307510b040301e10503921860341601002e80a409074001031180c582241c3c42e80c802082e0807040c886034050025a02103060145d914504040004803804143d210a503450180d414403190004000c852201d4419900071001c1007039012070000c1c160b0f8440000d4070291401d00e94818507408040510780c071b9102140d031001c08940752020030081b40300b0004003d60661041101c201e00e800d00d80c2080303038000c054503492416062101c04001c614001c030740c90650000c42c00103201c0200c5c580004859040300e03054038805018001d881016190800d4400c0c0f10050001c1d40d24042c020504056400706100005086070000403040c4080c24501e400c0500406d010203803020805425081c90b205840850750000e004002e10071071440155076010396480e0081c104041000250081441e500085000e015004000030f410032a6042c4035040b0351001081804001405e45c4c00c0020503400140c443e800d01807450324556403d0948001102e901c180301c0c1002c2c0c03400483c0006 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 614283633 1250 614282383 614282393
    0x410d03020c01020606010f0c020d050a150203010608070507030807080c13090501080705150f0a2c010906110c04052a070b0a0603020d060f09020a14130b06041503090f 73
    0x699000f03808445141c0c454a006650200d01048402c0c0020b80d81002c210240c45c01d030300960740460054054510f0548a600e6030780c40b40354140030040301107400100403c4034030740c800203080e03006410389441401c00d2107650707006081c400007824240c00c00140c400841c2184540d81c01702c0d0322079580da4500b2100e0540d980e000f240070308024803502c02030340509480001c0a0501491094440c400a44000d00c0c0c5040203240003103d820540308075081021050780310b070300800c00c43c801b060510601c02050f0541c1498000040543c84107400000402485100f6441003041c0094070f80d0030a0300444010030f42d41d40b120150848010281d0440030110400324075405c0b21500c80d0010306620740a000005000d5607014580c00640d410b520000390008001c580c254042103a83d8040803402260020116851050b50002424100039402291150240b03c085000903c0d042d4a0b06901090403a81404401c0d028400180701d805180316003101e464003041074511092090f03001505c030550180340c2c0b8207110001c1c280 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 614284883 1250 614283633 614283643
    0x6030317060a05092706131b050604030606080c03010e03190e030a1a0108030c0303040303020706020d050a02040602010f0501080a0f020a08030f091011060712020d1410410d0302 78
    0x5c218105416000c090100b013011500c0c41c440c0000b44010500498241d80741c1c220b0a6900101400343d989440010a081e40c886004100035401000046090343c10204000e0402d18a00c00a0b4400d80c58038a10301203422000c82942c49500020f840d00343c190b0280e64054031811991500b556140c01001c41c040200039440f000070b0100b40c0180507403541aa20340750520f0350380c804c42d807005200d54400c0c00040d0000b4070a40041079120712a0303102500b440e00d2802c0d504150380b8283e400025058002c1406c1c89403d50921601c0d11141c62644180544d502d0885131036140d5001c51400351441d10303128506400d54599000e21401000000d045030741d9100904500d40f0981c1142007068070612034815035280091103111030510450b9107801900c25611000000d0301daa100e155215100c4a03001d000c11589031040303100340345204142c5229008245007083e07203030440032001d402003500000d141181d440300f280040000c409981030218442008000d030380345002c04010071404140d0050020014004140e40460 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 614286133 1250 614284883 614284921
    0x15090703060e091e0d08040b1909111306050d020d02011b031817031c0e0d050d0605120d0c0f061a1003050c070303090f0c0b0711030106030317060a0509 67
    0x314450b5604003007607880d4441441d0b00c205c0380000d82001c0414003103440c20009a4000c6002404040c0510000c0c00560a65003101001d46095240841c018000d041c01410202000340e081c0080140b00e04020002c0d040c0404400040d00803100c100b9044110f9010ba0101d190b58a000c0281c5004a06189030081400405e400c0d0070075854071110b40010141400d010701c41051209401a50800c400c81c0c034501c3d058a2007118a014031a01c078580d00040000522400c140324901c2ea07180d6540f92001484141038511580c003090240e82a085030a0381c16201054038888400305180903503850004c2c0c281004180301c602d6014040c00c1c540911601d0502003844800d101400a80c1c600312141801e140c00d0341100c0007200c215113030807410084030000902c030368404400030780716031068100021141c5a50b10600c0f85a0445a08000c000a10005000a010341c0c00c1903120218028004070b8203540e40185000c00e00d0907951401130402c4041043e030342d2001c40003005014045e12a95851a1080e0912010000c542d = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 614287383 1250 614286133 614286163
    0x80a031a01120c020c0a08010c020f0d0212280c0302010c02160b0913060e041b0302010504030305030c070f080310081501060827010b040b0915090703060e09 69
    0x22000c2840040944900c4420050507107514141d03401045402c0050150588807001314080c082c04001c05581e4405064003619015000040501d410b500191601072841c55a0b41141e00841d812040164000307404204214562101c40d10f41c4802da8028652500c80700d071824584240003e0004111351014404120074001c1d4028440c0e42c1c0301c49000d9884000c03951000e040f0f03009115091002e01d90341030080c4003140d00a04051075000001014004035a00d07500700080300c1d41c0e110b003800306112903200c0040d160081d824505045918544c0041c059118900c4004d0920070044001003014800354140c0c0c20564000d103402248000f03601c1c00703d42c550301c1100c0313031949403030700c6080401c401c100040c0010f2aa0044030301c0060990078540295041000142031a4030090903d003406108480c005207030716420f25201c0082107141100c030400040d40ca16030005406112a0010003900c0f00d5400c1800011540039114054140c07100070003180079003039542040244500f0801803128904002442c5000b1440d21 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 614288633 1250 614287383 614287391
    0x403060c0c1a0712020306090106080601021e1b06030903040905040f02060c0a14160902070228060906030209100f032004170c030307060e1e1005010602060106230f07080a03 76
    0x1341210204a0000b507441c20707045401c840050201e140212072060b00454140112203440e8a02d68110654842c120388038041508502032030680c4941102c0c1300c1d80025412500a030440c40e207102d015649000d10300c607202e0340545440c04a4240204400070501c00d50700600043c1c0c4e104455580903039650160347c070844164001c106000d00603603020036800c0700307615041030850b0110b140104441c0030b500b0502c0166404403440d803000c203c1c2210300b250020380160000c0c0e60f0105500d0524043e2884065a200c08141801000380d01850340d83e40141861710030030743c18044804031a61504070700a00e101d4000f000c7c41c1454030009a4805002e5010300129240080032191600100015a4451241089080d0980d005100541c00030303640350400c0c00e5034001c03503003114104104403803060035805c07400071854100c2d04000b03000101102c144c0542809850300340001c00481d45060001004c3e0004044203054060742d0000004880c00a10b0440707101d03111100c0c01340e80380c40c2c103400e01c40707850360060725907801080c54 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 614289883 1250 614288633 614288657
    0xa0309150e150c0412032006010e0f07020c10050a090305031b010b15030103020d1103060a02030601020c0915040c2003190f0804150e0a060605240403060c0c1a07 71
    0x40380040b00d044e21407080c450a000c20440d582a50b4452568441d00f0b2002c030220100c80707d404082004a008040c0010540b443c1c0c1070443d5460364044000d0702c43e4003190804280311174140c0701d402261410315400c1c5407007a43d0324646130080f81c0f0400700e80c2000f00a070100003441c0b1010240c0e4003546008044d13110007089648800c40801c03030b208100c8101040101410303c010409403401d82c803c180d03028000d010892482200304000381c28194200c4000c034a10f940402842405e503810000c10700c2d04002601c1400ea00c1c142101030717482d41d081003080c5510a984610903207090502c940341081c075088076240e4100f08403905d1500300f0345035000403052401403401d20902c0c0c00c030700d071003840307515880c102c640c940201940355031b1101d0000800200a481e0016242c041c0d41c0350310602044043c402501400e000034205080008203d00b2850f141d4540c245110341c5900c01210003505811202280d0f807003500014818407544050707420781102400540710155a002d160010240c04d064240b059000e96100b46031569 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 614291133 1250 614289883 614289901
    0x3031611192c15120f06010603050a05040b01050405191503020117010e060d0809210111071e060618050f0703020a1d04060b0705030405100309080a0309150e15 70
    0x261100e01103000012500c0403e142104100c09040003d501034908020894400c900300c1c40c04042d0900d2004650200c401040501d91610540d42c100100c40d005000a04180e114880c4005c4180107461150f80d03140c0c04120700c58009482038015512203d810702c1b001003000b220260746d1369039100c01d0340444e61400e000e0343c0b41c185440001381a541920048462511810280151005125070840f00814204480c1c441e558070009001a203a0209042800c9c2d6180181681d003543e44100e14010031040510010b000140b8109400350022040680b013600003c07141007100280c0303c141c1c0400202010142506d031079074007541006100c1c017846800003d80d902d42000840c101e100d200148000a1210f6500e4400c29510074844842820000e2010500030384600309100d140d0300c20701e0102d034036a0001804210b9400d212900d1501aa0141004c01c100511a1110701c624460041d58200b050b80c3d8012507020082c0000607140a00c003104400c0001064540c039583e80d40e00b480c0208818054820b0000d80d00f40 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 614292383 1250 614291133 614291189
    0x90b09040309060c0221010e010b010216091503140622020904060914030406090f0803040509010e040507080312060909210a020709230c090303161119 66
    0x60790595680d01c0c03041c90301108681d4a109800201c0c0e0280d804010700c080116501d1082c10000b010707030000a00004d03c0b210716400c6880d007907500f905540001e80341c2444056413010b0a812164904000b160190202c50008600f0100d6080100700340500841780c42000b0740050002c0c8200703000d044040c2c0c8613102c04106814a890a480294000c086400280004040e40c11091582d445406400901d42511002c14210b8000d6000b80000503404076082149036400c9502400818050001e586020300300000b0900303540050150141c04c00c888404035040020420501004041310415a43c560840341c80c1416145000d07107200b031080e0380308800b14880d1180440c01c1c2004a0f07444100c031b4201c408603d0f03075a043d0740110070b8080a50040c0500016285001c0c05003860b108400f43d0031116a100041d40006000c5020b01003c0f56005c0500c202c82907518000b00300c800d181c114034503001010302030b440c03c0302000d01e1034500140c100000c1101c5900745d20940e02080305403656051403200060301d45140342241 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 614293633 1250 614292383 614292391
    0x10f090603020906061b0d05031e0910180512040e070809150a1e02031e0907050d11040f051005010c0206091507080307020601060e060403020d0b0718030c090b09 71
    0x200030f0301c0700800c2252030810014041c1c1d20b00000510048202d12942c141031841300240080070a00000c100068048035600604501810343d0030310400703041000c40c150703443e4800150741100543e01c84c2072400c003910215103884a41c1d0f001007150007000e0a5503025005030040d01c500c2c0c019000300400f290321103024021741d901c1080713078070010218440408914420000d002c0c00c03d84150b560382c0061202603802034555941500000270160340e03402d1140303080300381c1000064080c04a0b8a05400e001c3c1d102408140d0b1021a0001c5801500c07503580740c140a40014503040480b0b43c4280b4042e000700021100381c012501c21986082c01b50492543c030030040d550311420b140c0080d80008200003000da80c1c9030031036586215114504c505070601c0781c543d80e003004a510959a00c40503034000360041069961080301039400d50810f940090900b8599404121004031031000208111640d1000504807441000ba40110001600000381400d550742004480b2500714000da0303048030308200c20b1208906201c1c0c009401 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 614294883 1250 614293633 614293639
    0x160602011107020d111903060207021c0c0306050a1503050f0609030f04210f08070501230114030c0a06090501080a0e06070c1505011d130803151f0206010f09060302 72
    0x20304203841c0d441910f01d010409845600101d80025103102c00c0e200800304007e144036220040e950307a26070041003900e602d1490502800e100c0d200b0810300060705c40c400102240d6000c0e2020959460f05107201c4054030a1010003076002d11342c85030000a02c00002040c01007140c6100030b17607041d9250340107019101c2c8103111040d0000d0404220420000744164a02000f54600e45001641c1c0d14541c0d8074008072644114082c0c8000340003290002c01d02c84207108111035000c054025007500b004090a03070b030071440e05104e851405881c0f07018402082d00c081c458030000320340050042480703c0d296130020301031035100d00840c2d001469080001d80c90160728442d29140d286c12100400d000d82da5008100c03054017012001326680c40698a0383d0f032a101050040502030700300d82650104000691118684181005165000c0242007440c01c1011528100072641c004421151800c0a405c030f550120b9401d280a1107148211000e0349400d001196020070418140c0d5401d0b080700e020281e8854602094542ca801b01030742c = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 614296133 1250 614294883 614294899
    0x3062a0e1c031b080403150c021e0f0d050a0f03020408030d0902010c080c030d0c08062b08040902090306010614030f070e130c030e010c02060c090102010e16060201110702 75
    0x340d249040030214040510a20b0008920380f402c0702004000002075604950b91640420700f03104100c070f41203000181001c000010070071107001c000000d42d1000512856410081303554442c0c01610010300403403c905043c00101d070f500300c09000b0300400c0c13036005007401c100113900b01e0107040c0182c0c8240200d808544600300114105245151400020000c09404a0500454501c0c441c0001c062001400540340b08102a50b102c202400e010f10a55166480d49000c0111400c02c008255131100348039002440052884030340394100034582c00c4116900f16005d000c2603400701c0d0019031081160001c083d0018150203070b5407980da803083d0513540b00e42c80040c040c114040030b02c001820082d8800605621a480389085a461075074000807500030007095211040054a40411210207a058025039030010300e640b008001d4030f044110000d413200b2000d003460074094000110001d4070f80c401d41000001441c2071050300d20714503c1010804c089080c51150b00059401c0503013086241d1910410780d9041c035000350001c4 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 614297383 1250 614296133 614296159
    0x304090509010e0f01021908041e170d06050a0518011403010914030c060705090a170f0102160b0906041104020904060b0307020a061503030905150403062a0e 69
    0x1201400005140607025940c510111001e2902049044200c1025800041e5503090a660325121425085c0c44c04082c00f80880074000003c200d03640d04206000c1c0c910041d0503040141c5010900c0c030190500b8018440c0300070900d640072030591f61200b02150011503c40012070b6680c001e1206105542000d00c8074120058010802d0407091010444910802400020580c084d5590ba003c0b001100070901e0b00b035800420700c02c0400e0381c1081001c1d013052036820514202009400020800780984c000c2d042d0001106c5a480b40d0860208600607000c0c60640c003c0d92996000d003150100c040d5090800e8840c00a00310104d1413600002c41d055000d40d07005844240c46a004400340400795120703d103025001030307407103100056100445000e540608559070140ca4080c565050503015140091242d044004a0304020000241c010b28983d0845d10166000c4a0080420801256070b004a45c8003425190030442400514407104428040c1103c143c009c0c002c21041c00d0070102c1d9400d00d16040c10740c01c85e988001c16 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 614298633 1250 614297383 614297399
    0x1701050c1911060a0606020c0102010b0f061812030c07060e01080601030b0d051b03070518060118090207030306030b070c050705280b18010206090d1206051f0305060d050304 76
    0x260740d009a0a0421491085101d00c1d02490004111040da55650382c03100144140d80c1d05012540e062a4240700a21005400702c00068040c0e010030342c1c0601c503440004202505940300540600701040080c01c080200701e80820803501d0380c0c003030300124049008004010a1841c0200e00f21a94088103a41e19242541c0f0840190020261100c410350311020410700c0030002402009064008509038035050780141b01c100c00c0c1454558a90085485424a0a024800c0201020400384d0040c400d280c0f942d07103403c140300101340d030080e00d8110003142400008d0f0342d801e06400d50098401c4900c504658465540c0710f170021110344022540082c005c0e04040000c0050b0702e41019003201010029182c0100d01c50031000c117458040d05548845069030001c22180540300a080080804140030f0000d00414a80030b909951910341901602c02488100c00070500c00804a9201c070b00540300141c20f03207046944400c4401c618003c100072400010b402d0900081c4175082084240c1103055206004604140c102402 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 614299883 1250 614298633 614298667
    0x80c060f0409110d051312110303150a240825030b12011d0d090b03010e0903040314030702040b0a051c050c03160e07031b0e0a0b131701050c 62
    0xd1070400110500004a13020140d208290107040c28016884801615203090b0f020302552903a490144244002032500100010003140c1c5d000c3da440070510320f400e41c0d00e00010f00419842c5c00407811210000d410080c1107100354007180040341291516204c580d00ca41003444084144804200b82c400d100c000a8101ca00942000b044500001d065904282d00c0d8806039003100e5071008118050807202c1d0490729410030900102611455a1420508a03400e01a4451042c481881410b200c403c2800c0020b600321001e000b03039009554400040c118000b4210788003552074003c02c100343c0c4580e00e010001000c603d001305007001218000f500d84140e074100820a040d03484040f01081c0c5076800365940840703180d17802380040b02001032810144042e19092210200419100034040c00a040c540754020f0071900324890080c50701c141926008020407a0303c40030560540b2140c1c000c503e05000400c90400800c1401641000c1d51040d203002c420503042185c2c240d09a50040c1c3d800c04010303c082002001141c10a12 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 614301133 1250 614299883 614299901
    0x11a0d06050901061a122412030c011409060a0b0109140103060e0f0f0709060828050702011d1c0c020d0c090209010f0f0e040c030b1504080c060f0409 66
    0x1000003a1a513031540d5000d104600b00c1c4200521100005512905c81b01c81c030043c07074000500300815680740b00c1642004144021741d6400c680324949000340b00d5039444013001100c5000c00b003a402841440c4010345000200c00095540403002d00803100080c140034140d2080108803001650788108151500042c120103100e10003c1c02d04041e154000880c001030800d200500851a00004048a191912074400101c50141541007049446081000710950120941782c116641902440741511104500c10310f0808001c201029a03080c0700410905c1ca4066001402040019a84040c00300503c50900c2e00d5030b52420409039600c0e801d0340c0c0e040d1003600c01c8025200c91480034000034141a0182c444e182c0316415544640351131a00003540c220196030200c1b1500c03880041d400c1c02d02c280403001302c02905a225440b10180100c0c0c0e40e4189074841480794010305540400a007800c0001d00d41c4a4031483c4a03400b46c0942d02c0e451044a10000281c02d108040b00c2130904001115410a81400520406801410 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 614302383 1250 614301133 614301151
    0x30e0309090f060105131508012102061c050f04050f0f070b0c0102090901090606031512061a0411030109110301050109060c05032505070f1406340302011a0d0605 71
    0x20006c816401001e858440c09400000f000012045070200c0050910308140c0106828040c00d007200c520084010301d003181e9250b4104d511076152842c2c032201980b040c800d180c0d500000740c1803a052219040c1f04c0d04e1401d0046000d201552811301c0160072950f5545c0704541d259505901c19081005440301d9000030b04520725600c40050700d032000610000f2030a050a8000000c00d80c1c1d51601001040d8041c456888071140c2c40c204040e07528a070014502912801640c081c11301902d40525801c40c041034070050002280040080103003070311540b01e0410540090281e80c214a1809003a02e07207480e12441070321704030341e0165201c01141e070400d00c08903040144040308130340d144410300101c4012200c407141d130340085450b560443c00c0ca0609040491405030325034403031141d007590b10000b07001022800c0000c02c50742030282c500703580c1c4028090002591740d41d90182d01086e110707011400305881407032000c010102c50113a8020311450b50034200402219207484811680204810350b40800164030703400083c0d11031000 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 614303633 1250 614302383 614302387
    0x103020c101a040e0607030b0103061a0706060302090c0903011a09180703080d0209041a100302090f03070905101710270503190804021507141c030e0309090f060105 72
    0x9000810706942034403445503031301d400a0040121003a410f2107456440882440c043c03001c103280c482c6120000000c51a070030303040e12001a0850610880d41c012000455000d0001320542c5841c0e02180c0301900410b00c0d01d40300e5421712454200b1320300036000c259452000100100341c5500c0f030000c0f248100e81c40c000710704031a008048002003c608058007422044014402c05079440310040200300494515940c14100c50300d20001e4408103460f0f0160f0100135111a08005035680105c20010b880b8840b040e8042e6850312500002103100c42c49070b000320303001d4001e06814407e181e44464864050380c0070008040450360090084032001c1c01c0c0707904910642c2c400c07180c1900c01802d030b801c0800c0d00c24107400c809441c964400034a1150012421544400440340c1e458062002e041c03a50000d81362115000310341442800124140e4103000c0404e050300c03d0f00e80c450045942c3c3c6490014180391800620140401282c90480e0110101c213003c0201e034030045000f0140c0d40a55107000c1001c140050141a250401c40c003 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 614304883 1250 614303633 614303681
    0x100810060504030506070806011b051507031b050c0109060501090603020910060507020112062607080718090606050a0e0a0f0c050d090507080a0605160516080c1612050c0103020c10 79
    0x1410840502b50341c080d40140400341c60541c159000e0380c801810160030940b506030101c50b03001d04290300c0100c0750810b1421a507214061844903001d0b050030388010f00054600400014012010750103802100c2c401e8507860020350762003d40d2182c2509900c111f03c08920208200c200561107020466514070074100005945600c60204103010942020700b0108000c20798080082040c0800c511b8008050320001090300c1030038180c000c03001903101c2c240d4051641c0c40b174264000f00000c5403c00400380c05c014110340700061f80d401c5846c0c1d01100c2550312421441c0390641140c001c8129000e2038004642c00e481d01850241c600010700c000b4990ba43d816516400742ca000420100005d0040c00b40c01406800c0c00700c3c0a041800b03003540c41c0e6404140640602c201084107612a155504010b0f13203550b00141e40e29210079490a100e4101102140c02c10108e82d0081c002140c1c01541e10760140d411800ba504035051040b001005400724802d030008041d6a903c0741940c8036090718582c03c1001d00b82c0040d10000b0300040 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 614306133 1250 614304883 614304917
    0xa0b161e0e0306060a1d060607120c060c0203070b01050906040905061303120608071518090e010e0705300f010902011b0f03030507030b10081006050403050607080601 73
    0x20582003000061804400c0080e01e02c1c041242541000d011612100603520b0450100b40c01c0c11a821140d031500031240c0080c104c1d58580b0300b44c1d001035422524003503103100311060041c84c080125a003166210b14000c182c01020b80f0000681d590f45030b0081d04155280d08201c100320000078000c000662103030f2140c011000046061081d54011440c0b440e041c80b4401c10b40c039002c1c00c1030b13444550030958503207070140812035142c1c009100c40c01c9440c012140301e5101041042100c459445180d201c16460080740700180202c0964003c211400d038490081010800700d00105480c2c020521a4130760100a01c82100c8540441c070340c490080c03080b88100c0c4000342020300d031980e0615001001d0b811081e59582c4905c8255600081c5003506c1030300c1e1421800542c83c50b9a943c0300442d2503107038041d04056035600054141e90107030388468200100184112540c600011008010401c119890080d000c241d00c00050341398003540c240c60a4135400809041c069581101c103c0b00381d14010081c604011100032800d036410 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 614307383 1250 614306133 614306177
    0x5070906050309010905100b1309020303041a040e01080604060f0506150a020313180c0f0203030c090a24031107030504090b180a0204030506070c110d030203041d09060601020a0b16 79
    0x21f040c9100414080107020401500072803501000309102d08020318000103a0303002c0111000c1d83c00c003131006040070041c000c0c041202d0150380c1001d501d04d4215000820401e40000712a40b10f5403203035005020704040c0d0713001902a02c100362038083c2c1040c0403055611241e20613102400302c000701441140c1c1021001201c4540840e42030740900c401168050300c520140a0a004901082425083c0340f80c2c01c1c454050000c0d640c1c130008007142e01104010401c0c00030740d82c60080d0704c0014011504902607a01404070440540005051002d0119142c1601c510948207070105540090b905900ea8600700752500741e030700000d0f2200700c80c01c0794068142801ca0401424000c511406040000c00c0140ca1b0360540c80c00c240350040180a441c21b00c581c0220442c00506010503242d260700d01030711003d03084101031405070701e103000741e820400c3c01e40c4281d901c50500b031080c00c0486200321030750022a07846450b0840103a884a5031707900060400e07040c0c000000d41d0752001d00b2803005102c0342441c200074601020302c010100c030 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 614308633 1250 614307383 614307403
    0x4210c0312020f1c0b01020105042d02040501150201050f0615220303091a1206040b0301060e07180e040201020a1202070f0b121803090d020f0406081f05070906050309010905 76
    0x134080140350003001c0340030f40b040c2d003000300b001c0c002004a070410b501d0b21982c0303044060001e64400f038251701c59000c5034031034612405143c0d07000d4030034800e55840e410f11034940d150461024005620304000142080c45036141da60141801070001071000c0000b060000382c0e64400c400003107400900518088090710340030206c0d070046000c4d59a060702c0604100d541460741021002032004000d0601840380000410403d00d900040219400164400e000c00401d01400301c5138021182034581100300601c0d039800000d5400c2c104010600c0c8072405485000b90a54580b081e200a13006074004170144000600031485e075940480c0f9401102c8400d0fa0f52000f080c0b485a06400000380c1d6540400c050080c1c9070044285ca4010720711400001c1c1ca40000b00041da920f01400a0141c8a40d144064406c192f495101d40c06405104c0134206000443e10f840b03241d5598050352010003c5000340517010b003003d0380140b01d01c0d070098903207940e98440d40d45009400c6800d0381010f4440d0002c0d561300c0500300d00282081000c10340e9 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 614309883 1250 614308633 614308657
    0x60503190501032d140705032b03090201020c031615390b01150305151806010c0c0b071101020a0f03031104090207050f060112050c0d140a06020304210c0312020f 71
    0xc261f042c0014903082c5220340c1030580031030b80c00d000800f809861220340601c100b8014500003403090310381c0c00100c0c0340c01c40c1c0401d0b0b15014002c4403080c1d5500160f00040009807084d0301d07401201e4046907102112035402c40c11200e2103484030840305080440241ea8240c015284000703c0090018031511030341400002a07200900141d00103003000785054060140e240c0c08000c0348240d00d0042640c0004c5180b6224410209074030030107903c0012034a078010b0301d42c0c250140e0000f24160046464115940c001da114540030354441c1400008028907620000302602e066501105e041c088084641c5c0541c040c000b80c4440600c5014244800700d0346070203a1011348401405440200311841da00d001c1c0a04265040e0041111040c0c040c8481c1c01003100020400203410341925010700c09015414104a60502c00081c003005002c0c2283d4001071101640245010794068031044807407048218100d0350348042d081114002c600010000d0001c280501004a650780d0307141000b501e40400880074840039070082030002a = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 614311133 1250 614309883 614309893
    0xb100507110d051b03070905010302221107060b120105060d0f0c150c020a1e0614090607140610150507050f101410031e110a060503190501032d14 64
    0x141901d82001100001c1481c11f00402080d4159004100701904208000c2c80350070810b415010580a181d2202800149c124181501e843e143d1034000090300b10f280a2a00c24155821058007000d4184242c50045030b004050310004561366507505500b4104544c251034440c482c1030005034000c1600d4500c03c0045c815034401815000c42d2040000c00440c61300500498a400f100e0300c1103a0f00ca858040d0305603120f600b4040c00748011044c180c11184903480e42250001e4010a2241c204820030a1009a4a0614091310328503620306410f0014192036110790304d0b610054422904086004000401030207026000741c2e012900a1014140740c89a11406091041d6a9170490050341303020760740083c4c1200719105505451442c5458050060004000d01c15131034101404a00401005040c3c0c49103100010707043c00040c80e540c80014000d070b0421621600b0145100b0040700c880d860350f220707650590ba0710010b031030500c2c0010200740e18900600a202006218820000c101181c89980f90010b0b5070340300c00045c5 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 614312383 1250 614311133 614311183
    0x4020d021b0a0201080c0d0b060c030a021005071e020a06090503090f0105120708060d1406070e120601090c140f030711060f0403080406020f0a030902040b100507110d05 74
    0x1904040c05152101502e402480140b00180e07800410b03d0f400080c60001240c40c0c0b2032034151040100040e10310390b540300100180c400c00b030f490040080c028081454007568011074a190100007528001c07581803001076840c001402a0071004042c40003400c5a030300c101c40c100702c170aa4071070f030460704000f0307040d52035500c00700f283c50350743ca807022950105450a1170301c4c038149581c80094481043c00504120240200100007070342640b03a01c500a08082d4000c0c01003c4619041c5c00156203e04003a44c056001415840a100860400c005100581d0071007000401c0d840c1c0c6001401002010038007000020030030060701c026561102c40c0e010344020307e81140d0555070380c180280b02515003a040c4902100c50b40080c010030403440118404954000d8240c20001559078540c90300c60000e21411503102c0c421000822154001e540c9548800b0b0000c1c405e03a000c200d0f844002e0104aa02500d0308109400660204020000142c040a01040c1e445010b810510119241d035075880c1041c048112149811195000302 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 614313633 1250 614312383 614312407
    0x302131407020a1502040f030b0406090209040c05190302090415020405061b010c0809030a030c031d1b0103050907050d0609020603011e0f030314090f0405070e090907060e100e04020d02 81
    0x601c0742134040c03401103250602d42540410005000c3c8005051400d0000004090001d1070b0400c00443c0e500800d1301000345400d00d040c400002450003454000c4000c45a0b655070000101e9000050700c0d001000740340c407613540e55103a42034210b0305418050070319028040000d4544600c030190450031122078071042d0380000090b1f564211001c2c003003a441081330070010b01c03241c0c40000c011038080c025649008184005e409105034041c2241c15003100c00c913114041c0c042d06018000c91203000c0341e54401d03a000e0441c5007080044041e900103460a80c4160081842004070f40b0b4180301a10610b4420307034010450710b007260001071241d08240c0c040d20a14111a601e0744442003403030315020103800500b148210460039910b0007032040035030703008804c08603000091000f00741d51200b042122441005106004501c4c110030000d203400c004800030b0303009404800c0030440521021400700240c85040c0d0702c01e09440c0003281002074000d01d06a43e03000380020740110300e40380c0e03c032400140200f401440025a41e84003940340 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 614314883 1250 614313633 614313653
    0x10e0613061b0519170a0f0f05060a2702120613020703020c04020306220f0b040614100909020c0304050109090e0d051305031023010308040302131407020a 68
    0x41140d01c2d5114180c0403120340101c152072800c6400844c01035a4041110199120084568000034108400c002c100b0204d040c0d4004071816002c5410902100c00c000c070105050302d4041c0c40d640d50041413810180440c200c00300d4002390b0492000725151010085481180480e4842840407141030408010844141002008041504880802113113404080d4a000f0745a8680c0d80c4114421900000440d0f00c3e5a9071a040996446603040311984860041224500801c2107002040c00f46081c0405204540341a1050070b00b100c10401c8100501844031040040200c0c041c6150030a02c20100008a4806024405001e40040c40c00c010743d40c65042c20005081548a03038040400ca90520702d11444080700441e141a00001c2400c1450f10f0b10706061a0028000c8281c02068140c40340c005101e00304a42030b00302e501546241c0a84440c800418503110b19207800034040540700142c204400c10044c01e1281e60502c0c020640007001840c0c000301c0300400d4094500781c0b103480040c0c0c4000349404c02d2110300701e1 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 614316133 1250 614314883 614314901
    0x80a0e0105030f0109020901120c020105060a0f050a120215160203060f0403050d05150415050f030a02031b0406030c03030f03060f051014070c030b0f01090902061b010e061306 77
    0x1d0490a501c0d201a45a07101d42050244980840d000300d00f10750f1a074060380301c8101e900001041031080c01c2c51950f00900a20b03048404500ca2950040c0004502248d82c1090098801c064031086030a0300f04440380203c1c1c0c09003801240c220002142e03421140c44c08201808803010128081401070702140101460480c029091038600481c3c5000d01002980140450308004e00e5140d0108066450200c0a50280c0ca0243d40d150064140211190101d508015484c180c03002102d8440c0748080c0f1006042d03540d050100000d4065001052002503084a0580504500310060002c1000c6480396650f020880c0e081e03108501103226107140d40c0d5503a82501500014150000010500d9850400010152101c2154020511014100c50003049000744c7c00c61b0001c5c2d0700322240501300c5940b89800500107a0032141c0e810524030320000814080c5c09401200c080c940c0003040941400041d08490b903032104000c0740340d55650b60300c0b00011030462060201c00d1248070fa41550180300511403d00d074007610b10800c = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 614317383 1250 614316133 614316137
    0x70803041b0b0f070204090c0e01080d0305160503070c080d18060c08090c01180b030112050d02010c02100f180b06040c1b080a050c100218031911011209080a0e01 71
    0x110407a4518a0310000744c80d142c80d0101c5002c5450716950420203005581c070303000f04629a0315032001090320200045c03048075060080e6410001e03550b1f1040e07148a41e081c030704854000194200041248203224640802840d406441a141f4118503980550110380014910038603075448018000d0a10059100d4030a4101080c108103400c0d1805072086074880c450349160505018a80c4040001e404809400c40040c00c00e100d42d5030380c0c0796101e11540c148014000402c450303034819081a0b42e00540706008108889179960000c04a8103201d030640000340c00f1444c04684a1580c0722102c140d09030150420104c2c00b8082d00084015041c008244000d60301c2e20480d601c2030040c060b40c0e15414120405042d0441d039003040fa030540310300c0307007003400c442c5031066029200311441110000c060f81c084940c001c04140b0b070401008007100034950249510351150301162040350581000c0f60000c60a00c01d00000604070500d00307050040015010346003150a0326401340c601c01d4000c296420000d4000d40408001d103424 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 614318633 1250 614317383 614317387
    0x609231003061805060a0501050f101e0507050109031206090911090718080f07060306050609210d20030933070521090607030503040503070803041b0b 66
    0x49880c80580180340c400200203542d503032020303407810100803803448115038020240d91590400548540103402c7c00c0c001e0510441c00302007055658541000c110700080090385408020004914244080c91440d000704000d000f400c102c100000390080c410801d84600c80d46174058060741004900c4100c9000b80c01041d44a45050007490100d07401d0030405245d541d00b01d1306010b455441000c1119a1704051139400c2400d24614808101d09502240c450075208200049484040d501e0100301c1c10341da094401c09400c10030030000c0090714106610b40f281c03000c83d190100b0703101d1070340140c116107815082e103074200000e01f03424441c507030b441d0707500302a0807240f100700c40110304144030b40000460080c100c1c00c001d1001c4c00e21700d401d1040303007030b04110101c520381500950b141c481180c3d09003241c6490f0345581c9030141c2c4000c001890a10180001603500d0350802401060610506a5090b2265440900103031043d220501c14200002e4101c0c0040d4403580c406c81c0c040010710f80800c0f001340070041d20b8220300707041c10003 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 614319883 1250 614318633 614318641
    0x102161b031a0901050a270204020d020c0307030212030402010e09091f061703120606070c05130c030506030f06010b071b080d120603170d1b0201020a02070506071a19060923 76
    0x9188608003500c7d51003110804035010a2000a000b48200da094801c114004603003140b081501101400c6414041d80983d45607044c07031180d40c0c042d4072003102c00a02043c41a10f00c80d140341054000741e64040501c1c000c4036000540840c3d03529801c1c3c450030802055130307203805041c0801d540c100c580002d18402030300154140701c0076070407a05105d04002d0407075006400c080303085418014550002e01c000d22018200c0180748550480344806800c01303010603004a8200303030200d01c0341c0c100003030300c000c2401c0b8100281016034203200d9084e5041d484403105852060084035056001441d1080240040030402c0042544403214140500498581c04131007180f00d241c61400c20200f1104d40844400c0301c510030b84d8aa80e00408490702c001407441d4460040030030203100c00203071601d40560060441c0b685513000c1302d502c50750351010400c1c58400c4a40007415070003100100b840e18440f05101c0d079085044403c1609c0f000c60300140501c2181d040e98800c035000d5403103d04a141c113100c0961140c880305401c00d6160000d281c = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 614321133 1250 614319883 614319911
    0x40e070513110d02090d0602030a05010e061e010f11070b0301091b0207262a04022b0e030c01090c060e010c110307180504050f0102161b031a0901050a 66
    0x24060a83c0c0f02c803030300094400001c0d0b88208044aa0591002085450b03040180200000b02801d0081101e403480d10400b2404902d086000301c28043c51303079004849032011060045071041100d190b02c0d400e0201c040100801c41d48240800c801a181e200005a103c1d031421407120f0a4880c1c410314540043c115402480300e803903000c6081d00a8951000b081d44102c11200400c0b51241d202d441c924141c0d000703900d0790100c041c501d40c3c4544082054000c1d8884081d40410030041240b250070840d000300d81420f503000e400c070158255a02601d0190030070000d072201d12112081c0c00c552000c3c024120b265034994a2008001004448001800880c90b29403a89101440064200c02c2c0c3e160010f0000500401c1d00030003550100207420103010ba070070f800c01e044a1244081c00c0500415203044405001d070412444031244148256a0120150301a043c3c071190315440700361805001e84001c6120b0002e8081c080f0126080c1c480181e207502040244221902d44036245a0031180c010b450700c0d0b01c2074240072a01d00115 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 614322383 1250 614321133 614321137
    0x2139020118020325211e020a0e06010c12110f0c0105070b040c1a12010f120b10080d020309040f2c28030305070f12020a05040312030c0f09030b0a0e0c040e07051311 72
    0x80362040090200d888ac0f00040e1900c24000e41c0080188000c0b2115000513a44920f04084018800080b1403983c0110038641d0b8890a080c1c45490001e602407141c500400c04c50002c0540040c050540c1c0180c0c10f440f2004921104100f008100d04030340006421042e40c0c10450303016005000565070002503500708203e02c104a00500d101074201c1e80080302107145424603e010000510681d011201c0861030400c0c0a5280d8001d06200c5100c3c52038698509011007c500038126424941c414080d0890004101c0c4501c01c0c20b203032000312491107240c055070700d041c0010000d806410050b51030303800b9001607460014103070b0300000d20020400c0841050075490607003040000c0c1c2401142280581c40c0c00c1c5100003100c6501556001821a40844e0114440700c0d805a2260080401651720752290407207540064804036034510000f8080c1315070030002800c00549901c402d1000341e034481903540303a803036800004041d26440c0c0503001182d00460310412117440c1402c2c0344901c00168403000d00c043c51070b001d2494058 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 614323633 1250 614322383 614322389
    0x290603070902070201261e2205030c030a03060f05011b110315010f030c0b162004021305102139020118020325211e020a 53
    0x80c2c1c0204500c42160b00130b41c4460300d0303480c26a44003d0003030341c40d654255000c00c00ba07035294036168101218589180c8002c0000c0d00c0b420110a40f0040e50a0106960300440a50314064403036010038004808800d0040c802880120026a00030446500f0031404003010400307640514144034104070804a1009040c0c0c10016860700907861015000b54180481c2c04d150001885000350311b5407c001060910038a080481035034007520019901d80c1d15040000014032988e06100c64036244410203000142121903030700706045511010201445082c4049000e076044101c104c82020351002d002d00c1070b402c080c07801020080c080c2c9031880001c2c0202110503c0d0f000d620b0103c60086444c0c9195a0306000380b20b04c01808010400041c0721042271014803c02e20302c400c400824010750800312050450003a6100d04400590020064105d01c04100c400201d1030f898565022289074044800081c080141580c0b034400c0e45140d10801c0301d90301645050304102181501d000c00740c010080d240000b50b15040004019 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 614324883 1250 614323633 614323649
    0x14010603021519111603050f211219050a09060e120702040f02070b090f06010509060108070f020f0f01060305010b04110405100c02040c090503160605030c0702040e03040329060307 79
    0x80084000580e08102ca4244401718610351800000100500007031440e05401492043c0da2019604001c041c0000d00c9400180640c44000c0c02160b2801c8400d045441d00301000d00c2c0c2051103c6040139025080c1d80c0300f111b10903641a07403040540c09100541c000c202d0b0710100705000e0070440003940c111252a00658401a0146a54940c52013802c16154121481207401541a00f031610f4010b010554486c01c000944c0302d01e000d408000126400c050751101c3c041c120584951040e0340d11044121110940405008110300c10500107200b03c0205000d05c81c0030790201000440c0c0c45017541442401d440e411885140101d1505404820000209064030150f42086a1540e800340302103c1c219112080010065400380c41c0421881c0701680101e0240e040b6803040d004c1c0d600d0000c130801c0c03141d030b014618420803010580c10000503204100820051030421300c001c0c0001202074101d800d40c1c0c555009508112114014503005048400c440a4a0042ea00552031004250b140c1900482e8803032600f40704e1210 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 614326133 1250 614324883 614324897
    0x100201050721020702040203040f12050405092d01030303020a1b0206041208070b0c0304060501090b0109090507020f0609010c0311040312080a1b02011e142214010603021519 76
    0x82c010060f011164100c0d0014403d64481c10a420800702e522085401110740c8080c1c204020b41c1680141e054404668000700018150b6441c400c0d080220050760351a000039034030320170440c1c01e80402401c08901850103503500580768051080042d000d46a0502e00405074103810481d400103a4440c400c031001e0700e24003a418030f0f48881528055603035020b1580300400302c4200b00d040104a40002025601c507a004038414002640d0383c0086000f22420001c1d500c5c0012503c040038014020160001e0303401c801180b04842d5900b00c0d03815000d007069416900c0ca9000e9465020001c00c0700d5040c01040481c464a0020916161642d40c40e00501c1c446035450000f0321200e4000125110072941c400c045801070307400340120f90714181c1c1c0001d009004403035a060070440110361034188200e0300d10450786c4000c2d5089094480e5110590781507045201c00e10001f0048440ea40300500040a034841ca40c0140381d85030000c9070003800d62042010001c42c5031401c060307046041c1320140d295440c414140b500c0301c0301420000 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 614327383 1250 614326133 614326187
    0xc030613080c0a0f12050a051602030709020f0909090f0304090f02041d0402010306061d04020313081306090b0a080a05060a0317040e1308090915090c091002010507 72
    0x704050052004412050150840303000c1800a0183c070020440d200d10408040c1c40a1004207986038042d800818002420621001996400803041114994001000c0b202030941e10030015069a02c500800c0034401000314812105090500e241a00028104094550786d0046070f038081c0c2c3da028501c215403025440c0c2156281c404c000743e04460242400c1c203800050401e92240d0480c1000e0b05075030490001c0e00e03000d00020801d12801703005c40841042c00404421100500c1008080d41000d85107a482020003246100000c41001c02011582c18524030402d000d49000409030150301c1340d0384a00c4031140100004850705921250980d8089112100011240c407080045080380105070002424a07030340764548000d01e2600401390003250251820148503580d0030800c050312a103003242c0145004414041c42025250255071181d1127500420141d2000c8260000a502d00800391040003500c0d10014a100d07480c10003000c000f1450398a40001d220324140030100910340c603441c072000c902c075007074980d207034 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 614328633 1250 614327383 614327393
    0x80307080a0908030301030b070f020a0c1e121209060203160b04050a0b040b15030304080303010302010e1f030903030513030e0f03030403140601090605030a0c0521100c030b030c030613 81
    0x21074090842241200c1e140c1d87c6a24101c5e99402d030542d09030003c21041031251140600c00230303202c480755034006011212185001f040c040403001045c1100341c9450101c5011510114101c2da041056018084246e13242107204000703491b039691900140d0440d001000042507045d26005030b995003e621884203000b40c1d0f41d0741015801d040e0b09550040440040400740805e100ca9041e46034007481c245500f038059420b040003015520b20441c4110318680d0000c4c0f00400c090347c0161132504090201801540f04100e10740201c540c0a55074030707070643c00f0a90350900c150034154980300b00c5a000390002d850504180c55602d004c0c0518402181040c81041004407020b41340c1c50600560300210740c0b0001c0c0100048060180b00d868400c240034030a0194508000051940381c0041c043c003800f90010003d03201541002c080c0440091540038030b14000614180c5500b448070300300b0040c4803094103000d0005040c1000c00c03008050342c1035041c4082c4039501c04040000d0030760300032440c1d80e0070212000340c45003045054581 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 614329883 1250 614328633 614328647
    0x506040e340908190309090b06190c0606120f0b07110304080705091003080f0702041d0321370504140d0201050f040807020103090c0902090901050406080307080a 71
    0xc245125090801c030844400e400014140070707a100c500603550020f811500c00d9061001c00007000c0c00040e104075040202e90305940c007154203620b001d08100d1401c2559506100c10030006c4150030f0018002170510010700240e4841c06020300500c5103403540c03800e419200c2840e10a40c02e0f00180c50b15082c0350100d80003e0041070f494118a428009803502d6035504c1c20010345031001c91088900481c0d4520004682030b0000c0103440a1780c1c0d029280340d0030401e212031406196003054100b00d03002545c3e0180e40d0300220107110340883c1362090000440d070301c1801d0036031111200254854200009002c3c01805910b2040e000310540d81003d0b0103011410324050041030724900c40080c22103040b5450034003401300f4800e00500c03200181462034105ca01000c680308040303007207800c201c40d04c6030030700030748004100040d051200900b5020300516011600f0542510784520008481c3d000c000e445a00013002405802c0c2403000718014401106c040088034905107a40e070b140d110b050002009200002030701510b10380101c2c5 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 614331133 1250 614329883 614329951
    0xc080703110703140c0103061406070f03020c0d152409090303020405090711060c0403120c02040f15060f02030c0c09190912090509062d120102040501090506040e 71
    0x403001e2100301c1300e4406030744070042c40f2900350019042c51404141198914400944444090850f516150072038482028078400a801142103020f01d05189030b10b65141840c0d46500750043d0b954200340d6030600500e03c102d8060002c5a010340c3c210504101451a50031400310465130440808200304141d441d00301d00a1085800c190b602c1b103001414060300c0d0790300418454854207427804942180e10f0b403403804400750050307110041144008031608010a0310071045103c15501c040e0011803480409420b51059584420309181c001f00703031680c1003125561110244440c01640d00140d40b529425000107a1242840b1101900502904010030300850030608114030025644500304810803492074a00403520503456050700085e40c540000c916854460000750050000030040e01010082e000035020840500804081540c2e1810440c586900c0f0004280d44400044000590312070074280054101001038005500801c024041800240c45c150030158111903145003415180c0415460134a11411101d = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 614332383 1250 614331133 614331143
    0xf05240f0118060b1605070501080c0d020d02090306090f0d051c0e1c0513090b0f0415080f0312070f0c080706060504060b030a05010803180d020a05061b0606010c080703110703 77
    0x2617001003001d07034140440180e0780701e01c050310102d40d51480116210785d410750307610110f0f110401603081001400d5000300401c0c0d03000c00b4050704001c100d00c0000e04001e02103c0f4941e2a402500904130555402d20036400106041d08066007030240583d404840248443c46202c2019036601c2103505c098010031510030503500550f521240740c1e4010320001e20036005002d680091140c0c08401055118140c01240c8401a0180c2220044282a07080101421290310464003070780c5500404a1829028044070354010b410340025070381c650600c450699443c0008000204100071703000030702011030340b001c02d0320901a00f22f4000c61302e400c101c0c2007500041c0032550002d50b20a01d8440d0000d1200803950140d4440c0280e16400c10642ea070b681d40b4503449224a41510b090441100b501050a00d040c44013285100c2c00949034007091503e42c404111240d002c441c5800d0f801d44000c508400c0307650100304242d4014000c0c60000c400b24500e0380c41d90582c1c000d8520080905c00700402110541c40100000c0700107603008 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 614333633 1250 614332383 614332387
    0xe1e010309110d2d0f031b050610061815081b0417010c02010e06072d030509070807061e02010e060c19080c0d02090d0f05240f0118060b 60
    0x1624050b0f00182500720b0050700c4860703514000ca0502c820102010f136071900842003881260041e034040b00d481c0d05040113409600310074400c0d9008948100861442131040c908000080b81c203102c4080d088840c5818110202d0080b51418080c04121902c00e0b0f081003c036041c00c00c00c98440200c01182050422064171440c000840c0009019240491a1507804009002013249442d2010102d00380d4000c000442a96400100810800c80c45080105042a10f0201300c0e0541a9447c0d01808158440804100060f888005003d007191090007149e008040000080c06c07440e24150001d81000745401721409180a01400d416440703000f07400c9883d51b8058401907490341d107420001c0655a410091000c44d0040c841000994464080c965080c0614000100305042a00c05420b0304d01a60001c40800d4120040921290010311140c2d840110300e8460000703054207511844c00001280700f4140b4200c0900d999105002c810089001c403103055859404a0300e40039000c000b0003001801c1c0303070341c000b0b0b022500c0 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 614334883 1250 614333633 614333659
    0xc0d030e120d1506230306011b08070605090f060f07050702090412031a0a05040e010612060b040f05150409020103060b07050604051c210b0604030809010e1e01030911 73
    0x14590200702080000311504480f2030b1590001c44a1081034000c810400c80c0759200800c080b142c000c05541e0015051611042c0d030214280d00001070000c801e011610307094045414000c02c03241e130041550103d10032000302000c90011049907510b03000900044002000304d400300e403003e88108201e030040c079000b8081c0d40f08ca0a10385481d0310042290768101d00013078503040c40802d600004d034495102c0f402005101c1000c0e50700306402c200042c64403600d034008640d44e801e000290000000110310781e081c05650009a0001454140015900104000303101c19103400d0401480600c04920039410350000d64002680306040d200603801080b1b50b400130400c04401056030400c0240014005100d9403061068500b40300010340610485440e2200c1040400c0142d04410482d105052101d010100d40d16000b20b514009580407415a901581003aa041040002c08842a582281100000300029610381c00001e00c0f1028900d1060300e4900b801e81059146d203040003e1125103810700585c000c3c0200800c0311200 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 614336133 1250 614334883 614334907
    0x302040c0806130b0109031104090b09030c12030106090e040c0b031504180209011503020405040c09093e07080f19050903210d1508010b060c0d030e12 66
    0x2c8a0082c481e2901c15088081050075014001c600d00f81a11444086400c642c1c035203814491424a150f04241d5580c403400c007013620007840714000d1101d00c015607920613a44003980d040c1540040040d440c0b150030801040043d41c001c0c0d022040f00c0e06c0d80302400d010707140c515085200525039404103175003400110602210301d840204242c2410000c4404000f542031252860902c81c48940b401781d44078007108010440a840d100c0704550015040c0303401486c0c01d480310000b0341102c480c4405000080d11654061000082d01e100d104080c5516245100c8440c825060110350ba41109403132055810504c0c4000d1000c1b1000780075110000c0d1b00071040f030b48034234521006e090301360881090309900b07102d10625a00e0460080c0d0880d110001c004e000340c8041d50b01500c02c1002d400c120322a11900b40000c00c5032010060b10361041d0300c042e0713402600d405c0070b86140c071b2555400d551403400034510920b0108008045140300040060305042c86080100750b80d54507900040c1018484804403220840000b00070020b68 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 614337383 1250 614336133 614336147
    0x705150601110c09010501050715060f171507051305150702090609040b1f03080c1606030209012a15060510030513230109200105070804140a0302040c 66
    0x294280d844400070b080c40c0000955400b2074048040e08079207982d00506c00b5500c21030043c29201c0c011042c06044840140500d400c44c2c0302075000700a500400001440000c0c040c000c9018000181d038000c28050580e04014030b11640050701e00d80c14030400003000551141d4a06203080100002003a0920060700c1c2e050380e090325823191030124030035081000090781c1807510710045e40c05103810008102c0f4581c8c0d03441c50100106002c582c9a454004581030000000c0d034100003c02d00d070962000541144034018111070306101c01c0d504030000349401070100740c0351139a000e2009840c4101c0c0702208518007040c0038182401201003840034201c2d41c1c1008051007242040e400c41011103400351400c04c0c9241d0b519400314212401039800b10180301c500360010011845c0c407210340d008050320034017140409081c41c802030300712900108121841c5090040c07034149031070002c401a02c04402828100d1400b00c40740d0700c441491143c1e002c2d61620000a051900d01a203a481c9210065503010b0402c01ca450b035610340240101c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 614338633 1250 614337383 614337391
    0x190b03100906081e030d0f0207020406140f0114120c0705070602010c080f0402033f070f08180d060207120309151d03030f011a07050d0f020102070515 66
    0x800800000150314045214050442c3d40742d00142c0854600d4915401e035001c03402c031816405210500c00040340394070700e12411380c0030030791107000581c0d8040d5481408295a09030b03124000e140201c680410041c2c645010008640313401f440d1403c180c005120086249010700017180304004500d0080001040300c00c8010140c4a01410032150f1041e69030000700d081e0380e4005005000100350380c0106596102c119162038009200905542c0071441c04211040030703400300c103031400c40301020044a004145001e0b0700c442c1d40f20b10b0351004070716040481d241d848070303500b001000501c8410000b889202e410802c848146c02c00b5030041c4480380700036040c10804082d4009030400e40b04a1001040214518000d01c03808000a40c405014520b449102d40040010f210b404014016810400900d2408140c03d0004500c60300c4075400c00740141d414061801d2416821003002128400d0400092000c10070010754200c1d090001e15113038140e08504c0104a01900901d00010300c1c1d0f124070001c5606180198890901c1 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 614339883 1250 614338633 614338651
    0x30105031507020a03121407120e0a0506060d0f14011409010b030c040f15090f0e06041e0c090c11010e0a020904020d03110304120b0f160e190b03 64
    0x303104440d60304141d000da41502c0540141c0e20807908500042c2c0070b04102c41d5800b4550000164501024010042c048012a41c110010f4446254140c61388070501c01c070001c50038020000c1003100c400c2d43d01c450b134607440030307001c0ca01c40c2c514641c00404100c0c0749201511159407282246012181c51081c3c07501821400c00181b40005000b400a40c0c0f800c014071600301000030060081111890050a200041954a5102e10b02c03580b10b5180da06519a24041100101107460000032500301c00320712a41159899460901c5a40040342400f010849c1c130000d820442018005802e4a9602854480d010001e40d9200040050a2004450710340c3d400018072410220681c000b4450605c2200c001c3d51158000c5c100250702030382c0c40021030054100503080e146401c2c03090504103603403a441e00e40f00f407840c1c101d41d10002d0320341c20040c03500c1d0402c1070180045420480741d268684c40e60610561148002c403050b4000ca081245502612070b899458841c001d5101400c2e00945840a48806040410f588105c0f40b090f1 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 614341133 1250 614339883 614339893
    0x30c03160209070f2010180209090304061e0507240c0203031918020415090b0103050c0f07060f0216050606031c0f031103070806130b01090b0a110a050303010503 71
    0x150f418014002c10140a11680d00d480300340444208030314000b010f0b441ca071000b510500880d41400c43e62841144012a0b440000c1d00c1350b00c2c1c0e68030401ca4119002004101960400d02080003181d4002c00301e02800d04076048851030740300048200300e41c2401740302e10140c0101d082c04030301c40b1012840003210403842c00c407481c00e1040c00302d05901aa41d0744400d840305822400c0313002c0180b55942d4030758051444d02004e011082031400542c1c000034250740003030a00c86032500342039804010900003481140c1c2400c0003800c0502492802414415850103202e8400000301d20010307120040180303a81c0031400b035003441c0380115101c80c0c0255003c11411040c00d0115028403481e400710707d44c1d02d000900d1889070903001c0540300c0f68000d11002190000c0c40184030070245500d07040c1420f160b01c60700d0301862194131a651984207900c3e101e010800c901903002540b040140ca040e440204a9a01080d008262030b692201c283d900c00d15058200c5004036800d4a507084c5016026000d0700700300020000314122103040701258 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 614342383 1250 614341133 614341141
    0x40311040b01120b0414011511010902011b02010203070212010501060917030a20060415271101050c1902010816020a1b26010e030f0403060509030c03160209 69
    0x4012581c99182880c0032803100ba08001c105003260700152411403001e440070030f40848110801c1d89a04c401c0e00140c1c6014003c038200c0310010b80c415044607240128074002c0c0300602003600041d001c2d80d08104440181d201c0c51060409590080046682c00f6034007401c449422100046030900801080c0101030029070303c028001415002010f03210b400c0c00c8400059440c0040c0010181c13102c80104003c2d4010080c09030031800240c030107000c01407169025001016841a0030310040702103442018102c0311078070b09a4ac00320051586000050081e50748040300d41501000800107030b03118000e5190100c49031140b54040d0302c1000b180382169a00900c01e803548429030312403101101c441c614034075403400180e1140f0052800310f100a8141d6044c441c0344c48907002401d448021140c001090000350442e501003c400c010800c280901c14924140100d402031814030300c42c00c00d29071903842184405862580c561011440a0713009204407012540000100c1c0e640f61005000c1904607030b042c0c103051b032182c14104001 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 614343633 1250 614342383 614342389
    0xe0313030b1b030f06040b060a08160f17090f010f02040515030f040f03170702060f0105030106210206190807270b030a0e0105070e04050c04120201050d14010308040311 74
    0x211a041c00040d00b0b00e41107982c4c650404c0025200240740d280e01688920844103d600d03848020b044038000d035030702c58109281036008014420044401d6508101c042103200030b10b181c2c05081c100780304813025040b5000c8d8440142076403030112900e800105079460a002241125031a50060017103c3c415114141a0004031441c85200d0204036007044607103032050001000500d0804000c1328243c031a0401440b0740782e56010040203860111200809070307108a0502070300302d045005840c01003004500034000c0f103091003201e913000c0c0403590886e0b881c482c14040180455890406607404491480424016540000002800140103480e01008901e400300c0a94500c403060540c1c030048a20100000714444c40d000700c0010b40d81c0010301d1010020707030301c40b0b00d203d000c41c1c203000d200d0061403d40ea41480305002c44080208940010b410480f49040402c410070030703401301d4404280c0075602420903d46070301c500806034028000c0c00f40350100708104000040304001c0d90102030f00a0b00d001c1e140314041a2040018 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 614344883 1250 614343633 614343661
    0xa020309031204030201060b1b1c0926060a062103050306061b10050106030e070e04120c0501050c280806060306032b021c140d0e0313030b 61
    0x109140c140c1042158044014102c64903c3d041842407000041c0c496170343c81d80d000a50000101c01492018081c01640c58103800c1201c410b04c600d201a80345105024000080c4c91000e1601c207041030203080584440380751408002d0b030140a18510252401c52400c02130440044c151805a10100b515004000346000c07959017a0f18459036040c0ca5451468a03000304105181e0421301c10740055a02c0c83e29104030510741442203100c214560030000c82c40354100b82c005011b44080c070034001a80c1c2e10116003000790080015503160001c0e00501e041959441d42035040355040342d40c0e14050203940c280001c1c80040581c140007490301c2d0300d02d82425820140b0007072a0140d21001e400c135140001e5214801f0134074a290130b40095400c4100101100c035294614248015a409012142e80081100d00d820140303440e0140189a00132040030b940c507480500f04103000d4101c81241e56105128500452003034030610141d40a440d844000c0c004036616803540b02854044035510f0f0108a07140c2140c01c010401d440c0300049 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 614346133 1250 614344883 614344891
    0xc1b040c0801032d021206010e010911092e0c030e151209030c0a150b0a080303070302070f1709211011040e190c0c020f010503040302150c0c01050a0203 67
    0x400880610036544c0b8001010709000c0420024a8199900b40c005a40303110324024509041c00241030b0079858141a1051014140d101c0d100443c241040603c5c800c00c2001206d14044040340c80d8202e980e42c54484440420054050421040328070052000c00354000b801075604612940c0c80c1c111081d000400d0200c04d00640c280102c504806010749140708107020010b0f0350255900046905046ca0a4015841c00c01060025a07808a111040d001030038000d02540d800c0034426070f000c6804924140a141e80c07480001d180c20201540401c0600070080304d00540030703400c1c3d003100c4050410800e00c0524030840c4d01c1180d041d40714203550b0641206100d110081d8524014900002d480c1085040003450060301c06c4851240380da150030000402d400f0b9141c0c003400d0141d803003807040c0c40040599402041c1107446582040703090043c11007003040141c0c1c4000e80c2070300e1840c0038a001e540301c1d1150b15060740b03484a01030002000e10314200800c88030b60030040c054201d101c1101d000f44000e440742c00130ba200b03c0c80700791 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 614347383 1250 614346133 614346143
    0x70e0a02120a0c020f01050a0b0a0512030301151403011716030b06280e01180209090103030e0d0c0b0c15150d14060c07060b10081b0c1b040c080103 65
    0x40029601c0d002d07039000340003510140c0195401901c0c80030f480c0c0d0864000321400030b20079564400d1510541040a819030141c8400d0782c01500c02c25001c1510ba580340414030914628154603144611802d1180d03480d120040d6042149545a50311480100d05054803000d000c005440749541d00a050603108415400f140d030800366280d11070321050107005d40c00e8a1511010501c0807481d9038940152030801d02000240400840101954141160329006d4202c0c0420b501e081030040c030418200350389180c051811641d05003000f100c071200b00004601c0004943c400584011a4a0300000e011102440180000e5100405540500c0d066101d04602c00b00165014150074010300c044140b503040000300520482d025001c1483c40b01d407989800c51410000302c801214400c0b000c50154104100c038024907102030012a42c285c100006040d0041c800ca00050005000c01c580105c030364817000d03940e400c82d420344140505440341240c0d09012081001d900c103980900840c900711078801128406c0a100341620b5002c = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 614348633 1250 614347383 614347417
    0x5070507020a0b2203140606090c1c1d070f051012050406021303051011030708070e040b040c030e1c050706022a0604060c050a051b01020f0c070e0a02 66
    0x111000c1c88403a040100a00d2503072054130300b886001c28150076a14029407040c01110250750b001d0382801c0c180f2a003e04514010b06c5070b5414002c800340080c0030b40b40b800491541170101100000e11160140003586007a10131644614062408014040b030b2030803c0e04d41400860304d545036284103000002684070045070000b117000603101a04c4040d41c02a90304140100310150420400241d0344c840b40d9101c3e8022140390303008403094807034407403140114003186440c004841e08515003002c000d03013947c2c4010266000c00003140c000c62203e954a80c003140e20300e640030308100f0502822820140c0100742550b156a01407082070100d042a418120f0341c419004071541c0d80504002540d500d42002e500500d25002e41540a02c00d0583d2004c2a491100d460318103ca004040302e0615040200c00c8400c01166441001020801d5842d001d400c8004c9440e0012007081d83d218800342c0c581140d00a0054601c100c403402d1000a458a962000251075415110400007440843c0c40d1040a08100e1051045000c040400 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 614349883 1250 614348633 614348639
    0x91606020705030309041e05130302010f050105011e2a140d0917011413110d051e0309031b1003090f02060d0902040c0908010b01020f03040b09030f07090f05070507020a 74
    0x1c181c2006c0010031407d800d00d58004030301c034000000c1e140c0445401d640040c0111400c0145642405203003c64000d440c1d04010b254100030000702118800026429000c00c64810f1070509441040582c00780d0484000d104c2c05604052003030700903d0041301040d0f40c29035820b80c0d46144001c002c200c110304d08050b5111401c0303182c50030311840c4035210314250482c00365680703c410307064a202407280c5500c01e40b10050003540818543c60004480d01d204034003280191482407100740042c0c0c2c009150589030480c034619021000000740441d15500c50980c416801d4000c0d021224505404100d8140d4101c5080361140e5110707121860480481d118505d0207440d860b60b01c1003e10150400c0d1b40100807100c0a0300c408100040d00c1d40108080d03035441104140020700203074040040c21030038403070507034001c20920140581216032041144c2d82c1c0158095900007840000b0310900076070341001015a18001c403c11b689c01035907a141504000c0007400710681c41c81c0c1c00c0c8000141c90300d10450403140280e600400b1401c0843c2 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 614351133 1250 614349883 614349889
    0x3160e04020604120c03021f2f0f0a14151605040302090708270a06050901090b0f01061805061c060504060e040c08060408031f0e091606020705030309 66
    0x2001500681e0401c004000c081035084003030760752042550107050204c5c0e2003450b5206001c10f08600c250360700f1002800044c0940c080d94080490501504228402e1030071560006201c0d440704200c02d020040e5204001080a88038400b041c02200c01e40500c10781c03004640d00c401c005803039a11810a60040213600e00001d54440000c6525000e110014500315003416140c0c1d02148030001300352401000701d00f100040081951070011415440000083e42003080342031515000d5940342905401043c0a07120b00002d12008001d40c00295460b0300241f010034030b8100078841c242d041d01c080c01f449000804820482480115100c400d00c11648080c02076441d041100c49048000d046511105c40055100c640024156496000301e0024040c0d212422000303041c80d03c1c1407089007480380d0002880342c03c44030400010a5a40007501d80c001265100341d4102c8d030346294440303580f0143d43c00c0b0749150702d05d420500401420000e81c06401f4911080c0c250400c5481c1d50040e81e40b0340281c4030716549a40100007184c01c1b41 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 614352383 1250 614351133 614351159
    0xc021f020d1101060b1209010c050901090605090d0b041b06030b060a08100b0a0e0406141c0f05060708090c030c091909080d0c021014010b160210080601020c0316 71
    0x1951000001103058840d541c031a440c1d4000452009500c0303281b02030042c005004c0c030924800c0506418154035207105100081c0c10000c45104090900001107507050254481c846501c0340c4960150313081680f031400e4902400051104034007054a04550b06011654500034890034061050042500c0d090043c066401c40d03020900601003640042d20f0440001e107406454040c00340400c20361030b00044804440d0910040714090340c04858003252040d02102203849074416480c6110032030000020717000207410302c0100c881c00d846009106104410400524950225000e0301a0110300140d8100069a07000c050b5290084c0d040c50381e1244074580030903802100300480d276407140054030010429200c81d445640480e0032601070340c5187d03a203607a13020141075418407604042c1c0051610420803110089090345141c2c0c01401008200b680c0000c001c0c0e2507100e00e40c825003030142d0082107025040c0c0c201d8001031098005032182c6025104460000c00303249008100303641c0d11000032035040c0c8814503020b8000010 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 614353633 1250 614352383 614352407
    0x9060405060402092e180614150c07060903021e10030f060308030a021206032e09080d09050f150f071e0e030c010e030a060f1b0c021f020d 61
    0x400624260341c2e031040d003840d1030005201c08100c07084042070700d0301c04000c241034005000741d21280d142106c140100780c0303280a239214000b010381e00340b603020304030f03a400d05803512031002d114031039200b81000000d81c0f991020000050701d00c00e07a028428171200c2101503a032047c4000c80c4c05c0e403000d060f004440066100b03901c00c03081c403414241c0110f06955251241701117a401501c92440007500042d05507403880c00701c403082e500900b09030001d00c054841c504a82c0440d41c10385150400e03003c1c064103101060890340d0040380060380c010040031303956079100780f1100052401210880305806030200400120b50003241780b10b00b4081e41c04800340d1030759612088480c14040140300d4418030200071240c0c07a2501114882c020340d40c0294450420070381c000f104152510320b014030307554104460010171840c641c030040707030401031140d003e00f010840004580b200d00250000340712040f01c045114451880e0543e022540e040c80f64029a4849640000d210f21384540c0c421044145016a00100805041d548039110035034070 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 614354883 1250 614353633 614353651
    0x12030e0f03100606121a0310110d1d060123041e050907030b131a06030c04291c03050c01020c0303040b160c03090b07110303160b0906040506040209 65
    0x218051208102e08440482c0c01080000c0ea001101403801c541510400014142c2400c411480180c0b100020356a014048440701c455034031454a0320660414600756801e48041c20700c244095020711400303a80d0303540c80740c1502c1c00a1050780000508100200882e1120300e032103420708880300000704203003c040c1c1040d000e0007210680003143c4144070880b03840741c0e03801a010103001d01040c92450425140001014200e9014600c491061200150008900001d032a08a04201605a45050020b400c00180307080f080d030040e00704008a1400d9404000004511171030402c103a80440c1d182b030038001900c4030b5114051002c0b84852208021070f0050f806420452071036070015203420b4200d10401d0840d0420b4074111071b00704000080c405a01c4400c0540e80080481b032920b590399841c0340d20001c00003040e030711405813131140018508e800c1c004200c3c005140c6590280c12203a07640705040c01441c0d81380e006e500a40e40041c1503804951803a0000c9031450040f504200109203a40701c0c0d0b0200001198040c2100f40 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 614356133 1250 614354883 614354893
    0x40c020307060f06050a14060a11150f101a160206070c03080a030b06070f0b090c030f060f010f0f030312020d0906270b0103120504080708030c0712030e0f03 69
    0xc0000c080780541088001014008140d1303078501000d00c1b10a59007908819000300102c290343d111900c90b54142e030041c1049103054840410014a0309081120316550a122f1070210301c20002c00d008441b030f4641c05000184501024a5580d034130307402400c8c2c40f2a8004007800305c00c0260000e000e50741c1d8480c3c800355000821081c50418540c0d04d030034640d0798a82c01111168004218001150780512400c8a4980213840d240e2900000740c9d40c401078076a0000f4002d044a0005c004290040410052003120400190449101c3d5008000709681c07044201c5843e00420a02400400e514004680340412505800c0030b148182e41036070b900703a4901001d0201c000c01243d0070f1098000c50701c118010b50110f0380c0104400240300108500000c40141c19101a0f00004030201043d0001901e0740a5039045a82080c12141180e0b80b058003210741e07200b20f030710411580c0300300c800103c0d01d0003004c0001c06840383d04400b25050141d8400040461610100001d00404e03030355510352000d030400b00146403c0660003400e40b2 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 614357383 1250 614356133 614356147
    0x12180f050d08011a0708130f120b100e0f0a021b03040f120314030c0d020a08040605010e011a09120303011e08070b0a0f0210020409060e15060712020703020d03110624040c0203 77
    0xa94801001c9c1e011005044100c4400410301c584441400d1f0800c0310080c0c0c002800b818004a2001c041000c3d20179040c010b0542e001400d201c10b1941600c1541c510340c4505000c5a20020a403680c1c0c0c0c000c1c0c0a011191140c00f400082c82034226511900c2c0c5652603102c4055030313168004c034901107400041c12004238040800440b8000c0c04148010592180240c540c201c0a06240c05d14504440701608034400802c801c3c001848000034410070141041c4004518550b150981000f18504882055a400d1648004400854032040f802400505110022000c2d43c4859682c00c62656540d00c0344181c045840f0100030090320244500300318414441280104d405000365400340ca012a0b00c641c2c0a01c4015548480500c5910700e00c50f9800c1d00144410040807044d2043e80c0000c445120300311340140105c925080e2030101500038080c0030000c42d001400d08a141c100c509028002040c03a1041100b40c0c012280043d00c0e4115290600c0445150f00071820152680c10b13051000a080b10042d80701903102c1403000b0 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 614358633 1250 614357383 614357399
    0xb061c050d03020301031a0c04050f0117040f050d050a09120f0b09030d1a0f10090806040b041109040b04020f0414010f050f0d0312180f050d08011a070813 68
    0x505401c45080c0d07030059803917166007004214417807038a04419120b601241441500d9803040c0549040d034074100c41d410300e03100700f40c0d0050707420034841d02913194200d403128200300c280b11682190600752801a01620001315801e6412030706480365802d01400b291403c01c0070300100f00015001c4c0311040c41a05000300b9403c0c00d0b240d400c680070741192051140e03400058000d4243c00715014015840c54000e0041100807000800604600303480d118050041d9880002419868403425900008101e018251041d50402d07050039125640111810754109425a00242d254105106442e00c01e80e08980309031200e03140c0c1c1e420050340f0120144080c0c0d101d902c605050294130aa0042d86000b05010b02c50100344c1ba00c0c042c1031080440d2a2981d6900c18030400c083c0b0710100390022400e15542042d0040000c1d40c80c42d801003003200070280c0030f01a10f04c1540000315020410006050080101c9688079107095a030b0701c03860345001030410300140041c64410b20040c00082c00c0440070301000101e910b8103c20080c0c40d6104 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 614359883 1250 614358633 614358643
    0x180b010c020d051c180b030705040f1401181805150a0801050603070801020705070b0d090f060b090a0b0d03261608160c0807021219140a0b061c05 64
    0x3083d2a01d400001580a0580d4061040c00105807141868545803241031885c02c25002d092042d05a408000000560768501ca802140c000c3d0440c0c4402c106040d80300d194110700208144911400300300f640b41040d0040102c1d4030303c0400c868080420120001845da6048040c06c80600403000302602c48211000700e5036201e001e08060200c072800020309140210070186444070a0b48807880c66441040580302146000c00c0d20001e50b11801d070885e41e100341411144000b0140208050a000c0c14a084174041003100d030000d10030200100d84220f0765840b605180c0c4c04444200041c15813107400441c0000000f402901d20070039150003903558503203c078100c0d1f0140c5099034049600030f032403900018180c2415074000300c0aa0308402050608003005152440c041d12030541540c002c5d054400200d0703030000b10341c0c82480400f8041424070079111005c00c0b09140b40c00c4522448821074004d8600817911080580002d03040711b1140d04040200b5154a4180510400990000c0f100803440e0390801400e001c41c10400c4 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 614361133 1250 614359883 614359909
    0x5040906110408101b200a080f0a030c11071202010e0306010801091b03020f090c0c01060608010815060310050405030408070308030f0106020a0209040201050c070519060e0a180b010c02 81
    0x3000e441e813000d40c0401881200c004010070001d49182c041801410390f03014904502c1c5001c5503200b401c100305071008a43c540341c20700c003000b0908070300024450035030100507000e030045c908c01351024801140900c034180c6000052070410403055000754010000b17110784410502280e40181802e001e401801000b0a0410009801076203490303454107070100030484508041254403003156020780110b0b05550004d4140c00e94114554440c48411000c00c3c1090050340888088064150080182c5640d5078005040041d091041c5001070140b10034001d040c49485400c10301c2401c004002e003603240114140100100301c00341044c0da9510041c031001c200340b501004080e000d18000d1004642300e24003041003000036041600701034110340008400c1c40068449900c82504950309007043c507100c40002c840303a032801c59958081a0f01c040b0461040d6048181040f03040145d8600703a4400158103084820300c034200d03200740b04051811a070143d01a02c0d003981603010301000d1728145003640f4031801c0b80c0c0004d0303000d64520b8 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 614362383 1250 614361133 614361149
    0xd0b0a020d02180321030c0d0f092105042d0e010305150604060503030904111e0c120c030a030b03120a030515030f03071518140c010305040c050409061104 68
    0x15400740c6a0307144c00c201c10510044180301c0d102e10315280c6240c0070070501018001c0c8903000302c042400031071101c03903410400340b02c19096801c20107c411801c02010003021a001000c00212106018050900c54001c58065540418404120080030408108940c5c002c050400e51348050312400310300881d00202c001d0085d800b50008000d407070a8805010118840540303203a22491038200c1c00c010300d40b404010b4445880d070481c1c00040003080035042c40c40700d1140b480300350400341c02042e0b5103441c045110090300c504801c41045401c031a03d4048021071301c3c0300342812040c040e4424806d08500d0b034400c6c1c1007603810f4040901a5082a5040c401300742d031a41052082c2c0011903103850402034000211214040c41e0390049000348842c1001940036601c13881a001c016002c110409c541030381d045643d0b0041001914107116050040ba07850500c589a0000d0403040182d81c001d940c101c4407603610a004e503500445e04071454100280c0b0300810400103081001c8225103180d200d52803464080c0e16200604001c100c08 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 614363633 1250 614362383 614362417
    0x3030712021602040f0902040e031c020c06011203180609080114060a12020307030b07030c080f04080307202a0409080708070201050c010e0109020117060d0b0a020d02 73
    0x4510040d00d9420035081008009205000c00c0e00408202409190380c0c0b901660001030900c2c0402c0e0070000b500e040480030350800c2c10100c114040d541c0010003000c461080004e5000d50240c29182e41c2c099104030802c0041030b521050041c02100142c1c410011101c0c803d0a1a0f070018500010100254800ba070002c0003040200f0001c0292000038001d66165040b00030080e0110710f080300004080301c0d16400b4203018032171180ca4880840d00c040001030065030f0000d8102c40c091a10000c01400340c101040c407403001540e1603011a50342126660080d001c2c0e644403001c54256a22a0421074100740314142c400100c505000c1c160450500c1844810300300202805403016814610001c00c8045021441e80d5000d0780c9058010004180b07a0303000d0700d1115611101d19075651120f400129124058002140103952a1042c00c400501056001da11118400e803940d80030040354031b0401400c807100302c0b0619009010003051100044903c60096441040990014200507215881d41304a8100104091082a02c = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 614364883 1250 614363633 614363641
    0x120a050402100f0206010e0606070b0a241505090409020904150e0d1215050307090e010b0f132703090311060415080615030a090b0105010e01020316050f030a020303 72
    0x1280d509500000340070f040454031200840d000940c0d0302c2e814490b4544405009000c00d0f140d507591000c8074185a002004601d1600344048044c0061a11000f243c017101c010090004105568941c40c0c030448240160b58540605d1600054880b9880009184d07482541c0ea003c0390010f80d20607034000d0050b806224000b601114600c0c541c001c40c0d024800407021a0b00c51902003030306942c001e46c000c00c40c0300c0e2204041003990400b911301200d41c045800940d810f01a0401c0494560480d03440760402c0007845009005840c0714000780400901e140e4091034100c8000ca400130750051a0f500041622903200c0da440c00c0320308a0b46c203020a40d00d0710800840004164000810512409038802c2c1074490046901c1443c0a00d801c81c01007949000481031001c1c088410002206651a840c03803e4902640705c54a03503680c90403440c03d0009002c003040440700c40501d80c0000c5001d5110b003804184143c81a002140780a02e62103143c00b001030b01c4d03002181e032442741c0b2102624400080c400342c40c0c0384541e50010346c0c490030 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 614366133 1250 614364883 614364889
    0x40e0a051506031b0c0a0b1609091406010c0c0b0a020a03080f090613260703030e01060b0306060d110c01021e0c060c0c010228090509011206050c120a050402 69
    0x44098078030441d014424070522010a5859000244610b00d1556817050708070307004d5003021074288000e01342100c040c0c02c21004003030b04981e0303c46c0b602031665001412501d503060f0604448040c4011810380d2450320004035154024580d003169240a6229412481d542d03403102049a840344800000507044140c1310010941c004800b150042e83e081c1801c261860407207101d541d071302001040704c042c01841404e002c0a0000346402c0d0454000d8403042621005800003c0d001e01c5c0c0d0055104a00091a040c549410350070184590b20075100d001800074074584078441080700c43d40100b26041c061030ba90360070550319420110001c20b05100c1030000981ca543c605811000300820000002510743c20030404501c07070481c0801c0b038551043c0c034801c4c0a601d803000b4254007070090280705562041e620300e0aaa000c0b07035124000c008503a0300003e6407180400c030785800520009070828850440b401e04204005800103980e500210703440101a039502e0b0810720f500c0751915021405a0b0465945c959810610003541 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 614367383 1250 614366133 614366161
    0xc090310060906091a0402090d052d010c230f22080f0a0f03091707090b040e0307080d1512020a1a0a0c11041a030606030a020307060c0305040e0a05 65
    0x40010a010000407a03500c0c8590451000b402551b0301c41d941c0081c55080c5940c800e0041203842d900f0004851491311800102d10340c400311131a801405144803500d0011140050042001c0108683d07116402a0b41e6028040d20841181181d43c0a8400900c40340090300700180141c405540c0b00c102c01b400004c80709400e02520703001508200e640340c002f034007015554030300041d104850903404041030602800905045507486d890b1340000380702c0c400302c0c88000503141c400110708044d6110094108112081a02044102c443c02c610032483c541051200b0808985c03a0f001400e03201c2180c1c0703004900e1026030006441a00c40f41c1e0400444020010801400d505007420014050040c8401d0070680420500c100851400341414120802a80084480c10000d411505800720180500240150055185a450b03002c01039098280a0300c0b8540000703c2c0b9150010310403281c9138000c0e000c0c2860b60704003282280c84a55000080e818094200300002e00d01c80c10380b080c54814111901d00042030305040d40c01c1c070032003 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 614368633 1250 614367383 614367389
    0xd0e0303060f090108070303081e07020f060610120509070b13080d0e06070803061809030a0215070c081b03070303061401030905100216062a021b04050c090310060906 73
    0x1e9680f46006005504000611030305882d0503082024035581d40300059842c07015880c840300b0a894106051002c090307000200031a6040041c000d4500d15603d00d0140310110312110f8a03040040c0030b0004080e000b0f100f5500c1184c0080403602541c0c441611001ea0b4400b692240b26003c1c1c6040300c03520100403c000c01d0180c060852100c0c5444040307104c0d5880003a40c42c0c006d85c40e0280841c00c0010104000da650380560401005401004554a282034052161207130403654410340540a02c03e0304034079050014400c1d621070f0045444854102c046500c0328000b9800040b00c0c0c1a11030f00051500c0c121400c100058a81c80b441b954001c15503d0a000c084e0240e0390300c07650001d0500d4140340c030100006001084c80548805441e1005884140d10540e9521091b02141c002d000c0038986100390440b0320000c2c101d9144001e911100c1400c1d00a039480807071795510460164024a10983c12300049440e0640016812681000700c49052802c094002810011035100c02c0b00d02a54402d0100000340903070003602e0003 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 614369883 1250 614368633 614368639
    0xd061205070e150103020c03090405041419020904060b010c0c0b031b090a0e13080c060109060b1201141809010606021608060624030901060305010b040c0c0b0c0d0e0303060f 76
    0x34500f00400c520300c00c0441e030b900d15030605401141b0701c007800c41c0400c00d581c000c1300003e00600c1113003068141040544160b004240c00c60083d20a42c04252441aa00040b5207a000c0c010805d90ba0b510345541c0c00030004187c0c0541005000010400400c0001200d0005420490519a40c034242100801050b80c0d03099074080b20a6024407503a9000d581c2c03151a50b044440d103100c250ad0325034801c43c00800106441000030300384500031032007044c280030000d00f15058503502003007081040d855800c0943c40740205040030f4020031110b8014005180c0380014025180c0014214030a1022602c44018201d081200c10850a039520790782040000d50400c0100e0140e0340c26008051103c0c06d0107004c0b91030306401040e090040d5003801c0d03086014050010410203400f06609013903101d0400900541c06000c0602c0241c40c0c540c03c0200d6441c20380350070700c03e501d51101e843d110700030007450079034843c414020010300c00e5943d0703071040c08000034003070b218010b0340c0103040034001646d50703442c4c960704001d05041112072242c0 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 614371133 1250 614369883 614369909
    0x712050a050606070f03140f1c0902060f0706060e070f14090102030a180305010903080106021002040b0702040e15011d1006080106140c07060804110d120507080d06120507 75
    0xe0b00d0b85460040380c85082d08062090b007100c03a941016500c0c41120700300b4140300080014810f00300c1000a01030805140d00356803480c0760b00c03807400b001c000b95041010b01a5004608104500701800f034200141200b40c400d000109625594414110580303038125000b001160841d044000c04991002c49188202171100034117050104c0b4900003580d900a103414081441310300000901610017030035800d40115803080c02804803a81d6031400038401102032242d54094454510b003a03503100d0b128001d031000c0d600c0381e240441c01c010080d020080030b4070000c4020403c03401200311600c80d14000c110800c2c00b802203c07100c218000000e2002e4101150014040c07540b10070100d00c140001030340b16070b4480c11900180383c03810403031814090500c002c1c4103000200c003071880303503407800920319400000c4c0030700c07682c083c81010748008086005d1003034007031050034001d1000046425003856540260098a54580251205410300d91100f414408031a43d607004000e041c20341c075681008100c0300f0030101003c0e050300341c0384072 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 614372383 1250 614371133 614371141
    0x8032706030415051312030b01170c0c1b03280b0f06240301031b090207060605011b02030606190e4b04140d080702070501090303020c091e0712050a05 66
    0x1b6892556550781d51003016100c0e064450b0503813184000f0351600440da052030303125040401e402042640041c40c080c0150240710a2860020b140040415010340041e018025910031080c03100100d03c0c50700c80700410034807546c004102280804c0810340c800d0f000d80c42203143c41c1c00c241040200d200d145025480a20000140321000852004280c0b0304403548211440400e00d9020310000800a50390498101c01d8800b243d01d905020705d0b0341100c801c803442a00c0306046144400841e40c00d80204080213174159000340041140d41c140704401407801081648620106a160002c0e144c5200d02500c1d007444e21000e00c4400c3c00c8400031410311211440e00c0003459040700c2e1942d84890712105508200c001d40d0800000003c0074082b003002141003940e0600705490018440302e1004e0408a010f54442c0c005105104020495500070074800003602d4050300244180d5405000304503860340024852402820380b01000711120301001030060041e029901e841418100c1c01400380c0841e500180410940342c108000d01c = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 614373633 1250 614372383 614372393
    0x2107111b011e03020906030f04060510081e01021e0d06050a0e010e040302030912160e0705340321050c18010e030d0908060c04080327060304150513 65
    0x31900c54080312032104441100c2400f540240150650690885000805c0110440c0c201e940c0b00c1c4264072440c13040055440741c0f41d10b00071a40940c000c0c00031301d80c0001c2e2a405203442d8061090032581c1c200340058039008400000c16201407040f0400c5648000100d443c9a034003065001d010003400055881040c1c991400a03241600141031107900c0648210714042403c1c54070910807995001d0340506200d0404612110b0940d0f00e03002031114400e80004bc00c008240364154030300490046950750398041c1014042401040440c40c8584405400003c0c2011901e9805007020b85840d50303070098403440300c0d021a16181c09001120f418844802714506020895044044002ea0705908944141d08080b194000010f994004040392081c1e4544110f00400c44410b5010000c2c03410b644040050750119151015025014002c9008040f1190028448011200c2e45065200c00d1910300740c0810013800a0310020070705603841524103880b4444c0818a15080b242d40e4028680c00100e40500240550301903111 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 614374883 1250 614373633 614373647
    0x10b03011a010c080d061413090b07181a031b04060503010902070303020705162d12021f1d01050313031407050304140108010e010f0306022107111b01 66
    0x200da4103000059503c181441030800035141d850815003c1005110780301c0418205002c00a24040e1207400b601d00b280790603c8480c0078428100354060f48105c41501d4540c4191505a4416803807a180458488005020921694528400011501c0c0c490340c0342480c141030310488040e1242c00120311070400042000c2544001103e0466082c0200161070340264501200a4440e820001e005881482071100c152180d06120340100c503c0d51500c00d00d00f8010b82d15103c11001039002d40318401524030010011824000e1980b829280700178042e205003010003000703104814030318041a0002d25540390f4000001814180400141c0f001d0034206c2c150328004981038201085072100401f0850030400820002c00030006450800740c0c01000d032500c69468519100e0003000138640b26000800603000010512901500b0364183d4a503031162144150840c0c90b10f03000707540890041e22168554200d003000c2c200450340000d010f03941d5550348222146c0160a040d240400d51084c180ca02c0c03250340b0350701c10182e0b08120 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 614376133 1250 614374883 614374931
    0x403050703030e041b030c0f170f070219030807020d111c051e0702130b090411010509040915050a0e0a20090106082208250213020c010b0301 62
    0x1906003c10a03c84001c03030050455008105203032a03d08401043e01905a0080c0100d561b1554600655941c40502105c06640402900004510a03804034410030b41218074940c0c401c005004a0305483c14803040104030741002e02094000907000030034007407120741c1405111001d50b17080c41c1040454445407001d54030340181001070021704c81c800480c1c46a85003d141030310003808a00032601070200d03074103441c11016400381400301e2244140004140c6400110300c00c1805605014041d0701a41e80c1d84d550301481c1a801100042c1441400d000c500d500703030740d40d01402811a00c500078541c1d00d2220180c00c0c405035200603110491031402d002001c01d041c0c00c0010070040e4507420100102c242031902800fa11032007031806e009604100d1500c008100181c010780100d014542c0da80142c840240c1c250741c11b0761003d030b403c500102a04020888401080401240f0704210080a603110007074a0705980010541350070b010203401c0c0700750007046842c40800280306014030140160000c0c000040c0354400c0c0c0301e50201d480 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 614377383 1250 614376133 614376137
    0xc03210519080702070f061110020712080c0c010501170105070801032118090207030f1106010e0606090d05010506030c030705060d110c01060305070510021609020f09130f11040305070303 82
    0x100000f003441d80f003040694001c2004a1103280240d84a0714018501d00c0003480301c010910401d05c0d0500c00d4011482240c1000c1d4115100e00a21a15481c0407649503102034001003500f142401815a006e500b1f1140380d008100303541110304002244d000741c60a69000604d140c1c2840045001000842c10b00040030b0502000d4840c800c400b55991041a580c2054034406510343d220003120200740c0c0180f03030b1b0041080030b0098982ea00603040825044910307140744c0d00303000321039008070004206244410103480d420101c001c00c17050824078540c0204030258400642521269104d03000c3c002c20381420320072030040752416400740c1049424100400d04178440e40c400700545030350341c420b0300032090111000c3d00c03400c411070b01c000c0c0a029520708265a503001a070180501c503090760407000b96403a0001545640354540c8aa0030380102e4030b000e50302002500b002042040d60002000643d1305580c481056605520111400042114200001c00211011110800c40d540e82c20041800030920010301e4504480d418 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 614378633 1250 614377383 614377397
    0x12010b0d0f092a0605090105070f141f0207050c060a0504030b1603060605090906010c06020405130603050c090c030f28020c0c030c06090103180c03210519 68
    0x103441100c01030040340064001646000540c07000c000b00c564851880a403034111101c0d000d02e908280e0314220909100b03010208a007005860180d50103100641040da024905d00310481d1015110011180d040000384511908904100c550000c0c082c0441d00200900b410304500741001c90784d6240d555000c07c4505807040300d000c203541207038030320074403c0740c014517403054901c07000d81000a10061090045202480802c7c00c200c00841c82c036125009460404030300400780d540e10b464400054481d5242c80ea03055504035020007001c95036882d25244a80841c0944000150403481e50510f1418091680889441014105c051050045000d41039903004030000c134080c110394030785000c2e40c81800030f4610168034191582e014621500b4036170f8040c09144450100350361401d0001d008158907120035181060703001900303100e00d40300c0354880c3d4071040e840c40140441c82402c200c103445042103220b16500490f0034600b0310ac1076480403c1c803c03e0041001c151420145d0419001c03a900740c0d45a403200720300000300144 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 614379883 1250 614378633 614378647
    0x303021c03150b0319090515070f0f080a060b03130606050a06020606210106060525021f1103030c0408070e0408040b1c0905010b010207080604050a03052209150b12010b 74
    0x4641159090281c45d84000c00003040c1600d40300c3d45948141110083c64614040011207560082203901c1c8a0300080d504c040c031030301c40c245060b038203040060900d800302e981c2c03003001040141c1d5420040d4052020f9640481508036030b1f2174500b05032001504100d001c0d00245004102c416000200150002801c42c0c40710500c0380305000303007200520031010040056080c0500000c0c190f41080041c403d0380c64800c00390380c804003504100080c0c1e1040a200a40024403502c510203084440d41d081e2402c41240e162500c490150704001c02e286801c140c039019412000001d040001c1d901c1000014010f2005816008261400340c40b0004503010b01e03c9400480d0600041d0315051006511a140000c54641070070414485542400d03802001110312660242c415880d012075107460019146101c0d81d8003000030021022a6075044502d900040e0140d20090300d1503089014110b40d4044020103000586030004400f103000c040700081d446c099000800c1044104619020812048207160540b901c5408150362000 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 614381133 1250 614379883 614379901
    0xb0916051f0f050d110a03140f0f070201140411030d080f0627040b010509070905130b0a050d060e011a030c090702030912010501030611162006040303021c03150b03 72
    0x2190140e1030104902d8440e0f41d000d00c005c2c840207010000d1b0296001c20503810380d14160404030700f0965201d02d807904481d00156010005001942d8045c0c030398400816642810706801c01ca507e02a0390841c0c1c00340c54000f00f11100e05040100e00010503203460600f0241c1841c2140c149030440c040e0641d40608020348110900480d80e420700340880c2d44a100054032031a160808502c0c1c0942030207454450700750740c0c001c160301c942f25204800903039400400c80304412994139155001844980c054940000081d0380000b1141d0b1290b00450701c039801000c0c00b20700c0941010b401800c540072504000b0700c1000f030202c1e60340d10340c0b00000d000e100c00c00240e84400d1103454440007645540104040c0550205044500d840d06d0319042d0080d40c100d034412035062100b00b03004d581c0b0407050302134a242c020841c0d5459403a00085910031b08604d080b41082c2c2071440d1481c2a00021034000e40c09a00140d0150340b01038a41d56681d00492400d960030880c41c6070400c5100e0304842a003200c00c010348a4076001c900040082440b401c = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 614382383 1250 614381133 614381137
    0x417030702070b0c0c1005090609131b02060403020c040501060504090e07080105090c0112020a2102090910240915020f0313031505011508040f0b0916051f0f05 70
    0x101005600d91303201ca0b01c00c0000c1e592182c43c4080d203806100340c07a0711a0b18190113802503d00405000f040142021020418440c1d031200768848810360341c0d10b03000500d5590115114945211005074007520306171500f0308020745005030f0140c0c0107000798909801040240c0d405010f5030b050792201d80011610607180f03580d09180c41995045404a946440244443c0741e400250340260a00e080e20303000101602000039004030b019485101d008181d1540e81e5440ca960310030030790b02c41a0041000141840d005030081070b80b6901c11624480c1c2d2341c610f07260a2000c883d9451030700d20800c240c048594001c140715040141406850300c18402081d5600b0243d0842c02d00074408400310012030b8003240c1d210001d07240c41c40484040c5100640f440e1925001c0e442e071041850007540c3c16030710040810340006010203802c8450300c4004105030343d80743c9401d041c40f00051203840700c240105040c0004005106200c201c4400c508080d61109101e101d040b011140c3e200400621146000c03980d091101001000c48000d85482c = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 614383633 1250 614382383 614382389
    0x1e050d0c020f0706080a0608070f0506161a010e0a2c0a02061207031107081207090b070501060f080c0109170c030703030302041404180209061f0503010815041703070207 74
    0x2e40155503011814079030100300240706241c1d4403024480c02e0354800b0074613269405405264480700d22168240100d0801310000e14000c860700001c045611500d80b02c0081c6492144c0040e000009403000401010484281454000481910030480c0d881c0750183e201100d03543d1603100d40104400a81c1d504422801c0c0550030266402900c156540d40542d0504a983d203022101000441e140c0380d9004400000b103000c0d43c040a0f80083c032286085400103071101250070003001c0d00f00300034217081d01240105e03d100107014114421030000c07800d80e0900d0200f0011943c59044141e07185d0107145514016a4810304d840c0031925413038001e8000003407180450b030403c0e480d90203264040c4103c9800000301541a8010701c100c0d00403544078502203c0b4103003004151441e002c41d04100e04044071320705002d464541901500080028034101032840d10380642d44052a52003d0b460200390084010040c9110500c80c00540c1c4181024203c50781c80d295940b103400005003401c0000c1400c0102c001545180200700301805 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 614384883 1250 614383633 614383663
    0x90606120f05010f06080d05130f1e05450f01080c06090d08030603011509060306060f030f2d060c0e0a0f06030e1509030304031e050d0c02 61
    0xc90105814000c0041100881c125031035841c00344003002d0a0800d12820081d5003042d80580101900303140104d803a50003906140341194075480e00002c1e0030101050b184020615a1181c240c44944001190010585984068050b00c100c24150f0361445001028850200a865040050f181c4d00a0f15441103a001c0c038900f45889400014000008000c0a5440c1240d2130711048030b000c01d0399070050107440d000701e41e4200d411052100c040d400103001c0f280559400403000e800007441050900540321100e106030311000c1110f58800003882408080d00071180906188005140c11502e9940c4094941c40c1d140000f41c5588080d40800c0107150100c0889111040040c2d00c16881400606000005100386001400450800e4104030710030300706a002481110010913240611501c0c26000f5000350241c070022140c140610345070740032030313030015280c15000354607200055880e4902840c01034403403d078104028045001034075003005040ccd44901101d402540310040411900c05548080e854084103024004c1 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 614386133 1250 614384883 614384909
    0x20c0a1109162a120305060a0929030c1005030717090714060d06092712031d010e07091107050c040906021b0109060c09030c0b210108010903020705040e030d090606 72
    0x390131a4550051405443d003194802d03100b65a030340c44070040703404030038048451404980d8400042c500242c210483c0d40d0b40075058071840d40d5003400003100400210450004a080030080c0304041754010604c82518140c0c0c0b604c5946030809044244d40d400e06480760402e04895001204800e03120041628040e200c2020700344111074a58000300d018001401e070340d103414805141842940d01300b034205800f443c7d030002415102c25044801c22070292104403040c0807c007c80024540805009100d98000c41040c0300103407520703a0030b010080c025298a0b00012b49005806c0c40604041b40000c031381c441c4090412030740015000c01503d4008007a014500faa02c007100204062041c0540d0103402c2a15070501c980d008200c08501040d043e14011941e010240c0300c2300e0064010b21507209000014030104405110802511001101c0784000744000d130000440e0340d44410a000415804001d20405803200b10340900c04540f54107140c0740d0701d004142c0c002e04d1042d142c1d410b200c14420f03103601c07000242c841c482840d0 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 614387383 1250 614386133 614386163
    0xc170304081b030d1109090f061512010e07020a051513140f0606040218040b13021902101a01050a11060112021e06040302060c01020c0a1109162a 64
    0x281e1283c21245821440d1170800e0000c001c002105012102120760003000c250180d2038000c034440c09200014941130304015280d02640300710f43c060014200b4440d820b2602003c56042c00010a56408050310601c259408140140700040c0c02140110b079401c21380136940110360354056a000500702c00c1502038100c1e1700c08003880385825808070344518003003d200c2c201e0f013042d1500c109000491007030001d41c0e40203004040d9064140d2619803c40200c1d140700800707268202c03011fa40c040080703038001e486070324420121400c07400a454044c8186d503019000c4080c01c00031050728010b901400c0441210032410014001000141c00380103e040b0304182a0000444000d587c41c0d81a00c1d42e42c9008103000e0748120008880b00300004140814501c40d044c0140000d42094a9039080c0b1502e0742045a030b044155409110000c0c07028001c20612540d280510045100700c0d0040051001c0380c500601907161141d0394030a401c16480d00319010f1040d4241004c4050811589400702d0f414003411032074003c2803103015900e00 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 614388489 1106 614387383 614387437
    0x1b0f0905300c1002120306041d060711070512030a050304020a030515060114130312030e101a0d0c290309060702010c0c17030408 57
    0x80d00c46441d0180d03a03a4001d03810007142079034030340c0705a07081c0c0390b146000440700320007503003500103401180b40b20300540c04a0312005100b0b90059856560b150440c03003d20000c16581085102901e2803070404603c020210091482c0b58209480760740008111171520468030b060109040c0000d40c0b818a0368401030340e06070401081039a00030036500b8008045030040c00310a2400d00787c00401c40c1d60703103050400074000740e040d803903e0801c40d0300601c004115241050360303640903650020605145d40da4a0300045000d00f418211103030302d030b001d0480b0f83c11500d40701d5080708406200c0040140e454142000c14015012a160f001801401c6050700400900d40009030110108921a250011000002e4021440c40d03200391290400c5922110400c148140d081c03040b202091b45d2840d050413460029151054586034040765403806000000c081000c00159008481c2d4a0001825400303440d4410841 = true := by decide +kernel

theorem cover : BRFrame.Cov 614208633 614388489 := by
  have h0 := BRFrame.cov_init 614208633
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614208633 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614208633 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614208633 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614208633 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614208633 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614208633 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614208633 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614208633 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614208633 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614208633 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614208633 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614208633 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614208633 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614208633 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614208633 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614208633 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614208633 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614208633 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614208633 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614208633 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614208633 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614208633 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614208633 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614208633 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614208633 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614208633 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614208633 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614208633 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614208633 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614208633 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614208633 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614208633 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614208633 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614208633 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614208633 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614208633 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614208633 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614208633 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614208633 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614208633 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614208633 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614208633 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614208633 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614208633 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614208633 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614208633 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614208633 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614208633 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614208633 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614208633 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614208633 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614208633 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614208633 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614208633 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614208633 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614208633 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614208633 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614208633 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614208633 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614208633 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614208633 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614208633 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614208633 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614208633 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614208633 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614208633 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614208633 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614208633 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614208633 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614208633 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614208633 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614208633 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614208633 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614208633 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614208633 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614208633 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614208633 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614208633 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614208633 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614208633 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614208633 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614208633 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614208633 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614208633 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614208633 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614208633 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614208633 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614208633 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614208633 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614208633 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614208633 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614208633 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614208633 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614208633 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614208633 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614208633 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614208633 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614208633 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614208633 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614208633 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614208633 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614208633 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614208633 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614208633 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614208633 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614208633 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614208633 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614208633 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614208633 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614208633 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614208633 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614208633 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614208633 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614208633 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614208633 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614208633 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614208633 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614208633 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614208633 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614208633 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614208633 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614208633 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614208633 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614208633 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614208633 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614208633 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614208633 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614208633 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614208633 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614208633 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614208633 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614208633 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614208633 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614208633 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614208633 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614208633 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614208633 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614208633 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614208633 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614208633 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614208633 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614208633 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614208633 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614208633 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 614208633 ≤ n) (h2 : n < 614388489) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
