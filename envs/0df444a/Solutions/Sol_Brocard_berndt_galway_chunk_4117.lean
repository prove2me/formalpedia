-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4117
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:37:09.47822+00:00
-- url     : https://prove2.me/submissions/5a8811ad-14cb-4583-b14d-b14ef344cf40

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 740287769 ≤ n < 740467625 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 740289019 1250 740287769 740287771
    0xc0406050a03120e04060905041511120c0909100e0603060112030c0507030b1f080313061b171804090b06010c0501090f030c0b0c09132f130e 62
    0x1000005400d1465031003e00c2d40d910700e0280001d00c443d565084a0300d56441c0700c2e0720300800d1440c20204031842d00f403402050340c0020700c0e02006000d2a10440f00d60302096281070f54015907a00104500c191984500b02640740240c1812590001c2c008041000c0d080c03041030032104541c03035440d44540380c0d107500080584821090280c010310a00c03501c2e00d4404644030f9956641c0c114040c0083d504099101e448000c501101110102c0b81800500c40703403000c18281381c0c0317020014105140514109101c030003641c0c5060220344529010407009004030262101c4800b070448281c1c0c0c0c4000c6400014601e0106190740d9006072510130408201020318920b20b0416001e821485584041403100596403000152041341741d0007002d03200b540d078495801c000980c1c103d445480582c081e440315800030882d03203041c81c1201c4004244581d008002c0c0f003043c0940c3c4454217408031a184003c0c02085e8007101c403210385070a41000d0041d440d0190100b1501245007000700003866013000c4050034011850b110201580b03890301c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 740290269 1250 740289019 740289029
    0xc110610140103091a07030e0c060403121110020a0c030912030206361501050d0506040b180139050714010605060f0301050126070815130e0c0406 64
    0x15402540700c440398401e0740b1041040c1c2c8541d41301d2800c00c0304660042040001200d40f200802e9032803080b55081e541c00c000074068148100d41d60303403405046640c0e9440d0101c503c1c0640003801401e0316802d1034510184442441c86102160440d240c81c00400020074420505e03500303a000c03032109a0082111121010208400780e00340c0c0042102e51101d40899115111003145680c0c4401e20324500d035003407070a021072110b032551341d2802402c00810040d4002490401a0300440c40b650070280860001040424540e600c140c000b41d110039980d0b02d00c1c3d4601010004009481e0300d0b54079080c08066100644d20f044020401616115000d44c0b01488150500501d61184000424000c0c0042c0001070000707890040150700e1040081000c0b5500c0b408200d00750805000c1c4655160080014015947e10250801c0080c01c8030a1001c03501002c80340b8840031a401500100800030380a0018480000031012401d080b20098207281c07040800b101948010030301c04a0381c801700e0182092132a903500d020300941e42610 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 740291519 1250 740290269 740290289
    0x90c0d0f020a0b03010b190909090302070513020301051003090203010225050106092007140102040303110114011406090a0b0d02041a19051c060b070b09060f160c02040c110610 77
    0x1601c846102d00c081410603400030104120307968086445609c0e800f61406046c4290018a0200d0a04042040d0840107100c0c0c00301203481400100a681d03204030041907007102071b003400180803019001103806403240d1254443e40c000c0c0008400904d0026018210002380901c000b00702d03481d2645507101c2607500d102036120800103070b8a841d8500c49034800c010405584915061020101071400090990300203910a4022070011843e540a0710028080c07002652144641d400083d07042501148268040c00c88180c0603003804030350010561a481b070824040d0414001c41d9031502e02c0b0300b10b1000a0341c0240201081201000250b000303680c0210f081e13071840b81c1c448614201c21040448200c0b1150001c0c0300ac3c400c4100c0c0d07a2641003a5503160703c01d2001601420144954840c03080c104042c210001411a41c295441242003051140d000041160011484159078209440103c8210340341110914041d5000389420112000d603604141581d000043c4402520595540e020701c03040c1c500100d1003080c0b916 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 740292769 1250 740291519 740291527
    0x50a0501141c050601060302250206030109110d060e07090806010e0105040903140f040608160804080a03020d050903030a05060607080712050d0f0c090902070f0b090c0d0f020a0b03010b 81
    0x10b2410784400701d00340e9054000310030724940c691512843c00c14213034001c601090780018004c000740304d00715200e2851030030b80465400e000483d030302040b4640b005119060010399070b0b44c50345440030303004001c640801305242014040e1548030000c0c000100401d0f90407001140401c0d0300011800c6005c100703141260110310900c1c41c40da1030b00081c00b002d04001030080b070401c8149a0303030007009065100a803012500d181c0105890314207044000d4200b090240501d80081c11501c40500300c02d6118110741d900c141d0051080f521040b80e118246c1c01b03070061540701d0070458105070802030b0400740080a140b103030001080500c03040e200c600611886120300310001c1e24194041001c0c10208020004040101c4400c0c6007241c03600701c5917801c110071121403000e041762041d224002c0c080000e5100d0740901c00345c1941e02e0114607010f81503440744000c0b03255041c000c014040d94000030b1800070082c0565140404040c000d031250002911300280c40c3c002401f0101d11401d00c24102141d09800c10781601d041c0c1e940c8000e03641c98 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 740294019 1250 740292769 740292809
    0x1107020907022b17010e0402040908130605070231090203150115030507031a040e1002030f070f0206040c062d0201060504180215280f03050a0501 64
    0x1480c40040001003944030700000c90754550070300458080410340c0302c0340990485402200c001c3c0000c00400c0f20310110354104c00103204070059601c2003034015504450015814845240c405c2c1103000b40d1240c0c1020950390340e030005170260004c000384420762084440c007042c10b0b0b00070409030010001d091600e102040200a02e4040794480d441101c14900003411503012000300000002d030400b007600401060f40e450340d43c0034255034140c09019003003000c90505106690754424200c4000240341003451042e40c071480e07a46291f0b5003d00121076503100b03c480540d40ca00c0c0210102600e10000ea69001c0040e4212801d500c010f4404a80340c1d000c1d41d030042d000202c191810b001103980034100f00c60014404142540000d041a94030040e600021350364001042051400c020041200c4240008180c01f01e106882d060059a070305030700606110469030195150101440c0d02200009080c001031400b0310b000c1c0f504408035400500d4880140407641c2c05100b41d85ea1031140c00d05482c028884c50348c200798801c0d0351201e = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 740295269 1250 740294019 740294029
    0xd1205161202040b0f0903010f0b0f01050d0204080d021f0204120b0405032b18020901060f110a030315090b0a05010e030f0a0b0412020304030b01051507050d020c0a09110702 76
    0x100c00c14100800741c10306880c0e40c10410f59900c540171600380410700041c0b41449040c28010000003942c48a0108030403040310011a00b0b22010082c1d00e4100a0005050000201e083c2d05030741c050700385917044070ba550b49814000784d0ba4a0b0846100703495690407011001c0409024001c85040d190580c603d0702c005444e070390316030340c104c03001074421111800180915244081e04e1007030094010880500c1100c0701d8076048120b0308540c132078403e213038000801c221454007581b12012200d0440300c3d2072a0803203003010680000c5071540369010f8023040901510710f4038802c1c03680c15004900d000440d04c0c45503070b0840e590280002128a070f182141d400c0000707100200860760151015802d1040c000d02a82c0b0b035202c40d50f511a0802c008000c0840f80148410f00307101c284004091401e01d0149540000c52401e421506d0b8015010414030445225001e0300104215251111064504090b031103412034580b410003001c003070344401e0b000c1086409203c40031000180d031229406510001a401c200c41490000c0d03540900c0 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 740296519 1250 740295269 740295287
    0x3011d0c041811070b1b04121202070510080a0f02040302010e0f0118180605060c070e2d060f010504060e011b17030a051003030807110f030c0d120516 66
    0x2096a500d03003e5244005541004021281c0705142c200514500250500741c4008040410010454140301c01c0c8005c04011040802c295006041c0c558540181c00c812441d00d110390300031541100311214540d549a07080f105103405070034031650502954105e070340043c00728021448042d000404944010b0941d00300480c1c00d421700801032402030407501d010310f18090540010750204a1820818040301900010340c0b041502412080f14000d01d80380c5100801c42c0d40310058092a05020440c07404201202e0b10301101001c6400c040c401d01d188071080080d80741c00e0074000c80d0180d00800d9100c0c105d09040d0320503411113080d203850382c07a08010b9034140c500440700c41c052030318411220401800110041668207001c80c44480c80088903030360f02e140c14280e120903198054080414030801c0d06092000942110325654003507598034141600c0540c5442903172614041d280e1400d2140000114803000d64004500003007560429201e01e40780a07480c00c44202124412240a81e401480e600d20b0300703807140314110ba0 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 740297769 1250 740296519 740296559
    0xe040507020c10090602060105030c1807020a050d091d190c090f030c1a190e0f040501170d050c0c012304080a020f030f070302040f0e010e0303011d0c04 67
    0x40b448420440d011903c80302850328802e0100d070040108000040d4100603840c01740405030007030721400101c00085184e0001c107441d80c111415002000840081c400c10031b4860307868003c0104c0e0820f582e083c8001e0701565180c0104504141b164507810055940a5001e600134110200503c500300c0c0c5103c4e0450041550314404070400090740c0b80013a60b0b0010210f003401540c000c02c544108a8034100c49198500c0c021040540da016081c44804592003559607641015150782c201240101d60030800107505c110b01c1c2140c29401440c000005c50000200c403829258424400122181c07222045002d40b518040c070308955030305510002e000c82e0654840c1c5480c2a81c02c9858405942d111021801440c90f90020b40107411a5408030b0860829807402500b4961b02070010707000360219503107040d50b090b150b101c02e01020707015540743c07510516441c0c442c2e03014003000c0120000030000030104c54949602c0340e0080c4035034111701152445880c0c0031149840c0d030070b0160750500b9401c0d01c0d061401203900340c0341e0400ca0138 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 740299019 1250 740297769 740297773
    0x150e0a020114090414090106081c02030a081b070b040b0c0c030306041104030f030f080606160b0c131d0718060c021801060f030c05091e15040e040b010e04030e04050702 74
    0x3507401505c0311403500400b110800451498180f0340b1291a05041160b16450303034500c40e054416994000c02150540440b41c540804150785001d041850522203901c01041e040b00001c0003402c0c0124122a2130150b0b21905100c084e544440c528001d0b0b074007401d8500300f02c580080011480d5441c160340080c00c0c9449006031035045c595030351107030801080f8060050300401d013403420124900782d200214a50100c01225010b080190f407181d40c07412000021700042c40d030202c50f004680410124130554500c0c1301c4848000c40c0640d2038074a01c000c07500450510701d610800401c04070b04007500483c0d04a050f400c014080c1420945061001c5a50310004d600590b0004140d0107500f1007810703440c00b4180603001c0c949443d00028034990000f0221280c181e8518200001030041c01040e03038079007051501030400b90085041c0309440700c0010b0750301120b00391030241d2084001f400140b12039516400340e104900581000d089030303070f03a0840e0b10203500007240d0003000100001c17240ca2081c80c1c55844903412000d80e04c1 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 740300269 1250 740299019 740299031
    0x1204020a05040509060a050f010f0303030b0d170432060a0c29060301051b0f120708040212030405010203190c051506030709060b0f0c19150e0a0201140904 68
    0x842c0c100e41d41a0342c0c08075180c0220701041240c82039801455004552160880390300e6140c8169205003848902008003015203c00e0b0f50030b0310b950340d011902c20b80c60b0081e160f4403202e0403c0e007810460f540144118056100700002d21140c1c481070240d001c4e1a4400e00e903422280015a200304061680041955010310070216050402f15a43e507004101c1100f8611003a160028454100119540e00070f081178030070380c1440f0400480d8480d480e103c0c40c2003055a1046c0f07480e10600c8190100c14000d03406400c28100b040c50030007090396030050704e42d80503034000d40b0710107071000750b11450a84a109501555000d68010005010f00030750301210000b10b04c810f03240144001c4202e94641d07003440075500d0024251111402031008905c6e0601044005168481081080030700e00f990074441c6000300614808140404282004d1400050084900c5601d00020000c668000f9140100c54481c1190101c102e1524003601450301180010b4202c003140c1e0140c4502291100004040d2200d5002e5060660841d4580e9 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 740301519 1250 740300269 740300279
    0x3210910020d0b3f2a0109050a03030e0f010302040302130912030e0705060a05280215060906090a0213091b020a02011403071e0e01231204020a 63
    0x7201500300000d00300808103103580c25400700701109074100540303401c0c0244a074210032004200011000e1462104204c98a200c80c02131480e410302c030b000c0c40c0324901c15800201220710b100c1c0421030780700c08030004d03210580c07002e80324800c0c810140040d0000401040c00c402e80d44045140c46064900b072114145070151030281c4a03808500544a11a02e0508803900c40d190982000781d41240c3c41400d11319488c0411100400f050074550711840f500c111406941d0005200004510070406c0b0350010b020703c1003180340c1c02d001145030707026481c61026000040c00313a006000320700b1080c403080c640100740050070030505844003400c102440c40003030701d0f00c21015801c121134080311540c0c44010f0018045548000b42c0d912a09440c1c4510760241643c1508541203881d2220040c0e8201e5901015401c441e9081354403561446030035100018038202c40764003c1c40b0320791400b180f154800580c4018820a80c1c43c0014422448410b4402c0011125640341203041800390007201e10010020342d602c140020050f03803440d80d0340d07 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 740302769 1250 740301519 740301521
    0x60213030c0308070b061f05070f0b0f040b0f010b0d0e100c030b011d06030c03090115030809030d080702060712090b10030b010602030c0c10030915020d0e03210910 72
    0x240d40121043e071400f054100501c840d020515038400c2040e01d01e1514503006c440511894180c1100d690300303000c0d020400105025109105289055014022140d5400d01205841c403181040703404484945045000401003183d00c4442412240441f1130207050a440d81c80801c00303080103080102283c030955549032417241da81c0c040e601c0c030075840762800100807090400040244a50740f090080221034200405007984481003146ea022513048555901c0782c4416407100d02404202c0c204203c0000503540200500845000622603640104d08403842034072510b50684926070203e45160158128030005968180100314a0410103011240092500d01341d644030089442e040d2140c00b111020030b41e044c0b0401480d01e00140c050300c0140011030400e074001d4415682d892680d008107002e10716500503249064043d400240d6000c0e030007071010f10244c00040c2910025040028102480703070030880b0b02072000c5808400c4802900603484a0308500c16910441005458090b0494070544a207840403013040000d = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 740304019 1250 740302769 740302793
    0x9071125050a14030c040216050a060b040f1a090c1e0415090f14120109121b02060403120e090907031106030f0a0515060705073006021303 61
    0x19109084103a8100424000591040e400030800c0303604440c2c00800c1c5582c0041c20500b40c9004460150f900c000c0c1e0044030f00304401309200185684541c1045030b040090395000120840b8096404014034180196000260382800c40e030416028800d0781040110300300421340d04e90015100c0c40e45031030210440103140f4516120040301c0c1140502180a11102031811100e81c80c40e060b501e44200d24a06024140d10000311510035005210244403e080440d00c482c4011405000345400800003518035091900030550b005803070600207011407141008800201c4c01d8540c4403900a0031090a142c216642d012903151460040d00521000313400300e15150303442d810850b2298804d5406800f800345185401c0018115251310640306044c28020001c00c1c43c02c1303590342da501c41428a40480d00e0344403412140031802c00022150b400c138400141200501400040110844101400513400440c140241074030410424408010300716a0202440c04268640c018100100b84074030844c6070b242c0d076540c61560000c0 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 740305269 1250 740304019 740304073
    0x40209040f110604030f0b01060804170d0605091e0c04270209090702070314030313030c0215040609030528421508030a0c050a02060705010e07060e090711 68
    0x10018810f03001f040103150107a8018042420712142c01d050540e250482d6001c0700f1003081d80302002041600400007243c10110041c2805482c108460034100b00d00c2d401595070361414540c0718940c10100e032854403540c0890301250010201a09a0440d0110038040511821408000207400340104403199a6805074140100706a8005042e40c51440c6003c40c013075030a14482c15080d4009100300003000b451154050307031f21645072400749d0b50144540f002550307040c5d20b0441c190340324002203408543c05800800c8402520301942c11280c0802090031400d001c03980c0308000c40407108a0415690001d100d103121a0380c2840c0011400750382c042000c0c1c2034000705554180010655101075507885100e02c540c41000905003c440d04004454108640990340c0e1080c94022402c05c00d070109200f060100c01d002040c01194000c0010340c0d6240b103420803a0282070301c85440c0190b0f01130030000007103840c000c001526410501400d4140c0d143d56442d01507982c040f00710211001da00400340d00007203414850440009c0c00c0 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 740306519 1250 740305269 740305283
    0x90a0e04021e0f0f010c150c110a02060a050f0d0c03020d0b0405060d023709141902250312050615040b0a0921050c09040209040f11060403 61
    0xc901401048600700e207840d6026a030800d4540e240d00c00351141d01c941c02851600fa5428800260300c00c004a490f000172000c058040c0d000e40c050117007039264070340105100a400d070780d442c8043d66005015644404078424000e60140d41080041e000c0b9015402030001c0c11420b10420f414024500f40b200160f840d8074a90784000b03980026494405c010300c1c460b0048062003901e040059181c030202080d109241444003903c502004e850301c00c1d01c02c42070007044a4407003540c21001203a00b001d80c0004400ca805000e4816920b0920620481601d082d200300d070b00c9901e450740081440d59402071040000e40c03000300c103150700e098010010424604020098800144a5a1407908030700f041c0501008a46003d04038a03c954200c82c0303400003428850f0b00342c82c159200d5500c0303990340b0348181c441600c20540c540d2140c180701801e0008540660b05188420000c5801101907c2010020b80e04201980304104c82c000d5204103600082000314804020345041544201b00003103503985103100140c80d681190348122444 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 740307769 1250 740306519 740306521
    0x302040f05150403020a0906180209031e160b120919080703120908090316050f12161706070206040201090e070c0602031501020f060402030303040219050406090e010c0c02010f030f02090a0e 83
    0x2a49c40b044821080b0011800c1142406580307400651101c11040642e2504000812032101c598400d00c480703134522000e071a125807200d42c2d800d1500025004445500081c0010f00002007507104042611340000f60074451000c00058941d480b01c1c25504180801d80800c5800d88800071105034622540300c290b80100d100c03d807590040c00406140848501090040d1500000100265290321022042c9140c08407410145c1000300c00041b45070015461113020365002200c400100c921304450000000d4082c1c4044d82c1c21551020780903030740d0380b005803402400541500710411100b03041541c0306800980a1a0028041181d51140c00a0303170402c1d1a144021207420090150540e010054104841d02d03070350142c001c925098000907124040200040d014250044600311440c2d11132100e070b405800010410810b00c2e85460403c401045a2071403d01c0700c2d840d085001284a000d802c1ca00a2198140c0d903000b62031509020890141191501010f0225000e00119807140c0c0c94a48003800751200c031541c0041 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 740309019 1250 740307769 740307779
    0x706020f1803011d070b22060f0807021b27010602010e0114040f0f0807170a0e0603161d1201090203120c0a2301150e06010302040f05150403020a0906 66
    0xb1911011684c181548443c8041240d0329808100517013101e88021040380c55803041c0c402030503080c0501c070b80c8860742052440049007654010455100c0701c415a0303a070a200d581d895105907035030090304080718a400da801c0e1103c8402d00d040072040542034a056280b4031180e0000c00807039050182a0001d00142c0d468858001240409116118207440140203c1a0034141915402c1d0214a103a2000d02a04029041d40b02400300001c04c81c1c090542c00303000081d44400b00b0305400515007142c141000021010b06480c07100703140003002e5901440404035201c40c401920074003038a2250f01d582042c0c9000005043e40f00c50765444200e001e8401402d8800401c0040b1030340304141c1466007452805066910034005641c650400280810074540c3c0160002090140f900c000038108200480104031503003400009285200303490b1120003103c070004107001803901c8a800640c1039000328050040084450700c400c00443c5070146051240720740c400c6606107001e80300d401041c3c0c6c101c65a042490f07800d84494003005 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 740310269 1250 740309019 740309021
    0x6090c0315060b032202030304170d050a02031b33060102030309100906110328020f070204050606310911070b040303061e05040e01051006050706020f180301 69
    0xa11003244a00400005040802c0c0700740c04c0c00701812110165000d050302e80c403266482010492119001800c0702e840d6941c442407070011106c2c0010180300d90084040f00314100d130181058038903145460700a035080102050b82d2100d954810145202d0512441070480b034030780400120241d003429410303a1a0043d203048040d0400b08000507011604660082007000102c1384085055503442141c62000300300c007070160800b003028010840e1040d00f81440001400f42e4060441d44244a82100c821000702e00c0701141e140c0012806180380400d0210020040440185440d07482154050b0300107010508200c2c444034038061230354006041c0c0b2864250320070a0180c10358003440c82001002040303002c0c409208075002e401980d0081440090202203e44049000c140c042d40000000d041d60190506489810940901c50540c2a00c00d00c3c0c0140d1902022822a038010700402e40705d2a1450a9009030f946054011070b4203a1202e8820f41d140c40d428031000a40102560040a08080200b443d10000300030004140c = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 740311519 1250 740310269 740310293
    0x20d0b0a0b12070e04290c1c0c090b21070f091403030a08070c050a0c1802070503030105010f02190515090a030e060a1101090f03230910090306090c03 66
    0x82203988800b80070000403403504e907203503405940184410380c41e18504c081011020460141c08851039084030801444810f00307009400d00c0ca0311021440440c0c145018040700f00c8a082048000050110300288103c44200c40140700d4114060784019441240450946187d031041e5010300018688410703000d80c8a622007a00c20160600740250840c50b00848002607a138441c50700003078140440c90700092512030140404104440e00a020350740140e8076072410040130100360240b00d4401c03528094880480010b031003039940c600d911000452659090030015200c002c207030920642107100d030001900308480140810b1a811744520000d101011400c0040ca0f0180360040011419501904c81103011a51102007203503120019038403d07507074400402c811100e0318094a102940c640c2804001403c00ca002071400e130308c10b4060f81c3c50303041160010301d8414003202c0c0c00c45003401c010f500b030002e41600d181161003079a4407184c42c1806908150b485d0307241c500380c5412910580781c0201e0218200144071106d0554 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 740312769 1250 740311519 740311549
    0x1020d2f0304110d080a0206160c030e0d0507030f0c080d050306010c030309020a0b0708040503070f1208031f060503071202130311030a050114070f02030421020d0b0a0b 74
    0x411203441440300d9002140402440075001c49078001c0c0d80507a50700d80d03600340c81c8030342c1d0072111296540325001c0307000e96558000e85402058241e044107030003480d4070901c4180300413503140d40d0348400c5088175000c20204119107032003680c2501410380d0000010f0b06491807590b042d4414200d13000b9252804200c02c1c28000c070448903102f803101c00c10401060340c1e8840404018164141000202c3c3c040e94000b20310b035000c039504a8562900b002544005002045c4041d0045900440403140055200c5090b6081c4005c107100c2d2000d414500c1c402c0f1000101c01034090b590011082000350104292000c0c2070b031002c1203030f07072204010903c000f0a01807002d5002003403601c1c50481c1c450551601040c05e44404200300039102c090b10504a810940c80c140d60140202c0352001e40090003400301340c08041d418401c50f1000d5852001103609049128116030010065401303d800550a011661103240005881c0354840034089911001c550942e00005011480090107450104000240d860100051081e2040c1c0700c415 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 740314019 1250 740312769 740312831
    0x120f020102090a120f0203061005040b0303090306190216121205010b03070e121b100306030b0c0d15090c1b05030403030f02071502060406111e0c03070501020d 70
    0x840061511070484480407034039504000c3e00319030040e00b0f1030b1795403c8024000035458010311090140308903214440740140c41c021601041000d140710200740d940e100750b04146405401c00000a40c1e55059154404800c0c19a1310000d86049604980713400c03131f83c6090303104035110120b809680402660102091030512200c402c2009107506002c40c209036400003e00145c1009024044405107845680703062001c55444000c40d09044500b604c890801d1100d0002c6500604183c29040c4842e03119001d0311089940100d0b00803080d40b1081c0c8030310360a5000000500803d5190f40300208620740170080f0300010440c08000007001c006c40c0c907000f026210103800e074407400c40700c2ca02c1d1000858000310032a1b048030f5042c01d280c1c032651712041042e4104007031507210300014102103103c01d5031141c01085592050384184000c0100d0211044502c2090041520980104509019451201d8130302802072512415410440381405102d595960076030340401d0355a0850703901d0b00005200d4082d00308c0301103611950110 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 740315269 1250 740314019 740314027
    0x30304060b06361512071b0605042a0e010f0b1207090b0403141606080f0c0c0708100b061c021c050a0b0a060e03031c0f09120f020102 59
    0x150300000f1040d06500800850000155440a103003201c0421980b4406030580c0c50001c45030506084503002201075018000c3e04030002003413a40710303400c0c800c09112500b00003507400300e540d140c0b03600808000700101d81c00f61002c2410801d06103818840b4840310303000c03102e0420050038440c00300d50070181a0701400c507843d41c2081c180070024081d001e540040c80c6181452200396100c0074200e4420500303610403010400c0000303011090200318410f0712642c119001c1240c0000d101c14410300c1e0081c002d40b00d6540003441c6100407031b688489640d0915002501680414182001b00340490b06005007075002407034580c03000c00c64280260380e0f402114009001181c1c9181402e00340f0f0b50070351089060307203541b540e09a4005041f50400303159110000d8020320300e9a080107945003500c941c0000300324248065105803500d03070b0006101880703010384c2550310401801031170400c0c80c03102c00c5964820405882102c103039190760824000f90502d00c1100b8041d401401e0700c4040d004c0c00782020b44452a864800421640100 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 740316519 1250 740315269 740315287
    0x6032e0810180204020a12060e13060507020a021c0314070305120901020408060f0403171015121a01080f010e2e0f080f03030f0a020307180602030304060b06 69
    0x1048400504102080109078403901c00c00b0107030348001d1214020743c1300e4804035400300b106520030740310240c044500c50108401e41d01c1321000020746408070340f6036640c1000742034814001441c0381c00140c1c000586004403400c0c2c0321242c0c000b400304d522040d030020710503100345015014035900a980c01103944c100d00c0d5851901c0c0e65618014401d115250032168400484c4001c904810800d50443d4010304080307040e60985c1c20900300150203218203a44c00e50002d9900a65100b11034807440a06000b0620010181640c514003803c8000164080d5101018001703220030025007420340c0e00480445e038005100140705031002500150500602404a0225902c403c006001c2d01c641c2580a40c1c10481080c4070400c41c20010400d05480c0c00d40c0c145040c4481e0784581d000401810b242c2c00d8009603101001501e02090741c0207100c9580e80411580e800c035174003050010520307565880d8001d640140440c42c204241400741c0140b003212080590000006910004c01c10080c0680d81c4070f5807900070421a05180707054001 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 740317769 1250 740316519 740316523
    0x5210c0a0209040c03120305101e031104090c0b1b0a050c060d110a0906090503030a020309060918010e101202061e0d1d10090b040b0a060506032e08 65
    0x380300090055000c00003003002d2003c8000d103e801964400a0301e507000485000041c080d02090f00c1101d020204408040f50640c441c1c2c44070a00105195140144680381d51540d400400d1415491030f042690360301800007090f103818460001d041c2d00d9200d41d076912465020101034081c0c0100c4100541c018691950006002280c00414804c1c11240180c0380d0301a901c07543c00502034180b10340b991100c00140c20700c8854001324100201d59041d22014070447d0b0f640e0525889210310180e0000503002000719441034075201029007140071001d0415901c03040325a5941242c80400e8209081e5510090100400e84151500040c090010403503c082e9016169000ca40da41c001d03900b06010f0100031a204043c1c003103281040c0d4003800d51441c800c3c45108940720a0b10750801c030003040d05007d40195280c1c01c0c0450b000b8010b003107485600000e10007103507803161221a5614409040054040d0b280e0b0710024695440b00c010314003488030b44d4030301010954294030841240f02c0010262480311034a48041043c0800 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 740319019 1250 740317769 740317783
    0x4090b031b06070609030315031208091f02030c0d06081e010b010503190f060b0c060a0b0d12020f0d09050f0a030b1306110a020307120806030705010f12050405210c 72
    0x112a0000c64445d4681ca0254094044d40320009480400c03c80c00105001c80c40e5440c03113100c101502c80070f07550f440d6150003c0d01c8000403070f14440c1c046960f03c05100b08490030781c001c43d4045400b41915041980c0030034000c0690700d0b5640f000d080c40e80100680001c10075101c1c50041003000e0700008101d2100c0e140000b0781103020042001907006041090403e200405030806032495a4000302000004d03202c1f010320605400501c3d803690540318040025111030400d01c1b13041c00c058401807441040c1021542c0c2c0f905058001800c0c14114001c0e041c00c5048450100000b0040d1891a00c03039511890408085c0030000c40740420241c8608004034080000c41c5003c46d0240d00080701b070081d0303101003280f801c1403006080040c547d245810800141d064400380c1c044041c0c95241d22a0070003181c440b030ba4140485a400c4213070740d050b0b07240e004030740100699070282041003107107070301403d21060b2099841c80c18001c80c0c0c0c00712420b0340c240c0c0240c1400f41c01e6243c031107402401d80120140300c0c0d04105880100a6031021 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 740320269 1250 740319019 740319023
    0xc070302010c02010e10020f011d07030206090114030c183304031415131e1a10080d090b07080a021515030105060a05030a200604090b031b0607 63
    0x280740740c0442564802d01242d40101405400d5894004d10700348000d40d1690741608e40501540717065050b00202c02d641841003284009940102107003030030b580030803210303904c005041818015090f400440144503813010714402e40401482c1038440d0482031112500085030301440784a26110700c401500d812040c50f2400412185a81100880c502412555203d104682000d40f6003c0b4102c0c504032483c40c001940e82d0786162000042050b0f1320390031005d001c84443d62100806010148000a041d012410190f0010f54090780c0c442d83d4112080c2407010040006648c07441034102c4a40c030500ca0240c0402c20b14007446c28503c0c00c05401031601032155907602400c0303001400c106000424458131442007100d0702104000480d800d102e41080e44100c3d4a205401000360f00075420040051000e00c0c2504400e8116070300540540078045481d075481c1c1f51900c441e501d01114408080010683c5d807a0000540040e120f28540020703100c1d8094100b41c40c0042020004142c600d8500511680791141e43c01c3c2d40f4525 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 740321519 1250 740320269 740320277
    0x406060509010f2601060f0e01170601051008090703020a0311010807050307090b07060603051609061401050f0a03063602041a070f0614070338060f1911030c07030201 73
    0x700004500c80c0c0904041d031f11080099050301400f11740740d2014010241255880014003440c81401450b0700e40b2a4024411617030b22003139a003503803071443e40114620380c0d11014600607507045035203941c0010801061500280c80182041c400d80000d96080030034070350852080e091140c11071403c10b400900c028214040c2400c010404601c0d40c040006030740000019540c000700b500c0c0d0507151104180d040c10128412100e901f42000c0780002c691040c0c100a070134001041e540c640c130380044a16194043d0340414010010143c0e1107400199820a4220b021024040000c0c5108100c201010710b100f0110052103c60394144104000c002c0e940d08000c0c1071000700d400614458540c0c0d000e00b01069810081c04000c0c04403401c001f4259007407200c4012042c41010540c8040248000d01c071b42c0d6801000340300140107c49524600944401c04150604d030300b10b850014811860031140c40d62508040d0450400303181501c0d039031111194010340000b89070070000b5907500298108060f110015507950680e2102034140 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 740322769 1250 740321519 740321579
    0xc051b0a050d0f181202032103010614160b0a060801110904050919030203040312051e03130204090c0806061801090518011a100c080301030b0a140406060509010f 71
    0x1860150904c51200c03014081315810580d81d400030b000c03070b45040d994100d1007030042016a070010205100003102c40f241004840c0c0c01d60b8203000c800d1754038812100111800000070f01520000c5445142900c86981c0701d8040703042e207810455a0203041d282150030401050741000c82e040c20304240d141c1924002e21044801281c0c945039000ba013402c0117899200d20340c804266103112028140c00200410031680b08001d44400b06011f07140c01c0b107090280c0500c0003e104c0d03065075082c0e5842d031000e0165070021120081841180d6050380010100d0b50308000484001c5440941080f00d0f00c020b102e1641d104805031190213111400c0d4080390302e21081409092005552040070030a031a06034000720101d00c21070320081051a8241c041200f96601500481d441400c00f0359000342194494450805825400440c1030f05503429035a902e4400b0400901d50500ca030b654102d0b0066143e4501020341c09240910400134110341014144080614140c000e000300e123034000d07800c21118070048408401c0886944083c148 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 740324019 1250 740322769 740322797
    0x6090228051e041802180d063209190b0703090c0603140a060b0d20031e010509250908030f0909061c02010f050c010c051b0a050d 57
    0x725004003108001049090303040c0c0004003a00100a10595686040c107495030b030050501441a841810401b0b0b00c2071807010710300180390403d407071649603180c8285004104404c0c400c442e5100c094420140200b400c43c40310a00c4040e11240c1001034200140c1c8014043c07100810080d641080c03101400180143e0080c80000c5c000381c80780c0c0c09806845c1d48580800c04040d940d40c002006048900c0f102c86800d00201c011500d0340c00c1c644502d404440600ca003c03030900d86065101c00040100442801101c96040150038848101034025440b800700e07800c1e03062108246001000342440c051308a103014104c03076800d00007810114503070440748030074850b154240861807100c1114048420740c0103000620001c02d05c2c11100300d10501400d450b00d41920710010658a21003088500310700051742e0740a01144045031009035107c0d2090445546240c02c0c050310b041300c0e4844890856400181d200300003440459520400800b0340751415845c0c1c280002003480d41980e4031085c0d2146c1c90302c0e030440f0601c40c000002d81c80b = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 740325269 1250 740324019 740324027
    0x10c05071b0f0b030f250c050102120109021b010203060604031e060f0e160506030412091d0a0c0804151e151e0602061513020c1006090228 61
    0x102500b56000d21000c155601d80c0030308001e8200352010080f5100590002e940e4080f41c0c0040741c0c80005141d041d010541041c8030540741000225070a803255502000002c44a045905042d40203240198006942d0450b800060010004145548000741d00410901c4000c1c3c1d903e42c281c4043c2c907000320300c05080070040036402d40c0681c03401d4002003086042070628a482a9280d00541000d11948240c3d410032400942d074081030b8480340035043d4003000501c0420040340141941d07020307810641c00c0034071f402a1510601d90a486a082e244140403102c4010004406064014400b0303500d02d46c1020b0096040542c0c90040a08034009820341075a40d4040c00d8507101602c805050586544500070007258180307041c00483d943c854000c009054015881400c4003a12803400ccc1d40c200c03101035001d012651104450a40c1d46000c0910300360f405901d01102c1c00c8070b12554402030840d080040028031425207080c5451095a207164469a000c0f4414448c3c190040d1a400c10010203003504403960820b1000c140c0192 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 740326519 1250 740325269 740325323
    0x14010302090d0317090a030c12030b0a0b030910090210030b0a0504110702030105060306040308041101051e030a0e01060b0f0f0f1c2f0a030906020c011d010c0507 71
    0x41d601400d44000c1800341900081e841803040040e9a841306150340e0f01403142e0f03842000650060002e0b242000190100c2c140130030780c841d1505079180104a504c240800a21006229042506901c0c800400d1150756907080043c90030f80342d15107100344583c25064000070071840040aa200606441d0300200b01aa9145220800074201c001c1c4204209440d01032125400d030042c1c08124000d601c2c040214401d80340005605204a9260343c0b011115038031943c03008a21600084c2a5050000910521920300d1041c00403801c0b4802c164051a101d01c2c006a0f41e800380d50a588002d5001e915002041c403411100000b102c0301031409001280c0e5458903621f04400500c40c04600a922180c04104940c60000c0315680e001c0c0b160721284288101c0610240c0540c0280b0074501c0182116907446103000021804000f07001030303041500700050259000d8442000b42c0e8840e0902c00e665940d1218101100c0403016044400f0400c00d4008203d07202040c40054043d00c6440f801030110200d00c00310309400031030311480d8 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 740327769 1250 740326519 740326537
    0x70c02210c0a09060e010905100302060d0b031005040605070e10030c0c021008010e010e0c2703070f08151605070819090e2404020c071e090e0d050414010302 69
    0x6081c82c0d50300d0306032000400b040d0180c49504812a4000100301c0540c4c01164041c4843d004c49440c1e040c90355003040520380c40020b9140c000c5403100600c0102d540c00b44006800301740c0d10040441c2034541840c1420840303030000d200724180900c1e01308146aa8490a40b05900d143c840e0034002141c1c2540e21054400340680b00b4025803060b241b0360400c00440c6d018600c28100d800481c281c1703109076261100440e1b000d40c221100400c08401b0710408003002c8903002c140e12020800c480c02e403004203020000c2400c040c040e410130b003c41e20070802c1c1000981130404c10345c00c0c9816010142030340c41c00e1400e00045c400e0342031030014041140214000c03081c4004a400c64804c079040142c031040051035a20068014944c40c45117540302300d00703480000c217002c0c840312400c3c0f21844c0118401d480042c00c003007004005c0d000325003803403030742c0c45001c1c000b046121020603001c0c841202c80d403050480320b02e0900000141c422084030200141c0180c44418201504007081d01e00f61510741d81d90441c19014000104e00902400c811 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 740329019 1250 740327769 740327779
    0x305070308070506091f0b0a0902070c05130e06060907090b03070306150e010503040210140403050109050f010204060842040c0302041d0a0603080705060906070c02210c 74
    0x10410000c1c8004241c0349200d01d05a6020303903120030f801c1e500c950320280c519002c8031441002c01c03018800ea5100860035139004045225035501e60304610121b800003c0e00312808802110103002502e003108143c0c0e000081d00c0000e0000c502c0100501c0e0304c802000d0300c940d005801000120b04a2401183c000c00a0052156030070b45a25100710700402420081c030410924501558421165500c52644543c081806845052071510b0300c1e4207004102043e00320960402407051408409181182c0080000714058800454600000d040c881e00f800890b600c10001c581c030400c030030822640c2168909520a50451107071010402841f4040c3c1142c4951000c0e101e0908100480c1c1510945a0b03540f5102030015941001886180c40701501240304034051546c910440510729000d03149070104003540041e50359804138486a4075a01e0700300b2600100421181c6400000400c40c0540c020401c940e804011807410b0800d912554020903842082080181d003100290f14403008010000c01001c4416140545 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 740330269 1250 740329019 740329033
    0x10b130902040e39061206121902040b0a03020f121c090e100e06040f020906070f031b0b240a080d02014b0c080f0c07030f0f03060305 59
    0x44200b40820501c0304e0161400e030f00d0035909014162401c994100c0c1e07030000d000189007840301e4854460b103080c0200460392040110511044048050051078451110b1000b010322942c0305104100940e041c0b88055801944505420000340e52041250300c00d80b241594411901d0030400f0340700f81401403424403550707218071103203c2c1c60307a850b804034060003211040090382c8001d40391040031032500ca10074403407240d592400f800425203902d099803029a000480751030040c0303064240004240c031500100c0e02605e080c600142e094080c580c201c81c0509001e200104042d488100307070f5803244607042d80079080306036911010310001d0385011904811a40b1450080801c086159945411581d60b40e11a4207100194200101c00d0744c9003000703680b05200769441c194150702103070502c9219094101c001d92540e44981950b03080f40310081c102e204840440d40c5a9940d03054524091440e60301d003c2010f01001f103807280400c14440840d83c00300f4022403000380c52030070701e13030140304000128090a8550806441e80c02400 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 740331519 1250 740330269 740330293
    0x40f030b0105010906030b010215070c060515010e03070810110d050f070e0105070201170408210901060b0f091509040e0a060b0f030717280c08010b130902040e 70
    0x2403201d0403030320701340c0e40c81c90300c00c0e2120011429030fa44a4401405607115036240319000c03802000d8142d02c14640c0ca0b001d07115840c0c944401e000e544041d00c1d0500140e16841944915503400342000c4102c0905800a148807881c181040d503030784410f030310700051866455690856a100c00003c40d1300d0b00311440741c1400030b82031621120032413070000c2d201d003004143c07070000d5030300c0c1c550081c0c00f601c000c103805840341c13903075007182c00c01e01120303884024801c940d090801c00c203e0511108103104c4d171014503c1807026000310314260f00c0c078030300315402034000d8407080805000c6540a8200501100c4d085481900d403100c180300c032140c10b01d6007400343e41e0040754400e09044281610310000240e983d2101e001d800e050000400c07850070700c13034061200d07400b194043d0000d1304103001c06000520040f04d60325100b41141d811901440703420030105c064018000e16525455020310600c24078041c0e100c050001e0704c00810902d00010b002600004242c041c1504151300c0c1c481120540d51a540101d42c1c2000d80030680e6141c0e0814 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 740332769 1250 740331519 740331533
    0x270a1a06040b0a2601020f0403050d0906090b09010c052806060515040b1602041401051e03031602030a0b04031106010b0a0c02040f1812090e1b070503040f03 69
    0x454600d40114500b0b121054203141a2140f00202c8502000411160800d420226594030500741d003e84550740030004120f601d8503c1d40200020750041010705100918460020604081a84400700f0021010000d000380005401107980b0200d090900c903000002c0761403c5400c2c003c8240c513855580c04c0c0f1411241405100c410f0601f03081c0d01c600010000c2079181c800300306403078a03010030030b80380c940b0f00f0700c8107010301c041c543c00404d02e41c409c0e14628020403d450740014103031220b1080c8242440751f4400100018240200c07500b442d64405030322044400e10100102e0356a001d10007030800d10140b254800e805544090164851460300040c40700031a1401d828040c00302c8000c41c0b0420000e03c680800042d4090064054980c1640c0d5941c900c54059426020040a1b101150a0300000c0d03645541404010f0001900813a40601c0f44224440c114000d0b00050304a04050b841075103040811303002c000b20203100109180e8211054031805d41c940c150303820b219186020316084500044c0010700d011041c0054 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 740334019 1250 740332769 740332771
    0x3091a0a060614160f02010c0501062709030f080703060803040b0712020304080a030c021518030c030c010c060203041e0c05090705040e04020904053c06270a1a 70
    0x81c54a400d43c80d584180c03d40b0a0341d1140780e80c00c141c1601a0180400005c440440c00e019640c0145043c0410044689070380d0300f144c607960300c8083c07100400071040019001700b4600402a800c0000c0c200700f6140103031800340c00d0940480ea044200320303078a000a40094000c0e441400500340340700c2281d0711141c540c107146280c0d6028a81c00d860668500f888035101c40d01c00001c442c1550085005004900da49540903643c0301c0c05141d049a02a000c581c840240f030403000080c0c820a142172010700c000309603110505052a10051040707000e60400454005180d80150142c1e0304154441c10050703480c2c1d201e04220076416042003200c94406591560007040c03001c81c2a0503415100100e414a01a446652080c4c503d0701c903610030f8910700e044a0300010007500d040d14000c3e070300c0741c0a10291105402074041c01360310320702290401200500c0f0f510608909071007443c0b0103000001c070607008001c00c0c1400798036402c00005100c0a2040780c4038001c5000320b511010710440ca920b0380d221583c3c440314030300d81404540401e4 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 740335269 1250 740334019 740334029
    0x708102301051c0902130510090c02031b1b0603090a0305160609052103010e010501030c020a08030a021c0207020906270a1a04110a030b03120d0605090106020c090703091a0a06 77
    0x2c0080c100e9071002c03500b41f140380e0140030400c140096481c034109040e030140c503052401c003007540801d1214081001c820b03508420b484036403602410341411600c099413182200441c10b035024810510801090b9030001600c680380641504007070340c6800d285465000d0003922103200503e042e040010380d0342000f1300010a4001c0e060806071501c0726915000303107000580424424481011341c01001040194029030004110800138815104c4804960701d4114450740299181c03881d40344c1c00542a80e4202e044070744141e8008084205518140331900000c88051000e051580308000040070340d44001c0744018008621b40014508542501d00b44d0001001480341c140e1841d00c0000740c60b5100113a00d80352081e40d5081c80c054a030315003000c4400e60120020000c0c21350041e011300c00c403060261180c65000103480302c031200060104206040c0001c1c80004101030703004005540c0034400c1c00b100c95a03102000740c1d01018901d07002032030890a00301110101032103100030b0140031045040c04a41e02c103941100d0300b0380d0 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 740336519 1250 740335269 740335279
    0x80703061b05030907030f081905031014030703032a08251a0a02040f08030d29150741070b0306040e070902030708102301051c0902 58
    0xc0c1c030010090740c0b1440308845154442d000307641e0620009201040c05901c9501503c0620300704030038064040341d824840d001e10130100b030020082041c4201c407801280040c2410031704010807101da850201303540f540c090100078103020540e0b550f9102018504900c0546928581082e8800e1000d070800982ca0350010280034a001c1c0c540b010043c00071340c90000c1c540c0307042d03200b180028001f28003d00c078102d401c80070300a03500c01a002c01000520b910300c14094805410690301640c2c0c4d8485840001e01180c0c901120195940700b00d1440070a0341d4203e001c22102624160b802080c610a5a0000c00b0309100e0188000c00c101c10100c14200340050302124000c0c84900c480107040850300c8584170310781200d0040010001035015134014001031070790b44040c3d6084070b005403000c03403a0401d05180a04002007504280c8a09070f003c800c0082c01a031140880e5044a60349020f407030118140002c1c8030703c1c1000d03002c09010850030310090810380d922039412a40662052704400d062640034030962000341030000000d910034 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 740337769 1250 740336519 740336561
    0x121110030b01031d030742060611070303180902030f04020a060809030702190f06020f010b0915090912030901090c0503011a150705100e0d0c05060105061308070306 72
    0x14071010609007000d61000801542005029070340d8041c604044a51400b070507c5c50b1907040c02100b069040d6100b92607140d013130310700344507400f44024044600c550b00c400d08128141c8517040c040f05010070300000b5a070b010318203844400340800c6c940c498442a0b600c03021a25100004100c425025000300c0390165108990004020b56100002c880c98182640c0400a5070401c1020341c00500e1300c00803a003001d0550722121010709507113000c0e040f2541c00070390082c400f40c0c00840380700c40740010a101d14040e824049401001604042c8440303c451035503a6034090040201c10081118200100440d01d81240300c0e110a594030315000d0309950123001d5944044504182603040480e141c075041c040d0380d0000c2c909010700c03a003003a144010026210821080b40300048000c0014074003040083c055444e008001800c089000401d0040e500d103030036540740150781000720440f00c0200245c8007083c800d04440044a0f2903880f8442c90684c4082c07500c8540c0080c82500c81d251002040080c5a0400a954a0310810034290 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 740339019 1250 740337769 740337791
    0x215150f010f0e04150306020f070203071a090d05010b030703050304080706141602240304020126011a0405180f1f03031b060c090807091401121110030b0103 69
    0x14503a0302c41990300109400510100d820f00f000d81c001c03101001e2220034401d050fa501d4a0f82c400326406403001c903102480009518084d0705041103440f00401e00d9042c455124405210310001034010b0300d406610503880136800300c042c46000d4002d6900310368000c0903104029640d1030203c6d0307a64060701c41d48081e03004540c40011800d01966003401510000c41c1c1135407400c3c101c00b0003044241010041241e0009584600c0c1840d0422900c10554404082c1d01e8207549043c5400090f14000f1b4000041076580407070356000b86c4694004070040c1c110765202017082c40c10044121502110b0140780c125a400c40540065484144440c070030075402007591070002d1841e501c0742520030740350300724101d4494101015080101700003071249841410710000510308440301c4c880e82e0b486006980441c47c10a00081c904041800850b4080c800a40144001541005458081011130900c2c0c00144078411000c02c049608800340007104031104c0440c4001060700b107408801e09070280c01850301e030b02032070300280c07805c894864 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 740340269 1250 740339019 740339027
    0x901030209280f14042f07150504020618031222150c1101022a010e030d0f030515030106240c0c1202010908010507020d02061f03120215150f01 63
    0x4191096003090b140b0b145409018030014040301c4000b6824030359002c10400511092000d122204131b032944000f5900c0d403184c00d06071102101580512005803404041c040182e840300211021440042c03031100030300d04032600080c10f014418154400c40c038000a41c1d9008951140072401090140e101030602e20303a2201c0025190303001610840d800714941c0c1000c40045420500403200c0a44144110b6540801c4100701808034003203011108401c000c402041c210940c2c206c00380c0601c6080c103900414030130fa002c1d4030003042100c0300b40c41c1405166840f000308804034260411680007090140007482010341d54403590051180c50700b81000b851103404082900c032131080e903d81c552190440c919216503818081e0341b007000c07008054202c0c18000d8101002031015070030301405105c0d8440b60080e2040500c80c4070042d0908134003c1003007400000301c00403074002d8405900307070400b030300c1d0040115081508000800e9103007001402384032440015000401510f400c2c10340085140f02c1003500c4d03d892101c0c2c07010040d2 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 740341519 1250 740340269 740340299
    0xa12030f0e0c030c01120f0213090506030111030a020a03060510021c020303070804030809190804150e0604030b06030f06040f120203030712020a020111030406060303110312060402090103020928 85
    0x703945500401c4c0d0400c07441d842a004254008000f4000088041d0701012038000ca901000b02540c817400c520a0401448802d4403505520075803e03002884020801c0d000720003548401090328006d140c3c0400e9280c034551007640444040c1c000501410b00f509a0700310080e40d10022a03280c0c807031641d00307035008460b62440482564021651a20349010940300c1da90140c1d45500d0042040d41184a4103800c500303180390307840c20780e41d8990003110700343d64860414081c11402d800c1028031600b44020b02e4030700d0b0215142d090442c0c084030342205030b0802544617140000d0030020000b030303200c24511601c0103001c1031102d40015020058407806c40e816594400302c4007070340c0380d0004440400201e400542154007410a0350014111a80e02c0c0c400060524000c0d42c01441c1504103840071340d00c0c9030f034404003441016004a514110b25060800840c144002440ac0080c18180104401e01803078012480d580164000d40599103508402480e607601c164000200c0c94034800e011080f90a91106181c1c0000c1c0040751314048 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 740342769 1250 740341519 740341543
    0x6010f031404140d1d0d02010c051c080603010b0f0d030c15020d0c0e010e010c050c06040308040e060301060302030a2a08010902010807092105150c0406030c030203010e01170a12030f0e 81
    0x5440030185c0341c10440318180200042c0c0c140101007000100190007030280c904c80b01944c1403c5081203a070303000010101600144005e000368034000381c00c50302d81e03100c1010340c900c04811542514151100d103411128600360f08001401d00381e264256407103400203a00900000d070b2208a0800070320404940c11a40c0c0412020342ca80815580610702607075501c1749020304025800b4000b101e55030340951021803a07a41c09580190307100d0350080350034400c04512940d2203410800440c02403250605640000c3d48681420364000c044c0e202002d43c010080b5174004400c624440c40e10011103201d69100702d098043c140006049001554603000249054050055441924a80070900c1c60301500448421f00403146a8810380e01442035140a02003410410b291600c140021440d0640326440c00402400f80c40300030b60700e0030501d40184014803e4410003131714241103501d444911302c510703081703895640d0504240303040141a50b030350790790744508031500360704042038025052004220203040c09e0f02c0c85440c0d140205d08 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 740344019 1250 740342769 740342807
    0x5040e0c04030f151b020309010221030c0315030a0308061008091b030c04050106030c090906031a07170108031b010509030301150207270f020901020606010f031404140d 74
    0x10003000308400e0504c082c03030a044084005203080303155880c0ea03e111004501d40006038030026064520f0b5a040c00707140c510950a40340c12206140b09211143c043c000200079216460010000403200c44822041c0c80c2403040c0601503030b0240480d402d000303100c2071007196100d01070890300d1800021070f1710071019541304800c240e0107000700b059079a0400c45442d4020f003102760302d8490f0014045840e0b1740c2d44501402010280c600154002e01c0810103017413120f15500c0903031810300c0d00c030301007000c2144521030040043c3c0756803510f0800e0b85c0d01c2c80180c8104c6900c510200c05980d00800128444038000000c008401c0d05100060140600811407401c3e100c048490801e5074006100410080448400f50380341c00f0b00790b005036a12140c40310000322038000b8011110b4621030403110302c1005900c42c0d201d181a0003080000561a008180c0c001039036408014026030b04100d07040c825006030034426032006160051084c94440181042d081c21448500b070f9018039180c1b801140b14560f5640c0c000c60074004400340480c0 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 740345269 1250 740344019 740344043
    0xa06061b030e0406031a060a050108040b13020604030605070e040b06090303190509061603080a020304110906060409181209031e0c0f350703140c030d05040e0c0403 72
    0x601201c1190b000c6050a8102e500d601c80480010501e03020316041e00b0b038184210341589414404c200303000380c4981c09641440f411805101c00306115020950780101080008031900d081440420381d00e100300e41c03025085502c2d05e41480242544000f4a0021800868084c000c411f082c50410020703101d08103101d949544204645510828060351002c0c0b00c145604005040c00e914602198041d0f0280001481c2c50364004100300805400003005038220300328038070450540c0b5040e940c50481e0301d007041e0320902c00c0b40100001815030342e80303c003110081c25550034107206040700d030400682040014034049800c0401000368038445840740c0700e940100c036005500355642041001c0000c40400214070f0035030742c010b03007014041108000f070646000201880c1c0e00720101d107002007541340741480c0081140f5401c1d00742070503805c4404c18000b80303d000741c941002242c03004030050805c00b0700d800c0c100d0300c207a90903001d8003030407070102500507000e4011200348261a1260350f0380c03501040900e1207140001013201c40380e54 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 740346519 1250 740345269 740345273
    0x90a060c051c051012080c010c0c02100c020f0307060230030f0c0c01090f0228090c0201150806071101050106080a020a111006090c02011a010e180f0a06061b 69
    0x20700300e26001380e500c4d000c4202e6503031036101c0f840c100e2030948002d07a0f000700700281241200380d0900c96004861002d1a0a5101c400a540002ca00c243d400051030301b04076080701c1c140c0640d0f64110b8082d05200c401000c490400703a8554020303480300c0100014101c0303420207100c0e00a840303003560b1a2503000da0400000074a50b540341c991404024070f0142c039000d2044014007203040310300802d1084090440c00307a101442021001d10400c0400c20240000703018204400c0203804070002a03904c004151405080c0216501b17101c9041203005002402024100502c000400202e11401095140c050029661882185010110300c0c80c240ca50a10803200000c45420000e41081401d50141407502d000c0c1c6801401c100000024a182940708070404480503a50001044511401d01c25a44402c03098002400700059480c09070f200003182002c56414800000000342c400d85e6041807130240b031180b03010050401c4c01e01450f100c0700410100c5002c400b1a191050200d0103a02645100c243c03c0801c00c00301110105035 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 740347769 1250 740346519 740346521
    0x213030b064e03071a24010f0e06162114070807050d020c01030e070602250e040312050105040e100c090f0815330612090a060c051c 58
    0x1080c0301060109440b2400041c0c0c000c0c4014240140107034500440c1e00418540980000310242031020150500700c20b80080c40306001520700108000d0134030f02c0d03102c0290001a0707080510b102a196204c040090100394051550482441c900e0081c441d030130b502c51080082a0090b0092407044021402c0c02442c0fa21400b4804014507582d03106040e0315092040c0c0795240b500d009041c409a0001d40c004014a01c0296498400c18030800c501e04002c148040c81c1c100081d480300654580e0101e080c0d0701e83c00398400708814070407040007041040004036051800d401e005105030742040801440a04050001030f46d440d00d8050080303000a0380d400f52424076804407280c40100345501860b414005889000a20035840e500c42d0301c001c14020016100d5141e0059680718107100007000c007070881a40380c1036154803d04090515407600c00c60080828516008800107034580507001c05003450b1040c000030131444540c0482c61002140c4034030428854400705010503511380c014589442508104a02000300813902 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 740349019 1250 740347769 740347879
    0x30114040f0203010801230c0901030509030903150415111818010f062303160c080409060302040b0f01050906090109030516180501080d030905010213030b06 69
    0xa00c00906512105088416030b08243c0c0a120103035500c001d42e10401d00c0c0010254049014030669100b980340c0240001140c0c0240342c8a2410141d4940018031114400c004441c00c01c40002d00721084c1ca2840c41c0044c54a01e0211000c81c1c80c62090791003410b01c07074040e008002d0300c00203502e9040e00300403072120304003046030310381d910f80d07038400104203840d12603059000d102c078041c3c0310104208131450b05001025100b8540482242c0e5040c03082038100014191800550f03411802d42d10310010850b0511100b00e42c1004100c001030940800090000b40c481032681c006c2c0c040fa40700340d80510105003400100520300b40010b9045000c6030b010080c15405107006002410400c005041900c29140c6a444062400c500e0840003091618444024003d5466000c40d410200c05028024003456040102164440d00c01071554405d044e116007500c000c001d400e405445035001640f900c026040d549007002c05030310000781c40060088600303100d00200040c5034240140340001060144142d182180210007803244 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 740350269 1250 740349019 740349059
    0xb03040f060c032003040b270102030907060906030209010207030b18010603111c0809060f1c060302040b06070809060c032203110906180a151e06140301 67
    0x1402206040003070040d108100c0b80007a15940015000c00060080c3c8620440c01d0380850340340d0b400d008210000b0303807921007254007d06211038900707210540c1104e0464200349240c001a994001f008200c0c403446e0008144e000c50706241c0e5200f2078540c1d590343c203404922038013070b041c5e005030003107201840440c00558241d5000204101441e5a15482100180c01c640c610f800448542c000c5008400d118a0601800c1c2e9903400210410005030001d5a9101c1441c80b405814500980001c9080b940354400081900c0140c1c1001c00141040141410904010078850204a00c80e900c3c0c012905440c0c10158240c07600c190348018400c3c5001d402c4010007106800c440414001c0e48000c20581010031100c007504c107c0c07042124100d401c85421344c549418908007041d00580180d030060f0400000e40e0700d010f8107011150b00440030b030f43c0c5a100d019103200584183d0b00040d1680040c6040000da16204403401c0d882c00e40740c00c220f410150b03140c000c211008a800880b000c040002400144090342c5084030040c0080 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 740351519 1250 740350269 740350283
    0x1e050603070b0703080f0f010819051c1101052202010315051503040519080703270b0d110301050d390501030c020d0f141c02090109080a0308010b0304 66
    0x60ba940c4030a64550b4498031003103001901210902c0015500100c409030005541d0254910b6503051800035581d5000503110608034110841c01513051100512030001e0b142072801501b02d2000f0101c00c0a441000301c0c41e61405190b03e0031000620a0f41e1414000b150808260030381246e401f203980044024126641045c14074100782030002485560385407043c5620308115500e640c49141c00d00b8000c1c1040082c51110030b0110000a40f0000540c0d01c000301c5080f5941400c0101d4418441d46443c17610360110400b46031400c040c50f2011606407003440160109071290901031160b940c4006981d4854002880b607660061940c0107564002804404404502290982242c13107803d600c1000000700e41004469513a03c1e0301c0001c0038051541d060064400203400d500081100c905441c00040c196000480040100240030038840c12040010084440c41c015408100b51840c5a562000000398440361180d07010800c1e00e840040c00220100e4040e851b1074041d1280f0009a1030442461165800108104c03500 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 740352769 1250 740351519 740351533
    0x7111002121c050108011d01050103080a03090f0203010c0519090b03010504330f0503010b15090103110309030c0610060f050901110a050601060f031406060f071a0601121e050603 78
    0xa0803a440f40e103008101400010071205e6226803407002a6140c8a030056803a41458011320100e0510421900108074a00d0300003012244c90428100000c02c2e20300c029811b50038880b81d800810380c0300b80501903402e02c0138803005910b000d6035800d6401a501d84100342031a0020b000401c4940340981c0103100c680c81c903288a244c5150b001b4188214402000680b20003144c080500703002030382e020000c0b00094602a0001c0010102e00000200f107108220007603203a501c00000c10214a0340320b074110710354100000f0116500ca080c0540c40c1d94407034000c0301c80340e4a603101e04000500540c0f0100c0c40001150002e441d205c0c0401408a01200c081c0e02c2918030505100700c00c40e03050001442086411081c0340118003a01d03282d410048002e0400e0f444500318020141821300c3c004400264031501c0d50003c208a900980e9520f24449181c09070107602805044000b405410001800c1d442007558450a426a40c01e4124038600c11884122106803246040c010142c001040700005035034400d50304140b0043c101d07a44 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 740354019 1250 740352769 740352817
    0x1709011e02160f0f0c090b060913020c03041202040c03020702010f050a0c0b01030615090218010c02040b2115190b01090302150a020123060105030a0f02040303050711100212 76
    0x1480c0c3c598102141c11403003d120880c01e000c1c002c0c0031040502080d41041c006c8003682c10004010f406003c9240384103a540030038410280940350304407990222075800b0f494503140d030380c40f10210501a40f00b040e1b003d01d050801440b6943c1c802d1080303a40513a8142c4401859a0546508071041d42011710342e40c007805038441454010403079000703403075000398407996011032813204c0f08620315a03241705170740854101ca0043c0110201c1c030904040030142240c081c03034070b085050203500014014140705042c2d1608015030207558400c2c1107103001132164025152045541c528613280d158504010b00b250301c07000034094580c4c02103c44500d07400c903c4c199041494030041042c0c50703400044188001254118003c540025106e099503020702440c4401c81012461280b001c0002c007006020030401010103040040000006a6450599000b0046180c000404640341d0b616031402030483d5000480550f404101314100080c549030030500c1006d009190750151511459145074224641c11413580e0042d62140c1031900c180e = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 740355269 1250 740354019 740354033
    0x203010f0c140f120f18010603031e030b040e070815150d1a0f0604060b0306060403120203070503070b01090605120715410708040b1305040c1709011e0216 68
    0x401201c40e1a0310440b02d01b07020250100084010800c0b030300a03418802c003000460b0304071413a900d01d40343c4031110f000c9602c00030100304c00030401242c0980e4043d141802d85000110b00245c0201580d071000d049030f142411804458410342c00483c0c0000070080d00202c1c4240604001034402c075035034030078030b184000c21000d090a86400c0070100c3d04841021100b1041124601d01400340a0050010400d003524506011001c15682e100b11300001c1c20181020340100e050303a208004440d14a901b150030340c2d4450145103004000301c0c20038482d61143c0f6003801c4010400707203010080f00908802000080c8889850f00c4180301c180c45002e1380c80d10134001034411102104800c052200c0f0030580c0c0c505050500304110342c807118051901c0c0714100341003000340514000981207400f103905581c08021429121105c0d010750f0000009543c112982085c1090382404140e80c005803403015500740c0d0445a1650303070f03030031060f50f0881c1c8c0314421a0322701640311450b1006080c200d0707004207000c40c412562040c8112050703c4040d = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 740356519 1250 740355269 740355271
    0x10510050d1404050601140306040609050f0f030d1118192d0b09030709150902072105180904020402071211060603070e04141f090203010f0c140f12 65
    0x92095040001000f04000c1d0910000d0301500c01c0480b840c0d9207547c43c4000c01e5075020700810042429a464482e901440403c206045158086000f10345901c2c00c151152130b140d8121079030404460b07081c280714020b2000c080c0140c850241d01852004008031511b010411100c030004060340000340982c4010403400c030155460401d00390090b445200e00c0420b11141d10881c0160741c030000c0541414070119001d540c01040d00012244002408680c8103500c0c504071440c4d090341d9108031140c80c07001440c0010003c54800350807003400240005110700c0c0c919003003500d541c85006040305030003040c00008000351510102090f005800900018217009003507035a03400a1080969000c00701e800d00980543d03240301040071030b512000c250083c0c0300c1a4a04036040022030740c040d10042800040100f0031600342c8003049030341100000201d9801030b0b00140f0607403a00414081c0c800303034029400c15a5440103500c59020300c24926406a641300030103030319141c52041c1c0d074108603024070031f109081001d100c2c45800718000c1 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 740357769 1250 740356519 740356541
    0xe0a050a0f0c020c0a080102130312090b0d0e150405030316021c0206010513060e071103281206030c05010c031808011401120c090f06050a030506040201020111040b03010510050d 78
    0x6000d444030078070810102c01451b40c05001c0aa00421000000b1021500c00c00c003100d6000381018207a103e21401a500500703e504020041e82022401100c085040d40015845105041c103682c00340e8003540080f04099011100a0010b034410004114122184a05080301809034070603500550404040040f2154401da62540141c0c0800014006813800100b02d002e0140503c804108040c9006120178003141d000300b840701801072200030761b81441014812100c020211450f40600201c0c3c500c1e0325458900080c080d00c2c00509800703103000c44200d042c850b01040c0ca800103480c01d0410b280c5401110780c004090070442c2004944a0400c480d0416840c960002d054400d0000c80c045140381581c0d00207a070164403180810240c145c0f85804644249942c0059802e40317600802c0c9550801e840340054103071a48859001403100000209100010800d640654800d0b4000d0001c02e0a8080c513079124002e5000c0c400c010402000100030703600e010f41016910811b0b1b1f003081400c10a0f010811403c68200f5040 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 740359019 1250 740357769 740357773
    0xc060d140603030a021515090f07020609030702130b06040b0c150c0a081302012307110a0303081305100f0504021302040b0702040203191b02060a05010e0a050a0f0c02 73
    0x1001600e11a10004240c0c0034800368015801c20754808002035455603c0307081d03c14040548404101468900003031031a0096000c3c00e2800b8605103144c04401005040b0350780f0005001c1d11011800140d0f001c0300320340f8407a80040201691000003c0310900608062860581c02102000002440031140c40582080341c0d50a001c0c0c01402e402900c0c0640c1c10034010120030280070308201600d485a00100000d410481388010040b20800d2440140c5605505101106001c0940000170800c0362034a07000b0302049218103102000402c0c41d10622064254078040240801e1903040060104100d007912030600728015030454010040c40da00c9502203880840036404001c2c0c445003000158180f0428000800c0150b030002c51034289004225025070181c1a80240b1a540000200e040303140070200e05030040040b90010041000c424a40105070450704ca0480c001d4011030000461108413441b5181c105e441220422660b0791300d1300c1c0030320000c0c1401090911407075541c6445001a20844c45120140551600 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 740360269 1250 740359019 740359031
    0x60f031312081e0f07030507230901030612020603070c0f0c0f1d04210e10050a09140a05040c020102190810081603111206070c021f020604080c0c060d 66
    0xe070140b4026030380b01c1c0f0801d5880a040512218004e2400d04a9224049140000e1141c031029000c4640034600c1441d41c03080740408484888520700c0c4401020060b10076201086601da592a8102c1c00c00100304001e5400041400066121b40c061a042c020852294006140103249a914460121110740180140d04050b2a01b4008040c0c94168011003030030303c01c100380c2c07140303490342d645a090440064031000c1b0100107543d050107140154a0303039051450040002c4c0c00d0050703140e8010319a0300265031100020345020300c000f450300345400c084100702e50003600580b0306a00f00014400503110801c40d2004640d400c204d032900301c4244021480080c141c2c3d039203002c82030603d60f40c0307042c07800ca060b0040c01c6180c0003400f21072806543c4003015011603512080001c80700300280c00042e0f49810034080c1c0c3c2580c3c0540402c020f201944075850042841c03080700c40c08a500f09042c1d210403031030f00d06240c03500541d208802081c04513681c400545094001d51045800e11711341d100119405800038240700011a031500 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 740361519 1250 740360269 740360281
    0x803220e090c09090a0c140312031e1b0d1509050720010c0804020909030c031216050901120e0708030403060e011d0319033207020309060f03131208 65
    0x20030054011400300020004034400b81c4803014101b859200e4001c40e40c8070480b05200a44050280c0004060301c8042e454903841d20090801094403a00300301856007000300002180c845014421500c22401c058840d0b08100c06055004010701900f240d040445148584c00030714100140951449401a5500d01654000b07030a40012a040411101d1003107904011554100c103a000903d10b40c00342c1c04444ca04529200c0c0c1000d00e04520403c0011522400001100f161842131802040e00034a204941e1040c005040c1c0c60440c0c00d070141030300150014064030f696000d52851a00320300e003044d0318001034801340d5030b6a0503910710b150302039030003110019254210710319940420301c1400c0301680da40c009200c0120080c50069224030415240b600701803201010f40320003612070f42c0501107140703601e600e04100d5200c803075603c03100c14050107521000c00041400280071a00c040301741c1d11144009040c0741d040225034400e5400ca41c00040c54050701098517120000401c010462184104c80b2584400d1200c0c2018 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 740362769 1250 740361519 740361529
    0x302010f060e09030717070503120f010504020a050301060f090e0a15080a02301204051207050102060a11130f0326070b0a0b0d0303020a030b0108010803220e090c 71
    0x2542c400c051032101e11040001803540882144c465982c04403402c030103c8999040381c107950040c41e0300642548408a04e003000d02c01005046e40c0205000d0003c02d5184ea61407080100381e2280c1422080050030a00c010006079004000b88002140d00d0308100901c00c3d2940582900031030100e4484042944521604021410ba241e91402508a48014200081c8141c012603058950040da00500741c00038414011f400300200b46910622100d4000e45482c158510451013458101740103042c031036203070460a5602e040300040d0b0001202c1044e00640000d070b0f140d4608000408075112010700500c400c0204200c18801c50558501501158883c4030005042d03042c6480c4030740820310044030741c15071500b0f030341a000c03081425510a250312000c1c40800da41e0f41c40607800648401c8a05540192240800700c0c20103425030041e00d6a507219641c02c014040c400e00c01142c0d190000e205802568004110711070444591981414150700004014540c043e0350300f050074450b0b5001c8440d0402038022081ca103402d4940 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 740364019 1250 740362769 740362781
    0x103053702010806220c1805060f0a1202070305030a1128021015170604050a02040902120a200316261915060509150f030307050106030204060503120304061e090302010f 74
    0x301c007c28068050070300010a600e4441e4140b031515a05012840b070842511848282c011200c216005540341e010b2840c0240090f00160b500700300a40c146001614010000c0381a151021205102c11202d41d018031581c21024900503a440c00314041d03082c0000889013540212001180c6801100800502c0d10094600340e00501210b2019608184184004906c000035150311081d0100c0e0009001c0e43c0340c5c070014140720b080d00d002c0a540c0c041c49145509001040c80c206030171841100040300b4041d4000105900d0707041b1409903030f001444801003400140d81075402d548250842080001fa000c21200200345000701481e90500c120000d406e040003081010842c2c1d48201190400074002d00313040c280010781c090310080013249840c4400012a8680d610782d51044000f000242c16241d132143c050070024064605400b080c2e002e00d003010030016041c100081c82c3c100745c2210001c0242151219603803440508411000442e802d8950440d15401c1c465a1056a25071882900005008494078803827009803a2 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 740365269 1250 740364019 740364047
    0x90c0307080705180106051207020a1712060a0f0605090a1a0c1c1e0216060306050f0a050f09040609080d06080c22110d050103053702010806220c 64
    0xd44c8401001010b41040540d85104100090f01e0075540d5001001c07407034044241c0d0080d0403101c3d0001250b02c041c0c8070400030101d0b03624824102300d01d662600280000c442d01807003115405100d028040201394800e01c040c05094500410f200200c40e5515550381d0410307200c590264201c0000a05001282d400308010309450b4081d1190508102403010051314028400050303010501071403066800e118824810b002c090310f62020824806d035184c0c1c00080007021103018560288604010419003840c0c000c284104035400100100b000f4a079000030f0001c0c0001c0540100c42054407030350b03241c0008024001402c0303000c0d201070300000c03590300d0500303158600300c06121203d0184090810041d00c05240603c1550000d40124000c2034402031501910075501c95140313072501461822001008008002c01d00d154800851301298175805644040581c0800100035080f040b03c1081c80c9400055020340f03c1c469004800500000055480c50103070320744130050303404d40300843d5035909695452541107241d041d1003103 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 740366519 1250 740365269 740365309
    0x406080a110909010b1c0201020307050601080c0102010c2109020d0b040f1a09102711030c09010b300907030209010815010b1602130209010801091a09090c0307080705 73
    0xa00c170000401d00304040c0308450034150701000c2d200300075a40200200ca03d0703a503009040314550340c0d584440359200c40d80088031900650810300c02d0b000d03042c820040a80d000440c690144042613941d9604001441902005c903000002900d00002107a04d040815114501404045489032902d2620403644c010520b06058200002410b0101c0306e400058074480f01d040c020400540d40066100c0200810000003200b860501c9640c401010009001c0070404100401d0b02184c1c1800c00200400c05012002d0064402c0c2c42c9052089400703114180d04407501100d181d21240e905203503c80c000791034450084806001350b0b0f0220004100714200980403a0041c001100030b8078488240c400c8440d54501d0610403040d0011b00411a414203221040e400310303100c1d90060402003001c2e00c107041c1030065006254003501049082c000061080d0107802000c031b080801103203030400d0a580c1c004004198102401d008040e21455030160001d440802101c03014013204002041d09500e0a030402c481d4221000c6202190 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 740367769 1250 740366519 740366531
    0x3050a031526010f0e15092a010c0609080903101e09050f03040303080a110406121e02030112021c0302030915220e0709140f0406080a11090901 63
    0xc0594040c072480d1081001245801c1e0b0140034080b0780900b040000040c41e41e46815081c440740040080e0360f01c0040d10400c1072000765516010b54513110702ca80c060023044582c600581c000c4032041ca03100310483c1d0505060050a401241d10303250308031032160700201c440b5480080c800c1298641000344200021120710180720040e031010203101ea01410300c2e469005251620b100d48100302c0107010f404003c511020481ea1a560780c0d0a00800398481542c5051403145002e02540e00071078510100c4040c2c170a26290384084156103441c0c1401071082c056081c0404500310014480041140000c60003441015914080000f0500400110400007180002c8000d81540d614001a4005c815074098540803030f1100c031a012103500a40d03080c0b0030380c00b480c201c0d000c4c42c1c82509000c00d01644440203032030040c203002580e40e072500f4042da240d45250161707940307900746001160315070302c3d08070034960050b080541b0100310959100b140502e4400e1000c0210f80150300e0340c00c0e000c003c0c2008400c40341c4c050f5642c0c00034008 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 740369019 1250 740367769 740367779
    0x102070b1816260a2012060106050703140904061401170112060509191208280b010507060e071e0b0d050a0b060a0309120302281b03050a0315 62
    0xf07401082c070704030021141c2040024841c1400384103103240c15400c02414164042564003c0450501803190f061144011800c24070410740700280740340c16a4070a84595141a202d81c40554480903109010300c038a40e020043c1c403845494030b004840082c16401000740e00240810000f428001c5540c10442508030708100400c850804420041c00881c1c100b10001210380798404200c0c10074015041c500104940c403020036003080024640001501c450fa070300d85040d81c0380d202c184514051252071032040060004d00003a00c1c03e500340c1c851310034844141821440e000599070f0300015160040e0800440c0e400003001000a4401644840220400c0700c80d5040300a0a200740c110b030500991809090b00d03030f5580d0002d140415144d20007200400001d122070b0700e60f11103600080150110b40d07400c0300c00350050401c081004d4003d00030785110104110b881c0c040132154801c180c0b1044640c0386c0034000c0040102c0041c480604c02e546c42180c10380250782d002c1d90b41500301c4002c0d090303d0b11841a460b40b940c00c3c82003082 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 740370269 1250 740369019 740369039
    0x50f06040303061a031306020f030c03060a06030b131a22050f0c0a1d1e010905120703020d0c0b0714010b0114090d020103060e09010207052b050c0102070b1816 70
    0x1c6e21030018107640c0135170941414810020b0240010001111800000380301ca00074041010b10b118140445442140d540c0320760f0200d045c3e4130000a102c0d04070b0207420340e102c00c2e0305158120140b802c0d60782c02c035020001500030000d000c180803811829103054914082840040301400362584c00a0041d502c28844c1c00c0c000204a02840350400315020451241c0008443c0d8408600c1108203220050403c001740f20020380d08603458003611421404a030030b10600051a091164480c025038001c00058a84246144c00f80007504805481c00c4503041c11850300412203103d46409803100c02c6c040d51a100d80760101450031421181042c40036814080c65001905608800404a50740488240c87d0321101d07039841d20058028011540141d804180b003070040103001601503024141e00c90003a821204840110281d401b922801c03046030040710840b9107202d06149006400400700981c581c2c000524025084d200d021080000707440003000c2034408440d144882c4010800000035070321100010590a1620035400 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 740371519 1250 740370269 740370271
    0x1030317040510091202061005061602010c0f0602250b0c0d18030f09090e0d0503180601030c050901091419140408031f0f060507020a03050f06040303061a03 69
    0x961824103500001e0104481442090382e07030710f40c02c0e50500c8809850324111400c45102509100140329041c0001c00c2c01003102e44100455001501e460300d030000e0f5900380084030403409403c0c0d06201c0c501401c000000c94005100401500805c4016258200302c412016945080c00c515428030800c2070b0140301003101700b404580c020304001e401965034010280e400002d4104d040320010315440c01d0f48031105140d0000e034020070300100307652261091911181d210701160502c0401c00d503240c0c4208408403555014000454225903003007480d1040341d405040040c50803509800490710300c101c100d001c1105091000000e80541300b103040038000754401e03110080840000400820243d41c58001c0c1112050150740421224803404082211900c2c180c1409181d41d0701c192004440c1c40114503039074090000f82e812403000e03603000f090400007803840c003042220544c0200c20281c0e030103603060b000080011001c000000203d213001026000d140f40c00c1c18003800712101c591101c514008205001d0010019103011a = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 740372769 1250 740371519 740371547
    0x7020c060a0e061b160317070f0c090204030c1a03060d02010e030f012c0601090902040609050a050405010f020a090e0c0408031210151d0301090206042c010303 70
    0x100d071101d5541c08116003603600810b5107078003d2000540c880313000400c0c1c88429080043d0004032004408074401d8140750102d2444080c048488081e98800e00c1c1c05c8000052010034010b0004030041c40d50f94550051220b195031140c102c03591b00207420820866620050002000542c0201008860702c0741c50074898403004144900c02c04441c2d40040c21603002e016803074001100030701110308000c00c3c251140e00808190a00201011209244461550500c0807203000840480007400e95a40ba100c854800340c02207a1040381c0c4140c450070081641400c904c40c0500c1280921f001151504042c02e18500319982c00e03508050a50040010307000c41c98104403094201c03040c00b10b0003011952413109007a421f02a503003100706079000003c0d03150981d04090761420701480c80012661413887d0340780c00e01c841070243d008036040071031100341c1d00003c114164108003510304030240c00401c5403400c581c0060703a1030344280c20030310880e05d411140320403400110b1203181d01040c0c156410000380d411514042c10f269904d00803 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 740374019 1250 740372769 740372779
    0x902060306120a060e070602010e03070c1701090510060608060910120516030609030801080f12030a0e0d020601230306060405060307031a0732130b0d060503010509030307020c 77
    0x840258800c0400c08440059080501041514405c900550300c076220307446038800642c01d04510610488010003260781c0c450384000e0400e6040e2818000c4250303c18240100090755507204c240b000800c1040c031100b06414280f0b00001020f5040403000b8002c400041c110034014400d003000c002c01040c08009070003d407030a06690348860440b61034020b00d000551011840f411403280300010421203950007c240075403007501d4802003aa266035840d0350f183c548804140003a403180761000300e0486007500860700295801c602055025110243c18038005448441c50b005a00c41c000400240741c800c41c1840245a041361100401452000000e9880c003010700024440c5560b03201241e0141d03410800311000b0342e40b00e050603036185c05100309849030840407582d0f4800b080a1200e8207440d0518070207048048406141c01030b110159428828101e078021452141160911400c042483c60005028120019800c000413800d10b0030201418290340003e02002901e034001e0051119541d004161400c400f20305450b = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 740375269 1250 740374019 740374039
    0xf090507090308160c0821130306090809120f07060201090206070809040e0a060917040e040b06040f0f05100807060210020f090409050a030905010e0d06020705030f0c0a0b0105040902060306 83
    0x135900c44001c02c0c2d0300d8001c0080c40c00c0303a00061a0741000c901c126004030215098401000c1c0b040980406200c0c1d1400c00b640c0c1142c00c50203100203426a4044204035014001c100d0406c1055000b082c07461001e080d85007107590141325281c1c8a20b1082200c1c0000d03014500c024066082d4a07400f0a201d4010035500030b000440103d04010580c0319507022003241202c00085400d1002c00d410800d00402d803103c010381d0001c803030050108103410321000b2030301258584072030321840d643e558440c10344070003019007115445500c0da6000b103000500d60152031b0160f1000d01001400d400c000c1c407103104c0440c2550000250b60011801081a503802042004c4600d005450240e640e0382e084810031030901c50a140702d940a40b400040b4414854009444a9540e210b62104800ca54590f03006440c807035069544aa805030a400007000020f840c0e40103400788501c10b01c122810400b10388a40300050300401d424400030f5101c440070000380081648054010001960100036400e6550007048882c4402003000340103c40c021 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 740376519 1250 740375269 740375287
    0x60c1d150d0b0415030f030201050106050315010c140106090c02070e1b18060f04060e15030c0a02191202060c030606071113110c0c01031b0f02070b030a060f090507090308 75
    0x3e0411800326840b2038120100d55128903044621b10b02c0010140c0c0158a003100100320381e0b0084045a00845c1d8000c40c1003c80b411080c01120001c450800841d50300300761380c890034001c40090180741c2c080c1126000120300f6231015807000f490a8000d900c03c0890318107800c140b0141c5071105980e909029658a60319030368003150000751b40302c00c49000001e500004002121207918461901810507240340d0380d10404a140004100142000d81b03100301103802900b0004158180e1444000f81046006401584c4102038041141034a80629910030b480071300c41180341c0201c0a6040c425950300000210350b40307045044c10008141c00d401030b500010840140c441c0c2411040d5100820340100d46030110b410b0100342e4401541600a4104101198461103462040c00c207542c043d00502026450700c4180741650303039140e1000c8402558007000780095010781d00c0007203070283c0048015031044c0e0310700201051241ca000d4842941030f000d603000c000c0d150300c2c101c14040d00c00d6004a00c58101c1b5002035074242c441c0094 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 740377769 1250 740376519 740376521
    0xa11060c180d081215030a02092d0f01060f05120112080708030a09110d020f2e020a051005070503340e04050c07210c060c1d150d0b04 59
    0x71030006403c8400204070403c0c07401d500c142c5244155451388111002c40c40200034075135180c00d4660001d500400d04000100400500000300c040311511003001142022894040d40c5100b1041d58031400d15460700005004070781e00541c8000c4075401518000b880c00400300f21000300804c3c107000715011410717124400c1060240c400181c407106908110040d54a0074000c0780c00004103007108007100ca042c50070500f880140780441d40e800310300e03401802c00040c4040000402c404845142c40e901802034042d05050240e0140404440c203d0b14030b50000c200f1600306041440c03800341c41d0501000c10390705000401c001c0d44d5108041e40e8100000d040001901c600c1c50081c588194404070388113620305007040510a2165220b0300e003040d010804e840410841e01e410307034007050317911801c0c8015110820001c0110038010010103100c1760f2085c1e40c6020820141c0030742d1071034103640b031410358500043e0321010b140d802c0d400110100d607145581110214424048071240d240d15015005081e0101070340ca60108500b42c0311 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 740379019 1250 740377769 740377789
    0x30c07350432060418201801052106030601080d020c01081003050105010f1805040f020d230c01080a0605091303020a02090c0d050f0106120b040b0d05010204060908031c0e03070b0103080a11060c18 86
    0x291440500c0c1c10041912080c42b440300845800d4407a2290300000565410003141a44c05070b055036014000b1b1003200b000541d004403000d010300c87d80888104001012a20038401e0030701030002040d54030350342442c01403143c954941900d4088000b51a00050100044410400c0c4044587c1991140d01445290a0089002e102000c1c0d0f41541400d0419a4044040c0410b01c141e0703c5100742c03603144440c2c85456081003102d450303005550300601480007203a840e42480a2031074455100b4030469200b0035030341c1d0114070362035402d50740d040f8000804500c112a8000328080c182e48500902c0078402c031036142100c014002c0b600704607080c4004e650f51211a0172525160801c01d224000070f0318a00003003e6514045000758860310484000486080004c01c030240040300b2100c0c24680c0003054072121101212090017080b550b420301e8000c1c4002c01070310001622508455000714000c014164807070b811103a014260b180800c00e0304036141c011208024001d8500400c1d100c1c0b5408032000c203c42e240c440c02c00700c2d5958070 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 740380269 1250 740379019 740379037
    0x30a0305091227010e0406030c080f0c03070e09070902130603140f0105060f120103050307061811090c0d0c1d2202030c0735043206041820180105 64
    0x1040600c0801031050402785d00d800c546c0c08000700c60000c8100e041041c0c443e00400026030785504001800c00c00d0030282840380d40c000003c1c038184c1e11a160380d440b003801280d00002c9074040020011808011762034061007090502085d18134030039820f107424001c40040e051705002d0144110008280441001c044205440c50070100c0c460704010784d41c403400c2c41e03981c07504101412581242000d44000481c010001300c8921103600141d441c03610070b0018104841404010212815100240140e005040b00c0d4029440025095107807040590004400c00c2c088001c03c00809002d038414030f0004030501071030655250000425000142c0300d46a02520480c81e01c60001301030f00489100410461070103101102510104002100b500000007400d151085070246106d40c0c0c00e42c0e0303406682c01d045030343e010214415000d00700e00b00404071046980011941d401c1034001e2000f440c260b404195034004107200d91541c4425005e414820100c803070030300003100c1c8100401d02000241002100710aa40120195a40380d1 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 740381519 1250 740380269 740380271
    0x30603030e041d15190e0d050726070b090106080307021207030b01060909060e071706010c0206030703140907270204240806090906070f050408030a0305091227010e04 73
    0x1001d40c044c08601e08080c1c482c440c680107108400e2010036014801d0380088845100a485003010600c001c1c0c0c0c09402c2200203448010015030001c5486420300800f111070b040105440e82c0398804c500301f42844c12801003002e49940e06d40441807181010005c151504140c1c120380b4200d000c900b0521807418078003d80d2000700200c144100100b0710b07a401074020425503800020800010381c0e6800c0c5c802c005c10050310007401180800505d4607481d64240324060740850103042c0a0769070101c07640481c905501c1284c3c0000040c0e0382d0708008880a4a04109a4200c1028001401e50b0760609158040200382c8402d407050500b0b80d804100c00c594840c1d01a90014101100440102880010f10441050038040b000000440c07020010b455407401c01003030b60148195038000c00580e80d03040001c0e6040c5d03007414421003d0090511000981020800041070f0303039007503540c02140ca820710404d007528015805403042c440030740c1841411803031890107049030746440c540d2440a0040546030300603103000700c550440507041 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 740382769 1250 740381519 740381533
    0xb070b06101d220209031209010c02011101290a0f080309060705070807030f0605070f0e0f0109050310060512031e1308030a031b090e06040c0e03151501030603030e041d 74
    0x1111851303020f0000781c101581a2402c05102c080300c40e0052140c1710041c4c2c0400c1c0744000a1300954400c2842e41d18000f4200c00004040201c00e03842807030302c1c001c1c6018940d902e6902000d107020f4101201c6110080c9810031101e2270783e60511810f0f41d164001c881200b8024000800e02d402030103800c2041000514140707054403e61a103d0805e507140e242ca0030070948500d4103000c081820148282d8010303201c040141e42c1c2203a07100d2807070200903035014400d062904100b1200400f260076603081c84200d106000300100055900e281c04140084601c040508030314640040c007440088101a00603602c00340000042d5641d108003201d02d40291400540141000b840007180b0703500082c1d055404908440c3c0380c1c40c44d20300c000d8480349080750040060b000e802c81c9aa44070010529605040d00001d40c41c403031604201010314500b8003c03d03d0f02400035007034514400340405000500c100b400851039802c0b401e1030107008107030654a01504603031026146600880d66a10741c064802e48081d0101d1030000300070b09441c85 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 740384019 1250 740382769 740382829
    0x303061d0405060f070804021207081614060702030a06050702071d1506030108070e1e040f031d0105190c050d1710030b0714040f0b070b06101d 63
    0x2114a044404540350b00c140404100062141d041c000c5c4950b100d0b42c1e8580c0c4036a2140c0c2031091070816400021440e1180394404103000c0c2080c40f069122240c9170017403200d22841c01c80c00384c01a881512109010702c004000c0800541c802050914085030031410109140d122040d007249042071550080720a00c85030402801c04141081180d4002c08001021401b450656001c02c41030f0b100c20702c103114103540144010450248601205540110351450070b8003007007007201441041000c111000c5640d141c8520b1280209500202803a0000344110382c00001c5010240000c1c25501c51103640e0300da0302c44072010400e841445034002821a40d403100994000d9a840040600345080e48100d01825010400001d403102d0000f40c403040440c0c2d00480400100d882d03e000559a160281610000b20301e170402c0041010075606210030b00078504451800e40c0c0f40710500741644804c0020301118801c0495940540b5420340c030901c4610480901c00d10030101c0c209000029404c0113401c01d04207055804a04030101d = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 740385269 1250 740384019 740384069
    0xf180405070e040b090702061911072306070c0b04080903011401090e161514040815130b0402011b140607090f0b0301090914010e0a020f03030c1504030306 68
    0x154103505840031302c8204424410855200d100302c1d02c1000603407006000a40d20031254892010740c60b03d11600081064241d040503505a102980940d90414a0311a00103212040300c0000c40001c0030501400083c20854801030242200c00c0000e8950b420541c049424000c0010880d084824020020841e01610840c0400813940074071503040002c0ca0000007495020b800f2890200840d5140c1c0059942d5042000c2e009200006031260020862020700748101d61426000070b10141524200404804040902d00c0d480c2c0e1100404200304540388052010000f12201c05560300720b07509003002000b103803003901d0305400124800f6014188441852001c00d440c040032403401d00170100780c0e03520030b1015218458640a00076521900311600d0b42000100140881d640c0030042c4248100f40038900c0400d288038103801c4d0388165001030256000310303081c4004c5180400d50010582400c0d006941009182c034032840d01e0b0501414010302900300100014105442a449000507144469851110380f0854030011 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 740386519 1250 740385269 740385287
    0xe040b0a0b040608031210050a080a05010c03061508071404031406090109080403140a170c01050105010e060a0c170415030e010911010f020f061812070203030f18040507 74
    0x90300c0520741030302481d1904203030090350103890030316008600c0c100000400c01c00c1050000d11070101c46d035400c04041810340d6030300c0c50b01c2c00600003c4010041c60045040450846903044a06028940352007800c010315960440810b0b812a201d040030fa19a50b03c3d48010744222400982302c0c450104000340100800c9041074801078800c1c1854215103503559a00e240d1030132504242d5001c0d0010000f84001c00010381850300001c0c00a16031800e4843c02d0f0981d582d840d0070300c075440d596185008004200301d0320b4480c0921906005220918001c0380c02c00024002c10a42e10032440c003e02000344485c080800d10072500c40c40c2001200320344c8160380e00c549d500b14101645a0314454075002a0414044040320745d014020249c409420106180076850341c0b400640e100803540700c3e40c1d41580180d1001c00b070b2803802402641d20501409094110740981800e2150401040f18141c00c6101d6040c0b103082c0c05600d0020035140d2182c8114800f660703501400c4108a824550502e07043c1d44142410104401c1982c4280e006d = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 740387769 1250 740386519 740386531
    0xc0f0d0903050c0402030f041e0210030e0f1614041506050703080708010518220308060f03030309210d020f09120d0c0303240b040501081006020d03150e040b 69
    0x43e03000c1c100c0d001d0410042e88000e40c0c800503404603210108011981c00c030900c000c1c9044010303003000d80141d198082004844c18a1030743e004079944a1104d51502000d1100c0c680030702d840d50240c8044401a0b00850701c07848280103850720700340c0140030b101c03040d1555400031031040b0003105082ca881c0e40d2248014404c1d400490300324002084400864440c1d400303a01101c0c1070302c1009280d0f0036095400e000002e0740c41c0c4020444513644607803040000e480001c0d00c0100721414001c1d134074240249420410700a5a45040c651a0300a80c0700308200940c2d4080442d490320b03412200400c684146084a0144a05000341c40e8111846440044d0090b00560302c40000c00d000d082c02c3d5900c503403460352450519181c5007011401000300701c2d009400c0c400039119910007802003010100b00003000b4203400c160302c560021a0050400070a000601307016640c0c02c0240d0765804094142c50f140898100440292176500e110248014580c0b40d8091302c00a86000c106000941f2484844403028036007405c05a243c8141941d0f2 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 740389019 1250 740387769 740387773
    0x7050c032b0e040f06050a060c1505070c02031509061b0306010e130207080d0b060903070b0a0c1a04030306050402031323060702100c08011a0c0f0d090305 68
    0x14a2580d0402264840464445810119034140c10880c628409030480e100c100400107481100754443e9124415100d0901c6034010005580d810241030080d401a607401070401c1c405041d04003030000e02c0021200d40c02c0c42c0b180d080807800740c46413441a00d4020307103158000e5045c002c04201e28842c4500303201319889500c00800b2108107403142e1a04419130b80d1601e007121051041003001900035400303104560001c0501405136a04521401403070822600810421624450000b0302000019502d004124410200725445071a0580000020750795407000c1c8a038100c680004601100b0043c000d2801b25800341d00200407042c1143ca50b16205070401003110200c000c280f0304500882da508181c070030340744210000742d07035000828031359100c2d01038412031700c800c44d412030a184120104808003404001e0254980b0303001811454001e800a0080e02e40f212040b104006250004010a105000d24503840104c42c4002a94451140b6802424413a9003548941c0f1407149000401c5c1d6641e214000408030790060007 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 740390269 1250 740389019 740389033
    0x21002030c070e040b0708100302040e0106061205060a330309032607230f0306180f040303020307051b07090c11071a07150209090708061f020c0603010b0705 69
    0x80c3c1004803030b050310080c10b4002002d000821042c0039028003604240110504003406544e94009000c2d500320310701c54282a51190000c20146402600001d010b80d1550303001d0090f03180040200c0c4441a00f442400e9100d80780c0c4100781200c210498031041000d038034580313200e401d034072118001d000703401207400407000944070107004186440c44105904a45000361a44040c5450b490300440d0790100f0f030400c16601f8484140030015501c0745030010141300b4041403900d600e9240c94020020000500560501d51103101e0041264007004607100e2075010707a00d4140141c594a481c1812070b414015858107084820071008202e55800000609074200c9030260030503c042c0c099064111501210506d85840340d17400204280945041191010a0b1380c0b1011140350518903a070300c6012403c4216441c9080c02640050012450309141c000568805041e040824240c1071000c08501d10025850444811440d103214200d6514800d2140d080b100c10003d001b5500c81d40c581614400d141c1c04000112114440c0c2c2c4 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 740391519 1250 740390269 740390279
    0x1517010b120f150601050405030106150e010207060504030611040b0a0e030f0318060903031207050703030c0c02030d0e060f07060e010c0f0c1401200a0e03030f160f021002030c07 78
    0x151211650102d9400740c220b08010444410044001400e42418044180000f00b2591024843c4030f006000031002e5002d000f042c05409071246a54000480c115003022030b0600c06207400404540841e50b00c032030000f03138065995000c1070060050f0b4200700045140002e05045d0183d0005010084580481c1582c452280c1c5050385940c0f4410411101c421108035051640545800d40141c10b0384d040140542c0c1c601907801d5140052060221070200200e0808a414418960705100300500c801c0075061002017800c03d03400007a6503444d003604c072408004094044c1c0c980c80e216076080d16001134440380e90703e850b10142d1500340301500313000050102640c81c00200a0b0b843d0301c034200c01c85000e0105e468100200c0c0b501d40b0384d4206d6420000c082c8003250740742d6840e0fa041c6810b59508411000754618000d45070702100d1002441604481c240c503102c0d603c14030415080721008011202102c603040c400c41c004e02450b1908111090381c2ea04041e520004000c0c0b190a00394002c001441450ba42c3e0040e644629210 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 740392769 1250 740391519 740391523
    0x90d030816110a08090d0f051e01020f040e0601120c0309110d03050f0304050102040e01030f05011d060c071502070b0f01060c030813060905070b0d0b0618041517010b12 74
    0xb48146466102d001e545000c200d42e80020007403004c01601c0c0b2055503c5a4030360360313044002590700716000c0d8007411490034203010742c5160071a00a01074009600e031210501060503a801107000c0ca548039940c001c08105a43c0c0559a09002003029038030900c001d003840540a40180207401003601c40800400c20010545400f42100d0712296058a4542c2094145208840b280e00000d10880381c40d07508020100d80c0e800003505890082d40314a070b024081d030b4070915010f825140b0340307410804c4210300707110070300700038440483c0c4194820a4003050036111903013401c0c92a050350f0326100c0700142510004c3c0d00804c0c0600145003502c40d60324440030b84640c1e40e90300ca0880d400c04500401400252240c6c010401c0410551103004540c4d000d690b002c11440c0c01a102d26050a080d07038484451083c00065503811103405004400305140f0441d0b1040c03d04024080d90681e1654030050f4902c500d0303840e042147d42241000079071020709404080f40c03e140c0c2098141034000c260907039400d07109001b12030402e5502040 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 740394019 1250 740392769 740392787
    0x206010f080a171b0307080403060c02010203070f081306060e04021f021216080c010c02011a031509070f0803040503070e0112201207030209010515120606090d030816 73
    0x2000e45900030550003007983c22200d801c5005411014044488002c02c032401c1040508031250141d00c1c019a59032a40c0381140494190305000c43c10b690041c020010316582003008204500240e0420365500d0341c501c3c58a100402150f00000c12051404002042070b086c012803651265200359418200d5000808040c0d0880007000da1080040e40300403421039080f0710610140c203104422a8480d548031485aa880e01c00e50404c28600b88160343d41d041c9001c00c903509020b007000c11101240c40e4a1a681d00b03c004c03a4640c02007070000c0d8030000c0c03598081200b030700d41000f44a00a1a07500702d0941640d483d16842901d991007441510700c24411084041083c42401012a0490383d504104c00440300c410f64a000e0070050b210710044440425004904080c0c84088002044401c04806045442d080d4410410001c0301a000540224a05114020700f21600401c5800d1715044082c0520b040d50303400002000c0d8400c003c036044d000a2040544c200b050780103014240a0421516104c0d00030707407003500448040311 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 740395269 1250 740394019 740394023
    0x1020c010c1115241f020a1703062404080706051e090d060914030315090901090f0f141006060e030f100c05311508061c120206010f080a 60
    0x40c601c0340b0a08010b03020a044054120042d00c0c4100158419042e1002407005d01c0015000d030b04070340d000b007041140507000c03d0071415000c4003c600310b051540100306003d101c00d8030300307000700d10b513140d8101b4014000040e2002000010116416076455081c010055000314080801504a14200300359180c118416640b0004000e02140c00780682c036250400580040c031030584103042c10031180ca2000340c0500095100b1034401d240600c1d0340b0840b0003880650034000b4000c10241c0d24003d049400071700411030001c0d003181c1108040d181ca4400741044003003144686600d0495104880d924101002d25810040498650b0f488800800401d0424591a0721081c040000d40b90040c90081480c41e1059011104007511071070310a080c50600880107020310203850700380e91040d03c0003520698415105080901416945082c0c5911701003804001d030280c3d10140040317100b04e500f902c10100583d0340049911000d0307040018401590b100b0b00001e502c0350000e018002c00c0c200b54460100b400b1400042d4810550b03 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 740396519 1250 740395269 740395291
    0x705030402030c0d2a17070f050f1c0605071e023c030c12181c080a090311010c02010c08180d060c0f0305090c040b0301020c010c1115 59
    0xf00ca40310401c0103c1440704400c5458000d003080c000d8000d0003000174040d01c61011080050040d04040c00c40d602003c03a500c074112036a00080051200c906080703485000c4501c1581c005e4200341c9120002815800f0003c51400020955500e8405019007a000b1500900e60f54031403107410341081404c40ca80c05840700031900076901000956031340d02c41100c0c041100d0480400359040101d0f0601d140181c00c200340480c250386910106902500e044c09001c5e0040d04c01d03003c440a8604802c021508181480081d801791003030401e403800107950100030b1022403269a2102019070f85101d0000d000c0d0201600340800d0341c2c3e80303403504201c941d2940510441d101c1c0300e80503113a51070175042c603030703206c1440b0ba003c40114581d20036500c4141c0f0003516011424104144a40f2000c14002d0b00000c004046920440d100410103041c001130000000340031a9060316920159008100300b000d08001c01e02921885061081c250302c1c02107180441e03035100c0104103d41c0c4511054900c0c12581c907107040040c01040d102c9103104 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 740397769 1250 740396519 740396533
    0xf05010512060f150406030309090501080d12021806120f010608131b03050d09081005060d11030703020a0902040e0a1515020a050601060806091003050714041409010b09070503040203 80
    0xc00f159041c410741c0a80500c0c550710000c8901c1c40070406640c49903100314003145048800744102c18181c01a140585030b900028040360070f9001d40144800b5107541c40c0c000f610f50005d80711040c41c0c9510740b500c680c00005001c495440e1321680103030315220700031911040c5d040501030021442c2c921650245018207000410120200e0b4a9190300d14003220b41c6241c0c182080c40420300000190f82407007410309103420b40e10f81200682c5005c50380d604108094041c200aa40351000300403480e6524104008039a803c280c41012080c80080030a00c0e05040b80c0004e9444a91441c0000781074103160010f0003621040c1c0d0a61005881d42600001950481e03003404e041100d05842c284000000d0b03220640d42d03409144101d841000c0e0580f034a0781002d901380c202c200014201d01c10840241020b46403150003c1d40102408006441e540300e481e210051409089410070305996161120b079115008445100080441c0c2202810922030b440c1c020144000ba1501500501000440003400b1b01d041d00d104a80240c050498 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 740399019 1250 740397769 740397781
    0x902040f2303070b0c1c1707020a1a2205031e070b0612120d0b04060b0c0d120213090903020c010c0803010b030a020d0516021915110405060d0f0501051206 68
    0x229007001c1c503d11128892160032100d8001c02414600e1b40d95030310303112035070600701c0d003d80c400d0540002006601990b02c0f413441100003030100040d00c112101e603030025240c0d41d00d407000d50740a54154980030041880c4803032040c100703220020000f0032005901865a0480700e440800c0b2100d03e004540c00035100030401d00c0011410700b03040002c0c8103c50128025035051480015004085400a003900e0800c550780d81c29a001c1400c05104030b8000d07206002c02d0341e00741079480c0b5056039190a80070b980401c01c00712aa4049a15510340c040e52082c01c0c100d00da24550715102c10302e150003045042c8007503005100d43d00710807600b0b50044c3c080d048404e4200548600d035a0811080252550014004034406507007000340010349281d0b485558040d52541c0d0f452509995100030017840c01d40180f282c101440c941c00c00e600c00049250b4210b00503034160080c0400d040150800e03809403070241d40d10042d04007000096a40c003602d940c2d4401718411400030403c0180e40d0700c0d4002d101c00d03c0d004c43d0904429a20074070108034 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 740400269 1250 740399019 740399039
    0xc15021605190308221406190905180a050a150e09070306020f090306010510020a230319020f011a1306031b1a0c06040f0c0902040f230307 61
    0xa9860007104000b02510342d00d40d55070130503070700041e0310b244200c0707082000c05805410840020300424060703140c00813110803040040c18520031564070044001e40c1c00c3c940c0c5100c5018186120007414000c140c59410200d0321380c031161007402112021921450200020190031403446040c0c403c43c185088403201e00d05000c1600700a40000e1300103180b600c100c80700000000c0350303400201558001541b126480b403202506041c90201c1c10b030042c40c401c420400f0f0300032846038002448448a60000d201503c0240744511010070440302001a00080c0130004104180300110b1902a8a20829a085506041d0841613003400c071240101e643c01500c000015a400c1d40c0b400d0750340c0429084261200249290340c940c0c80491007080ca0300200c0004454030b204000009000c50700b049207480e508601450005000310b00c40d1160303001000200201308140a45052001a814100250100f00c00031580d5a88611a04480143e20f2007039911004140000c54244000b0700713021840080043c00800300c0c2400e01d15012 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 740401519 1250 740400269 740400289
    0x30f02010204080a030507050d230a0309020301020c07060221031503010209040f05060f0a0f120f1a061002010219050d0209040203010905040204110a140a0504080a0c15021605 77
    0x856400784000306083e80103201c0d00a0080c8030792140b80c1c2d9a141840e001b800c209000f4000014001c52007258840c60700403d1501c180eaa043c48001603864803c4c08054004001e090302c06034042d0320200d55405051400039003501a10a59005c40d101602030071181c2102aa4060360b5480c11002880418a4035041c9240c0f509030a0004001509226094010038104d0f55044145900b40d601e80301400340038200300500509524040d0341c107046580c209011038018021622503107694844031003881080c0080f24a080b402d0700d41c4041020f003800032403450700d1660300d030580d0910301c0f44234a90044003110f40140b08448420483c0c00700c07000c480540c91802e96947d003010350308955483d02003004246503980c506c0110b010b0081c100000031241000d006100071101e103012241c0340301d001004040c03446504203100d12500312021100c1035845a031180b04a071300e40940d5021050500c282c1d01c444081000100d01c0c20f0035140301902d1040d0a00d240709c012070340c1e00302c000d5010481e1002000c0c2408281060f070100 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 740402769 1250 740401519 740401547
    0x7060c0306030b0a0c0908031815120a020304330506031e030c0706170103080f120106050714031303030c0206040b22050609060307030504051219080108011803 70
    0x1c02681d41c2e00c40000601c0220344c2c40031a80e60762030481a20542191143d000f84c01ca983c02142456244294100c410846611031841042e24000080780c100303040044481c0004081c018810b241840c2c1c0f00c003006074000740c80440e1841d401078030a40c134154601009100107641300c1e5070010f200444101000052002811841e0103001d40c0551000046001d030b88074440304881d01c002e56131840030018550400280703401201c20402c0e603036680c0b2184540243c04a05694000300110f80da900c070300d940d0395041c0c0301c0c0c02490a90410003400015210781c1041c05040e0301070143c4c0070340e00702c0d05203024816101d01c1804c0e00b90020071315202d02400071910401c0e001c102148090502850551500f50714244d9801c08900c40700c0c1c85130304a003021300001000c00803000501d8182c410b503042203403d5001444902000b40041c00b0190b0f507a00003024031404000c07428611400c44c030060355510340039440c1c034040350380c440c22070021500c20400090764080511130107490307040c800c0a2300352000042d6011034800540d079140c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 740404019 1250 740402769 740402771
    0x20714040c05042106020f0c0c0a051807030e070303080402041508191103010f1d070806060d0f0f031211031b0702060d0c0507021503070e12120f04050901051507060c03 74
    0x84038001745075403000382560141c1c0302c0c500d91602c5e140701d2480c2c60320700c0214255000b0740402108124075103604440c00f8040e255000d040704a030b034409400710010540380121803464480c0c0f00000003410303000403905018a00a450030710111081e8a2520440c4165104a540c1603000c026269030f20803403540206d088500c1401400b031280d807107400107429550f8194500c1800c56030791001c425400900c2d4480b03842d494641020f8201d06240c6443c442d102c240c000c03c258040e40e908101141007003035070390382c070201c00e03038400c1c50040a01d101c0e060083c051200920884034440c9401805045c0c1520101a0703031240c9102c2c80b4181d64103c41722402007194010400498000f00280030400002c01c00340280c1c007000405a885d82c2c1c40b041103004001c52840c00845e8408454010000c0c03051a56002e40c40d6000c1c40e0b004e45161000784007445141c0d1801c24003002010345800e01044035007590b02d035680208102c031000c50b40c503d42a42c8640c10000d024000c030900c1d4503031040c2040944000303017140d009800800c0740390074 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 740405269 1250 740404019 740404079
    0x60406031a07020601050319031409040c0905092a0a0302091305150904031e020708010c2609071211090a020a03050f0610050c030910020714040c0504 66
    0x40c503a000040d15403141440c0074041400c0007101c5504101043c0100811001014019161021142c09915000000e005c00c0440140144014210400c4401d104006402040544454607005041401c0d40c040e0900c074002000100d40308000c5120038402803030580941c80869030a0500e421050351102000e0002d243d001d009881f8590f40303043d002601c0c81c807020300c0425a4501528009030240000803014071601ca50028440400e9000211031101e18002d4401004001c080400740e140130859400301c0804c1d0b00300300c000d0902c25071101002008031401482001c4859108000010080003118140c2080d445083c013000150205086408190700a0340002c1450441c0408500d03000802c8070b0500344e80f500014558842075051140d2603220b01c0c41048050a41004400100c3d4038050750940d030200100410305041da04c4043c03007120341c2c1d568010301e000402c0c184140c01940301d00a41c8207404019070484100d100604050152603c0341c4025514130749014101450444021500044100982140d03c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 740406519 1250 740405269 740405273
    0x70f20120a030c0323040f0507140108010e0103110d1113050f09011103060118082509020c060109180c0306020d06091e020309150f07030c03050402150306040603 71
    0x11054812104036104416030300c070039030080501614401c1c03001070704144c40c203180341403403071024240c1e118013400040b448550b035141d90a280451903052000902103009052001940c2044251340b11b0b0991000c0e00c070317060660707680c41d104042040c4c00d20000e07060340321a03d0580f0140c9001c00e014045607115907480a2811a030601044c2e000c001e054007202c005030744a0a00030142c0f400352495030f2020101009001001c4075925045003404003804040c140300b105200c440240803c1042e8201074424581242c89102c003410707582100d07007020815039441040a0401203000d9406008440441042200512a50b403a2280f0070000f4070801000c1c8070345030000d1081030000381d500e010000055004004c0540c1f2360300001005400c8400661000018914100c0d50a0003892043c0e44c200306503e0103c40140c0b2951450040c40c00c002c141060b8410344000442048908494a4001c60203014695420080c005042009030200e51069a0282d0b01696055080c111540035000540d80118007910115159943e5 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 740407769 1250 740406519 740406523
    0xc020a0e0708010f051210050a02040b0d0b100c03141e0313110409021305100302060307022526010f0906091202060c03040b0604021b010b0414070f20 66
    0x15911100050321500c01080713100c000420500c081c0c14120351030b010815940b15070540e11010b40c050500d40c2e603120800107070040070310b5041d20700900505203051350307914980c8441c1b0002d00000d640309109085e02240c60b00d52a2240b2a04a00304e07a1680340d0000200000080b042d85030021081c0700c129000c42c1d03040c40c9040703040f075010390f000e00388080c10150319a4136440c0101002c180400010701503444c0013907010169407007070f0481801c064848400680c540314810441c100105682010350001d00c00070520400d030750300294004001e0a0b04910344d11070403a120614034958042e00c200003800f000c0c0b181c0825400c4800300060100941c00d0700018165501201c0101500c038200d8094070b5250352010032030144007251001c5a08000d152015202c00c5c503000c06012282c1c00007406c054800720030400001d840e501c035a4119244108142c03da01d0404248140240c060301c08005228003450a103180c4000d08001510928042c100544620070b0f01040040d088a40040c41032409031724000c60301506d1a070b1441 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 740409019 1250 740407769 740407771
    0x1e03020d0b28060807020c1306030503040b1815070b1005030d091d060102070b0703120230071409010201060f0305030310080d17042a090b040908030402010c020a0e 72
    0x905404403000c6220b50380e0403000e4031240e440341c1c00b4029003d04000815501007110701c104801241c8690340f044000343d5840013044a50401820352100003004070b00001d00e0300c0613003c400900b01c4007807a040ba8500500011040e46201000d2204041c4940c2000072920000b0030381c80684004203040d0b5565400009103045240b40403c070100b61800e00500035051001300c02c1700b0b19415507071a07070007038182080001d41e00c003405d20420702081404a0303968200b41c4a2501110302e442c0510741551900f1030864100a130f482744895016407042c101e04c240780185100b02c0c0445c450403841d200c82031702445005500b5030550104000314115540ca07040841c24065003010702e000b45000314020358491400200000c00200075030042c10f0b565101c0c1d200c0c44030b203ea1142210f65142034001c10307075020b07850f00d142c000e0340108000016500310b00d0071140c0d1300004004408010442d042141c0500c41604c03200d05110440343e1003040645030030380c100b00041c050750007240302c0109284080d0040f101c071a500c001c0d80d1f800841c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 740410269 1250 740409019 740409049
    0xb0301090b160503040b0f04081306020c010f030c02150604020f03010323150601031e05330901121406040303020309160b0a0f090b0c0a050d1e03020d0b 67
    0x1c084090289921880006102c9201c0b01d00300b4610710b04154036101c0744280c0c010f03d40d59030700c1b4200000030204070744e0720180c4680510035080d564150b921200040d458140c0000c40c0c0d40010906025403200d14400c0c00b031620360120580142061846805008800000c0140310b07540040e02085100354034042c0600450095001e1441401030440600c000503002c9641c1c1c0e000c040710350251262030700c00c061824480707030824405d00b00054001101500c84074030200d1074072044580392400e01008a0020582ca41180c1001d124184e4a0b5210b260424030010b02402400142c200e50300c0c030014824103000b1b81c15481d140b03004071b14442c210042014445c3c034001007114100d00194002c014002003901c00c0100198949514581654080c2060840b41613400703880c0e200410002040c0341c2d540301340c1c06044200080d11100000c10358a136540d036022070340c0d040f00400848d031074410262420115403081504a1001040a00800306240240c0045010750401900881115980d1800c804296909100004510 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 740411519 1250 740410269 740410283
    0x6060913061a1c020306190e04060f060b07030302090a030b071d030715050a030b2805060906040e070516150c020d0503180a0c08010506100e0307050904060b030109 72
    0x90704042e5214140c4000078800384220b01d0501c40e11600340100305005407422580200140c8031340d076501c00030303804004c0741e950920705603e0948045050325600250300e01c1a0b000724400d1017481049a841c50403038409100d44481240c0522001d03000078400c1d0000c0041560040451051a17100e485049400f00141c4100c40070644007141c928811014146c02103509004501074002c0710720340001c0202c042d0301c90000d2420403c002815140d014040d50059041400242c02010300d9894a403404268510541020312809503a8600252518201c41218000c5501030100d43c1010b20303210600d54464805001501801800c0c000c04014100580510401601400c1079211840d0795000b0201150b2080d6503010464108080242c080b9070400110b9800030388991a0300c025000b5080400d080034180c0c2401001109081c2d07000607611015000980a030000b141e055020b03080001e82640c02c1080d103588030b90583c01c015010485880c110100c19403040c000e00000c115400d000c00042e003114054402240e40c8 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 740412769 1250 740411519 740411531
    0x11120a030213141011010e07031419080d0504030207080a0602040608010e1302090a0e01020c010506030d3e030a0201150506070b0a0b01020a0c030c18051e06060913 72
    0x1035003000310b0103002800608000380703000080e00f000c1080340044400e000c081c4041d150024864060946c00f402025400000307403926140c880c6080c4070004082d50118640740709080720400306500c0307803140d40401030740502994904483c11001c01d0241000401c290154002c651001440481c1441109110303841084010303640d030309180010b0500715060300045a40c0c904202041141340c1c040c07190111507074045035040a556120044440070b4540d000004069500100c1c000e8010b2005400041c000c01c0304034290341556206040486a42d486040c44040440341545104141070080c0c0d00c5035425842480d400089055040006155a210145e0800140c0d0344d2540e0041a40c0021100006000101e40f079509d0900e4a450741d14400c400604481440c40d658042d000307050b030082110540c40e0b98020103007001c0c1c0d650b1b8104080044480e10440304800700c1c00d514251502d40c14842c00b031203078289000c00c0d40056070090300b07a400744000034007598000ca810800520940c0c0d605210103450040c440001c500 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 740414019 1250 740412769 740412787
    0x302030604050c0109060e2d130204090c030b03060a0e0114090a0c08030f0d0f02090d0c0609120f030c0213020d061e030b070c06110f0a032a11120a0302 67
    0x16440c4c0c5640f165080290310307c8a80380030754408048007000d550b0348d2907040440722900030384503201e941e03000320981c40005e440214041401c1500584201c902c0ba02c0108840c0b841030000354151512810040d906401c09000143d140680d0342c0039090a08104000041c0000310b4036140c461584180d920380203960140d88604204405020503601038034140c00614140300040c04660b50764000e44080003451071300c429081c074107414554141c5e0b104100041c2001080704a42c10003440120440c0600c5001803030f12280401d0480441d00c50001e041e03070065901d55051103d40b4125000710000c01d08030390105076011070390040c00190000c4e00c42e00f01d11a0000034060f00e400c0316214103846400e880c04545480c10345c100046401c000f0660791011440c108061012440d01d4070078010300000c00118032a00e0003151081443e40c282c806400c65070b990f40c5007000744200c05c4a6001d02e01c0c0400c0003030300b44035050ba002a440c030780c4a000c0c0079003c800c0b800220f4071203480006038003040c1e4208698441c0042d07800728900308 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 740415269 1250 740414019 740414027
    0x402040510080d0c051903030c02150609010504020d021c0606030612050307061d0a0f030f0c02030615121e07061121072001120209010915090302030604050c01 70
    0x1800c0010220140c1c1c64518181c1d005807201d201104035001e000c07803001d018082c49414040940401c62020003034591910f145809070040c28161000401803040c2400c4400130407c0d19070b81c40c040c110007051190703681c2c80d280401c006540038060100c11240c082c001104100300c085248a0007020b0401c0c003045542c2004401000c4410715400303460b81406100b4002d02096002c030403511059049140402c0e80b0500c60074070342d40403610207a0592a40701c0c3d05001020301c40400b000820451282d80e829040ca0b4240004580b42c80006901960682291000ca840134510586401d18401e01426459801c00038980c3e0038280408600100400044240e8484440a0a000010140c003060a002c0c1c0400d41c1142503503540d03c805801c5d0036281009a058a100401410a5404d440d600c5600c07030400013944660360340c0c503403001c40074039000c200e08003040c4142070356074000d594000c841070f901c2d01e4009280000c01c04040500e104000203000c1c0e03540c0c010002d41c60500000380b145000b80300078400500300000043c = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 740416519 1250 740415269 740415271
    0x204090515040c1d04020706091b090b0f01050a030b0a050a12050c1002030a110c040c03140a020a0509040914065101110f010e010608030426070503070603020304020405 74
    0x104220500c0b9060644c14801c030f00b40d400e50b60042e100162100800c0c54458000c04440d800504500304048004d50089504061441901e80100003032012106c48005c6c814850341c0c000c00c00b030119509012112183e407283d44540e0595500500300c0706140e135103401080c002a6a40c224201e00042c80e100e030014440c08200e01290b0541c1650164080c080000f0020340768002c01c05404200070250382101905041003140450107600107008220380200740c80f0240044c20300a1011500140040000d030a0035050320a43c0c0c80044140c41d05d03443d011500c82000002d113800130040b00c8548a14035180d00d00e0f0b900f0418603108014840c2c808001c80081c25040c41c03a40704607000d03aa0340c1c0509001800c035001c98030549d01045403542501c6100144502d0060300c20102c800e40c000b009100c1c14980011100054021310400f14401000b045815202e54403641c50384110b0003807070082110500c0070a11108001c0407099035962520540d12007685a50010741045c016604c910b0001c0d802009210079850244500f07 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 740417769 1250 740416519 740416541
    0x60902040603180f12030f051504050f060105030c2803020c070905010315050717090618011109100c08030c0a0905100c11270901110a0c1104020409051504 68
    0x4070b02660184e62102a0703007819190040c2100c001071300b5400c420f8002c0c0c002e501c0c07002940c1014801c5107002c00c1c40809200c0c420321014401ca0a0030040348100700b1003480709000c2d84040e50f445245556412240e6650b0384410304601d0408505002907503521200e42c501e80000d0b10590f40541d075200403007801c07443c0172101d40056407098070300b5004000003402503100e050198210320380031945941e8403500351210380c0c01038180e851040784030080045184c00480c02034030900c80915016000030220045a00300d4500c0680848107003001c000e02d0038107140c10700746c410000344240340c0841c0d030100b50754844415400c03e1351a20409280400d88503010354001190b00041d01042d900386880707416920006107007607065180a424180d003c8000150381d00c8a40140842d1171558408a0701081040240cac60291011147c04155500e007200e030380d80d004454000c4902d5480b286d564500100520386a0040706201c0e01340140c1e105500f00000515041d29004091003100c508400c651a8a6002c0c18881503c1c160442 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 740419019 1250 740417769 740417801
    0x1031416090903051c061818060b06130e0109110a08190b04060b04090e1c0810030b0f04050d0305011809050a0203030f0c1c0c02041e060902040603 65
    0xd004030080e8100c0c110003100c4240701c0114000e200307810103440d03601c229040600c2c00e10450305210040856034204d00215208640305425480000114a040701c10100d4109030f03503201c1901032004201107400403140d0480040159203000c0315114810700c941c1c04d0f903010043c10109032004109021440c0315100c0300d02d031f500b02100c0c49c2040d4150000d019030b00041500145c512201603000c4040e404e07034010340c00c0300d0024004000050f00d130110b80c1c905400500c1400da42900300394200c0c201a4000c41d51107504820030b10f4042014003016016030b100c0c0c8008040c903140d20341e604000004154040c54007405524016a42404d504041c10b140d07080c00a04000c1e0001c2c1030a210041001440c4d036072040d121002daa00d80080c2c0803856107084c50a14922a0001e5414800070440500c035642d060010001c50740120112100081c41e2010908480700c0d0b01003480103d00302030015000350800d90006480c60f1880c00e4030720701c1003041c0d0302d0740c10840d01160881002194041014800c403074062049281c07541c6100c2c2 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 740420269 1250 740419019 740419033
    0x9030303100f060e010804260a02030408160506041511011b1806090b160c061709010911040b040207020d0809030d050301080d0c03180905100b091503070c020a08010203010314 77
    0x207006d5210103080240740c1030041d4254000c0d0b00908503507404041180d04002da8811690200079500d41040c068542c99000702e6070303e9802c07103001d8001c0c2000c0f00e8001d80842c0c1068500b05120b0b00c4640017030380f00d01c244490388501062209081c0300d07070311003100c0e880e074910021440481e004240301003060803c0000284003209000c1142c11014150894a034402c1e15550390a0900b8540d2441c000190b00804c02440c82901080c010740210100c903441c49012603108040d038038214200e080e5964003401611824100e08101c00c2070401c2c0e004000d2000c00940013502d0140998082020161144400e8918070804180c505461809124210200c00d080c6041ca00b03550621000a403074024036003a100c20b00c004d001b0320500701801a40c0c954080c1d60700d02c41703000e012a0f031a00d03070101400d030449040e180301043d0700010840510110540300d40c0700001e0107400f4503080c08802a0031540c0041c0c041424000b180e8490030041e500c4c104044090017204001580f254554a06201007501c00480038102c0d0300b02d41c2c = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 740421519 1250 740420269 740420297
    0xb04020c060117030405090a02040819082205090a050a0b0103200d1b02100b0402070506190b0a0803090307060305280f020711011d0d02060f09030303100f06 69
    0x290306064a0b40e03d068101d64806240141c1c0c0b40d84110340c041c5030418a568100150403206c0e60150045414403810389594440040f10402d444400380381c024030641042c071078241c442500c9807421038a0040e2080f41603515486000240e503149013280c0d1089019210010840404881d006118006000b030034248240708066499401c0c0144031002c107000d00c03078081010310071242c0c40c0c0c002c0400c45685100e001c00071103075660000d40b50f500750744a140c480f43c203100520016081c207208a94030076412502504150700d1b41c10503405480c0c000c04807a8115a03d4114850b11070366180007042c01018900000c59031640c2640c1418207154044c1e11040601d07203064200f00440741c0c0208200c0024401001340003090204400c40700c01000c1c14600d1502e064804201c0d60f0030000240802402040c090b00e800615401140030302c1c0c040d64100c00c1c050740200c940e04000c801402d0403809001c403140812940c9091450920100b841c41d00101c0b203810821501610400526008981c0c290207412145841d082c031400d08 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 740422769 1250 740421519 740421523
    0x6040909031d0f010c0219120b010b030103230a0c09090b01050a030803060d051504030e0909070b1c060b03040c0312030204060203030408091f180e01030c050d081b100b04020c 77
    0x1d000c205040c4034040e12a40115603626160040b00740e0b141160b81c1c8030603110120084003003236043c41120070050300d20000c10010055000d41c1d0480340e1001140c2c024100f11001d04448984c0481047d5952003a0300362000013551441c20880940080700c400194503900b4104029480c00c181d01031400b0b80f800c03180510210385841f089a9019005031128000f003212490094070302922081c01c0c03000c1c691240284008c05178801c0340700f1084003003101d2408407901c0d00045592280420301c40c0c0c414042082192040b140c0c0da0f000d61040800030703110009240c903a40d80b40303843d041d88116011190340301a400180704210201d1660703004426249001c609050038218040e40e244805040030303003000e1000c540441c1b16951815903162401e001c1c1c801c0d16401c4040030018142984409998080215899000c92a0459070300c1560403242c00c81002c690641c540380500456483c46101a15462030070441000911545c80020000e00a413030018030f40102c01c131952000f101d014521151013580100000c460308800 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 740424019 1250 740422769 740422789
    0x1608100f1e021b06190506010302160b06040f050f0402030d0203030f0a0b0d06020c0f0f0c0102120c0f06010f0501030b01052d090d031101060803030115140906040909031d 75
    0xc0c80001a51482d4207090025250703d0401d0f5294184035031001c200039040c1551001c08550741412042c081501c640f8015400d902070340e2407044910040005540100311801c80807a08a40003801c0010a030300c0040c00b90080e1042140c0303410140510609101c210304040202c84054507003880a98154103003111840245503000c0d007105c0120707468400e040c040f90751b00038072441d40d00c0c3c3c0032a0441d40e403801c0c501903d889442458140391280100b0b0380a600440e0007044682100d80305a000d4140d810701c020b03c4400ca50403803000d484c91842400380c4220000810098070340078181c0542940c82c0c1c149800001815204d889605d5810884207100f0424900c0d0000c9a402490091041c245240c00c601910403001d4080d4076610355001c40707081916824113800c45800f20108844500900c1a00d032241402580d0344028410500b8000b01e03da001000c480c840e65040404503c2c51007003e1806100c0e20000741145c115070000002c1e285e544901c0c004054210340042c952140c0c4820986080c55a0b40c00103418400d = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 740425269 1250 740424019 740424071
    0xf0b130b010e062101090c150f110c040c11062a09040b04061e0e1e1005220c0206010b04120602091206010f0b12181608100f 55
    0x90b0a001145043e51500c40143c0c0410344120f1030a0420061020940600340c641015984401020404254050000701031400c1400503191040704c00c00c084000c588041030390000c10f0381c0380031b51000b4141660300c50040f034940c080d2540c0c0d401c20b0b203402d5845031414040c0180a90604100e03d80040c20852002c00f010703007031103c0d0310304d4064482450101041c0036022803080d05a0040c60400c0224000011058540b00040840340c40c4108648607a4090081c4006491265006081002d0410090f400d021059030000c0084e80f04c1c15115607035030119800c515030070f007028500001c00c6854407038402148102074500c241c91000304102d5140c03208402c01d80c4540e01610303410200550070b0300d0501039150100c50321104007030020001243c0702461107032079800c2802462054844080001504035a080545030b504544075038414154461040542c0c04000741041360860f8000d60051620441c0c0c031a440070000c1000d800906840c040e86000d400455001528450049140924500041e08117002d84440e081c = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 740426519 1250 740425269 740425289
    0x9051006030201081536090105011e03110d02180403082d0a020c0102130906080d09060509060310030f0302010b03010c090e0a0f020f070503040608061503061005160f0b130b01 77
    0x2e51410386c019142424010010a8a10480074418040415072025040321501808a0302211010b203513818180014440a400b039400403401c020246044140e0340d09484c40248030f08002c0400c002c41541006007141c0c02d0b00400c811500b04202d0b24501c1c0342004200504100c40442c60203003a2214200c7e42d4044c00286190368007055070321800809504807800c80b084850840348103903881b2003200c0940780b207005400e954000e1400f01c1c007005001e2103581d42581d456490301030400140d10144007494000500c1d0385c8032501041400004200d800c40403280d001c0c0250b00102d02c9076003401c141420b603182101e00d83c0411000941c01c10000d03a20005803904100300a802055101413000017034060f014442403400c070070304002803034400c10000100810455075661101e184a40d6003d0400124441c4884440006003041002400f14030340501c080300000d0107030901da4141044042136000d13049600f60102c030030290b190306034020700c04002e840e642d2042d10640c00300b00204042e941c114040d8018401c0403020 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 740427769 1250 740426519 740426569
    0x3070b0402010210060803090a060206070519020a231204050d110a0e10061b080d05090a080d0606092411191a1501020d12090510060302010815 63
    0x16031080c490503106588130001400002e845500e619103a03400817605500c40d07034055400096950000c9070080c46800941ca8141c10000b481c542c10400c450505d40d02c400310300079000d1040002c1c55100c201e400c070104e6554102e480200c205a401c3c41c00504040000108500340400c0015550740381c0c0000c800ba03480b102c9d0550841803100030881c044030680218610b10340f40c40070449a415124180411a0000c0e0384000e201c4112804100094000c00000b80024a040000c20001d00d0760790401c3d5008103400b41114500349081d15a1400350f00701c0c4c02d20f03003541501e50300c080084640c8002404050000500c006a40c80e00b518a414030321300e0034021440c180302c04088c415400481c00d1050246a81026a00480030521403070800001211810b0381c0000e06111408124001c1c52303411000070403903040e0000c02c03520201940564189003070002103038440b40ca98282c90000303034050103040c50300841d095002c1031490a61001500e181c100400c1c80c4510034462081c2801d41d91044041c000d6104000d42e0f074060 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 740429019 1250 740427769 740427773
    0x19080913060b030f0402130504030e1e041a030c01090b0d050c2803180b0f090708010f020705210f18030102131410050301090203150904030c170a0203070b04 69
    0x16050a5105410b52200031041000d00c0f052507900501c83ca10840c0c000106020400719070040301c8055401a0005580c00c4101220741040550000e00048000c5e0b000000d1050740000340a4494100c00c40f1051502e0b071800c2010750500708440400e010b8242803500c01c080c01c0c02100007440c015900d4000c802078072040401c03a041041021141c00710004201000c08c41e443c41241c03440311041260400000340340c02242c01c69074001441c243c404a030300482055903503c3d1441d41242050b00500040740e54000c1e5100066502424891400c1c102007000f000341e21080c182c01c06500304103000b950300400c0c0c2c00f15800c2d5000462401c1c1207a20000c101610303191201c1c40030107040107925100900540561000550307458441d000b100c0181102c001c505111070315071100e001d00808608071840d002c00b140080c40144440f10881d0051341e4460b03181e081d48100d02440c82c00141c4007000c01e850540104140403800414810170055910b1800720342180c0c14644180944000c1d48c1e840f8800c0090080d0490902040c2 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 740430269 1250 740429019 740429021
    0x90604050306010605070c050604060e041d190b07020a020a09091109150f030d0507020906060f04030c0f0f060804030518131a03070f030222050a0e19080913 69
    0x9000c0240441d9070355a100e10019101c1d40c0558400c4e20078019a1000041c1882e00600b21025681c003907070360400c040160414040074040c0101d8460704400b0301610140c8003001040700a001c90112b400b110000c1415003403141c0d1603100907080d070085421204c0c0d0b520160f11030020140031103032a1803000640300c07503500b018104c8583e0b0044041e0312145810a03c075400704030404503c2a880708031303510300c6c02c89114030400d96100f40300c80712100450018803c00000d4035208025a40c84507010305a6031414140581c40001503005800071102d03c12280c90500c1501c2d030429000c070140c000e101100c50301908115000c0c1411070300800c010100500058280d001c800c4c0319048803240000901f14030080c00f140c00403900903106402c840980c80b25040403e07580c601e40000c61408440d0444c5001c6042da0841e0280058210b031940a9000340b085240303080403441b950712030b551145a40d0b21002071000d84040c0130318100700d0300c406100451a4011820004070700000111001c4060840750003840d00d074074014140c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 740431519 1250 740430269 740430277
    0x504050d05030c1209030c0d1e02060706051e0c0301030b0115020c0a0e01061713021002190303090308090a150203060a0b0414150a02030301140a211205120a020906 72
    0x1143d14011880500d00d9014184003411200c10110280c2e2400b00c026021302c50445280580a00b940c1400307041407002c24421a03d4104450010703084901d0000300d900c5000c01d031041600e0f41e80c461900031000c0ca100c500c1032507409030400c018104003440c551441e01d5a40700c08606008081001d01d40500c0705c2c01481c000c101c461424880078003800c4d500780e52400300148000c0240b2641001c6806141a01d000c3c030201e0180a200c0c2c88400d2007038442c50382c00e0302403100070404d89400c902544500140e00da441c0c0004103800741424401d58003c076085065250040000201510101813540640704500c0010b0180f441708204600072400143c0b00da80305000601c1d07011180e8030196a400c800140414450480c0c4204e02000310152001110f07464107a6a03410a4410203c030000180c00500060001d68234920340c0d003c40300401843c0d1407146441d03417240d55809501c440c0340c40056411003a0101000709000154503907203004e00384182003505000301c080044030014441c02c1c4042d800038140c0d166075142c009031 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 740432769 1250 740431519 740431537
    0x2030f0a050322031206060c081b011119170603060a0509030f0705060a05060a06121503062a030501060917120a02030c0c0a030201270905160e030705010504050d0503 73
    0x203044002d42c00d020b00800c5c40105903004080c10000d001c14014080d0031400b00b1541e01240c07181c80c100c4050900101d01e01740311800399480d529150000ca0380c02e600c4d00504004640c0c2010100068108800585410f003200114030b000380d108010040c070303681c003c034009520130f80789440481c4554604180500714891242c2c510020100424000107100c00000c2e481e11440c1c0320001000951200d004105040003203200700d0001450024850503001070b02d41004c204035207070007007000300b00341c50b45c0c0d0340c1050340c0311103268900c0005050000300742000340303114a8071680e078107040403c19541050801400102940110101130710359094400c0c0c00d2804001d5810303200d8004840c0c680b282d4818000035100d03402407a0402d40c51080f070020201c00e00c0c01d46295000c0381d505071543d81961080d8001e60f540f0042c188080ac0d0400200b00f000100d0b03076500d01486210b8171410601001428040c800903100c1c0840403134180c025800124244410303608042110b043d00c1007107909840d90781291800e02c0c90340c8520008 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 740434019 1250 740432769 740432821
    0x40c08030a0306030209060906031f091e02041a03032706070b070f020f0d0c080910030b1c0b010306020c070305070b030a1d060402040213050a141002030f0a0503 71
    0x44107400e81d15602002c2501d108a480450544030803080040030380064480c980c0c160401600c0d100141440c089003103202c007031100c002c10207800c1911145002004400d040c0e2050400100d01c0c070462030301c1d2040bc48050300c1c42e008170505200d6400801d83c1ca0103201e10211049415801c001c18402d00f40d10841a45d40e0014001550350315146040310201710141c41050205010701c1010301c8903400400c464803541143c00042042031a010021101801d000c54280c035072000c10803042440e512044c100d821091030640b400b040c0681e500003440581e00e60707108401c100240c1d40c400c4000050100c98002d044903088040540c81c0e68a08868074100030480d40001c20901c12610000340e050340030401346100707502c20201003010410807140c2c1c420726002c1a00450603508180d00180c0149400e40c080c085c403041e071024070f40c8055181c6010404c070000a421200d4a04120442c0c103000e0318150721310403c0d07407800d1b10286041c0034108d10041c04c10700450b01c00805000c0c01100140c400249192038016000d20050 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 740435269 1250 740434019 740434027
    0xc0c02130605010f050f19050f030906070e2407110a181103160f09170307050706140403110402250309090b0f060c0c0909031809070503040b040c0803 66
    0x80944020702451094601155100d05051003480c05003086d40c2001d0403104210b85402085900702c0c216a41400c0c0f003205020701032281c90b4074500143c0107184207610b40c100400241c20000005044411468081ca205d11000c60031000d4079411821030062202d5411a96911404585401611151494079068104852000004490000c040072859000d072007001009003c608030380c10011840212031118912a51800c04040c080c4600c80c0005090020b01d0016480c03900d0780395050250100c4c507030343c9036140c0c0f0220b564018020180000c2d401400e0300d003002c4110382120200341d0714034000c80c40302800020440e81a200c582d100c03501103401c200c64001600052082c80800001b05200e8404241e00040050358042420a100c0c8580c183d01c9000502d0071b1903181c014000c03c0034551000040c8015030158038000e40c4141c585d030b44024000e0640da8042c40d02d0310480c20782040311410f070103010351050307600d401448442d9030030408480d00103070050700e60301982d62941440c18942e5007a0f40141a01e2000103 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 740436519 1250 740435269 740435299
    0x8250206010e070314040f0203161502121801110109060230010e0c0d0b0405090601180b010909111e131a030c0a18030302010203160206190c0c02 64
    0x480c6650580d080030300340550075110540c048046600c0c4c4a80404400d00140100d00421040303494090010300c010101c81034851101040d0340d18038507540c4000c201400c031490107181660140005250580c00c05c0701c55060000001c0380c1511591841449030501103442408061a0000e40141b10240d404c26000d65a0710449030610380f40e203400d46403001182d24034a01489150205101940c120384400c000c80400d0380b5901c8100641d41c0c488046880c140342e5030454a03a054560f8050705205030002405455079600d0401d440042000154400d551a13242c00403115082e0b0b04510303c48142d50200c00001640361000e070100f0120701c6804441101c415400c3d030b0b004503d1507d1002005180c00200c40e10810036940c040400010f8100c88030700c0c004200603c0000c001041040142000c0600340c685400c036110310300010404110983c005400607500001046010710b2249580d4403542418402000700c1e00d483c4600b00c180d014404952424603441d2500842c1c000d100d558502030603600280340100c036046034 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 740437769 1250 740436519 740436523
    0x4080a08010803130905060402210402100206040c0b030a23010f140f0607170f0903010b010e010c02040e0c1005040311060f160f1a1b03070906082502 66
    0x9848900050365000000c1001407020040d241e10301c0301a68515007040c14550400c019043c02051150443d500380703c8600014108540c40c0c56402003903c04000030b0a160060050020300200c0100641d440101400006900310020758203d41c1c0b001c41c010380302e0b101d075001c1c01c010b0680d1800d40c04291031038064100d00c0503560840e41c4d0480e40c840d91707410002c654031203484a1440e2400180f5600413110410b08200741051030041201c10b2080e007250301e02180200c900c4400d90000e1106101c502004559000e50703050134410360307142400c2420800711945076600001c2110501183c002e004039160b01003040d03405c80070801441c1580c0028280100517458200007402c07504248010303100000e87d0100d00245040000480e00e0301c0407d601d981c0d15004c85040861003180c03001c00111004038200723000b18041919140c8148000d03800c0320304c0c1c030f03d142410405859040460309119111841c01c00c140041990007500003400c5900c2404c100c1030554448040404529213440420041551511884205940 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 740439019 1250 740437769 740437777
    0xa0305070e030d0203040b18030a0305030727060309060f1b03050f15060a09031b151d0112140a0c090b04050612091906021806180910030b0408 63
    0xd0303a80e03184078181440c109640e4800030b03589000980c208010520854800c000180060381d14044da070102102c3d0707840801d142031100d440542c0080d1001c010b01402d036920501021644180110b0503061400c2261040488000340c411042070540e04d414074010012140c010408a07400c00c007042001490a940ca089418848100d0000080c600000144580104c500450042c05898400301d2400c200d035050010950005000307000b03000c82d40c1400000111038000c0d00640c1d0303003580305070340045292480310400c0340d2000d110281802100c1080510080681d003000a0300042403a01030690180e44c0070020003015068a01c120625000c01048145200d03070300101e442094076a15111015502ca164100171f000324000c181d8000c000300320380d007400c40c0018000c40d00400e140042d640e0100704500102c201210316401114100e402113090811040780d00820140d440c0e003079900034a04211008010030004101e9646407094841e8000704051f045007080110103982d008010b90300d541024240789101d608 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 740440269 1250 740439019 740439031
    0xb070201110403050703031803060c0905010f030e0a0618080d0b030c0a0e0103060507120203090c01110a020a03081e071b050a0e0703051b0703180f030b040311120a0305 74
    0x1c24910160680180c00c030469080b20703041000360968504564003251149032020340b954075100ba0800100c0807030403911813a000142c198460f1101caa00d8100007511810012084106240c0792a80b9108005008101030030200e9100714000f4003048900d941140b00001a880079008440c00b04442403480000c1d03100c0b81d140312040741240c0c0703080084000c00403a5040c07801944103209000d00100001241034000d00c0d00091103040c05a0300307007002591b00d0101d030000c8518440305d9020000c000401d58000049903458501070000d1b05041d140d03900072488003802844000c00d07250001605800da620151390469582410840d0305544102c581000285c170b13401100d1401c1d200c1084a0001418600001d0041c00c03100403000c103008075030718900c0580003050b00400107407852003000c04001e15607103010001c00303465200e41c40c0d2011002045110300c094034003d80006002c03c140710000d001040c001107034264081c1d454030341406008404076840e8200401400c0302010002e0100360055090341642200348920 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 740441519 1250 740440269 740440271
    0x20c0d030f150807090e0a0b07052101050a0620070f08060901091a1005060a030207050601050319020909030f030a020d0b030a020f040b010c0506270a0c0509040f0606030b070201 78
    0x900b584803142d91240b141c0b04004003540000810040240f6a0700843c0c000554001a80c48100090f01d0b68000000704441600c00208005068404c520100340000100304074460500041d60501c0c01003690034065004110501c0700400b800000400c20140000c40301c0c1d050002d6401c0e45a684000d290480164080c20805010b6034001440c1510144500941d030b82d000030385001c0710304441c002000d0182c0080d01d100e5842400100100e0207454480040114000507640140e0700c03007090400605043d81a04018442c3d00480300c100350200c441c8041c0401d85030120b0300c45011745c46810109140d0300c9800d00460000303401104001c0152165405014008000f110900030ba9070780c1420141c6540303098070000c0d40105220015140360605921248000700b06050482810b801900c1d628600842154410448211850707045c0c02041c0c0c0c40d440e0900e028244000b01261030305545e900c103040c0d210740a02c1f406010240000b60a0059900140880582000342007003090345a041003030380410220b0b01003000d5 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 740442769 1250 740441519 740441531
    0x120f0a050405121c06080c2b030c110d0b0a0e01051902030709171612032a0f05210307050d050a0621200d061a03030a03060e0a02040305031c020c0d030f 67
    0x10390f00c11059008081310b010f071406508e84956034191828072440809880d00c503003c0740724440c0c0c1c0e240c95801d00480c0f800b4030280703019841e040443d001602c0e00c080050025906100030b0240b101a034094200203091a08009600c0382c1d00c004007212030800030360117405020720709281e81e2a40300c07003c103614045440e0003a40300006900d404002e80340007a200e00040c0003800c649d1911542d08406550000806480d0b5100d004984054136680d0841c40c012805a40a4002e5900c8100820082c2103003c138a0760100310381c0741189403c103809020380c05040710840280d07490b200000c00301178581c0c8c0070b44090003882e0380e4250380c0146000c0442c0080301181c0200d4040080380529110100100b050601a0034000c201c0c403080e11407030755003070301920810715011030a00c080d0182001650f014406040350004507a400240c841c60302c0c20101078403e0141001c0481c0384100028004581c012007103c00344186800800310144c4665041c0009102e106100c7c0345c1d034000e0b40000070740c059041c0c00200004504030424007070 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 740444019 1250 740442769 740442799
    0xf0d080901230327011401090506010f0f0f091205150a06121401020706110a080a0b09040b1e07030213050f01080106080c0d02120f0a050405121c06080c 67
    0x320051007008a6492200b4400501401e49800800045180e0b1102c1a01c03e004c07040d91003429142e4102150419201c0c0e8001808254207510641d03074003c030700f4606239050b09200f110261802401015000401c001c6100c4090340d140200789101c000e2a00c1000714110070300d10308086440b4030101e00202090032802d404142a4015400307180e06071092202c00d024080360942d13035000103116443e6010301554003400180c003c00c140b0f11410b2154100480c2e4142e8a08400e4402080c000e0020710b8a04214985203040ea01038441e000440d504c180d000c4407a2000752282c0103101010041450701c2e2054140040800101c594190040c0856a030784c005200340d02516001041000200e440c18a80000d41c00d1004100d40d41c859059190050a0b4690b45445c3c00315443c1d40c0421b84e4050f2402414030040e070310500407038108051010764420303c02c10080000d070619640325525100b182922540b01d01010800101c0c102240224540100e0100402c100c40350740d070040d950311001400005071044510b0007900ea2 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 740445269 1250 740444019 740444057
    0x70f0305060d05030a110c03030d0b010912080909071b05030a02010e0f121303080c01060f120f02010807050f1204050c010801030c12060e030c06010918020901090b0f0d080901 77
    0x4040e40c020007139801c0a120440032502c1c00b144d407070008903621400483d9601a10140010840c10981540210300712140304005010108241e10241c0d89400b100301c502301181018044d80c0400008451781001c1c2d443d00b880890704660301c12852002d44000004200070008008010701484a2903002840700d6101c900e88a074840405601e40c114682201f030302000210071803001013694000e4144000c0049842e602c601800b9000240258000c2c0c0d0742d91810b200080c8a05150700003050312030540c05110240360340e8807200c5003046100a06000003400450201390140c0c05442c00041920344050b00c641d030321203d01c03080c140c0a96040e103070f900620a440c2115403080c40744038140c9170031012000c84a0703e011060003003803180c8202601d0480e0342e2002e1940e0800140b00910001c3c07400c200070002c1d541003482d50f404895641d00802c6240c1c0b0700030513140c01038489800b29811609110000981007840344081103082c07001c07050075075114a103080e9407030400001601500d90b009082c1e0f55009802d0b2411340c0c030700c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 740446519 1250 740445269 740445289
    0x150306010b04080c060304020420120c0a022a0409080304120f17040807080301060509100e0a0513060302040203090d030e0307112116051806010f0507050a050303070f030506 76
    0x1c0d0700b0b0b00080213084a9040100045402c5031000d4800540c2d106d8008414106003103215200d007000f840010005481c44800107555007050154a84d5031404084043c0a59285c100e08041400e14540e204140502007100380e142d800300390085d0081c801d01c42e0138900f90015510448044400c0d40058202d106810b100d011501c609400315110501d46100d4038600300b001c43c43c02032040b101c603c010020321000800c0c0c40003840c0200f100b07446458039045140208445110060800c0c01045041c00005a142d604d80400700300701c1d442654801500c1c000010303028003030b00312504003035000340c0008203110000100150941d501d03116542c04002030b400014409440e0300c213881000e802c0301076116000815141c52400f00c1006010706030107485924100c02d4060030504590000350190310f8080c2d003044582084180070000d548484240c0d030b424549040041d0a5000c82c46800c420014041411800c201c0704002d0080070542120441c0d403a850000d1005040074403000c00c6200290610b4041402802c10301e03512 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 740447769 1250 740446519 740446529
    0x60a0b091509011205101a010201050912030c0a0903050f0706120203041505060607050604060c020d08161b0b151c02030a0312020d0501030f031e0e1c0605150306010b04 74
    0x1c86144d103084440b01c41600c1e80601590240100c120220b543c2e4068403030301c0141d10101c01c101d103092070b10304001782c00c4480080070202d00360031000903003868244420440791b010104501460712030480c5d41084030304200603000107181e4411608130900a880000e10403049641079a00c2d50000d01098000b081640003d44000b4440c0e0b44500c074202c00d0040e950400d07603002d100a080075090400a88683d45003030310546003030351610307500c500245000e0b5040c002842421120b040243d082d04000f003100340c50180410300c000801c00c1c02429080c000d01581900900f540d00305200c10b11302d0402c48044582502214030040c85220300412a010b4812403a00b0b450403540c00501a00030319060361016121082d011850170526079003080360031040f14162042c0350103103001c1d0030081d008003914074015000780649801c104507000b0400c803085c0e040303600418141541d5001d45652000b000c0070129143d0f010f0012900605181c20b1404218540e484103050a11a490482c1214856640c503810320826116500032 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 740449019 1250 740447769 740447779
    0x5090d0507020d021302030f01060912030e090c16050c100c050c0f0a0807080f0105071704080706090803181e0304090218030a080309010b0114070b0a0e060a0b0915 72
    0x1c0c140143c40c2c00c90b0010603250028010004210070701c000c2c0412a80100c0d451001a0f000f44010310540e41d0000406020700180c460b000e00c03016950301e005e483d42c4140071890340304126000c002015107003580c2c00d980d80826107082c5c00450103480e00d00705d6180c91006042c00e02844d10a08029901441100c0d03e01c4007a80040240010700c00704000e110a005c48111016000880c8000c001804001000858002d10309000602000000342078420f09403003024015900704003c2c414003880003141890201d4200da40b14903e50fa4850312403401c840030305280c0c540600310400100811001c1c4d01c10900d000c0044010000faa00640d01030940a040400c011381c0c07016180c0e105000078840080d040d07009040002020000c10038103449900040d00d0300411007011129020003000340009401d09000b1101408024282400c00e40343c00a8040354034003607080040c14402c00308010030b001e03444951101da0048840d100b69405480e0800c00c400181c00001545405100c406000484c2e01d1540130b0301444803200208 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 740450269 1250 740449019 740449027
    0x80907030309090c030b13020c01050c1e03070309050d092925052d0601060c0618020a03051606030506030d050a02190c031203020304230c2205090d05 66
    0x100302401031090424a8007416541d41b12918955140f048001401d1418100942d503811001d034118203680c0094603804200d042032001b98503020007540e0321b1008955044900d5180da0300c0072401c9000d0140c4030b002400c0382c061234880d6910107920003049801d0f1542000c0b2861404483c0b80403521205508006414048041c0003400c00c40d0214188402580c20a5401d004008040d0b11403a0070032078072002c9810b010001040070b040040072000c0041840324590058415076250071400380122991001c024070081d81c0e103e40710342c3c5518030280745e0021900a40303441c070748039128a401d96031030b001c294a02c40040003045001440074031030301810384209070150140450700f13104034013500d4540003c80c1640550003215000d4031403103070500c6c0c0d50f81d03201d0142124208081c51070410101c4400b140401e5420580108100004148044a0246044001040e01c001c020070780c015641001921230b209548014102900080c4070401540604107910801041115031035454405984101c10303281100803c000380 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 740451519 1250 740450269 740450279
    0x109060e0112110405030f060f01050a0e040305250309050114070201140313171e0c190c080a051e0105090d05180406030f05011104062007120b0106080907030309 71
    0x60400ca2022100d00e0810741400d465400107030a1400e1f200001e560741c0d1200d02088602d40e01050210700509090b1140e80015042c4a20040c4280c0010806001d1240009004119907500519040703207150180e026081c0f00680d01e00180f90b42c0c054410180092120101c29189101301011551499416120560b044c0241d20340391070150002801011180390101005002ca25100079074aa0201c01c0800b007550b50310300b0045403113510180900343c80464414002051425000a0040303074406c4416440300c100d940521f084d449125103900710460300e0086002e00703400c0190009804260302e600c000c3e1595545c0040d5003140c200c84089a07a1021644881d01440209000303400815031350f40c0b1056000c00324180800881c064410a9008554001082d2844028007600303106c0c404640b032a040605150a142060050245200c20f40d043c7c04200101c400038906402008103100401d00c0d908000840105800c0c8686a400244107500c045075503140003c8501802003110400da96054031481c84482c141 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 740452769 1250 740451519 740451521
    0x25050a05100204141e06161203060b04090f1d01060612090506070f05041d07180509060f010201021e07150b1806010e0d061b0e031e03120c090109060e0112 68
    0x4402c02c03401d8034010f101d00045c2a1105002080814140a071504001c4005c0c07030b151540d15840c0d07403090105440c01c4c0041c01028494070441c0c040b02e03542d84002c80c0300010a00c90382d0040c1402d40e5480d880845554090001ca081074202608803100c6449a003d05a640300000050703c0041d40300400036000307035000079609400340c0c1404090b07491714a040c60500d91590b00b01c2841940d100181c1210808000401c120203a1001401407e146a14013140d03409141c0f0300072410060010300780314410b505440d44003849901c01d41c16074800111034064100380380010b05920096500c1888150355102e000072000d65207a42e94024111b111314003500f100c01c00d114174034903080014800740907e410403030fa4001201c02075440182150800d07029210004800c000c91403d0604425080c00e002c0501024000401890f600820b4808040c409907408451064081440d5415442039900280fa0600710005110800300c01402900002800b07884000484e511010290f075006401d65096000806454100600c400c0c2 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 740454019 1250 740452769 740452789
    0x4020105031801060b1206030c0a030b1b0409021305010908070509040602121906080c0108040b040314030123060702091303031e05100609150525050a0510020414 71
    0x400c1e01c25007000c4078007449040c00e40340e8640c0b041110203004200f1b00c0a102c40281241e4015130101c006100f1002500081001c0d001940b001918110858000032912000f030104000d0f001071025410f940d503a01d404074a03000750881881c9140e402c42da2500800c00d54000c0da220010360310590b00074a078651802042040c01c500003072049602980a03c48072041c480c1e0b14400328001c030030f00104015150b0000c0001c500300c03100b035803000300d6035403005407120b401e40d80000d170503904903400c00801c03003180d0b440d802c0035146144109a50102c05c4000000040d2020703400413000c40411140c0d201d203c0904562040002c0c84c02040d84c040d40c0301412202203100f0100c4148406038161003402c011491010401700d241c16824400c811200050326101088010115460444040c145070b080c5080083c0c00c11a081c1000228100807205102d000100840001e421480020b10020440c80b076418500c075520313085880d40307210f100403549403017035001ca03c2c091681c5000396006e542c079400743c40804050701001c00410100c = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 740455269 1250 740454019 740454031
    0xd230c15092802011215060804021c050d0305010e1005061803010f0e06010506070b070f141902060a1a041109040515100309020604050f060d050f09010c020c090402010503 75
    0x440c002ca048181c14501d0030341d201d040e141d41603642551501d400054508401e401c180151a8605104040684203507092001950303214601002c0ca80e81e0751020584004100760084180c1e045064450100f240004020b2890700080c0c1c0d040c4600e0b46e0361a0000400303c000c7da00c142000a0f003610500c41414103c0151249109040c00421060801e00120382150301502c3d12000841e156040b046c0e0040f420800c00e03004200c251506440d140558454040151002d0221420480300c0d1006043c428840d91090318800780446005980e0814050b1511041000204d1000580201c000180c2219001e120b10004072017030040344503201052008000c010540d40c40c2204002c2418400c4031010307152445000c0c414142e0b00a0540594080d0007040402d1050081402c2094200341c02c2000517181c0c0020f403001c6030402d4402c0241524000700092040c040e030041295041d103404100480924050f4809010701d100700004c0018031200d80c0120785502c10111110f42081c07c2c0c0b000f00b40154454001164416 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 740456519 1250 740455269 740455273
    0x605030a0f06081c050301031205030903070804090203040b06010c0f080f0c100606030e0d051204060608030c1c0c0f120c210801141c080c0d230c1509 66
    0x80c107880303003000440d0465040400542d000444100007a503088640d800b101c4038034285203042d58174669800d5403104070741300894100400840451070103002001550506680310304000e4441d07444042460094000701c1d41500d003c1980030100b07a0550080703800f522309903040303002d0400400407500d45c00c2c11944820403140c9030301ca08200c8010103034401c0c003000c504030404443c0425614600440181600c158a90006158202800c2802081d81200c103c0e02a21201000c41040d580d480c00c0141c01802c4583c400341981c0400244080050000704510ba2140403080c0c00003070740d9082100c201e5215601c060005c2c00102c0021055001c1404101100e4a80742c1c01e00d0030030300701d0303405643e800c072000f001c802d500c0594041c2200c071180b025001003001d40500034040f03030000b22144403000104081c1c2c003162810b15042400c80c80b80d0a110b010402c44078052400400c9519440302030784003c10422240d40029080314100701c0d10140000030300211108608148001c10030140451600302050f44003806202e014 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 740457769 1250 740456519 740456531
    0x280510050d050a0203010e01110403141204030602030f0a1a01050313050f0a0b011202060a030506040906050c0901031b0c0222060902090108070207061d040b0a27150605030a 76
    0x155a4a000c2a4030062090b0041c1c560f00e002c9106150a4035542500814142d042070398141003265100e00342c4045a420030325048e48131290000c617904000c04070088410320400002c0100501400390011806003040c1681400c0d41e079950243c40d4211a0070346242108010000c1c0b4400c070f150711a101854006081c07081031181008580d407041d240c405c06802a185c00c3e0048c032495130601c0000d0300c8827401006d04801010b085042d80c1d001610620810843ca0103055403100854119103480c4d00039651301d42c0c408010001814940c108048903003040f00c0050004c0c0c01c05484009003425a41c082c04203660a480d80c00504411fa4200201041304142940110f504140e45014514060061800801c040b420040e66903500304001003040400800040c01e43d03000d4002040344a602203400300c840800340403c00d03500d413802030001d8003904240c1070311a40204403100210340d8102144603010201690a4811203803050302c100350054803684401106c02c52126081005174501030001035600c04030b081400990 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 740459019 1250 740457769 740457779
    0x21b090c07080c0a111c05030403030f02010b0a180e0307110d02061908040b0702030304030807080903070c0b042c1303050d1d060a021c090302031204050105060108280510 75
    0x780c4042030006176401d90120700181070038201026100c140070612440e5261152068603800d503a03101d203210040803c610441d805009070310030b6001002e00c5c00003d000d011041d41d01c0c4907040c0310700e00315004454841d2170500c00c000310040002c1120041d0b42c0c0703c2403200c9403030005401c00140e0f8040c00c2059030020810800c45c0320102c41c8042d480540a02c903150310343e40d410b0070705211a8101703009000c07000355032040050001113504000030f15031100741440c1c50180c61f90f132761a0050650003010b01c01441001d200f44082040d402d004003410a4500c00c00c640c11010f11810001d01403402e01d591001044141c800100380b0442184514413115030003414107900d081d0103403451901721200c45548480b00301301c484a4504007070b014002e81303401c00041d0030150300b00210f010340c003070644518104002e012aa1030b940d000405000744140d0303002140710002c180c81451b240c10810f000e824125081400240440e00103504419000c010999449244204856103e06e81c0d0404008180c0a418400c40001d82080011 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 740460269 1250 740459019 740459023
    0x90c030b01060309060c0504081504260d0b04182006030405030a030c030b03030d150e07020709061e05100c051e060f040525090615021b090c07080c 65
    0x1c020099a0340c00513a00850b42003603812107612110b00c00c03c02c0800c0004020296000030310a0f000d01103400c4e01411b54503a86080400034540300b080c554410140c0b481c09004001c603002910501481c03907000e000c1d50a0140c100070484020b1082700925240c0c000c00440443d10f02920400c500070010700f00200040d07481e000800580080320100c07100d901c00250313440855810300030040c03903005505051100002c02c400003502c81c050000d81d050415070310305020030084400800340340200550705442246045c00c901c02512a0303c1c500600f07a9041c105280024402624030040308040c0e00d00942c1a07600c0d00300000c01a0000b24520b85404000c5001d03440700101d41c044c1300101c0b10310100c144604101154110140c20608000e02c01c2407940400400c0001041c0040b582c010403e51038102c0081129190b07616128444142d0080341c1102c0c50150041038240007051a4605004d441d0203c0b010812900100c9528100b42d2034182d820460f000003103010302d031152014000e040d1007200c2c042c1c04c000550190034 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 740461519 1250 740460269 740460271
    0x50601060c1b0f0501030b0d02061605070b07080a02071202030d20010608030c070e0f06040902180a06050906040911060c2a0910080703150b0909100507050c070306090c030b 76
    0xba810180c000c0f030810140d030f003500c40c00d0f0440400303032071034207441400e034000402502503089452280402d44515800b08001071124102031300b40f20b41e8050b101c01190a200c1010707004602440054410850f010820005a1160701072141d40200201301c03030040d01d40105c685120140500e001d0041000c15160481406c0c011040030b410040c0c0250340743c0b4a03e4660a241c40840c1d401080390340210414800d00445088803250b01031416a00401e00001030310108442304400e41d8070000942d030301c2d000e10083c82c106030842801c4482c100c80d0120940c88101c04c01c000c40790540e2009001201c0b031319184591b42000c4028101c41000d60b0180c81903060180900d0304450005600003107070300c1c002071400116180451016400c019042c0010f581c00741071184169540350b503404041c02c9001400c54058041039590040700c15960090144415409e080078459611569140506482400d01d0700281c1078520510036507812807651002455807a185440b22001401c02000544268070301c988041b020401d040300c06 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 740462769 1250 740461519 740461529
    0x80304030f03120b06070f0b2a03100b0c0a060615080f0c040801021c0c02010b0315190c02151f0501080a02130e180604080a03021c11090a080109050601060c1b 70
    0x111078040301f6150070303141d08074010180c0b146c2503d024030103568421755421405c100807207031045543d00c0d20780d00d100304001c01140c2c0c0011001a00080d401d4140e0a021510b0510103100f130600f44000c0362030b004800c0803228000c2040c400a0060300024418402075242c05402601c4c0d50200740c9820388a01d041800d980c000400400e01010401a01d6880d410398400c0e04400c0360a48020400b8802000c002515440540c11030b610000b0080042840e50364003081c520350b00b00040c1d808000c0c1ca51007141c040d4403484803100c000c52040d0000001900c00c2640c0d225040d0403520a6220300c407290611005613101341c0b0281030850183d03800c3c005a014101003502c1d14001d843c001103004c00780c1c945071103a05601540e40109102c150031107400d02000551060a80724010f440e42409a210445902da01e01841a607000710095542002245464858120000e0600103000d03a1402d00e11501c5070348003800e071010950010401c2c0d101e100100300c003078420810385030824401d811780380402c159110400b1000d5455040 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 740464019 1250 740462769 740462783
    0xe0603130605180c03060c0415120f06090b01090b041701140709030209092406030313090c111b040b030a05071d010801050610110a0611070606080304030f03120b0607 73
    0x18051040f001040043c011a20480080c145846d1078568411039020314400e440800c10003500c0c101945008256102010301c030320104000815040340c85c600038041c54411054401c1c0f81145880e0346501c281254020303291321308400c61030546806540300c07840509140c954100d542e01c8003900101040d011001d80509000d03074130710705000c0c00d5004112422101030481407483d880503002c5500e081a2400c42040300ca64201504a1540c508011030304600c200c2c0320501c0d0364218400e001c0b40c411859400403803510031666881074400c0c0600f00c01551a0b01803102c0e820113100030a02542d040c030340764101303101e4050090240c83c0807040c1561040d250041540040d50300d1484004a03074a05030448040500501e80700f8002c1c8050309149000c5800304d102040348204000101c50540751800e001c10190300f04550082d8100700005e03881040c2865600941c404894190038080c1c002001d80002080c0ca082d070340c002c5106404808503503000d440c03088114039503285403500c4140c1c407441c0307a850b48003504107d8050f1003 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 740465269 1250 740464019 740464051
    0xf0309140d02010e03130519030510060603050a060302010516210f02010b011b14011e02190804150b0a1503091104150506031e09032205010e0603130605 67
    0x7030f094600504aa0a4541c801c1c000c2d0301d00e80b00314038680d00454405a03030302d1040442914200c01c50103016040900117104810030030310780790319903800360007110065502000310b5141e120302c203425111103210207800540140403003501c0c80c40354401e4041c0c0b07034803c54007501e524110790000c804406404403030700049403c114440181c03a4083c000d0b45003001d000d1074513007407400440707580e490200320202d40500020981ca20280c24182c0940c0075003d030030341d0140400d800803a82c0e60030f80e01a50040b40c04d0204100040700d0145054080ca0342540507550080e10516090300640030700e0014aa010200b076071102042c900014040c550117141c000340c0d50203507008258619182010691110b103228558052407400b400400700807440c5005034250341084580ca0ba69894104044800b00b504640c0d0090b504040c0c011b00c8050100000142220581410704804400c3d1410050303402802512030075003c40c4100c5074040440c5460401190702c15044403441c012000c0740e454010481c0c00407500e40400c145008 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 740466519 1250 740465269 740465293
    0x609080c0d0302031b07024e0607080705040510080a051302130c020a0204110307080114030709112704060f081b030a050d030623010f0f030914 63
    0x11010310700c40304041c1429441c41c10411103541844442000c00103401402007448411546c0e5aa04180485064034000090490381d400002100d90890784640e401240e80040c02054600d0444004c20a00b500f009070039565030b098400e5a10300d0340142800100a42000042465518909284034a0171195202c04440c90400c81d000121400589220070706590030f8100d40040c1c0e00d00000d000707201402c900202e41c06810341d03000d030718082c01c5441c000d5016040860803020000c41201640c81003016503a0880941d99a0005441d030704d1001c0b0041d070700750300b1000c004d002c0321600c2c0d0441103410541540f903502c5c000d8454540c00121600c500180c0c103008a0840300e41c1e02d0702d01401050064100c00f103801d01550324041030300f6510101c410345008540366103400d245880c0ea05000d88041e60750860107481115400400040c0100400c0c0106100c49107020140780400e200140c012405034030603110647c01d00d4405401303075024024001a0000c064448007141c00181c504035040d0302407801354009044048030340e = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 740467625 1106 740466519 740466523
    0xa110c12210117011b080417072003014703190309060e0d030c080f210906071b030905041b020c010e030709050a090609080c 55
    0x40e034000548660451045040f2040300c0c0c0003081014070080b51490703201102c410703520009140c08001000100c01c102d120b11069095000c55042400581d14140c0d8102c8080054060140104544071182424000c0e580e41d001d1001340c00207240840014500c1d03203800c3c9c080300d80c1c000c1501018a25141482c1003415406030003d001d40700c14001103030070740303c02d4401c14008400246044000041052058104102c0001d00a0403580e4a00b407a4400f11520302001000b501c1051040000407100701664009001c03444200300c00252000900000c0003100c000180f880c4140d41008041100d0b8950115120048810030008ca080e03618a81c24201c0d1560340036004540c1041c64807400d03428242c0035207100e00c0e620b43c850b4200d45880403188011501d190300c40c0c10b0396804d0340c062a020300800e043c9070411a401a51080b00003900340064640e0400e940c02e0395000d481560380050740c0342b084a02 = true := by decide +kernel

theorem cover : BRFrame.Cov 740287769 740467625 := by
  have h0 := BRFrame.cov_init 740287769
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740287769 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740287769 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740287769 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740287769 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740287769 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740287769 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740287769 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740287769 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740287769 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740287769 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740287769 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740287769 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740287769 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740287769 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740287769 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740287769 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740287769 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740287769 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740287769 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740287769 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740287769 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740287769 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740287769 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740287769 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740287769 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740287769 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740287769 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740287769 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740287769 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740287769 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740287769 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740287769 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740287769 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740287769 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740287769 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740287769 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740287769 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740287769 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740287769 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740287769 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740287769 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740287769 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740287769 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740287769 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740287769 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740287769 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740287769 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740287769 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740287769 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740287769 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740287769 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740287769 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740287769 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740287769 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740287769 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740287769 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740287769 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740287769 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740287769 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740287769 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740287769 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740287769 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740287769 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740287769 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740287769 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740287769 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740287769 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740287769 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740287769 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740287769 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740287769 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740287769 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740287769 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740287769 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740287769 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740287769 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740287769 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740287769 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740287769 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740287769 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740287769 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740287769 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740287769 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740287769 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740287769 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740287769 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740287769 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740287769 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740287769 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740287769 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740287769 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740287769 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740287769 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740287769 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740287769 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740287769 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740287769 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740287769 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740287769 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740287769 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740287769 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740287769 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740287769 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740287769 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740287769 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740287769 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740287769 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740287769 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740287769 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740287769 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740287769 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740287769 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740287769 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740287769 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740287769 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740287769 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740287769 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740287769 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740287769 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740287769 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740287769 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740287769 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740287769 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740287769 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740287769 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740287769 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740287769 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740287769 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740287769 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740287769 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740287769 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740287769 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740287769 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740287769 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740287769 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740287769 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740287769 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740287769 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740287769 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740287769 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740287769 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740287769 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740287769 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740287769 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 740287769 ≤ n) (h2 : n < 740467625) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
