-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3221
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:01:17.268815+00:00
-- url     : https://prove2.me/submissions/d83ced47-23fa-4f7d-90d7-de0825659fbf

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 579136690 ≤ n < 579316546 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 579137940 1250 579136690 579136693
    0x10e07030e1614101d060c011401090e211621030218030f0607080a110f070b01120c0302010c0201030e0a050f0607140d0e0705130902150c 61
    0x451009842680003030080d00040c002c940b0020396188030300816205981c4242e03158a81d11180c58a103050807010756402e000385050948000203500310703103d400101c0c56440390140d0f401003040603059400b50401e40c0900281c0050000c2942c60381d191070064401c40010f13054900c5101c5203040101404a085c520380c40a8610f00c40c2030030400c085914200d00c15200c29100748812144418030010407100302840342685481c0165030310300700004190080391041c1351070711a41058584840920000c282154030505c1e40c0790200c40c0d9640d03041590020240a030021100749404521180b581c03030743c1002000c525000381840c900036039885030000081c005003000101814072408007080194003804030700d80c110b44141400b007041402041e0091074581002e000b528164010403820391844810f011042c3c00c005245000300064603940400c60a41c1b04004110340c950790340d1004403452103030900420024050080808101000d4211054060f203000c0d0740c182d2040300542c0703080010400e50400c80711000380500 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 579139190 1250 579137940 579137969
    0x201060803090a05040c2a020406090b06090d031b05060915190905010609110a0e040b010219050c0a1d1003030c021009090e01020c0c09091e010912120c0801 69
    0x1071002074240034451b0428400c482502d40380d19003951601080d42180200342040c848040c0c0100425501e05034880c841e854070b4a9902600361300c90004890400500765141c1c1444420b42c941100d40b00b584424142c5450380b0b2017110f20401802040b030300c1c02410340344216110810080907080d8001003c1e660240c0c15962080c4845442c0c0b881c1d00070000e154050310000810300d47d140360050075201e1903d0320b08104400000e12008094004041d00e089840c20303601004882450700011f90307038681d03c1d40c07013108030349100051078100312042041c840c0c82c5001506800645940c1c8007100d40344c8035111814012000032600090200510018200032250542d560000110181d02030021903610742000c482008001000810111820300800f01e4024150b0300050f40c4a06040ea45414611030b1200c0b40c2c070400c1c4860601042c11000a0b0811038080305c1e203503c40108170030003225401080200710080c012903141844504c0290071507202a40003400303410600080d00707113180c100e4224500f400b0300c018105501 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 579140440 1250 579139190 579139199
    0x2301080604020d08041e0503100c09051903080a050310140904171b0309031603022b050f070e0105040e1e0a020619030e030717090a1d070201060803090a 67
    0x120f1a01c0b04990040c1d80482c6040d84840038203c0b02e05001c6d46e210f018180c01c0710104600c1c03d04115508100031210002c21840b0a0b83d24024884005482113a102e542c5090301d18100c1a0801c0e450030045a00c40f1713049035119401c07100542540c2040ba61010704900103540003498030b05245101004180007420021a950741da90760440c004610408004980307000e1200302c1044419804040c2910000c8009680f540303030080405103065040181903d843c42882d40070401625040d512008002144a010240c1548606402d91121810f60f0183c01131280407056403d4403c0070a2800c1501c0010b4080700c00c9a0700d4405000c265850690340311703895806500b8071701d082c00c0891f040a036206100b00c1030354018211600080c1c030301c1d044503000d020315025000c84805c406406203c0c1426507251400a1801c280342c075101c0d80e42c420b00540c60400305101c00284000d0300da4854591401400c0100321010100043e200c510304540d20440308000590f01e40040400c0151001082d1070703088600601d04440325040 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 579141690 1250 579140440 579140449
    0x111203040606051809120703200a1103070f09020a03020909100303030f0b01080609040519030509040506032808120403030e010b06130b1c1805011a060702120c13230108060402 77
    0x882d4041d41007000e4940300703803a86846008610140d1802c00d000f0b106012b960300b040c010403190141a68800d520840e4100510000c04140da02100c2c810030b00162600e8408905230041c2c812449c600b50300008107010045a01103090115003902d0080d681040400103035806501211000d0009901280800340000c0003860300740c404e02d50052051080c0d580d150b81890142c555410104800c40c08076101145000d041d04191040c0d642c000003c4004211107040c00c090400300c0180440700d00d48202c0d801c400c01c000d0264400c11075110101c880704240c40d525003418000d00800700180b041c2107030350030824190900d26142054685100341e241220a03024a0451000704c107030b0189034924000a0f1004000c144404a44619417001c092001c01a00300d070958a0a03a0844510f1220040390721480e0800b1095502c510041e070700065416980c2c40c05903504104e8640c600303415181490b610200c049940701d9155410741004040701c008124130182c0040240c190b0455140034002c5030200d81c49180000c01501c0c1 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 579142940 1250 579141690 579141697
    0x30209040309050402030a020726071203020c030d020901021b0a0501030903020a0210020a15020301060e090702030d06032a050609040b0a030b0115110c1011120304060605180912 78
    0x101e0305200d250b2a540340d02040580c1c000725116403001e6800719546050004c07005800310081400000c00b461000d4074510805d450007000e101a000104464044180710702030f50441e010071048070100c9031100d01403141000a9480819114014040c07046a5040c4a500041001c207892004002030745032400d2500440c000c0140807015011441061084405602c40107601d14101519034080c1c5040b201504080c01507192040a4038003441c81000104102c03079220200d9601c0300c1048801f603002da1180300301207103507000388440407400074980000007081018081c12450492140c00c410351100c0111110301072911070030b10482c0c1d0440c60030050084503142079030000ca40d81c0e4004000011250302c0381c8441e210b04000343c00c985a2040708a00d02ca4146030043c140e22264180440200402c030804404901ca014584288005200d021a00c142036842c05100311503400d8480080a500c0c0d2074142450030292400d84285801a0a80741929004e0300e00101d2507840303800c0d0304008041440341c0400d03207001c5a1 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 579144190 1250 579142940 579142943
    0x6060f2103030e010f0e01020901140309281a090d02030702011205040c170d0815010c03360314010603080a0804020a090608010e010b0a140d0510050c0c121303020904 73
    0x1580d41c09546014901c0d4400c24003951b85030000141c9130450b4400143c60701c510b250020946ca84140100131a6030700000ba204600d005034001200c403400844c6400710f0021600170700528002c0d14012004800f03291414030740c400c4c0540000c64030428007941041e620303807250301c00182c001a040d40b500f00d410461500140c0d045881041519030b45a50b0700354041c981c4141d00d1080d080c80e081640140030a41d400100107800207050b48100c4480b001039000030b07000c0e11580c1c0004040c40700c80308140c0403144804c00602c50300401c001d1031218400300324151040c1c00c4098001100c040008900d4182e00c80c2c414030802040d80c0e4481210341c54041007a030195200c540c0100100c0c0e0015940101040700011400340c08001c044c0b15002043c0c080326044010f094400c036074800c80c0150040c5408101000408880c95440360040d1100c0c02000c0d40c0f41030413821f0152816a0b00e00e01c5d8240824800c000750b01c0401080500445001d56000b9000d0131000401803040c1030b40c041c88001e000005001500d0040741107a00705 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 579145440 1250 579144190 579144193
    0x11a0703080c190804060c090e060405070201090210030b150c0303010b1e120103150510050609060408070f15140f0f1303150605060c1507170406060f2103030e 70
    0x44048040150303842d0b03000048000042e41c00090204204047c05442c85202d024140715004600704030911408420041c034180c03040c3e8444e00440d031058002c0d8015502c19401a118401c04580440040c0151207264281801407002514a0340b5005810702960042400440a5441e50b464503040c0c606d65044103104a240000c40e0311420380007400c00780140310700c800c0e10140505961441c2442981e009030701818070802da00340000c00216440c03890b0004203a500c02c6410030b4548007241c020452501a60b044003489120301d2201107266041c1008400c21038269465001355098800e1003242d141012540711240d40c0790034014910202d0444002d0107000800d5200c413400c0803450034070455500c100340e1098400c4c01da4440424001d15503030140f140136040c2920903a10b0070020191061303545100c10f003821403840c01c442c0170400840c801c0351419142280700c04408001d0515040c01001081c1510411010340c081c1140081c525583c1c580d0088064100c140c10414500b035500c09601915489001c5c5c80b89 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 579146690 1250 579145440 579145447
    0x3180708060108070509010b0702031513020d060e06130b060f04111602030d0e0307050607050a0b0106020f100614010c1401091a2a0d02091305040b011a0703080c 71
    0x10000c20001103000b460054001c120042c03403c0180268404182c07c17800e0170304401c01258001d1b80f80001c004030111907001d41c1e0703011641c8244820800702c130b01c0c2a0007544081c1240300c4105020480e0001109001124162412600c0c0c41c00182e5000d45c039050004e0403d107240300000c10750320f8030410162410001800124400ba82c2c051100706691000b003014404903810082541503040030460724500081c941000350207844072000280c0e0703e400a1288611076072000500000f088000d02c42d0340051a4400d8442c00346503101e844c017a45540000414004510814410100020701c40c02210100ca0705000c880000880440c011994840c21520030b4980b58682240c070030b04404c0034420a18141d0040c005055410700c2171240c0da141820142142d030110180e5440028070381044100c1034044420b9080171540c44104803007001c0a4011223980641c0a4040da2421401861541141b44aa40300303c0c910704160ba2260104640c88000c166411110705040c0f01e202c0001c1d0141c48955040f4000000c910f05 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 579147940 1250 579146690 579146699
    0x40305070b09040f02030115080108062202040608030f1e160602030403023d0c0828090602041e1a0a18060203120a0e0a0201050706020909010b0306130b06031807 71
    0x5c1c2c2c0e00a80c0404a14400903074061152a4818242805000b4403400f03000142800000600e50b40b46240c0c030b840d0300c801d001c00c2074030440d611980f2010080201100303580d03c500032800720720002c0d084440f2584902c2909a511000450200210382d20802e984a13828120503c0c1d403180750094200400132801d62042481d65820340c8142c520305c1da00d103cec450740f000d40300340c01000c0711a9101d81012400c1d10b205040440c9410141e0300481601c1e40480f038103c22045900240c0100c0ca6843c00110070048010301c2c00300b4080602600785c00401c10790300e242118048414610760928240c2c0950700c0b452041150112038841d104440d2001003100c0e0700b2a14000038070a404201c0000545426440600564000110411058440a40d40340d102603449030070040d411000c04241d8a81c040c0b480028100040024654100701e1a6416102c0c1c80d5000341c00e015845d03845090304983c0b503105807815031052030f0441281e14500600d01401002000c0645210704548a12080445008050309400c81f1401039920106 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 579149190 1250 579147940 579147971
    0xa0803150f221416080405070b03151008040c051504030c12120206091903030212160212090d061503050a2a0b0a1d030d0503010f0506040305070b0904 66
    0x20b500c0c156144080d40c4190321002410100c42440101c003040b0001002008402d0700c0c50040d210a1811604040b042e99a59280c060b04000094202c101921004014020b036404002c0d0280144001601c1c03800d40350200d080141c802c0d01c002ca8009010b60030401007805981000245458141401e558142c18161a0b688038680700b42e440d003061000d1b640070303040101403100c04041c61030034103d580050502d82c2440c4010646900320240c0c5051565001070110003050b221b541140d00744684140e0521041c10100c176155055010644408014412803650302840040d04c4221050312000a1003080d010704c2541d0f800003e40402180b400080b1070448000000c0380701440a0706005206034455421031a0103c0d40d080e541d06003a1030a00d020010207014480000101d0488000380b0182c1880922522255010707080baa810940da5501401660788103500d2a81140140d03069629038000500d00907203c0091250078000c1c0e00c4050f1043e40501810841c21800c10014016120050300110b580180720041c1e1 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 579150440 1250 579149190 579149209
    0x4021603081e0f070804020a030b0903190e060a0e040f050705070b0c030106120f2a0314101a040f0b03010806060d050615010917010b0109080a0803150f 67
    0x3540494400e9080102007550090001c82c006100c1d0b04040c0b990510100007890518020001410302c401d10020409566440340300d81d0040d54020300340403191406c41b041071b4590b009000e01e030110100100d00055114080e4002200181d800340450f82040d101020890303800c40b000861682050341c03011141d40340b0519009203803188015456041e543e078440c8c5002c80d10b002004141b411141d80c144014040c140d4010515221234160903070214964664003081801003140604000754020382904520314034502c0c183c3d8a0404c0b016440421a004400e14140d58021003180c064640407002c40f03050100c2c0f00002c04000854170051800b500b82902c1c1e0300204007c50b02c6c4d80000c0d02c2030f10007100402121004110140c0d0200c0144c41084c2d4520302640c0c0c00b90b541e08090804522840d03500d000440d1a4414480b28005002a800030440001004c10701c9000340740b480d60103800121181000f140d04000000c1c07000180b988410712614640e1981c440a41444500c51b091354001c25090800b441540e03881d000 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 579151690 1250 579150440 579150443
    0x212010524150a0e012a0b15030d030b031b0901060f090b13091b080109020901171015022e02071406010603060603151802210f10150e040216 62
    0x1358111115594009017a1601c500030b4003a00d1403600101c40540400c0d1014050340640c8600c030f1141c02d485011564400150312465160540f00d00903101d60081c2c0e058205840d485003e40544491741840c01c8500107291740781101d2508012000010443e0b03502c254900c03075000803107181000c0b13000d464894004e4194080071845000b02c0c3c40c420240481001445030b40c41d42c1c900a6800c4002244840000e000c0e920148104500b07590f0101e0b1031402030740902c1c040d106c00c106032805110640340034401c005601902d80a103036000c0505828410b255800080d607044011421899100b1b0401003000c1c21111800100c240c071440c980030b104080000c1d04500c0e2400c0c642258001900ca0356040250040884100d5408482050304006448007100d406420100540304001549507007074200c0a0703405c2c007a114901c0803100e104a16451081780d0b400108a0034050501c3c400400c140f92500324113118106181d00032500c1c4c8a121440c40c10855000b540305c0600308001520150030400d545441c20410341c5000300 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 579152940 1250 579151690 579151697
    0x50a0308091905011d03030d0f1a150d0510030b0420010e0f0603060d0b13060b152713060e0a110702150705010908070212010524150a 59
    0x10361211925003403105011800e4800701c1c8082c0e036032500c0c0000300551000e07000301110f18a80b0070f1066280d10280200c691400010500f4001c00e0941040303600100803504c2c0c111408884c07101440c4007440c00d0350300c40c0041200c82e0805804c1042507049040100b101030b0103400035031214000000003030300f400b0758a44200d014035091001003500a4805031800f0b41780c048130f410444240210743c441e60320341104c005984020b9801a890f42e40d0070000c11280702890380080e146079410000c00541c1c40040c0061110303184111360521103910041d0034041310403c2405642c40840050002c0b010884121344000d900070280c1211440e007030034400219051000402c001820075032903003010311603103040c00806900100c03410010003065a00020b00981c902418000078800c999491400e030440d11540140c03040745030000d0081010680602d001561903018160803800740d400301e500403101042c10711580348034400c02886a030b01c0e1071042c9000c0b802d060f400c80000390f01206184413142000d101c8000b801003044c0945 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 579154190 1250 579152940 579152947
    0xa052a0109032705010813140102040f0f0e010605030103151b030f1103012d27240e0703140a060602070f0b0d1104030f0506040204110c25050a0308 65
    0x7041c0e00c403103c04422003980300b503c2e583c5041025036800907526900c144210fa400d50b0340450740c64000268403401070f1025003980042808034000f1707001d600030b01c21503468034608c82d0740556604200d68048024403505000c0383c0280b0040020606c817400102d10101c0240c40000e000c8490500c50103402803000c68980000c2d5152100310703820b4940d200342c031540b1106401c820f0847d03140c42c05800d0350800c1044403a10506150552410258180a09038040c0c256a60050030f01c03c0540d22001c0b604a02d080055041c5081030311030303091401901003c0640c0604142183c00c000c2c14080c1e0400d220302d0140004040550364603650364507125800d0068095031480340041005071900f40024949021500021601c5200060421011241c1e00840e00c00c100c1159010580c03d02c8840d044e512030085a00c06080794401d000e084d410024007041080c0310702c5c402c54081010107c1c0c01c02c4144a07008000c00c007a2190f10044d880d1044907400000044c07800205e64081040740d0b00c0da004500303845081d07401194201c0300031 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 579155440 1250 579154190 579154217
    0x70e1005090d0c090b0f060d090c0b040602030c011803020a0228140411130e061302040801020c1c020a0b1f0f0e071d0126011202040608030a052a010903 67
    0x140078107000180200c44001c06c40c1c2d85000000d000b0b01c5200c955006140d5520b050908224840718110010b02000103095110366440f00007030f40b01c2c0d210b02001c8043c2d510700145c0c0303116181260014061960103030700070105442250700303000c080e409000c00400761244007088840c0c40305d0441c643d0805004130f00460183c3d5548801840281d07180c00d2400020645d080c041203945e548115880b504880302e42a210b0400d4440c140420340c410951040202142c1c0005000301e02d5180c150020302c80c00709010115110002803e8189042031002680e00c4016000b404001001c40c40d80c4101c15001160b00070b0101c80300d4503800388242c5446540d03101103070895110104102e0010904035060b800700050070f10065840410391511020680e0461a9061140d192440c1000325440315004419107243c3c1038441803940c40e078804c00c5844200010480c422810036402207510072000c0191141116107803542403e00d1519620700e0003030201c00d030052a105459004840e4000300034003d103c020b5000b5140c01c0410401d9 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 579156690 1250 579155440 579155459
    0x90303080c03011202100c02060d0c110f2515020106060f05040e040b04060e0a0506010810060b0301060806030a0c1d0a0b0310020f161401060e070e1005090d0c 70
    0x601085003010700344010052482d036980510021035044405070400a440c01c01502d8500c000c11010390482c2c00072542201da41015882401030362130941380c01110039500108650754011905204a060f08107400500703012810030015031100c03005a1541221941750030580110440040041c00140e44400c401c000d810340240740303244807000c2441c2c000d01c0d1509203000a4001038018200130000c070207580003e000e1224a50060741401c024405403000341c01c45040a07a0f03299000e0165440600510f0005002543d10303220710380480c0c114460036030840c0c0c0b8095042c0d074554001400ca58060045980c0c5100140000b28002c01401455201c000110000d500f110440080140401e02c40d619001041c20607550008075250411f00d00d12001da07545802004c0d81c0154010045135a12500007845500200b00a41d460224408051f0000300100c564428850307003522015102040402d4138020000d159041c2000002e140c4001414614900214000483ea003c4000321080c5ca01101c0001c040c01b84010307 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 579157940 1250 579156690 579156707
    0x150901020a0305011203050405090717090d0f0c02010207030611070503120a180206180112020a050306030d030b01140a020703080f0309010b191202040f0608031309050c04150207080706090303 84
    0x81030100210345c250165400b0345a4030990080c41c2c490f440c80c400040115100301066240004141ca0701c1000d4102051842e60728020703142c1c1e600118038821012650248030b41081078600b90164000c100c51343c41c3d501e41500030001d0b41e0301e00c50000c07001c0140da404902c0810040c00c03050261002501c00d032a0038801841128044440600650080ca80100c05641e0f548240d03007034910124140e00d40c907105580162001d15140c0034150096001051003104250004081c600c81e034410350980344290200da0003182111188400c6501041e10042d50100074003016024095000c4607004039484161030703403505d20454029961100d1a075000200308400010300b8080d800d48080241c1d03078204641c14180301c3c80f202d44210301600d803005181d045a0070540d61103401240002c0003100c0100314882d101c44c2c00c44d440b81d0009040d81e0310020300c640001035804161160520a052108055081a0400040b40c00400b005030841c402c51181c411b001c15464018040100104016100e2040b81b600e1481c002e45021b4 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 579159190 1250 579157940 579157949
    0x801050906010f0509030708100906051305070b070305130f03030f0903210e0a1202192103031b0e031011070809120111180306040221150901020a030501 67
    0x4540c28810079980040c01040403450b9410460340301e82164011a15049540d0301458192054001101214080d40c0c410444107018120502c011b43e980803428180f140115401400d40d4407581c810020b1584500203004d05074803d28009c0d2404030b203a06d0415410390160402900c0c04141e140400825401050601c03c01e10f50741442040d09146865a07180c0910001d0030102c2c03d030718500e000400c07074031070448850356a40062106103195292020031014400d081300890081610144100b82d1160207100303001181d4254002c2c400102d050f604075881941c000f802101419240c0110311202c001e0108403101c03101c4290343d0390001c13021550401d4980519400d034121136504d05010740030080e03051802c440300207410400e56030b666040003003ca90400c010500101e4154a810b62071104039030702400620341c003105041e010480c4180301c800c02d038680342e0070340f40203600240340200003148400c1d0380c900040305118074003a0340341e2440d010441c1510f074001303c0d000c1000340d5000541452441e0140300d01400350 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 579160440 1250 579159190 579159199
    0x515040e0a06091b020705090c0d1509111c0c1103030a0b01121802100c0b100f0510050304060b04060b0a030e0d080f01290a110d14070b090312070c03080105 69
    0x6513103004060b4454a250040074011850080014400c0e401c0404455824000c03032010030140b1022640c8903683d8103540641d00c282030500c80304c410881c06203c1950540d1580494018084806501003c0189960142c001c180020000e60b4030512000f480650300c1141d1078107000c2594502c030000102400d000d060b01c040c45c10314041010550078414a0b05031140b66040c0d0f076154080c0c2c0500d10a45a90760204001803500202808006601c00c01c56210000c644541c0c0324040210349840801c0709070704543d80c908001400a00015010580c1a00200c040d46070280001500f544c4801456110742d1000040f030700403c0c0c9400740c86840c00000c00070005c80e5080d03031420310424101844255400c12040c0f00d699181c040301c13a220324600210617400d07200c04540c464034980d03400c0701c0c020190881000040441c400d0140740c05a41c541401003074003046500307001038810301e002002c0d5590614a0805080b2460500c0240180c0092481d141520380c0100401e4481400ea601645401805800305801040c0076 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 579161690 1250 579160440 579160481
    0x150c200a021014040b280c0b0105010203390d0203090108060a0b070201140d050f091005070206070f0c0c1413090f020906030c03101a190515040e0a0609 67
    0x404100742e05035029161481540d41d03a511482c1104110000d8058000810a00f18042c0411003134204007160076091050194400c68ae90300c0005988900440186107240760464903c03c1021614040d03604058001c95035039803031521521402031516401e0380c1d00e00c0141c5c0c00000c5980340d81d0303000b06526501c90800ca91100c505400e0103000c2000f8050800b00034184905080100460a64042500e0441410f1002001f041c504580f07110001d02068039520014003600a100f0f4845540303000b8507100320580e4000340320341d03281c8450881c2c1c4c1582e00d10000c01008027103844880018000a0900001c3c05d0513000c5031101840d03003040000743c50440e200e101e0340e1307490b0101d880700103640710301d80c8a009501100c0400c100c0e0350303400109007480c80c0d0496182e41402118140c00e43c0d0703030075507000030401612000004005041c8209000d000444503035401e5160b440b0b00800c0100e8601018440320004d000101d10741460f5a5800b5100d0b4100c05070ac424003072640310f401c1482580e40710303c00c0440c1c003440d00500c02d44 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 579162940 1250 579161690 579161717
    0x110408100b13051e090a030807020d0206060120060a0501030201140a020c1318060f0e0705090406230a090b0c090105090f030f03070f0507080a150c200a0210 69
    0x203000c42440b005a868586540005414030006900b104910118012009103483c0c480301c4142c4841048000b100455021404a058248000341032000410250000c080c5a2901401903680c40d070052450110f45994011165410005101103801040000004503065043d0310024024511180644203200300c280282e041c410342c0002c0060110b40152000e6000b40c0ba0070f0340d400e010303000c025a170b89000440c551010bc100041940040c0150618000c2008100898500c840d00d800b040c3c4101e50780720001d0804180840c2503603002c010044071400310f0121003d40050304080f0b0007000c840041d45d42ea92811003105100030a298143d02102e8210094036120b04000040c2850152028150046010005556503501c0070004120b241907040122a1941e03840d00d4604080d901a503403c50302e500414074001446480001c8200030329038060105491600624404401060f0070a0250b040042d180c1c0306054102c0700142d59204240480090000582c003401031101455600011001300020000d641c103 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 579164190 1250 579162940 579162949
    0x1c200f10090611030403050703120605030d03111b100f06060813060b060d1e02071101110a1b031103060403050a0c050c060309010524030a0f15110408100b 68
    0x3260142000590544a00b408001400070b04031030382610340d002080c0401d00d41c1042c050702c502d40c440d640300544514051070301c0c82994803912603d60503910621028080c0f034040d80140742e401511840c02414a0151440795160400420012041c0e4001000c400600b180b14000c000304999014400d124144c0380c14401046884010501c442140b51480c01a0801036650050004c81038001e100c9501c403100f8203581d05c0205100d043e10000d0ba150804040c00000702c9009130784d051900f204101004840341001500e22118940208486014078403c140014011440c04c502564508090400c07050451408981e0000e60980d094484c0e03120100f017000095000040b55144415460a910440d04610b0a2494211410603041d400000401000304078501548103501c20b0301030b170140300c0e48414040c070480700388280c07111079580680100e00c0e294041114640c480800c54406d5004805051100a2440c201e41c500d4041081070400050100040c481c1001610003000c110501002142c09820000e03 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 579165440 1250 579164190 579164203
    0x1603120c030c1205030601170402030d0c0c170604020406080a05071e0b0301140913030c0219030203060a0b09070f050301140d050a0303020a08010e13141c200f 70
    0x10820850401038030400c041c40381210a034502d5109420a1400c541100040c2c039907001294824002602c483c02c010045405140351409660080d0246c1031040303890804031040c58861400380e40e030600007000022800b01011003081c514040700044c0015062910400c420780d141a4021800356000c541240040398000c249081220080c843c4591841031440c4c1d119450101c1d80e1200d40d08a1700030000044103a101c04201124100c11260f850050340e514144d4a48461134410290001c5c3c080586100181444480b04c45481c0048040d5040d182c0d80c0e078000b0303140c88030495602d00056114140c0da002420603d16440e00640d0b1400c100d0035000b0b4411005043c0d0205105042c4c00d41201c9140d01d1007620b91081c0d20301c2035904001a05c4800100b41009006580151781550009070310400001da00401000c196010b0400c2840075030080c0034a84030784c041c500c2620b0039409640140088610750144001c04020000080d446030110f807511040107000c54100d0740001200c81d04103800c6039411803404140b1 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 579166690 1250 579165440 579165473
    0x30312090812090c031e2e180b040f0507080105060105160f050303040b011503020301030c0303050304060f020d090309051903030c2901090b041406010c11060f04081603 74
    0x4641d010790312100140e180051a02d070745505405103410f4020f000551840c0f6040d2010b0000c00c40e941d40c440c1003040104841f00c4210301a0050324601d5440801e14541c000c100140c04902c11408030040e141c661040a2409503422151402d03075070991b4003007100a010b0f002c02006018001c214600c0c0c403070000b03080c84c8150400c6111101d00fa0700480d0801120800440d02542c0080c1201d460b841c040c500340f400c83ea8207004903640c500880ea01840b1642c824000c0300d050ba6030015038040c40900d140e17400d039220b81015208070f40c80d07a00c80400c650b41c0780061015080c070448104020460200380d0401a01c29003441d00018001e003000d482d0010401c4102201d001125850319011210f5401030802280c0e0100540b500825031b40d8000c0e4080c1e600410540160680c1c412180411169030807408000842e6105100004d448012100055041d8007034100c0f000303018052072084840100d90800100789911400754201c04140104041c400c040c0100081000250341100900c40b01382551692284a40c01248 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 579167940 1250 579166690 579166717
    0x519060806010c02121b01021510090218030a0302010b120102091503071e051b0d170601050c0a060222030503190302090301020d050f091b1e0d0c0303120908 69
    0x28900c21505c0b07104003c203900040da000d860f104036101c040c8411506607003130100d0041c41030078071080400268084080c0a0748030b16901c0300e14a441c1420b0030f00a50005201c84004400c1042500d50310380f0117120120095100b81c2c00000d83c44040303c1042440483d040084049a10611001080e600c5000c00603840c043d043c3c0f02c4070f4403507480c2070b0120b90380c0000d49440005500300c151100119904107000d0f0000e50941c10301d000c0302d0464104c2d41da50b10200400b0040c0003c200c0048005130604501c0b03c0d0390000f2040c540719207008420b81c0300d646070041440045409a0f4000381070a90b44030900b0041009600c40d12600e20002c1c40c0d0340352a540c4c1d000c0d44003a942c03d01000140c15200360701030303030403141c5900d0701400079034544030071025400007800304803001040c1400f06c40c002010702001180c041c0140d0284c40082c3d564554000512508010240c503a0300300021200c0302c1c0e10a0355688042071190b40c803480a0303040ca2429850024180184183c0141c5003504003592031000a19080598250001800c3c = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 579169190 1250 579167940 579167957
    0x11070608060f0a0302060f0903010b0103090317071e02070806090f03040e0c070c0311030606011407060b030709020c0d110a02010503010e04030909060b042d0e13081201051906080601 80
    0x400548410074903413000f903020354001203903030700c1c002090044e00c0c15080c224004c00000a4502c019815641651300003030014030403008845124201d00306a40e00450709182c020b440703043c25000c20054280010140d40541c2c45006c0811140c00100f210a500c4080180540740f8120050801c42d40c1e40554040d10b0a181401130011304408692401e07249201d801011303d090080e9241458017401405e03060050090040d2800a801035016254404290035284416880c01c8610344a41c00248118500c2c507a150042080008070200f240c0040e00724000b40c00e0280036482500c5001814071441000d902149030413078007113200540e0300417003900d0446000051012480c3d550345002c036200501a0400509075140100200d1044124405041a500c02a070801010004c5666500405146081c4100e05101242050065407440407549400c282181c011008190f038580d03400741d4a4102081061004a5004c0100864500388880c810170031082042c00b1101818810001c01c40007004190303505000104 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 579170440 1250 579169190 579169219
    0xd0e010e0c0d0627030305060406140d111e240301031119082808040303032703030506150325051209010603020a05031609110c0f0a031107060806 64
    0x2900001c81d0360021a140300c01c103200568015186681d00d240176030000780f5003000142c1d107003000e1103a00d09803481d5a29210f07454140c4010041020172050080705d404051145004a54035034202c6c031070b24120076140c006140c0c10700303005002d003007140d03e00c1d01c40020390140b220408c0100c601c400ca9054a4224200f0403001920b0300104801404003048045402090440051040d030045a20300c01689218004180f0120606c2d10510390320481e603018106c1c0000700000c0002034040d9118807100d0054180c3c500c080400c0d400d8855072080e4055043d00440e454800300440e9281c80c1d60f10004c60003c250384c150450420303242e0034803c1049521a4054038072610880100240600c0a5469001d0304401458640c68601e4032180604114401280544900040896035180c0810700682c00c001c43c2d06928000d40c54001081d000d4151281d07140c50300d000c108005030b840101030000c2112604031000411400d1154a00103041c202800c1c42c1402c150480c100600880e944120b000e80c024108031420001d40e04030 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 579171690 1250 579170440 579170453
    0x4020904061d010e01061202180703060f090504020a060512161404080f0c0f060f0d060f060503190203150d082110081603021207090e030d0e010e0c0d 66
    0xb100d42d100414000720322601114150840c542c103001000092000c81d5440d410f481904000c0e0800a5000c05131982c805811420101c1440d4800200d141c0030504a642e43c5810f040025207400c964545c940791400c00c0203600b409003401e0300405440c039005282840080003d116408003406403411100324569000581c2d11036900070044018444410340c0c4d86664040031030356814005c0c0000c0050040c032505144510b0040b140c00042c0c1800360070b091601d6940101300d20540c2c00311583c0071045650ba40080b0305519454844c40c00740520f0b4650701d9880c100140c1d0500c01000c0d92039144000b600400401807002c82c1204107154400d4151840301e802a050324200200340580050181e500009465121102d4240190b0714001c0c5801d1342d141c040c042d1111041c50312441c45480140c440d00400c4d0003040142021142d1316846080c08007951156900c410502003911001d80e025103056102048142d0410510300c90361104040000007080411a582185502d84250408aa100c0c451810814041c00301c03 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 579172940 1250 579171690 579171701
    0x3070c12030902060d020c06061c0b101806060216080d0309020607060c2706080c03060607020d030e0a080f07060806030a05060c0333040f0608070f0e0601170402090406 74
    0x20700404c6261605204203104000b5000118000390310300c66030010403290700f070014007000d1700c4140d40d02e60042ca928035203640c6a03040014007110034944003483c0000d000c07809401200281444c041020422900d031642c028505480e4440e04c4051004e05581000140700024003010500700c1e50901041c00c04560001507124010184080d02036800c10381303801c08481d0f114114284039049041855481003883c414441aa03c0d40d0103684003164440e000f00d07105c00420300140d0351140004080e185024107d501060008c04240e908802040e007861002c025450005124006400a0001001c01d00c0105c040c0956a44407880b03540180120800400c2044e2401c0c0310449015800078100d40990500c540c079212181c0c41120164040001100800c003010b0102d41410a08403d151405030041a083c00f00402400c034000b02d00400e990300d0500280a600c140802001400c603114507140f078034a0030000d11000312009040c0340c10031408410b20700542c0c05030404141c20a0b0185c038010115525450800020f05 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 579174190 1250 579172940 579172943
    0x40e100608010203040302060117100b0a0504020a0f1b05070e0406090c030c03030f080105011707031e09110909030703110307021507060b0a060e06070606090e1501080303070c120309 80
    0xc0c280400452a110150021800713a03100764202e4919a80c3c80281940c44500c600c0c1c80310494022503602d003001c80701c0f0b8200c0b021036007000303100c46d003080e03a5100000c080f41d003d4101d16000c40c4e8030044410500740c12100e000c40350216000200303140c2c2d42d25541e187e01c603a6180180024001d4120218003031044560090743c48130390280d426100c10340c81382804489400c45d171104900140c400c8002e03006e07581c4181c00352812188103842d01c403440c0e0040c0030540c124030300003480042016a12400c00b4001040c14002615805080f1000031744000d0a040c5130101c4095482c000c0e0182d1000c0050000e8000008101c030f4181c0d40519020466800101c1d906040d8400c010303020390300c00e0540c83d0403081c0305000001403c3e03440c8200803c2082104550510000300658810b00004c550744104e00100ba0614800801145100d94000112262554a083d04179500400422820341c81880c22090345011602c41e1405040c00800460071403501c000001c154010503400100080f10078865416180d0080c1c02c20040e15 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 579175440 1250 579174190 579174223
    0x70b0c03090301060b13052d0f040203010609050319080316090803040b120a1a0f040f090302030319140c0d0212041104060906080c040510081c0906020102130302040e 73
    0x1643d0340c4145002da00f2040c3c00050101c6d025000044501d405a03905071580355a5001c41451303a10b044090001420118580b03801c00030303d003d5a5082d0b540c3d0300c011400303009551140d10200d81000181850001400049a5007403482060b2002003a0340006907a44001e06481c8162040c0460000f01d65132803142d406441544000300700032540490800140c140840710340f10381819503440418000507540b5048071814900501c28802440341410700300c01405050142000c5010180c2d0310080e41180e210b0b150980040c1c00c040309101580340e01d41d0455224110b1403005100039030140e020400210000707048900d24500000c5c00d01d0310354400d40c040d21506030802c0080c000518007414a071211400303860034180f0071071504001244400c824401c550542c0c12580081203184030300c0c400e000060002918005030041c0591000a02c05010450301c0914002c0312812444004105005490f08e01690807030740c10341e401400a0034140003d002c403038048030740464000c12045094503481d414242503100c0705040 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 579176690 1250 579175440 579175451
    0x90309210304290901080105040b041103040c1409010f060c02040603080c06060109090c021218100c030806090408070b1f0303020c3f1e161403070b0c03090301 70
    0x703a0460880f580307000b02c046182c03c00203240c03403414860b2040da4600341c04a208540148202c0c285548156480900a4000104000f600036000019001180c007103907441003604060002000c290803106500d0b000756102802d81d414560905e036001d001e80101c000300305a103140e150071355681381c0241004580003004150b0750201241c42603114542100ca80340404d8070380c94001000485842904603a24590340a043e15007841070700c00030343e54840700c40d0400ca404090712010617070392010b100c03404840640c0c44d41700c03101c1304510380603108440c0141454400c100c10010800800c80309000c035034003170740c0c40400a00c0301c1d9249140002d94001c0a030403070806030400007001c401c1540009101c41203403c1103d290b002613914010405180d880749884420b002d000c2ca1032425900c6518140003100c249010541d1070100a0758480d05043c0c8000c52408680c3e4420742459004c1150b18a010000d040100640200c20305041c0200341d5900301807003021514803002484560240c0305005451000000030001e018 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 579177940 1250 579176690 579176699
    0xf0f09050109120807050a12021e040905060901050607060e1507020309040e010515010c032c0906042a09050d0b07020d03021801050a0e041401090c030203090309210304 74
    0x918029504580f000300b0380281103112400341d080d43c1c1c82000f55903a41807500c40c0c04001200c601200f001250007144d000c1c401070b051440c00c0d070850a448802c00140303584942c50a071000e0700740c5034081c000f5400791701c4d4000140029102c0c50115000e4940188000c01c10b824003a500d1840d003051010000501d10491050202e03803a03000c40101200742003158140148545c0240c62400c0751000e4840e820045188115070105501030315504054500a0403c04090141102140d030082072400100c4408422615407041c90b240c6408281d0b004401a502044054401214500300e81d007044108004401c029601100c0d0912501d004000b41c400038001c041c0510341840c0444c5140340646595002d405000c00c00c0071613910900c00e071110b04544108900511429000648150b4405042101001002c3c504a203440d00e5a00408020700500001202d4030b6140600e0001280d0842005104042c010010702c464200008291222504101d800d60680210400c0d03100f91141c11500e504607034000482c0014 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 579179190 1250 579177940 579177943
    0x2031806090606031506100e01051201080c0411120103081309060902090117040b010b0a1b050a05060108120d050a0204030b18070f1511030c0a050303091207050d030f0f0905 76
    0x140102020713421100030341c45840203c90404012249943c00c90340041400070400e00c200c040000e0207006040080c90051508000c0b4200e1b03200341c200c011668030041c0b071448541001d201d044500c14a000001e03050030303c0c0803180340702d554041c40f001e0580503003c40d0f00d0291000d25002c100c01002c2c058000c100850795403c00b5006904800707039881c080b50700e48043e2140c41d01003080300ca1040f6030100d00c6815503800c01044c0040f54101c80e00c1c110420542c0d1041c84140407903005480302c824001c80050088075214600700b032400c08141c1001d00140c00c050348800080c0140c01c1512588800040c010900740e952508090007400786601c090880e4551109001085140e548080740d60110749091f0343d0016155205160802e07102e210350b42c0c0c00c00707152001e441d80300d01c510141380403026808103681c07801d1000442d19103841210780703080d100354100000b4403140b0703101001002000c900103a800c0d4108007031030711a181c640007030425140c141610f9480d800400026540410341d450f054030740801c00010ac5060a6 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 579180440 1250 579179190 579179203
    0xc010222120312020304030e0d05030904060f050a0311030f0303041505010b030103030f0309030908070b0a030509060907051009120602121e0601110a0c091b0504030b0a0203180609 79
    0x18410014001000c1225600110700303540c0c868040e250941ea0340d500a80d2080298002041601004268400415a680d030000c2c64a4254010300007161100071301c4d020001103d560740e002000440c40081b040115454461082040340d8014221503480041440803070b0400400f0207000e0041c4c0400010001040712055103080f100521749001c00c41d076038071030f24201c89901c020b00000d80440c040c40310707030bc0c003451080c2c104d803000c0c1e807082c5050324102d5510f00e007161400c8d2090300081b600d00750115a94801541c140b0803164051882401003071541810102c5549800c2240561401030006040031f1032268002d540e80002815089481e1030b41c201356050a400039040034402e07906400b01000820800f0350f040c0050f86403403400b102e410100d600c83e1801555600100d08840322140a019405070100307070700c800a00020501c01001044040841130102649681e60800301c060100c00e00c400d01c046042e000420b49e2190036030400603900d8488010309010718043c542031503080e2103410b0030082901400f00c1c21 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 579181690 1250 579180440 579180487
    0xd0f11010e07060f0302091323090105070e040501210507150c0c0501031a040c09031b1401020304030c0e0c070203010207060f0605010e032107050f070515030f060405060102030c0102 80
    0x841e10300c48991301c422001d07807046041070b40d489404402c9030101d000c61a440007082d10300e124628000c216000300145d04844040b00c00d0300203659910100550545c100b01d5500001e070040f50b0801013981044814403400d80318940c00c1401188028442007005030400c48a0701408080c4502400b17070011107001060080b800d0b00407170301020034200000b01d47d40640203000259582000c102165035640e411300009000e541d03200410004844c4000010840c6544031101c00200c60504240b010b041c01040c0e140410003140d51811584104000c00c08030b901c015a80342603aa103a030f0410160b450f4410a03880d1405405006581544002035000410546901006503460031510610000340c0e1080150345940d03100c500ca42d01138102070b11465078100c4a81c58a80000200c800b4941846e100c1d403600e621f0160001650f131955800002c2c03d11481ca018840f4112400c140d25440d80f441c82e0001c0324000b0f1020240002c2d00683d102d0002c10300b568000d00130381d00881030500085481c0e54070302d1000306200c60200312 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 579182940 1250 579181690 579181697
    0x40515070c0b091e040615090e010e060d080a020c060f2a03041701021b06070320070f0507240e0a030308040b181f0b030109050d0f11010e0706 63
    0x10000d0364600400c1039410b240002414011410741301261520010030040c9060750140e620307403002c0f41d12241d07002410980748903991100145428856650005141a0000b03601c0000040c1042610359416100210140e0310003003243c1c03141ca905038140d2802e000811520303404580403c0b400b414000c48009000ba29247e00754011628003242c140001034228020001003030b400400080c003c8240aa0711110520101c5c80018540144c100300440140e52000e2050000c1c0c0200040c00803080e41400340da0900d0302c0700030395802d400e440b03407003152258410404c004101d0100c1500100038000140802c0c8000c3c100c08690f0351312525500c0c152410080554801c42c04108038050030030300d60800d4a41c0c82c0580354981c90b254030f90744a940321807840403001000905070350a1008105860042400401202c800c20030803420200884400e03a41500d140294141c06689014240f0700030900c0040c1204c0c90b1030300341c2400490500800c60440f1440302200b01c040e1070750700b051030340b038181a00080c088044900303da9 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 579184190 1250 579182940 579182963
    0x30f0702010b120715020c060a03151a070f210906030606090806041707080d05070e0402120c0a030b03071d0711150601110d0e09090f0613050304051507 67
    0x2402c11149141d0f11404400c107034002034042c0003c400380c00c0c44c1344e48000d55004951400c950500083e5469005c0c0c0503000000b500c40d50314002c03100c00c00d91054090b2066840b4860200c03100400d0101c0c4d13010303440000d0540008050b089003400324442d43c0320441801807015400000400101904200300c5220303820000e460034000250710b5120305a100150b0300c804000d0982d540780c40e01c07031600348071120000d503408a10401200002888241c01090320090291020600c1d1804807000b405002204401038040c0303004000c050004c00c000b0345510751002001d11359507103030010210304400405001440036058450301e000031a0303103001622001c82030b008003d01d00309203586010781107400c0501c0021113521070388014104154601e201349401e40c84103040c98a00c6414a030306001038501020b001c080e6011a00302e480d5481c0504011091640c00b40d030f140010003594844d600101c0d0b0b603400c000d08176060402d00c01e00c980304000342130003100c0081c140140840c20400c40d801c0400c0740c50344800e008584114206 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 579185440 1250 579184190 579184211
    0x180801020408100c02121204030207060c24020f16110102011503031407021302030a05070e18060409050f0d030b0306011a07030309212003071407030206030f070201 72
    0x5000300c600703640005001c2d0a1070700e126503c080c041c00e03040c0418001d6018045a906400c00588090319210400058140c1e0350b0506050103410b01c442c0d40c000104100039070607a02d02003112503440520040c810070400c0b0000841000020080c05406800b65282400042180003003082034400c010340350081690100d180101c1340107900f260390301d011012000003000b10800100c3d0040480d16452100d50301100e2410354145e001540030300840d031507511010390101c02d11104504602c10142c5c0b10741c0909100c108850001b0000d18002078146001e42104510ac0c0003c40395107854020200d2698442d0450341c13031206007011192103045024000001910700100c2c40b0241c540052000d04070703a507400c5041480010000318105a90140500307400f032545410001000030000c021358001c810f01c03049203403040742e4079000045ca00790074100400403c9a070062a10700ca4240407003105c0740e10b50700c00301502c41700c014807a00e5400d000c6a0380c800f9602120100c1000b0010354507400c06403096005500070002034450 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 579186690 1250 579185440 579185443
    0xf0204030209150108062209062702130b06040801110304030807030b060909060f03060414070f08030a0302070507080102040f0603050109020723010e12070210050a020c04090c0e071808 81
    0xb0f082d101e40011915008078442e0300b00030f01e580f6260094000d00c58441d9107410020380540303600610450741c0300c0c0d07200c0d82c652510b4242e503403007040c0012001c11030703081148a4002404800c8613012031088113035100e260030034070703660a0f040310018400d000003032000200e000c00c245107581007114254042020360000607401c1e4481e100c0c0c039142c580024003d50505581c0c2d8184005201c1c004c19454014007800f140500d595020840c079442144990002c061881001c20000d0074042d0350b520582c0000d0001c0300c180a051804026244492802c2c5001a190701003810070602c2d0110640c005030a070f500c0014081407501700030104e83d0a4400e00d48051090b640c5e03403e50501284900c002c050125051039000c520302c0d641e00d98040842460312000800c00510a20015090000904405040c40c1001845204604001c50401d45901d96410002c0c00c001559a010b91035a4186040903c202d98842215040106185424000e0440c0e0048040c0c1c51a0050303020742a12050090180302c1119000c000910100 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 579187940 1250 579186690 579186721
    0x423100609050609100e060418050f010b01020307031b0c1d0601020601061b15110f04030b0705030105030d05030c070c0b03180610060e060d0908070303050a2018040f0204030209 78
    0x1700c1c944104a00e890b000c140c2d03080c0c180180003c0d9002d5180d6501c4482c0c0e2180000b01e80314180507001500c102d043c085006400c4917050383d14141550814081100440c1d00500081046000a00c01c8085079226107420300c4011400d4225824010981250303180704d00010207000e00c030b29000e80031900180d8a0b0b503810385640383c0310440729114000280c1400000340b44d6500c02c1c00d05565840b00400c0e40d500341c07c0200c1c0280c000c51100440020b001c1802c20034007101d0b007041038004e00c407030410b11700e9541000046900c1c1c800100d503007030500500202103000c0c11100000c0301c03100c5c0d800034001024241ca41c0304480c0540e205a0f90031803d50110480100c4801010a40324000e005140300581e08a2400e1426240c080705039140320b911130010b0040c441070b43d980e070081050f101d00c6100c002d980d842d418034014013100c20103418031110354030b020781d41c0b00218203a06268002819220441d0303100c1042d10040880d1449507042c40350440c0c01d1281c1808200b01c0740d000750040c0d0740b080303030007000703941e81d12010000708034 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 579189190 1250 579187940 579187951
    0x3030b030c0607120c170c12040f0e09030c010c083321010e012c0304120501091202060115110706030b010912080403061a03060423100609050609 64
    0x20100304400002e52503003481c000103296401c025a50369400d4544020313000300486d1281120740c0004040102c54001d02c075141261901031416030401d070900040162080b180c5c0a40c200c1d144c110000320324038400401c1038032000711000000b445410003d0701c0003011241d082d200300940303489200c01c0b018544040c1d030012101d8021143c2c90710301c044000701000100d07407041058610b664040302c240d4550890030b0040031088030039100045500680d4158000002c608101d41d0b0096144404012448040c003104940883e0041e01c0c60b80d07080802800d0041c0103118005000300030301c1d0460305d0100b0b1141c012034a141200c036095101d0048501c82d80c4103481181e0700c1e043d4000aa00040030910103e40243d200e210940310614044000c26103402800c1084500144241c95800001c40d081003041003601a0000c6002014841840e040583c00402d0303450a02500041c1041c0c0c3c0d00c03051105254900c01100e01d00c02800c7d00b240c03410008801e4440060120340940703c003803828800000e50318100314940034001d0 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 579190440 1250 579189190 579189199
    0x12071b1203120b0f041134080918070207081002070203060c03090703200a140d0f1e030302030628031403040b0712020f0c06041403100c0c03030b030c 66
    0x8002d06a01e04004080c06440c42d42c0c002400411661180c840b4803402d01803001d40380030103031350b030000b21251070483c0301c2c2d804c141d450002c0022488800444046140501355408201c190305c48500900058111240800142e01003c0200400402c2940081c1c00d00881d000e00c01034500c5680b0856155040e481001c102a404d9808140880c8142440d880150390180d1000146c8180c01c0d26552440c40e905080415442041007004012200d40307060071007400200050360404400700c0c02e5030040782c500421a880a0700ea505080030180a0004510030b0f2002000d120380c82e0000c050061070b028000f5002a5103070340c00b621a088140d019150091007501c5588240740348115054516600c1403071100d4004603800786400140b200140c80b210003030140c0401d512809043e00400982d000080c40d01c84405040c1005a210401d00462625040101c0d010382d1120a0584406061000804c0c58003801c0921019040d1900740c024000650140001c20f585200360b4061003404480c1d03003050f82e41e80341c6501c1136600 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 579191690 1250 579190440 579190457
    0x8070302150130110d031d040213090e070b041d010e130b1f03110315070914010306051005120c0309060a0c03142805131412071b1203 59
    0x400d200440070f000001d20510100460b45164400304514081d03074402280401d40c4400c405100070a61450000e5002d81601e0850030180c00000c46012024544900e0034910b03521000300108810a103d10009410780304440b5a40303a59a11412010802641002c070912403075000124001c01744412041c0900580c1d141800c02041944a100d6012800703480007e5104600c00681e0310f00800004480055014280e100240c01c003d405050030203000183c9001c4461021003080f000c5508100014181ca03460400c0410010011005078005c0000d5000558000c04550154028a92180c020422245040d07800341d502e440340d0000600c240002d44a4040603048400041c0c10055079a00c0384110114520300070482c012500d44442c3c02c110140c642c070480b2840d08440942d40c0e0754500b0211a12030700000200014038000280040702140d158004101d801000401c40500101700202c3c443c048080c004196038051b11310b0508030341c00c3d48105445284540000c00103503e6004601c07042c4031905500c400c4107 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 579192940 1250 579191690 579191759
    0x11206152118020405150102150a020705060906060f03070e0a1a0619021b010c14120d15090522020102010f020f04030605060a05030a0618080703021501 67
    0x40c0103000c503450001011002018400a841a0261458005540700380c0071002082d4018841513030001030140072100c0303009804950a036800500b00d00c100c0d2000c40d110b00700f03440300c82080c00644181c7c2009007903446030070148007401702e0104d0010b00580080721401030039008001415115841da124211007810050006002404150030240300100c40c1c0227003410060003080060619040568000c00c80328420300c0c410820f0f078041040d01000103900c1214125a40f1050008141401c18000146114400c01d42d200060030200000e00e01c0881646000781c4070030600010708010301013011200d040d0764044000280c0314810b07214040c006c1c16400d40f1803801040010100b4079400000c0350480c115940c5054031005203980b0b05c060660386980c000015a2a407850426070280d4001070602d51190741860002c11850350006088400982e2144c008121036032010051002d00100c428090000303070700016807008140e40450f080000c1e201188001c0e4031030b40c0720180004040c0c04822140c445494100c90400c = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 579194190 1250 579192940 579192947
    0xc0a15050d0b04150b07020a0807150315030f0807050607140d2003010b0904050603010b180901060803122e18020906040f0f14090406051509040c0501120615 69
    0x1142c1c1d01c0058000304504103801d10b814018001d42e4490042d00402180072021480c0203804007009114844c010404d803400c4c000e101800c10820280c6030300789903070354000114440d80c0440c91401140c2000c10200d5803890740c2042c807d5a803100a0071220750041100103400e050103040c2607003000c0704442000d8203281c1000b42d10b10051402401d5403100040341200710704072030790503002180a0111089055240c40c0c0310414402901d0000c0c094030700c680d0405018000b180c5813202100304010689440003016102c99461500400300c0b5007048031f15000010303101c410340351920b0b070260042c9000c9260b89224540d030706160701e0510203032070240c0c0c4003034008000300b15030364514075501c22119000000525200031080060f80542c07140d0700200c0860000c10040115900c2d081254006140302c01391b101c8421003040005a000754018001058196542e01040d40d0110041403500c00c1e55010346200c0345e07406c10f0b092a085c5000c0d0307881001d0000d084102d001c1c09000a40c0203000c2154003880c1d9034442180000e0054 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 579195440 1250 579194190 579194201
    0xf010c2c0d050f011119020a12050f07080d090b06092511030705010903020d0807080105060a03020f0304030905031c090b030601021207080a081003051504080c07080c0a15050d 77
    0x3600c1a01c9500c503440d80f260020b100d208255410014030a9441124403d40e0701c081010070040015900a816114081115411001010a00c40c03130302e10358031507030350100502500642001800c11030001c00c201c400f4092981c811001c00d8041da0341c00456a0f200c10401400309021940b200c10444011103115040f1150b4a1440e0400e505041206002011801045c03440d08141030a03280d980d100e10f00a030a05030140400303940c1542501e8411440d01c2d00c0035000c0d01000c01842580d00803a400035023103401c00e10030f40c14ae540d8a540b0014030b60b81c1e400c0604005102e081c441c01000d12038016507103814040c80c0380007001341903140c890b02c1c0d0141d003904e03180f0200d540c3d4200410803415801901924414613100070010902e1a101d020026142d186c1000002c00d441402030000101c000040024400f260000400aa14845079045100d00b41d80720718020300d1a00a030035440200e48038062004c100d5040109185142c0c00d420f55803065103d81d100c00d01c0c3c5030803003602c043e140421010880442c0300b040d142c110 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 579196690 1250 579195440 579195443
    0x6100c030f0e0d05060615090d1b0b0703030f0c1d0613050a1e0b03010501051b071707180908121305070e010509060a0803030c0703030603050f010c2c0d 67
    0x700e022080c00c0b001040c0b04032405a401ca9581c0c00c604100903d500c0c06560103858401404c00f4079040121304404202c160f41e0340c000c0680031000500c08003e201003014103182c081c0091000850b00c0d51028640a4040c2501520100419041401103521640704280342402c40305030007518560502d040b42031080d0380c0d10040e8800000c550034040481d558440b100b00740c00502444507000510300b00b84515101078803841e084044025401c100410441ea030041c280c60b0304140308201030141c2124241c0c040e1510036242d2050310000e04104900c440040045152000c540800751072140c200003414196003120343c038200040503110705001030010b0101070001c05511003500b8641070050301490f12020300c2c10603103610546860303005038018043e40c20031401064120308151852212a03042000355034407400002c083d00b5a445000c102c09061600c00d4020030002c6030032070f027074601c00a02100e060780070303100448940703020401e802d070305000380c0125055020140100c07007901810042c1310703420010845d101110 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 579197940 1250 579196690 579196697
    0x30601090b03150103030e1903020109090c0e03010e1011040308030a022109030306100507020307271a010207050d0803040b070c150902030d0c08030619030b0703021206100c030f 78
    0x3c04814044014490340c0a18003940324000f02e19290810001e4140c0781c60400460b01c84211401c20060f60404034440070f544902001181c400c41583c1c085031059003850710554598203043c258a026000030402c0510090703032090501c104110075113440740702e20641c0b0004010080404c0001c05040071039000e07004007204520103403030800116000a105280566071078155420020611030a03213043c000784100b40c546030800c0d0342850680e40020352208594443d000260440302c86124180054240d9204180c9a0340c204000030402d0525181030b44c0785120005002d13200312407010802c0c1c0303440843d510381070380c4c040c1c5000d145a0340c07961a2042d4038000380682042c0201c3c2100200040d29014101c0e42e04402c15400050360460380c010546043c003405840d0041c4006050b02c500403c80c0082201d5010304240c80c00c2c05980c602041907031905400d0381c0058142400d1006019601da410703001400200c0d1007a04642007600c8000c200702500407540c003124041000d100c42c14000a01900d004501c00c541402d = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 579199190 1250 579197940 579197953
    0xc0a020a0b07030e1005010503030a0309050c130e010b0402030c07110d0206030c0a090902091e030309190602010e010b1e01120f0905010e030414090a15060309120e030601090b03 78
    0x1e5070425000d10586001001c41d440d8000b14228a200304840c40104079101030034003041d490080403d40700c0c8074040c0c0c1102015111108642440410004c80b84200742c042c20404080c00c85e01e600400402680042c00441c1d42805032003001803401d402500c0c0200c0c0c00c0312800b4a80b80103a684d1034180c41c013181903560030441c061004405039442d03801070b6100310924a0501ea403400c601ca030083c0560080d4000350400d52050001510075113507a8105c443c50340900b20704014600000d40000c0c6135010b6038200035400401903041440311001815100c0450f0301e503800a201c41d1010701c42c064280c82502002e1034010300500d103400d500311103c80c0206914801030400c004081c2180c002d2006455400341030004042c0c580482d8010020240709102485040340c014500701070910b003c0501c04032551a003a07115070f800b0001300c2c020744a207034442511800701500209685581e1100500513001c07840040e030b00c41c0f4904c61a55100c1c0e009045121507810010050211607080c800250010034002400d940c16201c0d80 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 579200440 1250 579199190 579199193
    0xf0c040c021f060806040807060b0a1a0702211c020c010f050a0e2e030b0a14131505010f0302031e090304030c030c1a0406020a021e031507110706080c0a020a 69
    0xd200d517500480c01032401c9607603945181004815141d0010100707004540604013007145400c040364086008800c1070007203a41e01d0342c0e8000a006043c0d803202c1d00c0005d035807408524182610028900c1031007013048400032800c121009040e030b1104651703001d590204102502c408002403240c40102402821030412151412040e8040396001c0a0301ca04018030f890749245554400d261040244000c0304146003c0c800803c1c180d011410350340281c42150340510b003042d00007429560313810290700c18035540302007000149041002d80c001062240300b014040b5410b00c04000400740300b40201da1040c0144949050300b0644901200b0002c14010400015400148808000180007821600045004072150340109040007881c541c8025401d8510380c180404000c100705207500031034500b10035501141c0305d82e4584030410b102e05040c0103036980e03a41e0500070f8a034103544440c1c000004600454172075440e104080d100c0214a99580313014090b0340040303038030800050031a030000c4c001071000c82c0c85441924190680d5 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 579201690 1250 579200440 579200443
    0x60c020d21020a060506060c0c1e130618020313030c0201021f0209030708190b06011e020a03030507051305120307140a1407030f020105160804080f0c040c021f0608 72
    0x14000c0381c006070030407030b44402030210320701030036420101c100c500710300c3d06000c2c40c0c5080e656801d4401490040c0c0080440400384001001200140301010344102d803212603411200005040c00d02403501c0c0d00510510f144140600ba109887c030400340c491031981e01c582c164400f60b4440356044c40032411841001c102c0c4e40780b100403204500c41d54040050150715090b1080405081882c1600503016a07480742c81480c1c3c11700800201200100d42081c0800120b89409004868404200d50740741d0301e11413010340d003800259000941c42c803000d002e5a020070aa40301c00100301c60300e10404940c08801a1444024402858803a400f03200740740101c006c4900d0400141d03036800d5105244030442c812500480d82c0801884040f940402d407000d40c04018003009411655a0084041d184502904100300803660b41d001d150000d0320700100a4200018941b1240d0380c8002913580d0300711001018850160540401280c01c00340941005070503a90058041c0d9054500130481d4001c030003024400c030903107604000505950 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 579202940 1250 579201690 579201743
    0x12140c030a1a030115030201080c03060a15090302040c0807031802060a1b0204090b012108030c09030f0601090b1201050606040b0702010203070b09070e011e03170903030409020403020307050a060c020d 88
    0x405c0c9006581c420320b50b000250110000030710001380c1100030010004c0300e584803006101680c00c0ca000201d0102c440c00021111010300382c1000b03412501d041000307203085030400710061143d01181e03000d0080e000002030808110b00e401d5402500a24184583c4810f54050110040d2030000c010f40c8408014454000405907001e0030010348003500c0d10001071080300d03903e000d401207880100788004002d540310303076459200348070041060a82003408598008140d5003408070381140340041d0211681c07941c5440e10140100541010144205540142103203008410700442c0c1c82140300514841c10302d41703000c1c1d5101243d0300c0158104e0450204014100002d00402c0c0b01e01d0107004501c0c02814264108160ba40c40d0400680210310000c000701c207680708040b038524168082d03070381c442c840780350710b00d5140945a03150080f8084030390315000226020030501010380c043c0040345d008030201c81e9425902d0b000d02088200d140207000008005007501c1d8058104038800901051050711002e084a010302c40354001040d = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 579204190 1250 579202940 579202961
    0x5090a020f0130051006210b010905041a040615050315040617100c0525240b1309030813080f1b010c0807022a030a0312140c030a1a0301 60
    0x141d8403820b00c07612405c1d40d07513a00003404890400d6480800488000048000d84040202440c1c1d150034500c000c0340d100382903000080c030001e0030611402114040f50001414400720550090f85443c50000780e1101040f600c010080d480e495113880c581b560110700b03100300742d0030b1071103238016450b03610008800306600c2c0e14035007030004040a80304182010340300409440d84802c2c041d040040c144040780003a0001400c80e5070451921416034081e01451400c0070f00c441d0000f003c195111401e4107150360210198104d801820404c07255000d10071202c0381d06508881101d07001034005840c440000784075020403e040314405001c1c03540c0e039060000e1844443e4a03588200074410001107248000308089000340981d02d481405810011154070704000002d641c0d0481d81c0c080e03903030300020001c0300607513400030a1b01849071b03040038003505d115948504024002c1d8103404913003403c5500d4400e6030050065000119800382c1050b0503484c1c999200c03040414040c0c07072a032000102d481100003102c0b403159400d22031f0200d02d2 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 579205440 1250 579204190 579204287
    0xa020a0b030106030501090615030e1c020f06062e020111070807140127110d08040e09010c120b010509090a05091005040807080c070e070c0605090a020f01 68
    0x20b43c10481c00405460b03060b4041d1800b035003000c400b40141c840c0c001c000201503209140008134421100206441d081c0d80020181d43d00040e081d0700344041e0703800b01d1a8610200b4090481d003460303ca601c18000f42ca5008400300498010000c2e07100000405110b00b107900b0081440041000b50002400300e44a0740414802c89081030002050780c10020b6030740380702c40a0380c400342c0208142c00e08035552040304050604042020f034078a0f48018100404c940c40c14142ca03001401451a0514514054070154840d008201d88488a0760004100a005026218a00009643e00c01d12000c050461602500380b8200813410300009010070400c0e80c4038a60307000e10900c1c0440010440c1e041c488486810b00d11000c2c00a41c005040c142000082858503044030355030303644030908643e00d001c046070990801d407036504600384000141051040e026848200d0480d25030042200300815160054580d44e5212070080094006a010803006c10a45c0201d0314034103440f0856203000405001c00c02c0e83d10704202120f80c0040078 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 579206690 1250 579205440 579205447
    0x90403050c1f061202090c250f0311032b06081009060c0903080306090604060302030f0109020a0608040209060d0825110a06123914030c0406110a020a0b 67
    0x510319000e20f800501c0720f01040110400d860f0049640081d0007000140e03041c600060360f096034811410001a08501c05840c195066a1860940101d46140100380c0000f04a0403000460348404805c0304e41040914101c2280002c140d00104805050281c4003099940c1c0c4210024090200b40504002e000350145d002a800d00d042c50580b04481d000c4104008100200e501440002d205000300c9802010844080c005a500e110016010380b041c0e800c0250580501d5121710884441500600c07081442203601410940d100c443c100c071400c004590180d4014075601c086174132410b0000036406032500844034035181c0152100b5403c268400c2441c0900324007480813040c0144015200c4a0001c080100c640980c0c0e60700d003403001045030803507202c00503485030f9800620304a0010088501039403694440b0400390021150320301000300c058004003c000c510510246001c0c055000d040300d00c00d9024210bd00c0c11f207803c103401200c1189101684a91343d12a00d006107016a0310180c1c010020694454038559 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 579207940 1250 579206690 579206743
    0x2210a1b03051f0b040512010f0207030f0e03010c17070c02040617060f2716030804051c08030c070f050f030304050f030901050405280305071409060f090403050c 71
    0x94003003101206002c84100060601c085081c03c4100c5c0c045407012540844940003600c102401004860306c1c40d400c4031704c00500c5a0400d508030952416180c859221041c50b10710007070030300d42600d00080750000041c208030a5100c1e18003a8002054200b016860202d440504550209080311481d03000b03441030410b80b14512401020030000b03283c0c40901800e20840500301030f0784d0f10081c1010520104040c025111100308050700030030406041c4800c1e01419410300340e8030b04004419a001e4014140141903190030841d061075148200400390b43c0c080c46491655407504642101030f00308002c00c070351801f00d1403c85400b0450402182280001200103507075a410607142a51078122100035100b000d81080c030001d05180e0308401038808503201900c0c040c59041188040050412604280d148014440407000c414850001488400d0300c182c00060703c50342038007508001c10790b20200c441541c410000c0c0d500c1401424043c4655402c588039082c02800d0505a103405820446001400780050340c5188070900c = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 579209190 1250 579207940 579207961
    0xb0a1215080c0f2b03181203090e1303080603070e0f0603010b0108011203050d14070e030c042a0504081e190b0f1009060807140402210a1b0305 63
    0x504514222001060341204d4407415070007840c41c035914000c0441e64050034090602907800c1c90740c0c1000d1402c003060516252440100c400070158400d5002440d10003000c241034902e040c8007401240803204800210200d80d8046500c800003d0069405000303000780015003c4401c901580155556800161640380030380c18903003124002d0483d40e040003124001044103441c080300c81030701103406182c520358500485aa00b0003a008560941400d07140341c50401c85660752050042004440450584241503440e008100580c0d000e811244402000e500d00c8203000711070343d820051b042074682001801c26540301da01d98204405400000d0f0440f080b02c0b000115150207000200318000400304460380c1903003540780ca10042c58002c0100d004041258080303a910400017910100802c0102005c2c03007003a0300d500c10140c84012510420b140c0900780c1d44040c28528050090700c10019964290141e0074506001219215501034131700d2140c1b40d070301c002c840d10161540803200c8c601c41e02c945000c609810a12001c0 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 579210440 1250 579209190 579209209
    0x309050c1e0d26120a090804030c12050d030b1c140a0c1401020316081e0406030f0f1a0d060b0402030c0304230c04110c030301080d08010f0b0a1215080c 67
    0x7003a0311400c0200c0c030549040d1044c01d50b00315220343e0001038580a1031414180c24031a540001d0030001c0d80c01d40029050303120305032203103105103d0001c6c1c52003040d21510035415160300b0392006901030020301035184980d040304070600c0064003642c1c40c441001c1c3c000010a003444881501524030a0f1a0ae80c01c4c01800140d4909010b000c44c20710085103402010706014042d81109480145a0000042c0001c8000c40d0080350342e14442d0401b41856589a484002134002c200c180103481c1d01d0750600720241c0e6080c03118400e100205114003011b410308980c400420490005030307402202d111381d45080e8250341da2240d10155201d4a02400040e60703d0406003000c020b80f210b1840c60fa0321000903000c000040501c0400c40e0b180343c00095a011440551460b040e68050146100369100d0340320110000424040006a42c0d0011010303880301601d907625411141080000c90160070580802003000a81084c45503411102c0c041e040d005c001120700307815481c441200416440b10409510140f140e401d81d15144809 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 579211690 1250 579210440 579210503
    0xb0c07030c08070521070b03061f2c090a02031801060303050901080604090224090d0602070605010e010b07030e060d020a0e012604080313050a060e0d0309050c1e0d 72
    0x107417520540454a819641c0205010380010f0840200c040380081c0c8400070106001d00c00411100e84146a400c070040003882e645000085800400c04440c552130458255000450000b61540d080c0c0d541d280d071801c0180d03001500c0e5075020540d0401407400c1c13641c00e21822000c0d521a0340c42ca0b6a805e201d40c001840050042d100f58030807441d14000b800107a07101944424007281e06030210f44003030418801d080d1035025490303940743c001881124100800c40c81da401080c1b524031a000400c0f29989450ba0240502024010490454001c004030004a80180c40001e40910000c2105142552790a6150180d802c004c1c4442c0110f060f40110184d55070700b10303920a440300300008544c06080d940540d40e032940000030f440034242c00ea000000c01d0b99185032025003162140c012084620760a070070303d4664020228191b426070140207030034641001320721038080c11a03c0c075000f0008101c8004090200b105030131803204041c0c04c1c0c220380900784a10b40c552030f004c1b0302007134041c0c00b14040c0d00c0c960048402c1c00310301d9480e1 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 579212940 1250 579211690 579211729
    0x1a1e12040c0302030d03060b07110a08030703080a0f0b0102150a1e14222a08030d05091f05090a0605010803041712071b1a0c0d030509070b0c07030c080705 68
    0x3c0230302802d40d01000340d840c205d8000710055000201240868000134544c1c000c1c0c04640400220f50090680012110b4001d604c40d080c10000c0c0031044403050203c0d0510b5941e240160031480004c084104a40810394003d89a9100000d040b02104441c0c16080a2850b40800d11a150f80d508507070703414080c802d10790210644807003207040d41c020302070020032610300c040040140401e01d80070000f000c030045003400c1e80c03039244080c1060700d0303120740110f80e998200d03400740946181040000345102c4070100b020042d00041d01584604100c2c0486841c0142c0300041c44050b980c0b1030341c13145401280c082d016460090100202030742c4d0342d606069680d509040410104c01007a4019281303050703034004034812030714030b56000b207030860044402407a02d0b80002e5285d4803c40b00e0702c0c80810107420001c1c1d05401408110014001ca494803d000d180a4060391812244148290403251080040301c3c9400c000340054801d100c141c134007207a2203554031045c190203504149819400140284810f007480c10896000c1055100d = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 579214190 1250 579212940 579212951
    0x90c030e0c150703030609020412020a14060418020c0a150e0f0a03030b01050c01020c0304050f1801033309050705060403081e071a101a1e12040c0302030d03 69
    0xa002c80e10042a00300c08100000c4001022800c2c10710176400b00020303044502e400c7d5506c50341d440c8040740903c68080281c0c030806a02d4800254040200409000e81d0000b0300031904041c90550a088030000c40104403402c2502002011580300c400d01100f401c1c14850501d07080e0422100b45124202e44445210124a910620000200080010b11982c02a605240204000090000407030711800f031401c90700c81e1580080340300c2c240060044054010703140240d815039001d003c103400300502141400c00540c0e15452450041c000f0456407a08050700c00345442560002035069012015409149441c400070581c0d40c000f10001c1003014408100180002c440351030400d421038617612500d110700e28410042c030700b1401c030740c41205911005540b40e560300503810344116002d05100022900003100c2052100480c1400440c031098220319806a410382c5290140c1015861046881400d4a140500480703000034003403c4001c0c41c00008240c407584c400e4044151051440c81850301c2c0c82e0340c0011020502d4140b0 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 579215440 1250 579214190 579214213
    0xd06090c152105040302070509010b030a1b0f231b10020a090621050f150102010c02190f060c020a121d010f030905030309161403060718050a090c030e 66
    0x3403007403101d450700a0b0342c0010b8a4455190981c60030510790322081e08031a42c480001001160a405940b044450100610003214001c8052000c401039036400e80215100100102056214010300481c20301801c056041d040349044120ba285d80080400e8190070070007100c01030100b00300b8406101c0f00c0130000015424013100100c05010780c4c899028030420031040303418041034403800c4e6110422078042c4103000c001500382810039464809003143d10141c2c028089842d403045500c1485088022100d9602505070202c2c10b81840490101c0c0d423005581402c140e000540220f80c080c4104459403280e03070010b240000540c5003052606d820031495005110a050313030aa08507a03c034100041203002481c1080101c1d1507198241d00070320320b0b200050518070010013040788501e4001148a28440304046814289995842e066908803032505503e8043e0081c0f0003041d0614016001415204a00ea004109498550002c01c064000fa544800c045a45820791045007542512075200d420103600041c00c84031150 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 579216690 1250 579215440 579215477
    0x618080f030a020f0a030b01030e0c06031503070b0c010c02190b06121516140f0901051b0d0306050a0e0f01030b071215091104180b0d06090c15 63
    0x1400351a00e4650000800207807803200b958110b030b50104014032810340b03410210328018000c000c13560549011920306040ca2042d00380020740d0752071001006050a21f155640e9940200c22510390080c15014440c03401c3c00b140606102c0b000d0050341102c0c4000054034000c452000b843d103061011000c00901949801e01e0100b00014000c0d1342c840b50541d01c0c028420740814100b40b8140e10052450321130b41070b01047c40200301d44291410400c00950781c48021550354882c0703002161003005440640b60310100700c40c950650140e40901515149101c40843c10b00c107040440d410910300713000d104000ba81c6c500c2c042c0071a203009440311000d8101075003800180c1c80c144000111464041c0030180032081d59200140c196440f600f10341d0780e4220400424002281000080d024041003030007140a11410001c400c081e04e504034060710700305d0b41c0c0a0224a03802d15100101e2000382141082c0c4c0b45c00c0300d080c442c4580403400900407a00c0043c0b05207240c48a071480d144040031004141c4ca50407040102034412200013102 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 579217940 1250 579216690 579216697
    0x206010b130509060a050405040f05010b06090117060f06041e121212020408030711040b01021908070204091406040210080112020f2707080703061d0405011e09061808 73
    0x5007610302d580d41d9103440700040c0c05c0b0b4600ea48081c0c0d02074103103401c010070001030342c5018030b1442c0700380000c1c09556040e1040100b1401007000c1c140c0040c04015032103400c200324802d40c542041c1c01807c5504201c510501044c030640c020341110001031144031100614620015510008007103000032001c1859031591000c1c290500e0301c2d1410300300250f03056401d00200d01641150000c2c0b010804407a40c8080d00d1134001c0545d281400c042d4031480c60550218015400403480d6102e00c6c010942c488154602d81c0d0302c8041c80c1e0050082641c000340d41d0219800001d18808091044c0c2d17090500410292600b071040200c10b00010400404000a00c80108001c649160b4002c402d694125443c1d050b00d1404400310f80041e0507010707084842110900c0c000744d1083c0d882050303400749261f83e8803100b56030350b101810742c252000d42c170580144403840007140d01c50030702c03c1d5881504544a00c002050f242c00405020030700207120103110030b155a440c9482c101704001c0d44a0383c124075103031509081a20b012030f12200c00500 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 579219190 1250 579217940 579217949
    0x1b0e0c09100f121a04050c040b04120822031e050304061b0b0411150a05030105120316080c1e0303011a04080a0308040606060302090904031818020a0206010b13 70
    0x30240b0500440e840c05152901410b9808040800058003007900105108092444182c003c1d4030b0038004c07d0104004008031004d803014900002d2030103203401c1d01e403d5101d405c0082560010014060b0901c2e1041613031172138460314a4110f58003109815810411032580b4601100300000000341e000300000b880c0403042e942141d401c0d092051022481048203201e0141c0e01c280180a0706948041000b08159000360700c007580c0c03080e00d0003207141c02e0b070f19140c01c91481601c000002181041c0700400c254581040304080c2414200c0a072801d01c070f000103844552151407a0100c5110402003011811032804001d5206040862080c0c00100035520050341c0c3c40740300600130030010380012204800c9c00c1440504a400801c0705400b00c964030000b13410020072501c030569003221030317509003800001e180e0302c81d009541000c42c000340440d542e40c0303542d981640c4803107024203042e407900800c0b88005480750085018080b000c841e5940965103202d0000001d0800f54144c00142d07000001b4041000c45406407952002541d = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 579220440 1250 579219190 579219197
    0x11b08041214030307300207080408010506010207030b042907090501030c1b0f03030603051506040b060a0e0d2105070605060a0303022a0a060302090a080c0d1e1b0e0c0910 75
    0x1400e10043c5160f4000c4081c86c081c81c0940001007070020054080000c100300d409020007045252a031100480c0c941940b4403001d410301c0c80500101e404110b0149241460782005035480108243c4c5400c41c05280c10212041000702e1103504040226580502402032180d035a85001782548401d01c58181c40e0f400c080801414282c100c0d40c0c09410103003c4c0d4820006540c104045480d4810241c10541408074100c450501540c2030042540040c100101a03440c2b51000f600d45000022006040c0402e1208440050f240300c9607441a002e62001020790303800c00d01d01c403940d603182d9034519420f004050f6407020b040c00c1d019070486502040821350201e0400b5440c01d049140083c4074001000c01c00101000e400490740c8000c080c2c00015180e0782540c010300090f0407e45048404640d034082d41074031340d640b400b00c0d5601b0140004440700001c04040807687c5081c1c03140c66400c2e21094546509510a07950712002e1441088600f040c030642d4020441981d00090103000b15181c48034a202040c07100200b040181d091 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 579221690 1250 579220440 579220487
    0xa050d110a06110d3204030806010503100e070f09050a0308030402130207020315011e050105032206060f0e09070303050f0306010e030f0313080a02030c011b08041214030307 76
    0xb019807242102c1016001d51810301c4145002d454a0b042ea101600c17440e6441d041c215806890300b4490744d440e134480c540586460800703507140c00056803181d000410381a8044100c3c100880c4000005607040c0c010f4181c4d41d1402104c0900e8407003d40100095040301e0b00c500802d400400c0001c0c102001c60b035200c0e1341902c0f100d81441811040b00003038010514001d40c54011200324079100110404401c4c103c1d946050b6142800e507282030440300b42025800307803600207481000052110309103100e00c8810b250041c6848692035425465413011920260409011b18003006810043c0c990a140c0064209a00074007602426140d43d41c0603000d84102d5000441700c00c408000100641e0003464031142c50300000c0d090790368001c0320b1181251a9031103d2500440d00c480064081190f07403001400c1140142e0160040000d17a82400c0117444144081c031403200d544090000140014010710041c0004042c0e655000000da540340c50041111000001d800c0c01c260b100344100140d02c1d0303100801c6002d9205c0040305d00503 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 579222940 1250 579221690 579221711
    0x20d020123070b06130902011e09170106081c0c06050c04030203010f090b0a0c0206010b2a03090114121503071a1801090e0403031802120a050d110a06 66
    0x1401c40715200741100a2101007000b5052000c02c83d401849500200c0740d402c8a140d4a003110005c40e1820180a40092103414450b916258107480b810904c01d650b080020300d2980e15000541c49070104150402680d44400703040040c2c031420061609094118644015142034480005069400f130b480060180d64803030001c42e00c2a20403a04aa002d140c01400a0204003014802030340980003844044560611440000b03000e9480b03807169848c01106035003e441140d10300480d0b041260416541e0003600d007613034001c80040c91760b150040d120440048014603101d008510014110b4000388900b420383c008100408031810300c58811075035004000c9100840d980c400c42010a00d00b80d50358200030700b030440500c580800d0b4406000940281da008144920110000c20b00440c0c0b500c0c16481104101148100801c000901981010840d048502c019400040031a000100c00d5441650214000c5e04040c1c0b0780000c0c070806010014111046083c440c00700c6084900f10b40d034607502554085c0880d07035038031515031 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 579224190 1250 579222940 579222977
    0x2c030a030902010c060e01020711030c0307050d29040b071704020409061526030a020303160c120305090607030b01140a030f060e25020703141603030806010e030a020d0201 75
    0x6456076000305c020800d280700584e145000b94002841070300c0c4540b11002c07105a600c0d000650401345007018020b0480d8514250500999603d0391000303c5107913032010881292007540e14141140302c000d009190201e414281004400d242024004400308100800860404120514190303003003a8161400900c007551801c0c07001c0242040418100307035100520b4005104500f484103000b80131000c03912040fa10718003100c01944c074441d0100e0720000d604144001052001407140030020100c480c103091401140c1992298100110302015402180e690b10a10406010400c0903990103005401c04002c5108a1000a46801c003081c1c252004d400c0002468090a0300c039800814a00710890014000a91100e2119111540131241621805005101c0e00301501c40030b04d89010340380040d000750250900390707183c0c8140c6001380d1900134030354404c510015071030000100c0b120000b180a03960381071203030800c40c00040800e00c0c0210341620130b45c45540d801000d43d4401150320b9480703509080c0b0045c440300110882 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 579225440 1250 579224190 579224207
    0x606170402150c01090510061a131a0f040801022a1203280b0316060e0f0a030f2d020102070b0c0c03070e0411120312040809060403062c030a03090201 66
    0x3416400348840072001d0501f83e8004000703507081140340d036049509401d80300c03900e802075852043d110040003004100c008074030202004808200d411492411124000f810706582c466400034013980c0d80003410440310060814106103400515106503010f08454010b81d41c0c442c1408808551503100101050b0040300c030400085c80302076065920be000800341c4035030600824001e244140030740968070644014801d2182200250342c0b1545510045401d8070b01409201d0820700310054000340340c11404000f00d2240912440390314440c4840c00302040138800c0d40200900e09100114240064072401c000507a0042240b40c140c880803100326031140b00c801c0360549060104042d2542600580303902040c1c1840504007a44502c2c0034040c4031030740c003d101d0140088241441e110740f07126007003031050084401c0302038405a00305016801c1740341020300d0303540000d404e0341c42603200301d07225991101c00024a0030b50500b5441c010a10603105444000b012070030503180c0c41004140b808140d940c00342482107a0044645 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 579226690 1250 579225440 579225443
    0x911040518011d06011409160201090206070609060b04110d0906150b0a08132001200a03080c090102030301050d0f08031501110106030c1a1204060606170402150c0109 73
    0x740f0604000080000d5041c100390380c241143d024103c00458010f0031075030402c4030b041001d8950744040d92501c46c101d03005102c00b0468002c55407284c00100250f901c0030082d08205000d45800524030610385460011a03000a4905000e107050200307031603c14554078141c0712a80d2641c0d40200790380d490740c686000140070103820310300020507602001c16605150b5020746941311303046d00e07000800c1d00e036901264a1300c0340c07180c8000e08888204280c1440359560340c1000d1314041060401c10380c200802c0020130078080c82109005003e0384604108814168440c0045030042c0e00b5800440c0b8000200000035100c0c03005028986c090100340c0c0d090720803c49008401a10035410112543d142e040c1080e000198960364010140000c1c042807005c402a03006100e01401c490b44101c007032030414036080b44040d80d114010318074940d505081c0041e5a1011005030407500c580e2042100103641400c104016203804912105031401d4080d2404001c0182c03944094140c45030300c4080000e40391140e01d0041c0c0d026100c1d0000 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 579227940 1250 579226690 579226693
    0x70f050352020a0b0c0c130905060601140c011b020106090203010e22122303090706030c09120602040e0c120a0207021c12020f0a080d0b0427060f0911040518 69
    0xd901750108000f040e0f4210b068001c0b240300d442d1200c01c2d49900c0c16100501005480b5820543c049906503004000c052a02408202c985050841312183c450842c0d6001688141d8401c000c0040d000c0f4075420711400c0701400301d4180031811541051b0060203c520010300c1c00c103c072004402d0022400c516200c000c9450fa0340a0003406111000f43c80c010000000071000c0c2c040c074450600302e40078020f039600c190b0303200380066001045031a1400c00100c01400540b4450b209202c8401c1c070100e0010b406464241013a4020782d0050703951460888007116040000f480031003294010b2005500100c0c401c40e030140c000802c01e0001d40c40e41100c1c000512a10707100d65210994540c101c00000402c0082a80001c03c0030b0b036a020303120021481240613072120351000c8010240d03801003000e050142c1d410343c4128130070740000c0d10004258240003807a015240d01c0007095100e540c4442010004c002d1140a1201c030f2014000c0140012069503613a50480070116903030912403911100002ca040c2c1c4202e001c4d07481e501c031450 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 579229190 1250 579227940 579227947
    0x506070c050c04060b09010e01030b0d081207030c1707090b073e1c0c0e0f0601030b06091e03010c0c1403030417070f050352020a0b 58
    0x60306500c521030084601e4029540300c1240c1e490540b04007401c40380b0800e10030703103081260001102e4007008040024141940e810b584071a680b6050100301b2924810350289030b40700d130b049031101c440d170500400f44002c040c1006a190080382d408030391000100481c500302d4516440b410000d50301281290400030940101007031004c00e0040c0031803510104992940740e2652000c42010013224128100e441c03100603201c01d0070344030943c1041a89070b0559001414817050282080d518001d201800d680b082c10500014418022059400134407250010800d083c1004030355440800f00d81e49000d5402a103200c0c0313204500320a5940310500107481da40740c2c010000c1180d00d65102c40504100f25580c4142c5440e601c44848404040b00002241d0045400041082d040c210210005002d580000703001c03180c400d010301c2c503140062010405400340148515102c0300307102003103089034074a00800240c1c4000e00503005454261011819040281e501c220001a4440a0070300201d07085082e164040140c840000 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 579230440 1250 579229190 579229201
    0xc03090503030304110907361701051602060105010915110708160b04030b13080c07240206041a0c070b010f05011403070e09040f02300f0a021504030506 67
    0x25005d0340c04151080359081c3d81626000d07030403a031a9142c01100c240b502a84042c100440d243c1c505007806c1601c00104409070980c5411001d601d044401c421000e00b691128148401c0c0c18080b40c0083e400800b43c030003400c29625101c0001c013900c0f1a17108641351a50707000c03003900d000c500c103084c1c03074422850b0f15088600310303566680c4065503191140d0784c509640000c2d01c00071a030404000c00b210200c0c4c1e0002502c0303e80e034807040100400e1003000c3c07200302c55980040000c0381000c1c41c1881444000c180064410f44482c0200c04040c0d200b0301ca82c500c82c01150806c0f070421000544040031189502c2c2254110707040c5542e00700841e5041d1243c0b08005d41102d504174000101a00119003030420b440c001ea075645001a004108100380303000a0750380300003040307002e4540405030828010f0a036015000c0c011009401515401048086415000c0c40340d50603116580c2e1035600f02014042907101c0345d4440142035903c400b1010640f0f54019080082c81010061080401111400103550180d038100003681c0c1c960410 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 579231690 1250 579230440 579230453
    0x103090c24030615020c13090c0806070806010509030a030e0114040e0108010f020a021b01090b07030c0506061c08130b0f04090f020f030a0203060a1809050106140a060c03090503030304 81
    0x801c8081c900090603c0d0010a00401107407007400e29501c690000c00c0102d402c441084800601c11100304070282c0d480e0095804203a1303480700032004103942005064542880c038401000c0e0b000040401e03050140c1008803408984000038024085501807a15510100800300100c1d900e442a40c03014a03850000700300811240c00c58100da07412602c0400c000c2003c590b45c010380c0c400740c0c003501c800700c405070300700014441301d084042d100c014410005262408001d600c40560f2000d642229130107400080f41d41030120100502004026002001103c04c10000d450070240014880f0300ba503c0203000a002094141032650b0306080c50001c0d040e5000c003182c0300c540580c0e07130811682052246070311180c00c091041003146681d2084890f00e40c1c694200c145103640702c03601040a940302034100d940020104034009800a03101e03103249200c030788004011170301d0107da090090035145181c001c4982c2c100601303070220003030351a004c58a080358010b090100c00e41e16142010354100d003240d800541c05010001c00c0204102c070 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 579232940 1250 579231690 579231749
    0x160509041506051005091c1a0c0705010207061413080910021906140a06180507110f0d140301053d020604020103380406030204021c0c08090c0103090c 66
    0x7e60351360341c2e00000480da40e01203d4035910090b11406100e841d050340b510415402c1540300c415055491b142441c10b40c2d9903422607014180a44240f81d51300305030004000c411103e107070030071041024503451b8141500c540740c1034851500070a201d1164034003034040542c024801d21f03403190703100104544a0f03580342c101500a8091905050720302d050000004441d290030344200e03c02d81e00540c955940310450003628030000c001c05001c40d01404a520003c803c81003041010013111880580a0450039200740409490800348680d003183c4034109000500080c1c480c868802c1e503058010b5646034244da207004640148941511880001c1031070b10044020b0b0366000202980100c2c800c1e40c08200490120f030304003090000c000c8521540290800d01c20041c80e60348a440754282c40000c00000e030b8190303240d0004049a00480d00d10381d100804a5001c210520140310f507643d0080e02c1c0c1420003052030080140e6480c3d24015048505050341e998940d800d208210300100003420000c0600c41c50020380c800c1010400b003 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 579234190 1250 579232940 579232957
    0x10612060e0601060804032f0105160e0a03080d0218090403031a01050a08060d0624051c03090b030a02041205010506030105060307120b150301110c160509041506051005 74
    0x320b20400003400307911400d03915106940680d140c410f0020b080c0a000c002d10b240350441c0c120340c0c50900d6101240c83c02880b8282c0102d08020784031290a940800107401c0400b4400030503c1f80c41d07000010808200030308215101c0c0c003800d0360b0041e034580c0035029194641907420001074012550104000c03c150709544403100055400d405101c00452250044450b8400e000716280044c1c00d130400320f006410020b034000b009a01c1043d01003040750003240c0352000c40c00498002d03c585040355008002030b0030401c031030004101d0b058008044845054802411452140c452011110300020010798512200c6e41a2009400008e0074004070340e4003420141d02814040d01c0300740c425441c2002003001c514001900104032000a0b04012281e0050b460351550702c8002444024000c0b401c200d1400c5540d820320400c2411210200c1594a600c0c0c01c00c030b8a450007003000040c140c1c29101c83c5041c41160740340c20060398000e40c8040d118408400b02a45a405400558000c6c3d80082c43c5035080032080340c10002505604 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 579235440 1250 579234190 579234193
    0x30a08070e040203160c1703280903051e04050a0f030b0a060513020d1b08180102030609010302100e041104180b060a0309020a0806010f060e0102030c12030603010612060e 75
    0x1041c40d002080300704d00c0150f44429129224040340d0280030302860815410301d000d009898003495840300c0c002d125502c121011400d1203c074a040c0542800e903502d407028812265082002584095075000d0103a205081e074610101007551903200303040314020200e60180c000a030000010a17558202d909003c607503804110388203081c400008003024581d01c10002101d000516298242801c5c8104200235071092586a4040c0e131030b1480d00352140f080700710f000c854007410707070301d0b41d01d00c1c605101c8546031441d01c00c1c030111290b401001841a00d80c3c039038226606403901191900d4082132501015190001c0907101640c00504000c1c170080200850030103881250302c00703000c40c0e41c0005400044411103e0021440e40d00510601070220541d2081c0d00454034144081d0040b1141c68a403115a441c054090b8458041e681102d181403050a910540b860b0b20f07190280011424803c10503001911100050003000342ca45003c0001862a81c0940101004201010a1410f0030005007004405400540c42d005050f = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 579236690 1250 579235440 579235457
    0x60203010e15100e060f03090a02040c020d0c171b1605190e04050a02030703150c08070c060c090b0703090801150f0311130203160f020f0a1104060305030a0807 70
    0xa2441c0440e12a1502e4010716249203048580d41c00d480b801c81c100d803070b50b401c008144512843c010000e401140034692100040c010314815104000954490070740700d400b11340001c01040c50035504114103a100c030303038072071404801c100308102c203007695004003d0072400703d800260515001d000d011a412181c0d000340c140030710403140c80d10103110001404a080e690782d624109010040315180c3e405260300148284140e458040194000038a0a205504191501c25461018000140345845207120301c1000e42080701c09464404006442e42201c401701a18031511003c4084a540c81081944007401401030f081e0385a0056040040c80501d0b24000d2540030346c44c000c1e6280440155007005421104e1131122180c00c80d045690b10068142494005900802c86d00c400c90040329050002d0352191421607a2120f00f4a440702e40106140724042e0140b0654021084440d1000c0c00030440d40c03d41604001c4140b140000e25000ca0010035030340e44080c01501002c01e0314009282d000d14a2030048040350b60b00600d = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 579237940 1250 579236690 579236701
    0x302011104090b0906060c1203220309140315060d03020f0616030f0b0d0807141506040b22020c0c090106051b010b130c03022710110303060f060d09060203010e 70
    0x40d00c545482200706600140042c0840c2032601d0041d0341c020ac104581c590700031180d03044050000e20480d002c0740440d079a001f041c4005081089480c1c0d1a0000701c008046d07044a140c241c000c04180a0035850107032403c8407092007410b0007000f6580003812080112043d92604900c0e80c586400d448030014002810140940641110f1340034884e00400700915488000d0740c40e90f1200f1b41c40d407014004032144140000100007404003405508288004540003108134500801000229541441c3c131511030105003510f0340202c640014200745c0701403501001a0703070300456603581c1d2420280d034a0855002100d180040360320365001c00544100d00d412508007405805d400a80340c280c410b0f44000c240c0015110203c10b40300e0001e030b005a007012032581401894140021490a2040702130480403061014592903100a81000c0e2070740c0050700b100d0b2500b0700460b120b8010f9551640f0010f846a8406c000081c2d0b075102031b40d602002c84550702c43c0d110040001040c42e180c81c00194100740300d20380030960040c00054 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 579239190 1250 579237940 579237949
    0x10f1b02031b010e03060f0f070c0b070906120207052109040515181506030c1c06030308090712170c16080c060f030708070207090c030b0405010605040506040902070302011104090b0906 81
    0x31f02403582290fa000c8181e40f41c031520341c21760f43d000b400c4604100c1402d140002150340106194011012503840c4a0840c0c01c051300a081c00399161075103824a4410070182c0301043e004120070400e940c607100340c82d1a102d00c190600c10700d0300440f000300da400780c6040b00b404144c500c1c41c10050320f0b20701e080d05c0304c4258400380c400482e420401101c011100201e000903520f020300d0200001c1d42e00c1024488481c0c24420706500d01d403204d400e100c032021305155440c0020710900d90080c041c0c1e1343c420b81082c0140081c60034180c201c00d06e00c111143c01040d2851050341046810301d84410745500d03040c0f1a0445004428140f030600071441540f082040c0c1c1c4c024501d44803250305100080b12188021b220b031080c91911105000c5902c920024411011400740c0072001c43c1e8070015004101076644070f654089100d5041204002c00c0f510181e000009001c020401084207842d07000550301115400400141c546500703040607030140850f401410300d0303101700003004503450405500444100304291034292242e42c402c010711 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 579240440 1250 579239190 579239203
    0x120105180c0301060f0909110c011b090308131d15060901140c010908030c131509182d050604090809040902010504050a03080c0f070302010f1b02031b010e03 69
    0x1840c1e519030410041c44480d0084000d01d00700c094616050104c00c1e03032403540c00101ea09913540905507085c002120000c01c8024000e0413940700700e0242403d054411a54081d0445415120003090240d02290603001c01ea005d41c003c000412001b21152043d8490032030701003180f0307400c4a10155040c117030f0000010908000d01580c40064042c0c403000f44139049444958003c0d040400c044003959226031003440040c4041e40958065503c10080030303204c04080010300000210740d044040c80d0108075428114140c0d10802d044220b0324000042d9506041c07c106600c040c0800b261614800040308142e05070341d0310030031074034402c542c0c3c045d03c1004141c8403a01004203650001030040d18000d81031245d0bc9080c5410303800041d48500c1410000d1071320780d071100840c60b03d8a0681c4161120140454040c1c14020107021107014445410054014a803c0d82d00180c02110f01e50441410000350070320307115a41021a00102c6034070f4008080b03900d110495036510100700d20314412540040c10304003c030307003140c140092030 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 579241690 1250 579240440 579240451
    0xf0105010e1506070c150906030e0703230a110a0b1c020c0106050415050306010602071d0601030b040905011a011106040f02030a0c12020906152a0312010518 69
    0x720740c1030780ca94080007000a501c04159940c080d00400c48200040c0c1c940303195500610850181950b124a01749016100800030341c40182418100204458450300208004003526406414480c141608201804c01d02e5207186041d00c01d80f0a52484e001480f0101d1840560341c2c07801c0ba120301c20700b504d49603104014021003068000024a68030780b440c203510180c010300841c034001c00001400e503664600040680c2c02040214040c02030791402848030f42024440903014211600043c000c8525200d09440ba1803200a0070f07027182d241140102e040c03a8480d400990601e400140180035154050915500804801152220307004c404031901e107440d4040d49ca80e4444610038030141c8a075030340d680c44c0d10400405840c02240d1500642e580707040013400003c0c501000c1c00c035034444860034901500c1481020080900414420440c00e81c00201c01d02400084600780100302c0e0aa0504110710017540400e0031105215004c640030225030380c100700d6510380c1c449040b9030080f540b0b09001c00030a0310b600f41040081e10b5 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 579242940 1250 579241690 579241709
    0x30e0a0b0c060403120b040204060c0501060902031e07140406020607030c02011b26040c0311010c150c0e0909030a09050d11010c1505010905090607111f1415030f010501 74
    0x25001c130b8020101c0c00b6003001404000b0070600782e14800a41203078880d82200000ca01154501c00a1003030902c9110050813803601e046140d42400e10b42c50448070194410003e0025100000400b100e2003040c4408940c0500940ca0751110303190003019481c0c41007140c40310002841c040503000c007140f0501480e8410a10800300c20200d104d200401c030703850210510080d0030190324410000c0e45000b4124510321a5000300214224503085180801d210800d848640c1d041180203440324000c941440341541c0c000f005400000f5548102160540d030880e001c1c0a1a80d0116583d41080804140030005040c0f052a80e80c031401c0581e182c40400c000c1c40304444016105469141c4904400d501450002001324020303400302d0a807040b400702340c00590320240c020a0045846c0d9041c480c1d08801044001e40105560a0031a041e841c1590300c1035462174003010390810401048a001e00e2401598040c00c0000d9902080201610784480d000c1c00c50081c95000c0d600900c81c0c0c0051952a440c188a894103948200c0b4 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 579244190 1250 579242940 579242953
    0x3080711031b040c1803050a0201110d0e0603060d06090b010603230a020c031e040303030b0f1e060d06090e0d02070627090c0804020a150804121b030e0a0b0c 69
    0xb8280030061010ba04680d09000710240600c4500d840c030f41c262401175200e1401080b0303101140c400185811804c40340b00c00140c0c0000e2602d108142c101c03000c4844a82c007918036603165031b9940001341081502140141401c0d00c1d002d16641448400000c0714180c5000341c07424001400400c40d0801c0100018003a40400b00b40000440d0228582e5001882166500c10480c1d041005806413018a8102a0702c58103405400003410010944c05000744640d81604a50f400940c4a41070003241546480c82200001c1500030051520f8941e6800262030501007001e004010182d20342d1a004000c1074603c0d000c020381c0c400c0303040c0d000203248001206010364880340e986a01100352110018148400b034159400090302d00100030541e050b40c2d10620040b840f0303a58034110b080c10079005001585415401220f40d24a040800e00030f240e801540c800c3e00254400c160b010f114080f1007040720b1a06405080062040014044c4024141e0145540c2c0e13182e80d04658100d5000d5860382d08085605c1040c038881d00540006 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 579245440 1250 579244190 579244243
    0x10b0903060a0f090b070207060806060405030c0f220603061b020a1220011b05130501050f040b0703080108010f062d170d030b0609010206010506220308071103 70
    0x82e0001c00307801c400f49501040d4072465a6443c540002c084440304016409200100912640110781c207400500a80d095843c00c0c1c10a004030ba1981503070b090343c1c0c0c0142200700d0743c82c40030f44520a10304407042a0b58145e9400100100310080a0041d6210a56040d4249250300c5030448012070503d0000c0b10030340003001d20003442e5079501140c0c0c2801d5040d01c1806a014414565804080d1040c10b07610020000090814101000160584052054101040340034081400226030050145090b0b035000d0034200e881c3c80d05c00d401c00740c1c4d502c074640102031454008900303041050340100134681642e0b0f05400a01c000600032556104850591180315500c0c00840c42c008612a004030700c541100840c82d09206040351510140c1c1d949860307400f440640e0744c1c440d450411031958548180e213510200ac4495070b192011b2400002e5a440c410300800740709003030015000c07034600140741c8103410420b1000e00c1d20003c55035a00348030b00c2581103c070041e961007074414201501c601d000715180c500e04204000842d20390707030304 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 579246690 1250 579245440 579245461
    0x15060702100e0907050406080f07020d180914060306130804090207020d0c081e0619050c1905090f04020910030b040b0409151103191e02120f010b090306 67
    0x5100340414000c0004070300000f91034503050700d485000385850381135940c1e01e80100100318a9000f000040c42d03030009020b201032140d01043c010140b1030076103032005480c0010302c0071a103100c9007503009000c03141c604401e800b40908410303a540c1c8200011015214690790302d0800200e40103071804002c240e17107400c000601189580d9400341602c6070003d40b40359003070001540c4801c01c61140341c003d000c46030311170007140003580b000a17000561980004007400fa20f00f00705441d8004075492170101280c9075107440014002256041c1903c4040b030303504516035001c0f01d8010010f840340c0d2000801901841c0c1c80064218941454004c4402500c030190804080c81d0700c01d5030441c002e0000e01000d6030700980f1280e09c0a0141c1e200e00803105114019181403890103401d404201c2210381c0c0300344407110014148100240d17080102c101c51900241004040b40c18000f0010070003030030380c03003c0c0074078009071010404042c0c0c0700003102a070b482100c10220445030b903625108504690f0083c000002c0e0b00d0360000001030240100d = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 579247940 1250 579246690 579246709
    0xd151e0608190f0501052416050307080703050315040905030d0504110d03030b10021504080d02070c140316121b091d06060f0a0501050c16061715060702 67
    0x5503440c5403034080540400c0c09050340e680c03c1e00220220307101d20041c4040d280069084540802c80c19500c02450710840110240e40204a01d00d901c4070342e04028401030081c144215854503078898501c698a070058074010340f56800903145000c2e40484a05103003000c0c20188641a04035030810019030412141c03544140180c02c008100300c500c584503505c0c0ca00740e40c8030030328460030107031094402042c3c0ca03a01c0d60501030014500d003600030443d48039040c0394010301140c03280580c0203500420001c2e07460074600200300103131203075650003802050710440009402e410300120011b004000c5041d1458201041e0364070601f50361700c2c040c60015580c41e183c10b00014144c01e88141300da078110500001c40a41e241c105e0f60494001c20740720402c81d41c540d42240802c0d041801105ea01c14400c40340b20141c004000e001c2000e00c1424003815040c400009012003620b401013003081c0f4545450900c20b26a0398131307003000902c5c01900c034100ca61040c1401c004034007080d602c1d200d900030059029180b641448115020440b0044 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 579249190 1250 579247940 579247951
    0x106020a081803070b0d2304081608070f060e060601091a0c01060506030705130e16031113180e01180201030908120106090f052706150d151e0608 64
    0x2054410004031040054050003907905030380000907e1199850b00500302c102c25034030051030940464100b00c0010394003c1a1804038031550103105078050740746030480207442401000f61004202e07600d03140070000f4a070401d4841c0103038002640c0a03a2079084c01900d988000b40941d5000d020041204803440d01120b014141f004244000413844558400200d81154000d0710000c0c0010740000d40b0301d40901c20300c51030400403d14800208207614051904110a542680d00442010b03296030001008010780c000703454001c4e8489614542042d5101c0554100030480c0001100460400d80090a84003040c0b00b182c400c1c00a41c80700d000c205290354011001883c8444084514000510600b0a207401c81d40127280030b4901a00c2da0705c1c1884c10078500b284455079591169111340c0c2d64000c0020302c0c1c0d8030b00070382001c200b2180d02030141a40740e41c4001040c1015441c10380d07407001c2022608010301c2495400c082da8413400c11504540300340e281c2e0301d031009a40f00c14281c4030105042501c10000d0384d00c24030441d036000c1c = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 579250440 1250 579249190 579249193
    0x21e0a030602120609060a030804050904080c0f0d0210090b040206091503010b0c0c090103031d0a0812130602011515030209151207081b0d06030503030c070b0106020a081803 76
    0x80d100d607600001c07a0044010745940905210800206090200815400080840c3d00309142807859071900b02074807850250a01820803400410b040060f840e0541e42c044943c1015038800c5e2001c503502d184d5560104110301c00501c01c0700b150054101151080d420f806800030032880b1540d0fa15000c2c0406580711244190b000700c41200c1d14600d0070342c3d400280d8040d0101000d07040c2e444101c009918540f505051180b4482e04059004000180d00000342081ca04180a600101d690b10382000800c0c008140d44042141e0250f907005c0c0348103001d1900240081c2e00742002d00800070b61100c404900301d40142e401c001c2d803640f81c41c90511034004e40c00c0301c05081c0c20040c600035140000042c0031480100903215041070f801c10108900e4031844020400e258001643e1034268402e140000861a81c0d60800c1d80503c8140c1c4c1c0010071141900881c1c0054000e0b54002049980d641415030f000c2070150f005142c10b507070034103c0e02c0010030040c0c0b010a109180c1a0041c074080c2c142a8051160184444101c0c05598903 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 579251690 1250 579250440 579250459
    0x60914150f07120207050612010909020d0c15030e06010e0601120222090c080907090e070806040f0212030f0f25030305070e030a0c03030503130602040b25021e 70
    0xc040745a0010400503218005541c07400e044520060310f0305500d5008207118031707414050310100d0541c0d1307011181100e0102d003001c1030a01007800811200e10040342c01901e042603420000c140c0254000130000c4000c9039a0f410010104000180c0d501c8000a00802255004400100349a584a03c484805009501900600d0f120302c4244440881e907940801c0079400441407001c00450250380300b071280032481030400d502185800606a03844110710301034103850300d039039000d80310810034200526800b800791702c0201e68540c01d2608100d80041e0200754105d210f03994208004a5000e40481901e1100e010301c40c0107801d2401580d101c0a560b040103102c103204000149000071031070001d0044a8415010380c80c0040c650030501c0c4c004000d41595420503010340d109002c00303070001d04c0e8105501c044036090b01d84603403603481c0c007500b84110180c5443d01808a60001c98040707840000e5030000e0604c9000405081500101c09118201c04030031900041d48c012001c0b01c44040220351004140030745180100301ca40e2 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 579252940 1250 579251690 579251707
    0x51804140f07180e15010206040302071e080f032203031719231b0405040f110f0a08013816030309021e0a14240a080106091415 56
    0x10f05a120303030200e042241c00400b8420249001c0e400f041d1112401e20181c003540ca042d88010b952807a80780320f4000084010850b11220398004030400c4080d00320301050751a444203441d021552900800710412889181391020001c100340041c043e002c4948c96110880c010911106011401000900102d68000d00d00e03500180f1660074801c03801c8076501506035200030880c100c480340742a48010407004203c4000211520038400b0401910101e90b402c543c08204a041a10000d000c0c140b090a0004501d9001c1840e8104100c00c0d4080d1960f0015595251480ea0b070351140a0309000039901700c105000c20010003580712980d082d03a0b86580d0054642041d140c600c48110b120340310744d814441903000a6071482c80c00304520703150751011600701005d0718410900504c04001500d280c00c501c14910740101d83d445d40056500c0e0b1400300300184a883c0102c420491141c0140e03030056119400100000e400c84c070022071480d0140105006907903000c07055044416401c814005400e80c1e01075050808401400b2144 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 579254190 1250 579252940 579252977
    0x611030403060c02010c120510050918070b03040b0a050705030403050702040b090c0d050a0209061c11030717061012090f02130603020312030903030601030903050c0706051804140f07 80
    0x180703c2c0041e0300010318001d40d001e0041444003658001c00e8607a007000c003440720900d0041811000e445085560741020384a04000c54038641842e0f8600110340618800000e032810b619000e984550300a600300354040e0f441803010000c4800444110020820901c08107001c607225402a10741948080d00010f030102d9800001108003000f11a000d1906070005602c030b8504050380203180c1c000303662400c250700b0840e0000024625000e0500111401c009440e142c50581e003460700501100070080e50b200ea52030510305001000d8035401038003d04002001e80101e083c50a110069100b5210103030344407090001e030380c0103004c080c0c24000405d85e60ba01005190301c015030351710820541000c00302d6000158051070b501c1418180bc40075040140f6403001130080001c48500841121b03844403007440c000840301d03424941512540141c0510601910030384601142c025081402804040464841c50900c1c51112040109613507146406070150044040880c02003040c2e00c0f007171504102c0074103041c61070107060152036 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 579255440 1250 579254190 579254201
    0x260708060111031608160512040807050102010915090519080a0e0108040201080a1a060408030702040605090f0606070311010f0b03060c07030c060b0a1208031e0405060711100e06011e0f061103040306 87
    0x248c041940000f41004200f904100c0d00d03004210a00007801881d280781c5440d403202d000e0440d001c0e44076449000420401c2030600903681703030880c03c0400e88042680c41c10f106c1a942c01c50400d11000c1081969114100d6020700d4200e48a65816910b2000da5038840c5190005008800d0002c5448040400e05502ca0f40e00c40c030240001d400c440c8001d586449a03401040155076081e800746000707500c10307028400e1146840e020698420000d0380e10030360b10179003803030122001c100e104403406a0354604080f00316041400e4100500c204000c4048890603182d0343e080d00081c0c400c8407802008035120100c1030700000c0c5540c2020080b040d0007850210001e031342c0c003d00b82a2003045042103403ca5000000c214811b1004201020008a08443d0f04158941581c90303541e50513028142c2018003188c1c020783c001c014020448104005150082481003c020f0201c45544402c2030042c10102104802d5030302c00e00030341c01a484d0031030380740d228030940c2c0c1860b046094030716400d03040095115002c00c00011001c20307251b0051 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 579256690 1250 579255440 579255463
    0xc030905030a03021006060806031c02030d050a0b0906060c0a024507090b04091e1e2316090312050d0b010905102607080601110316081605 61
    0x340ca645061010118120f0f50660000800e008c100c0050080c00c5d10000380340e002c101041c104640c50441410720980c07950192400400c1c1990901c405c200003101142c0098140d900140c07217180c0300c0d07241c1c58200011800752034440340803940084106005882e103880400922680b00b0900c15058141d4612011117034240070300769494011040c110312051504203056507100340c4a18000e44142e003001844d00992060384034407a0380503113608111280241d04181e00301c0100f43e56804208651444c1c1e40c2140194502400608081c42d188402510840c0c0a424050617020039808070070564680c2043d181c5030347c1222000081007405c0b0408000105258031141100c0c13240e03100e840d124a402148107094540001c3c40a040001d02c6104201c1600e4180211140c0300c8142004030031842910000000d05d2110b80f050f4810442d10420320001c1c0342c00004640c080c0c0c0003070f81c0f609411000da0500710350300d1194500b2031a04010201d8003001080000002e402001111416080e003110107881e8285041423a012 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 579257940 1250 579256690 579256693
    0x110406080109051605010e151201082a0901030609030c0803040605101205120a030e0a120906081320040e061005240703090509090106061206080303070c030905030a0302 74
    0x7a8140706080000413026100440c0a080f80c0e0704180001b06600d102c0c0c0c51003801403280000c815652900035068919050740d141307040c1c82c60340e96124040d64032000301c1b507943c1d0f041c07071611703076100c14503414420040c8480f030054072007440741e40b960390760000030040702e4002e40400100780d0260b400121900001c600447c0581000708160800410900414016134000d60481d103008010000154012581c20390303420004800300c4d140c000142081e4081c2c040100000020300425807520b007000142c02800500d9801c0d50341d0241600c1d01c540302500c02d0a002c1c1c445400e5046601c84540c00551a0780100e00c10004504c00c2e0304580e0452000f0a065a8645810000380c1c0c004000700500001c18949143c0108402c80303840b0031300300c3c07207080da0b6003600040141a0009440043d10500f41801800d040d0b001b448003525000b400e141c0402c102e03000700030500420b0b0006200d03000c02c1e501502c141c06600107840940c0b0240d46036403a111015540041039600403001c0c44428400040d840e601880182c250501980 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 579259190 1250 579257940 579257951
    0x3030e0406090207050d2d0c0605090a030507060902042304020414070926060916081b1023071104060303090506031e16030b010f05161104060801 64
    0x2003005444141d0000c8803014810711041c80401c500085011041115003031180c0c040d00002c6501c0489003e0760460301044103000c041c49005648180e10703050040c010602006a0f4540410040c1c4402c0302c1400980003c00030300004006c640294404450746100400c001081d81e441c0540b101084203800b204040f91401000f0401541401d010748102a01402141c0d291854000b03005001c54030340c2d015418440c4d05904500d21600e884460008407038040601f100c140d4941181c40a80d5011001c01d174084e40001d840c000600030b100002d45508402801140d4080201c1e0310040c400119040e05a8a0400100120004801e00b40d030400c200c4268203190220f603522400e04004814468a44190740114680f01d0100003080d408211042502d0040384d48656a07102e1a00b000046c4590391003248040c17044106100da080040c5200040342455a2401e106a001c038100540308000900e040c0804540c0400c444518038014650f564019481504c4182d840c080c140085022034045410400c02c0c0d03903452 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 579260440 1250 579259190 579259217
    0xc1606030c080f0c0c010e03030c0309070611030f030603010207020d060209041104080607050c0a05010f1a042307050705010216020901211506090e16141c020105090a0303 75
    0x60146081054990401040d1824041540f1142210040c845003980e41d01040410303000e20290444900d02c4841001c4036201d08003071000c203200780c0c0181c88400140c07081000000740540684080c002222940f00503500b012208042c40050384d10050903103030b00d550b081144a0040c0d031802c0c81c51011900075040140ca450301c100a210071620303000840148440300380400c00c464900040c0c0294407001c05c1c0740c81d91310707281d80c450003900c0c005100c1d10040a950810705400b800e40c1f5036522201520807501140c801d10f1102905120071151114142880206046040103041d01d02060742d80c0c01c02d00b6842d00c54600400c0d521303500c1c01ca8000115848800100d80c038003401350319120800e9405040180703001e0a0b030307448084103003c02c02012040140312a049031017001041240340d100720010102e0382002d00102c03854000c02901c0d0740c1e031800010490400d110010504d01040807641c24507500240c40c40a00580031400e2918044a015007241004010030840001b522140d2440004500c640c41c1c0210b0407400 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 579261690 1250 579260440 579260447
    0x60108100816061d0607060b0301021e070605070e01050306120f03040e0609010915060e2716080915040501091208190524040b091302040b0a050102120307050c1606 72
    0x400f44510b43c1c1c020000e18803040345c0d0b460003104c0605030300840000d540c0440fa404240640034000903008400d0300fa041c012101000350000301034080c4142c1d0308200c2a80c0340700d03007940e160807640c00260000b1014400108a4101808000c012000c19012100a2041c0060301451603206400090840040505100320340c1810f013134407800f400e101d0720b00707018500d40b540ba4104d0749801792040c3c1c405c10454081411068a81c18124a0b406c60034100a00c400b01440b030040703103100015a4420b0070624102c00881d07007948617400440c040d601040c080c3c03485003820360411241000140098405541c0c500300400001c44260324260f6a4205483d404a01d1800007102d40b0015000c800d5483c007e1b040c0010007049400d030040c2ea1042d04000003031343e003400203d000810000e04080026a800003802414060301c1e030420b10017500076510032036051101000c000f050111181181c80380d40d0140e80010301700881038410102866221440c0d1074410709104401c0c04c0c2c1c6190101c00002c0c0b0300007090203c0c0511203a03a0 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 579262940 1250 579261690 579261707
    0x80f0901020c061905132313050408040501050d0b0301050a09020109080d02030a0507050c090a290306180a0605040809010908150406020a02070f030b18120306010810081606 76
    0x504a404505000182c4e20910003450844580010070000103641c3c2c00b4144003d18210103042d290202c040d41c1c4038460030101d20110014510340c4580c0714004801e0005d0741c140240c0d4400c3c1c0d030010115040034585001550141c1000c0c0d1903644039a224010320030300713881c24800d0300e00c144121300000c40c0015050001402d0a101e54005020b25000308901d01b110540000443c1c842402628002c0e58980131800c01d5401c282c08425500e40c001d2000007403021027681034002d10a01c8150390400701e1000c1603111003440203c818070781e054040e0050341c00a5151010810651030b980d07041010703a41d201246135103103802c449040714111807000010403072401c9960b111003040050010344c03000340450b1a42c07040c119480c000041005044d03640000b0000c4041d0720074070400380200710804080140c0780c0c50b468429580101111210f401d58465805410312200016101e80c2d0721441c0c3c400d0510b9501d5070710046841240080261152501c09800010440420000001d000c1d058200b05403c0600b4008010003290 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 579264190 1250 579262940 579262963
    0x5010f05090907050d1a0103060503010b01020c3304180501081b0301060b0c0304150201090b01030602070203071701021810020c040906240315050408030c070f080f090102 75
    0x2922425080019400c081194000c1004844140241d41e448004440314410301d807046500e14104207040301400b005c00000000d20109807428404140c0711014107088401c9810018016440380d01c0707440e49030818a40081014522021260249500c40f4800300c50703000d202e60074030f11100c00140030040c91404141c02110032041c648180a1135152a5a4a0751200f415400c4100d12694101c003501e10b6078254081ea000742031074603559460b01c100d040415140c0e009445031100b0241c40d05011601103106100700c0f48811fa01a08880c1c0c0307070342161200c40c000c0d0061360003240c142c0b00d801800f060640c07040d940b48650000c884000b60383c0c0d14010000119451401e1019401210100c0d8031500740d540109400f002e40000b44d50004075041642420b4010b0b01c00c614060341c4038941c200003c80301c46201c001d04d1042d81d006039a644084481200020101d5a040328007604244042c004512105141001080c0d039034001e8840002140040c1c64a80070790b0f01c80c0d1240c10b1041400602401203507010300c241c80c600d2 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 579265440 1250 579264190 579264197
    0xe03040e041e0c090218190317030408030708090c060d020a110f1023010605030711061012060905010609060f0504021804020307211d0f0a080a020109020409050114010501 75
    0x288041e43e5002050841809800c8400d074010071680d4510384c4c445401402418000c01105010681c04000c9401e4001c034041918656001d04401d8103000c20081140d000b1507024401c1442d554450710201c840c40c2000c0c201110f02c1c0214100240c241d81e42c00007418103d80f000b9001a90348403c254080c0c03014900000420503a0000c5583c3c0800d400003152605a01d00c504901003100c0c031461001600c3c00c44110099000c4174008000401d030960b0000145200b03001544480c07140c003854151159444908517010001c124042d14188000c4018518035030101e0b00c59100070030888803681e00e4900391552508100030303150303903030404100780c00344842c90318020b01e41524214a8401c4207010380604061940040340129000030204219500c41d9107182d50080c03020720107243c0404281c80050150185600411070190900c4c0d160a40107004200b00c00130386461070040080072000c0d03807499090780058901c84255542d44400c0c5016854500440b500544207200019a02c0d04511025522504c10b0f001941007 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 579266690 1250 579265440 579265493
    0x14060f0d0c0b0d020403061b0f051e1b030c1b010e090615070506041104060609050d1b080102040605041a16060f09020409050d021b0a0e09010e03040e04 67
    0x300702100016400d075a003001d0302982d61003611000030040e10035a4402003480c0d180640300280e1030101c1c08680a001e11558a00d1f00340750383e0003c115181d00ac0c40d0020950200c00000903c901900c240c014071810825250172003d080404114604540110031420000e070400b1420350311551018102c5410281c090a0050b0791074074142c003185c0540700060401d4010400c0e5894111203005070801d03140125401402c0303907524035041c501f0050540e007417902c90340107a0400f6008500c0ca40201401001d56502a1402c03030300126030789a880c400d102c201d14401c0d034041a4080072541c07440a0004001500c001c1d191b05d5625880d1801400840004200da002016002e0000042881080f00e180030007039001180418400c540ac202c880051134900c1c0000d6109107062184410001d000c10100403411083e029913003000407620342098a4a401d8840a0740201613100600c45154002400c641145000b03000194540070440700c58030b076501a4001c034410b0010001000304120803801b180030291031a01007a0311 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 579267940 1250 579266690 579266693
    0xb100e070203040611070504021903050a090f020d02010c0605090f0f0127031814040c0906020c0105210f190204230609090a02030106110102070510110d14060f0d 71
    0x490f40100d02662041214000d094079100c03004103c524094a401441159510100c0340c0c1314001e170504d42c40c1803021a00b880002240c02110788a0700130181d81000304400c4803021f6074200720280341200012814040c4940880340802c64620034184140070070b000a00e0100b8580c55441d1505912610010a41e81003515040e22012101075030042c61410074800b000d20303109442c040c1e42949400a0b02400c1948025000442200700c075040c511002055070108071401076084102c4848141e8020940542d100e50014440e0b948100300802513101e803d4071821410140c0c104100401d1800e441e0034150a5243c014800150307500c840c40e070115500c5d0801107142038508000305880e80f032002448441d001400e001c44216403141401c8a00103a402031000d2507500c1c042014000a420038050703000010080010f00402c15414821101126000310017400004402c880c282c1c0078100c5603569840b401028400c540c24002c1d28040c0b148103a441030001c0d0445c0c5018014003034091a10a925446107154a80640 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 579269190 1250 579267940 579267943
    0x1a0a0302060901020304090c031a18060111070f08061807032a090504051507050403020612060d080a03090318180c050c15101d0c07020d0f0b100e0702 66
    0x1100da05a034056210308002005070b003113000c2e5030301203142d51381081189003007130754150f1001003000c030760384401d0964050150500c100d0b032680c40203140d04440b0b040045001c9600070164404202200d4003220030494407001410740c00c000c1d56000c00a44c6e800401880020124001c14404c02c99008005100785880c5441e54100c403000d5808060b10701c1c00d00d004a1807010402c40d002e00280039050814402801c003858020356920360540032545410a903804144405d206200300e504880c1c0061040b4140741c0e001d054071582c810090314440d4403010001c640b600059440b001742410384040d49001505041d02c0c200a89500080c8181c100da001e003804d001e0011208060f00c550342d80c04085000905411451815155841945500000c9200d14440c0c03001005060303410912400c81c1c0032a880e007250340d0b140174204240608000c2421484442c002400c8082c07a48050120203000902c9801407560b141c0759030010258000d0180c41c4081654100050200e001c4a00d60041020030b222100e645480e00009 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 579270440 1250 579269190 579269209
    0x9060306050a020307090e0408070f050d08101a0c0a0203060117010c0504120b041419140307230c090c0a020c010e0a05040b1f23070b06060d0212011502011a 69
    0x81f11040039410100d014481c10a0071303a04190340c804000399080040d400c0c4103603541d8001c41000002502d0b400044c198105002d42042251010744012003505071f6a1a1f004c807070303084a60800d00303030320580b0301800159408011460080c01000030480d80c0e40c50601c0c0e000d0954040d9007000c01403140c20002081881c10081c2c034444200d8000501100c2500c0e0362030100902c0e6510704615800f8070540880000004820007801280c42c8617840c40e0384000d54252009859000b00100a02820f80d070807010b0b078032900409104021100c0e20029038200420f040d00151644e0020303240006000c8011520706040c44d010040d44521200900702610b039031601d00c0008031071076030900800740195140d50f5013081907240c0c81c4841c0c1e540030042e0044003012921180c0248038901203003802a0725001c02d01c7d41610800030384c04541080e60020fa00c1c03000c40d550f00c1c080c0016640700c10030b5480c2280e400c10802d21004810000e42d806404214180d5000f400418002404d44080301041151902d503450800074550300d21220 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 579271690 1250 579270440 579270449
    0xe120c100c0c11040f090803071106040b0c03180304090b0901060201090f170405061603030b182a070308070201150e0402041d06040506221e080405060409060306050a02030709 77
    0xc281007001d4001080c042c01700030005218031401c007061031042041e003201035031091071581d6032104014070703489025644d00000d42e40500881420004200c5551516000710362008410b0703490044c0940320403590b46142d12541c000c181031640c644520b03030703603160407103215004240324802840005c500351500c0201440e03c0f00001d240d0a804c2042c42c250f0095601928010031008100944900d2904000c2c0c0c8100d81d000d90031800a45880d0710348015190010119204030750b20841200c640e680d41c116481020050406c110301d05000545100a13094030000501d5024480d5a607074080f0300b40f209020b400d480f501040307030b84c801002210a010950701100b030135134402c0d012100811005035402140281648004180c011400340d981040f0a0000014182e406042e41c0700c5820075800d22040c1a61401c40c0080f002040c04281c08424081254544e8501c10aa4051b2005919150303030f0303100061142d481540f103045100d860340800c000b401064401c059026040100a5285180c080001031184185006 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 579272940 1250 579271690 579271703
    0x15060f010e03012007060b1f080603010b060a11010c050f09190f24080402060a0e13021c050c070308040201080a090b071d01110c0111010e120c100c0c 66
    0x11581d4559000d40044c140b401516121108440074001d600940d03074041a030682d82ca03410010380c0409400c00403003c41d00304000f02c00c2840003411010781203880c0c1001403c620b500d9900c513101c0c112543d076400010440c0011680315460b8000c0b00e1610142500c083c85a1503050040a00464117030f107664030100c0d20101012901c5d502020000220465044007c2c2c0001c00340c0800081c0100d02c41103498072420344c03c81038031151200184600011201107030100e80080d0088401e2080e50280340c090310819002c00c400074003481003c1c208540c014202d0f000400512003d06258048513054a0755218450b0840c00c0303061518601035060f18042e00300d40d00a0002410003650500052284c1d45a9112110351944101c50304424200840000c0030712141100e4900700b5206818040f1203503003c1d0700c8280a52400d18082c01c03001c00268015900c01100440885455403214010400c0c5030701400107104011000008640711a84201003524002c844040341c0c8165140038910704020b82c1020030310040075031180 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 579274190 1250 579272940 579272957
    0x10801050d0804090e2b120b031504030e100503010b0f0c0708100605040c030b10080601030b0307030c14180c0f0c0303190b0a230103061d0915060f01 66
    0x18211032144110340c85022024503041c440003603031002058050583d25100412801036140101450030f50b000c018500d0702040c3c2c2c107141103850b0002902305e01500ca20003006d07550410803d80010a503280f0032a0201c0004901c0d155900e200d181c00c001500f40b4071450701d016800c540c18000411158440c25005500c501c0011403084100e003020080321000d000c9c0b0406940d400b040c206407130000f500041c05130398892400d0420342d40d12a84039128480d03400380010070500200004080550756540d016007000d04050b1146c185081584040095600070b510030302c1d000450f6840d101e043d90020018080c0d2034417840f09203070b250300c1c001c5040381c0b0b1135000030b006640c140d6507403000c11a4080038031440b040c21000f40030200409c0120612010707259a0003204140501140c01c100c010000c401c0100d0103581207191344903240654000c24904030110058060400140300d5440d8400e992165111485d480030313180401c2d040004031403040c40315502045410052400720305100001170040d40008020604001106 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 579275440 1250 579274190 579274193
    0xe0a0f0b030c0c120d0e0d0c12080606130b090a14280302040509010209040605030706020316020a0b0f0d0b06070201081612050c0a03110405060307110312010e0a1a010801050d 77
    0x784411448410002e803142c0c0e1714030245030f880001e0200244440c002d40115400042c03054062000c061200f68004080d07035034401240c0058401c0343c009020590001d10600440302c00c480100c40080c042c1a400b0b007a00d4840380301c40204a8010b10030780007882c80320601d141079040340e02c6182e000002c00c040707400204030340090a400203980d21321170b9001035840340c10102802004031040d8000c045140d02600e00703201451300d80082c5943c4080710300c181e50046e80104012910070280d00b0ba0b082140b0b1005120403403032641c800300c01016030812504030542250000c0d0301c1c204031030603210320441404d0580b095400c01085400207041240700428408800c2c0d1401c0b480050b4038421440f01d03155940c42c81c0c08100300e00b00b0101080e8a608001799410101e440c6c208008010700c070342c50503903080310340c02004103246659030f8600315058104500ca00c00e862109000c0d003050142c0b05441d140c00f17002c0201c0c1142a900d0680320f002c080d5502180080d03103020490f01010358507640002e2a605546040e541e9981d0344400307 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 579276690 1250 579275440 579275443
    0xe010c170a0e060f040b0601020c0a151e090e0a050118050402010201020903010603030801080f120301051009030507030f2001020601062f0706020105010f060801090f0e0307030e0a0f0b030c0c 84
    0x6030390ba01c0b03018000c4104125490001e900014001c42c000e00d90200156034100041e03903104410720416a0080125104100000c030b03101045400e00c81502d052010142d1110040c4c1c0c03240c42d0400c41304080395070380b42c051220341e80038030b082a413041b007008003030007103500d000c020b400200700c0c11601c403c4154440c0e0011b01036900035011940664009002005610b07a82d04005082000a00407240c042c014070644240323803503000a0040420b200c0c58001850760b442c24042000d44c8046030a08003d01c2500d08000002c20024402e6400640c060042d80b00002898070b4019182e00d41142c1801000340702c00002103071644c3c00680075042d41c01e94101040c912107680050300e260142c491381005400d0618151a414030790104201040319015002485280d8030ba08074040b070344800e40075580000c1d070418010810003d139a04681542c100320000090f0b82d202c000780c403e0540d80101310950209402e2410f40442e414811140d40042c9041c07100101540d003001c40190302ca00c40a8a40344a40001207003000303401c0300 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 579277940 1250 579276690 579276701
    0xf070c0f03170f070909090209060f0a0b04081c05070f11010e0d03020307110d0515040609080c0102090f0a0503030a0804230a05070509060108060103020315060406030f0e010c170a 79
    0x3824641d01d03d15080c61091940310301103890400040c80c140001070b00044078003070199500c2e401014942c0a03070b145c1060001d17040441c1d000550000c001000001c05511b2000244040d14070754001c0c003c3d11006007104c0040e003074146241000c11808012800c08039070749444041256034000a1000960500300c0101c5e00502c40340d004560202d000082031042540000007000f80c6440f40c44094040c0600f0401c000d4030040500c00a8240d400c0282035030307240016518075561082c850740001034490f4082c1c40365070725030700a8680048580e50008503003030180740925003500c412404031642c1c0c03155400d2001094690060204c100300340007e0002103410001414802d0628480c45412a1005044103001d0f60360340030040340586481c00340400100b16030620001c524030411042c0c58104080c1c4403100118002c0d8030080c0580340c00488000005041ea84190080004007041d40c0d000c144401c0c84601882141ca8160442e80b01e68500110040d0480d080201c1281004a40c01403031040c0c4d0701e61111030060038 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 579279190 1250 579277940 579277967
    0x90b030a050706092d060c05030c01060e0f160f03020d0b18010e1602060f0402010e1002060702010e07081209240d0b01020d20071215050f070c0f03 65
    0x10b80b80c0d01241140d0310200320f208403401c1104000340f01400140805040164142558403004400000e00c109400381d00018407040c42982120300c1c4c101012803403070131100e540c0c0180826911702c0d802d101801401000f5140c00070031030186a903810b0782c01c12000d01078030500c581c550213254010550984422050f4031480300b040b40903100c03002a41c112812001e95140c07d0107a81004150700740800d074040c458044000b04260640c0090155071a156034080356508010001c80c1044588104820241c41ea031401c0c1050304165002440903040050f0007030300b5903540502241c1e4641c0821410816046c00007140042400c1000c41c0315a100390381c0010075a06800040c0024070114019001380805c18600002c00501c80704d680c08125140f107810049803180d0485c10070000103181008010308501c040504d85002c40e0203002220f814a5076040055081440b21030180c602c440030b000d01001000140c001c0c140d01440400c150105868424401fa080c620403810180c03210f200c4100b05010540580b0b040030012 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 579280440 1250 579279190 579279193
    0x20405091615020d050c0c0d230105040b061009050d020312040b0d0b0604260f0d0201050603010f06030c060810170a120f090302040506030102040b071a0c070c090b030a05 75
    0x381d0300d881c2d40c500c41821150790040140300da1220644d255102c0c105440d208013841018209040e5020b04000c0c161842450540303c88500440c00c00b86108000c0079401c0016010002040e2880c190418888003a40102040c0c040c9141c032401c1885981d1210002c01528000c80d0802902d84507400800d00d41210f501010034240c40005001c10b0740080b11000c2c0043c40f14000c8182301d40d018807003c2c41800d00a51103805101400c0ca00001c03180003012034440440b00e4080215030070707002c1c454011072528140c04c58000250b5500c0092040909003030207010404d099580381801000e1441d0703105d4404007503e110303d00c00c00c188000410000c44415100360020210408103014120701c3c903c0c6291911242d090032034840e844400c03140c550602619540b842c1c99026111751050b079103180c0a01024082c028042c41c0d15550030400071803c11209009407402c28042d514052046040c40c810b46881038020300b038004c40d5603003449104d000030340070743e000810b603507a003c004145c006c02100401d26214040307034000c066 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 579281690 1250 579280440 579280483
    0x2091003110702031e0f07031a061201050a0b010314040201092c07050a020f0c0907030903020102040302040212010503160806180a0222111303080901350105060c070302040509 77
    0x40c5d8490201164810983c015215000f02c4807034a10340e1a5a2884020001c002c0e40c1c00c0c1058804044680d0f95000701c01904880750340f500703c0c03402400c5072001c4802d080c0c1d0b030380d455000c0049960725110342403600182100454050400360006810401a8440d0b805178080c00c20198801410380c6800f00b058070600d107898a1241005c020240040d0860782613080180b0508120100c3c404000078442035200c406088807840391503035041117028018059080d015903408210020050f141c501c0181402100481c42d9006541803104040c101411103014039840c5407104418428118007040c615082100c0400c020400c16448850380c0c02d001c80705d80060f500010007101d0131303508075002d0b0340704007541840c0000300005002d401220280f401111401041c80c3c0d4401e8080c400036007507000800c130721801410100c001c0b00a103c200d4100c48024021362108a811a96000d44e04c002c507440a13000d01411940d0324280501c5503450f0b031303850480d8070019215903110b00c041480c1c5182070000841076590100c40c09074 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 579282940 1250 579281690 579281713
    0x90607080f030415020a091502030c030c0601150c050607050304060f1a030706090b120a1e0c030c0903080921150609150105040b0f09040c021b040209100311070203 72
    0x41c2500202d4007940c910b040c00850620400452086075050016522045076080c00e2192100d07040c0183c01c85c4400b9480100305101400004101505445e00c9132001400c1960603e0752000c8864200800714080c092880703501d200150740030034150341c0a045483c120351a55114105400a040c0c0500810b5101e49070642d40c02a000058140420010047c3d0440c1c130f0056070343e0001c0720f00b4202880343c020398520501c0320003201511210b010750820240c610201d104c00480190689032001c10201200b4255100e6a000f6001e40502513511008041c0c01e001c4034031071968035905068070801d0352251143d4840000e400100c0d606000022409664008403510382a0154801988400c02d40c0d4031440307121410000781785801103c1c02151540c0040c0d50341c0c0c0c1441d18200e02c1c0645a00000c582024a46050003030040c0b50700c0d584150b80d40308035270b540109440322006198403518070402d0b981e140603900420040086803190502c25020100c1480c00003211032075a015000140540c92000358140034043c0401d0 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 579284190 1250 579282940 579282967
    0x120601020c100c060506220b060705070b0703020d03050c220e0c090a0b160b1b210f060f0609010c021305010812070308070305040f0c06050309010c0c0f0809060708 72
    0x40e0a521814017040191644020010591035400c4503019400344400e44100f659001d80101c0324501020740b541d402c15206644403030601c0e22607000018002c802080100c14580d04000180031050107050801c0103061140100c980d43c41a82d07071a072407181c01080c21514040344000f0400c020010414581d91900b0305072071f030800b10760044a0880c400d40607003001140d010a41d0040b82c942021141035148031364a81d5413142640980100b07065118080c0c1c00c00344101d485882c000f40b020707000c9409456881500d070001c0402c40e8401518081905201c1001c124440e00e84a0750300c0000502140c80d240c0312601e00d401281d2400501e200250407043c04480c040e6040c040e0b42085050743d010200b65215400014980c4410f1700648002030005100303d1b001c6512103000750f111035001802080c400604844649440f500d020b500e500010004000000f00400ca07002841965000011403500300580c0c005510382d419102943c07540030344000741c0010f01c641503a0f103640440fa81140d00c06d55003500c800c0c0d0b0a0240 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 579285440 1250 579284190 579284207
    0x2130606030501050f010201020c0316081207020a02040f050402030a060f1d07141e0d0201050d0513110a08150702030912060906010b031306050c0d0e0718060803120601020c10 77
    0x4d4001e03070160900d204c0b00d60041c020307181c2c1c511019000f142031084401040c41c840c212084203807a80d03201080481c0c40b12150030b0f40c2d5440b603520390f00107040707090703ca01c1407004480350f4100e00720402e4a800d007030100603500403e0a0195542103100031441c2e00502c0f01c82c900812501c5075003407001625007256610300301e02003044001c607402c6011781c1400f07018401c14881910400444c8000c540e0b4a003901c0c96692501c0c20030310703000c03c1c0103160113030615901120803400caa900b0b95031510000e040101ca0070400030400e000d454043c0c001e4440704056880c00d0285aa511801da1481d4055a050300025a13034520800a954030b4032002014860701031100410592103039416035080d621401200700100d20b900246044a000f2072510102e045039075865280d00000b03001c003900c900c150490400c001c4401750035070f01540985180f441d0140c00100c0c58400741c2c42c80c1980407281d1411650a142041140041c0403003038030184003924100901d150351301c00040b401e1240008043e5031141c407880c428071149600400f003 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 579286690 1250 579285440 579285449
    0x30910090e07170406021e0a0816020316060f140c040806011e0b39060609060f190911041827020a0302030a03030c1d030a020d02130606030501 63
    0x30310640b90004125540500f0021208510741c040010800189841d801000a4043e200c40301d142e150615401c44059840416010006620502030006400c03d44080c0f10802905000551900c405e0160007100c401d15500080d003500c2e580c0c1c1c40c00801e80400d400104820154440b00e8626107408020a80c05402c01d000302d0300184150800400c219103420424042441c03289c22134181940341507561142a80044105121024005484002034802030f400400c0448682d98080820f0041402103180a01c002c0c4180c1c41485508140002a240c52482d04080d807002d0307030310384c20b10074952520b07104035109540010440c52608004c0c004ea03000420141c070039107091104080e1141d80d0a6071035419115210754000429049203894401d046800030802400783c8050710b0b11907043d0b07490f000a41002020501907011949411420754270580c070892000603400c500c3c402d0031489901c580800c2d564880500024007500640d10b400c0d0a55031150000d0071040c4050790180328454403440c0c010050f03c8203118 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 579287940 1250 579286690 579286709
    0x80d0f020706090e0c07030e120c0102120702090f090304080303040b0a0c26070306050a030506070e0d0506010902160f11190315050402010e120a0309091404110303091009 75
    0x200403602c688601c419404468405501100d07a440d68120b141e41a4401e4404800380b050050b0401101d803548101281c65031040c0e00640724110040c0001381c101008400c0a14514004100c24401039507007038962a008420312014860319650195085e107036100e547c000750071503c00481008200540b080e41c00b481120070010a01030601c807030009440d0074101701500b034400c1e01c0200c0c0214103403200c180f2043c0e1080b52450301262640c0d179600400c48103a903942055404d9041001006039441e044060409403240c00c0d50f110580b001d0940b0303495101d07101170290780d5444c0e4000408020901e44442c65032516030700030b450030b00380003c00d00d2f010190302c00c6150b24074012108040034070b03030154039800104210ba8002140c0c0c098080412503081c0103000080c4201d0511041d400c100c0e81c00c1e00c440844404000e01c8a008080440c2a406c0261440c1040d91190701d001c1c1c00c054040001000d07140340c031034005a1002c041039800c01000c000908600030310344803c0c0c00c2040d004540508a5105e240482120011103 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 579289190 1250 579287940 579287953
    0x9020f0f07140703151116122105090d02060c0d0f0b1809070828080c012c0a030f12060305191505010f150c15020a021506090a02070507080d0f02 64
    0x1c019046c280100c10542c010414503402d070b07902080c404c00c1040032007030152800030f003940341c500080806000c80444009841e40d448080000400c6c041200754894003541c001040c0c180751034102c03941c55205c0d1030042920300e03072a10402c0c4e01540d1150004088000d004240c00c0805901020800700c460048540c3d0700b40d071141090000e80c4a00120303611241b43d01c1079960181d440214810f4101d030051103101114030210800c80403d01c1e500030b10400392406a0381c04a00080c2c90203c0030081d0f4070003124284070068214100510001c0e4111400018003141800c06081c0708800d03c075044010b007065800984940949185d01c00c1580341c0f003200706e040394490f542d00d0300c101140030050700459009008071a903196404030140014210086c0f0035800d881c03580f510404143c0301c0c2d9a110010380c0132210fa43c00c0150040f035422202ca8052140d281c044103481c107035081c03c0c1307003900000f41c1807100a001e52280b294001001424440c050208201500540302212107100c40d0b120020304040f10301030080018041c81c0b = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 579290440 1250 579289190 579289211
    0x6030e0105070305010605030a090c0302030a05030a020f030f0307030f021c0c090902041412030c0304031a07030504030206010605030a0212040503071e0507270c080f0109020f0f0714070315 83
    0x20304c540c074140c03219591103900790342c0d421103038100400140c5d0f01512101c100d00000401a5010446241110302c92000341d902c401c41c001000c1d00e000710801092060307800501c415210802100b0503240d200c480e515010503400740d04001840240b01342802c6603929006200165600112900014802c1881d59550654a9500d40d02d40049001d0350081004204c01c0b580040f0581c5000c07403a02c01c684001c882928a040d0342d0b511410b28560083e803040354401418503002d0f10301c003510213600e503210040d07007010301c11490a0354009441d004140140014410044003060306400303030390305885400c1301c40c10400e00c403401d0a08211307580f60441d800407106c0301c4003150301c0d54041400c24080ca000d03c2e442001000d40505200b50b9410000158186142d115840c00021204550340d00400d410303000f0725101c119103030510b0007a511003124142c0004606500410802000d00d01c010100c0d10140091460f00303803a4082403408110541800000130300b144210100442070200217a010a903c1d12101c00805c10301589 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 579291690 1250 579290440 579290447
    0x906071211040e0c1318050f1e070509060a0306090c0c05060114060f07060209040f02090130060f1410080a1a03010204061d09131b0f06030e010507 65
    0x8001d921403048040c0810015038411120035038002c5a61500300b801c052000d2490041d8602c0d5078002e0303112140b400d00f2410318460720f11030140c0050a400303c0004500c0c00c10b0300205054545001001046070041c00609200e100b00141c0e0005040144540e0350f40b03104280c0100500020300400e801149450120903055018101e45a54280d000000d810242e10749042800000c0100c0c2020b5048101001030b101002d03144030092100c01c0c414000140c481c200e8106000848001020102c42144100701140032307070b0f80000b80c0c0340b00f5122101d80d60140c1c110748402c54189030302d000c002d12030f4a81001004103003d40600040360981d111501d803000d5100541c410000e022044185841c01700e00074101050041880e900039540308004a09194206d00d4a08042422a4030540c85080024940b100c0006c6c060101e05540d50300341021900c0d551541410fa5504500d41d408200041000030304420040400b01c0041c5084010903094a5841040d03a480c04058090600020781300115481c1000203802c4502 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 579292940 1250 579291690 579291701
    0x2010513050a0b19060308300c0a0c060906050103052a0909010212070207090e0102091807021501031a091917040803042d08060a050a06050909060712 66
    0x400600a000002180d02e4440301e900c00074144280103403a203941e03a02a4084c6000c0c1c0740040d881a4640d96541c0c481d01042c1c409038800d407031118003030f80705184a140e512511900b043e4002c0c40380400941c0c1c07001031110a403104c10007800300401041c108921002030205c690301542c1224096000d494500c5401800d01d8035003c3c043ca04400802071070640c1503200d04102105070350122500c400145822005414549200301c126903110040e0320281c818403440450313009021081701000300075030601d4000c1c000900c00b00c1407800040425080540050300161003000003c14286c0c6107082034640c3c3d40c403400c1400f4056002d02255101c0390f850001318996100028481c000000309000c0080703954400d0303032407441c1c440280c18806500c0006000114040c481840108000d018440009101c910450740401c4c0007020031940021840d026507007001042400b02d0f50603400005c41d00005035590b501400c0b00c0013040388e07402854103c910003080003480c210001e401400741c070258440214181030014682c0c291076 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 579294190 1250 579292940 579292943
    0x12030702010219031e09030f05010516050a050f0f1606020301060e1e1302043201020a05150901110408060f0612030a050c19030c1208010308031501090905090c0102010513 75
    0x1070000407900a6010a40c2591815080ea1b1800303c40341c40c4e594540c178038260b90380700c020f0720303e40d540c0c00612480001030320050030450b009003080780c14142c4408015200b4040d1721040901084c00080000001c84000100c55054a03020f16000b610f880f9410714800175002402000040740200e01010a549003041c1c0920b043c160400e000340f01a80d2007018410300040340168010269000c0c00b0100b90380000c070030310310064600107080e12004120780702004050307034a64408038150f4010f800d400001c542d02240c00c8101918154000c00720b44c842905440c0142000749080c40459070110340401d055501007455400740e1407150312081c443d11900208000516815103880d0903501c20844075408a0161002e00109001d03601912071800d041c0c07540180c06813440000701c001504c0c107541d440c10403030000c07000801c01d98640341c4652150306541e15208a40710242282e9408104251039807200da200744032640151114200a2107581000300c51643e4450015460074050b500b0000090924149800500c0005 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 579295440 1250 579294190 579294197
    0x72d120614010b19031b0e0a050901081203150a06031409070810090c1d010501091d19020c0109060614010c1205070212060f04061409071406091203070201021903 71
    0x4103681d9403140c02e0190000382c1002e16844080da01c50120310000455403980d40c03600d40110b0742c00e20344101f023482160f0fa000301d48580b113482c00501021000086103011200c036004155a20307142d095002c04480b5001d01403e40c0000c1c3c8c4040402e03500e03499045002e5030203802014030b4440c1c441d041d1307154403841d0500035115168841d011500c206911504001d100a000781000e10710291500b085c08074198812040346213084e0710100411040d42d10106000040000b1082141c015046200d005298400640004a41485d0181c02880703d1002e604403054400c0c200c008004a00044c0b4054018000b41d04c19541d4000700061501c05550040c6041d02241d5807002100c00c81d21554002034400350856070781a0303001101360200040202c1e04020382070081d9041b800d081d0103845c05150440036200c007289002c04070400031083c81490080001c19005650030500c4401d0f850780d1403800f2032100e0047d50496507005041203009a005030000c001405498000e9095a2121114640200b08108200d0009000 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 579296690 1250 579295440 579295447
    0x2040918032c0d0503030108120a14090406180507030b0102030702010e090c04030f051b300f0115030c09020301180e1504150c0809072d120614010b 65
    0x380259507088403000c1582d181410508030504080f81d00440e480f0b404459a9000100502c04104204144010f40518200a07854440d51040c003e05480e80301002d034140c14008518065a81d4468201902800c0030580c1c91400540480004024281c26a00440400c1c41c0811000481d40302104490940d90180c60350040d0355658400c4c41752180004104a2070034509100c01300c00205542d180600c1c09000c3e900406580410701c0f00182601803c1504ca403240b04074040035090008400c883c01241d800c046110f8006100c4d646006041001443c40d04409502e052340e03020300c0480b4011a402a030340140042210f8685441c00d4901301d100a02074183da500e0424039400c1c0f0942e654004840b1941802c042c2c86103082e034141c1078820700d1303010b507401c94a500d91a40001c07040a6184150070314a020340c5000622424044540e9440740c0450103045091601301c443d00200c10960040016500e1b45200c1d0440010f0762040d00c40c0131171070384001c111400b0341000c07030301d801c0450080311590603039160017070311841c = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 579297940 1250 579296690 579296717
    0x108070e0111010e0d050a09080601030201080109020c0a140a0b1807150e0904061a09041e060605100305040b0c0702030d0503191103091912030c0513090204091803 72
    0x219110b0200b401c070300641d00d81c40013500c90441441041441c0303580e40c541a0b101c181004000c1c0031020a50002c11850303110400420250303134070000c3c0701c1c11503000c0701005a803546404041428010b0b105405000c4941218032040343c400c002801c100d046001e541004166242d400d50216000d07541100d000c3c156210000503c000b8084200b240c0100b141418160414500c440c08285061412a02a5403040e41d07000c5011401d40000c40c2e102c1c410100702c401c04803529080d52001403150300b000301c1740f00c003074401901003003081859070281e4007400e001040220704451605001b0083c10046a040f200840058081100c41404205482c4070781c0e4010003618074002c9601c81203840380c10051054160000703404a040d45a2011f10849600b40b600d1400559039181220405141c20043c000c0c4055941005002901240f04c2c180c007804a44c1842c600130810000401040742c07240904406807a11400d400350000b0070240c00e074000d00480e04603c0d81072107026882e0b01c182e221200c9608003e408561020020034 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 579299190 1250 579297940 579297947
    0x130f120f030203041220070e070e01030902010c0303051005060d020904060503060408030601051c0c09030201020105010b1201330309021e06070b060a1d150a05030304060f120c080709050108070e01 86
    0x404540e0001c042d150302c1b0301c02d00180e91a000307103075000d43c1219802c1001d00156581c000c1c0d400e21640400e003400c1c01030301c0e120340c00245001d1082d1006001c05594002160b1400c207000407001c01008024065925182c21601c444002d500c01c5440c42e220b01e08d4244005010305011685c288250340122031141990394810064501e9032002c6c40907146c0007c550341600b00350049104591019089584855055086100181c01c507139040e00a4940c4410600550072440852504581035070035141810700184641154800c40d2a052400780c640c4542e00004c0e400c0b01d613490340c45000c0142c022611900400600f181d0040503044542e2403a4110004102e40808684000075640c0c03c0003001d0400d5098503a900303500b42c7c00a00228526840305907031014001d100c540780441840c003003400c54541c141c0c1450100001c0d0b4902c168031480040c08145195104014050403440b20750340e103514818441605c00342001461200120769800201e011344201182c076503c01c4100030b21403141515003156078801c0c42d0055 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 579300440 1250 579299190 579299207
    0x7020a1b030b190f020310090f0207121e1409011d06031303090504020405060412060f05191a06030622090b0601020d031a040203130f120f0302030412 66
    0x5411000c85800000002095501c4a41c030034541411200e00100c140c400180589140d4911190141d0042c02405281d03152206a82d0894002d40800641e041c1c80021040190240c8403002d410540c1e01107120340d9141e0010442c594001e01207581e40e4154409010548400d0301c0008290003001d82800091955405211589920040d80f46110400001c52000400c0d50b40b0480c0c1600603607440c48444001c054128208001030001181c0641c00d06050401066070381c040c42c4542c00c0e044013825100e40502601d41d01c0101121800c0710280309510306a824650804418019010018a840b01031194a10b00e00f00110710600001c10031071442e20b41c00100318450703100140c05224007190320a0200484e83c28420b1145183c03007016070012624250700003a061003222100d02091500301840417419280e000c3c2148000c4408442c016101d0700c0d16000d06186100000008003111079400080d010f111228080207034400c1c1c550359040c0c4105400c00d08500f60701041d1002840d10300d9a400c1d100800e80109c144 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 579301690 1250 579300440 579300473
    0x203030c0403060902030118150e1c0f140f04060e09040b04060203070e060d0f050702150115050702100201060302100c02030a0b040602070b0a1a0402120609060a090603051b0907020a 80
    0x400c03012000002c490400b80e804d0800c07120250884151220b2201c24002e600c9aa10301c60060120110007903820809914117481c0003040cc00c40d09074000c0040d018441703141c8840492081251203005c401510012507019005100c0403401d0f41010380d5692820341c0940e4411984a00041e0040d240c43d6103038806900080d10342424400a0240c0044680b100f001404c6850076440b004154440d510540e84201c2c2c0f000740c1664215005250300401c20b500c2c071a1040d0454142042d00346012142082c1269140181c1d40002c1d84925458000044070354150014000c2d03e0007100c60381e0b41901e1145080e0751071001c600009401d030300324114400110301440d607020317485800392101610388030003640c0d024185a030448400918907078034100c5100c0144c03000850b4031291402c0e9000c5181c500c40750000080b40d0380c000c22284c81410703a031000920585a103440309004100741c2c001480029103902e03010362035000c0d5045200150070941580d01c054641011424028055500500680b00c0383d500c52810700f032611100d = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 579302940 1250 579301690 579301693
    0x406140a1b0201260a0608030408120c01150603020310080d1d040b04090b070207060e090a05090709020c01020408060603011b0c11031c031a0a06050a0909050f10060203030c040306090203 82
    0x3e9000c07058200c0c00c0c114064004140a4900c610701740070214100c441940103404541c5c401d010a00c10600006040d55080c55445115921402e00200303180c0504020009050848411070001500b150141c0285010304048036200315050340b154111640d804103a001000002c407004a441c00d03142c0102d849405840c40944045020710040e070104080c3c8203000011500c0c041154208a102d580c1440160050070413440c0011400c8600000291610005441c084c00c0e599600d01040590f0300c100302407001000c00001c19074a0b8000c0e40c131854000e402500c5520407600802e80040e03541d24040c41406000c8400010f41c9c0c150b01e400e00d0086500422425003104c980151242c0c958003030390200075080b0210785801005084000c101c1c801010390303c0c903500605142e20420300303400316a0ba88004034020303505c2a1400d41d03182d000b820400c41d030305000f0380e002603040b500e0f0900380b14210604581c0d05101c0c40b503455001144560360030049a4174481141e03030f00f142c81c006010a100150003900003191540c0000e0 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 579304190 1250 579302940 579302957
    0x50f040801090305130e040206040b0f19020715113d050a0c050c0606091f03050a11090709090f0209030f0115050d05190501090f080406140a1b0201 65
    0x6206003101c403000700c00d9010035008105d018003200703c4543c4501411030348403400880e040c1640070400a00840c000e100c02d0301000704580001240210540b240103410441c1c80f0600c028544001c1d4555005016401e411140c00c090410018050380d041142e170380e0803078010441b007219007150703414003241a0844094880c4181d850b000031440580d15918202c0814000552420010f00328411140001c2c403044c140b081c28403444040c2c130b00c04584903074007000666500c00c455461900c0d080d034818181982000d1183c03d0300303002c0180600001c50034030b010720401002c100303000345204000200504480100c001110180148107400d0503800200f0103190781c00c0302604041299002a060200600b01c240c0c7c1e40e03640348030351044298814010340c01010180d0303046040340c426840d803075142e078404c514484130301010f14091410400251720030032030180c00c40c049460783c0b0118030f0140c9042d031043c030440300082c0c40d03031002000030a1101c089a81c4501c10343c42304500d2040c0a048d10b105c0e140980c0042c1d040c0207003031 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 579305440 1250 579304190 579304199
    0x6040b090a0b010b04090612020f090a021c0e010e1903030b03101d010510050d0f020a1a07120f0e0f12100905010f060501050906032508060306060d0210050f04 70
    0x40106401303003180c161810307101c0b801c0c1075000c012500300760300442c081c48814501c00d0150325400c0c04502c40490540c3d040a5aa4580031010007a00c105007808103600112420b065100741c295000700882c04105000317021009800303105560351464070514114801014140c50b0000e40254842010300380050107036081481000c041d00100d0b1180c48140e5030101c9144884142c0e03100c20b2041c298025070b82c1e030050341d0b468201170104100c2c11480303a000b401107451070f60720002c0d03640d0644c2d120000d00ca4040f200801402e1504a940550001c500844403901c1b0f49840321003035406010311400e640360560355288013185540410919001040c01147c01501034a40e100103000306000001c2c107080300b1000450034020354a0202d0071074603208082c080b4140ba011080c00503a80c8502140e91000e411529140c4036113400c05020741d00880351030701d4000c00a598441990071a04001030a1207403e0440c10303100103545000501c0401080304200075802618501c4c8114681e0140d4081c1610200713405a0354241a1107 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 579306690 1250 579305440 579305453
    0x10519030609140105010f0c050303150d021201020919030b040f060221181204060f0909050a0c090503010203040b0a020315040905070e0705040b161127061206040b090a 74
    0x1014801d03c14808200600107540c00512180e6990a9885d04808a400c5a00c80945a01000e0800280003c543d28410010360b6500c084504040d002080c484415142c914842d00030740c01440054042d0046003540c019050314065448201d0f41c10032649078140d5244d98076109280d15580d01102c6c0b1310707801c0c41074007100c18030744c400c0700000801d005001a45041c801401c480749031660740500f140d17070721520591a84006800c00c1e0b40072104c90341850360408012034000d0745c2c20030103070700440740541c602801c00107181081d40100c80d5120720750715038429017070310350307051500341e1100b12400b03403141c3c0741580072a900c00101c3c0d000b10b030b1000d103402441040700d50b0080080d054442c000340548031036001c41001d00c44c6101e07408200d03401c00c50f41d082c42854141382c80b452034424040c0d040403107140002040f1303400074062103012140e55118001c0801c540608004582e1841040c00c10310f84104c0c043c40000500c090401c81ca160314901c6851006020710b07940d41d681d1065910004007030301da40d40120403445001890 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 579307940 1250 579306690 579306701
    0x4020304081b0706121104090c020a050d020d1b0b0f04031206060206010321140d1b05030a0e0d020c060903010603021c031206050d080315090705091e010519030609 72
    0x410300c0903010076858018001d045d100f194280d640c20f6032802595404c00048070003241c4c200c0e400d102002c550390940d60800d81c10151000006489030140c1c02121401b0350340801c003200595800c2e05c0f40010407039540490b12428540f0080200a1450070700401c06100e00300401907841031007441d220f04001c003000d100e41d040c6e811581c0603401680c0408010302c00c0007214211096180c2542c40b82d04003c510704038009280000c00c100c04103011000044030303443d4608030342006e5044024101280500500d000d001410b42c1e1048801c4030700700f40380042c0d02c200d8110200d054140c0440c541d000b8440b842283d4200b010650200c0c0360150b141d07594002c000010b8861071b2020342c3e904041d010b500d00341403ca0801800141b07444c42550f840600d0a103060020355a0407490030b599036000010385450355100c2c0201584005551840741e8400d54100c01c0201041e071010080603e144181c91401341d00104a4010140704040c0c3d5000f40420414808042c80208800042c451b5003554503001c1200d5a40d0f0609400b102c1 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 579309190 1250 579307940 579307987
    0x81207180e1b041701110909010302060c0c03030a08010816060e10091502061b1603112d0124030212100626031602060a020a0c09050406051f050402030408 68
    0x13201c50704802a81d1800e00c18401d2a0032400c441515080e40180054a030350414080248130718008140d0700140394040080c07042c0b01d04040c0441e0368501401002419040091040040314801c0148480c6402000904501142c40c0b40d00c500b60800d03500010044202c10106640c000c103e0100c0c00018040035045110820b010141c0183c00c02e070401218085500c0d07003101c4c11200c0903604010151003e00310740c3e24001015010700d0b20100043d0141803090600d02600c240740c0c1003034040d03200d0b80f1950301c80030320380c2110b40c903030750000c02c00035090a0f400740105c840b120501200c459510400c0001d4203104001078904a02c0e042a42c040c8401c003801c880031078103d90414010710b10b030740002c040710528503901c1c2014010304000440c24011b401c0400c504500300050001c1c02403801188520b2042d008000d000034460340584140d1106071100c03400781c010a0211402d4034082e0800001c81c1d21b640808000480c03403255203241c41c80709820901440b01070360020f0001c40b014001001454110340803000c0c06529079 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 579310440 1250 579309190 579309209
    0x301090f11040b0406050a030603052409010b18060a180b0f010305010b0901320c07090606050a030e0304211412041403011404081207180e1b04 63
    0x4045518440c089901c1c002040010341000c2006101501055043e40d0848a0915000c0d43d20301d44003000300c01404c00c59000810b103214154405600c0c4003141400540c16012b25007410389960340040d041d00381c1e410b17000010381141c03401c0c0008404c241c1c19411a03510903800b0301010107065980460f0a40c941101201d00b001a40d180074001c554074020000c00300304c507800d182c00d0103194100308040322a0700ca03111100341030102c0764a010810030341c50b0b20307041031907040d050b4040c044003804400300500394015480c04005005840011555005500c522410b40e00a681c41c141407101410b02540104080500c1c0c981a20040c00000b0b5000c11460b221003085289450081000f010345c9409805c1e03485d102d052585c50780281d1200c14031981c0c0c140540b0103c42043e8242255651000040303401041d1180d00201501010f00404c401d1043c0100100780f0701c4251005069155104d4000301c0304040080008044480c19040070040fa150314407030b10b80c000041480c5625080c034051482a020f9202d6403005244 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 579311690 1250 579310440 579310451
    0x111903090614070b0606030406140c1308010c0c0b070c05010903050a08090705030607031805060f010510030e0d0c03020f061618080a080a090b040e0a05010b120109110708030109 78
    0x12039012600070b00105030003406900740355580e6240043c008005088501404000c00042c06010941d0008260141d029000c0350050070300c1d500d040c0803940326a100451318130355080001480c420510420f00c0452541d6209801d1035216910502c10280140c200d00820400030b00f12008100300303200701d1200c0c500c6615070503564514401e025008040041801400e034100520801041c1c6002c101e43e13901103018640000c90645a04d0b40c0b62178020700a02c054150f10a4000300710294810200c218141d42045070342d40300d400f1000b50210b0568420f41d880004d04d82004010852440c043c04090b00d45070b21078010f6030309189000011a2030500100d55a401d5030340c24010944245411020344503d52070017920000c00d05080c03410303050350342c8062a40284a500c001031815103043c81802d2440290000003100d07a41c0ba03581703200c032223003011080d161681c1d41e034070f0440001109000c5c007080f224800000307101a900c50f841c046503600180120b00000e56002800c00940001481100086001c1c284002c0005207 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 579312940 1250 579311690 579311699
    0x50f1b191d0d0b0c03060d060c0f201b0102150a060f0b1608130b030f0609011205030708131203031b0c030c0f150e0601080712020d081303060606110c060f090111190309 74
    0x10002f501000028540c0d00c441611b145254085002c40d4110400f00291044d000f50400403840c0900d0354034810007804480b800c0c0440705006070032000807210004c0e03080107042c1e00ca4580716901e201d020004400d031088a070b201d60014000401410100c1305400045403241d0390342140801d984d1048840194000c10707003003085158908800281d002d0f20a804440c2e49407441961807591300d00c15590041c0c6411400b0610896003d2420310160140c824072b024818901d11a14010b000380540c2086e014692040c003800301c01082c866119140081d4169840100c003840e00d465142c0c12003000c4d801640c12010f01801c1c666030b40041d015100500010350001e10b10796250910041c1011a1900300f00a031003c0414241e0241e0f0300d920040c4070aa4102207400d40d116800c40d80c003c480495940b0003401903061140008125400c034044030452070076003041c2c51107295814108982ca103c0e0380562079800c00144000300c55540b20301d08802c0403810380c10444003a090114500c01030043d010008034000380840c2010b01 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 579314190 1250 579312940 579312947
    0x60307180b011e050906031f06020d1205060a0501050a03090501020f04080f0303010b03071101090b040c030b0f01081b01020109020604081609050f1b191d0d0b0c03060d060c0f 77
    0x11508a8111404440c03070f92400ea005009101d0800f1040c800c0b8000720116141c0600c0b00445804a0011007a44007003a90304c10029440d05c0488155002203082c070543c140c448079a40c054203210b190000c0110300280e0400e001515a600014201c00402d50b8440308440010f000348000e00c2d4011140c1003035a101e514100d4428542800741002c8032080c1c0051004103c0f040b414400c2c0c0e03400540e941014a20300c0c560105660040050b013070082d1170040050184018040c40c040307910141c9000b094100e20a41d0740400311a02140207220785405079100c81c1900100b0340508600000c203200c14400404d140805400145040c0c010fa040f200641e040f4505101c941040484600002c00f0143d5040c0000c0c80c1545002c41d0107440140f1aa030380401514041c040c8414040841e0f0788400001d084052540fa18180140070f5800c00714000101550185112480c0c60003400200005030f0104402e110707035640004d42019500050720f01d0350420070f0f00001100007640c5001c0d45620700c07441d07954412480d0032100003c = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 579315440 1250 579314190 579314207
    0xf0210061e050406030b060603091c0f080609090604031110060b0c2103010e0621010b27150103060b0c0a1104050c0a03050601180905060306070323060307180b01 71
    0x81d02c55481e060781040011100c00d542030303011108032360f01c1c0c0c2c40340d481840407402e10741280c1640518140441d243c000d101e0308981c3c1d0150085403551505044c0d0780355824810040c400361030b0000140d05c03a5000a000900c100c1c1600c603031000a1042d20481e500200888098900036085120440c4010403901001101041201c0400342543c10080040c081100100924401801020121650400091003a44901c8104042c5a40104446401080011b600c3e402800c807070b10618400c4116110720720400040c21581090b8414031080e4a6554640080c40b8581d00303c5024042e040c0b5460341c00000740c100112010b1f045104000e000341030410310078500040040741c2c3e001d00070710a03440c100900400207481b4095a0081d0124180000d03591980c50040e5070003d0007420b0703800300b104103610219660304aa0450341c040c01095048400c3d0340c903000300603000c0d0341d00681030480724480d0040d060f400c0c8141032046d41d0803c801030182c441c1140ca4000c121501800441e9011a8a407106054511940e001404 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 579316546 1106 579315440 579315449
    0xc03011203030603080a110c041b05030a06030b010303020d080a1503030305100506041e05060a02190804080a0602041e050f130f150305060a0b0108070f0210061e 71
    0x10040d810026803500923010f010b0205405040c903024140750404000c000e02d00f654800c01c02110150401424074983c603840300b0b0000013007646a10618081d500a502405070042c2548019041e10340140050104919007003411424030602420182540e83c1498040341caa01c0364000303da00114a600710691003100014001030782c80724108061101c446e80b131010360b0500c0c2d5413020000c1a00500f10240c0158103c850a14054103032140d4044249224401403802c0c240c490254900d0800450021034207280c1c0068140491185130424003116044500c80f0250181041c0110b0302d840445003c090042c3c15100d00e21a0701445500109804a2203070f4040140c84e15000343c43c000ba0543c0e10040c1c4150090b840444e03400741240c0203082c682107040e11200500e1b2540401250254000d11801007140030794410107115400a0080c0c0c802403003411a0705e45141c01b003510f01145500302e50b01 = true := by decide +kernel

theorem cover : BRFrame.Cov 579136690 579316546 := by
  have h0 := BRFrame.cov_init 579136690
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579136690 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579136690 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579136690 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579136690 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579136690 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579136690 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579136690 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579136690 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579136690 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579136690 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579136690 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579136690 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579136690 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579136690 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579136690 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579136690 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579136690 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579136690 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579136690 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579136690 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579136690 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579136690 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579136690 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579136690 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579136690 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579136690 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579136690 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579136690 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579136690 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579136690 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579136690 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579136690 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579136690 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579136690 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579136690 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579136690 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579136690 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579136690 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579136690 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579136690 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579136690 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579136690 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579136690 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579136690 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579136690 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579136690 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579136690 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579136690 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579136690 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579136690 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579136690 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579136690 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579136690 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579136690 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579136690 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579136690 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579136690 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579136690 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579136690 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579136690 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579136690 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579136690 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579136690 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579136690 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579136690 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579136690 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579136690 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579136690 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579136690 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579136690 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579136690 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579136690 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579136690 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579136690 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579136690 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579136690 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579136690 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579136690 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579136690 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579136690 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579136690 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579136690 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579136690 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579136690 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579136690 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579136690 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579136690 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579136690 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579136690 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579136690 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579136690 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579136690 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579136690 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579136690 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579136690 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579136690 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579136690 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579136690 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579136690 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579136690 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579136690 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579136690 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579136690 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579136690 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579136690 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579136690 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579136690 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579136690 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579136690 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579136690 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579136690 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579136690 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579136690 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579136690 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579136690 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579136690 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579136690 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579136690 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579136690 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579136690 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579136690 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579136690 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579136690 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579136690 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579136690 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579136690 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579136690 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579136690 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579136690 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579136690 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579136690 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579136690 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579136690 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579136690 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579136690 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579136690 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579136690 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579136690 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579136690 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579136690 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579136690 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579136690 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579136690 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579136690 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 579136690 ≤ n) (h2 : n < 579316546) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
