-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3272
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:10:20.012021+00:00
-- url     : https://prove2.me/submissions/af13ec35-c470-45e2-bc6c-c832504da616

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 588309352 ≤ n < 588489208 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 588310602 1250 588309352 588309377
    0x20607020f0609060408072102160608060112021c050c07111c03080a02090d0516050d0507050f040b0306010909030f080f07030905030d0c03060906120510090602040e0403 75
    0x1800300d001d03060040001400c061510b4030516540b0745000e88040d003e10400610b11043c4508229000340540c0e01000d0b5103981240450020f6654034880f415040380618000b002c030340b0b00c0c80354000b94000c400c142d441d802411540310620000358808502034600300600300d0380d15184213442c004e0318851803101f0440c030303200d0025041094035203a40b180040c1c40317200002481c003c5030100355545041550540752208a0750360307020a550003485840d031066401848080240308001c00000d050044800c060800a9030643c0c40061252404461100800301c0d0030402060185003802c0c0c150140b6888020004101c201c020004a0306044081c1c0124000030b4541c201d040a154210228110100c404e02d002c4909140410355800311160107030620040680701c94107a020f002c0c0800c10f5800c19902c41c00e040101480d000b8000c1e00070b007042d1150325a29410610001050744200a0326054a9008409095004040a85680284184a804c13110301303500780000318009490b00c1d41588190300c01d0b20fa00003a00300e0b = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 588311852 1250 588310602 588310607
    0x4020306010b0f070b041a090a05010b060c120702030a0b01080f19080414010207030b010801020c0c03280c080601060903060b0904261e0417070b040509180d020607 72
    0x303050300090380d40c46007000000481550903044034807864000342c10108070780f1146071135050b03508108080150400844c040c000c10340780100b0140e0803a88140002c0140500000501c043e82c0280c0c50325103a20f070400f000e102c04460751030004000d05440141036030a804a60303902c07034260307407003c0e000344034142d1106069a24444040220a1207061a020500000521692500d040303108a00030302580007594034141206034001c0100d400a140d200d00301080a43e1030700c0c0540c0c000e42281c020840d451107612640c01081c28042200c0070040f828130400b4204031203030403201d659084540011107404554030703400950103c0500c400c1e40030b4000784c1d664405551843c24188160b0b00500e00d118459403000b4103200000728140080007008483c4161038401d4514502401d40300d0090b0790300400501d6045000c80b40b2600100001d0050b607803144145081c0209400240741d40700254020b81035400700c108010b21881c9012803019500006414810009500d010b5072542003510801c41500560300c000180f00b030f801d4 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 588313102 1250 588311852 588311863
    0x1509050d030224040c0b0a111f140f0c0307050f0a09050103063312090b06030607020d02030d15090c0c0309080a020108013302030307081b09010e120106030b040203 72
    0xe100c180d84801828180c90b5042c07900c910341b207400048480040d850703200d2400f036880d80301a1003003a015030741c80e000c03007419002c80210039104000c81c09250051402d130000341003a5042c0101c0c0302000002d0302c0d0380c440851107660743c40680741e01c4c184030003444481c0405e8640d00c01021002e100355244210185854005020f81c1c07641e8000b014007010050304204089000041c2540c0405580c007012a1160001c6042e207501d901400020412420800e0303480500000340200c0d4000c0b4015022200c482e80d41c03030003c80c2c540c01e402d0144030043e0000c100d04000a80c06030010b462800c00740060b810110b540340c034494221914154002c0c0415440306002d0141500428600018001d06002d0714108200d6400280450310501500c0741810a4048211700720401c000d40d540c61881940d4001200b045080c80a541c1f500204d58200c00588c0c1800003440013282c0d007103c1c035502031412440c0ca040ca09034500645807000c0c0c00d01c150f608050100102c0c17407003078400d0007000c005500a00748100503003000d0044c9800c04 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 588314352 1250 588313102 588313153
    0x106080d0801061d0f0a0b0711060a0801143d02120f160501062306070f02090a090b010f060306082107080d0f0c12060503071509050d0302 61
    0x100380300004004664100507030040382415401340d51050701d940c0e0000f40511303e44103540d94214802c03a501040030007c090080ca01c0724002e9058460504400040001500c21481440006001d0000420001d403a101d000702d0301100052811b68501d03444000144104151513080004444904030801c414003000d0b1740520950701032015014040308242d800046104041240c040c2c806d0014100d010104402c4441c81d5590303000b0300a00c001581d403140d241c00300b40e8820382002440c1192066162038a0010100d0f40070980c03002900540c02c50325003c20010304c00c01001090066150f0780c030180010b80c01721800e030280000003514444141000c01c02011101c054016003c1580003990f2122000001021804c000410312200e5aa9441a24003e001da00861000c88005800d001101000e034241c1d400004c090803240d5034a00d0a099031602c80c2d17058030f01d00c4c032505030036802502041c01911041006485999050b09024011507a80c0000c103666044e62801134005030020242d4842d04401c0c01c1034620341 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 588315602 1250 588314352 588314357
    0x908030f0402040510060818070503100b03190b0105010503040809030a0c080d0c0c27020a030603060e0c0a05040b01180e01030c08060c0d1503080a080108160803120709170106080d 79
    0x10381b4105903002d02800c00142c070306402e04a8044200505940c1049110301400001d402d45090003e40740100307025010380c031038052082c0a00344c0c00c24003000d08442d8003600d540d007200c94031200340d107000c0064603554006001900e88400412041229413801c104000301d50788200c0c1170415041c1b0744000c540c1010b01080190007004130712101c400c00308148246020580b50080c09210b0402014034042c4c0310b403901003100d110440d00100c1c008003015010351090742224010f082c20300025200c41e05440e101c121515105078485076084003400f05041a030300c4a840b060f418140325401c2040c804600203070702c41e640c0c40b408a000340b203801801000109440c9400420551006254031308040280e07803098021306d131001e284a41e841106201465079003400340300071900700c0c2c0456542c4482010003080e10109000d6402140310703844203000c9060b14500c2041c01c641a00006d581402400318228800c003070090540070400c03c7d0b40740082901c14000c0442e1210b287c003240000f401e030349010016030828002d40c51110a = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 588316852 1250 588315602 588315631
    0x31e0106020309130c0203041203020609102f040902180f010503010807030803091542010509040b0306071701060f050a230a02010903030e19020607060908030f04020405 74
    0x103e07074440314100701031444408004a56940d09190032880c50085038460074000031101401c078181a00440c21a0150a402042d99100b0014550701e4041c0c420801001029210b0080d104005488521081091210201109240a03134030824034050383c111070383d40c0c0301c14000300780d0b50b003440c0c0b81c68028641c15040a00b4507070b04540c90506031503102c00c035a21010380340160000c00122f024205009003002c2040b00c03042200381d402d000d209960b1134840c5c6201c0031071082440c6010401282450180c01c1b1405001050074141901c107001103a503504031866054100303841ea19000b0242e5000d1008a00c01c84442d40d5100c03229031034040e03d50b4800b20683c090300500503c0d031010302e4003a41c40f204036119003029040c19402e00001142c003e0070640a0340e80c00400400104072241d0055064011003005070090341c0500c5023614110010f5110444081d4a03100312520620b480b00606194011780100d9001e64030000311408240c40b2824240e008840303500356502254104030071454644030b06a040071400c01040e1 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 588318102 1250 588316852 588316867
    0x10501051c0311030d0f0509100501081c030e060f0613060e010e040f02040c08010627051005040305060c09040606080603060601030b030c0d060f0b090405031815031e01060203 77
    0x1c940326400310300501048032244070034454070740800850315498852071042080200c1502c2410041500b85c8414400e8011006501024441c900400d4113941c201000341541004019a04c1e20310600d04244900341034035142065102c010900c034842c807981c1040c0d091101c929000d0304025015841d01c086d18903207854500103001d031180c00c40a2300d06451080150f45129101c50502030001012018002e5005003054100140194014202412500302e5164500b0708200190b0b14a0801c0401c80784c1401c02d100c0950400ca0313850318220386e0016141c241011481c09440e40c071428207006007113a50340e00c41800045e40d64981e0800d4807801c0014180307403800b4a51030800200003621707114054015410152100010b5001e950148405000c2213401850b002c400059442e00201409851007140c880070f00d40300ca500c429080c00305010b84282da001c40030b10301c6c00720a0942e203001c00071444115604101d5180c074491200d20310b90011801000920045403110180c0039146071410b078140c000c103045400a22081 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 588319352 1250 588318102 588318139
    0xf02030414060706090b0403090302011103041a0f040b0a020a12030c051b0319121503080409090c0f03150c0311070b0c0705011812170c0903011e0e01050105 69
    0x90714000040b20007a90f51110381c00e01101610341a140a00007080c0300341404101600f100c0c0d0039003124800c0e21540e03821941102d00a85902440c07280528a0f0703007034012802c5006010008000120f44400d00a08081d00e803003001200d03400991190000d6407015000106200d00c1d04c10a1001000610b001c0c4103030f00144c08010281c0c0294002480c200e074608a505804203018825100b0103200030709a403441d6450700c00d00600c1c201d5100180901c2c03600e4240c00800e04c244008004081d2504030218900d02454110110010304026400362050005103402040c040064030b01a401180a40300c001c00d8920398418200c200c1302c0702c0c5010400e243c82d0581c80e9480d0001e51040d18159604403404178050741d0b624548901c0da1042410007802540b0348080b09034880c041c40c0c0d40d801158019480c1054100343d0310420380e101400f00705004544111030000403d49c03092030004002d02d00d00a000420007000035041507544004c204007802d01d1640311396081760701c51003d01c9072900400341140c1158030503071009500d = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 588320602 1250 588319352 588319379
    0x71701140105090d1b090e1204261209130615050a1106100e010905061503060409050a03030507020d03180609020a23040f0219211b0f020304 62
    0x1401e041c070101082c58007403560740801074030b0510340000942d80d10051111001806081c18065003100911b03200358605900c01c002100d801c1801650a200d10301400c1021041c4031360007450700281d210450030001c90043d2000d0000f044c0c2c155015000d80c2e2160580c008118007501c00c03402103442c10f80341c2380c0c01f04000005204038042c2da82c03550030b0940d5100c0e41c84404a030b46032440c0d00302a415104101c24092170314107034421882100c0e000c0b164446036980360201e074801d98800b904e4096000c40b40c4940c4d00d1201010000441c8c21040050000814031070a54075903083ca40181400c1e030220750750348100844150148912071320354842c2c9c6001c11920000340707409801049a00c0700a000395603906044411500c40c103542c1c0307001c2c4c41001e403403420120710070110703d0ba180c040c4003216000c0d41c01c1c48210003245100d8026204000000e9030100800341443d0401c585d0b03114900380d45c2c117010412165101d1107480510030744000e100c800748141120881e43c00003821601407558501e0466204010410051007000706 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 588321852 1250 588320602 588320639
    0x3021309050c10050d060f05031213061b020d140609210c121c06150806040c090b160203010b010f0906031806020f0a02010606030216020906030a06020c06071701 71
    0x60580b089000fa200c11107a9001d40e19a403038409107849404101522071404900880b0000c0b000c03200388003c00d160180311030058806000480c00004410300c2041d004054000803990b020310b144c0110800c5400190034100c0240003a2078100b5080d0403080c05031006d000507540044140014104200d4821034030b860a1040d9065000322280400c0c14500b42800f1306c83d070301000016903a9a51034610358035420396410508007401038000c0c40c06000142648840c951311030703d20165110040b040d80d41a06000c05002c294050801f001800e590208000d400320000d00b200310b00c03103460400281880d02c103142c01c503814803a00a05204046145c01e01705d0381d211644c030064544034540032902040701101038440c5081d0320402400c2e180041214403403809460090403a00180fa802480b1066072000194203c0c45032000900d00380c01645059005402c002c4403031504004041e0844802c85440c2e2107030f9007241c02c0b905003014180c00020520003c158401655102c1d082c5c00654001c003545808440381c100c2c0c14065 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 588323102 1250 588321852 588321859
    0x3070f02061306200c100c06140a0b0405130b060105070311030f2109071e0512030a0807030e0a02010804020d150c020106061b031404030c08030403021309050c 70
    0x10500045403078a805944660015a0740c0402041c1c560002906007003680000e4003241c5940b180c1802e140200080c0c00034001c2015061091020034408102c546001031102a190395894011641002c800e00300054400d03190000c0003d0721001c440104401e9400107000a0030444103841001c002c58405ea180301c0e004070090030700d03a9441e11985804e480720340b9510b03884c514501002c12880c0d605440c80d0300401921340d600f000c04030301075003907101401912000e40390040c1c00d903c20001405000301050000d0012108982000d202603683c00000b601d003000e01c01404041c2e0004684039a0050708070b01295044190b03400c0070300810581b0410035a071211200406410409517030042019903e40040700e001441c1c10820003130344452440d61444c0504510359083e00190b180181c0003c801d80710703043c00320b80e82c8410b80444081d0b6819440890746034415001190110b001080004001600107810a00804131070010790f442d01c0c9140100060008a01e18450b203117400e0060400010380081030380054801d04a = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 588324352 1250 588323102 588323123
    0xc12030f13080f01050402090612060115050d2a0804110405060616030903020a0807050d080f090d0507060f261f0303020c030705180705070503090d060b010e04060501020307 76
    0x40340c01c0c0001c003607907101d040340e40101d00b005402c51070190403c91090b4002e503007061803504e40c0014000203110a00c2240c0032908903000622180100d0b0060416214417490320380c0c2040c43c14091441200c48004600e254204240e490700f00502c0c0b040c4030b26521440e6804d01c000300349055160490440040b00c0400d106640e9180010740950726107040e1550b1240450020b2034440091802070003918050000b64070440480000050300d21000855405445000c1c0c480d07420050540d03102215a000802d041c422160140501c074442d442c0d013800d01c2036850040c0c000f020001d103003040141a2094500303d00081102c85e03100c1c045541d0902c80ca402060035280d0882c1d4140c0e50302d1800c143c51500f1108210300d003e0100e20000300b0702d07034001146240384c54220706842c807460391401000980180c2820324449040c50b02e0008505078005c0c0080c0c08a18020029285010750031800030711071844c1034400721032065030b950b662981c40d40e0050078001c0001c4113940802016040c180043c0d030301e00031010001c1a14000c0d = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 588325602 1250 588324352 588324367
    0x2701081014220c0b1812030a03021806030403120b09010501090608040c030b1008060f130f0f172706030c0d09060603030306060f050a08010e1e0c03090c12030f 70
    0x190b405109069030006100480300f51164002c502550006520700740498074250408100c0c0382c01c045a4000e041d6000c0210720308410741c14140c019400030b4020b20313810402c2001004242d00e43d04000c602c124030a035524000444010a40000c0703401440c0d95600070640c4400500241e40c02442800c140ca825051406440d030320740c504001d645104e90030041441d20a001480700d40e0f00122130031000d03100d0f03081c1940c120307a980b081108211641207402c2040c0b036240d05070100201e951112040c03080c80c000c0406420038481e60701d6000b80c0604089600d000340b840080c0c0204202ca1640300450340c4680b1130014413082d2809030001d203080c00050420071550b840019089210301d0a1f40c4034081103a0b00c18028000181d407400c016009108074840c0b800441d00c180d00d12086076120b0b01c1180c1d030f108080e4603000c03d00d03420f0401c0035144000042020000c02c0e58040b60104100c13120184620554020b407480f0360380e181200141c0d08168500b80d802d0302a00c407607600e0b400d103035502109032040d1201e00c0700a40d88800c0c2 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 588326852 1250 588325602 588325651
    0xf04060b040c0306050a08120910050c150406050609091509010906060f050f0a0320041805010b1203130527090705180103021e2701081014 61
    0xc803624690092401101ea4001034154200104903041254041400d55540e0410368841060749180c00490300100b110a92074a80410001003034503042c58003600b400a0100c90fa4070b000540c01203075038803620ba5030412042251500945500c060140d4030744401d41803590b07d09580310503900440400e40740f10000a5880d40b000d62107100070680098051000656800d0010b28841e001e010302c500402568200c1c082e982041d4249404a0b6409240642d030300200d0444004e400016801669005440340035030790f6011000364a0040c2d5070300410000032026008800c0100001c0e1801c0f00c0c06158005010050410fa0f4101100c0e00300c1e0800d80d001d07032640c00384020014008928040740b000e10140b010500080800001c3c5903015544103a44040c00407000305003411031000c0910009611080c030a20026241e2190141d1241440c00903140b441f100850f4400c0e800581c00c101100005c60b842d0310010801d51008124540b05201d4420003007110031003500040014000040c01d0310820070000030350800011 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 588328102 1250 588326852 588326861
    0xf071502121603200403050111030705070807020d0804080c1e2d03030c0313061701122607052505010507050f160303021606021b030a080a0c030908150f0406 69
    0xc13040130041200208100007409560014041903030550718042e11000744502110459009010035180d041c18400260f460304d06035402040c2c101d82000d0509200b0000603c190b014001a10107107028020b440c3d1500b0030f014000020b070f20702c1c2c2148a20788040e034a41d500c60104e12011410405199510305081c40c01c8001030200c0c0c0303000a5010b02c07000034413402d603890100140400f02d1a00180e0700c40c065a884084869034400042030000e89640300040107545950500c07042e5107803144200c0e8030001c08503440c104010001c801c0500000100040103010020240304000003413001f040c950b0b0030b6040303083e0284109002070242d1410704c07200040c0032061000030815514400243c0c07040b5055542510f17040c46001103148002c50140c441e040d0b0a1941e0b200a46245c81603070b02650040040c1d42c140b1000c08201420710316503507014000c1d4440400800c01031401403007400c0039034490500c00b81c00d502d0001c040096591241010b904104069007004141c0b107400c0c0d8010a41e1100002541c030f41d803c0043c001e2 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 588329352 1250 588328102 588328121
    0x30b09121c0612030509120c0102030a121806021c060803040b0913060815060108090606041104030503130501170403020c01180e071701090b1507170f071502121603 72
    0x1944161240f42c01c15030301400814049800381d50790340c4d18120022200342ea502031650602d000d83c000b402499015482806480440a101c840c0490702003c10328414600340d031806400e9071480c2d000900200325075601e859a80182c640f0900400500c0d06d8188221345074099070041010280000600070b0507a41d510041040c441c0d01380d14108280741d5942e00584e0f0b01e6078003101107128400c9040000e01c130b035070050b40f0f20351091421307102401c031319a81c0008010003402c1c2d020300b40c13420240500c004008110100040c060fa20351300a18510301e68242400034095010150705002440080310411000a80c0481c0b210070f80002828603400c08102454280c5802407560003070085141400c0c10860030b80c1c3d0015964121103001c4030b0303209203662a66001d006a0714205401074100401002480c80c890001009082203405003c03490510161503c0007402d075440081442c441d88004102c120a00286202046d00c014001000f1850100310b03484051580d80e009090300f08a01c3c2e02c496880313042e40680c0125565 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 588330602 1250 588329352 588329369
    0x1050f031f06031a0702100b0f040c11030f0d18150c140304150b0102030c0c090402040e06010803040f2103210e0a05060901090f0b0c0d050709030b09121c06 69
    0x1d01c4c07410444c5588100c4101e031302400620400700350039401281481603445501000d000290255407003420301c809844090080d104000001010340c1d240c41052000d0300300d400f0201c403541d9652003113001501c10384000f2030b028018134020705d00303850000b421080b100c1c14000c5100d030041105103046105880c1c807040460b81140d810800001c02c000c000b4984284c1c0c4086101c40010021424444012a5a4064a00302c000c0341e40c07050030481c070a898004c3d10158000d100400215a6003410b0903198145007003079101290550000c07400380a0f104204a160380540420b04504040104800280a40c1c004920b00502481054a8a01c4100b4448201c031149410145418000c00c610000c4050765890a00740654150050501140307070000706008050006806c00009541c030740940d01d03810032203440544408003c1004000400300f0102d640200791184103144c54100c2caa5280d410000d026560080c2010300c184c100c4450380703188a0301081039500e03160202c4d40c01e0304044030320000180189407540100c4030 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 588331852 1250 588330602 588330623
    0x30f13020a0e01030218092a04060e090706020a0506070804050a050a0b0a200706020a05070b010e040b070e01021b0604050607060b12060f16170a0c0801050f031f0603 73
    0x500701c0200d42a50304985c801e0312004117400300c401d03900d02e00c0e0380e05a6203084a40c02c0f1405080a4100d440031004402e10000b1060300c1c2c055100d4001022103400d80c1c0001e003c164000c0030000f004c0000d22034913008120a00240c801414199501611004c0c0208030b0014000179401050501c00100240c2514a034400300310755441b1980d04001c4003012085845002031404c10800e0f000484404074030503003070280c08002e181081c030b02d039444502940028400c1000c0000a000c00301c007040c00000c216008104410791181642440e08010202c0c1c3e400400100a01160032001c8055076030010307140394003d50244040b642900e941c00000c40358440c660000350711807008100c074000d2040c03e41c011090a81c080b590380c241070f003100c11026283c54086520492209850740020080e0b62294035032544c0d01c100f071a03c54525401c4d4082c090500e0810b451088003103545518110340c40b608000300301c0c050241211441c94409000c000a599005207800c50102d41c00107010030340780c1d168207800c494091a8400c00584 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 588333102 1250 588331852 588331859
    0xd03030515010903030804080d111305011b050c0906030106080d180504050906070c060b04050f100509010b0d020f092106010927020a0e0901090323030f13020a 70
    0x4000d0311003591040884100100d0320803496020301111012203515803220601603407079841c3d403080c90b0400445050340c143c8440411011491500c000c04035070b02e458602c0880c09040c0703070006260100f88807a503090040c1c80c82c40e2002103040000e100d00c0c014412100e051890355000d0100c1e025000300d9000c40b006101d4844800c0300b568004d0708602d1061400b80c4500c00e0b640d900c0d02000183c540641d00110150004404151701d40c0c07195402410050150402155510303010700420110341c001c44030b2520802d91001400046005804407400520007159240790130b50401c0c0c44410345209010204620301d03030010340c507411440780400703403048523900034003c5a00d208080d0400d110080000354090b4280a24800030521450a1041244055008150308030820100104100c038849481d07050340c1c03182c0302c0003000884107881e90f00741e0300c038a0a03800007261072442860080d140603504003001008581810348805104c1264043e03942c0003903400c00f200415241c19456400b050462040079400250100011 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 588334352 1250 588333102 588333107
    0x2042c01060806060a24090506030f01180c0509220515120105330d03110d081303200f0d1103160b090115030b100503030309030a1b020d03 61
    0x1082114660b80035120207030b030342400300f188441072401500038a0602101c00540d5440706404c0000d00c1242d420210051500c0750700166160704215045040300c0020070041c0100c00c404001c080070030107441d00a001040c40b00d48060110700030070543c2800741420b2407440303803810383c041c141e200402103d000803c800d0404a182081c03001461340e1660250004a02c5280c12607014440d051040c10ba0040420040c81107090040c0b600001000b4440c402025140d00750705135589410045840e0701c60380ba4800003049200d1280c0c100505509414181300f8054100210700d01440b903110407141c1d0502c3c14890550048003a004280001d0000c2d201c035110702040c0400303900c40000c1d00480c2d0b03083c0c1d8486a4403030000c0c001c40b03950780c070429400016102c40b020010001581c00c0c88040e40240c5254000304583c6a080b640c0c0c440410305510585454038030074103001340f6640d0000e040001d848140c02070740c6189001541030b41e4034442d21000c80b040080c80000403140c40c0c4039501d02c0c0441540100000000401c50400 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 588335602 1250 588334352 588334361
    0x1e0a0918090609080d0c0f02060f0705210711120906070c15020d1227050c0d0c050a080a02011d0103020d0f090303140601022d0a03090e010603061202042c01 69
    0x3400102e03c0c01d10200400c07806140d02022047c0a6801000305580301002e80d929450080c2050061007070078400382c1c0c54111401c0c00800c5440007050404528a000003000304601586008800c40f40c00c0480d08296078080b2004481490005680b51507031003210349003010940c2d07869405401002c8560a06440080e404243c10001441c1a550710729400e1800290400301c4070072001000300700009880460024902b00c0b0580342050088081d03c484c0c0403501d010840d9109401011034440f1085403085c8902d2034100780d00b0015100d003400404103660a81e0000c0c113046a12456680d14840088402c0d40e10b80c483e0301212006240c802d0700340315518403d48410007800300d1800440100342010b08854045046ca5640c0e489244142d00425a03d200488410380054840400e0318200d50a4a5610340c0c030ba5003044013209240c403903902d2100140c50100017400d0058182c0006007050b040c000100007a000f0b1070554040c85070102c40003d0340d00d50302142807030341074034881d0001000d80e2000440ca100c09010b601 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 588336852 1250 588335602 588335617
    0xb04030b060901060e100e03010c2f0a330203040203010b04142205070b040609080d0e0f012123090709090c090603081e0a091809060908 60
    0x500240c180c460700d040142c0030400340120f800103464550307103000d18504589503c1105025040c14600014008042800e4400740110300020030076035280e815044003841000c02d2005c2c07410b085100200030031700c070642d00d0b0b4240c245c019000301015142181d0340207203000c0d6866070041042c0b0340c03040102841c100c1c202a402c21182644254a0b140000c0700c40e0070700d401a17403068155480b02a0f02541c44581159800c0304042c0b01200c560095000800010030400100001e043d8005000e620340f841d00c13000801c0c04c142c1d03800948194000c04800015150440760001641908803000f1900d104e444004a038148020000c41e010004200090b0f00000710a601c80440000d21034603041c1e008000d5020211a0300c420f4408003e15032040700104081a030650004640d10310842d64442900e5480c21f070a02540c0310354005644005001419255000d4540d00101900301e03291541400c100c08004054a0140e00b0720401c0c240f901c280300b00f146c1a01076648275845060b0f00c0241000f03420b410341012960b90f0080c50 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 588338102 1250 588336852 588336863
    0x70e012105040c0626100e0103110405100f0b031816050102010b01030908030a0203040c051f020714010c031202210a150503070320040f0c02101b03240b0403 69
    0x3801003244e80c4205005800040025200c4415510781e01580d004114000c100b1018081d0011b40130840e14a428845402180504031240810318804c0802007161000382041030010300b022800c00c200c41020a82204503004107440e60748960f107044040042c01806132003142c0703074000c07440d0001240701c6403005c04007500c4003a8000c10a50708040300540407601080780180c84a4000d100081c8030b06002c0d00110b91040c455088412140c0d90b80340403442210145500e00341070030022028081107941040420000d0040b0400701c13001c51521400030740081c100c480d01600700210074020300c1d0003184a030120303841514140d079100d000d02120544841951016602940c1c0242040d0103c00c0b0290060b41c42400d40303100030050100c1e50f10316554030404040250996041001e48002180103555503c2003184d480980720010890720100a40241445600c4805080c1c561805141e00858040c001c4181c40a070000e08000402c030039100e8001d002d0841c80344018090041801d03001c24081d00c1080074204507480381 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 588339352 1250 588338102 588338123
    0x8060a02030a020d06061715010c020d02040f0903080f071d04020d140c0403030201140601090513150e04020f030105040b0a110c0714090705070b0a021c05070203190e09070e01210504 80
    0xc82e00c2807000100d548d81400192507101c005c01600c5c0c501e9005602c0c2d8401000010003410341c045c81002d442803403070180c0205041404100c0ba5140f8a41c04c01e5002d03a40d03144c909860034940001c1c45c4820511140c8070f016039408a14a214580d40e58404001c10782540e8482e000c500c1c000703003c030403954810300049006508250064140c2485211241e009240507100c101441d810042800b40c00400682c0c285451510303043c102b00020514020440034003050401400285064010700020358092110702e8000d0f8035113410000130a40d040001c603000004148041400c2c8090010440300e406508805825806180d0340040c061001220003801140d098400316001e6588040c10f81b0309000791903000e4500d00c06100050020103140d801003608821102010030800520b18280c400c403a0100c5440c005644009200103000006e2038441040c0d000d070f80707041a944c03441480811141d410141c030810600c0180313a0324283e2a0300400308101d11103100e64050010b250f151142d8400b0b4841950300341d405c038410 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 588340602 1250 588339352 588339361
    0x306010c0b0a2901260402040c12020406030903030501050102061905060111060a020406110a0f15020417060405010501090902031005070302070b0403090f1a03070807030204050418020a0f08060a02030a020d060617 93
    0x5d40000d6008090350300d4581c0c0e03150740c0e00d409110181400015000412103045c10208590300a48068009400155000281c0014a1802a00300d41041e00810b041d540510700300500c4113000d000c00200340f2091000451580c6400c80140c680900007900550540110f8003001030100b0164050011a400740d6a40c0d8a819110104142c0b10301d00304401800c4042480306000220344010400c2680b4603401d6001440d0aa4418084419481500300c9030616040003040c441404406d006240c0074014844081180c00441d81c00aa40c8070ba009100080b503d440300001104140030ba4155a4086c0d0007400c8130280c0c0c5031502e0000c01d0145140641d0058006860380400d00d1000304000f444154181030345035141d621250300980f540070700204210300b0035808001c0821035450303900491190142d01c50030812002c03c5407041102d00c50b0a80c01941000107107103c200700c3d0880000d603a40d00f0000220006a60f61107441d0100301a208540428a11506100000655a903c50786480c4032903580041c01006848 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 588341852 1250 588340602 588340637
    0xf060c110d03050d0515180a0b0114070b04170c030403120212040608100f06021e01020f0406080403110d090303020105072d0201020408010e0a0c06050306010c0b0a2901 74
    0x1c010005000500706120529224840b41e0000350031040d0a034030800d0560180c070010744039041100314100c600d44c0e04424004041c8081c0507400b03240400b401d00c84d113059060707c4031046034000c0501c041c000358503202c0803400b4410101c01d0401c0404c44410070035550f50402c1e4440d60b803a4014842145e143c0030070711803001124400302d1301d03a03540c404d0700103601d1600345001c004590b0307a10090001041c20300c800d60000b5441c1011000c00700101099009080604402107501c07200580401808150341d00410007210070002039030896080d0f07049070814141c240c4503814111241003c4a9190219100e41802040c000341c10190503004c40c3c1c801c0e8000d221954940004a8030b400850340301c504e50041c0c011003190115042100544400d2041c4001820030f0b658501c1c150035a599030202601c55041041000c040c4a080d840b1040a040c050412500d54100003000900440b403000024000f0380c009000f045c000401900328040c3c0340c60b20280482ca0f1042110b00c0b42070002c800c0040e90129804040c041d5410b0b2 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 588343102 1250 588341852 588341869
    0x50a050d0605040606030b2b14030d0e07080706170f13050106030b062d10141614150c1b0303100f050a140f01091a0409110412020f0303040f060c11 65
    0x1c0748c00619500142035640b50701d0b40c00188208041e40d07000500414184003a140302c3c0401e20b40c000b000400000e031078045480c1c201551500007008105400c10445480c4880c3c50b05a1303004086102d1500c40c0d556802c0010000d00c460700c60040055081c5140041444450281140144d004940031a4215100c20022070b03080c01c0e200004402040c4911303d88843e00d03116800400c131507082e0400981c0951030320510b01c0305510409080e4180310801c0350000600910006400988603854020300da030456051800c03420f1013009107100c100140c0011180d400c40d00c81d0403c0100c01080d001226220b040481444481c1d001c10702600f000c50105000024882c83c01c20920700444406c14121740c40d03010800c00f401802c0b809480418140109407500103203502c112046401c840000202c2035450710b080c42c84000030f0328510080300768000c4051005000f450010035024810030790407103045000c1203013000880d00f140542c2d44904242e02000306d0000c1d8560308054180a40c80c46065810b03034521111040180b041d = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 588344352 1250 588343102 588343159
    0x7120314030118050606210906130308010312050405130b040b04020f071b030c0e0a0e01061a09040f052a040f060503090a051b120d050a050d0605040606030b 69
    0x125040d803915202c0f80c68550042c0e0b080390b4007800103483e0054030455280d0a12590442c0c82485d003095041100c0711344207010940e04111140b600c6002a045503d00078216501030201074502d0002010030f20645016000301d80050801800303442204184100e800001c020607540345010b54107003e520040c502d040d2080328400201c000c1030508210749034680e80f45403050107030811611002d012011012500d500d0301d0030020100b00440540d140750000d4400b040d40c0c04100981d410b0380c1411002d02c409040d03a1030b01e01400c0d0f40b15106030b49800d0160001800307003545540c8060b0082c601400d000a004101980982d0b0201e043c44e10a10b150440c0b0190340a0300c04d41c8550b1003c00300c070207020303c000c600c90002507400141c040c00b16402400181c80701420310100396008840300301c15604010300d44c2031013016420703080d500c1809000104140f180c081c040d8800c403a5564100400040d501c0824411644010040c10014000300011034a6070400790050505030750040c4142c2038078400800d00310941c241a9843c = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 588345602 1250 588344352 588344369
    0xa090f0b160c21090503030f0324090609040602070212010b0f120613020a03060e07031106130902090303041d0108060c0a090b0703050706020a03050f0a0b031b03010e071203140301 79
    0xe96140122040100c03400c4030400c4100041301100007015a41000a04001c510150701c040d66428911418604618805003d0180314001044500c03183e81e01c241007580520140d81c2e198895072140f6011000303120b0300030002c0d4050f01c0070b00150b120000541c005000864103803219011074404c1c03070402500301050298443c03a41d0051000400240380d800f5444003462010b82020b00c01c03600c0f0303030380d107400e40e54180320100c0107501440d0200700707000682d03100c500b01800c20f80303126242c40f00c3e1114030300410b4000d002c0c4005007500080c800520351000c0080707900500070b9000c901c0da602c0001d4201c01620100784910f82c9140304450100d1090904030084a070003207542d4544100b02481c003142403910ba00302080907000d0005c10b200035404541d160006084510b2596000910751030007481c44289060060f00c1c1c04c011500d40b102c58005610001680c4901d40e13900180300400e81c440ca00000c1c00340280c41c0483d40c1500070043e000442c0f0701c050701c03c285864807984420b41350f6014020174241c1ca00091003400078 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 588346852 1250 588345602 588345623
    0x207091820090403021501050d051518030403030519080f01150201090c1203031d12090418050f0706021b010c0c050a0f05030f0102210a090f0b160c 65
    0x34880907410355100d00000142601c03000341e18001a84282c1c110f81c2070340540c1100c4510541901d003106d203507014010881e0b03070602c09034050300d8450fa2203008042d100780126409000c2502c0f000352104030080101030308100c0765180e449160042c141c0c2c10032840c001c8a2101d401c003600e404da000341c008901c0748000b21200d0030160b00e0904440901b0340501000e03001e6560b2031a4010108048030849406095000010281050140340003400c544441d03858555403200f220191001810104800d1807041c1c01145150321980341e440000c00806813012903030052440b04541408100021401c07402070450503091b40c0c0415a40d00301070380c40e52040d0600070703010151060030712075540c0182e02100d041400749491303007500c0d0b440b40085030003020107410920000250000c03c00040c0380c00c10003950380101c018000c1d410308003c006c2d00c0c1c0d00320644406440c0d8105c80000004d6a00000b03030302035843c181d0002449003c3c0007041c1003000483c0b2058941c814203903a42c20b14141e103640280308d2035000c1a4020910407 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 588348102 1250 588346852 588346901
    0x506070f17030112110d120309060f0e0a0c14090105120a0f0c0f06020715051c0501092702010f1805090f1015020c010318060905010606020709 63
    0x414280c041141200d021000c011014949401000514060003e203680744842c0105400e10081c111801d0031442d02c00c0200003c0000040c2506503450140c0040e8200030a4600c074626010002d070102c1a00d44511516212940400d0a0005541d401f200d024000c1c010944d070300c640724035640301c40f002d0700240c2016039000100000d0806000103852010014103980901c5030380d6a45594841c0150f038140c607210350490f0140200c0c110200118000c0c080707400101480c501d0012000781e001c40d103926901c1400740100b04003424042d9a500752440680d940410040f568480700194010035603210441150070061483c1000604002900102d40d50141c4441c900c0c0314280b841116040c241c2d82610300c299050260024140c3c1390740c001d503070260000703091a0400b4a0550f81203100e5035059840540580803900085d10102c0d0003241850681d1800e10f07021982e071841042c88004911503e1000306000d25044029042c04010741c0240c051324425800d817140503940b500700d0b00c02c0e100089400e2111500030300205 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 588349352 1250 588348102 588348113
    0x210108030c150c1b0c0f040213030f0c15030c0905062a0118050303090c01090b031b160809040e1f050402030705060a080106141c0b0a0801020d0f060e01050607 70
    0x7a6800940c2803c0703030b031401640c04a026202c00f02480a08481d034814a1940c1d0301d40f40c07048564841c040d05880c1107040c010205105c20345280544009031a41065410b50000d02000d0701180002c1c1c040701911482644004600800501c144951038001030002840030a00f86011001ca58024046e802804011000341c0084000300300d6000c814095503517110381e400684d0003400d0034004118000c0024580300c1c64445841401c003050384003114100220400d082c40355408100560380c00c1851941c02e005402d0603580c3c411014842c45131251241030303280c4082d000b0002c0c00d50060022400c2554240701404424540300d540308600c020001c904000c8000084a011142c0c0c0300b142e100c0e0000f812240d02c0c0d50703100080f904075800b460b0780030001029000148800790b0860100100c605181758060f15050070070307901c4a0304900000404ca14184c5030024a60150f480d10414806006920000c5503501c0b003a41c8408010705503154003907006414144000b1361a80141c01007812034801500407490020300e035070307032 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 588350602 1250 588349352 588349393
    0x150306040e011e0c1805150a11070e01180b010503190f020f0c060108030a081302030f07080619090c030215160b01140904151e02210108030c 62
    0x40c801c25941c51540f45400711020b6140b0b814109444800110781140d0740780100011030302d80340c442c490307050034100f005680c40f01044521001e1b201900243c0b1032104410031a40240f806000c0f0800788154140402c41d108100e440e68101d80200d009444014600b10b075250648000e400c1040c040340c014000220ba0140e004580b40c1c070f000300200700150001541c1445822a04840075480070f41300081007a0801c808200a4170703014000f218002d5041c007030496402031484600034891084100311440007001c54404001c0f42100e9650141968801d50322900c1240c2d9452048031080c070140c075117a11440707036080103106c1c200e1003c1d0031050a0b00c15508640034010608042040c0540550302003010329012580c01c002c410900384940c2c00c080e0b080d40f5192601d582c80300034290040c03003000900244800101b803545070384680742141e440410a00c0d003a414000941080512645406000103450349200711155020f031101c021001d071412507641c880c3c6105582c0d0103804101549903010300c804052140103e80e0 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 588351852 1250 588350602 588350621
    0x607080c0318070f0302120307050c060f0405060c0607181409040320030c060f36160f0807030503041a071502120606190809030706061d0615030604 65
    0x5075400ba0b44051903103140303050030580c408048580d0f102c10600c11072500c1103010400c4d8084000860600103e512400c1d110b15000400501c183e0000401a82c004240710503500140340c020841501e038168a8221500d807070080b03031824000f45482c443c601d010400704035014160350346503109003c4031001038148082c0d000027404c03da0a00104100c0003480f6640817003010302c004400001b131511201c031040f880d403422a001e0b045800d94030307401c0108419801e640d140700c1160011040d400c2c0c415224a42010514401410612110b000c1c10382d4002e0381410020b001d9044800036514103d14541e22007041d40c407581da5000080c150303081008200a48503080045c0400c1030340205110f403410280350b9655454001c01d60002e02d4494000c600900c052180e5446580d005000341c4209181c100d00c051f00426044401c0d204400384440100440d030101c0041040d030310443d13032201040242c60744982c0070012456a000c8940c03103c81ba00c50000c0c10b98208910030f110b0b0b00c4401d400450a544452080201903c031281 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 588353102 1250 588351852 588351871
    0x110d050904020d0f05072d1e1202040b070213090b0402280608012102011e050405310b0603040b0c070c060908010f02090a063614030607080c03 63
    0x139402c052105132041c540500d91179110f0000220740d44000e44103292100e41c0700c48a4074060010040c0300394209203402d644030035040144142e510007400079070b906905010700c018141d02c04075003c00d84a003504010f2030f00c54005c584c844d181d102e400300f02509071200c00d04018032038040600413a0040c2800398503125415620003610b2046001d03440303e0810b900007540101c002906501c010405400c2507022960481440e440d11104007416800180500c02c15110002c2001011803414601c0c910a00545000d44401800e01e81048120310311940b120b51800920110807015804800302d050041c86002c0002e4005001d59003075540ea074560b9051044000c000403c0a10100802c40004814100c040c1c00343c40c8031b0b281c0c0862107040c6801642100c11102c1c9211101d80704011800c0c00f6079641c400d0001b12001840c05a0f115052060030901460603420003118203c0040b90041491200d0465102a140c1c8011440040080103007096a1680c0680300c180118a240d00860704d444c0100004541c00762002 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 588354352 1250 588353102 588353111
    0x61309080d0f0f0c020c010f080c0f03010801020705060f101203050705010507020109060506010f02100b040b060c0d030c050f07020d050f0a060e070501080405030f0306011b03050a110d050904020d 86
    0x99000d0095800401d9480b40243d40c88a050109207241d1046100400305440100f01000c252400a809084501c0c80c00741440b240800082801001d40222420080703581c5d8116100c1d6918001c842c042d404c0b80360100d0301c60180308000749000c03c203810900d114850306004d190742281740040c001c01d00a02213106a081042c20441d14010070802d0260034003c6400d580005039075217103030610310111000604070904001503601e04048990f40005d400b51000d40340d450002d03100c52a940090010102458100c0c0c0010f004500f07003280c0040400e110000c184a5142403100e54160502180e0501c13514480b41c0708580c05018250150902490700d1011501c113000f1100d12801502802d403078201b0380d11044030001e803030303410b141000a41801031000421003820580003506061740c8050712800340c0000819109404000201c13268802c00b140d0b0300307400440782106025200c0f4103000745254040040c0d240440c803550136411103e84001030305860002e46558035030a20404c8002c2101951100b0710342550107485 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 588355602 1250 588354352 588354367
    0x712090c030f110907050f0a080a06030b040305030901050901050c0a111e030c0c090609010621020a030212060a030804050114070203030a030c1b3210050612010506130908 75
    0x100142c024140c0d010704020240105204108410b40c8802840c0d0001c120f4203008007000502c080050b00c42c0140704d81041c1c11542e668407103180040050f6480034007100f030f4900500090503040381c000d501031881800213001541c0c503e8401802d880081e135003480340031810404015001e10882d0b441c0d44c038114030001c0d268608c81d1a01c11840e0108401032100c000c0c0c1001481040c0002e0801000303100344001d681002d0140750100c00500704842c14441c480c1880124154901c141144c1c1000e0090202280800c54862080a00080081d008801140c1d4428803900c0800c1c40d5261842c4048203c0e81e108281d5440c02e03040100440d0004881c0c0d00342c2d0100101400f40c100146c1d8180003400d09032202e030340c3c0082c9403007480d1703401040b0300000c484240c440c9032800c04e1140401c0805058070391141d02180b10744869810200002d03080b410710b20082c6818000c51940200447c4036420090082100719007842042c0310701030b103503422100305640c4540e005924613151030034030706650072005210740140781a5003003038038 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 588356852 1250 588355602 588355613
    0xf030f0f0312060f0513090b0c07080c0a2003151501090306181101110604110607060516020705060c060a0b060408030d06051806030604110a05030a0507090e060712090c03 75
    0x20603003211840340340110b02444681406c03a005d004a102c2d00030b09112800f2a03403100000700d10007600300c1c10060000140d910601c01b01104840d41800204211040440a41440c00841200c185842d842c0541400c03043e16614000600340164198903611400c940c5545081d104018812800e040c144000b0384400030109070144101e1007110900c1c60280540070a0340b504035251680340b40c520741840200d0080f09200700001907150b6009034042c0c0441190141007001030034038060040001d20790f5082c1001c00c100c52020300f0ba20740c040b000980884400d551502c040010354064404003120a500c0303c80050039105490300640030701c10025081510b41502c4800d054150b80c4803031300380003002e42c403048204102e040100c44a11041207260120140b8103003d00066141d12002d000a0000f0b18202c209260668502084200803e0003d08817010481c0320720304680c550040e445103001d22450a001421b038a1000b18180303204011950b528a000440134030007030014030748840c4c19904d803103980002200040 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 588358102 1250 588356852 588356861
    0x18120501020c0607030c0504030b0408090a03080d05070519030b06040b04080618120405010806040e07061d0f0108010b0307030609050a0f0e0d1d030c03010f05040b010f030f0f0312 79
    0x140558000359446680c803545070700c0d181000d00072070205490500886000344c2d00405a0b0190b991003101c0e64856151810484001c0c0610046141d101c1000b000010803c10084010000c0a40d030b240103000b2980c904d4410740b00b43c01800d00c60b00e000b940503414440f13040e1083d44200c0340602e00400090500d81c580490042e2608245c211a40e00d510030700600070940c582100743c50980001da4001d19041855181007a413070300a500c6010305009903070011642d2945d40d45c00c0007c1c5040c5400880311451341c0c4510041c01c1302d45151005d2656071900c1812002418801e01c0c013146050181c541c00f0b0540d1070440d88142552004045208041d075811000c50300784641d000c0c0034001c0c20581c001050b00b4440100640032500d8980301c4d180ca40d803284901148490b007044264900c000c002000182000d485004070703051100814680354154a0510b010301c031a031840c1d2105000f03034080e400d5129546e88415040441005500014112200d900070450002d648400c0f81e0b80c045d0b00c246842c42c9039491000aa0b403c0d00e = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 588359352 1250 588358102 588358139
    0x70201090809310c140a3c0f090e0f07051c02191205041203051504020d050f09071404050c070f05070305100b06070807020f0312070605010e04030e0118 67
    0x169299070b060503c0e5070b8441c6100816500740202c607454410700300006003d03040c1086011110044800c01d141e0087c1e80b0440950f08980320500c1c100d680200901c006140000711103003000440c401ca0710114001d6000c0c110107200b050a40d40d0030200d03031552002a28540c12880340c0c11440012000511561003060010f4801d00141d40901040460740c4603010b411081e09140811009140030100400b041b9403240e00700d001404e50a00041356140d040c14580f0240280e00d0f81d81c3c20900000781d003042191240e20580c03184051015442541d00c0701d420711504d552103072080c180424503941c0f110425140551041c1d4100283c405ea25161076910340c0e500391420460041556190031060b01002030103824484604203004034501000000f00000014646000c0c02002411a0b1008150030f02152101e00d12586200d400038111003c04c81c9140c051502e5912110040383c40c0c5052900010740b00e00d813040024000c2d6410f44854030f500f8080c2c1d004484130390242d456889600301c5242c001901c1180d2000ca2113a5 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 588360602 1250 588359352 588359449
    0x20d021923011403040f020f0118060801050a090b03120a05040e04080307120b010c03141219200405040b18090a0c1d06091504050a06030b070201090809 67
    0x35060744000b4140e8a01101d402294640400402000403202c0704106032099044039555815004100102d400d400e01040080c04400154030104000c1d80014003075040310012240740140c242ca440b015007d541040e90001d8250344680200801041100080c1213900d60920300b140c18503070744101c1042140300c1514207845120000080c4000b155202019840194074010140418182c06000a201d030b21040340140c204414010440280c2ca542421120044403030f40502005003401080803003070700c4490981c4d4031064940590080e8058140c8800100d00340c08141c20b5041c9458801844041d01181040b80d41c4184c0740c020801311a030080030114018101d0700c00078042c0c540c0350300c0d1411010341290046101550441c504181903018984030552010050714069038030b403268440c184280c42100c0641e80e020b07080908111218a03141e01002c1117038042c15190a10f502c0b400d80c141d089460303440d000b03041410100032205060504800d0000560031023181d008100319124420102044402402d110 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 588361852 1250 588360602 588360659
    0x2413050a0b01081608030d0b01051204210c0c050150040e040303021c0c0206060a0e0f01050f130f0209040506060f16020a0806071e0507020d0219 64
    0x34100100301e10f034008644215900b04c21800c291199640c0c0c01100d01502c0d00c2901e80f40c84250702e0b40320b0300c10307124003031901d0b403421406040503c3c040c00d07101a44d500c1c8100711030035204002c10003440380e207a102455401c04c407405550741c01e0400441c5c070250320740c0c1e1050078241c4402c0801d2004501456610350b5001d60302c840181014030504e00509400b01d509104410a800e0206000c6045c080d405e55401540c5400c0050f59644170084c564060341d08406040c0c00c2038541000c00130501d4010460921440c01100e10001d60fa441d40340400319000107540d645003103280c1e0401071045003020001d465000600074001141e9400042c4010309888440c940c8003842a000b00d14030109050600a107a0000b008490540c14100c2c40078100245000310203090604883e0501164203544a8450b240094414803098840910700701c5400f4201c000081c0ca03462525410195010b410752252007601e4980d41e004082ca01c0108194003000380c5281c80c400c2c0003103291000080010200c000d20030407034542c2c0481038000d4 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 588363102 1250 588361852 588361859
    0x708070e15031e0a090c210206160201080601170403140c2b0f050307080a0621021305010807030308040602040e090706080906040b13170c1e2413050a0b01 68
    0x8200362006450082c030941002c0c1e00c2400200f4031110003042e950309100c201c285107c10a036448840c0002c1d00040d401035000555000c2500c0240e0f0700041d050f00030307256214142c5580004482400100f14002e03600d01c808008280000c1c4518140c0c211040130303007151420541882c600c0e03070500a210440d040006c030001c907e813016009148100c0f50040d510f0401044c500c6521030040c0c85071100030320444c01c0003112000901d980070180d01c5000035041031b40303c05d101c0b4105c1030114074450007180000d034030130320b0084034880310840540600d50698020f030015040711890340e82c040c1d0708147d015004807801c4e40c0030301c0b01054102c54101803a100c1c003859401001c2482c0342c013002600c1d03524003601c500f41c150800810007000c43c0c83c50f0846170700604946206030840352181803a150311050280d06031565180013801c1c16018000084403031140d103002a0700e0011102c0c403e122079a40c005404030300c1d40d000035010541c004225202d0303200e03440382450101c220420210754400d82090201c480c21a00d9020030401071 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 588364352 1250 588363102 588363151
    0x151a0109080303070f0c03020a0c09091a0103170904061208130e0601052a0106031103160521120d0903031817090409020a0902030703050606030708070e1503 69
    0x40300404040c405103242d8144590300810300071800c0031200610610b1545201094400c118101589070456400c207030260700c420100c000340c1140340b0309850324161403004800703102201ca0303080d048942c070042c48009800d281d44044043d07000040410340c0160355460008204404c11810b5010701c1c0314800d9142c4c1d44c80016004040d00130150007031220310120704100601030b6007040803902e5907207500c554a092488030320300c51720700340030b03e040780e107285e9400c01000108000700d403c4072030150103045040d1081c40084000300c80003d0624402e0650244440b800c0e000c00c501090b250030aa4550306055518202c400e04441d40c0980c041c0c84058400c43ea940784440905500d4800c0740707003d021204888400002c0740d114401600e41000d04040c09030302c0000c41c1c140c0c6550365441040e80700e03405084191071503560704800009400032614000407a08080c00282c591421a0490384680d589440c2d040c000d03210040e0407144549101ca210390408182390b40540c0904000019520640400c1001c019015885030130 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 588365602 1250 588364352 588364367
    0x10f0c140301030b0f0c0d0f06060219030203070204180c08102d050a0b0d050a020301050105010516060c020a0f1b050a05031e10150f051f0507151a01 66
    0x501280c084203200520024103488145908010f005215280c140c6445140c001c1500c41d901c00210010300e001c030340300143c0640390018401c8540701d4007955100041c01040915802c00ba001c01401070f04104812001482c02c1ea001003141904e18400c6140d605032580d5a620400d540e80010403154000c1900084817003242c040c004011102136020440103180e4024180f010790b0b40020700703040545900000c2d204400c0740e444070a810f00c0041889400842c281400364442c40a40001d0b80030b5403c2c60b00210300c9500840480d900002e0b058246c000100712902c1c0d60004211021140c1b0442c001d40300320f00046020028a943c03021f000d16440031410402c100343c00b04014556000b5802280b01040400c0642c0d40810f51a000303107001c035002445000a0600702e030402d56800c180403a118603000000041e2504a00414140c0e82452108030b145a04d038002c05c40d25880801d074200e01c226078001d0740d8502034030940161113103606c1001c0c044000381c02004203005070b80321220030504440d0040c0b0342c000740d90391001e80b = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 588366852 1250 588365602 588365627
    0x71809050d051b0c01050403060c0e1e0405090c09160516030302090f010201060b1603020c030706211a0f04023718031b08031305040b06090d0320010f0c 67
    0x4107a40034644d000130f40030380154880500100c1d907449060250034016420f00340722190007080800140303000003c158509184820a6006501d064005049518005066800322000900012050f41d9584040380b840070609408030801c001030040400c000f05801c00c11a185110b81c40150301c440825003408200c0c2c2c58204c8803030441e81007010401a800c5180100e81e6907500400d0301c0c2a07143c001d0708080e45400308450800b0341501c501c000024110f9480000c00511035003401201c0c01c8581c03400c800c80240c42d0845401c0a0400365443d490320743c0c0c42e10342a80c0d48982d101038009401e000c030b852520000e0300c1e4611468052150308200e1445001499042e2412200c8642401440501c030420032002c0c2011a010040c8811a0000444a80b61048000c1d000900352034049a0ba24400f0103980c1c48408010311031036000d6410150402c060b494401c0542e0204a400340c4400c2c0505120784003210500268030320004005000701d950303024504207002e00c50722603420403004104085462401401c28410b0303030 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 588368102 1250 588366852 588366907
    0xa030f052e0f0902012001180b09011409030406120b09041101080c0f0f0a050f030a02070c1a190e04110702100309020d0803040515010e0612010608071809050d05 71
    0x882000040c1e82202a040e20401c6c409101e1340000c2064120a00429a0f1a1041c2d4884080c105680410910b61091071040312640c0091108001c081c3c001c2c140c0762002d449201c03040d0000d005c1404000c2c440c441204034941e03c0000810105a0400400d110041c280c800761814065200c13403543c01e58020902c0d50b0042e00e0452094603040b5403040d070700c01600400c203540b00451340c0090341c21404c900c507009a8648030b080c8100e081d42d90a03d8201c0200960060100b1160744010010000319030303507841c440c01680300315510882d1500210581c41c04001c5911f02d0810140000c00d541681161154810b1a0a900515001c1a907a0990f0b004000c1504d0200c2201d0b0205400c003403000340140c4581098150700c076409288140c03652118984a0308010070a00c900c01140100c00c0009070f6100041d4982d801800f0070b84038080e10440d00154036080e0340c907901941040e80e10220041110a40411241ca0201444000018001201e5480608010300e00800d400061004141030050300701e08059010001c80c1c0740e = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 588369352 1250 588368102 588368111
    0x70e090c030709080615060711030106120c0801061508090109120507060b040c0e01050304030c1b0501080f04030527040c081807050f04020901180603020c1006050a030f052e0f 77
    0x402509a034031190380b0201d40601f5021402c4020031895014107090200000d0092000a0321603140c50030002c5504026211030706000400500f0741c0041c07280703005a80c410803810981380612101070341c11a0015001c203070250358404c0b0010119007030045211204441d942d03020b6540442d8140b203070583e181580003d2165180c1082c100206801890103281e902e020b0800c0340e100e5841d400e055400320740e01c0b0b502030903030050010355001710080001c0303000544509803500a229120181d400b01c00e9a401c5500402081c81080703032039103080c00d9449214030303500000e2220544d84c0c03000d03011400380c603003140030000803d140da006e01c0aa9400100746061036000c02008012983c9800b0000d91202c81000b4064041c0e58001180072407070344551802c02a1490941d0b0000c0c065980380c60003002588959076070407080c02048407d0743c806140e8040d540c01c580005015022181c15511054811b130748060b400c0b07c4611483c5001500b60291090b100d1500c40e4404925203540582030b4600c090740c1c00c0801c11507801d480d0 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 588370602 1250 588369352 588369361
    0xf020d0b0906031011040803041d07050909041106071b050f3703140c0307170a080306041418070b0c0318040608150406180c0e070e090c0307090806 65
    0x18504c1c481c0440500200f102810070800007028440c80d00070f4041130000050200301e00f01035042c04000145040403000060ba80c040c41190103010307140b03455900c51424800304010071910000e01c10841c00080074a450200e666450040149594069072080100103d08000a2a00d0a09004110300c00e0301d6401c030401111a09006010301028a0b01540525003884080c041d807440281d000f03960f1090001d11030340504d18080f940d0b0686d07404041d10a114022010031501f102c4030104180580840c000c15503130b140c0e0f44d00e140071034000400d940d4105a60381e00300101d280c203d11091b8051401500250f00b4000400842e074100340c90ba8205071008041040001c01c0190000200d50381442140ca002c190304030410b0000700500499809641c05101d0a89140d1148a9100c50316000f58410182040f141c0405144008103135901c1b50050041c146444081110003003030b0141b15032045a41ca0842460701c982d00004803480d50607a19840015008001c11070310582000a45001e072100c0070013026117141 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 588371852 1250 588370602 588370609
    0xa0b0123011403130804270e10020313080301170607031a010c03020715170915040f11030105070903030e0a0e07050c010e01020309030a020d0f1d060d0f020d0b0906 72
    0x148045180401000000030b588458010703180581640c805c0d00d507075030389a980d01455054581203004050700c03070200c2017082448406e4481c2c04212107550025019083c1360010200c005c1d00001c022002d0f9001907420500040d51000045000c0c0030203408d5180900d0b82005600d140407030042001003814a1f11a460442c04554140001e5905003460543c07951101850202c3c105182c50703100d940c020000b605541c400541009500109980b03012204c0a02e544015007a0f9840304034103d58501304415002003004658400086004e080c041c40488200d2480d001c08603086a00c2110150009604441c080c01015409281804061402c641c40900142008032119011102a06110600c4000101c0e110080f0085d00403512441c1c2e00c0380215101d00d8003000d90b0361658400c410710001805404c841d5041140141e600504803103a5988210120035254040d45240501e0341100d640030000b4071a2044800960003142103e040d481c00158640c0b000d0b000110139107a200b40030134494049507040210310f85 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 588373102 1250 588371852 588371867
    0xe01090302040b01030b0405040c090c090312080718060807080a09020f100c0507140a2907020111010513060b030d021005040f021206011e0b03060f120a0b012301 71
    0x7901100d0028003500c0703803401a0000c180100300e440e000742c03c0030204000c1c08458a5400111941c8950601c0048103d00c42150010f54902005111007102803121643c0703031088085a078001e540f420042200000c804020b01d06224039032018001510400c00c0107615540142105d0300300d00791060901403502180d000540a4640b018098081c80c6030141c00002e0502c07609000c03065641200c1030703440fd26190041c0403038401c03020b042c4a01403400ca900c0041c0891001c4210712075148150100c08403101810154191070f401030000760304114080070b0010f1369007000e00c41ca40c020240300042d0510089546048400e5a002a18883c80307070308100d1826100c00c0d004540040351051041002070665200c0c5800b5091900460001e50071041d9032600c50003c0314005000382c182c400000d2200034001104032000800105406864040c0c2c1060001c41d0035420141c0b4905103180000380140c00f01c1c2c810918840c9071190190098450b0414000100003002500075000041525601d8054a40342030100190141 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 588374352 1250 588373102 588373109
    0x6170a0c09110a180902040b1206090403270905090d1202130302090c0f03090f011416050d060905100314030c0a080c0102040e130605150901120813240e0109 69
    0xd86070514139050440b24a0300190140803003c545450302c64100341d480c0e4006206c480100c42c0180702080f03041c80c1102d001d80c8215815580d0030603850290300c0c19010b2500c22022190413400045002c1101c0006d401001e202e054030400403d8081500c601c000c0a03040304185c81c00d000c0b8070400801c0c0c0e10107800c2c83c90405480c0c0669504000d9190111000118818002c61110800c804010310030032060103c2c1c5040c045001d1720090105480e256030785a41088e040d185030700054501a10b040daa01d000d82c015001e0b141c03009070005203459940300e030a81034030350031901c0c03090001c120f060900c104120034814024404407031001b50305003000700d4555550360030740c400007034043c0d08049400d03040c040e003d4044501030060f8000c981681c1c00d103802c81d0105080b8541040351528200000200200d10030411502100801000c000e5607900e0074920182e069044401541c1a010070420342c41d0345450580c904004015660740c10720340460080c51440c1d003e09441c2503004102950080944a03a401b15928065 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 588375602 1250 588374352 588374357
    0x7210e030d050a0210091101091a03060d050a15051909150e030f040b03010509090a0b220506090d020106150503011a0d0c030f1805030d090606170a0c09110a 69
    0x10b5450031a010382c1750550742e0126044e01403e03e003600b4100101e000d1204007040003a04c403020407036264160605042d0004403000340841c810f00019150380f5040902c8440b16010302c0c159075080c0080e8440413025031002c100790b0f20300d64507101405001c92641042c4154520048000c00134080e0711f6440390481c0703600042000103907858070350032400e03034800380101c2e6825200c0c0060710741c2c0c80d984c80e0842e40e405c4e0400d10595214a0741a400900c842c400850300306080c69001410042c181d590418405085050343d50801a01d40305014600008400f0804503001d640c50300010f28002454103070080c250703003554005190101561824200c15900202a00e0545002a0b491002401d0412a60203a4011002c006400b2800d180c903103090103400d60f101c00c0001b600f9200070b121003906000c481c840e50001200c0284141e10412034041d5206203035101d03a009500c2002c010074150343d81d0320741da40320300b007d54426a1681c004284003020040b81000707080041c0080c09050191008a5040314182d00441b09404103 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 588376852 1250 588375602 588375607
    0x607020a03060c09120b010905060d0519030908070e092b0e060f1204030207080105010f030b1506040324050114010f1e020d02060a09080f180607210e030d05 69
    0xc603180901100301c041d114069000d4000c445e607040c40c10003103100b8441c2e00515498000802c1d11803c00d08880c5076955003140050500e07000e400a40c1140d00200d60041e420003202e240041840c04c0c2c203102c490010725030040001c0c12824440501d505184002d090300d0b403680012045484071006280308102c0d10f0b8002c1c1000d010404e1428045800c038854000001500c90000804040d000980d90fa8507004a001c0d500300d03003510792030b0a00d01d0300700c17042030007a950071405a00c81080000c08880c1c03503aa10a8410780c851006000c08800314806400c180c00442d0816180ca2114040c0e1140e4000045810781c01c0805002ca9498001c524524540f4044840d0401001ca41030b244054042c00c1d80088070500c58030310741304940d01d003880252106d1012022400502860011804240443c05080304054020007458500a0543d031511840c1e0300c03a0b400040034002c10306215045540f4440a42034440c002c038180b081111b18038109940381d4000051f02400c0c0040619003103116100002c0210416407941800e95 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 588378102 1250 588376852 588376871
    0x50306060127230907050f090f0901090209090c032724070f020f0d0c1a0c0d0606020a0b070f02012a0e2407020f13050f060607020a0306 60
    0x85941000062690b0780c0c9009410000b455030304000905403000003001c0e18610021928100420540c080d5500300c0014820301000c0301c507001b5200180031300d0b03000031b210030502840907011444040090380a00d0b01c890b40400c407070800d4145818030560264031244014034500c2d00300b03112404507044262111135419158041000301108001c415110140c6c000d0902c0c2d5403103601103c1c46141000c841100004031200e1031225000c2c0005a04014400080041c02d81c542c240c5904841020011000781d9070041ca000442400c010810041ea024082e45035505903508804080358050b00c1062380f0140171507000d132907a00c000c5002078064682106541c50300001d0400341203802c074094007080031141904041c0310800b131074140a010b4030b8094400181c0f140401c8224950420540003180440310825010103190b201c0e003030251b50024018184000c5c900c402d4034a248020034140140c6440100205e603275803041c42105603610f440940d101000301d60003031801380683e000c0350211909100040c01c85032a080220b = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 588379352 1250 588378102 588378137
    0x302070b07021305040f350c07030804090504120c05030904050903091003020d0f06060203031303031e0c032403020618060c0a060b0105091f0c0503040602010608070f0503060601 78
    0xf20680c0c83e80c103080c0400c0c2094144030580c9000e8903005c0b030b542c1c080001a10071000088407e41000743c0c850b19000301c0e0b41c8048005000a502c56184400c540c040d500c00800040e8044024101624010800003068034061800c2505410051400c1d030a0144543c250000518000b04540a60800303440205440d00c881841c2441e5018038880581e2141460900d445400c0d8558050142490350b950b05028444c14101d0040c11503c450044c0c0c8010b0300100300040303c03001c0110400f600d841c481e00d000100c041840c40c01e003114206075074171f41c03010300e403105071504c905645805a1954480c00501d01248050150341c1841201621b00c0300a00905010940b41c410110044540384404005442d0315914000880500d850741281d0008403080c520b4021800391552003141611070303048014280245030f1035845010b000c1500401c8007030702045022070000700000c500b44046e00042c01590000b02d0319070700789038800e8140a0740b0782006103441c006020400c081d9800240050b0800c20a0810f5040e0180c8100d51 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 588380602 1250 588379352 588379369
    0x60f010e0c072f0406170604080703020309150d0f0b10030b120303040f0c0f1202061b0f0105180303060604060e0d060603150606050315150408011103010602010b0d0302070b0702 78
    0x40c00070014000851800310710b1486a501ca41c03d0803601045200c0d20b916170703940f203580019007450042c1d0040340050002550351001700703070182c00313401113a040c01c001e06e0015000030390307001085480d01008142d105403400c0d140580409405102014090045043d011800d0001e9040f84941019101c20500605803100c0400c100e0b00d081200959a0f24506418192803c2450b824111182c5400400014907445ea001c81541540c0e0f0210b034515080b481c0d9020404560000010458074194900440c00c00f01c00c100201c10318400c0e0003002140a1a204500ba03400740201014030f102d0744c00c100100603550303441c20121420b48804d4206003c41500007800300701d85a040000040008d841c004021082c030507031549044c8103a1a1810500c61503840c4ca0085541c0c2c0410b076881d03100918502015001c2c0e2518100304000101d180c20301c68102661030035041d0a4800e0610310884400c0c00000501c0010340c2070140c681c20030820f8600d04c003485011380d0025600d000900c1031940d88000494410115034a0b10807 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 588381852 1250 588380602 588380633
    0xc0f1e09080106171501031203020d1107050a050f2b021f09060506010c0f060e0c1908070608100e091c0e10180b0d090c06020f060f010e0c07 62
    0x708440c0d500c59030884000402d04c90b1240f4144140040c2c50b20300e48802c03001c617050f2580000504044410860164082c0d00003900c1d15420580b03c4e2407207485000c8090103046043d0140c00100000c1490342045070605480d510050ba1540083d58412642c2c5149810b141c6002c60b81f050b0b05460210f4148101c1c1410440100b00050031001c00d006851001c00ba00138502c4280500c00401c40d40d26810015100c846000390b00820059008080c0c0000c100d4039840030041c010300e0f20503030303600039241d00001d01001c0a5030102582c010400300c040c84800000c101c1d090181c01e49081c80301190038440360080d03985425101f55510000c558000841701c0a05010f0401901c07801c54000c2c042c0980070202134051000706c80c0e800d0207180c0746203080c1c0310340e8812120500c0361a864030900d00b019080c11104000c9500481c0c544e05500d407035100035000118204007401c024045640034281184080003202c0c181800907044501c0c040e2448014400e441c40c01d0f0016801c9a080407040b07a840d5618640903c52015100 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 588383102 1250 588381852 588381869
    0x31b0310080a0f030206070305010621060302060a0c0b10060206180f0303010b0304120207050a05150405061605100b060a080403020f06090601080118050a03081009020307030b040c0f1e09 82
    0x20003420030801a401c0000f1814401d03001e45d000c0f0750300c0e14021030850300248690000515201280d4401c1c000b01075540140d020451008650300713480745c010407041d9002801020004401030019400e00c1000420641c018401f240480503040c0b8000f0001d40e540000303000000102c401c20308540c0408001c20184ca0b00c0c04030081602c1e16507a6031131182615810854040d10381c031400812000d200c510200c0c095059640c000c0910f118075003008117104100c07071038800307a0b50713407000c00c10000c910355079400c014040a403914001155642560300d2b001d4140000882500c0c04c6034205400003906644070800c1d101d82030414600000c0540d5903040891400b240401c150101c1e02420060004139940412003906030340010000307008120a41d114441c03107242c003c40c0a0215000000000000307446220040d401c0204074190120300c54881001c3e034101e90054840e100400d548060f54055401c0074010000c54007080e050002d80e050039024058005240360250112041140c52003010450046104c00082c18400 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 588384352 1250 588383102 588383113
    0x60f0c02030c2704062313060e03090d2006070b1b090405070809190503120a200304291302031015140d1502070309050409050607030b06031b031008 65
    0x1805c15400402c42e0700a00e0f010022020500b04207031001b0325525000e01014000300201c032510fa1607040050003512007100c4140000c0116603402c0d0740d100300702e80000d4000c11441c251509504500c6074248101011f50303001d41e80038000b01000c40c9281c002d055003c48461024001b21404000104d0a48a140d114641c0945010140000d540c2e1115006225894071021140e980d0781c0c405035040e90255166006000382d004101020300c02010343c070703c640c10580820010070f081e4402001001c00100008030121303500d402008200500c0b0b00c0d102500c1240b100c00c0440855200500c0204c003902d00700804a0f00c0000340614144115102000411807684807903c040100320b410502003512141c03140301c1c044941d800010304500b6882c0480414443d141d2201c003210010100c4d207240c2c40070750090501507081c411b61210002d501d8940c2d00030103006600c00c038007400051600010207000c4699a424040c0202c0b400d03c200090f440c00000f404402e0035800030707190345076a5138030b8003c5000b01c8190001c06050080 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 588385602 1250 588384352 588384361
    0x30b04021b01050f0105131a090f070306290a171003030e03030c03071b1206020306010305070e01021216050115060f030213050d03022401060f0c02030c27 68
    0x990380c141c45094208000303000a4440c58500b580f050700a02400d035114010780c8091403010420f5000c4d40f03e00410809560004a81800081a884040b01c5e01c2c00030b0004c0c201000b10071a030505c82ca0000d00501c45480f070b01924140c8a4603040c003881c2c29285440000060b155030f0241c00340081501550380c032040d0008602e00200340d45029090382c80b0440104004c08001c1c607007441e02005582c2c0c1d40300d0400c0294140186a21b64072001c0040c010000d0303030703120003031404600900314a000307049241c015003015999040910004040b1103000346030108100500c94403c9003030380c4c0860811f00c0c02c500c61404a0b100c5206902e1000c90110624009205618000b048051422034050b0b18048484984814040000c01c0d5030a80a911404003090701810781c0820034425481c001d40b0b01c50685000c2e10440b6010121508894030001010f00e50701d15140100004024240d48201c0003441e003c01440d140300e000c8a20360101e0766a400c030200040c8500c0000c1c1c03103002c119680c80744908522050160084480c02e0 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 588386852 1250 588385602 588385627
    0x506071b0f060f0201020313060c0c06050703090b06090f07180f090f1107051513120801180e03030a0b040207150f060504090503160203010b0a06090504062112030b0402 74
    0x4a6100c0d04010805051003c54842d00620a03644100414000101a0708540d81c40d1801825041c02d1001802400004c00340490f51078810a80700320703400d45000419801a007803043c40b0040040416101d0130485082041040019602c1034020b01e0500340031003011120400707a42c000c4901d400c070040002034a000042e404007641c11058645001c06420440914240600d00151290b01e07030141c5158803000c5201d1540c0791140000d80d1002c1804030301000340d091550703205010100d020031540021241b000622270101e54483da070860500f860340402c4200f0003102c5039900c9001c02060340070b249940764480341160305d441e012100100e6020070f4003c012118118050002e103084004103e08502d000300100c0d1a041a100382d00600350000000c50034002613400100d504442d00038101d800d03540300c2c01941c0503520b4142e4800003400d156203580d01003504100c144403c07941a90f100300e8500481260904c0d2010301d841b1220740140c3c100d281c41420f4030f9000300035000b412600402607000340c40054103240406 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 588388102 1250 588386852 588386879
    0xc0f0d09020120031803030906040b1e040b0703080a05062b05152a1c0b03061302190f061103190c0302300c0a060203010602030927010506071b 63
    0xe00c04003505002c211041c03d05589010f8000c08c039401c258200400d004d0341e804240541079840646045417180b2890801100b015006948564100d0f48080b0b2404109904145170562090100c94100413600d400b0000bc1e5900340d4242b090341e11003042003494500e83d000b0ba1001c072880c980080444100402c0e0035000b01100c042200c4070500109000c0301c0e600f1800340d000000c140482002c0509003410b65807524500910034210051104603910042003809883c103000f484d2041140d190a000201400d0051281c5424429045019003a0383c01c402c2c0092074400d0040c07800e54016140c400003a01c0c4c1d000c0c1e0710785140b1035000382031208240380c0c503003c80b40741d440380003220042d1290b420b03103403a410152046038030f0450b21154401e8582d07009818408000922003c2c283e2403020708211078402e011611284100d90003038000c1d41c016000010914418201410071072003040c1c0000140c0504418025803400301141070054138401c0e400000d20b1002c0c015011004411901f0480110000035643e480c82100784 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 588389352 1250 588388102 588388117
    0xb04021902210301050a170109050a0302010507020709150308091c0506010302130903020618070e0c030103060b030d0509040f06330e1c0606030804090509060c0f0d0902012003 77
    0x900790005000369400b8030205490484001611240d405400c1100480044501500704074407590390b20b0311340300800c008100150b40e01b4084d800000745810054802401e0058a4225503c0d0b1400d00301801c030506070180c000e2007140e40101105485013810070000e129000e0b15901d695240c038400c00640b0038440c1c0030804504076072080341c10340825140e8404c403000381c908000d80134015801582c0003501191000600c0e44c4294481815101c11948400825103c1f0f00141c0d0880307075120002c40103004001c0e06201c0c2c0c007852101140107111380003813100c005000e4410034210b070340a01d0b00c4140c42108001c00307030020800703003a009030750343e007031030800340c55000031140391300a580100c1190b400c1001d05500442c4520b0a210005d080548040e5405900844c50710540340100c5000b0740d0f600780000481c1c8080041d10144c084d080010941d4102004031038540180589954201071040200c40c0c0e01450160444821552450001c0b4020b000ca0005079100d01c881d100004209440850f0185071030004402880715 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 588390602 1250 588389352 588389383
    0x5041212211e0b1003090302070512030d060602070b03010b130f0b21011409041505240a060504051c05070b0c07080c01050922021c0c170105040b04021902 68
    0x140c0407400c00b484143d452050640303030010003c255040119202e500001c185501034011078014659510105802150211210955800124400d036003850a0b00410009000b544006d00f1880d052203001c0c0101d21062191081000c4000782603003c96440103019001801c460080502d4156620440c0310107a0004c1c080007540002011003c6803c06180c1420381610b01038220310202c1d013907a6051043d82080a003046d0f4603400101140038130781d0180d000380e5100e101d0754070405d080c8a8031a40204d00c0f041c8012400c030301c609407000d070038401c10b580981603d00300c0d40229000021014091100d89403161008000352141c084c4900220308800154003c182c191184412180401d540c3e119103601c400840908600240080200c55524600511041e000040e0042002440700529880600726030000c041000c00002c040c00845038041c2501ca11040c2c070115081c200002d080c003000c9000007075414001d01c0d210310b54544043c1c5094580d50f055a00c00c03611900c0240081c0b50308100130b5512460702d200c0701e60 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 588391852 1250 588390602 588390641
    0x70203062a0a030c2007150e130606020f01020f090103020a0302090a23030f070e09031207022a0f04020f070501021b06060109060e09040218070903120504121221 71
    0x800a200f00143c2115003165000c2c1201c58281402c01f00554002e42c4400104070700341040d40c089131365100302a2084413842d640060042e00e090341c0681001c41c05039448080b64418000c04000d581c1c42c0e822100b034020240f80050361381721014020340c028003039000101c1e005524108041441c942201d998910217843c030074901d080000f003008060742c80c0b204030b0450440d0381000d1800c000085440355825000310140d0260f0b41040400800040232940880706071006901801040790821400741d103800d5a240103100c143ca0b2420f2180210300064003d41545010350b50001c0c103880316000302010b4a000681c000002c1d5525118540141c003a58403554200c0c110340140e00c08102d066005040b140d08072081a1223812040c0344410405c11002401031003607030000c0d000b9905c0d81b400c0c000c070310315544034040c0744e01c50800310350842c10070002c20440f2290074030074450704101c2030240320300704030605843e00d0b17000c8414200c012022408507562001103900840005c000520700909400e80d800c0102c03000755120300c080 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 588393102 1250 588391852 588391877
    0x207140604080a0605040f0f031e0903030206061009080d0c050c22150b0c1e010b0a0504050a0b0d0807060c050405090414070e160305010803070203062a0a030c 70
    0x114a10551080602c82c0d4412244080000c0003038020726030007401a0b034646609800761f12042e8a40620704404c50005140703442024905400340c0d9207450401d558074101070741d42c0c02d40d1350107582e448025000910455054550190300c0384104160400b038000f000540f03040c5e01402402070b00104a00004450340c1c0114680100c0c00e041001000c8209280c50500900c9030b4024412440100030565400700701d24059900401c4190f014401895480400d04c0104086044552005010720340c002c8008200d074100000380803103644003500002a96030441e000603954a40d00440700041c540c00308159001102c03281d0325814083c1c00405050928003a1209218031117a0701070844061089001d00399008030b0341c0001c0f40108590f4000e990103200800119802c05440365500401100c0440d000e84c42c0785502001c1d1406103030306014180c0189041c000840c248507055000030b48030000104a116400011000031007241048041f82556800f01032080d541e800000f40b008000d040c0c0d000080c408103003402610f0 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 588394352 1250 588393102 588393109
    0x8010b0a0b07050c010c14030a05040302180601140f0d090506091002030702031b0a150209150403050a0308130f0606090e0d200127140604050d0e150a020714 69
    0x1950315581c000003504c080404130340152010140e407081070f51500c100124844104100300002c101d001240c3e11000d41700c0d4a18810042d400380c51420324a00c0483c9607040c41640d903000b407035203a070300442045001d89036000003401c0312842c080d0324000c120190070b009464080c004003041442c00b83c013030142510300141000c9050816407106031055001039000704406844556024130701109004190b003900d0320315002d62141c8a030b01e40711903820700e4160307070001d00036a192030904d41d5800400c981d0070160b4105495a00c41035229002c215003d014001241c3c0002c4d1411208040d0b11910707035004000349900a060b0030030700c00030701c61401401d1025141205140141c0300019070018407000b183d4403960f2030940e9101e8504080185071244074599215240c01c890b80541040d40b45000310104003d0282010904020b262805c0210300c4907060707000102440b020070000306050040940504018040b1007a080110b100180c1d0700a038240350385404039140440341d40c080b07404004c031003d00d01c80440218146040 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 588395602 1250 588394352 588394357
    0x108070c0f03050a05043623060406180f06120206030610050c03071a010b0f03040b090a0f0f0c0e13060e030f0f030f0a06050d0201050309010e030408010b0a0b 70
    0x103800118840c0310072002030f1060b0000d1004410525046040641d5a10305506a80d000d2a54424030b0710b58010011200d04114400100d2641216080c019403441030032103d0307411190303447d030700c680760502001412075140d68004200030000000500ca01d401c0003440c490003040c0034841c940e40142495070010300283c040401c00320140d0010025480c6440360001c2040c8607020346000d1050040502510b50a00c80600180001c5402074500880c8144000808a01100143c104400c4000103110700358407c0d07900b0003900e41c400c0c0d0080340001d07d034842d044014901252001d0003400c140464900c0020011164000d9040d42e125107074030f40c40241c907a404580d10300c0c0d003168400ca10410215494010518503004410a081d082060b00c1c50050711031071903c070365400380c800d070010080000203100004405016141d804800002c00f0440d482c18840003840c0c40000690190401102001080c44c04200394030099580c0314400440355925914078406001c1c0c031505d440c4900c03c440003c400200c10300c20504 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 588396852 1250 588395602 588395627
    0x10303170c0f09190b041818170c030406030204090c0807020c0613030b042609030712151a03070b0f031b0408030a05090906030102190e0103020f07080405010807 71
    0xa103040c01c81282c0c80e6034640d0030401d503541d4041410070405a1000c501c43c1c443c4003412604001e0765840d8140140000762420032003034440310714500b510502d45000065040c1101c90350010854264204034918646640510380103c8124000007800060701d42d00740e4024000c80e68040301c00c0c8200c04200e00d054a550300c080b80c0890258228030201003042c80c04400404484074071f0040055040d4076a00c0b4030fa44200c0499044500c911003011603020310024040110300403120500f400d141a020001103501e403c07592041401e0f050b5900040401c0100c0f801c004403103802e840390100404401000c110502280f0700d802940039024420020990031940c0e01180c140e1035007400b0051941d1106248240c0003001c140d00b003610141d0921000c0740c44a0240f00501404131544d4440d61505010000c1000140019107218802d030710401c01c415480340c00800f10003600c1100d01781240320b5441c400c0144c010307101e00d1000c0039440e100000ca00d0308011103803002d842aa4020381c2d0b08009640c40b4481030b280c2401108 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 588398102 1250 588396852 588396871
    0x906060806122a03031606020a03270b280b040509010b060f03093a09083406050c0c010824030a02040203040308040521120919030801030317 62
    0x66a096880c0c2181c0e2160703e404101504503807901c0145020580d1040016604a403c02e0300010043c0c04141d15004100c40c4040c03034004d002070554103601000c402c6035522001056601e100000503c14100210741e1459002984000214080c000200c94000c00d4805001c5205074508000b242c0c80c100144140c503500180500725510b000c0d040051500140c00003046c5406501c5940140e4503444c450620740295a81a510184249100340481420080e6850041c90420641d140200700c4d083c0c1c00111005996101c00416554443c481c8800b0405005622001341d2801c214500181540d407180042598032448415035015107408401180d8070318041c0c0c1c0540c940744641c0707680440f0381440300f40f032100048000d04960380c12900b5030209007a41c004640c2a804100780030100070070300c41d0902411001140c016240522819042c1039281c243c02034804c0d440400602c4000142441020010076070018002011003200030460724008014110902003180000c40c0c1c0c0c00448032003501110114003071074410 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 588399352 1250 588398102 588398143
    0x115080616050c100209040f110d140402090a0f140106090810020a05121e040f02010323010603180c0902190306050307120f140d030c050304020d120207090606080612 73
    0x10402013010750809411141d12a942d80d13013841c18130560b4411155007264004040d5110402502044100c95102c940c03013102030070b002d00b00710059a800d41302d40d900800034400003c0b005000c10b500002414604480384090341000b00214141d03403c04140404c0303c40800458807a0080da02c4840c01f07a0041b54041c10104001b030045a4030904c0040001d544041c40a050f4001d4508096111420420549090b1340041244152900f07550b80b50140916514005922440c1789040d44000126043d0510541d4200f40e0b8a10200390510b0741c1c0d90b018601c1540000009200786d8031681d07001c0003540002c4000219041503000800228002c2c0101c00031528000d01605000785014410003001d100c4c843c0c1101c1c015012200000000c40d4100c0b402c1c0c982114000911103841941400340071183c0c10303050701301403240c140104030041c0d4038225000d403050f5100c40200e03001808250180d14024481c1c001c09c003c0ea05281c1c0c0850081d92220a0710b00c150811a11081207402d080344164881c3d01200d003200c5a464007 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 588400602 1250 588399352 588399373
    0x3081006021f0e0f030d0b0a1e05040b0f0d060b1908060c0f07050a060b030610120f03110d02010c020d080c030f0619060206180303090d08090115080616050c 69
    0x2c0d51000015003150383c01c0c3c5950100e00d07183c10b030075a40940b40c02d84000e5510b043d886814105072444002601840d408950004442c0541740307521212889403500c45c07912440040c8413615520600e0402c0340001d45400c140d40c54514091000d824004640d80c05240d440d2100c0f4002840d403015081159618409482c081d262807446440d11707400728154884070942040030400051041202c1c0d05220300030712001842b0030000c6d04050800c4006492006d40c08042c84082c008502c0302680c111556034802e80280e0307411001e16013910900c410349021003a0340500a07010a0450701900940d000d10b81550a440c0e0030300d985c00b03007a00c030b18070155012003102030207000145405207100c0455030403140061180400c1c0c00900c6510708141001d401800068207c1c0f41440160350151101d8240450308901031400c510301049104c3d99501d406108a08000034203020840e003035400c1d801300c00c0ca81300c513941c501c0b9880d40707800c800e43d55140151502c146411a030103840c0071451240080d610f03100d03940d0b0007500c5000745 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 588401852 1250 588400602 588400663
    0x10051902011b031a0a0503100b030c060301030f05062404091a01060302131203210f0c09030311011a0d150f0506100f090501110a0b040308100602 64
    0x1402424041503650340d2520099052200d44180b0480001c0e40d80403619820640400380441c445001072030003508207800502060b035000c540d240c550b50306d401c1c00140e45c0d1041c10010f0b00d8400241c01d043d40000002001005001502d41c241d6112401201181c0703143d1a80c0d4060038403403e44900c00c0301000b03460281e000541c90b1503005840124003034240d1540c0f0b8600d0242c0c1e5184500280d100001007513001070740da00c20380103083c4c0d0a402014407000b50411b01c0030075100503010400214100b504100508000180c0810355449003003140030345d9504000715102180301400b80c042074042940800c030300107544c0b040640d0501454948184200d43c04441c0c0c41503405210760008503c078220b405000107902808201400e115a00f07458407050008200c0d4107208060056400f050300c20700c0100111158102001030f0801d07500f208a174801e28101c1440c0180034005400e05400d800014000361910003484107142e0301036050350040054000e40081b09549400c103a0740c0f000000c211400c0c460304900440f48030320 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 588403102 1250 588401852 588401887
    0x42f0a1106010b1911060f0702070803041a0f070606030602040303030b0405040203100c0e060d141e19090515010e1003020306040609050a12090617060913030e0a030f060b1005 77
    0x162a00305401917151000c080b078100034088a5190314820710a0400c0001a4100b05000041601303070055441c040c00c142a08800c01e0700285142c11500000800c00c03583c628110854681d5038110f9002c000d00ca0b00c900d060780181d4414881507002a003440f91702c0f082707407070b152040c0b6005660040080040c5044883c0803009081c41c95268018030101c00e0a08140c1c0d110b0b80014800600252000290f801550740d002d9070b00c000141003050b0311038800c035400b10042419161a504066000001c0c90300554004108015000c0548000c01c0341c01480303007540c0000b079203103c114140e840c1503601c10138030f940d0212090346a581510020390325a0042c008280800c529500c42c00750107000f6030560344460754940313594503c01d1501d55100005002c0060402485902a1120503005c0c1c1a5480d5666401d0280000711440340240c2050030510409040004142c091074001460032005840003101965030304203580d00c81e4240d48144c4086003001c050881503e4206201e1b0743c48881911210b003000001154001280d = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 588404352 1250 588403102 588403147
    0x21c0c0f030f0b042a0c080304170d0603080901021b0d06110f03040f06140411060901090806150301060f03080307050304061e05071d010905042f0a1106010b 69
    0x950f9a41c000702c420b42c0340c5000d0303000074845043c0740c01620140980c03900b88081c14000c0031000c02042030403550000c3d00d10070480b608160041007000551210084c505214072a5210203041180f42c40000420000400c000d0250280d09809a4580f4604d00d00003049211000c480e650303011201e030f02402d000414a41c8542080102600e8050600d81a010ac01c0c410782c0c003d84066801c0c00e1003412420400109000c0c4200031000c0c45910801d5040a035505501500129215403103180085813426859209000800082007101e00f02c4001e8101800c034860ba942541040314000e50070101c002c00d011882c801018101c0e0b82c072411440c80c60303491107003c4419400190085944c10344940c885200b40c0c0311001d24640c002c5001170b000581e81030003000034040c0101384a42d00110241d4102c5130b1841d0f031f04a045c2200306c480565002c26807400c00d40840e10b070850300301d00b01e45070661200d030303004d1101c0621009005070460710340380c1e07d0f4091084c0100c1a580c00c024401c1c1c0344a441c0810190101d40b183e540c080510 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 588405602 1250 588404352 588404381
    0x601060207060f110d02060103022b03110109020d061d0601030804090b01170406060501030e0d090509062701061403160309080705011e060f080303041b05030d03021c0c0f03 76
    0x142c10400071054108110305d001800140d20900051080d403509400c7c20102524262445100c1745001d0700304424400e007103e02509010f008080c06081e80310a4016112142d402000c00700505468549940240000605400000d05694421000703a2000900505898011564030b0510307141c590460040c028a915050406c40c0050b07d0000700c6c4102442a030165118540c003080b06800e090005080740c000011707460071648006130f803100c450b400403c0e400c292001036440c100e00d6658070740461100034808003102084c1011000307100200222425141c1030324145e81d900e500162140307080e01d405000036142250645140d58403030008a020758400c2c0040b074441d003107090900c00e868595500b11060312100c1b6500f45045a20003007420010b1058034054032194114502c6682800500d80d624000141300502100c2e00d880045d200c0101d86c054240205001001c0701e00071010110014040d4004200421440002160588040c1014090000d440b43d543e0782e1000362a409442c120050450442c45404 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 588406852 1250 588405602 588405617
    0x6100803070f200a06050913020405010e01080403030b0a080c040c05030601320c011b1e030207050708071511190201080a0f0f09021203040b070818090403200601060207060f 76
    0xf020345403515078000404080d00c070746844180500a005942c0704503008035040c10b104220074000350380c03c403041d81d84881003840c01c048166100c1c42c06038000c2101400403a4440c02501d8001101384000480c8900f0304001c1d9014408001841d0041e2602c0c002036600e18040342016804078000e6801d910083e001000c0e0b540c281101c1c409071100b03004903070310104114480e0394440c221004515000003c02900411900c0c190200c1c205030440c5c554182c00200702007081680000702c103c1840130030030402c005096100181c0d00c1150392642c07500f044107031030090540440c5820034000344410011172250b49011414619202c19041c690044422000c010300070041103580d44007194422359288960711400700d0406000614801c107004018900150fa041c002c00ea5000300130900880f244401170700c1c5e559602481c0079440300d000038404d401c0207003d14a42034200745000100f00625502c004a2010210010810307440113145d50203080d25150309010f01005039101c1501080824804d4056060320200f5160128 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 588408102 1250 588406852 588406913
    0x420070503070b01030b06010206180709021317010207020a0801090c0b16060e070f1a0405060901090806130b0606072406030f0b0702011103040f02010c03140c06100803070f 76
    0x100941003c1c0c201b9102d400c124800c01c4680e50701042201d40041100c2980350155802c618815541c07882c5000301c0729115000b080d41400c40804c0d0030442c000c0c103091700658199044440c1c1143c000d40110a090f48502c51884d0b001803041c0061144c0c0c6281a08180f1162580c1c0c00c1450512a40d4440e01c8000300402210010201040061250407026072845010786640c500d8001c0d100044a490341100088401031100c25000000100864080f20410340d605526900a0801607800c501e03560f0201107180100c40800c03000c144000d0406103c28842c8580f01c01da91558810321465001d14400144040b03500749140010190039484001c40c030000450110318036840e80e4a82c00c03c0594000c045400c1c622120a018800c0c0d020701131140e13022504104941180703084d84603080c003441c0d090000f80c18080c40303481301424144180c24405104662005455a036800d840c662903441d4001c541107e41a0001100441c0510340801203509140d080080801451415120300384580084e4109002e0070401c0e0b5481e0 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 588409352 1250 588408102 588408113
    0x1031805060a091101050a08011404020f04080a030207150f0c11130e010f05130b09030f0304120e0a1a03060d210314010608040b06040e031b0c042007050307 69
    0x940c440c00149002146142062620141c40c40300344c1011030621005102014010358868221030440c1d455a2800c3e4021220002060003032003040750700c1e0644e500004010034404c9002810349040c511927801c41c0c1c089984d40359102401d000d030303da0010000355142040e82900344100700f241889400703611030006900c0648000b0314201c12952360345441944618032100340c4203080c401d8051144a001003488680303040720307441d0100d42ca4054001d055a0b6500c0214812150410a0f2021510700881c41a940e0409081c08030100c40c202642000146242c4500441420110203800c1100e00f088800101e401944140115503000104086e402074180f00081c008075200c0b5206043e00600800707c482d00035100745009060301e020380381401e540228040100250782e840b5051650107900405240c2054962000090103402156460313603540c400442c2c000601c00029503800b40d4001d61030101d035901c14007031082c042580d070340c82e00c41004010003001c1180386006810081c50054490010b4902e01041d56846 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 588410602 1250 588409352 588409363
    0xa080a0f1802010e0904020d08031003021905040c0914060717130e07092105011805011b09150f18080610082d0a0f1208060117040201031805 62
    0x40e0001c80c4010180010365800188400a43c40c043d079031002c02d0701e804e0300410352842c1d010350014a031003000030003c1c1c20100b441e81e06802940d4010100a0b6920f4030580c01480c10341d450113503c4c403861615555a001601801c42d00089a102100c402410384c904800c0045580050b1004c0d5844250602d4040000000398001c081008a500030b504106003851080e01c41580c00030f005000380700301c0307213002e000402000510f40c1c82103144500f0f0300e05045280c40c010340034144c05100e049201c00c101e1074070000c11106402207081c441d22503003500900c82600b80b0486107500c5501c01c006a9a0b040803500c00020f220b205411024405070500e9074007200d0382104c01d126096a40e0001e801a0805420300c0041c4008081150040c20070100800103450880d10810112110041040d1491450b01304951032140c20300c002c070719254028a01c1c0841082c02d0a1140a8049008029000481c1c0344001100e9600489880307606440c00e4034105201d54440e1300544c020b06111314010020585000c2110004a04000 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 588411852 1250 588410602 588410621
    0x100c03052a0a050c030f120f210a05150f130b090109021206060930011a0906030d0801060e0a090614150f0a1209061b0906140a080a0f 59
    0x18021940030f81000d0f420880d448030114400e40190b01524a40a80000c2c0031042200c0c07605800d0f40c644040300c081846d8400c0003c550362202000700383d00b800814802d23240b80f00750041e10061040d942c4408020321010b801d160025400a44e9246441c51130400c44400610700281c09030006400340c0032400184000e000340c1c800c440c4240c00103a05440d00150102e9a504803c042d01c000e41407448910010310f4410303140e1940081d01501856a81e84040007918240c00701242100821001c610100f0010642016036030050054814401094040c240007410704240c609940e5030b0480d07039003402030407140603c1c10302c00d185c0e114041c44404504e06c42584580402019520104142111311703d007486035231140702d43d44081d0a01e0900424241c07810f89001c64046803030500d0304d21528081280392030000c001e40d47d400b411080c9488907045201c43d844001c420700000c5a2184450a83d544408544042002104a507807440604c1020301890148803200c0e000f580048020504600025542080780c00851 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 588413102 1250 588411852 588411937
    0x19050405030309151302040903120c03020403020a1409130516120506090a02031b03030f070809030601120f0b04082115010e03070e070c05010204080615100c0305 71
    0x14044480c50801c44007030000c486a013000340900d80800501c8510002080190145440c2c1d12640109071040b1043c819003400a04200540000b03900f00800135045400124002ca10003034002c00c982840c00040300700c080005040544990b078609451800c003079a4071040301c441c4503e00541030100c69861040c0090070715403500707808003c1a800d01c0c1e0310700100a8841c0ca81074001c5004500076840103e0070002d04503101441c00803e00b60440800d03e18451fa80b000c1c80c1860000c41d40c6420000648018060f40300304908580c580c0c2d0325052942e50845020100600e0070100c3c80b0030400045000b80e1890b801030042101f01d0915a00300b6042c0c0d03440d0512002c0c41e00c50a4103000f0014090740600064040000a2030151214426000400ea03940520300030407111480103400126400d10910200080e1079005000b591250780d29480c160380c81000340d0702d4074102d20304440210300d20f0901e45c0e14440b102c10283d0352030b0404002a141510341e5030141c4000b03040c111151846a865030544070b24500150341c02c8 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 588414352 1250 588413102 588413107
    0xc0c07030c270b0a051014040803070308011a0306100306031202060a0e0d20071706150103111206030c030102160b0c071203020903070e01080a030306051002030703081905040503 78
    0x700030b1114070341d40010812094030700d0001214026190b004039407080d1030341655403242c0f81008090944121040d40c40715030968038005004100a90080043c0600d603110b40c5541a0b1644ca403000640348450034043c40d00d05440a000141442c0b41a00003008003225a040c00a503142d100e4455001c3c0900f543e103041d001d6840b2409000c030381135a0b8800c050013a07480c500600b003c0c8204800040041c4403c4800304011440d00216960221003480304ca0000e12030b49020010a8403075011039a2100011103504860216a100d01c0081c0d5000c1e0140b04800c0818000ca580303004120f0142c0d41981001416064240c4039003100c00e10281c909200600c1c1c0611000030203264a199407808581100c03000b00640105481400030700001404402c0c54824a29a420056211042032021034075000b820342c046411008090000640e001c0003241ca00d000c603001e5034051103810b4894052007401c20402c1c1003000142d00c10091031020074403404d0040d030054042d007561180485c52446040c10350750150b400750713243e4000 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 588415602 1250 588414352 588414389
    0x260406020c0601090203070c021e1908070f0b0f0307121d0f010b09071412010312020d0e0105040501051605030c030c161202010e0316080102030a060b0405090c0c07030c 74
    0x801002c0e004081681c800e501d1071400000081041d50000c038000d020323086850050501c0740203007004010013800545010700b17810000c000038115035200d00c40d0b04d2550151800103c0d088010301950400d8800304442e080c40d20720303030074800300710382c0d10060006d010821001140428560f060207021051045818412182c09255a0841c2000d1114001d0000f50f2f1400702030031201d8441d03d2529600a506003051100c1001901d8110700310f210f01d0502580c440049030020040242030000c035048441141d0844540724038029040e00d05d498619100d5010a03420700c0b00b040705610070f60050581c1a401c581c240c10501c8141c0d02c143c616040004581d42c0c03904003041c0003000e0130b01000341c402c5c0b000301d010f9950005840c0c2144450b08210341c902c0a0304122030040248a5900c2c20040003c0178600e1004040c0126600c02c8002d00030f41040d00d410000e18101a070014a010400d41602c1c103991005145061948448400c40e403d5400b1180a501c2c40c024031070000042802940c80c1c00040403805a84255a90b2 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 588416852 1250 588415602 588415627
    0x201021305010503010e150105041a031005011112030a06080f07051009151209120c12050c060a0510050d03050304020a0e09031b03091c050d0203090d0326040602 71
    0x40d508040d04202c802d01c0108601914080c0003604440c1e049058080b004401b070041f111445260041c071000d0420303640c1e009a6005410044d4030488140c949005280d032114011204045401d41000007544003103003140040d92048011500310000020000340247c5e22a14942040344c27000d10140c0542050ba03017004203081802d19012034404516102c203c01d0709105084142d008090b8403034040018100c1c00c00d40c071094941c403505030b164205031191410398a02d44010400c500c0b680084828020040319080b03954020b00690b112074610102414aa50b13075039000d9402008002c05000c8002100940018684c82e510103058205002c0da0728241e0764602030061101c842f134254400000c04007484204009400084151000100002000c50804841c458820f03e140914406a40d1080455410300000e124000c0101001423082040e50b140c4888407009a13200e0240c0c1c007019410075007512202001911814001a0240519009150744c1c50901c1007942040070441d011103890307a00042e44500305a = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 588418102 1250 588416852 588416887
    0xc01051b07080c0a0609060f060e090c010e2709010606050f04090b0d0203010e0c030f03030603060105091306050f150d030522030f08070c0f05060a1d0907020102 71
    0x30300000d00c11182540182003103464892060060302c428000301e480202c1d03800601000400396002802403025544a042040c02043c0001151205c64a40700000a51b50040c1174983c3c0303c3e00d03c1c0e00184c801c0708038010044d503001c0d070040102a4080b00825142482c80e5907103000030841c1445c03807070300c80040c0b81030b251407030840d00031350402d209010041c0303c1140c0d000801802c84099404040300401ca02c241038000c210a800900c80082d815402c0401d04401c10200051010005c04120212a81c0b4400031102076100d100648000c0e405130000720050115003800101c0a40044164070702c003484500a480e85011140305072030003001c0c00c4e044014071404941d984818014048200d4030b100d4200c6060364060098884c1e8044101111905412185075030540241130b0015070300926400c3c2c1101c2d6614000101381c0c0700715411107034960740010204691081085c40029104050122850416009070a44850802141124440107960104c00c0f40b0b488804000b070041c1d0481c1c0000d038031880c40c241b1404004 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 588419352 1250 588418102 588418111
    0x6041103061509150303072a0e01140f01021014060a0602010c090e1905013003080402040902040b0d031e050a020703080c0313030807020a05040b10030509010b0a0b0c0105 75
    0x900420482c09840e941c1248843e000001031164030030340700a80000c03030b0640c09540c0f800340c40c0c60b41086420081d2103110354401140b0320000c01014000f40c50740c495109603d428024000301d0f086031705e0810304a0605949155050105004641220700c0140e0100259007040d490801c81c41c4081c421703c05103080441041c0701408082c0002d0001140f00760004000140078840c0b03001942c80300010805081b0f00c0c41c9118858910310100b071101d9070b141c5405052000c0c400c240c0000654020055038890704070010240503440c0e05990304c528585036602084003502214106a07401541c596828050ba074071218130a00c0c091007501c85030007028180203800280310440da25041888030400c14200c2e2139a003c29072030240c0e0b600c002c00680340c4001101282c514000e85c18641d010100313054010003030044200240080a00c212a070040460720358060105860400b19003580044010818192160103038101c1e03680103034141d000140076407012001405036070030f90303021089030b010008004403401028058150301 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 588420602 1250 588419352 588419371
    0x8030717070b131514101401020d030902011403040b0f060f0307170f03040b07060605030102401d01090504080f030a0e010c05040e0a060f051504080604110306 70
    0x500c01c0c20740765000c02000043c2007000c03c601040031003080002c840d601462902000c601081103403d2909038190082090351055040c0e48103003000140003c1558500b003041506034080c10624441000503009082c0740c0f00120706003d01d042c0d1001441820030082c40c415400307444c410300a410000f4081c1d0302124041d000601504001c041450701c0c0e20001258021192050f1590040c25041d007101810051015a400b0641c00700040005040110b070000d84070071380c040c075410400b4a94a0741054200c2c030034031034500324000e507442c01c1d0050b401c2c2000c0c4607003030350044901e81c0000f50300803c0f001300d1444558100d240a0ba101801410215003007064142c050880510704210600f03150f25021454020300c5590360742500000000344821000f50445038401055000a001d64000752002500b90340181c040c0e0203200c06031100080e202c9515010315030460313060790f000350700703143c01d01082c003c0340d8030b04070442c0300203450030400061000800c0002e144510b00442c4143c2030150350200301405c200016081410 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 588421852 1250 588420602 588420607
    0x120f12090506070c0f050102070303091a0103030e0609010c06090b011815140102150c071403030f0412050909180c01140a050d060312020703050709061a1e0408030717 73
    0x9030700007450740d00800d40e030400c18003024240c5414601001000401415540003150000c101074264204607039441c440c0f6020711803900401e4a03010195024800a00087c400c50410f10b000d0602d0703402050b0402043c0340030756442c0b10380e88540741a105200703400c4a0300f085040041003450980c21047c641004504400d11040d009109007000400b03940c080d00403420000b20001110341c1c001c2000d00d090f5010800c50860a1400524250a40d000031743c0131364400c0e410118141c0e401d1808022644118903108400c02c6070b444a85440c50101d400c02020400d022041111900f00c0e500e1191580c46061101d40150051390a443c8072403c0c0010b40e03a100e0306001c44240c02000d0012070301c0c02d03100901254900340c0c1d11040d08481810281009030b101811070a011860350b041d0590116420b4180ca020303400f100c18596071440c034170341101c4c0e0602c110300200150210490300303540450300070a1800390701d201c07410900040c10b003408155401a401284182d0000401da03040102149031125101180c500c11070 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 588423102 1250 588421852 588421871
    0xc120e0f0d030e040605030c180a02040f030b07020d1713241a03061e06061908100f080712111c1407050a05120a060c020a05010e0712140703120f12 65
    0x2720b13200100d5002c0c0c0d0740c1c243c1d5000041c16412040d030540340200780c1d4150601070169641007142c0b44207001c0c1c07031500c014014071301061851070103502d49926840b45821400c9a035922014242045c10b12150f0858180360414444458120354000c120104c02c0c0e8907030001040b901016075004013584409405009030894410000c0000d881c4240c1c11201102090b201303c65501c03100020303ca40718203d246141c11840303e4455061580c0030078650321400010940380f91594a90002090000d80c44c03003052082e0740100d001340803600004e40801c01c004e00c0b0303461071214440c040d00022aa914029a0300b01d032800d0078180c2c2803d001243c092a00042c22100261005a0400c1c02145107401035000c0d442c0150514103680e4081c0c00e041084030101d50b0046003c001c0910500c50003520f48060203400d9840c0c1d1b00b00030007100070b4040440c6e0031003282c00c40c80300d20708244807690380c882074403000030a80d6105009184000000ca403080180115400a56940180311070070100b0191080b542d90301103004c8546004c4840 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 588424352 1250 588423102 588423109
    0x1833051906020c010c140601030b010914040b01060c02030f150915070e012010020301050a09020c0a03230708070308010e07140c16090902010801060c120e0f0d030e040605030c 77
    0x142d9000e40f081c60100402509420640c038076140300032043c1520700c544000001801700302c88505040e1000c58005024065040903011903074413062300d002c1c0c1000b000c1d200410550f0301138540306600c2440542071f00c07204006403030900e040104180c41402d8105440e810048501c40070300c00c65400018201061803942030505000f04040008480903040c8110034030308943c10740035046e03c101006d5417403080300c49171030546400202941023032007600d01031204060b010800041a009507010100301c500200360218040c2c07411600743c41248019407031480d010a10b004494a890001d04800b4029a01c040d501c000b280b40003003804005a000321201e425620500c45211382c00301030444103070302c4440816118030161008a0130b1a1203510045545645244001803802d0340713400054165001342c80b05100c9a80e92902600c11014070880104022000f000c0c010385180265405056944050101d8040a5904022440342c4506000c1030780880e50209400f291031900380038420252105801030048c2c1010704020 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 588425602 1250 588424352 588424363
    0x20417030705070b0a03090501020d1a04270c050307030326010b1b010f02130515040605040312021f0203090106060905060f0f0c0a0b1e01183305190602 67
    0x1138940142c0001160780c0103c2c441d40090b030002c0e403c40c0007155030700e812181c1d501c02001065032000f000b464520501003145030511800040301044a80c0341d4143c00b03414800119000458422140b55124010102e825101040314402440c400d0320389902480c802c14004480c46207580705c5044070301c0308000500030403120380191045400c0c0d400c4503034940c050711407660740900b240d9819280c200d480483c6a98070b420120000400b1200140e03000c0031304603103071108200c0e244214000c140114100b0481000024200480b070060078403a0f00c16100c030340e041058520f042c100003c143c0b1406039004030600c13801c51800c0c440c44000b0200d5042054074146000003140081c001d840ba45040100045503005d070003d459000c40b4030084000b41900c140f0310b030600e0720080350b20042d210a26040d0012410480048056460505807008012040020502681c08030b0240440c00010681049081c1801c0b04000a00240e18401c0c01e60040800c01c41d400d24081c0728a00c992440740b0640c02c0ca01c141d04000ca60b8000c90f0 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 588426852 1250 588425602 588425609
    0xf0a0b0604030206070507150e040e0105010602030403153b060f060607050c0a0305240c1e090406090501080f1504020d0302030403141506011112090f04060902041703070507 76
    0x510944030401c41c21b146040420a50044482e07280805001140b80d5022141191010048408003c0c58000d41405400c0b03940c24001c040150f07000b04806c3c40401d044082c20482c58455410200e9050044850000c13030710a085010100340310501c45050450324041c101110046200c0c008084500d02260341d01e00606020784150b0040302c0015103901071000600409000620107002d20158039624500a9540d18507200b039030100d42000c0703000c1e01c00e04130440e4200d400f41204141d22414120744004260308a8848090040141d07030410981c035083c1c8a6000e02001844460800146907242c0055182401d90345480c00c40c2c290400c0ca0f14031610004661803980098041e240e090003200c5600d03059255219a400280522200c0c504401d20350100143c030b0446059502062074443d201c040040d90310f149181407145003a000311219600d816000c00c081e1040c0e030401400d0061080c21480803c0894041c3d03081800d003a41c0000342030142d0000c03010340c102e540e600070004500d819040e8075040d848078003e01 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 588428102 1250 588426852 588426859
    0x7030906030e071a07031b0302030706020a030b120c0f0402120a1508100e1c0c17041205030301051e03030a0e010c12020c030607050a050412050a12080f0a0b06040302 73
    0x1c100310b61007441040720a018040d40c0d0313200d9a0042d4040c1d03200015400c604011400200c0c8840200c0402d12998180021650316800460600e844d9544d480040d40144921a040668641030102c00d65504000f020303503240c1c031901411420803141c050003512507102c00500d0155004000c401c0358400351200c03a507032001d0b803070100085180050720f008048501551111240d1b114030751315040006c0f0ad546c0100c90f4020b00408860042e0003010940054103601101400418101000e9001042020b40e0321080f81c03080903941460b19490301800085080404020b8410340d1001c00140300c541005024100741003004500c441c500e11034400040c2d40ca1080e0304030310082211020140a190740240d8a20300c08540c171502d07115943c2e4149a0095481d1030300354842e40b0900c904008100118040c2081b50310016050792580e25103814014003c80034102610103c0f1349104503104580400e5010b03003018405080340c1d4800c5a14100f44a5403003030b200000d0319064020780b80490344210b5a462000b19411a40d054 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 588429352 1250 588428102 588428111
    0x605090d02040f0603030503150f0603150d05032a060c0f0a030917180f10030e07121a01080d050415180602010509011104050a0b070f05030d02030a0605060703090603 73
    0x40c4040b501401c10f4405410826080c4031000c0201600704015602c03c5420820178840e6185440c01c1000300c400d03001806422640800201e140103d220364501080c14010741100805013003640c5403481d580c00041d1221040104954901080c180460000e4012003210000d00090500208030074452044151442c401140001c0c0c000d0300358000d401c03489001c0c2d0003000048d44911540d451607069442090a00b80b09540900403180b6881c1034569a902440d000c1c003078101e46641c01d007040e8010261000c02c8403039480b52400025a04050070b608192940c441c110040b00300031684241c0000403c1a040a41f191304070040c0302d004a03600c0341c281d5088070705441a003005680d20143c16109204100c290a04941c140b920100d140c42d0150402c3e07018400070381c002c02026204918a00d107501441c01980d501c4041c21360100003a441410140801e14021030b8a03d0111007140e0f240d61071644615020301d8010340204c00c22600302c9c054490321009000c107640746c1c1d103070030000ea41c020030f011180e014000500d680c8 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 588430602 1250 588429352 588429379
    0x231c0c031e020a03030c05031005060309010905100c080903160b1008150105102a0305220806421e090c28052b15060509 53
    0xa92116000400310a00307040d4118041ca10094039101060000d1300403900b00304a00848134851021680720300c100058003c005030802c0100001580042d00d0609a90740b20080034010030414090b9411408951000043c01c9601c620041c000c11001030141c100340e0028081605440c81c4c2100e00c50840c0e6002000b6070311652022140c40b40c09101d44c02000c5144070395072900c0e002c8003007402124180c030001c44031011a0a4980c00c11202e0141c1442003450703e807075090340305e4081c01031460b401c02918804d0400a060103006c4080c1e061a02d41901380100c030303104000041040e60340c10301c540381d081510340c3e241c82c19010040d000149640a8080340301c131501d520755071070310340e20140500d13400c10b4000052040503000c41c82001c031a01034800d10041071280f45000c0120714844d84080449483c245044070b4280c040148061800780400851403010502404100c5daa000449080c1c8490f105291717280003030110b50504501c802203035202d04d0703880300e0306201c00e00902c01d494124081ea01030040448440100766203 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 588431852 1250 588430602 588430607
    0xb01080c0a090e010b03041412091909230a020a2a060509010b04061401020c19030204050c0307120b012f060c0a14070f0602030919231c0c03 62
    0x310f500a00340e010403c00082210311940e0005c502640c003840c10310101229007082141c449000c484900d80ca400100686e000a0034648440c02c0d040980002010050303a5649070a070994140c0040f0002c000c80c0b0021227107003943c000c080c40707820a249000860a081c0b40c030101400045089128074a100c0b102c81c0c2c0c00b001c1d85c04201c2c54424656024905000c00e090098640c0d01a00002c0b1003a48114103140b000f145d4a100c0111903000c80710164010f0170604c0c110020f0000049807d0481007048064080200250b12280a02ca0103620740e04080c540c1c17442c001c02700030030340000003051861190a101c0d00c801540c0e403081c07607110030b404030150080c0035000360904824421600c00100e02c1c0d81c003526007040f00c4555041d0260107002042d44801d40080c40f5400b50384000e109208008091a41e10b5075404086952071340078503030200035641141c001d481c10803c1d806103a03140800c215402c01d0300030034991002c0104241c2c4001010000d0040070700c100c4049002d0301403500141c01d2070400c4481d010340b82c181403 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 588433102 1250 588431852 588431867
    0x9111f02120f0d020f1b07081e060f2205100518060c030a0f090b04020108010609030b010915030203030d1a040c0206010308090f1e01090b0405011d0114040e0f0a0b01080c0a 76
    0x1111b5011300109841c03055a05629400940314141d0b10b40a05445584610000030755a4060441000548115074411005107c0760f00c010b001c43d40400e0408a56885c5160000c1c25524014001c00040004101c0101c1da0b07010748400038501403c070412100c00c00480740000070102d801ca2100c0c0000380c6c4a559100c28800140594a110300c14075042410745002c3c04858030480f07000f0b500030ba039442056a00d84d00c0544d11607165102c01400c41c0c80c0302004018104850344100c0940d6003c4035450f1050b5034a800007861034018a66032a216699030200d062803541990804d8014a01600d0a00c042e01601d9000381d2900c40c140300182c84084c0c002500a03040d83ca000d003030700b0165001811020301d08189007000c4981d502c1041c4180c085000301802081041821381600d0490390142d55858910803040d81c0240e18102d05041d05040c0084088900c3c2c11841c1e49001e04041c0588600044280c42d09401040c1950720140858580e1840d2019149240c0d03401101150700c8812175042c0f6650740d8614034100c0790007 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 588434352 1250 588433102 588433117
    0x1a190605060d27060605130e101a090702010b0102061501050a030b060702090705040806130f0210090902040611070b0c07050622031401050a0b06030a09111f02120f0d020f 75
    0xb1401c0e40342010420844e0b9000340301780c45042c0d13503000382d002c020b64003081100c81c58404401c3c60b0748034480d0b1400c81c0050340c00560b9080d00038414815809402c0f00400d20005040d111007000d40d4683c040001e0a5a0400c405980f0940340c004080d03128220600103031581c81889056010151640b428070240d0b200c0720304564056501401114080c0381c00c0c1c0d0700802c543c02074001c030003240c01402e001c44c420101201600392041d0700103d042d402d184042d070800004920348000b80d010b000705070000250700c181900c090070062180e0385411602055034400b043c240105904000a4501c1c00d1001c8500e1000c0019040e007030b100d05481180d42e414070425103012103844140c2c0c402d09603403072940110030000300f00038101048034414000e0205444031301c0b4400c107580d80d8180c01c6070031103030520000c1d00041403a00b00303160143c0600c1d8480d960761856404201a44003002e04581b03082c01c290500c1100660421070f2480c01d049110300a0b05005243e00801d416100d031000003040e480d0007084d085100d00c1a80c08507040c1 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 588435602 1250 588434352 588434411
    0x51312050a030b0d030e0a06050403021e0423010f050402070c0b0a1106011509051807030f1d030304170f03010306091401021b07080109110d0f1a190605060d 69
    0x2840c54901d0000c0507102d100406c6170180c000c1d04400100b8a003c0d50039039054035402007480e0352107140c50b102007000100340b9110503400303903c0c0c0d51028020440d814291003604070f0400040103039810518001020b19265210703600541c4100560404540401c1d030030b8040e1404a1040755446404880889084240c1a0b201c803141c0110000028010304101114811550300c5c1c807000e140316502c20800050000a00d045550314030f405d800901c00350b1007603014071081d15090000081280c950000c003020f608008215842c607600000502090202e800c000e4420410b8940e41d0914010041401103c0c3e40018072000307004d507850382c031520100003041c10082d94030707400d10008640b2401c0c0d5400f03803c0c102c3d802081e40c01c0385000b8500045130040040c0a44242c241d08071f1281e00f843c2c0c1011003801080200000251900c5030300c0300c000000030750104100004010192155000b80c10007070025041401c1c0c0c5020510f0033307841c5c05010840c43d00d41c0f4080c0e82d18000384c10000600710b01c1c2511a00230000400c0c584c11417 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 588436852 1250 588435602 588435619
    0x3010e0c062a0f010b0907050f0304030c1506030b0405100c0212092e0f0f02120c03070b18060105030d09291b01061401090506070305120a0c0201051312050a030b 71
    0x601c1c40305501515805c10300300c03890a00307a11540001d8866110321041c00c401840e0030800100424010f640701c0080900c100400740507445d100010000310b400c0c1c3d0b003080b01c0000d0140d0900091110030000b007207841510a02c02c0201c405a100080d5594480086c142808000401e49100310f0340d5460f64900d900b0940d07181d402c1410007400d0035502d48210000901c001c00e130b1340c11080745140e00c0350b0858044551980c00a0140322101104602c483d00540c40a54480c8403c00c034100000310503102150041090300a0070841e100080303121810322105821190103075108410403504035500c0483d5400311404e803040d050310781c0310045802048900d402604415042c0000e0241408110382c0b001050094600d4000c00c40c043d29040c3c25403a20880c07020480c00100080d400b4011031401500030969940b003401d009103082c10426401e030030400110b8010508666071159242c0164080c000c16500c0f440c101c802252242e001e5440d03034844200c084120003004030101c2d00c4810903000c0d9200d45501c8070f00500000 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 588438102 1250 588436852 588436873
    0x11190c060207120e011b15090501020d0c1809020a0507110d23072102040e0304030606140f0103020a0c0308060a05090f041419030305040206070f060b03010e0c062a 72
    0x2c01c241c40440b207441c0086e030342c400080d08403164141c0c010b0642da444034040b40007101e00e0701e000c40580b22051055801395400c000a2540030190b12940306118203a072514180080488010ba480614aa0140c06124010050340c0b400341e602c6021109000d07440000107121141d9800461503062003000018010240041e9050307140010410201c0c282d4000ca048034001d03511000c6450490258120170030650080030345440c01450700e908444c145031450b13021207040c00d5803600c0720b4041d1500741d800207401034a00e03034400c02c5a04107260208200202803c041d031500c040680e0080440c0a20b0b10080d04000146020610715911006108000c00006048100d2401d0402402d01d01003c1601c046600c2290342c11508049003021076a2585618800c40c0c03103100304000c0d102600540030080c800c0f0b07440b400420a183c0040c00f5420303602d017028003810000030503040102c241421160203a08500f03895011040001455840d130301200e05d298034954143ca80c81c1c0392005c480d054444c0c460a241d0460041c40d1044c0d = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 588439352 1250 588438102 588438107
    0x91202061b060a24061b0302011401150f0f0e091005030f011b020609070b0d1524030501180b0402070515040b060d020d031d101211190c06020712 64
    0xb0341100960364181c0314a200700b10250000d20b125072081704040f50b449286601261030390a80c86180c94000c0c0000b203100740c1c00b5086d03458032800c260401c0e21191910aa02c1c0680c036440150050804114100104080504100a4000000c021a17144034000340c4001071005580c803600480244005006c0318445040001e6107406021003403482d50f9030403100c8150051007440014914014000c0700302800300d06081c51701401c00781d480b01c08070488942d03d507000c00404403e04140f01000303146041d002c004054052180780005c026540b92102090b041500610112500c500c0e0132001202d0054000360380030421001c174029010381b141c0034000e401603440d918443c00c4901905407065200750b240c00400c2d9560010400c008104140c065000800714030341c10002402048142514a500400c64084040030400507004690491410380051040a64803003110064018103110607130b80031029042503403016041c040c1400048807501048500000d01c020b0211581c1100d4005803c0710711400d5691108202 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 588440602 1250 588439352 588439361
    0x141e0a050a030f11030c030703020910051c2022030f170403050316022e020106090b0d030f170c03040c062622150606091202061b060a 59
    0x18404603042500c0c501081d0f410344145154119503a0169045440312480b925581e00002d00010601d40c0c01c00025402d41d07a054100b00000317000355240c640c1c07410304128a50310b05c80031071818000c0508200036140c0c244d80c04240700b1090b600000e14649c468a032588040c00001d0144104011800014000b200b40502c0740000c4100c2400748100c005902d0000c10402c2d101d1155100140c030940041c401100020880001c4480070f5000500d000c94603100e40c01c00c0c6d9041e90515070b8000e40c00b03040728900450b598080c09200018030740030804100701c1800c0400b1800c258069900103040110030384030180103074040d10201c1854437150001105030715106c0e900a00c42d074020340f016100354459200014400788a841421312201e0000035202c1141104000700c0740390b000240c0100c09200f9060843c51120085600d0300703e11a008240000e064441808800b003125150380008081216111080c402d41d441142024406903054a4056640d80719038404224001e40072129460b0780501c0007807080d00d2035290007 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 588441852 1250 588440602 588440617
    0x4080d0f110c1905030a0c06020903100b03010506040902062208160501020c0405130f060b0607050601091a0915030309060a050306011d220b040203040309080705010807141e0a05 78
    0x40310210f01c00300510620032010480020803581c410004e05031014400c4018400041c81800b000d402c011821001908140401c01030410707103580c8109140b1710f46003d0041c2908050180c404009104c045d030082601031040c0380c01644e400365803010404001d0700e04034692000740048015155221469290951011a18403c440c014440c0c0c0030100d07800d103407510605000e42c4a100e0325113000706003961000b519109011042c1c4040340e5030803508001d92510002412010703c164003801040d81001c40c0034040794500340194034400c40c24205284a5160000a90382014940d4111600d1641c1000042c0c51440740c4801581c1104010501c0e20815810002031070084030b09803588400b0b01c9540c154401c0c03d07820855070a9104c0b1446030702c102d8005418030344102a46440f880030900241450101d402e90b4000c0e83c0880004a80e0300c020003000350244020b0018010900c2c0040b4182004d01c0700515018040c0c1c180c210384080019101e5010030440301e92000041020703410b940701c2004520207405c0d9000001b = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 588443102 1250 588441852 588441877
    0xe0c0a0f051008040c0503190c09020306130e0f0318092202061303020d030518010f020c0f0f0d0506040c0803070302210c060424110f03071205010905180a050604080d0f11 75
    0x109d0210310f469043c000d0700c3c03084501400c0403245825040d4043c3c05096a0100340025000712120711300c03010703001d00007040407808502c90075103884854410b20085100c01412161481c9032a000000c1441c0c1c14108400601d804440e100d4480c12245052410054507910007580040039540c000201a003000181032a48200c440c1000109281001582d10b8401000050010780117066020110700d082804291107100140842c00850044004a80181d6081d01d01341d40350740c40001040204501d07170b58442e0181c001040510300303201c55070b50040e540e110001c18884841c800064040c1076244104c0c01c2e5508854440704a038102c0c241801c107403894011340c2d90041da808d103c001d131040038050302c1d0140c0e4400e100340e011550b180c5118448004520307000504400100102016811f1340442070b80134150181900d80000905400c01d0384140d109010100015425a0000032403c0003180f0086a6941d002e40c210003010359074a034400c441001458140f004880303440ca4040c02c4000e0044650280009100340d1 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 588444352 1250 588443102 588443123
    0x15020f030708071e050615090f062202070c03052103041e120c110303160809010e12060603010b1c060b130c020a050d050712030c09090e0c0a0f051008040c050319 71
    0x81f0074001d103141e00701c0741102c1c0700080101145c41c40c1860468946440000ca11400c1c45800d0200d0100a0707030311101081e01c03c444100d030280f0a01c90144142c0b000d81080303005000440140742e00c8502c150000400280c000c203e1100c0740d540f9442107590665065a000c2d1071107400005a08001c0e2104901141c19070300c81c280000308620074240082241d140e082581019040302e5015a6840800e50007066010b040008503c400d0926440d000f62100241c0f840c2c201804140ca84070040c9401c6405d030390341c540c1c89000d81c0c0320058814190049200102030b00080081102802103001c00c403269900c281d8010351503d0700032a28845540440c4030a5403d10130300559040e176030016411202c0e402404409406050b0b401c941c68080340c0070b588001850001c50415a074165591001a03045503085006500d0f19040407041c1000c500e065100341d005403412030300d00a2042c3c1000c000c900c069401c20b00c00d60603c42444042028840c1c1840d0800c0200402000c440003030b841c0c2c186c8441030700b0264100f26100b4012 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 588445602 1250 588444352 588444391
    0x130e0f0106110c121501080a0302010b01030209010c1101020c091905010e040c0510300c02070e0703021303080a020a150e0c0904080d051015020f030708071e0506 71
    0x624201c900e119098401010f0040d07980c004c001445045407002400c0d0311400402030200802c02c009180201181d50140400c800d1504020303081d50742e2611018100341c410010903006a800c0507400b620319030006c8900c90036080040042c0d10784800520000d5010400c0010400148805540306003050440b903018026070b640c50900390900b1200b07840040c20050912404e00c51820001142108003510740390150035040d45480310010710b80c45210381c501d84056040c802c248211a0f020b02d49280303c25200408242d0b03e001300400d8804000b404070003c00d6000512002000803400000c4040c64000c540259070780d44a40000c0e543d01d42c8104102e03204018008030400e400c0c1c1901c54210540b1200d03019084408003e4104543e840e0000d00486485030b00340480702032810b5910030240b04a0140304203001660608a03042410310b1080135035800c560100f044020181c801209582d00d01b030340202c800d6158046440d01080124072041c0d0312044042e40c00301403040c008001107160007046110f05100f41440c6 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 588446852 1250 588445602 588445607
    0xc010e0405130b0c12040f0b010e040b0f09010b0411030105010906050705030a2303040302010b012304090203040c1509180606390803011a03070206150105130e0f0106 73
    0x200c2d0401680300200300d031280400e8155a000e64443d1403007800078a44000c142c1403030341420060b03406560040c0c20390004ca0401c0f00b80c0d40c4041c00b4003010518a0814039195440d0307907104000600d280440c500c00c0c000325881c80000d40140d02004001031041c4405440000f03146d160f50002d10849001030703440940050705a010b402201e030b2040d000f00c0a035142c605001070a903622907d4214100501c2c034200d03070000b00100b11602440c0203902c070b68004610440000300041c0a0810740c2401458000412582011020444121411a81d030310b2005a241d03035440c2045a0b00a805d5402580f6810b0305856026a041c2e00420110590380031120110001c3c08249240d810bc4005005017804a030b40d444048003100200c00403040c00369884088a07503950704a207811076600825401c00c81e06000d010006000c2000c84900c5164000e800840143c01e5140851300255191400b0384003220fa46d05038103004105902c904201d442c5810000a401c010554a50f07040d07003d1001150f011a0740d0750004008503030f052 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 588448102 1250 588446852 588446861
    0xc0f0b19030207080403030c02060912030d050609092a0901030b0106030f15030b0411040c0f0314070801060c050a05070b0405030c03011a01110a1403070312060f09110c07080c010e04 80
    0x1a00410014241703821550143c600c03001010003a039004000b48040d0038103540c0d02007540b1140030603801564503440d00c0c013015000da4901503d00d6101c3c0c04081c0c10410080c1000460908041044c1d8403165142c17103002800c2040c01d104d0140030313000320300e040005c4144040520058102d030740d250f4040080ea001006a030741140e212109000d200341d100b5104001046c4030444041e005805003166070003000101e0f00207001c030b038414104800031031800651800d174590107100300e90100d10034010f0003400346410507004002d154140108014004800b4114003071140420003609110360140c101c40c400754582034885100d0300903104e1288680b081d1030341c00005080c1030088007803070a41764080300ea060a6003030040d15014440032500c034162265400c03210109240d8402400351440c844041c6036200640d04008000050418540c400c803414000c04011400b94118800111805101c00040120740c64407001d480388200d0101000074443e40201007603510340800d07076510b0030b04241ca451020107100000d03c000c1d038 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 588449352 1250 588448102 588448117
    0x1505090f220308190b0310060927060207050f010f05040c061d010e0d0f06061409040c0905040c080a0c092711010e030d09050901050d1e0c0f0b190302 66
    0x2d0344100105021800340e1302440c2034070419100c0840e40700300910110b450300352402c0505586549815040110101314421841c0103c0401d58503280714080d6000d401440a80d100000c080682c00103c500502a0074820640516551030092104042e801c00403001391409640680750b0200c9050001403603806001c0078100340c0f041d005241944812240150354034001c1030061500650452004070010702407151600000b40724400004040381482d0418078040035031540d00c4d005100f40800c0c403012074050403015045401c45203003c180c0b9074440c074001401d0400c90340030304018410543d072001040300010818095410340e2404004030020310034ac2c58603007007040c640c2c0c454484440e2014408a180354071410442e18060418036440104500841e18103120482114002409000700780700e10b05d4103603082801094105c0705c2d6020f40102c2d4075104040301214407400b2000c13180d000e0200401030344c1c210700401000c14070f07001c081d00d942c0c950b41109107500c954024442d0314465160116407500070f100fa507001 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 588450602 1250 588449352 588449357
    0x6060902090d02150f070813050109060801120f0803090a060f1b050c120a050a11060402010e010e04060f060e0102071a031b0408010624080103151505090f2203 70
    0x40b1042a028050320710f010a0801c4c40d4440100b0215540112604c02861080d01c034809041da648514103c440d80304100d0b4000da810410840c0d001c10442d03a01c0702d00941914a415410a000740781403514012000348114010201d03040401000146c42d008240d46401380c2c0070385024408080f10940a1045400440c250703034140b040da44c04070118600c03400182c0340031082881101c120068099100f02140c100055080016400040007405d05900c00340584118070848000c0049007010b84c000303000b580c2441c5e14281004941c1c40e82d50341a6850b5040200107113440302520307031010388621b030081c45115071914040c054465aa00000c01c2c1d020070001310782d05084103000b2810b5480c1c1456940c17070b01051040c1449008001d000c0821074240a102d424010150001c2c200c50300680c01152136032186505a00a051010031401000822031289a6030a0302111400008009181e0ba046003001142c60b0010345e04070740508100301150a000b900140285076004102c01070306820301c640d139108082544001d00 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 588451852 1250 588450602 588450619
    0x30a0c030605060d020604090c020f030d0e0f011e110d060b1e03060a0506091908070e0a1407030e0106030f0602030f10060f08060d020306090a11030120031509090a0606090209 77
    0x4101668000244110385105031800889072f01c0000e881e5821000100d040d190b62a8540c05100b88100000702c0344100c020300a0080b0b400e50b2840b031034990303440002c410425846540a00c07030048020122030381d84c5081701040107866100c490384c01e501d800810318006030007826101c140c0c1c0000140141c1c0c0c8a580004c0180340014103107414407401c0c1c0c216007010fa82060001e90440b80c0d20381000401c001801e00d400081080c145042e050822000c0003030010803015181c1106240c440c606034410660002c060700740841d40386000c10065004000070341c000303002008903020550820115400850140c2c1c1401298200b45d241d550704c0c510542807501c20000821402608021094020099142d02500c001e101541002e800d80112703041840845010030f131600304409c22802c22903104e001c00c040c85025030080080f0b2000b132014080841d00c521030302d0a04080440002e61031345604518060b52a40a080c204043c00e001c0c0c05a903507602c03020300c1150480c1c1420408110100e140c0700303807a2002c3d0300801060 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 588453102 1250 588451852 588451859
    0x12030a0207030e0d11040c0801050d03111e01060302040b0a0510031e0c08071101050106020a0204050405010b040c180b130b0c01060911070302150c03180c030a0c030605060d020604 79
    0x14001d502003481101881038407180007543c0c1d0b0780c2501019000e4081d400c401c40c140c0e42d110801003190419a668014404184010701041c0c0344c03c1100e080740d0b0b5140c00c00110502158601d10b14203051554403140c82181410380c800000c006401282c100e900c02e41d418080150036000f004104120380c05481e030010101c2e041d41615a2094001040a070b801d00d0040b11070844010028041d03030250381889000c2010107090020950f40314000681c17072140140200815410108029100d94421501900c141c2d155400f09051000030b6014140b1918024070400419009950150048203842040a8403480800000981c2020b000c101c44000281e0140d0561a5040003083c03403543e040420300c0c021640d03a031300300460103a000b0711801700c0083d14050340a0711a80c451500901d010b140d0041103810101070400d000800038810140c0e44c00130850144684010140100913180441d2005420342c0340c410b0190503010300086000b032400742d030302604050103243d0707802003440441941942c0c0250806020401003 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 588454352 1250 588453102 588453121
    0x15050103032c060a03050601080a1e0e150112030206010e01050607030f02100501090203063307140a08030f1501020703150609020301090522050606190b0a03050115021203 75
    0x4122000c100e1a2a80420b5908086400764104001c0440072994643c2030040c1980c016880e03a50200100340d05100b4040344a112017601c05e9108080a502a11114080c00d062818007503924031b1882040b07000507a40e075600c1e08044000714034006030098007481e4004640e48203403036402d0b8142d1f413024251502e0b050f0725550403a0080b0181d000c1a08500940c011480c0c41d070b10f640940e0b0f00030101200050385906100040003407207041030390801110050040c1e4101440c04041c4480880381404c03c43d6a152400e90611344003c10b01d04460341c50034003070703a440041008202e202460184502e168483e5035555814141080078900c0c0d8429030143e13000703000810000340902202102c0c140205008030381165507a1059040c1d80080e0407001c0030f107446808010b50700c0705130103200d520707408100c042c1c0140065070b844054a074900901140d0280a80d114550181c2c89370f40c840f40d00800721b1544007a0349559540008000b40403e000b0a10346c0111940c045030f07074034400a490003040400c1440c0d10314540310454034 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 588455602 1250 588454352 588454397
    0xa0c20070608041406090a050d0512010b1b03040308190e0315040c0515190903031b06290a0e0606040b160501110a080105010815040c0e04060603091505010303 70
    0x101c4614141c00c0d000384c1c40f0707402809054045c5200b2001041d0100c650310300301b410803038242d48503400c1007410f11814414901d403400e4541140c1c0c024118555481c201c83c5810401c5281e1048c0784543c4c070000400108210b4030400500c60039411441642c103607100ba80048a1400d850480c1591550203103200120102c54900b05581281c491032500070401d030f03644040382d15061110410030140c0f0303002c1a141840880b0000d240a124418649a01d0407411590302815100c0010415560382a21404075010088168460711110f01a18000c4020250001801740d010301e01a1600d4040e28480000181c6024403129850240d00e0080072075081c20709160710402d540d00441d502c01c1c0d0381c4045550003400f2a80a100d034000f054030403140301e59220fa1007103003c0c01c0c03840180d01850402c1100800c000034207418501c40340d6502000c503000305000c400c20b4821664000c003c84c8a55002e442c000c80000c840d60940d00c005ca45038070030303d402c140c0348102c503600c40f081340e00922001e0003041080064400740740e2100038 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 588456852 1250 588455602 588455611
    0xa050703080d0e01020906220302041b03110901021c02071d04140c030c060702031e1606080601020a17120c0d1a0a1403030c0d02060a0b04021e0d0b0301050a0c20070608 74
    0x40c0032204552740e030002000c0d588072030f460494104480113903829480d814040c0d00150815003003a1440c01e400c2e000003e6a9058a140303800612004a00140c6c18500c240083d500030000900c00465440840c488039074480401d50f41283c1c00d103510101c00e0001040031030040180c48008014196042c0080d060050640c4442000c0f039060180c20420303a828140f07030500b0002800760034001c0c8000c0c03052040304000c4800c143c210038148800481042256a40007954103500b50b44030104da070381040c80c02455000c900031044901c0c1505501c02c00c11048034022405020880d02001041c403511040903110104428040b008035040140150b0074455503240c40c401b80c80d4000301804480c9040b07040c014982c18444075500ba000160408014401c405c1c0c0307239020b400e0f1030840403141185841c0e42c800641a030742c1040c107511038820742c011424001950566120a03007840340030b00240300300d10b8044665401400000140c00100d0150282201d0141100d9000101c040c112070041010300d003090001e4405800052 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 588458102 1250 588456852 588456907
    0x1110601090e030c070e0a0b01080903030604020d02040b0304050c01030c0f1d01020304080d0305060306221401020f1b151e0a110426030a1b050a050703080d0e01020906 74
    0x405480d043c2001710b90b0040c50b680c000c0040900b445280281610200c0d10001d041024403000e008500e03c2c04022690050821100141d84024009507c0040e005680c070141c5004000b208020a120000c04c1c110b016240036a07003041103011010050b11401a80b42801c00000d504004400d001040c12503e03481c1000b050040b00e00705695030700d0261400e0056016070001903183c0050102d5801c081103115042403146041406003660b542722155051f4640d04050200601480e41c0f040008080d812200c03192281d0030041c0da6510028a980c903200102c00c040326040c441c503200c4240300403140e180e0501800d81002114541d0043c9a1325038420714001d4005a0312566032800382290090001c0108010a4070801d90748031840f801c0714043c0d100050f1444940130303410402c0480700f0079034010f0504040510302030812100300d000341025071400408540050039842100c20110500100601400303c803a900d1000307002040d102d07451a8281d0060039581c681005050258001c81300c08030022100c40c81c1130f107 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 588459352 1250 588458102 588458107
    0x60906180b030a06020f0408211204020414131401020708072904061e050c092101061d011202030d0c03030906050118180b0105060703090305030a0806010e01110601090e03 75
    0x341c88131002c0342d12414855031002800141084220028000904000c2d000c0301c005000320308420a0408900c0303441421902202070314001000c44d9950303405090780c05840c0782c2005ca030b40b6100410103400d01c40d07000155644002e8005a9688030414022600e60950000b250360404040d0b0307480a242d00040800c0318144948080c40d000f0b030300ca101412511485c091080800e041c0018006008d05407150340c0d64500380c9003404104100c16a001080710504030080c0e40c0008400104000342d08100380c0b000004045500b00381000400d50747c3c2d03c80100c02c0f24004490401d85076a100900d542400100c2d0700290507400c8000c1c4011a40d0050200b2641640a4100898046015a5540100c031030980082810664044400c420001d1521661403080f4982100724009015901d607403000100501c0764034450304c0002200d00802d8840d044490081d82d03c402204e413607014140c0040c0203e602103c00c0750005000c050042d4a135031149440c04c0580704c1101c042d2883c0c0c0d003085540346c06803060070803840c00c0e48000c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 588460602 1250 588459352 588459373
    0x3012a1b0804300f0c0e0708060f0a0801020f0408150f0a050705070203011b080a110f09060705070806060f09450a0b060609060a030c120519060906180b03 68
    0x2030b0a500e00000c4c814518500e035000f4501e0094140d11440d048456407042d07103401c02401d5a000305810b5005241103032801c62134070325000007071009000c0c2c1e0010700c4c2e1075001040c50b90a20042e1000351082d03c60540c2612030f08554608079100ea00c0003181c0306c0058015a00c0420700c908100d5100c80e0700040c451600520b0007c00e034001c40c0c2501d80604044040b10440710f42400c48590014000d604144616014001c403965580c980c0c01d140124030842c405403000040c508280d654201c200d5096070b92200075105031f580d960a0071910303202c0450b03520f07005800c044c140788a50303d0f088084600c070300e10001c0c1c2080f12901a6240601940219903142e25030762800303424164204500f40500d45040c140d03c000d2042051501e0002588940035003020700410f03040c400000c4668a040a403005090320340350018214068020403144400e05072022400c40d450501400100f841082407041ca400380702c082404540c4c2d840600781c003107030b1992268041a400318840180e5006880c3c005d038608150080446001010 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 588461852 1250 588460602 588460679
    0x10905161b170714060601020f0a0b0903070606030b01150f0c1e140d1103070503070b220b1806010f180905010213030c0e06060d0b03012a1b0804 64
    0x40b050003914040c3c40f0400041313103642d0410540d5070142e030a1002d2704040026501c5c643c0e075211002001002990342c20005503880d04204180c4444a0b0861000d000003641c90802e000314020a000e1005400b030b072070b103d00040300d01420705400e166241d0f9580c0402c944080c2c1311076840b004e4a41c042400101a9405074020030b038015100020303440390902420303404091540150031500c201891969540040c402d2001213980072007512400340d001b2580c60b4450380d40c442a02503215070005e841454138120000d0300240617500d1242486400c05011410484501c0401995298024820100c030481080410301c1420003a515542455035001d4021408170980e90307605081e80c0186201000d0042040d50400c184a01900000010b02545501c003200741025404075400d4803845105912854444130170741d0b8161402d40c070513002e100d480030640c44054422080358002640c0403c40c000020405090b01c0c0000120800d00d14403158800d130910b207000d14009804400411040d030041c0c100481e000b04900e40b09 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 588463102 1250 588461852 588461857
    0x6120b0f040c020f010b0a0f06080705040b040b0909060906090703020d180501090b01050d051c0e0303130e1f15030b0a031209060504050d1424010905161b17 69
    0x2c4041d0003a141c10503445100508407401540480d22580c1d080004216030566200801d082d44c2c200e16002d000380d42c80c00c409503a14070841e4010000803900040008184042101411000b84100c40300c42c40da4940340f04101c4503503425100f02c5e9028107000080780d260350103640100024480a4004a00380304c0d40c070b200c038521100600b0280d44507510780640c4000c104600a15a01400c004c40b4046900917064036156034600250344609184d80524600a1040c2d0095a9950008800904599072501d40c0e0a803d071008005206040b408198400400c1c034551104507604581c400301d621403280c0b40c1c13524100f5281c0a1000c00d0020605942d00070080da0b0791034142207900518001c84124552902c090300003040b4070860b03070242007000028807050040d40c1e54100080d0074603800100c80d24490404810583c140f11240c14070b00003c0b880c0c0056500c9004001c1034040c100e440c0c1c00020040c8d5600d904000422864284030300b000140c040302e1460f19495007003070104e105e83c000ca0140348000178443c0d81c49250ba = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 588464352 1250 588463102 588463121
    0x609090809031014010e06010e10050c07050102010605011d0d0c030f110907080c0a0315080a1401020a170406020c0102030a020702040c031104170f06010914070201020406120b0f04 79
    0x254400104000d00b81420880000468010081041018810304045a9044060292400440500f00821540d0703106014070324002d0001455085e109420724800380c203030b50142c0034084c034900070a0400992913006109000850300180c4030b4031b442e85012460300308058420070304250700c01400060000030421b070b800d80d900a148203100c000e034020031a0800102c41e26020380100c0c400e0544004216045521500da6504041d8010400741c03110310119080d00500a1400301c060844038040001410321000101d0250f494003400a40d03845850b0300e9495801c0c1d11900510380302040d8400030042c003400318400d0f40c03540b0034002e040045c1445100072382c06080e81c0c010b40d800e02d4440e8000c201303107080d4035140c403c461884100381010007028800d849040e010b030045115040446100341c1c11001825414041c1c030004450f0041a5116907842c3e00381a4000d003d03d40c04d0068002d905030025100394014405c50701550559100e400c00c40b066662008094076000e84200d810903561501441503443d039001e0301d80f11 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 588465602 1250 588464352 588464363
    0xc010c03060807090203040c030b0c0705010c020c10110615060c0a0309030b0c070b0c2d070606061103030c461d04050417041d0604020403020102030913060909 70
    0x2000c2c60940610701c1c00d038242d00030082161040060200040c1400e000c6000c50f40c0c8a1a844075580e604810003105000e0311101814550805140c030a19941c007003041054400100c440c0400c811f80c000707040300c0000307005408101983c01b0b5400f0400141c0c801820103000d000041000d85800c8400c001d890a042e580c9104074041103034500180100f111003804540d00000d01c041311402c0c141070751034043d030349040034052590440b070000e061007140400550703130303501c9010002441c080000004d00c52800307030b03124a000391001032400c903020a503140310701c1c0030f0501c400c010f10007107040d62550070780341d043d0b50302040c56131204c0c3c10161800d90343c1070b0041c00c50000c151013281450301c001c5400720141c0302030002c45009608001050041d917018159110014010800079240041c240e695071030203c581c425003003200c01c0790210204002400b2000440e04000d441404821902070391100d40520042c0c0c051804024050780040c00700f41f403503041440701c100b00c103100408045074cc00c0d60307811a101112010502030300c9 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 588466852 1250 588465602 588465611
    0x127051e0a08010621020306070c080d020a0e040e06100311040207170706060801050112060504170c1605010c1505040c15200724090911040e060907020619020c010c03 73
    0x10201655a484085180101c5c0001025a250b0002c0e85a90b4004d1101040c08240e594050034000410152055145d070750b0303011540d8400c8990060441e03801d40c130100e4826410203c0c6210b14000102c0c18501812400c5262211a42140d6400c4501101c40b4031881c1c00581c280200b0f808140d0b08211800c1e03c90070340554030b0f52039460303052001c00d841181e088984142c0c1094010410f200c80000140c82c9641c200a0008440d00c0d14a4200710000440c801d040601202094000c2e020300c0c0030551001484419900c0ea0103165074100547d50fa0200300070140c9114088003901350201c20700c0c0c001a80c0503104881501003a51100c44085420801032080c1002451424600304007020010b00c200019400c4401415401e16050401c405008160344810601070240c420b040f8031070003200d030342028001c011007d01c41005400c0340d0309100d810030f110f02c111408000c03010032a03e00b081810035001e007006502405156461402d02514a0051009110b089034208042c10800e4400c2c85030b041084515640401c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 588468102 1250 588466852 588466859
    0x1801090606050f0904051c020a1407050a0f05010206070e0310060311100314160c0b010e1b0304052a030303040c0303021219080601210b0127051e0a080106 68
    0x656540f0005250040c0101030070301c4049900045d1000ca002610b03000d941402c0b4046000300c1c20402a84001403c00030711500f00c43c80c044c800314001003070303e400751801280c1c00d5a4040b5111428654414240035030040004128454840c91041e500c810011b0110b401c0c50304c545240104480d0994000ea032940b1071007010031041d01c3c21556403266208140350a2091901c00060401e55500252600680510b00015502114000e0402c46aa1504000c04100700d6035280107400c04200c0c11a904005064400720902c0a08010300c10743e80195003140081c0540700d40c44003070303040c807181030561010210260080c0110175030b001c00003948298840c01d403a008191951a01a00e02082200d151040c24010300042600b0007455041074102e400d0307031801840b00d40300d900058036400d014030740032448460070b40d40d031000c043c0e010f42118451003000c1c0c1e07504041c1800f0420001646200503026603100c0c1160400b04560b181c00d60344c0486c0724000703442d840c50000c4c0800000d81003403602c3c0d01c00042a51a06c4040 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 588469352 1250 588468102 588468109
    0x6030906070e03030703090b0c0f07120501061203080708040203011107060b0a063b120a031206271b020601030506010f0515160606230a030b0609180109060605 70
    0x750980b900c198015401d2034059034019041502501450a101e0070102c2c3c0d59403101003c1240c0ca041c00c4081096814071070712141c5004c008900c0ca2030940d050b40c2011000a05400010186070055406a0741c40e0030319101c030f82d8101ca07103000c090020f07179040d13480780c1c034020203a0160b01c000d01203d0b2044e9400035480d91900e082c040f04c48459030103041400703040300c080c901c4030b0b003100174100444050081001c60800449003000701103803502c0e50b081d0040f4141d00e41d0070624000040b5500400d0180d12039046004014502c2d10544070140912001c5424402081c0e84504203c200295100150072010400c0424480c3d00d181c495400036400d00103070700c0600100140a014040c06002d0301420804042850501e8007040011590000c181410303100080c4800550b80e011460b50301640d44130307505000362a0344031560004c490290346100c04503103100ca00310a0502d000d1894a003183c0d07000310090855500c403820441c82c2070000300b03260100e01070100c0542e00701e1003c2c407a1240c0c061040200294090804050 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 588470602 1250 588469352 588469367
    0x20a030b0a0c1d0303041a120f0f0f0601020d0f0207030219170307020d0b070c0c0602100606081902030603120304060f0e061e06010e0303041d0615090603060105090603090607 77
    0x80c0e11030b420f44200c41c1c03480c0d032000700880d000da40c13200c03403680c101121016000d6458410181211145a64542804601c0e00142c10441c004e246443c0321020030323100d00b0700e00d400c0b41406854250269021070100f2462500400301001c0107080350065038543c9035290040307014865071441c90880641100341c28410400c008410300c52a5000d84000c504000d02980410100722200b18040e0241015100007044030f442104000c000d00c0e8003170a0214841c0c0d4500c0040c0d515000701e601c5411050600c000840c0e21485090f401c0c1c4110340940c80c0c1c040c2c844a9905c20300c0203502c0a006640c050044140903010204508015130082d1701c0b5500c0000c000b0050600101100d1010020071904e4101e04141700325001a004a020f01103840c81c4450801d8880c200140c0d840710b00d08500310f8241c0008a00041c000c084c80f1074010604180ca254028182c1d505c03020080f0f241c90300041300014540034448400141005000b450780490181050f600c2e10382e0040000701c0c1608101e50080071076008004100b40e1ba5444000c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 588471852 1250 588470602 588470627
    0x1021603050307030e0f040905010b1e0d02150909070908071208092110090506070c0314031009090b100b04050a0501031121070807020a0b0f04020a030b0a0c 69
    0x24490502815036403810b46034401c41002a00304008050015000c5d43c96010314914030f0001003003045005294030301036000e00024a9554800d01721542104040c2c5a01c1162140c1041c0c020440510540981e00300118002c01d03c280c14441c0b203040c44144082d40ba0002d040d80140074548070200b58910f000440c9140160981144001080712038030b081c0000d200c44240c2c0e0000c41c0440d11100f0720311a54500c1b00c5480b00700d44240300380d0311484003a94074204155001c0421140114140e44181d0348184c0c042d21203e500841c001e0003d49030064240e48181c691026541060800f005292407a6a0762a40025511411005d5907104000020b004c10a2101e054140003000034003942c0b0f0815103020000b548407034a07441850706040c4ca4040102070f84020350202c1f0800f5044101801158202c0310f400c0d055204216042f0001c40d01d0800811130b007500005500c06d68641c401c161070240d984403480040b50f2000a08100e0f00308006140200000d5070410102e8894103800c50700280303036007881da801000707013166a4 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 588473102 1250 588471852 588471883
    0x130f091505011e050609030c130e070e01050906011b150e060a15050f0a031e030f020105040503041401112a0109050f0d0c0e0a06030b070315261b0102 66
    0x100380400c60200030b840b0f031044850031900c9548900c14200460300344009400300d1940000110307034141103848168003490300313200342c6422940055154010401400000e002d010380c0712a800001505a61160103181c0c0000150524400014150350b0381c031403030310948078040c0d80d56034a80070760b182c08041c108160360f480550284148095005100c0030585c80c5880e004440c01401007038881a1fa0b51a0180c020008580c401308010609003403c40d482e40c119103503c4100c000070440514685c441e0710500440313000b9034011014503e0245003194211412548404142c1403240110006501202c180070307117120362041c040611000c8126104802c1c0307a07034010078140d060101d0700100f03202c591250440c0c41d8035204152307074948408001d0305180a840e40c1d5584490900d1030308a04102d100310443d041031040300d204000c11302d001e4075042c0d810703015075541c648075142000d40201c042045d448007072030491081311005a10203224107d03915190800700d06005541c490081100c00318181d5030b041003813100300803040 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 588474352 1250 588473102 588473129
    0x30b0f0f0618090f19060c02070b09100c05150403020c03150a0c091203020a0c050105030c07021e0307120c06030c120e120a030506040b10020a02130f09150501 70
    0x1d000031400740c0200c02e0a04060030002c0000c00c040ca0422039620601c4006088440c079800c840b035103601440c10000116006410424982280c0e40002200c2080d02c0c480b812a0703082c12031550070300c0380e05e920b00c51008080126960700000880c000740140d00c0b45103441c2c000c403001ca01c0c103800d01901d007240f00c0030640d001740d202400c1c80c0040205044403980000442002013001d45000000312802d01c407a8100554007181e000d151010140c0000b01000f803d84a0040040c000d65140019541d0b40421a6052040c4400f04804401480c1400d40448206103078078110021a0500010a242a0740c9800c111000c20440e0036001c148141c012034900140000d18003070020700b82c03200c0001d000304448003d11110f1612000704034900681405002d040341c0c8c20441183c2c4030301409000401804082c0c819078007a40c81d001c1c0c44445800c02e4190541d4030001c070340082c04462400d90a20103041100c171a504c840340d5445404641d1001c1074060200054092203883c04088540ba01074411510180d201c450240300c603 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 588475602 1250 588474352 588474361
    0x1218030f0c01021f1112041202010b0109060323010b0d0b06090604050907231c0b090c0901030f0212041a040c0e0c130b0c0111030921070606030b0f0f 66
    0x7200ca407500d88250000864148007084d60001d0012000c800e42101c001158071864583c900c0b41c51403250b409400306400c9031010b80c2c0141d0803221850300080c0000c2c20140300303010303080c029042040529906150800b884021020501c04c00200780c00c480414140050b80020415142c01488103880d000c5442c076141c2040d4000041952045100300b40c00ba121700c00000c1c440c9801a2114040180318422121000d10039482c0b0095981c003414003406061200d0300390b00b0b50240c01d03100d00c216a06c005882d0001a441e130241c142c201b0b40081d480141015128000c0c400146142d0010b4240c4c00078001c1c84135103608092602041005800109040401420301000080342000080e103088440b5501e504042c0d0301e5001540341b02c0e110f0058454010550380e43c00044d4164120700078408420040000c0100b2080e40c610307130185110030b903100803560703009c0003031810240201c085840013181a210198544001e55413030381d0a81d1002d078000d0b2603212440041040303031142d80305c032260300c42003803a0042c04603c2d0 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 588476852 1250 588475602 588475607
    0xe0c09060901140d0b04060b012007140402130e0604110310050409030e0402270d0b01090b040219030f050f0903121812031803030907090e1218030f0c01 67
    0x70148074100d40070b05001000c0c46152121890407000c2c07070f08078541180074906030400602a2004040d22400100886c1001e00b0f901c00b515240e88141c0710b0400607001007480e04015003c04402d441d02640d104c3c0d820456540c074843c580881c01d000381244155655140741c81001c110803510100c40c0802e14000c20000c2010b0400d400d0340d01016200f040f1400900c414240c10100c0d5407070001e400300c039005071001803200042004815130225034203a00002c84115141d00c070030701c82d000744418402864504000c0c010b00c403540d1103800c60301c80e101c0d0141c001400c11045070502c00102c0c0d00480903101085d41e814100802d08080d01803d98003038500140300c007840c01c00c01461030b9203105a020742102f030034101003c19201514403001180200088003100d581003e40200401560300540d003403001c071048402d80d03c006010120070f80e44a5040c01000c2d0050a00e00341c1c0704000340450f607d030203180b801020880d169203c00f16003d032500c224030b0345080c20401d0008050618010400c1151405940300c1001246942e9 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 588478102 1250 588476852 588476869
    0x403091d041b0f0605130e13050715170c22170109080a0e0406080d091e0302030a0b131a04020112050c180f3705062a07090e0c0906 58
    0x1e07011301e00260f4400c0c5044184040b00c00c40d4001c6600e85200c40c041c1b000c044084d10049100b240527a0a480125540b0f008200038004030711800c00209116010180f22450404400d603030018024034441e00e071415000290804440c0039991316802c1851440c180141052182e220f082180854002c1151a00d2520f03a12441d00821505c84104000b80035090015201c942040000300b10100403500703030344203024018020902501034404440340030070100c0c000740b090356410011650041e01521044200d900d810403105001041d01d43d2000e4081d8405001800c1c0d070007010841c0040c6a00d20b4510704117032000505030314102da0700250403420201400441c594501c202c1d2010158454030740142036110011405610404070b8680c1e0101000c0c035009100035400d0700180d14100341c0c00740034990041200b60002a282c09002c0c180e0040300c248017241418440314032000c1803903076107500c100c500d92a0584039858445160420410941c560081038851f500402c16254a4242203902101907d40740c03000c2003401 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 588479352 1250 588478102 588478109
    0x1003060e160b0306010212040506040509130b091606021615120207112106010308030c0405040c092903060f041b03021c0e0606090403091d041b0f 64
    0x380c0d1940d10310340103503041041d09038414004031003140040e9034803006100c0790800c4a120740540030310841f9070402c501c034104641c00e0360001400c190500b42131800340003036200b00034000940644c426104102140245050500c0341910a00803d00c004140002403400752169200b8001d46d07002c40e015070101c90607500d0303500a5500d00c4036400e500010f44801240e285241e01d983c000268800a54801404030320707a004500ca0303009540000128400c0e444106520b5641005608503402850041c80004c0003800110341100d003144409080c9900c0750009004c81e20030b80c1c40607000c02e007040741c10803920084400c1740100c15414040c803103440b035244031689294800200307010b2040540d011280019920759100425401d007000038030f0740c500c1844102400a500c940c00000030400030309403003104212940501c81042e00c005000d000e1946071807003804000c8801400c11018041c50f2000800d03004901c45407504415981100d55030b2a00f0305080a040c0081d00c44040700281068100038050f400d00f00c41a41c085 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 588480602 1250 588479352 588479363
    0x1140c0a080c19080a06050607031422060e01020c0418030513080d0f03060e060a060c02030a140307030e0a03081611190305010e0d0905100e040504030f171003 70
    0x195101c8a0402c03a5110360144002c0104240d1422560b0350740c040700300f40c820003048904000d031030344803c10042c15020345c810040004400002104054442070054040e0b000c00c10498868022840d04400b40c9203c0b81e000140080c07000e5132008100d69040000c1e000c005015074040145900b20b00c0301402086000348003074140b1000144105450f501c8a40c3c60001f01a11416240c62041090000382440fa036403131000c00007401d00b0b40101d80e414101e803004d80078042c0141041e0003a0720f0700206407216203a070242640e0501a0a044601041c1c0d044001e90321000100095982d82a403882c002e0584600c040101c2d02400d42c200040c40040c46a4041f1010491101d0144e410740a1a00d403240d000c9120050103a003211408910302401110301c4184010340b071281c0000e10030102e40065140d40e038445000050000341008000b0031660402100c24040c00c182460210039185c541004034050ba0020f4804400203054500520289544007040405a01118a8020b81c40c00c0507100c04a401c91940005000c = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 588481852 1250 588480602 588480617
    0x30605031e3918100519080c150c0d080a1811041d0106180c02062509081501090501060203070b1609080a0f060c020127030e1c0501140c0a 61
    0x2007955814103110b41c440781240b0404210329001d1814100c0c00700f1403150500450b148040c1995175480740c041d21b07058a000030020001c0420001c10045900702d00304e100807599004100c80f12120206000403100132146840715030007402c2900c8a103003104c1c0081c1c0e440c000c041c0308801e064002a0038540700403001078201c030042081030001c03500d1900c440d1046802c0d80c1540c64080f00150080c2c01107040001003e00910401c400c1401c1001646c032031404840040d5507a58400e01003140300440c5000a80108181c41c1c00088191501c54581c50078940341d05800e240014413004001d0101c80f8081c01d409004a8405141000d59556440c50b2291001c1d00c00c4c0d08852608112000b00d5108a18440080050f0012154440214181041040780001d01903070710038244006c8050450050103285001041031240340081c0260319988410a05003210840400100b4210186140d541c80c1d0b448210507210b803a500c3c0800070524200f800c50702152617146802242c0c20400c100d01145c04241e4400c145581417003070 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 588483102 1250 588481852 588481963
    0x5190803030f0717040f020108060907081803190309020a0501050a0815031c0302070213150306050417030c12070c0c0e10030818150c0616030605031e 66
    0x480d84501c0646444e94500d40e84100800d2241c003090010b2094001c0e21031800c00d403a040c09101001408645e100d01042c851000f25140b1041380100300d80d00800340c402d032424111560592050644c0d01002c00000944a41c031a07415480c0c140c91000084c030090a11070300e01004080c000d01041c2000b4028070361030500603140d1641e6101446144e14540f041c07803907481c0311214203501034000d400c0383c081640144a109030402032180710340304020101320a40c204406d0a0301d107640e14000b82000a104880c1e80f01054401d6005000d201d01840c040c040707040852351619a00d42424000d9030000348101704000a00300d03500c0210354440d0004050340c1000e10243c0c020341e2140b101d02a001216480142100300c000340f42c01d042d0284403041c8141c1c1c40100c1c0c840c0b28000407050031034030600a2441e440c0d510303000400454a4903071022500301480380c540c1400710f42180c0e903400003400c24903559061103039214008080005003100f07000c3d160481000c000141c480c8080081c2c00c1ca0046210702000d40e002c0d440c0d15204 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 588484352 1250 588483102 588483107
    0x1801080c1318090227100513021b0d080108060f06090103030509180f010f080106051c0201110a0305040611031c051308030a0b0901150c0b06010c0f05060105190803030f07 75
    0x20128150050320b80755902c58803e05c0d105000c090012044000da22940100781d030810016800c80031180b0050100300320030503e4040c24003d5000044801074184640010070f0250000d00540781304d4241615401e0941d0314200c85241011002000b15685403200070801c102603a030104a00d042d070342c040c50000c3d21801d141c4081544290100041400c60500381c080204250000d601281a20070049601e00d10315550030308642030f80c805000791035020895090104141400c258405981401454541c221b000e542004900701038562000350000742d4002001d110103604600341c0c02c42a0702e4075005502d0441851501c5da0700c0d06054803009200740d21407012480c800b840d0320740041003075003040059540e4141903a61000030015110014020640b44000040800e4026040c1c20700e540036450301018001107039154003c0480040446048c40008940d0b1f00c085192414102445449034000f04815410101001641180c0ea50f1141b026444074605000c20000401500c2e003254903908a00003986440009 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 588485602 1250 588484352 588484361
    0x40b01080f0a0f0f061d011d0309010504140a030210031b110613060b030d0c0b01050102031c0203040f08030c031e010b0406050903011b1d06040509070f141801080c1318 74
    0x70351060f4403e201c8481006c01e01980140e1800040c0400156032002040c0d01685030b01403250071074081078040c802005002c40d81d00f515401800300034042d2800c583c603035000407010480d00701120006982d408554180c80c012612282c1000590b040000c000d611000c000c580d98030004145050151218141c1d0080104540202c80c000c5001003d44802c0503410800070031401c19601c041d6401c220400001490303500120440d180c90502440782d10142003407041000180d80040c10403942c00756082c0903000402c0014003e5806032044c2002180e03241024501145244008504610000c07143c100401c402c2c64004101c1e0115906420590340325031032200002e004000e600b0800e506003d1070444403903201d84c0848403800000d801010410400e2a60082c011a4000d5000e566045005074021582c9640a40c84911050f1042d140a1441d00b04901400c461500400702d0100c0c0741c0c04034101c10205603044402d40d54051120003081e403e028004120420b81e030142d2080c0440310344c803002c10f5104140356411 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 588486852 1250 588485602 588485621
    0xa1b0c051e0a051005070f050c0304050d030306080c01090806240901030b04140c0f0103051314030406090501031112060604150e090a1b030b06040e040b01080f0a0f0f06 74
    0x240030500e1450303406894042c440b00849060060030562810480c10707100c0c03107005110a50314203500040c484000c0c3c8296010100314056444140400075081e070b60003c4021901e0b100c0d58000c140702c0e2610070b515143c00800e89805041c0030000200b071100701e03400a901584850350315584261265000071581020840b6600290400205000801400500d61009011341c0c0300b40c00388001c040e401c210769501c802e110760301c1e15404500703020060b4444d03100e50012034102030074401d101c0c60041c00e0303903841c00b0b100708207070240c0c4907a080030504212440d0041600c5d00109001e0030107118614200e84442900e10030314100c0c1140e51625004521151911000d031781c0900342c000d001720030410074071038050711031080116514410322a60001801145486c0140328501c06c0c0300c2400582040c03c20400d9018011058000d50880c50034400002c140c20b507458540e015500a005050302395040c41000d03401c1c00e02410000301a9400074030148005810301006808143c0c2180040b14107804903d07280001e020a0396 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 588488102 1250 588486852 588486883
    0x31a010c02090a0b0402210907030c09020708040b0a0201060305070504110d0f0615030603060c0e01080f0c0903070e06150712050f1606050f180c0f030a0b010803070b0a1b0c05 77
    0x7081c21f0200301c0707040c2c2d8410350b00da59010f0540654402c000d00e5502c4507280001060b500c03410200300070080300f640140042c5c2c1d22500c072007130405444a111808940020aa1b00d00603034440908005008081c84030f80082c010980d014488207816a0110f0010f2290f41400c0c000d040c0d0f1a0351180c0000c04a13030000b40074004480d0b401610f02c0c170600e0014054000c5d80802c1d10358a00c1d00301d4401c140350040c8100180400181c4071b800d0f03141d80c0c1c40b055151450b0020482440b140d0308021000071640c091040780060091004a0325003401d100043c8244580c031840d0030708900c401005000c0105517075000880409046182055444800c03502c094014000d1041da1900301e4000e0700b01004204291304582c1c8125581c8282c58056a501c041071100c10300f84139102c602c190860448400707181480e0380e1400035207402a00f04d62042070150745468107048243d1240040d40c20104004082012101d009500a1803010051101c040103c0d4070702e030316075211034616061001164146082120510409200f0010311 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 588489208 1106 588488102 588488107
    0x709050d02090a15081b0909030415210c030f0c080a090c17030319140a0203042a06031103010806041101020304080d030c031a010c02090a0b0402 64
    0x3d0a0031074503030744501c40f02006001840b030b004000c1000070018000e510032040241150707500c04001a2080000d281400240d175000000d03542900c0000c02e44000e50341a510040c4c4411f140030821040780304161005000d0090f442e84490b0081d03619480502102d401c80126100311011303e2124001f040849001c0b44500040d0392000204900c80c81c0000100c58580d410111580700c901d040c0c450b0342d2300010402911400758166a01480031159060000c0e06110700c0050315202c0c01494a072016a0102c002824040070720012442c0300c05411003522454549824542251060f0140c4c40110f41800101202000d1100c2103904030b445c010094906a141c1e65200000c000071605507904510040c000030804010510200e5001407482d01d00096000640101a013075030680f24402c014082842e110411598014480d05000d66046441c04840da0b15007880500a181c001640750300540701 = true := by decide +kernel

theorem cover : BRFrame.Cov 588309352 588489208 := by
  have h0 := BRFrame.cov_init 588309352
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588309352 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588309352 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588309352 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588309352 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588309352 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588309352 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588309352 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588309352 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588309352 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588309352 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588309352 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588309352 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588309352 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588309352 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588309352 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588309352 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588309352 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588309352 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588309352 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588309352 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588309352 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588309352 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588309352 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588309352 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588309352 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588309352 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588309352 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588309352 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588309352 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588309352 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588309352 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588309352 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588309352 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588309352 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588309352 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588309352 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588309352 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588309352 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588309352 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588309352 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588309352 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588309352 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588309352 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588309352 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588309352 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588309352 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588309352 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588309352 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588309352 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588309352 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588309352 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588309352 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588309352 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588309352 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588309352 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588309352 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588309352 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588309352 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588309352 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588309352 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588309352 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588309352 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588309352 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588309352 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588309352 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588309352 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588309352 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588309352 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588309352 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588309352 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588309352 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588309352 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588309352 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588309352 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588309352 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588309352 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588309352 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588309352 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588309352 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588309352 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588309352 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588309352 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588309352 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588309352 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588309352 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588309352 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588309352 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588309352 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588309352 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588309352 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588309352 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588309352 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588309352 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588309352 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588309352 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588309352 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588309352 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588309352 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588309352 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588309352 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588309352 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588309352 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588309352 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588309352 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588309352 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588309352 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588309352 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588309352 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588309352 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588309352 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588309352 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588309352 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588309352 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588309352 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588309352 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588309352 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588309352 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588309352 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588309352 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588309352 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588309352 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588309352 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588309352 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588309352 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588309352 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588309352 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588309352 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588309352 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588309352 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588309352 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588309352 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588309352 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588309352 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588309352 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588309352 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588309352 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588309352 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588309352 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588309352 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588309352 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588309352 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588309352 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588309352 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588309352 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 588309352 ≤ n) (h2 : n < 588489208) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
