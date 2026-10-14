-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1669
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T04:08:44.790797+00:00
-- url     : https://prove2.me/submissions/fe852373-51ce-4a8e-86d1-c827147971f7

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 300000000 ≤ n < 300179856 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 300001250 1250 300000000 300000007
    0xc06030914100b04051003050a020607140f01020310060f02060402040f060b0c011a18010b07060605100e0306010504020a1205100308070f1101140d2a0906090f15080c 73
    0x1e10502c022000b42503100000164940c424040c4000c50700010880711961026510500100b08002090740c007584d41200c2d002e9807181a46049a54581c0104e0707400484e00c84c81e40c4109110138190095440b42c003002d00c0b503402c490b90b112400c607014584424180c025800078008103000d41459044007041e400324420125503240da42801120303070350140031100d4a5955500300c0c482115203401814104400840c3c10455580c048110b1105020040c4031f001a1711030006043e100b001040d800c00c00003070100428011a2910088002e0a0f0400d0411090b20a0241d880046060300e023510a49600c000745603541003510101100e8070009040c09081e050700b443c5076403000800170724150014281d90340300307a11689064410740342c02200f0041070f0f0b084d5818010096184030210044900b070f110a801101408240a03003401c5d0110074880d80101303101100c180d100c2500000310342200c051011103c4580e18091203d07034940b840c0d0f0750a00540240840e8446070304012a15034415440c2c1a08107000d181d042e4038 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 300002500 1250 300001250 300001283
    0x4200f06040902040918030e0603090712080703020f0f060a18050d05070210020705010c151b05041a04050609061e042301020d020a120e090a0b0405060d0c060309 71
    0x10307412503802a4142a0001014049040719004032160a140b000343c0d04014212507801428210f82c10001c1070180c074010002641c1410100904002004200510840143d0b00c1c20846855070241d0750940252260804e14608901700040f0301214500f211b01034a20f0341c40d0f800e14840038000005420750510440654440400e0092200501078100340c2c0300ca030b90303840c1c141c41800b1003164070341000001d54010010810843c1d070040000d03420340d54848006041c94401e00b5070000102880d113203a45840300c4e43c46203c50b2041c2c1140040041d0307454188815a8404a40360454040c41070b805801e4000e074041c4000500303800c03e0005000403042070790b00a03664030014000d608a076045076008410004e0f01d1100c4900b250705030212540d41e29003c0c030213040108031070b10029607150101403000b8030381d04c1c3c4e1600418205110300840c400e5060010026100e034200f020600000e00805c4007494412441c1c000414900d1824000d0900001c1d4800f02d00c130120351412109800038189100706840024020381c40d950f = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 300003750 1250 300002500 300002509
    0x5011a120606061309050c030103120503040b040f020a031e1b080c04090602090d0c0f060801061d0105090d060f050108030c061602030405040c081e060d2004090f051504200f 76
    0x2446087c4000311603440b5803460404d00903030400c200500c42800010003e101c0851890f684071517000740c0085080d2406812072002c0381e82e9802a80c409090210402c07000d00c81c405180003140c507810b00440c40c080c83c2411180962000c01058410a50f0176840003076500c4203801c06401c441c0360320703002c3d180040c14041402d01099410926402c101e80402004400340940f17403004c8a400d0203041c00c0d14142480f50304015010300603d0401001e14418055192034028980c42541144c44518010f0600303c080302c1d20b4504075003e801796040f0000520304050000c2a00b420020175a022a00a20010012601c5000d0101941c94a40140b1000c6000800001c1025100c80c0200324810544d1707610500540f4029038144c50000040811900004121090141c50765902c0080000b03160000905845a55070244039a007464050030800e400c50f09201e40001402070552002840d18020416100742807a00c0da44c03c1404c0c0000c8038000c040b11010341e03c640880ca0381c9101d00c0390f1048003a02018603050f5960005 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 300005000 1250 300003750 300003761
    0x10f0e06030715020a150501050d020d060902040c050912060c0f0a0309050601030b090c030c130b0a030f060504120807081803070203060108060714120a0207030504030f05011a120606061309 83
    0xb4400350744036070a1001003119070324035071400d0603446c070080159504080c0081e032400d08428000e480b400003c1c0d601b80c2446455031107940d131940c0c000c100708500b080d0482c010b00f0300e8124104030740c4170700c00030300700c1d041d080d5070105d00701d0712a206903600c00b4076001c484402c1da009500300d01280001c2550701c615200010740704100c1140694001d0303164544605c0d1183ca000d180030903212505000b0740160452661079101c26450582e002d03c5048003081d60848a070220b81c00a56950001c1c00c03000c0041c04500a0118a81c00705005070b0250102403d0001180340946201070180c03200000a1501d1000405a8140080342842e4000400a80745000d5468001928007a003e0f01312404e15040901403104441c2c0142a1070350443d5107030318090600100301c2444c031000c04000c1c06650a50340024459003054821300c04c54015591010034445520307210700700607000780031090311750507100c0c001e00404200c0d19044905468001002c401050a55600c00c1440b0a903005000e000d240385400c1c580109a0020358000e0 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 300006250 1250 300005000 300005039
    0x6040e1806040b0f18070e070e220b090411220212060102061f03080c0307020d030507032006040f1110020a0213090b0115170a1d0105010f0e060307 65
    0x644603030400c2d015090440101030a5000e00d602d450f003800c0c0c00c0f01700c003007401ca00321615400991000d9440c81c07815940300603544031a030350241045034000c015080100e040d00c640380c600340d0100b00c110041c009220700d000301980c0140456400420841c440c0c600089113141c114688041a44c080d034440040c1c0d800e0b41c10111034244407007154000c2144550713042000603440300c2c948502d00c0c8421a000a2000100210701011304480c4c4009020100e030300b01002158013881d0b000d41885c80710501030400510541040104500245654a070780d001d010f011600e2010120400c005865a0348444d07542032500480c180c1d08a0340720300c020003001e90641c3c8034030141041107110b0f0003400700e01c50a48108662004100400d2540c0c40c900307003401011507039403003206041d102420390300f41c841d01a0700000e0782c80c0c15407446210b0354450048100100307424150883c0f4101c60700e0b02c180d04040d05540c5806070a940d402d0203451031646503818100a80c0503144c0300c4541104c00642990500343c1c50b41c0131403046c0d11907000c5 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 300007500 1250 300006250 300006263
    0x30709140402040b011b060b030c1f0e04020301031208060a18063b0408040302040219021e030f0d0e060103030807020f0115061412100f060206040206040e180604 71
    0x800c002d40c209802101c2c0d01240c24a0329120002070b0641c005111000c03007102601c1142d5806000b00380d5282000400c6107410001d00c8240c421081584041d41d8500300c848880010700c442122070a203040c2070099034140c0303034040754012407091060f00488100d5001080203521800400300018140074080803000d0b0140c0800b8042901820444031040c88600080ba035441d003144a900044d000c2d07448981150221415003440b04d56848505102ca00b50040e50000782d481440040c43e80502800400304a5000e070440d0240d8129801440c43c20369449440003801c1d0494000300034120100d2140c1b0010100c4403620840080c280000f549038a01d0410260021404240c8a0701030082a5030108103041a00041c54002e211001c401044d56004c051184900e0040c401904007007070395154404107681d43c4c1c07503c20903142541d141258176180c504217244910883d01e9001413020414910220300a0f200d940c02505c81403804e8605a62050702d460000d200000f8661300840b00b004403d41401300c00d019038040c03034 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 300008750 1250 300007500 300007541
    0x50c130303020d022802090601020f10020d1109012102041206050f180a020d03031803031406010f09140d020a060207030303060f0e060120010c0c05010609020a1b02030709 75
    0x50700a0316101e40c1c5c1c041075514150110070f0b224041d14110000d86160342c16510142c0c15202e48005070315000041c03468203807600454070b420400320200e0380030f401e101c20681d006000d49440e140c1d00413040d203c5c03104c0050001d64072a418008002c090010310f134007140360b01c40c018542543e81561100300c11002c1c00c11a00c00b40c5503400d00c9010783c0820b0a1035081211881000300e11503c040f0a517030340e5098132000901450742c444500f002d15000f41d110500d99444080003410341107091400600400c0707a00c4400544401e014081407103944200d400301603e440c0c1c1d07103d010038141001419580003100030030f159070010b04c80d5084001030f01d0b04104000180b0440e001051060300b54034000c2d09985140d00036481420b82e00c0c0d0104408401c04031841e40186082c00d12540020748001904940120002149210360034280048105980a03490f001102d00810003004020345036904c400a0340b00d0030f05041c00040c402041c0d0010020300000d8003842d075200804650300c10383d9402240e01515142800c81c45240c0e0501d = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 300010000 1250 300008750 300008773
    0x120d0507060506030d050412020402092e05090d02091503010606110709020708030402010c030c1b03030806030303270312070f0e010c021003090f021305070906170a050c13030302 78
    0xa02441c3d82040084001c2d0100210000d0001d0083c0981e11891021007a40c881c01c1d825519184d04a0703190700342c040c0c101031601001040d049000f030a8014103000003190b5041c90455280714a0958100000040a00080c2c60701a001c2154130340c0003506003d01e0400c885aa6042035a09200c0d4500800303082d20f80a00503102c8082c00d50a01400c1d51003021070b04d00400c13649000840c59000c80364000da0900b405541109141000c07140701c2c141e490300902126001d00944c8203510b42c4440c800c100e81c0301c0c0c0d032010495507421080c561a40003c1d6a16070140c007012051a100301c2c0c2c491000b5254440320000c40b404d00705c049000e0300448006a40300307404070708a02c40c03c0f005a0750004405040700d50030b0074250394001301940810a000e0022000b10105540d64101d00c0c1007040c150601400c05400404000b040c040104210008041c1940c809020400c200c0d4001100c600484a40307089840c40c0402d52010380e80c0c0035030040138140090000508120412003c8130000640d80c0300c7c000386000c1d034010b0141d607586 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 300011250 1250 300010000 300010013
    0x9091a04090c0e090a0b0406020d020c160906060302090a06030903180f1a18010f05120a0b040e19021009170703060c05040f120c03081b1218010e120d0507 68
    0x213007510525410182010000c01c9070740140380d400c0b643c06500140d0f14444140c50800a010380e40b680007a42c0140d16041c800c402e0080d00c0b078002d880c00c02e401008065035030003054040788951203125400c110309100401504c2d000303031b10070807030b281c000d050030880440086000015a60756400668500e41c440500380030b049150f0602403d4880503081c0f01d4a495454111640300800301da504504005864580604803482441074900c5454100811100b0381000d6079090b010317217240d040c024081c51616400a8154030001510502a4086034048503100041d400344003810107003005043c1070003101040054051801031700c100f0002515006070850a04515210041c0c0c2e038000101010041c05100c148000881c444080c800c071400d155005c00c4400ca2032401c4100c0031a2640081e20402c0f0108802401c7c11034203031002100003190052f03c100e0030000c04805c4640c0600c111059021017568007000155025040700201618000c1c420007120440c0c08040d482c040ca00d000c200700150021481d0301c1080708 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 300012500 1250 300011250 300011279
    0x602070b040b1005010509010e0f0303130303030e0613020901140103020f040308030405010c11070e0a090b09070f090507080105010518060d09030216061403040804080a11130b0109091a04090c 84
    0x2482c040b03143c428087c000038a030019000301d50780301d221040005009544d040048581400e003c3d28109125550390401038000d1080090b0264140242c400042d60140000000c0564590007040009a41d09040f5032001000600100f01e0605508201030300400915102400c01984150242660780c41d00386003045c20f65003e01c8003d000d10031040e00101b900c0001041e00d000780e400c1d41c01c100369261f072071b03090000c050007072268091300c01c44d428024040a000302040140070381e04107401600d40f0f556154003180c111a421207119001810b50001030040350b10030001070140e040d003403250240d605d23081c600043d001d5100c81e4003100b2607680c07400c00104068040c40b0701020b103904d0486151b001071410f00d0180c203005071a1032189a490001001400700406481994040c00106003125611241c500d0540b61840d00d68072541d200c0c82c040540c020040041d8055010f85240c1030392801e070b102e49040c0c0b041d0007074104650500e8080209036685c4c045174885200e030b07440b9640204800000c2c01d10b020742c590a444d4 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 300013750 1250 300012500 300012509
    0x51305060f15090d020415060e01021606021902061c0204050a0506091f05070506090a0204050a0b31180b0f01030305070f02180f07020607110a0209040602070b040b10 73
    0x300c01000d01c0403190007210507180f8415007507545612101d01480014002d00300d10580c103007242e41d00440820420b52003102151242403c1e0216084c441a4241c0185d600b0b8a0744200b000681c00002450f143c0032041180040d290b102804445c03d00000803890b1240415450300ca164051b40810100302c14a0240d0f0010000c141c03c1c0e035420b2410000c040400d5103213a10fa520800001c81154000300090303c00c1c4116488940c0107019200c60f8200716524545813012140700fa44100c1c24a0302140f04603405120361441120300411100652008040c0d0020510301d03981c40201d290101c101c0c00404201c2400f80880b9006240c240603c0f16080d03282043d10f10002511203018001010014000650058101c818403a00820f074840011518400030f221070411000315024041c0f50b10501180e1841605418040c0d0965001d0740c950755a2201e007150a41d1515415400581c0094400307805820100740183c1c110303002d2070025103028401d0b100c1009501c800d6804031518502c950810026845441400020381b = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 300015000 1250 300013750 300013759
    0x3070f120e03030a091109010308041802030105100c0206041a030414010c021b1302040b0a02060708090a020d0c1a07060e010b090109050603011d010905060903042d051305060f 77
    0x301428001e9550303a00000342a4001d507952584604140300c102c00010340041001407010089603101d1500d0030f400d82043c4200c10392150700300b540743c80d000554004c1e00e040c1e44002e042c04000c0065a03030121070b90303200000182d030000d00420000c51078103a03000d0500c8a0b40e0b07a1049950303032410075142051072116117003940310035a4581003007600c1c1c0c40c0d80883e540c429603900c030b0542007a0210b0200001c0c1c20302400c3d580344003010320000700040c00c0c1100e00007424946000e90213a404039a50304000340c400c0e1504481c000084e800c05015500189031003911001954003650100110507204c00c0780e000b241c03164060040504e08041000d0040107100c0c040e18040c210b0705402807007072181080204164002c180190300c1c4584e2204006082500c3c01d61001c0d215000c2115072854121181103254000d0440801c1558a4059540001d500410000c102c40c1110524070340140304461603121004540c924003030b40140c3c01e1115000080e241c2e03c007590100b00528801e000501030410310300300020051001100c42c000c = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 300016250 1250 300015000 300015011
    0x1b020f0d1b0812041d0c190c031b0c150201060e3301020d11190813090203040f020402030601140f0a08180a0219030204091103010b0603091c050408010203070f12 71
    0xa4000c1d4101c05c101d508200076a00300341c031010020704030742c066000c8500c01451202c00001040e5031017406004060b01980b190700c05405040f11400060700380c81c0001d807011100c450100701c54410500f06080c010038a00c0001102a158070346451181400d5410017281280c4824913a05081030758911001c515602c0c402130464554440080e44031041c2c0810341d030074002103075600226002c090001400c064058101d50100d40b8240c6001c000d650000400303480000c1d07045034081280e4603140308403805942c103c0c0440480800d03550070000039600041c4214108621710031020318140003c405495111480101076403a168411001055907a006000b4654580150540c88001c403020480f1041e941d0191000854151f881080000c030040580c0001c1d0031900e01020312080c0240640e01036401c0d80300b28001d04c811755420041044900041ea4001420381111000a82285a5050920944400d81400c42c2041e84c1d40216500320b8000f121280042403036104080c860741e81c81072030742404078801d0744100b01 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 300017500 1250 300016250 300016259
    0x50a02010216060c0f03300c020a0201090b0c01020f03010611010f1a0409081b0a060b030703210311030901020304110306131401060308040f030b01061b020f0d1b081204 74
    0x180304035481024044040d062007484c02d0521410b011f40b40c0e81c8071031f00d0741a149103058090107a1031103845038894141d480d060602a0322440030a1510050b6016500d842c40b90b800c10700b2568a0b54400c00b0009100d65003004881c0c56105800080e5009085a807a0740904000d040001800e4410300c00450030450310f08510b19002d01070007580a0310540302038500003621011890450501e02c9103080d00703180b60320910440c03a080031000490314040d41c0b0510702404200000020300d9600c0017503000060107001100100044410300b121440e03402e00c114074000c20301413508210301c50203a00980b92021503035000400c000901c01640920604840c0580080c0708034035118211891040f0052001400300c00c0405500988540c02d40003240a180c020360680d564a94492034840a5041031104640e070040b030b000006880c42c0241c1124001121100b110484860150f0030400d0003c0a40f000d1607100090200e030001058694170390300084d051074400e42010a00b001e14142c40c129450f0321420001808000600 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 300018750 1250 300017500 300017507
    0x1050301050103080f0a0314150315060f060f07020910090516081311090f2202030c0d0807151a030a080a110f0111030f1312050f0f0304050a0201021606 67
    0x500000d518001a511074a00b0306040f000740848d007604100a80900086c403c00d0300141041c4681c2000481c1229050784a074006181059400c07100f480e403000440007903620300e080500c0100810b96242e20b19030700c2c200c0d140e40042c04030802943c213014211115141481010782310700c100ba0b08030704000c40600b124900900003d0940e1001001d00d0f8966861400080400030468000d104079007000340003143c60316080f11000c1c50400c04440ca0081078044160246800000307124214002e41c014000d0b10184032000c01340f28580e00400701c00ca07075480d000c00060300491141031a1031411890801c020683d11002e11200f000f0402441400744030390084101d80c40000d4480c0125010b495660411070504e0000951060500c051842010103650902c2c00c11a52132060b0030041d88520100c03c4201104e4a41214580c00c402c80000300030201d0b41d0329644882101c0c01440600440569650020301d803c400d1030241c4030075082038404549551000701c4c20021507030188050492200035001d2030254038504000103 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 300020000 1250 300018750 300018757
    0xe06090a06110412110414150121050901060501080604060605070204110f0f040509130209041b08010c0e04050a0e10091a040311070806010f0e090a0501050c120105030105010308 78
    0x10107030340da40c41003141e201c18001c0c1507030018440706204042404050074500c2c41d03804080911803003070f450700c198400c0c050a078000c0240a883c12108c1c07007440d88003e84c015502d07528503640c20212902c030310f226031000c903c4a02590384590040317030011410520f0540007404900d03001e050f031480b641c14118240960f5511005440b84103404940120b075000300004500c1d0f4620555080003406c41c00001c41c030010b102104014030481d003090360b0030140c1c2c0e510321b0a0091031400705100298041c19a03004103011542c0c5281c4803400da00c0c84c041d9034102c1591040300d10308503542514101c000c0780d10000d010a16262078882c4079031041c00c080d0140020800b0082461702c4003041207030b002509540382c102c04c06010b00e80365544041d4100a40c6103920742020b09000e85002410341070416144124000402e444d48086200c0b8102c81d0384000c429030103820000d0010f5072000041804106125010507000400d409006107405107628104150341c0c3c28020a80f0000300394143c06c628066818500100005041079044 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 300021250 1250 300020000 300020003
    0xd0522060207170708070b070206010e0f040c0e0a0e0601080109030516030309060f020910020a1e05030d022206020304120803060402070210020d0e18070e0d1401020d0e06090a 77
    0x141d56080502d810401182c0c100303c41080001d01090490802150318000c00741c86015000e0700c8859618241d040383c0d0b03200240030340702010505030b0112781c0d002c041d00030303041d086031203070846038400b54490850b44440442255540c0c0210b444a0601e450113005001c09405052018000d005020707154030090000e115007124042150724136581c14042c5031080d03000b10411a40303c1c1b42489840700c1040344034080e400aa190a01c9606441e9491780c04034000140e520b00700342d021012682e6040003a0741d94959804440094540d40000c11031850020b10700e02c01805140c1c4004000d10000b034984070241c840c142e4940000d010f643c41044140009803c061300c4c840d5944e808484070303a44c1d80e11403000c100a03015a40c0002d4100110007101d0b26040d03000315984002c8581d6584e900c0c010b180e80c0d42040f12011985100042c0c0c0455040420900e0748240898803040d5000b501c02000102e10741d03182503292456909408030769501041080003060360303000e1011080c1982c402482c2e070307090001e0660303100c4800c2e100 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 300022500 1250 300021250 300021263
    0x60403030c0320092701080c011214011a040b0309070f15080109021305030d0206060103050604061404020901110613030e0d0525050a0b1e0f030a050603210d0522 71
    0x2105c1c907852840e070b40450800140d68814018a5964070140ba80c2e40c0c010780c000c940401c0b800030381c81101080500c11941c444c1d40010386081c190346040411003401c284007030712070740d8003c041102040d480301c1140114040e410b11b20040501518203540c15000300c42c503420104e07107010300701010f40320b040d0b0041685064800741000181e6070304110150070b50030103499100d01d416000d21441c2505c0c2c02c2d00410480d20a440c01e8034244a01e5503131f0020001114468011880d107a501c00d95200014109507000c2c204043c018102403000c60b000e11015854214200c0fa40c048170782100e103401081562100110051a40645845c010078126595a540380c0201c028401001154481014000449542100018003024101c4035005071296003904159102081e28090504070b0360500041c0d1441e08102c0e01020300c00400310b41147c5881c0250300c003400c0f0140003942c2c1740c411806180c0c0d603c240c48806408040300c22203140c0e0303500402400c100a4540051a09104002c0c01c1114540422401d41c91045203a0164 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 300023750 1250 300022500 300022519
    0xf06140a030b10081510050f07052103090f010504080301170703060609020a02070b04290415030501030201110c011b050307050601091e0905100e0f060403030c032009 73
    0x440c210002e0514454036070740648501c5050365070341c2c0c0002007640100726295255010661032020310840c01c000701d05140c00a03004010000c2a030703807020040c110701031056094546540795226864512000c020000441c69000401e001d1801d40c00c201d014004200c18009008c1842c040c2c81d1440e00380414426080e01c021410080a00070302d0074800328001e5540200708100160702c404008000390001c41c402030145c13045a80218429100c082620201c0300382c4c01280d0000382010002d51101c86c4511070101107050f05100100b03903c000c01c070b01d9412036005650001065855400010303d98040f00b2840c48054004d02d881e01a540da0142010305080d410030107401c00e0f18942d107050740c550301c10100c01a090340543c0d07001007000b4a054201e014000440381352202c2e03013003030416a4030813a027040c40c0040c400c0c0d00091588080c28815040115850341040c2680e4440d400c1e820030324280a0304072000c0380043e50710b0079985d550035054030501d589004a0501c654410100851245282c81082d00b214490544903 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 300025000 1250 300023750 300023767
    0x5010e04060b040b03060a0b01110a02060307030b010c0f030c12050331050f010905120c03090919020703080604150506040b07110a08061b180112021608130f0614 71
    0x4d404c510794040001c0e04841c00c524041039400700410b03405180320700180114514a00642000860b00c21a54005105500c0c586452005074010710725050391506100e000680c1d0408100c26010080d001070094548503030520941c6810f44000b50b903007440e0810b1003010f0090000d1341d00c032160b059003030a000e000c04000010b40d1003040303151881700b403500524511840c020750381440d806400504003280300c1d00496869014400401c0340d14003c2a1a0850a6006107c402e001f49014140281c1252141d510320a50011201d50f80e01030381d20200d400c0d4040b694043c10b120b6181024801d01043c4044480c0c01c1000c0c43c24000000c0f030314440c0f8411415034480100d440c2040c17211584411160910044c02d050a860740c8103c0c868460900f11a0941340f15101d0083da240b41100c04220b50340c0040260b40000c08040c58001501c2c5003211700000036a0741e50a002003500300540150000059000c6ca234080d84901103c41c0c2540f241c610740d0404107500d02520010400640c00c0f860900200301c004840f1034a5585a = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 300026250 1250 300025000 300025009
    0x7020309010f03060902040f091b1d0a0e0103060b0f1903080306151911010204033809100b0a030f02010c11040501091a0906010909021308030406020106080f0105010e04060b 76
    0x11501702503071103032000500040d6040c85081c182c1c100c50508a080c095000c240080c05449503010041e44003180c50208490b41c0c41035903c1c2d18800050005022090f21903c9604c40b035801c0009030000c50308540d036456203104615007443c29542041c011250003003040f46440c00724050100500c0020b000f0903001c000314509a03a03910111007840c00c1d943c1080c1e107444000803440c00070026610b10001141904c100c015000b0b0040c000c1301d00fa06e230410444101c8000c11400c024098811606071290075070001d010041e03c00b410500503000c1d15049005065404880020000f22001100c4080c400c4400c88400c2000034030502e5905138842d024200409c05c0340f02401c2c100f082a040312902c81c3d020f8030b40000451842e0180c2e00607819024100c0d000b00c002d44601081c03209015094521501254403804104110310164005160b500c094011201c00d26944002041c03541d003040d08001d025035102c06083c00382e258108050b04060102000034015940f4044030309511181c0600098007240c0ca036010707003800d5101e = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 300027500 1250 300026250 300026261
    0x1c11070b0f10060915020123061e210109060e160509090601090507021c08010e130b01031407034e0f0302040b0a03050907081b1309170408060c0307020309010f03 71
    0x200d00e01c107002c2d200203448440348c80340400c91f000c0740b04200c4400000e10401ca0050b82010351040504941003030b86c0c2e00c0e0294000502e607220241c03010f42d2910445400600745005000c1c0010206005100380c50784d20886e80c1f14060a13421443c0201c10080801602a400107201811943c080c44005031944900100301c0c01c003050280022215644225104440707076000420034100c8442141a03c5240c4a80301044943d054503140a406005940018400314284624224288200c00e080305d100c183e50780c0d079420090507a0f489000e45501d450300d0b422521043e07007084500318816102c17041203040306842c07110350145a02488030100001c1d124501080c0b4040c1c3d0444000d4900d9a60345030700c130b0703204150007402307132404561f150340f00c1c02081d0002550303041c0010031684031210141a08000d1100034140300682d080b0400e005403541c0c81d894000b012420b90755000b12074041c4807002c2c3d5070711802d00160740d285c240c028000b1034106c00f040007003040c0e155001c820383e0205402443d04000700000114120007402 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 300028750 1250 300027500 300027521
    0x7060903021e03040603060605211519050906010201050603070b09040204092a1b030e150703020f06010e130305030a0608061008100c051c11070b0f100609150201 71
    0x10b50b4400141e002c0b0000081c000716031250340c0070711240d40c0b00c00341225603000d18082030311500f407028503c070340c01d0b02d000c1e0010342d0002441481c030500503000d8001444209883c43d4030714a08002c40c0f001e105608042c80c0007036220038280000c1c401800e244011071f41d107814034070618007508030114200130390790f030f494040781c005040da082c084c0034207001044150f2101001002d00c0d61284031818101090602425840b0b5502240100480304954203031804d440c1c004c0d441e07100550144114a44100030b02400300503214041c0254020312754182340011003440c1c0001a0020b0808a035000c0c10081260180c5810401c81036052030400c1d181c0e02c9038800700000d030005c1c0c4c00c507041c0c03801f031002004006001c4d176900d03008541c00b10040780c20741d00c03900e002641150601c81c0310000183c0c0c00c0104901c4048105049131b10603045101c0016030b0b038204404224190044001118074a1041c001d101c4510956030072581c002100460f2290b120b0728212015050144521a5241c84044cd59034011414001e5102da08901c = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 300030000 1250 300028750 300028783
    0x7050f060a0b09100608060d0201030f0204030308070801090b030a0809180c1e0f04091d06071806260915190e0304080c0904020f1806040e0c01050706090302 69
    0x2414041c1070580a0000c441050f409400d5500c00500ca03a940502803808441050b1070791102900c46000b8016a5800304500761b050513280d00c5000404650382c03008000460099646444904026500802100060740500b400505000c120201a03601050000140d644441803550751106400414000355912021162100300c08080084402d00c0c04001d25044842413182c001c07801400321f9500e654010084e80c031000c04014082031050803403a90006108032940102d60400c0b201c044582c0f45071040444406000608141507800c0a642d018107200c098510390038103541000b400300c080790407005c81c5c02c01c560004809001203000044103000403a0001e6120306000084d00c0c044d1520070b4a00740101499040340c0c0390030300c00d0142d1031005c000e0301c0540e070f041006420390401c0305040041d29500600300b03991102800c07060711629614a6540001610128a0f4030018600382e82000202c07907a0408684c0d550f040b08200144583c0d014003201d0310240e01c10070000b0500c555003400c900d8242c01d5260319590 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 300031250 1250 300030000 300030013
    0x1107090203100801020c06070206090712080f0705030406051c0203040803040303051005031005100911162f04050703450c0e010803041203081305190c12021507050f 72
    0x6c41c100840c00c40d214200d540c084032001d40300c01203410b81d507090030303c54031140c040800c0003540081c0c410002000581030030503146003800e0560f1581d03411684140e00110120380005600c1444151103a01019030302200b40c804c500314909a114001c10b444010802000c055860340010703280c1011075405c1c00603001c00340c21140880040050721009140503204148202c464090014a000c401d0041010800204090904150740000b40110410202500712030180c030840200c0c0030407a08400c124a00280304180010b01101c00091000f1200301800d2a010981800d0b4a045c807800700003046e0312200c031401c0d1350079480800390700d4041c10300701c152400b48524112822401c00b4492140c841c882641d00d000304503400b070f0360f1350b1803480d0b03886c4940c0c407510401e410603090300c0b0080303802084d2040d845a00759200c80c01c03102466680758240100541c4022020311482000c3c424440380c901d01402030140c25415100140c1c0c203800246030032500d12041525640d00040340800c0041c140031089031200140200e449 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 300032500 1250 300031250 300031267
    0x608010e03041a0301030503070210030e1606081b09100207050d030504080609071a070318060f11010501120b1e0405070e07210b03160e010510110709020310080102 72
    0x4aa07481446500891400c004001c164146000c00301c85c100d990000041d0724200141d0b0a100282600715090000e05584111269070404180810001c0070000c041c0d40300002d08045001d000900e015004c00420704101201c1007940d80315004542c12040203c0e80000764080e0400100c1c5880b4103500229005070340d080646080641240240050f111141e040d00d541d0344e500d4070784a5450b42c240c89021015286c0c041c10011181c5a40d00800c1518042c4c5080c85500030807800c9101550500c4d8400b400046804040c850040c0d400402d450a407042c0703100a20155140501d51400c0f0041d07880040c0c050600c2c1001301700051454040d491b039604842c8003d001c00c1c038107070400035110002c0f8800da01d04c41e0001c1d0000388542d8400c0d1030014601880c44c0001035071806050b002d0300240124140c9540501c03d18845078a141c4020030321000905031122014115810402400f02065280c41072900f0304c82580c4801c03e04c0340b00418500259000c1e0300313005813269101c4000b21800241c5510000301944001803001 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 300033750 1250 300032500 300032503
    0xc0f030c01090c12030f030506060d0c020a050c010c0b0f1f03080d0501060503010308121b0c030c07060509090a05060406091109030d1133010f06020d2a020102010608010e 75
    0x1a07a00442443c403005540781c80104844440c0c50000b03000581c00f041401ca918020760110f80c1110000c1d208c107040401c250310110032510321b0410180940d014814000030054200010020a882132030104036140c07941c1d4980080b00e030094082d01c00000703050006103010740700d141c81c035080e0241003900c4440c07241e40b41058425a40500180300440d0704000010803590302510403a4100e9030320040c51840c007041505036504509000d04070181d03056400440248082c03080001e011103407501c10203141c0e00d0b003804a0a0b4980b055a500420903c502400f80781c510727646900440d6401070001401041c20340e1200001001004190031a184561401400162084c1d00f200640741001040d8111a90030442c4101038032619140c450030702050713010f40c407a00e0008088030170f86005034140b030011f02c010840c0c0e00b0101800c03c8090f0450103105508540420440b0307030400c800403152000c0e007082c7c00350008001c04960150b28481d10645410ba00202c075004691003588584028086d84000f005080c0174648151f = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 300035000 1250 300033750 300033761
    0x1030302011b05040902180604140406050f01020a0f1406041202250603090309090f090312050906040201110307150515040608060109090219240509010f050c0f030c01 73
    0x9600640ca04903090301c041a0b40c0054624405964980a003414507000d0b109000c3c0d44049694905680252210091612a01d0107000030b13150480a2582400f50381041c4801c8030f056601661040318a90041c82260b42c002c00c91400454221981e20009003050a25131910070030400010040d2140e0000c01003804101c6d410810084c03610307402c1d241715851003040514040d031203400c41c0d40e400d2203000b010040c0034000d50002c0d030403030710034144115a035907a01040d808650110080411081e220802d41d0100355200403071102c40c2107843c40801040c101040d006907100d0000300024113014810200e201d40e88001c100341e910b101c0c1e00108100c820040c060106003d400180c8585117600340b000c10425203440c15002e5603068070030b1000242000c0e03180611400103003100580c2641c00111911010318071408140c4c90074050541c6034171101c4c40b281c140182c0070b400b06181051108002e820322109010380e1f0b001c1c2003040207031410f160031903d904c80d44082c1ca040c542c04020f280030030b04c00060701c0f03029110190001c = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 300036250 1250 300035000 300035003
    0x5060d110c0d0818010b1003020a02280314070305030402040b010e12101104050916090315090c050a0b090f010324030203070501080108120c0c1210240b0c030702030105040b0103 78
    0x32000e01124041e0824240c2e43c41d80071b056801001c030b500140000344617030301030503040b1050b1044440c560590391185000b003104a481c2e04800e40c603c1c3c0d1290915400180d041a135890300c4510034a84231145e10000d116000c0500024400c1d5140c40c2c03910708580c881d5042a005c008002c282d0f049040708805850307964040ca8070380455850400071402c5140d1b04080982e4201c81c406400300c2543d9440343c4516001c85e4034060400c0901c00c2d0550302101040c0c40101e6a82c00c9036194400003600030103030600f1227880d180390744414407514601c0010720107400d100701500c044800544118031040350342d03c0146c02070012a1030010506080501075140b070180d6000903c00c590080d03050351a00d54440004440c404800d00a10000750f0000142c4443c0e0010072009107415651441980d40c404100c200084500381101182020f580c018100800301c08481e202e1013041100c044180d080310310070f80046803050140352190400c1d150012482d040004010f03c126901d05a00400820072884c00e864404080d5070203000 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 300037500 1250 300036250 300036271
    0x31b020a0b0c2e051e0403050322030906080411120106050406050405060906090c120708190606020c2403010801090b0c130e041505011403010f0605060d110c0d08 71
    0x5103041d4465080c207020072954240d1440390080c4110074840e038060400a0014807104400e070410340c800203800d4045c01c0c09240310f80d464582d81d081c445012000350001540090407400c00c840c03510000780e00403403814100d4200341403114007a0707200c2c2004525030b0303001c50040c0d801c88103074000c0c411031950661100d410b42d07a0455040101d1074584c01880104c1d04120784c496000f460600100303803240307004003d082e4000d009030720052401d60940c002d60708800040d0784110200342d84034207000c8001c0303140c03404042410400c2c0e000c2040700e28212000350307030b420040603940c02103201c02d40d13031840044890000104066112510759803540d54442c010300030464460143d5071410420b0100d52501042c104030348a00000305584a000e80c10102103180a038406041103030f04170144100c44104034901d000c0d82e802030140da007504942e00441803e0509640d0a0f1f03001d0007981b0303e444070070301c260303a078074429140e411071404000140030745002c3e107d629500c03841106050a10980c1c0d6002040c0c0e83c048402071041d1030140c0d = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 300038750 1250 300037500 300037513
    0x1b080708010e030304080403240c0c020907080603070306020a120e210415080601050702030f07170307230304050a121106070f110105130602070305120306030703031b020a0b0c 77
    0x14152a100e0000340ca00406401c03081004101143c04500229446510030003027042a0112315003001c2154441ca0300880440c0301400391030305503e41800344a610801030f051030398141c03601400091f15440300d80001000c00798046100074105100b040000c1c041c0710040400c01c00c861038940503658402e0300c2c00280a000c105540952104480307001a1801c85602c2d00c0682d8241c03040c41d8040c5c030040d400810050400206028100150b50104040c00c44c0345031002c00340810300d0a0480a0307680154096819080da4030810001c0001404000c08003c0303980308a03d801c0075031713901e542414194411b580c4490b41c02541464080307601ea500302d112114803840b4000e0500c1d400061030901406024412000d00042400c0071020085811240b00184811052420900c2c0902c1140a0010300700203812640041c1e02a50041c8104001042401c8400d06151003e604614222000a03690b10303943c000201002203124005071094440761110002c241d0040003070108c1d940380e030346615042e040b1306000e010622401c2e = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 300040000 1250 300038750 300038771
    0x2130b0a080a170a050d05150d080703030c080606071e06020c030d1b0e0d030309050105090d080f060307030215040b0f0a020c010c0b010b070503040801022b06080601121b08070801 79
    0x300841303038114459100e15041c80780c4040303040001e040081400c10f03000808010081c29a48551400c504103200c0c20f82e454a4007410b041c000c044920143d200e00c00e0000c84024400c6d80e50b500002d8511450340b1864048a2510400c06c0103580c614540c0c004001e0303800072a140355200b5012001d481c0e40c243e403040030003460403a00c6072007034a4801613100102168886602e610300c0c0c2003440340d202c9554082e08001c00c0c0302041e50345003030850740101c0b000e8141d40c010b0751056038602c2d40402c00ca43c10200420310000c50307040480000351565041d1000900c605802c949504d2140414410380b3300420503800666141d02001110107541d500841d18900113000d0001080010760090036046c074210f803c1b03850040180c2c00e00403200c90b00e40c0048401d492501c028071002600c10b100340010700c081d01c000c03490109800e911445c0c141e5600f2160700032502840c10300505104440d07000484c141103800e00030b03088001a00382c1c1480c00030b10102400c8030030385400d0001c0100d540320001800f5400c0329820002080380741c048 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 300041250 1250 300040000 300040043
    0xb0610050a0c06050a0b0a0602160f0b09040e0a1208060a0806240f0a0b04050a0f06020303130c080a03080f0c09060403080c122b021602130b0a080a 65
    0x41010050200c0d080000b0140071440590065a00401104002555041b4403000401f0790b007495014100523401781c0c0c40c4c2c0c02039209609401c0d00420303a52038900f00541c101881c0405a0003841030003406507540e045c820060000800000c01c40980180508143c4816110b006000800c102e0350180682c88841000030000310004400d0301c50b1642c50900007156004d2100b46001d40107000d0055440321181600c1452503803800003c000400d43d210f6203941c1d852400c1d0900c00420110303800b0004041448130200039040d008400c603580820a1031448140f40528500f00046198a4100825a00c2542060350415401544c828020241d282c600c0c40541d031a042040640d20550383c202d600100241f208000182003640907141102d19002615101080c0010a81c51900312030304115102001140f107072003041d8803203420034022610007010740c0380030440c0307154800310004014028001d011032030501c900c00380c907075110f456103090040c51080c02d1950f614840d40d80380081c81043d91822145c0c1e80c6403056101 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 300042500 1250 300041250 300041257
    0x40609050909150411030709060f0b07020303030f0c0f03010e040b161407020a0e0c0a1103090a0b0315040f09050c0315040206070813060c051006140d050309030a0b061005 75
    0x1c504001d00303200205484101071200050000c603000c5030b000245c0b4026a80611800010b00022180080c43c40d18191500c44104007550145000380c1e02003102d0805a1000300032664071203c109003140c10703902c4000c11103101c1c4c0328243d07640c2c58140c4040000324290a00805081c0035a001c2d10b1418a01c1c0c031039000000c04040340c034a040000c103113503030000210325400340040c0a00c43d000401118255659144503c0c651008503807a42102c58002000960240c11480c40c000c50210b40c0011030516071300c2d0b4086521a8694050b800112b100400090115018408943e51404024000b40049100541060b000c0c046101c421500c0d80141c1e0018107145c103001681c50070210301c0c00180141030f1030f42d40030b004059122500940e010384003000040c000100100f008002041141d541d9031101d441818098203250138110000b801605200003003000440702c070100c0c0407102080b01c052548900a107801440d500c20014420b401d8000c0a03101424400201ba01034400c0e88140d84046071440e801c501200c0610 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 300043750 1250 300042500 300042511
    0x180a061d15030109180212011e050405070b160f080913050603150405030c011505040608010209090601120204050312130e090d0305060a03050a0606030311030f0f0702060f0f0406090509 81
    0x480a2004010844990300640b100c40e117646031076561129190007040f01c01c100d20b212405a60f44594081a40300343c0121010807030b6821500402c480d062139a6100d4030303141d01703100c1c0165401003c1001101400046007460034668000380c0490190f54901e4400c2d02c58004009903807140700400d070900d2150f185401164032646004004d0300300307420552140c80c1c02240c003070020381301ca00c000d01c40082800000d1242030440662100b82080c214500346c100700981c0c41c5078111000613401401203c0c038544a00080a420403401d00f065542041c0301d1803600c000b4003455101c940e062194066400600c130104000709001c455041d00303aa00c1c40e8403034007002c91003001036880c82d0f202d0703000c040d5800100b44070340c0c40b958011800070f1805000555075140c1c5032401c100800240c40f5142e80311010010903401c4032000380b80e0038021025509100045041248034081c140001d103070340030300140034411950b5074000c980e4000c0c0481e00081d161803440d10f801e4410b4110340901e80110b03a0b001000b04103403a00320f80891088 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 300045000 1250 300043750 300043789
    0x5090d060609050703021804020703170901060503010b041a0906061908090f0706050414041506030212070e010c06050c0c240703060b030a0c2001141006080705180a061d 74
    0x201d24040c00020340c0100816010849855242c0d493321844000c200d0141c151074001141e6a41000c080600311111408007034482d0f4508020003801a10210070b0140303084046072221415681c42010985031b103d050300e40c216581d5203a008405003900a80250301070041101194001d1362080001a5107200d07500802d80800c0041c0b104114400355140342e2500c08602400201c2c440c01c1000b0128001c010700d802c0381010a8021501400f850384010406512601501c7d154080504000018050200d503541c01b52100f6100c04c001a0140091001c5901d0024920211074000c0c01810005400c0c2e02d500d24038035021020749001ca2100c61080c0501030948140e042402c2c5940c80d030f444400001c04001e03030031200f17000701e0503441038040c076000c2d00544296060100111300c01102820402004030002d102c40c03822200c542c0248200c0d607100f81c0035980300103541400d582c3c4a41154460400d240030b01551070b441005140c3c0421a0780e80807001c0030f4003800016503512121440ca0412a501d004640a680c3c00e = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 300046250 1250 300045000 300045037
    0x617010f05090408070602030c0a1e0f1206081914120a0e1804030806030c04050103051504140a030201200306101b06050c07030908160504050705090d06060905070302 73
    0x11031410035081c0e50400c4c440c80619240c41d02955031700c02070340c100300c5000180600102d2004001600440d40b040401c403441040000d20991880240c1b01c0701d030050580040180041500c5508140760744640040c0480390704440900e010704240c1010460420003c4460040d01c0340342c40c4149400042a042000b00001c1e041d0920400000c11100c4d41a2202a00d6100041081210750403a80c4d61950340250300030750b1a000140380402c103040c50180c0480740715010b103213002c0040000c110f0100e80440c3c44d44800c0c0c502051600c030b03402c20400c0e075210004400d84034002d81c42c54108058055121b03844000c503004140c0f043c1e140d000140c2071540401c86407950030411503c0350309062840368030480310711191000110703961000c2c0e444140403141c040318200038505c00010100203050f08440f41304010f09031400241a0031485082e40782e0108054811180241d4880c0b021851240c020000e40e400910041e141c42e04d680d000b800e104000d0420f0744520401980343c000850480b030301c00d008403140d4840091803001c0707 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 300047500 1250 300046250 300046259
    0xb070c081206011e1e0c1a18030a05090f04150e1501080103020907121107232109030712050a020910080d120e12040603050c070c03061a0303030702070617010f 70
    0x1030801c805805c07074040000c000e2189000a404505e151103120b04148020582d1400c3c126045000780c40b003032998082da0080c0401d154695000c0111568500c040d0f6016408803013901c0820046c0c0340f080e070500301c802c0303400c1e03004100c1181a440240c4139080440c11110005071841c010f441e149c1d0700380806904030760800001040c1d540100180412a8400700001460904170501030b605a003025030100c4a1400000c181509c2c01c820052705118006580081c0207940740c0f00d4640d075a505001d030000c03004e1200c0403c1c0500300c6c0e0317420701c21f00008204800480071902c80324549541c5822a664040748142c210801040f2110203050203041683c204500409542c101500c007a6460105050100701c3e4a80342c0e0794a0340f02d03840138010000e6101ca02c107a984d44403801e040001c4c096400042c48991013040510814021811030b450f44022207820881c001500510842000c40303410450010755027500c4000284800c080d0700240e000122242da80c2c40c0e1400c00040d0340f682d003100c0000e10480300b03034030b03207801d030910 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 300048750 1250 300047500 300047537
    0x2180708061f18150c050106170a140c030601060c02030615280b042402030702060d05071b080c0f19030e0a090f0204050f0f0d0b070c081206011e 64
    0x2070420700501c0301c00f074584d5844040041403d10011680700040110503c001049000d000f48000b40449980d8514010302d1021282e42d1404181c1e005003c1101c0b44000a41c2a00c0c01d01210b440180b0103006e60307805684842c800381c0440c0c0201c03003c0340203110703420014026480400d401c04898030000c00e481c0408600000b1100880f00b130030b51000c040c1c03010510006200c929000180020700e007180030303d4035421003540412522660a0a040295041040740c2001655000c04590036403540a40008050f29150011503944041d0342280903580c44201e00141030040d000081d1120000300070480f04901741e2130b000e02c1c2e101c0034031000c0b0000002a45220300c000030f00074041020031681c0075103040d0456940d0700c001015120040d500040c100d80c000340c2401035051a0842d9880380001752550381e407815018002c200c3c02d05c0c0080c0003803c0e2a800b1000300e81650320400307500e042c40390000d00780741d12a0700002201c014207a080c0c440502241c1d00c94120260100105c1030198640025124186420340c800c0210 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 300050000 1250 300048750 300048767
    0xe041401050111011d0a05070608040b04060f020c0604051b0a0b04091a0306040c030b010e0705031501030e0304061707030902060f0f090607060b0f0a0f09110702180708061f 76
    0x1ea54817900b00c03842c500100c49540c0c3c07114400c42d00401d0380801908000e41451100d401800802004000300800f141100d01d40350b41041e03100c000024030709084031448000380600f202e41a001d024400901c4140100015404006480c03c1881250307150f00c4c0c000c0200a04d8944280d0750501d405000400c0094180d5200c40c90302060240301801700c0b030000001a0a01c0f4003158100c4560205100c2030050050001e81c0a02402001c28110a035041c00203014141d40001803041d07049652144030b00d81c00364404d80152007007015100840361030740d4903070f400035001c002c00e548000d1246107a90b000440782c5100e401040741c042d4002d02014941880710301245565400016800c0c2824000c0089141d00d841c0c00c1f004000b0940102c000003010301d110003c0045040016242910072140e645090008050b00015002111030281001404241d20b40e8030a689010f01500a588120120100710380b541120200c1881007a550f0380b510850755651082050074260100c0f60109040b81061540055000e440303034 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 300051250 1250 300050000 300050027
    0x20a0f0f03061a0301060e090d0f141308030406051e03100e0c1303060504021804051911030a030e0319030806011202120a06051002060405190f0c150e0414010501 71
    0x1200350f0750038a1800b0900703544959006d0400101020100016408244400c1c0398041d480c1c078200c2a08184500002c02540b01051240140c2c0c200286038401040512680f40003000a1815243c42e142d80d40005031407a00031008001c20340c000f034000c14a080b99004102d9100d890340c02180f48410781000c0a06803005001420b1524590f0f0800203000d1a00d03201c0802d070019442243c020400345040e1060082102841d00400040e13442e0900f0700000800104031506c0214900003d8100c044c15810b0002800c540040400d4150040000d03200038590310002c0750368100410750407034500791710140340149008202c05001d0300085070803002c618030390322452808208030340d940405802c1c030b019259a2500da48060b01c841c10b401d0b540b64020080360901502519089096001074085440c0a8035440c0e00c3d050280032200d003010b010000c2d001005041444400d0854010307461524031030316844045c406501d207901c05004560a0520f45003140790501648140d0f440680c00c5800e141d107045c005483c404070504c1c0 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 300052500 1250 300051250 300051281
    0x17070c050f12040314060402010c080c010b0402072009040302030316050d0f050f070504120213020f0408060402010e041b0f11030a05070c0f0b120604090b13020a0f0f0306 75
    0x100903100c01000c00c41c80c000c000300146038543d11451850400300001020001c21900d8000b10100320250380c120b000a001d440d0041c10107aa0b07000e000480301d0041820b500d0140e80648085201c505104c201c58101d20b0141000e0403002c0c2d0034008404100034441c003103c000b40140e1007000041d10380031134a164072115030750504185041404690504007500c1c2d11700e000f00b28103907465041004523042e500c1804e4210046c0d00f4514541410180b07203e20103801d80e10060b008201800e0b0030000c4c0440ca86c110390b1030004038445541c4a540368078005841c1c0c0ba058800341d000480264460300b961815100300c2900e403035019902c540c0021340003000e54003420180e105500b03021440c04072801d5040d02384000e1020080f0390b40e0786543c840d210702d030850039002e55410070030000b05008824480c4400d004229052645030310301d00d9580e9650306c00007502401c1c0d400710083c4890103020901c01c4c1c1139003041588400c18400c41d01c1d80c595075151100c1c3c2005148034441d402d01c0c1e640740c0304204003040c4558011041c1a00e81c14 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 300053750 1250 300052500 300052513
    0x18040f1101020a0b0a0218040203070e040506130504050703060c08060604120312230108010b0a0b030c090d0c05010807230c030c070e040510060305031803100908030a060617070c05 79
    0x1100c2100e240403c0b2102419950000307240c652148001d254055840400c80c8c0442c01d40c00c1c000001415403078044099400b440d69000482c841d541c2e02c0c3e6500705107080302d2030140180c0c9410320f08662201f40e03510086038030301d0401000040240c0034030010362040d5030141806041919001c16a00444000401642400440710590005400304d02800c110710203890400f03501814440a0740d055004144c1c406202a4901243c10b4165510030400390111003022486030f45070349a9003131041c42031140119443e80020a00003000c100083c000185c030881d070098032103154036a1840801e540700a0381c42c07102c50707410a00c03113130316180c0352054009050014075030021a824400e0703510700645005100e400010000c880241040104181082811000a6400001c3c0480c80c0740d581c4142d540e00600844201580040310111070b079440420510000c0c1140000921214425007005040e55005451090280c4d0421502147d19030003070b410710551000740390512181d641e030100c0413a400b210303d0404503078501510 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 300055000 1250 300053750 300053753
    0x6010e040206032d060f010503100308130f0303090617040f022b060510080d02060a050403030905150403030f0b06030a02070302010603020d0c09050a1a0d111e18040f1101020a 77
    0x140f29984902000b040a2032241480300c1001b0400550044240c1003110400c10040100e1851071540e0441e940485200e0f1200c0131569450210f014a801030b510000200c20000203156100140400700c0300f0301d0301e81c880a400daa80c540701042104a03005040b1136009103a4100504144c4817000c035982250500d000d801c0d4a42440801d561043c410695a05d901d4400307010510441e407007803200803d03046005085902c0040d0020f074503824020600740089542c0c000140500d4020740000210a60003010354841d0030004404450100080d541034000a1424070301081c00c94031407240c018202e070300909007400d55071800c500030042c6d40002030440441d500c410f400401619140c0e03900080ba1310852240300d640381051016412584020724151610f030901d182a03841804004121135418015907208480361040c0c14078051240d0118007264001c04240c01401100d44c0c0b0380d005c242c0d1000c044030f2202410303010f1002d24294100c04c2d1000b1301006040142d400006060001c1c040107840180107543d000b0849 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 300056250 1250 300055000 300055051
    0x7020c0a0807051f09060804030c0209070f02010b0f0a050f0607120906260103020f0a0e0a02180a0501022e09030503070f180b1309111b06010e04020603 67
    0x880c0e00c507a0866019150501281c6403081078044204004095882d500320782507801864140c0500c24402403100400200e024184200303001144a90040c0040840d400c0215004041c2141030a21800651030404840c065150030100e402e0364010040030180540c1c142410802551941c3d124030354042000c1044d440042d100301125216140d9503201e2204072490141c020f001c0725804000182504107603c0c2c1d01e141c003c0c1c807100c224103603a011340c0c0d0103c2562f5407501160301400316420840209211750108510907030a5001000103402021207000c21034100818400340400d98001c1502581011600494541c0407108801241c0403d40d1858004041c0c54030050484030000e80940c00200004204903109401c50b041c015400e20901d000240021481e64003a00641503001e0006144c1001074103039088104001d05174081c103e0660108000c9035581210103859115036200b48100000490281050b07001143e9039040f2900c658207041e45945035807c0003595880184000519041c00d840c1c0e600343c094 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 300057500 1250 300056250 300056269
    0x30d0b030115030c0608100e180102070c150f110c0d0c150206070305060603040b0105060901050c1605010809121606061805040209310624090506010903030c0b07020c 73
    0xc443d10000369040c8100200a83c9000340a244000001c10003002023103a20320085510994100320121106000945140a841004005440a10382c00c401040313640021568003030084170742d02d0b0003441c0c0500c604203807486513a1680b40d00044d001149a48a00d082481c4107444980c40784d05091906070f1104c0042141c400c0728a2404010f910041c00c0104691300340c840c05c5d4112a040340e40900b5031a0503954032000002c1400307141d0145501041041d41c590240342600d441940b43c8060380c0450710003442d0f58165000e240b28644c002100720002c1040c0d000080307600c104644075001c081c1e18090032860f0404188620350b40c210303020b594480e400103130b070120f5000d800031001062001180d00d0034503004200c146100549004002018960001200300010b80522545441c1803401295002242440c000800c008255a602c2c001007942d140000d2040000c0313102a40e800040400194440c0001121064018080200400c446160300400300345852102d03a4031021910440d400783e40d503000800d0380a207 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 300058750 1250 300057500 300057503
    0xe150c13060302120622090309090903050304120507050601031b030c0612111303020d02030a02030304030f03110a020604050618130b040b0d1a1003050109080406020607080108030d0b03011503 84
    0x2540498881644d2045a41a94102500302c4014060b011600c2a600482440e0300c51010000d80d22001c8908050041e40c143c03001b0402008104166291800d001e442984201c500703c528a140a0031440c03003d024a040e2800c441d00301005000300d0f0308598400540950320b100c0502000201100080010140740748030010780155600c003607000142092903025200d0a49200307113440000c0c00440110400221114200ea4040354003103852219800800d0900f42013203006905400001800f0003401502a100c0001c03a1082e40c1c0e002e60f40781142c0d903003601c503036502900940c810400c00c41000107241150141c00d1207012101c646851744036590024144c840ca07412030355005600c40d0020340091070188298802070905840d1008990450b42da502090440308900e01c9441040e400801c3c000d01d40303815081f014542c004001c20118086050601440d00b02d840380000505c140000142001d114032001412101c00100541c10042c0a20341d00016016046000b5050b40d07a40e012a40d44644010380071000b103 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 300060000 1250 300058750 300058757
    0x203090a03111005100e100803160c080303091e0609101a030d2303010f030f080c0a0c0f150215060d17210103120302090f0402071401050a0e150c1306 66
    0x601c0c00c208486006c400030682505c1044443c400c2043c3c20001c804c0326450320308016000440503251a040140403400d401c8585603100c04000c00c5840c40002502c159103002c0e8003100116070341c001e10010340e511001c80b2440318540202c2d54101c403a400a410003100e03414446046502403030100040b0745071a0304c2641e0400041c40600110040b0300b00641e280110781d030410f504070302d15030501f140f1a801070754510000b42030008016040d001d100c52081034400681c1200305803201c3c3c0b201d41c00c0440c22000180110300321500c05110008005491144501c40381c1d0858014021108024803440201e20340182081d070400c15450341e520001d07004620003160b0f00b00501d83d083e1120381c2001424209401c0c0e004080d0542d400c040140b02007018190852014a000d140140e0348141007004141764801502501d60080e00100e418810400d00c0840140c108540c01b00810681ea1085000b9081d2414520b01c95116045866034110503d50f0181c504d40c888440101c03d450518901454601054143c2c0800c001 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 300061250 1250 300060000 300060031
    0xa12020f13090f0b0d1b0308120121050a02130b130203090d022e06180209040b03011109061629010503030f040603020a140406030b130203090a03111005 67
    0x190801c6100c0d11280c0700b5800802c004100c583d00100c0c0e001010070702c000d82501d03010101c50002c0036030f2590305009590302108c51916000c1c0c0900010300c0da642805048812590f104005460000080040310465005030082c02c184601c0c0d002c4c020310000ba40d82d49100c1c1616200a101d1988400030780d15081502c3c074034016503070f03d00443c0e03e90070080d81048940441d044400350000a541446c01881781c1d44c00c10500d18810480812030400400345e83d400703031803010350080140303900e20003680c080c0035541c8050340e051100f02d0401d01014200d03201c0b8014817040a43c24880c00646040c0b0901900021003500c0c441036441003241c440ea0341c51070500c0c0d400100b140321a5203801c16030011a880781d004240c140e0045007000041c107a955803d0269010707c1c0300305940459500300c00c3e40300b01207400b94200c9104045a035a91502c1000303014000080344980120722561600341d80102078401c607441160500081d02890110b5601101ca034a00103a05510354800d81009100300e0340e03c1c2c07240a0003003040600c44200d = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 300062500 1250 300061250 300061259
    0xf060509040506031203070516122001050105060d090303110301032d11010f02010b100807090e0c0403240e03031b120109050c04090609060911040b0a12020f13 70
    0x160342c03004041c2c0e4002c3e04005030301d884c0740358031300242c98000000d03043c00c68488100d1004420400401c84c4e000d0108411041e0000b003c98000c0091466603a01c21100080385d0700c85a5542d003030307d000b0b1180070380140080208104030a0213600000d02244249404031300801c070740c16070404542083e00190786a02c000c01c03803100d00c0401d04c2031150b5441400002c222525056440310104000400c80082c1030020082c01c3c40320700e078403c0d4840801030200034000e042181084138009c2200e1401c8912901080803c000801c8284006001e2446401b551250f50305d00741c00c55a0b008861800c01c0104000361140d09801e128558250240b02026090340c4015522460002980c2c155000c115000e010002c501300112204000c418030001d040d518450300c0032038240c80708450211607104aa00c43c0322420714100021401803050340103001298103142051007155449a41010180304612904105c0041000728441e03460103032042d002c8408109000605002c05c440940706294840301c3d081c030045c15803880900 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 300063750 1250 300062500 300062509
    0xa0819170c090d1b300b13020414060f010e06040b070302010204080604050309040c05031e1506071104110a09090b0312070305030601030606080937140c030318190f060509 75
    0x4034242c005d105845041248201c0c042200805801404617030b0a04e0000e41c0c403900c07000801700429805081009140c030f071400115003061040e60800d10811200300509041e6109002c243c01b90745006102d64a024a004890001c3d94046081101595000e110004054000380b0035248254000c5000d10f03a24440c22003040210340e4000d401e0385c1071200500521110000b12601200740d000e14042909564480030805a11641c291811541c4030310001802c608020b003200388503010313800598080c0b00d40e00120224045602566007968002010b60710104007a400940101407102405001c2e1140c100074500804007540c80258280c0100c0d8001081c8034095925100754001800940345c05002c5040c101c9206840303100180c07110100c40b206081e2100c004d15045581400b118010140e0755001c607651400548035030440107000c105024090a070380203820044122840c1c040031f01c2c00244429294420000d0300d9003284003d009820200001207001811420040c0180c84281c0b0303040e454005220800 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 300065000 1250 300063750 300063779
    0x40807050405041b061e17011e0905011205070504050402090402101704061d010614010507020f1206100603050907030b130203100e010f0603020a030b07110a0819170c090d1b 76
    0x94200200d1108020410312810313107c030705450101240c1c903412501d40d0314242c1c0b2078107140c00c040d1310b05241c8000064490b0310050342c0c2c202c030391040381964003041c0d603002000304440301200c01940083d20507000400503d030009042c071482d441d0b030803c04418101d54690781409042290125992aa039241d554148050030150546044100c0c000748440c2e07003400301e0941482e50121406041c0800403805e401107680d5040e50200c4000054031000074401503000381560b0303000580f203007115200d80340790200b803281c420302030380d442403203808010071080d461943c80c2c2c0288040140409100e50340b5024031801a48d042c0729541c010200d00c80003240122204074083c2c2101d82d00e0782694100d52520100300010b0b1190702c0641c0031650007a08080a03646d403030000b0b4418a401e049070b20468000c10002c10704000f5180041d014101c074103d10880115508001901c4441c0400005040d18142d00000b5803c000008010400c00b8030181c54000803910300d550b40045c0d542e02031182500b200c1041024040200c00c0c0420 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 300066250 1250 300065000 300065057
    0xa050a0218090a0803090c150a08090307031d0607120c0302061f031506030c08151003020d231e060a0c0503240603040308100803040807050405041b06 66
    0x2225801e0400304016030f602d600c5200002d162000c0400020075103502404403984c01d020182412242c00c82100c1c414000d503002d0380c1c041002c5200d290114034500000425180300039071545800c0d18508000c0840310071034440c0410540d12213070400090303000884122180d500941c09480d000b01c4506280350113424818000c082d4116203211240741e20700c0800882002080340d8115000512695440e441c0720301810303a6800160484481c400c0c0040d00410004034030504821001c4108841d407941e0701408014445840003a602440410400d808110707008486000941c0c4480e00308418906c44000c2820300c000040d15490401c44c01208248199080c1f00c1668010030805080000902900002d4010300010b0305659407448495110b40c9107a50121288601800c0141000d8172031501d49402000a502180c590b0780c030080d4000006410b5000000ba00c0680d89030314041d0801505190910004040081003500d290212500804100c08045485405040941d846114031200030302c09402c0710341401d01c0e = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 300067500 1250 300066250 300066289
    0x2041a090a2703122a0e030a0506090d031802061804090c0f080606120d230301150e19060f0519020a0506091605010509040e010e010209040e01020c06060f0d050a050a02 74
    0x80592420110700d540503586802c5e82410918100f413080424030304400702100500754802c4400344460454009107030032a040301550140805481803c2a045685070090025003100083c0301d032200d11a10300320710000c1840d025100142d0b214042e01c400e1141c0c509a4071001d071302240c21300c051240c0e48003441032070b030b0041c4280d40c18110010344400041d0349121800c0360b0000c001681d0f5543c8006440c0c185003144921840780502e85951b181c0541c00c1c0803c203c80d4501011400c80c805008190910f20740e90722000d600c48480a06c15403800c00261103800749100351a003000410001c1106842e101e0303068070505951a8010b151808a901e0305070301d0f20101512a002d564004010743c4612210032405030187c80c402c0c07078a151070b401401d0201d006000084c20100b00340d402c1500075012650158040d10456008560a21180d10480c1140f400c134030a2401d41c0751944c000c0c10008015007043c1c03c10000b9808007602094004805880b03d90034480709480c12102d1350031849401040d032401d2207400284c480d0020 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 300068750 1250 300067500 300067541
    0x601150906081506090114030a06050f181602030d0e030c06010506031b1e0c0d14040303090b0702210a06051501050703030b0a08010905070302041a090a270312 70
    0xa03c099450340e652207148120000100404144d1003480030106103210588419140e04003412040050032013802514018880050017840600e8072182f07403803105180300c040c000203888200c1c0c10541c010b00c180125040d440104000034000c9090300c244022000c03428042c607105e03144102610308084040c0d00140c42500d0034424130450745074140c003220b9080211050030340e0755042c0c02c8400c00480e036140700c002c02903180032540c0c004070000451700f4162080c45e640e441a00703600355000f8060314052400003800240721040b0600ca0307008028010180036000a00c00101075118034240d61071f04a60118482d01d60304503014070000c10055000c1d850b00048034a842d100c1000225000928034000d551010f0105034031400322702d80c0ca89480c514080030b0400600203000030102410030139981c4040d8072089028900e440310714940703412000107a4010200c0140290b0702e68442c6444140a045030311182c1c2e92020300611103010181030103015410303840c800c0c2c840c81c42a0444080c40350403907040107c1c01041d2060700 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 300070000 1250 300068750 300068761
    0x80403030f110f0403140d1e020a140102031501032c0307020409050d090f0b0703180b160b0a090203150702030d020d0501180c050a180506040303200a021f020f060115090608 76
    0x2422a20400d0300c0794040c1d2300118047d00c401c0740350510a800c0500321300c04001c042c0b200c62006400441c4507c4442a41750720351000b03c001141200c00819017004015100c0590740c200200307041311b460210085200322800c040c2181c00080403601004001c4613186c0c01843c58008964103c3c4c09030340140080b958030002a0729041d642c442901c0742d840010208004007a141c142c0503014080d00c405000c03502c990584941280c5282c10740703141001001e40f641da01c40c900061094405000781503c540c0c0c040c010348485610441100381555001e002242980003d005460700300b03c0c680f002d00042070450001180300d505d44a01c0306000d4100000000344541080c40c070266141e005030803121a901d261922565280c110f22582146d039826822103940a10000780010906600c090140c01803c0418200d4464035403e2702890b5444151010080d00140401c03400c1114851194104000442d60b005940d20944030079862410003000741c0050340318002c03034898500c0155000801c41702a180318142070000f8200b8 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 300071250 1250 300070000 300070007
    0x7140304081804020c070b090316050a0608071e09030b070305040b0718080307080306041d0a020d0212010c0804030f0509030606060f090604090e120406080403030f110f0403140d 78
    0x30202c44100400001c2e1103424152200e504551280c440202074494081d1201d10f902000d0f4480d441007071081c41104003507400021111100c0f8101da40080420b480745291107400d031061340c0010000c400b4400c00c0c2c0d0f00000300074101000802e259505580c1d440c80d15013149022000d50f40041c0000381014078040c1080001842460b0301d43e0402079904207441f401c203200681040a0102d500300c810540404070300b01080100da00701540c010901110103210741a01d141c0342e04241c00c13450b149800c19500c40c08100700035040c021301c4031824a00180551011102c032115060940b40103900c20400200c00004001c140341c1d210100ba070505e5014600507103818000f80010742e0760030001d00b230184144400280c00219159601c111822000050601621103170380b5450310000f040b480443c60882c3c013426a034400740000160031241625080d40700c00322942c440340c40840003003803103100241f000d695507000d098841d0306e1223010b0114200d100314910740e164158a40b020041c4240f802c0c102e82039020003588004a40c1 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 300072500 1250 300071250 300071257
    0x2060c0a0e010e03070f0e0a0b0d020d2004090b06151318020c0607020a030207062a05010f02030c0d0b03120f0c07210b0f060916090b0a080714030408 66
    0x3801d1810f903580241c8580001e04100207a0b100140c285c069400018006010034a185d1044428000070401e426640090165070006803000030351103c01d51000b100003490082d1b1406954a82c1e1210a0741713507010340c001c0380031500c004c80d043d2440b0b082c1e0001c01490f4034103500d2184a183c41c05078440c0c10003010019451408071580580440c60751202000c483c150401e5040e200d071104032808580035800d000602940b03400c1104000d5005010720711000c54464015130b0941400080300c1c004951450410180c0401e10240080c111101c0d5203402201403030307403150b00207503000e00c0c0c280010541c0c8117001c440c0342c0708950000300e1950003904650008132240b1003600a1704c1c0788207101e042c06030355602280304003400c2001c9030f00f000c00000f100a03046142d4540c20010f030340741380f0300c41c6840440c0d070340b01e1010016182030708640f040c1d4881840c000151303c60403481c00910360b50125081645514bd1a034104406035040100e042c40001c3e0050304000d2050740c00300c40f1000035007021030201c1c0b40d401e00343ca45000c14072 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 300073750 1250 300072500 300072527
    0x1605060f07020301020904021305100201140f060609133306030b060d06060f091d010b0a091206020304020f010903080307050711030d030533090702070b03090105060102060c0a 77
    0xc0e008a9100d0a545081d01240c50070500280110750711b132201c088500400503140611402652504107400c40680140704c1e450010200500b07610b81540c541c4d000103d00c01e40148400e41110040c408484c4ca41c0350386050308c03049400c6d0300c000324429403041f608002140750100c090700b00d01c1100311024140c0d455410076009980706803401142d0b074801900030030050321900031040652440c143c00040c0300c0354409070003820126985d0f1140107031503507a11121442481d03101040381002208c0010003030b50400a0041800000038105858819501d01038501090b2460038252021600002000304524068000c4500350f8401d007000c1003006d0560b02e80c1344190000918107810300c130000610405000603480c009494200040444200103090803000b0b000c1c28042d5404000429054800350070300041038240d01040c8000404000400082d10802c12020700107840e080641c0119007020400f985018011071166801b032001003494140a000246070440007090000004401e10507008400c2c0d010559512a0 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 300075000 1250 300073750 300073777
    0x20606010f080a2708040302040b0a08150421021b03030c031803031207020a1a07050d050414070f06020706050301030f060c120e0a0506060d030207151211070203160506 74
    0x401c0c1c442e010030500b90072204881e62030314007162144c10001504018010341e8802d45003070201c2c000700b60078003014040e1401030034100e4004140c0003191503003540200f5840350082d114541c0c00266804400d100d031815285903401038011040310201025180311003415000250001c500d000e114050483e101c5c002e415004a0840702c4c3d070102e100d680d804000b9554560b501810300b0016003480c940c00f80d80c45c400d4141c02c44495014164200707400c0c1c2000d4402c0d100341c2581e00c03518030705030004030480700901300140300320f41440c000039080d80900400c1205c180075100c07101420081038100b9201a15201d6507034040300c20400c0410041c0005210940c940e4007071a40301901041e0b0040c900410b0b52461552064060000d1819280e03c0b0b4110300002e1244c41c050040c4c0035148907486807000c2c0f05030480743c20030150260740465002c0000d242c104a0a070603103200e0785082456010180703800c0d01030300c82503101383e424040041a40c8040d860300348000c2e0b079002c104485441d0380703518001c0483c0007070042d01134180d40c4 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 300076250 1250 300075000 300075011
    0xa020a0906140d0804180e0601151b050309060a0c05120c061f031e0f08031504110f03100b030903030103030f0302030702120a050424080105030604050a1b030203011b020606010f080a 80
    0x400c00a40047c1481c2c01840c094481541c0c40b144000b056100c00c8140600180c5c0315406400c55840c0244589845908030b03010310b14001000042c4005c40e40300c15410010080b1500c401c40101e0780500c444155444c45078a9107a440c00060211442c20401400c0c500401c4802084800701c1c9640403c011700316a13000c2805801d1015054428105081c1302c3c501038081012101c0c14010810040001d510403890b800140d0031440d5800e040c0001c0350000c0a03040c40f5072100f080845030310706080000e0341d44407010941c82038000d501e842c5281115002070303031041c0c41648040014410540c018081140a00607803404505616007400002e54030307a1039030011103101c0740004d08034800b1071007441210040e00601400342c8403455032810780340c03803561091580d40003e01c51a002140034600481c401e80510341010051040c0c03406030701c510b0200c505908100610b1400e10a000006071000c1c001c04c0808140100400c0600c0000f50010b030610720002c0000b810083c1d201c20b00e5044542010609170802042c2c1030000740c = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 300077500 1250 300076250 300076289
    0x18061303121b0201090309080c090612010908070506070305011d06040c1b08120703180809040209120f0f0c01140f1b03040815130807050a020a0906140d0804 69
    0x2040c001882c0201c0141c0e1401054029405420a09405100303903203c2c48406e0741c903100180c0380d0465064440d840032884002c1a00c5103031001082101030006000029400c4440c0e0b03420010340e01036a81122650811001c015810b030b05842070318010b100d42d200d484454400d2602284021400420403171045030780e910005070351440703620f102e645000c2c0000d00c1c064100f45410051025004112240907180c201d10025044602c40d00038400c1241c45881800e44180765550358402540040581980180d42442401c51079561002d0303401c4110041800b800e050158100c5450401801200f005201d91080014281c01e0340d0100c1c160340e030441204801a200c1c0020451790b11148075569503081803d000f01d031000c94880000c4014022969860b00310b0308401005e190382926410100c5840d0f00c3c0061003400400030808c035100400d40d040c85402940c2550000e580011641803180e080304408a6076600240f040c01760050080360700200031038a03050a0916540c6001d2140b0480c0140c1400402c404001742 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 300078750 1250 300077500 300077537
    0x506070f0f05060c0705010f060b160611030c1b0a0506060d020a03020a03030512010e07050706020706090c080f210a0e0d0f0b1506160308060a12050618061303 70
    0x1101e103540700c07040d166a8100015404d00030740040c40280c45951a15000303920644c128402c450840d10302103c80c60078a4400342c103030080480025426101d0f9070310f07041030480041c5d03a0002075102c3c20785c0f9644203403585a12003c0c6480d41c458010b441289900c202e0085002c03d0f000140594452011a64652000614400701c1d0461001e988003e40104103900302004040d00701002c0c00c070501081002140c56a42ea10201210340019103000003c0341d8100803803000300c0c3c0f858004002d800d001e40c40100300c02c030303031503441c101c2803c59030380940102e401401e088a2210000d2000700b000d0350000c4002210381c80a000200d24034800d10843c5400c2c4501001d03104165150705012410103604000600042c0075541440d10040000312055540d03000a04c3c1c04d00c005240c80f900b0354402407038510030017031404000c3d602070712580c2c00a07004991002c040c1e400043c8550004003080b00c181d21500c0945882c0c01c0200052010a0b12400e042400c2c1e08410200240e003022405034907140c5805207804a4009900107204 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 300080000 1250 300078750 300078773
    0x4020708030103050102220312050a210b0a0914010e070306050907030b010201110301121203061e05041406090f0411211006081f11040e07030b040203010506070f 71
    0xa0454034007000000038000190b001d0407601c01920b200198140391407203040344400c4a4040140450304085002e401036104401034220000342c0e041c4000c40c040c1300e404500e018404615032440b401e03258480494541044884003009001c558402d00864180190038035041e00705019800303160310380100096403144a504010024100035010200070b0800c0300b0024003605c91079441d07501640c202201c00340105122021a41210340f41298011007410503030f50100c0560360030320464101a211200400d18021007a086902110b40c1d5256130022494181400251a055042c4c1201c1c041501d04004664403291041daa02c1064401c04d0744440c0c1d19440d06c1c0640c400c0058006401407016540841103100403000031441c4c4041104507005802c003c4040426140c041c002c208554101c800c04204400c8e10007840090001c0940c004280032007240310002040c0c101342e00541c42e0a000c001030006898152043d4203059605a4042d0724540c1480003042d43c512a4580c0240050460181b54091044a6048 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 300081250 1250 300080000 300080003
    0xf02060601020d030b1c03050714061302011b080a02010f050114060a0f0c2013093314060910060503150d0b010609090c05041409060a150306230d080306040207 70
    0x301ba1041c02420000c11640001e841120713040040580e000c403003200040c4240c170500b014144140c0034011540112401d5480b00d40f00c1c4802010306036540002114040a071944011942c000111504d204036160203455040c1c0c45924020004061880c15440320002c840d0b510201b406d181048269034078046684520000025000c1301401a28080c0680c1d05040018082422140e0001403c0384800c00812915603003001813103958541c0c060042516000d00c00c40c01d4030b0b00c90b495901900e65050104060700c07210004901e00341880d804000c06032900d0b080707154002c2d503449603003000b260400340040e0003844003a105c23000c010070401040c0103da0701c00e0300345045181d2000c0c0809495960740c1c000380203500c1502694911b64104010441420b00c217030180ca0403182100c180c2c103e09412001440036404000c2d000a410086045011400118541400e2a582c00036680005c0082ca481e45050848186040c900c3d020b1500418041807030b99402400340f10b00c1d0f00400e00544e6502c508000800a10440c1e00 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 300082500 1250 300081250 300081289
    0xd03170103290601080103060b0f030f01060806010f0602060f0613020c010504030206010603140105040e0a02030703050a0309090203010e0a050606160f0215090603070c02040f050c07030f02060601020d030b 90
    0x4402c000381c0c466998499010700303003104001c1e00880c054001c41a4100d07020790000e2a0080104040340707440d08050800100074051600c0e80200c3e10101341000c03c21005900719a440d014201314002003044030a0042c1074020fa45048207003441d0000f500e925001d00000b65461800010864a0303980c00d0032008281030651086544488240003a0f018042c100c405034050b02900e40006021406802085003000001c522040e6aa0900c001c0000800318a0400310300351140040d5580180c904001c0300010794002c03001007520a039a407900420726041c540140c28002d005200420a00c105c10034a51b40040e40300b031020505641d180c0220b2920b005859042d481d50101241c203c041c41001142076078881d009480d07030380c442040f11180517042c0c4540054660801820000907801d10705c607403d03400a60b4030042001c264582c8024031035064031420f82d2038070b180c040001005000c04d6000b82110544d1300140c000303054580751090010791074580c0f28030200141a01d41e1031100741e550b03035005108861540500c = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 300083750 1250 300082500 300082547
    0xa080d0b011b050d09090c09050405090a170301090b01030903050d0b03100510090510030302031611030d050307030e0105040506011802040b0f21061003110d0504050f1005060603060d03 81
    0x3e22503a40d1240c80c0040c400720b228250040345d000194090600c201c080c90701c03401c000d14505802e103c010710300201181c2c2603000304030450000800c6040da0303505211450404a46a50410700d0010489850302c11460603d0325041c46070780001e4202c2d05a440008c02001d001a60305003800201e414801c01140080c04140342c50108104407012000501c16642401d50400441c0e0b90340998561000c01800080c02583c410710600040e01100b1910303150b901d2141807180201d00820022910308140a400240401e1000c810010b0282d81071284014180221000f07205034182900d0312620784078117015140320365554004c0d5203002d143c4d03a01254018090b4070400c940d01c0030b840d010034940d1340141c03224600562200030035800807507000c103655016010042140441014098003a001459060442d8000c0482400141c50318591032140034441c0340528054100340c421881680c2c06c0c154000f242601440c41c040900c8500d45030401640e60020341600d6a41004080b03007815100b402c6400040c0c2c01c030041c0d00 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 300085000 1250 300083750 300083753
    0x108070806090f091c03020c1b03070b090102032502042f0a0c0803013c0506090a05060a0c0c0f061e1b050705090f06030a1113020a0815030a080d0b011b 67
    0x61f4000c2030602100c1c030039240d0301501020103489104660402a9046c3e1040f0428000b00000720000d2481100500440303203000841049500d10100e2a03041d9403418005070035600030342c10903005e0f196040c0d1940c2d11105942a000c480c0310740c0380301410995114020007041440c806800b40070b54800c525000399003182c5a43c2c0d5520b14035620100041c2078141081d41150910400070501141e00384805540352501c0c400b07007000e05100b0280c1081d0323070190b807040600038002000d469502c010074601e40e15564150300103649081c00e4040c00002c1d44040c800010815080081e03551040d00102a0032000c0d0340c0309500e500e100f8084400301c4507265504025000c0003512002c01c10000b40d14012200180d030781141c5a5940300c3c0804041d2000c036410b6030035801c500207201c00111500386000e0741c603400a125107244451341c48800100d81000038202c01160b180818001c80030004454600100c0c41140148000603ea5507440514090a540d050306030b07454401c403c4c400e030301440c0800001c08ad88075000030a01410b = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 300086250 1250 300085000 300085007
    0xb1c0905100507030b042c01020901051215040603110f060406050d110702090c0a0e010306030f030804051f0b0a08120a14040e070c06050a05090601230a0609050108070806090f091c 79
    0x444201c608a50091f803840d605150060099604800341615482d092008500807400052001010406401b0000e4030306100e55865100e29000f039070041d04015443c41c00c040c240101d010010140350312420003070008104003a030141c2100d41c041c40d03000703010486070661404035445000c0c60500030b50103248102000b40c100354400151810300640d42e1907030300c0402c01d1030043d0100c42176404040c0611a000c240c0d040401e0003424802e410034411021502504c411010201102c642c148400c818982c0324400207005250905404000d000000050726151414241d10308081c85240d0741c000502c65042040c505211070042514020007500b4692080d85ca4844002000203e0100c0105c030240d2808010a4182c0c4443c0304140c49480a80002c20190f400e001c2005941e040c0c2c4800e00b9072262580c00407844580320007407a0b2000b0007160300c6000110b801e0400242a248000308201e080000071020050156580c052040d0800c04035842854240c441e8041c40b810a8044201c0d02d41091404450b4101c4960 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 300087500 1250 300086250 300086291
    0xb04020d0e0d0306030c0b0c0f0f0c010e031501050405060a0b0a08010e1608040201050c030702031510060536030312040606080106080c04020a03150b1c0905100507030b04 75
    0x48201502e000b055102c80c143c046413207034080500300d504400c0d014001099540000d0104040d501c0440310480c4640c00c605241080d00714000c00350350452054003030309503000b041141106200300d000d8800c0f500a600c620040308014441c0038411030b1038002088184c0ca4a0000c40040c04164001e29610703001e0441c041c0c100b440031b218500039010b00c80b00003007004001a08014072034040d640c456507152900c0d00111015004205801e070f1500081000c070005990410409020900c02e04012a840c54040c190710250440f65000d20f00f0300c1020800c10503c103441c0050824298038010161200c0c4401050303401100100300501c64040c0300c0018103610040e611900584110b02c1803101340b000d80e40f607802e03281c00d8802d41d218078040340d8445030081d20a450703c0c0c0c024000c20940313450300003031a140c550343c40c4110203800c0c0d020940c07901c000100c00b07003081c3c0b0418a6004015204106001440c0296503d6680b02c0070303000502011039540c0003184226209400c0032800000080090040244c00300c884c48040c41c = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 300088750 1250 300087500 300087521
    0x1a0909060702070522050c0d0603150b030609070605030901020d0f090c080304080a020111030f04030308091612020120011506020f0a2307050301050f0430030b040b04020d 75
    0x403401c3d90004452030301c9071901049644500e041c0c0d819540f003140002c09400041d081c40d452401c01d000c418a024050f12805004500401125600841401c202411161807007036a5000303400c08410043c44501c002040012100caa2914a5803075a80c8100c8600901a8a01e4523200c0c6040025403080200c294204496544c0616003803d20300340c0d160300c103a5803403249100d00242c0f0f802186064007d0740c0140055a9112138500c1a40d181a000c03102c441c046a000703401c2200821004410f20108060800c440070512000c1003583e0038050500740d03404480f10002e0f1000381081090050710704441c4540100a0031344180d90005c2c09015480ca004509440d17150080000502c2075969030070345410b0009021400540000900c110b01c000c4e21222411184100c0c0c08000612580d01c000505450034407821b40b2904040c0c4140100381018a0981130704505503050b0103410281c84100b640180440328801c2a0100b2800c0014103416200c001c10301600401c455558014070104900c82d02a0468200ba0001d4 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 300090000 1250 300088750 300088753
    0x80706062706030c090e0106080703050a1a01060804020616020a03080301060f0203130314122106060a020c130915021305031f15030206030406090204060503010b090a1a0909060702 79
    0x7a004048102152001d10001c0d0501d0340030f4404203c140010380c04042584074102c0049400394072840305a00d010f02651040700c41c2d44c0a03600c8003040c0403841c072040a401c0c90443d9481240d52410303c0c000c00f010f501500191242200048800000011241420f01607034081e2054200607171324144142a07400074420100410410344803940c10b41d10100451310711000d4085107980c080d0864940302050420021005038520894908402c205496005890a1440420130089071028010b0306460504040e00407800f51006100d080900ea40100d400000305030141e520204041031040c240000e0001108003804092501c02035505844454000700140900b452442d140c031035075503040c15559070740d08840a80305200b14040210488858002c00f01d83c0414045244100b512500000c01a9106440403103603a65621402003c50805000e2100100012802001108006c7c00410360302000100358581da40d6417a4166030f840c3e40000f111221614005d0b02c0e040707413841d0000c41103a46d200c00703a5007034026 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 300091250 1250 300090000 300090059
    0x13080906161a04060b0a0f0e10170102090f1f0305061f0c11010c08042706090e16050a05060c121207020f0a0201050403080307030609020d020d050f0f06090408070606 73
    0x201c1c1031041c3c60004595201c6801f4203218504810110342c0f420190110f90444120940040c149040c040301c100440030180006035240006010002c00480020b4410301502001124011040796020130702000441828086050303a01d80001641c0312207014035459209051181661065074000744c284002842012601c902040540042d00d262103940350042000380c0800082c002d0031000840c07608049040c0900262101c001d0a1440a45a42d5001271a180c0d54a500740100c1090422948140c5a0049000081c1c40d0900d400f142085400d402403078010080024081d04156040042d00e000d50700c1943c1c029120341c3c5001503050010400d880e020010302c40c40044400204000c01c0102d40030394141c5995140c2880c47e900d6100341c1e00000d1011062503902c40001400c0403031400181000142e0a0006903a18408074001c0115a0050715094040103620108480e80900119450704442c044444003c0c0b5035a900c0c0922179441117400051a550500c1c0000800ea0300b440c000d000003040e2038503200e18 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 300092500 1250 300091250 300091271
    0x40507090303141204032006070c1a0c0919150e1807051602180408041e08120c190501021c020a080402040c020703052413080906161a0406 61
    0x103950260401c1c64001c21903000100d40000d01941c2c80d110700e8501d00d1400e84144400d18205810401c0c04c481c089c0200340409030306420007490b05000500c08403502c808518600f4001c0415034680140503c0034011414150801e070100f203080b8aa04c000e00d03c2801c0707000d984040c034200038207480e0303540d81641c0981d221542c0d00d443c41d8184050103200c1c820660700c4a0400380311150a00748140d0184081e6000100e481c2408111000d1900d40703881039000c0d986880e43c0d81c2c40c01000080211211102941d000340042040c00f0040c8042642410911103500c0c2a0b01c0e400b5152402e41402e20800a0045503d04c00f0403010030020107402a11040c00304400c406214001140140183d1103403914000005100000207401032501d40e01515442013540f049920041c0c807662498608170038002000d01080c02c0e8500c90000c1880e03400030076403000b424280d07008184540e81c0c5c4e100040c040c906596110320f00c0490440315840e10340d0080c80e14a44c100210f00c42c2e42c80c85649465240e0819141961928106010a04c = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 300093750 1250 300092500 300092537
    0x109020a1107031502031005090708041101090608011701021603020a05010b0a0605161118010f0803090307170c0612091005100603090503071407060f14120402040b040507090303 78
    0xc2c200c1e0780086400b0307400701c42840301000941c8000e00e5015010003220010031180c5903115600d01c41e0f4000e07110890103040c0340c10855400200c1844050401c50843d0050150b10340c030800302811154407140355180c500f21004020b0181c003c9001421886041c0c03480741e010715500190440386035000d04000c008803140c40c81481180507017401103001181c0d04014600c514481e044217400410300034003d1125030500c04002480116284090b1100c6c490320000501480851840110040904000a514140c203010119440340f04500c90707401030a40c4940e007484036600520080310000401444181d80c0c807803060302001078100c01d40d90740d26588904441500c1107002c0e8450395000d000c420341c00035509403a00038100e000d0300d911901114540000d000000000d901c0a006600d046000c0014090281c1440030040c508034102401d0700c20070003908a102d40d50110002210f41c004a90585880c26590714000b10f4060550f025509401c140340004118080e42c1c000030f6030060381e00c80d580310724941c414600e155 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 300095000 1250 300093750 300093763
    0xe0106030219110c030706120f0b180411060708030702160f0b090301060e09010e0d020604031e1701081c03020c15040c0e25020115060e0a030501050109020a11 70
    0x1150349050303410100300c0b810b0240d6802c100c440003103012151410a104042414903410b0b41c4128045209008401c1e0604110301441c640800d440c0c0040080502c00c0c000607426540c00c0d1210303072880040b100854148080d044081462020152440340c1e6002d00d860203030503d0f8402c84a001c018040d0341108902c0065000c2042e0440d070341c1c04103800728181007080401941c0e102e04e8150341d240d9601c14002450302035203192540700d84009000050b0300085900d03200d00713051340103070450115045601004002500444603608444000007111000e200740c4000b651040c2c1e10302482e2a0410710100002100b52001480751907103140304404021042c0340701d506506a020f00c02d404130494000c44c2c440700401401210b81c030f0f80540601466101d179942c4030b2820881c004151303984420105030000040c41c10780049042e1440d81982d00c020041440e810702d2400390100f15011300010015080345105e01643c5610f003010203960010001c008950b565a90f15000750b02401641c0041228445c6001d907200010846 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 300096250 1250 300095000 300095017
    0x40b12042003070b0c0102091c0b0f01120f0807240b270c0405060708030411011409040e011d06010806010518160201110406050a09090b0f04090203031603090e01060302 74
    0x20f21086040c07010711800d90700b110303094489640d820b01c100c1c01c55540da83c0502a400d8403140704a181e1042c00d0918106030500200b0b0440c0101030040100070f04088803101540c1d06800c9151790300c2c081c0043c941201c1c0c41c8a041c102070000031000c8243c00b41804800080540041d1140c0100401d10403601170140c240300800740e02c140303804044c100041c070b8101c1c801311544c01a580d0307484600d09500e0360000740140d00051825500c03108080b0402c030030081100000350024409003000d410450603400c05290601c11200c55034021a02c51400c61006002504510b01040b80307411145030000c403405280d80c2d550024819a40540701d0b40e0000562402c080041e44000c01c010b481e00403013030b0b0301c00e8041c10010aa0a0a42c0c0440d982e41e660202c2c0c014010000e00b0103008981c0c1c95503512200c41100404c803240742c0c0c0180a405190410500c4690340c1c10147e24084a01a2000f0480e85c40d140006825401343c580780001c80c03070b8258010010183c0c07025040c81a2003101d41004003a0b45c84010443c102d01a2740034 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 300097500 1250 300096250 300096253
    0x1060215040204090209161205040f020d06150b0a090b0a0906110a020d031d03010e1c030207050304090903080703062306190801171506090606040b12042003 69
    0x41040445100c0c0401580c85400900f0108000c0040e601148658404480e44010f810700c244099031500d51014122640303200c0c030300040c02203050688400342c000e140f50000912414600c12050304100d482d4100ea0154040c00500c1c42c4e03540da0305c40241c0c0e10359200070720490001c0c4882001060f1b0110643c10350328103141c10b96400341c4c020308001c070640d1141550701e403102082c8035085004c00142da400c820350301218800e0307640a20400d9002c01000c0314501d6441110311a07414504040c66a0000080107840c410804605509903040c3c000140c000b4071502c40080d115000020b07003c5401e02158100d038900510980c4c640301d40b030740d070703403000b2012640a402001003807030960a60190820030340f8441b010f4441d005062514140c089900d0520340c10189070b0203000310f017500d001040303542c6d1412100c0090401e02c1d001b8054581407c0e415160825005108500c034900d80b40104840d601d0b0304050702d0261014101a903a5004009413442d0041411103040360b1485138498503082000342441c1d00e00540c20080c0 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 300098750 1250 300097500 300097513
    0x1e030201140c1806120a050403050d090f020a0e160e0a091107121103160819020601030308090f100c05071401022701020c0f0f0414101a0304030e04090803010e1e010602 74
    0x40008041d107c0500180c00f00b0901f4010031201003140d10902076894410b9505544002c064030500c2041c2c0540da1000300c0104249080014444540e03245000b072055030b1401414841c0b00e0700c0001e1170540e050304900e01c140c0c5401035126800c401800200074407401020b05080d007401d02041182c201c00c030803c101e42d03d50410b006900160813401c042c01411842184601d00700002c01e4a1030755442c1c940580600103901ca10700400a068201c81e0b1070343c00c50005000f810126080000782c1c5c0c0d40b80d00d10300d10041c1c107070b07525030b40c40303007120720650031303620f400764881612a002000805264043e420802008000117102000b40c01000701c1c034165001d050a068000d4681d015902040005e044440c0c0c0115412407410007989001ba80c0d28442c0982e408101602d440072803c21840f03401c10b4070310981085c020b00304403d500394058103000c07080d20f40c805ea2601c0c01121124689000c10054581560010060f01003c000466800142c00301c4502c1241e03001e601440203140001c01d0340042500784608009600710302c = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 300100000 1250 300098750 300098761
    0x10303120903020106090e2a0303091e0a0807060207050f010c030807090302030d02071a03040507050d05070312080601020f06010b09041a120123041e030201140c180612 74
    0x150401240240a0f0000007009551200b5034010366250324000000c0303800255a201140765081030550000209003099405038101c4030110359030303100b055000c511950221842c5000585601c0c4440710303181002d000084110303940c05602e42c0c1c624180c001c000150013034103070110341c500706038a04c495007102c160340b001d00c4026151810385d420000503042c101000103421000c00561030402c00040c00a40380da0041038a0341c03a19040c010803011400100400040c104144000f0500000703000301a0341048441701d14410943c034055240074000c1e40002d01743c540d41203100c030b1200c0e08520b000b882179100b82c080d40d1044d840e40e2140c0307840721401d014034801500140304180c4c0a04060348202e004480304052101c02140e00360005c3c0194143c1c41040340359a450f4166848255031002c1e1500c030341c1d800e002c241d02c4541800e82d620302d000c40b105800f100c51915810541818903200f500203407008122241032403c2401e11001501650380080c1203074807511070442001e4600d05240c0100c42800d8425140d0342840e498a = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 300101250 1250 300100000 300100037
    0x80405030301170c030a0c050a0e15011b0b01120308060939041206150e06041112070206010305062a070203070b040e0402040606050403030e2e030e1005010303 70
    0x410b02c0a0f6944541e110400d6035031801c010b01802d076801181c0d80c80c000e0b0302d08004c00044241a40002002086110920a1000a040906011400900b40541c03042c01006601900c002c1c0d41001411201c48203000140c070200b40e80c9007070701c0c042c001d0391042c3c032503a190414812071103010307501000e00300740301c4840341c2c03210a643c011070340d42c01d8050b048540c0384640c9400c940f41603002600100a12084961924100301080c850002d800108ea03284484051401c10124054a002040c0d22f001f80d40381d901244100303d9510071105035082d142d41d0000c803030a260400039680c1d203090000301c1d05840b524022480d109505590000100f4600000100780c20440303140e00b0003604034080c100c5c1c25108200d40403582e12010409400901826050280300d841d16004000907034006901400c00e1003c10403050012a9101031a10728005050361010003006d0b40026907024000342180c6442480c0228862105884d0700d500030224240d0349100f180c01c414140040042111300c284401000304014009039880442d4 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 300102500 1250 300101250 300101279
    0x70f02041d060406110f0a080603010501080d0f0507030306050d081905161e0507170d03060501140702031507120b0a0f03140f01021303020102061003150902031c1707080405030301 79
    0x81c4105c0141800820490005281c112012401c04200541c0402100342400d10500e8010845e0704000c10700105564005865000410041800c200d000100745060501a0b044600105009841c5444c818010308180e01c00360001c48004c0e400146070b103d078926045c4501c0503101290100b040052403460166500724003103c4408503075800480d9a000324003c20750900179000204140c40440c1503a00050801c1030130110a0101c820925191140c14046c50340e0042c0d00b0700c42e900301c00b08190341c1d90311030340002864258200c00942c0000035040401000ca40c3c07001841c050b03d8010402805185c085074104a40326800d80140100582c41c0c12082011031140e00350096012610000c0e2490b081942035500e007a40d000072081da451920444c1d0400031545d04119103540107065003100805035007035a4560340006d600f2400d02049541790480c0300c0555a0074048040f03854039004561450112200e40602205020040010408444400100c2c0b00c0d0180b46051310840d84071024502d1603003044000d03c0005e4 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 300103750 1250 300102500 300102521
    0xb04120203150709031203020c03040e043e0f0f0103050c190917150a0f060807180b0319030503040606120c0e15010c0b07020c06070f02041d060406 65
    0x10500140044429500c61000d020f00002d41c0d5252809007903003042c080c1c00c600c0d2481c2e5000c0510421644600131030100544085d01c040e0041d241091b1070340d0900c1c9110900c0d071036003080d220070240f00b140241801000301c06a055001c5807a102211100d00800840b00811408030360008090007149070258881da000070382c40825669258109508007894581034940303000720801044030f00c0030038842d00e81a652005000621039000b001c44000181200040400c003404070f0007615180d2140704819990349e000b030b0010740341c840c0454100a55a40903042c011041c80032011120345410038a6525080225241c0d00c1c0381c80d4040705480300e0b5400d940c100d0707081d440104103541c40b50365503070041800c03180f4502950328a030041805480349420480c280216075005019110340e01992500015203980201100f400950804401c1ea0035a540d00c50603070500c4440d03a003190744604001011010040902c0b05007119034000d0b60100706426002c29601d00071a640c048050241c2e0004000400060103500305110f880c = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 300105000 1250 300103750 300103753
    0x10f0203071b0f0902090f0a14010807030237030902100509030a060513060b010318080706061a0414030601050a21380103080307080a0905150a14010b04120203 70
    0x43d62607440e60380342000380d044280f01540000300d071021850306000c8a41a07150440e030501c050341c9000b041044112142030610306000c0c0c04000288164043c2d8103403407070307a0240f030940c2c05140a010281e404154101411009556000d5000d00405120340f040c0076500b07034003500c034102c0701030b1545059070140c011061441d40751043c0490713100010032601038030b0700500c0c1e0540424074100c1245042010b90354002c1d0540d040500c1c0c11818640710b0308a4400d480015048015946c0d21109414418080d002c240c11034200105500b0100c03c1d2072882c4401441140c004001010050422000300b507122a001e1140c503506c695040424058540c561196203400c0050035050150a4407580c1c0354107550140300e0300440d915090b20012401008405d485500c500180445403140790f041d956020003034080603100104010034a000149504490740c02003100c030b500102207456218404005280c86c6404480540540b410010301003050144501414107849007524005d09090820301400c07070b208090135013031340d25 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 300106250 1250 300105000 300105053
    0x203160c060f020d0b012c040e0a0218010509090d0f0e0f040f15060203030408190903050712140c0a06050c011404050102071101110606010311120906060f010f020307 73
    0x402e001e407000381038813018200d011440b82000c100250915501c000904056010741c808100c0300d00804401030a01d01c0100c1c0c001502035028841203250040000009400040c440f6504540040881d01d0750b04907401100c0a50a582c6c5001c207103a21a400b412442c404200e0451400005034040d00905112a002074a00700145544500003400e849040b42c01c040c28075031b18a480291001301441100152005000451030f5042580e40c55000b441072040200601c60361307658855146100c1c0340d0100c02580c2000860703072030301e44800011026500b80101100c81c50350b008207803404004040b555242600f001018030441d903240481c00d4130140d0120659814079540c9145200321007203c9420307540101d01440c00182c488038079151003072a851240385d0140c1841851400d031f21101d0000030726075911041c28640030485c030113100d140e94108e01440717004681e22440d10081216024002641030300c030f07090403603400101d94880d0f001940d020303400b60f21401c0180c00400120000c501140041e01060260100f46c868 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 300107500 1250 300106250 300106271
    0x6010834030c1106010b160c08030a0e010905010c020d0809121b010c210309020405041407051906180b0a0206070e0f1012110301060c150203160c06 65
    0x5518210000c0001621440d886203a40c441d03051046154502c241c1c10039190481404061903a6481305114540402c480000c0281e2520701c03802d040b4a089620100c011095500ca109903030300c0b0b800026252000482040d04641e1039031081009408441e07041e161099891a241c00303100502c0240507065401103400c0002c54040c0c4c9070340d5005030b080300c0090090000500b4a0380030f02c0c40e1203841c0016a04100e0100441c0012801e00d0740203600c8041401c1d03500d2200e92090f8001d0300038001000300a54402c4c90802000b090020030181c000000804c50265981c940e203441c02c0000c4042c510380300c07034441035440405020381405810800c042d9508003511400d256039a03004110703075501c403c1c240c80c0143c2000d02030041c0680c00c464507041c0f5010480340c0491031031440001c40c0711810082e00d248104101c40c0042d40a800c0654441103211080c11707a025525a142c03000038091050210040707410717003410141c003c86107a6620a41e4000c0b0100090205150f4100c032045560490710310044d1203e1b40e40cde81d490744 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 300108750 1250 300107500 300107551
    0xe070317090102100605010e060d110301030309091506020d0f0311070602041502010b061215040e06070e010314131403041e080c090105091914090d020d08060108 71
    0x810001040d80119601c880d404002400c0c6418a541012600e040c0042401980e80107200c1010422065070b0441e02c8818446084000c0c0096110f0500c0691001002001341036114205506440d010001030051074143c000044050065218040068100108503c039061043d20050b0404070186008520380322031400003065540205011120280d002900b00f007517503615840d170500540c080c002040080107400204805110300c20000d150b1460f05000541100c0c035013095005a600003810812283c60100001c0c1e5940c0e605440c01c0c404034a40080d5182c683d8031a02a0010f500d02a080c400b000380c55040c2e0395841000c2c0c0020440307048514003800c001821040010740010f042c9030000240f5448808603504840032590800c104903082252066090b440351411541140c0040d0381c6001207598884400c0710902c0c00c00c103a20b82041c24540a0a0303003000d1860f84c0340c000d1460500b074481c8104140401d0707035030b14074014441010510b810000f41c170035806030142d46d034040210f0110b500381800d40c041d00b0 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 300110000 1250 300108750 300108773
    0xe040f11040e06131101090311010521040302010b1203090109031419080a08060a03240609061205060a02031e0c091206150102030c0c0415031a1801020702090402040e0703 75
    0x100d40281104c403200103100d003240320900100030a081100e401800d5031118440da203912103015040c03103000200580603456103c01c0039a1f0701e03000d0028019904003460000e01802940b1002d900ca040000c0000d410014048111451100c058480090381440c6541d031180c0c44001d94030545241c05049180c80c000b10544c050044a40e2042440c40d541c1d040001c0050500c80e8050300c01800f807524150107100080c3d2004012907a414081a085400c030000c1c80400301030700319600405a10f07418004c0004a00400340c40245c10644610155003682d03813044115412400200d600385100d49035000c0c5207202c0840300e03a43d15080000c64401d14540040c441c0031030700b08440c444405002e948401c0c1000b01d200c00811304068248002d01c061480c1200080c05603035a2460846142d10075592504101000c00c20035203840025503201070401a00030384c104bd2000c15500c00c0f19105a01d12405e20602a82c0d00103100700c81e64164000c0480b0720a886580a000041c40b224441c01020b200700d8001001103008042d80c0c = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 300111250 1250 300110000 300110011
    0x516061503031701080307030c06020d0e030409020a030605120d0f0216121406040b011505040e04050c030f0a0503071101030209120304180e070608060105041710060e040f11040e06 79
    0x1d41c3d180c0300c0c0382e0030b40d03074a08501603121010a42051041c100002d501c42e840421554110002503220034800d804940107000c110944036a503c00010700250301039480d0040c00d00404a520704001c0c1d82da0b5a0305212401480d81c204505541129017510000c0b4000c40d181310b069841c61040f100c2411259100c0000c00b0001d4200010100000d4003040400c00b04e62135144040e0441009810706c0d04007556410540785043c02900050188005114006840745042d45e00801e13540c0b2000c10682001e050858454040b9030520707019028800b02e0000500e40000c0c84e021090b8403100031841e020240d146c00342075041c2d41c051241010703001c2044454540c2c85810480d8500d400c070b006561b580d86081c0c032140c58030b00001c64924407203080c80c1c514151400c02062075400c070390303460030908069030b81d000040303c081c491034001408460184242c0c500396540028210407420b000d000c100080c60725000f80824500044400a00c030500d0760706654005451b03840841c00c1120040e20111305c1c5c04031440300c0c070700702a01100e0 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 300112500 1250 300111250 300111257
    0xc0f060507020a090c0c1122020738060a0306090614070c05060a090302010e030c010c021e030a0f20011a180c180904050606031b01051606150303 64
    0x40d40015481e0148090008100005080060b91200e01015244054120000c7c184014506c4070200640b0b480c000d007280940d10301c00c494511242d0641c094000c3d006408103030364043c00c0b4000503004030102c07a80b00800c1c2d9220701000755030301c915180301c2c00722040003410343c3e80105450200100140b054094440c141d0301c9030201147d81707400c140c0c03800e0340040010148000c22400000b22404500d01090700c6400516400c0c010440100364101070740036115034511040340384400074100041c0c050651180b10082c00e6a42903079030b482491a00040d0407003031180a400c054200304407856900303019030b0114032002000c0c10034803100a00102c413190681c2103101008020703510f443e0b881d0541c458441d0042d40b100b1040b10340ba180d542c00c1e1303040c414100000410004110200040c06212a80f80b10703010b250450b4000c0184440f444c3c1454801d403507001c240d44660080c80f84140203000400002a40c0f0201c0d1410303510701e07045c4180b80c0c54140b800401d0380d200b070b9005595000b0000301c942c064580100510300949 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 300113750 1250 300112500 300112507
    0x30406140711010e06060604060302070602040b0301150908010203040c06115502100c051218041a010c08040807060201020c0f1209121e0c01031505030a06090c0f0605 73
    0x2d42500c07014501040e15403c080e082103003d50701c20061340c080d180b00d440c005071141130f20701d071100083c8030350740055003090408400026903401c9442866114881341d40c41e5840c0301d655080c224207030300040c1c4000f80040d0b50608140021031040c40400c00240480d4220307001c1d4888624482c8002c1e40c0c090144c89400c40320308a4012090740d81c43e1501d08072468685103c908030048481140c2400701d80002842190007131540110144a00000d01d0341580000584411289412010304941e10000c404c1502100c0c00b24007004c246407621800001b862120724110040f4001801141c00c2d0750b02c0d034001c4454440600000c2041c5204100c16000340c40c09400058ad00e03130081091a20b052040d00d144815540121180d40c002c0a04205841128000b500c0204949155402280c188008034510b02c0b0304001203102c2c034000c1d187c0066070110280080e241000f031034403400d50b0030a42c0c05150013030707607056844024000005165980000c08440c0240c02c00440c19407140b04901c101c07019684004005440030 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 300115000 1250 300113750 300113777
    0x300304060306080a021503090304031205030a05150d06180506091605101e050d0219120905070e04020105070b0c03100f150c0501201e0406050d020304061407 69
    0x1846000702510f210307401004024120360010b0600240705003035950102020000c00c54030003007002941c000d1a40700c0040b100e5645850380003003e540089800030481070404012070041d8a00102085440c0c0340031307019403084880d544404010340034011126071603a03c26032200e00031920030310009029880031005000391284844500f1541d20098101601c01d804110601d200e554122110354003804240c10071200366942800251a24055002038074000c5000164490b804c041c5094800031014081e210396113050400a520703401c845964100034103039402880140803280ca10710311030b64881d2051402d2403230b00c2c00c1550381800c40e100c291171039103509202005002e0003071507900203403000d8880c807505190328900c1c0100e9610740200303003d80c4509200c13030f004440050040c00c0d01b0207030071000c450b030704110032541000503a03110340c0c04120713840c060400c800c01c52003c001d41c1404072011a501d5503521410b00c0c680130032001c000d5101800071600146d80e114075041c8801c440d04028811009520740741a1810311 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 300116250 1250 300115000 300115007
    0xe0406180515010c0615091a1f020304062003042c070f1b06060b0d1d030f180d0b09010507140f070c08010504081b070b0301030230030406 61
    0x81c0014a000300e50002c2060740d40d1303003d44003001e01500000040f407524600491000e0500c0190480740030303581410510200e600003030310710301c200b500c1c11303076001c21200d298140701c09440629141c4140143c00410041014511860086041a040c0e261a400015079400050300e503503c240d10860080d06214040418a600e0500b0480140001101c20600b0f151403103008110703140d010155810301031307542022240c02031014000940b1581c450f5040123031030b8035803407001c01c1900640c000c2200541401c20141c901212984201c0706110204004c2d41401480c612840c50b60300f00342d94044100305e6031042400142c3d259a030941c40940541311032007403820510601425500000e000c002403200402c150060104500121090004d51444145d151030380c86c54183c1e508499603200c07020369824941400709004e0014001c1070346505030b102103103088070310754a801d44420052068440c0b5050500040026040581101609548080000c10a4403490381c0c407500c080020380002201da4070215040c081280c2 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 300117500 1250 300116250 300116261
    0x19030e0a030e1e060301030602030a0e0a061a0612070806010c06061d06030c010c0210030b2205070207080c04090201111e010506031b1c0c0306051504110a0f0e040618 73
    0x40f208408a084001e0804145a03120622009010950000000c4c694035110360107072400345030a0003620074500c00750034a40045e010f007100242131525240d042c40c0c0c2600d010000c0302c40d0160b2842c0650303203640d121070003540da040740100510305001e2090340040c0040c843c0c3c482e04001d41200b00407000b6410700c55404642c810b200811590080d4005003040c180d9a8006039813607071240d4120303940808000c0e950011006014401301c2ca54109460030b4031812407070b05448482d0414a02c50320208410395034030740200c0c0d44000711310841c40c440d008614107040314140390300405501401818910b4951a080c2002c601c1c0c0f9a46d841c1c4074140c001c404890b030f0401c040a00559811038821030007826140c011008002d0580030040d11684910300c281614050031001d4200400c0e62508400a85900d035501e0a00c1d2020b030a089030070340c00c108001030070312640b4502481224504943c0c0c1e0b40b424200320813814140c0d40c0081c680b401c0414020001031949469940d4015000a80b2580700c01e684843d0120403048181c60 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 300118750 1250 300117500 300117529
    0x1406070c0503070b04020a0b0a0306081c0807140424020d03020f1606061a13121e050f030d020a182d0305120c06070207050619030e0a030e 61
    0x220605000801c1d00041519a0550001c800a115071150b1002940a45c0190f100c04525440840c482d804150540e000304100d400d85019225007a13002d0013541104500509000041200e041c003050030342d4852210b0342042146e2500c607900d0640c98181c0707482c030810346024202091a5a10fa80c2ca0641d40c148100c02a14415013015402c144410392450001e009002e070066400042c6040d440c1486015013080c4010203010410300c1c0000e4407030725240c5082d0700c40c01e51001c00c00c000c1c490010b4011a00c0054500303660700008109510212484081d14000000c1001c0c7d0741d510030324600f4540c68206000504c454414601d005a981c8460304010b010b2104041c514a002c400e4910104003200032646800b4400400740a50004032031001071a94000f4255000940640308429500150b0710303020740108504481e200c02c44865035500c10040740d444200e8040d0f44c0d0401c00c02e103d00e04851140000c80345004010742004200f0018550b0441d1030b00e40c2c201c805800007620060030480c1403c20192107000a03 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 300120000 1250 300118750 300118757
    0xd2703050a020f100c18030b0114190902210106120b0609090f0907090e060a0209030a1203090c090902010f11010908070f11100203070f06061e0e0a0b03070509060d020904140607 78
    0x41f4a192503d443c44001442114181c910380340d03d9001c15502c004c03041b07542c0c2e50611940300100381c451401000a41212140d0200d802c801f641c0019002d8003100e4160403030b440b0b03039101c81901c4010381c01c4201414100c4146500043c050280c582c80c0e69800c0d140510505084020022901d032210265142100a50009811500c1c00004012102c03020402a0b4003005040340507036151264404039182900d540d030082c02c0160b48003154103404c1e6058005c003201601807003044d0005526602480121906803800070b0214006004c580c200c1401070681c1c0300c000d6156030000410083c1e50b11010166400030400b1500c0e124540d00140270490351001d5924900720660b0343c2c0340340841d0150040d540c2d02c51014040c0a80803040548810803402c0c0d00610007a01c2d10404074184416071004490421005000e411041c034411000501c080c4000c2c4501003e0410090050090354546018400404406040550050400980c00b0050303124401e14a001c2c61040c044907109e42070400d140750604402038542c0040 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 300121250 1250 300120000 300120047
    0xf0f0911090c0c0601052e0507021003020405130e070b040303030e0f060402060d0f1b0c05070e071202070515090d030b0d12051606110d2703050a020f100c 68
    0x2c3c82030001c1c1d2a0705446040da000c401d1454a21071001030b00103282d05407900100070304501e00000fa840360103059418400c0e211fa5000c0c4c030041b441507083e40203c2c000c160b0003400c5d203041c0c0c0600d00322680101400c0c80c980310036079480c2c9885046003000c9a04c40e400c00e40c00300e80c03103d21544032084104461100d05140d00040c00c00f606040d4000b4541e8030403002d11680c5a031312066010080c8040394084035800005c15090510002400c0b409040303140c00d524252428001c49200145901c4090042031103003000c1d40d0b0b442907118035030021200030b4024100c00c2e141071145484a0054411264030203002e550a02e00804000b62000001030569006052031343c0562140105000060307425850704a440103d8203103d0b45444500d40303504860004034501400403400c04c02d00194456801d030052001356414102840024410102c22035181440c1d0b08520110f40d40c841698003003407081c07014200c1180d00744191001110086c841919058202103100d4a02d55190740b075038403454210a2801d00800b030503a16644 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 300122500 1250 300121250 300121267
    0x20705090109090807032703033f0f020f0f03010512010b01020303070309050c031c12060305150408070b0a0f0c0318031d0603090f070803120601030f0f0911090c 71
    0x70617000c1c4a40060034026200302000c25119100b143c0045803806451481c26181c4d00e040051100d0009180c0d022141d03210904088041c000811404d8640030b40006640110940c0c19403000030401e06110340c0798240d003400907076460402c003001000403610b0303910101c0e03c2c0e5041c4410486070781100c16026210b42e142020284040c0d80100a9a5025960b8100015225103600b002c0e4101503078907600310f0b450b02030f0007d10100c0d541030b0503030600078140a03961004a0039201d4025011151031b03010113403542c1c0c01540050314004c40104400c1d4800c0c410a079160610415503544044d0510a81e2a246020b807240d01000140485100d20240c010151806110310440100303c0c88a6a010480140800828036140606100d00c9800c001810001604007942d0b0310304096002c0e1160b016101c41111402004000a4403040010030350300e1001e00c081040c905520340c400154028685014480d0000e5111109441410720340d200f800f08660095900c0c00035041c2c0c0c0c3c81084602031000701920045039050140a1 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 300123750 1250 300122500 300122513
    0xb030a0c0b0714010e060a0b150f0a1106040807120c0308040609020621040501060807030305040b0307021c050c0d031e111207111002032203090302040c02070509010909 74
    0x4048540d41030100340d50b403000b070500d120403c0d54802c0c41400c540c01e00d03c0c09548240002a4030380301c1c0242e2082085141d5100080243c43c1d03110400042030b849080c800c090880720701c0d200030710041c03501e400d2100c1007503a000303020381c10302800b260240d43c9540040362110078000b001c040420025842d1404003107c10680d42d0180030f20300054030140c0340c2c90b034440c1e000b0f00f10740300e0004071101c0071200644500030207410810004074400455048982c0d50030f02e8000030b81c1100000300401a40d5140c2c603a00e04290401343c0032140d6400081c0108110f07c10220021400c000d410f1301c0c58084c400359503a20750703100b500740891860b282d080c0003507800309071403e551441c0400110558003c004040c100100d100d24001400800e03c1c06150012004403c3d1003003800805a002510741400c910641d0681d030101241684110803070004450007541104070304040082d003a00103240ea6003017031085c1401448291250045411586400104400340e400071409100700e107030841e025030042a10304024001000d0a60340d03007 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 300125000 1250 300123750 300123773
    0x616020616031d060a150b0403080901110c0603010f03111f0c0c05130902090a02070b040b22110a090b0d032d1224030201141b01020307030b030a 64
    0x500b007655414080506100d00350760504043c241000301c40361410500c0c6100c0007406141e0b520b40d00030052402c005820701820307050700c0c01c494102400c00d062004200055441071008044242c171405020740c041780581d031300406940640010060503aa02e811807410602201c40d00c0c0b40d1070300c15410705040d4066540c8200d030484060410717242c800b490451600d03090005040e61740080c0e5210180c842c004a0300d000c69400f62070340d0740c001c03605625a03403602c80c420422803094100242181180c5400940803e11034240d5680115115100101450510b045005044c444103021190400b51036605840d900d04007210070050020b80c1c808100b0200b60a00007045d0441031340004042c802180d000b1109018031a24005804c003461802d040143c10101005281406442c4900c3c14035140202d203403c0500d215552151085249020b0100d117030a40d00150b039005611034164040d86010020131b03240c5a00000001e0041804d840056164100300001805645011011900a074851821503000c40c8442403503 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 300126250 1250 300125000 300125041
    0x60c0d05070e330304120f0c0c050d11120d031b170604060510030203091209060d1a04060e15030607140c010209040911090105220f0b0307060206160206 67
    0x20204100d40419400f80b00c3c070210040d1001059000c800c01c0f091042603208000f40103c1075a60000b003004240040c0c400500c0c0034405400c4880b090340900960a0860780940407030302130039164641106040002e640b06030b400041c40b11a4110466014070580c050107070002c6079004d6003c1c0d04500d40800303002132682c14410a001802c100c2c071008658141c4550740802c003c1d11000d000c3c101120f460407030141c042e600c2a12280c01c0ca104185100741c2500541041e202180d00c0180150305d0200c903250f6510180540019103144040000c00c81d50441d900c0b0312070080200142000e000700c0e8603103140032040105565030224020f41140041044c41680080d926018100e00032782d060329a0b0700e4440043c020300a4034401a001840d04200605108908808a000c4d0708125000030103aa280d400b03100401101d003d04000b82e52401544c440389800701d80003828800c40704c40700000d20080850029161100b40e510001c0560400000c0c801030300b2111a400071b500020340010b040346e00341001e129500c641c0c1c4803031 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 300127500 1250 300126250 300126289
    0x60e0402030604090f0503130f03080d02030402280807170304050d0c05130605090a0b01210906020304060b09070201060617270c180103080a051b060c0d05070e 70
    0x501240c0c0c0f03d60012640541100c0742032000311442c6007456881e8007110802a850749400c000042d0760003200c241000b0340358449902e83c10020720b03442c0e11019400141c0101da114541308040b03044180440030340303407050a0301c005190846107015800d80c1003d0319604542080c2c0b04240c00704018040000842d0201c8401380c41d00c0f0b40c840040d060601100c0e1040e003140f50301c070701c030308045d020380d09590f41010090300c804890801c0d41c0d440d80540d660844512a46240c041070303481b0490a018a42d080d55043e4005c440f41c80411001a20341d02c9034220b07031040303800700c558558a03410f40c4403a043c2100180c0d4000f06900007080311905201015040c405852495030700010340c00000f400084003803500400009c490701c2c0c003641c110000000c42d82c481740e20a00e420b000e2080d001d1030211110b03441c0c407498100da400590682c81c0445003502145c107079020011401e142ca0080325000505441004681e118211412032141c60b1030740010b00e502aaa030240c60f560401000184d401c2083d81c0e4200c030103d40400500 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 300128750 1250 300127500 300127507
    0x1f08070b0403020f210321060102100b010e1807031401030804050d0f2003120a170604090b161d010f081f170601061812030201020f070f0c0f060e0402 66
    0x400070350717140049036035401c0310349004400550105c400406442420260341d4500110881085010765030316080b02c1850060b80110072030b031490420759003d040882c00601d040506407040c071000c03600b65918a904e0b06455200c12082003401c9605116041c209116000c60019651440e245d4408a000758000c480c8560585061641040440d09490b040140d1010a940c990542441c02400e15440802070901900a0307a065243d445503a00850304041c42c19118002c0300c5600820540181d600141165006560f0790804400b2401000070715114440e603800b680661406610b0081802d498026082c1501c00d0504143e80c090ba00305418034009911450094140d40e036010790961242d2540c00d0142c20704c4000c00380030400d9500144981c4202c0702040c100c0760307140da031000b0880d800d24512a00704030261824800f4400c45c1210200044514083c0c4009400c241003200d030b51038168000c060898041d030300006840104101240b4031002400703000c04d044d030314924080c0050600489424404e1040360b001 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 300130000 1250 300128750 300128779
    0xb011e050303120a06050a031401060501050c031204050f061801060803040f031203110307020a05060903070506010e0a020c01020a0905010f0e0a090914010e031b010902060a081e1f08070b040302 85
    0x11760014000300001000c80484c113544c0d007804103074961142d802e41b42d42d5003000000f040ca035000380c044a6101d00700c00000d514080e0540d8410605040c080c1041f2000d00a011005104d100100040c50090301e060081180f0794010390645806c45400d035000424030380040c8000c00c42424040c40880c21241c002c560764070b0302c07445104110f0040100049481017101c002c03090000349a0f00080c0d2140d0f00744501c00f180c0964039450840b6543c1c0c0141c00d40140b4580c8a500140911021302400e2608034000a00141c20910712404c4213080e60800300c80c40d00040c1701034108004075a40a02c441419040b03038113120800d000c0d10000b04480b131055001c1c6500706901c1d40354807410404c50b012140c03000c0d00102c000308030108120050315201e500212400c0d03440c4418807044002d0917018824280032640c02001b40e071510310700b08c0050365030b818001d20300c0144a080d803442500c10318074900054425403403080480d81a5120740c4800090f04140c0d003050005500c0203800307020924034401114141c1e60110381d07141048405 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 300131250 1250 300130000 300130021
    0x60304030837050718032909100209131407080112170a090504020409091406070203030f191a2d06091512040b070c0809101404030b011e05030312 64
    0x9002c1d409200080c00400402c3c00310103841011f12050203070705101c400d400080400c1c0d02510680d010882a04883d15802c0c103026144c0c01841c412001600d1520100c02403031030300045a06c01d00f56105d82200500c10850425400341850707026041000d140c103040c08142e100d00040c8441c0307842c0350304545030014031000014018040c41004020081003507503071b1619071074981c010380950f800487e0301c5810322070494200c240c04140d882c0315580b01c0d402541140d907080d0150131481d00160040454207030062076a120306129005d0b20311980c00103009210401a89024099054503902455a0001d5040400c803200c00d80147c8008100c0e408036407454940704800009035011b1503000d2112061100050040100c030440300d14107204a004001174101952000d03020359880d04008070040c0154410010900305140c04003202c1c001b10000c0c80d10001014080180c8910b60780f06420590f14213151500400501d20314141c600c450303194180900c2e05091520b0702103a981c0c0903442e00610201910700020f189401d0 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 300132500 1250 300131250 300131267
    0x80a030903050f0423100206040f0201030902060c01021804020405010c0b0a0f0c08011703040f05091e0a09111c26030a0b10020d0e04020a020703020603040308370507 73
    0x7507000d1503130382c1e181e4500703016160f8001031070b090f1140c4110003600c0c00c040c40c11075008170034401c603074010b08841d40c1e9503610303020660001c01049050559030a481c07030141e1109000b40012042d00000140e0303c14140b07642c0074050510504080c400c0740100014010b90741d0000c80040c1d00c5030f0004000e251512907020f00700c0540465051040c81501d00b09000c003e480d0b01c258600d04a804c2251100b0765024040c00740c50701c81c8200e0281d06080840c1c250100018108103c805074407940282c0c0808060a04140e0000e0307140040d2400041c00392a481c030102800100e1001e90206c8404036100181c0c0030403d2605042002c8442020b007180d001e4103d040060961404002c00606650b030b1560f030399241065001c402008442d0080c0d0003440b421044c441d00c07500010300c00d102c0000d640c40e01511203081c401040081c0d4451000b94085020b541d034000016202c41c0040d41c065842502c49061a142600c0340c030703015200c41d01c4103090b4001031204008a2000141e1006941c0c050042e01150750743d9101001e940e101c0c03 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 300133750 1250 300132500 300132517
    0x4060f090203031902281a04080f0f09121b0a0f060c080c060c120f060102060105120c040515040509030325270f0501090b0f0a0c020604170606040504080a03090305 72
    0x4082c441d10b80030b25140040481e86c503104528410441c45480243e01d07141d20120340c01401408200030b110560800c1c04041c1030710050f60300302d03c1e1a1550110104840c01034544854596900242d411510003d40682c89011038401f644c614140901c2d1101c501082074542c454401848840ca4901c41170040340e0b01119000c8140c60111009400c0c8281c2c400000c1c1d22000c02006186c00c28804504201c02039071a880c0a800160b0040006034200420440244030340101c0c0001486005180d044d940c6031806010310880d040c08820219881e03c4d07091100380ca800400e8180d0302d070020020020828075984184040311034450310b01072300f10005141503034261008040c00128a078180080101100341d2644401a15035105120b1100ca90b0b40c00151001a01401041d45040042c448284c17030324482006056554583e10300328000c00d415070041482e5030f11640100c407025202150700e0303107003e46c10031400ea0043e40554080156240a4a4036240c9010b2002c02600f0591611035070fa060500c10801e990000 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 300135000 1250 300133750 300133783
    0x203070e040206160b06030105070305060d02090c0c1002070219030c03080315120624010e0d08040b0f1e070309031b030b09070509090f07060809030d021204060f090203031902 77
    0x42004e030402c160240d004503400c41c413941c20900002e0703220380321b401003501503400075001d01c0140940c0e600300040c2410084c01120100e205102c401404031007000301013450002880016030705e039980e0041c492601956a0103034030901c040c00c41000010307069a141001c40380c101c1d0245450f0b48600780007000c50000001250340c4160301c42c1c05004007001c0440c446004100c003030510b2a428810800000c0c1e0105400801800b0410410128000d4180313402c804100c1403103624803501e800d132150002c130f9040d00075105030341c010750021802078529030001901e519001320711400d0070708182040e54001c12140241c0001000194144401c043e0074000050100103907a0119a281c22450041c04041d50f070038481c85101d21400101010421149003c02c031542c82c51801070280c002c003402d02c1c400380c03048480070300712176111f200c1040701100f501654405808040302a02170031003a400c10f420401c2c00c5e6882d13180710041042c40c202c04800142e0380001190554100000700c2d40d075011400e40c0130b9041c03e00403418040e85 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 300136250 1250 300135000 300135037
    0x120b2d3903180f0a08030a050a050402011e0201090c08070e0702031305130b04060603021e09090a15120c322202030910200d0506120d090911070203070e040206 70
    0x400441602452180c07100c0d50007042180c0d2274141c0f140590391309480107400308080421201c20140821603150711007281b0f00001c00d07031030807955a5980d42001980200c0b11508101030500c1024804081d050b001071051004504001c0405140e68046915208452140c052034041e4920b882654215400915006208100440d030310f4102501a43c054209402c484004040d005d807454114016901c06031005800390320b00c4c1ea44c42e01744200410303401e0054043c141900c200014001d4090011020072880348640004051900020300b030685d5408074070445901c90070311001403524a000c60341000c6501202e103401c0704400b0311002544d1203040c10040e903c107800001044030200d400140c614070a08c0d40c900800204000001d46903900c00c10000f030b44c20f990002c1058032074100c003503001150000c1c002801128081500495145440184114103000c11540f010410a82200d44283d03507a2805118041d07244c490303944d0020b911501140201c0d0907043c2d40328045800d54a821069070b0800071000c210020 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 300137500 1250 300136250 300136253
    0x60f14010302190303020307020f04060305030406020a031205010b0d1e06060207030b0c07020d1b121101020d021c1803060e030c0601120b2d3903180f0a 67
    0x14148000d0005a001c0c808010040c02004000e00e6114116078040d4043c50420b0640c0d820400c0c00b050030303014140d010b603c03110048041601440144010208e903001000000810f180242c251080c40780310281c054509001000a01000d0045400c80300100c00000b0307521410700c0d84009401c0d00d0000c61070405140000203d201d9400007143c0d07040c0c3e0300a400380300007079403000c200b9011886000c00003500612041d00300b02c0019803043e104001c09031040008448951150f19102d210903801c01b080d2000140d019040b0100d50301402800d00c2c1d90b00c240b000d40000240c0041c00d011886a0708204420003803860b031034511a1541228440c0039541c040b03014071502c49103242c41692508004030301c3d0340a000329000020010404e49600301081e602501c80c080f10f544140310407103600384812180d01c849280c0d031041e5160f003100d0400e4a01c034903d0b0301c400b4003801840c00050a2480304950310801041130803140610281c1c00601a00e901044811034007603d89c0c8900600381c10034034054000e090501c0303071880c240d0 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 300138750 1250 300137500 300137531
    0x20106080d0c0b090d090303050c0309060703050405090f040210110106051002061b0304050a031d13020a031802090a1d0102070c150201020a0e04020f0405031504110105030403090b07060f 82
    0x50b210300400102d03241c3d441e0201010346551400040d600400c0d0540d01c200002400792010348600c1c6101c0023a070f41400c0f061408180580e00c0300408800103100060180174a142100840e40c04c04e005198040c4640342590200c0c0e03c010505481900307021881072210314000e42500202c010301000f0302448069504050065904d884c15580700321203c0c0c039000c0c174100726a5400240e91290f0f40280c020148041c0f02d40b015034942d6100003503071540d01e58401c4a011580c80702205c03124184000940140d40795a84e020090440745001d511011106000382c094016a407000400d64211054100010380103241400c4d01d072080b8010039101c1003650002c0340420a202d01c0746001c82c1210003142c41c2400000784148101e0803440b0300500700001c1035240c0380c07078006410143e0190002151100c007080c40c040c1c50717000180c580442e401c1d1132030800c0302c81c40422003000700010540090300401e007005415030406a60241901c40d0034003850040340d402141000038002d82d13402003100c103010110b0070428409001440b4 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 300140000 1250 300138750 300138767
    0x8090607140f012004051905030a050d0806060901120b0301090515070306140d031101060503010f05010305011112011a0d020316081014060d020c0124050609150703020106080d 77
    0x2040a51030100e010b89100c81c035041190300c503003024809501d843c0c28901007013603142d1f03410000e01e1004500303c80400e01752420041d40303207440e00440041a4050704150700a100f104000c1045001d0300d414008418103907041500040001c500c01d8010501c0d8800d18081b900401c80d004020340f280c810910801c980280e08400b042c0503056a9409000450310b03442d83c03000d0403200403010f5400c03c6840203103002107132050340b02c05012546403001003086540d40d00001e0070f5545802590168554410041007000804d202e80003254003846015030504240641c1c0d1303034102405120b203142c40e0f2200070108c140ca408440c2124071124101c4011034036402e0290840f11000645140031011841e20404500ac03401d0030b0303d8141c201c0d10020b42c1c0c024100f04220501c0a1074000080000e290f54090202e61085a001e0180c2c900b0f4850308403400e00100910102001c03e46200d505c90340c040c4ea01008a120781da291265141d2181c1d20b40340c0001d641d40380c1860128014101c0d98030590381800303140112101d269202140 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 300141250 1250 300140000 300140023
    0x11041505030f160c2910140a0b1b0c0a0f1e120305221d090a08041202030c1018120203101802040e01020c1005100611150f160806010c0809060714 64
    0x45058414420b0240552401c4901034056000710920ac890b08000e50450801c03031241146007a038a07118060004545406070a40020105604a0100740418010503048220040305d0b061401c010625194120408a030781c040042c00300702d0b00180102030030301d4507010901007906212000303081d5036895100c003281d0310700326041d600142d03400008140301600c00520141440c1d0000461031426140c04c41c21a140e00c030003c8200d0b014014500304040a654140324400c1c07195140d100c101100e881a075030400d40b41d16030f401501d980600381c180d21f00583c42c0083c181040c09a59400000c445407180d08c40102c080704c42000960150415000d03060700c140c107401602d0104002401c84201c21340c8500343e8800da0300c4c00c0385c000f90b80d034900c50000c009080c4544480c40c201c0d0708040907240743d100241d084050f009801c90304c0c0c000c1810349000303000e4081035034104031144501d245040341040c00c0840001b000c002c0700100107004004080b0b08090590703500411a01c10070743c0502101044c0010007201512548040013 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 300142500 1250 300141250 300141269
    0xc0f0f1005150109090e010e03221a030a020915130609121a0a0e150f010b040e0601080402040e240f011811041505030f160c2910 57
    0x2003440d07140c01c50b5003448000300586413000507a0030030128000500d0390518000d00d42d900c60958141a0100340020600f498801011506141c00000c0e2584003465643c0010034600c4000b141d682403200190940360401e0101360090780d10a40000040c2001444280341e43c00c0907800a40d800009000c0702d4540704a46c019201c400e821079450005101c0004031440240c204070f5280c007403070030039245080510361000340154001141401000f0641c0b400c0084440d0400410a030780503c812010b030000001d00401c0641c04080c6042d0500d40007011101000e001c06040c0400140070404542d5980c220240310a50841120740340c1007042c10448824800b501100c0300c0201140214004400b581502c40c10307504d22002c070514021000540c240146040504190484400d01c40480c0c205840288000010429a5866202e007021143c4142d042000340100d0400d02401c0403010b02d40d60425800eaa4168101303216858080b080c101056401c0703800f04c01c1401000c40d00c010001000341c10114501911314070344 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 300143750 1250 300142500 300142511
    0x3907020316170c0102190602032a18040b0a0905180d0210150e07050307030908030c030117060f1f080f0304080d02070e060d0f0b0726060a06050c0f0f10 67
    0x4010791b1103a24003960191000c11900c2c11201244843e001142c114055044040812041c182061240422100e81001c001ca0004000000c1c034a180000440b981c011601008404860030000d080c0c6441b600c00c01029549440001e0311284241181c109a01c1c0080140d540407901d240000307403550b84410354100121b250840c02c8510901140c0680147d50707224402500d5030315030100544c0c9540004002e034041549038510b08002510340e02c00385009405059000c4c0d01c0354140b820402d10907120700044100e07540700208000c881512000c0709034010319070310401802e148054803810000c000301d810100c42c5104d59641c400c9494400801001210900405d40304151000744040742c4902d4581302d1481501c02000210f00c462502d15084500c2c01c1c49608003500820007650340140050044500d0710104640910306091007a40c03811303400240c49204807012403850400b0014007804254042ea2040000c0856114118002048442000d8030396078219a0920920040d0355500d15119510315051428071 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 300145000 1250 300143750 300143773
    0x1270609081207030305090a2f0105090a030b060414090d09050d0503031506041d0103020f03070e040b0406021303150f0c020c1315060305390702031617 67
    0xc58000003552100492514210f1140c4045000e0321020f4083d11450080c41500000241050f4043d07540442c0c1c60742411401c03a845407800000d80000050030705108040141c0c0c0865920300135040152035100701c20400644078480400d008280c40c000e4413984440320000e001103460f0014100c12114042c0d500c50384a0b03a00c1b0424401d88840303112008025600600100c4c0010000d41c070218160074001d072110b420035980e8880c40b65a00040c14519004c10328000c01030044d4107081c0e0340a030030780d4000d60091103010b1410240d800b01d2040140007804400d80007001c9410440c568045456500e03e50b40e200c00c0c0c2e26101e05102c1881c0c0819840405e216240400a05070708500d0b00852500004c5070b00581825445e0809110f15400c546449840c6107580ba001c504046112521800c00340196540000d407034a0210a004a51100c01c26000c541038400340c050380024115000c2005e92030b0200398020307102d040601c0441d15003000c0003c03502c486804500003003580840c0ca080340c003460b42c41c0c0301150b00036283c4 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 300146250 1250 300145000 300145003
    0x1203180b180a1a130602210106021609020708090d1a070e0108010b0307020a050d0c0204061406070f060f02040303030902031606020d031a030a030320090a0e060127060908 75
    0x407460020f103500c900d90340380c600b00c4840503c415130116040740704000d0b10301303160f139588100e910181e18507404048000300d1443d010702d00640e443c05001140000c0220000341c00740d58181075690b1003506225500050740100308000801a142e40b81006099200d17520030130329041110031610444c220186181c2e200141c5048e2280450030881d95060319003100076400d03d0580b00c0c45620082c00d0200f98441d0802c07010020340c04001c5201d13600c00300c2e41c954951000f54410001030350425400410003041c0142c800303280e41d4031203045810803036000c0f00b0185200840e14025020700410750900c44880d2000c2400400e250705600141c0c201c6200f2425070f0b452210030360100441043d03500800c00103078000841703648903d000340d02c1401c0c92544d40524089a002c0480024640324206504400281d2030b07450b2000b61385400003c40201c00d400b00201401c00b12080042810f0594500c02c1d600701c0c1d41040c0c0413440e2a4042c9004c000440140160b585101d15a84c0c081402e0030300794230070280081c411840010b0b04010 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 300147500 1250 300146250 300146263
    0x30d0e1009150c061e0b210c060702010909060b030a18030e04020310030f05030d1103130f08070b04060605150f0d09030e18010305010f020c0a1203180b18 68
    0x44104001080e2114000703c4848120000455986988078010080400b00101040046000500116401b062102484000400165081c8050b410600302c070000e00b0001c506091825820340d1030035141c2a05000413250404281d009491091900700d001c0b030385400c0c1c0b0f0b0055100d01c840c01c0040c060b19445c0109000e1250700e03401d0203000901c1400c039200107454190010368010b113040000350b0680351a03440b10110101003800859082d400050046000441401107401c101d0286110a0448c60310101e924410306003d04014030305144a402c0c4000c00130310f402035441507500001010342070f1500b890004000e00850003110b204401d1801e101941004003c00c0b83c42e000404e5a020341010240d405005c0502591078084051240c4911a0705281c0c0f2202415184056045030a020035450b6080c0300d0708480240036031403d01c030300402002d00b9500d4002482840c117944111951012041800700310020882661a540a0700c08405903d0503c155401c4c140d00560300c00c20407090b03950101d000c0c0d43d41e400c2c = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 300148750 1250 300147500 300147509
    0x40602060c0708070b0a0e01020d06090e07030b04081324030b100905060906041a03040b06040b151309060f0512070e040210020a0807060e1507021b040b030d0e1009 72
    0x70804a400145e0442d902074001109485c0844c8205040c0503150aa8200d0400030564668541c0100030702c2595001d10a101e21412018094050543d100d00382e012500030030190200e28001032448525000442080003810022100c2c0c0c5188603400c8112030801445860a00203400c002d03590002c1d14116444c01031070005500e80c040181d14100500c800f075005903c059520032028400092110a0038003442c104104000050750f482c6014585141020000340415014600e084995030305078032500c0200030f1201940c94016101d550490003d903060181d9048000740700d041c0040019454015440300080d41c100b107030180c1305000c50b182c01c5a0348000d1841a1103c036010840130402505140f22507983d40c01451040c0c3c0c03490640c945595165a01500c070886445a48449000b100c0105002c00c5462503207031050680d003818080c0c0000d42d070b000b0b1001c038041510403059203040e29540301d510082c0969800380079510f072010303d00d001414025680c0c0c0503a00800c125159908290b1095266000b940c = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 300150000 1250 300148750 300148763
    0x10211b030e0606010c050f10020a201009080c0106081c03051b251a060405090604060b030705090109060303080c04080a030e01030f1401030c12050c1513080102040602060c07 76
    0x383c1d1948011030302c0c0207004400391914052408029118032080c000020054a01d40e400350303560010981c018551808640d48211498591b02c081e104810045a600401c1e013101101242d00155424552444c1c818208082c3d015882d150f80016030f502c011905402e102ca800400114030315090000303406903001110b1020040c6082c00000c2e05100c8484082d044c0e4441c2c0110716141e068160700c0408143c804400c0c00d0300d030110b0004265181908005003568007550030b60b810321203801c0900c9810b80d0b60802400007003d1039140c0c0d40c0c0200725241000b05000800d0300800601c040e50355018508010300f118002500041c0d51103002842501c0000d040b10201c0c1c4c040c00041c520a441a00d08132046200c4503095410962504080b460b0100f40307014403d1640008507254005502d1840c01c8152030425610030115818506500b001160f004034000c2d0b218a030545101c00c102180740b05444091182041c104074003494054040b035032403c154050419a15a81c08540081e1100c84401045005501c0c000740304 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 300151250 1250 300150000 300150013
    0x260603100c200109080408070503070f2612070308090c04060305070b030c090603190b03061911070b0708010306060b030c0f090f041806050a0207020f10211b030e 71
    0x3122a0742d00c180440041d04000240c2d0a01e2641c1d1004960320079840449503500201061040d03240074420200181003209040c0c40007441e119a0119200300480d001031810071132170034005c240340140130203091000c0e101d0103183da03080c0c240360280c030202c0141c0d0901c6080c0f04845c201324150600340b0030f80f01541d0300075004092a52a081030300d0602d40c0001c002c0d80b4070100a11080c003042e00da0b80007543c00340e1b007010088039150b4050403190701100d86035581c2511a9101005001d84030403a00316512225010000202e40c098101501d40341520520000901c1c9005403c01c001c15544c0c402c100038140c2c3d10411051100c0e6680307030f01088090005503001c45910310708011500a400d11400100300d11000500f0021500a00e000020110b50401000e41c040c803642048200401050f4400c00d940031012396000c40c01c06440c1e0300480c842c002581c42d114014418078225858142c010590100d50212806008034400703500e0420401501900c00d01d809030343c0080d1540c6400714001d000301c605c0320341c040000700702 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 300152500 1250 300151250 300151277
    0x2104051207080702310c0e1507020a090501031a04050c120f1e0f0703080d1509111902030a080a05060109091506020f0706120507260603100c 62
    0x48550200340e0807a00c1050030001d03180161999545c14400005a80406582c243c000f0101d05081c4c041220400781c0600c1c050b40b0340c40c215044007005025100c250741d0b130211448080c680c0400381c4545c2c01e01940c40300d80c00c9400500041e0942065040c0c82c4507a010400c1c2222032a0b00c002d42030001d03100142250032004480340d060502404081d803018005c4200d40c2002c103140419400c103280128401d03440e41e070b032070f40c0b00803083e0b005c002d46d992003d480c4008021345861a01e8400d0103001c0c0ca011224225221401c15101315001c0800070080c0204450820040200010445003548074503400c514120301048007000c1c80c1c0c0044140d4100700c400d5180d098aa669010502009280042c0710505015005c0703008115000705200d01a2860503003022142641d091880103482c02c5064007803078521382d05c05001440306031b03030001038120199803c00780030510380c640580503181a00c10750300c4402c240ca40d4600250340c0c281c040d210507026403016410307a8400125450b01c8002d550008a01c40041080d0712058003 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 300153750 1250 300152500 300152533
    0x40204150e0703020906191e14030105040c02010e0d051c0501030f02040504050304082d030406050d050a1b080604060905090a14010905070e0f060108160804030320210405 75
    0x241c40c91001b80b02500c1c203c4180c4e070b00000140303040c2c0d880c0c6c001361170440d42055101101c4907550a542413420404c00c0000060801d044522050182034017403070700d9102550015000b50405d00d02001460b0070f8a901d506c4050300101150408484003c1e200c0d040307a500d200c002058400c45050f2900b0a40034a0b07080955001d001c00f514020308100d4480c817040000146448040c00700149503071051052103a1407010203500d8104c00810f19014615420400c0104861078010b0204c0e9030309142020040f401c3e1750785009000045c40c05001c402c00c90200000031402d019480440c242c400c5c1002c5a0810205444000000449004a4422103250300956000020130100c0c00e0612440111000216002090740d90755424000b03698801c1c45190521400c1c001096644003180e5030145080c0ba0640491401182c8901e91501d00032910007404001e00c081004d05109030440c4040c07203e4a01c040104a0704c003401400e0b13990000c5000504440340200c03801c50b161a400c4428000e80d0804000d008958034481101c = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 300155000 1250 300153750 300153757
    0x1505040909020112290406150f09080715030f06061b0213020c0105090f0c0d0f1509080d0e01090b0105010f090e070c02120c010c0803070302070501050f040204150e070302 75
    0x164144401d00f01552120071260013240c41d541004014143c0e1700c00ca010b0300724a030b00c0030600518415030070140180a00c2c9403081d030001c418026842e088560500c00f14042d28102d45541004205000380680410075001c040290050303240b540e0381c1000b40c000407131011011203c0900884001a49605104080c8090904249011381c001040e00f003144140c1800740b41240d0007503134441c20b80e9440b42c1c10820241c10a00c411182c811600e00540300480b20040014800481c1d100d00803d0399607035001d05010b00882c80c0c684091a21142c0081120000c40d0800c0c1881d13810807900800c0b10b50030a8001418081c060117031441050b80081d061420b6400d02c1f0055803c60300901c155010492003460016000c64041800c40c0030340d10a85030600c000415006000401c3d40c203411174080c40d400441e0070042664000040d100d951b0f04460b01c41d8a039124000c00310086d2140c40c001506560030301c3c1c2401510001e030040340e4050761081f03804010070041314029440350b00c0035105034850b5400300700005136003d000c0d4006 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 300156250 1250 300155000 300155003
    0x30810080109110918010e010b0301180c03081602040203090703140304050d1e02060703050304030e1c020108090c04061710050c030708090712030c0204200904020c071502161505040909 81
    0xc902498070141702c6821940502c1c216015691201500e4600d800c00f842030401c0030b810b04009104510140d01c9a85104030944070092a43c0c0000a090a490140788485c8070f41d15030003042990b803400e00b26940d81d500d1415002c140c80603d44000d41012590001048504a0300090110f840284090b107410b44104004540e00d4a000c40c0101c1c40d500681e9030384001d08401e4441d0b1503442e2242402c2c00d004244500c0201e88900988040f14145075a9400c1c0c1c5401c00c400c1c0d42464260719076074800021034202503403540020341080c205500030844040b44011000280b604c44c00725405611080f6164081d914141d0350304985820030400715008a10905010b0340c008450030850301c28696696802c013041544050a42c001352040203c0021403038680126801d10400e485002104641810703910003c0c032440094610035940003580b03240a1070180300c580010090600c0546089442140c040d485801008e05020f4080303040101080d160340c07984602e20b01c080b090b03660905090410090700000e02a8100 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 300157500 1250 300156250 300156271
    0x5090315011a0c21040e071803020f0415090207050f03030c04052103030403080a0b0103090507050105070c030b070c02030d030e0703120c150606090503010b0d0305071a040308100801091109 83
    0x2184d000c6140059079503092032030550242d070f90b52480c00d56001014500a03050a003009440f152481a1412266a81e02541d4044880c0d0b1100c0c01d907440020000d2184550403440003405000004125034a0f03070150013100d000b0419035560303d99400c135860300d038401112840c0305150144010301c894100603d00840c041e20b00b01c41d01c2101c0d00391000c3c0d50b00d560012107080340050541c00030440054158002d418002200382028455048507603030703442d00c440260007024104840402c251007801142c1c222600250b40091001c690303824030010080c4180e1490201744e009104101c04e8142030740c441d00c81c880642500d04090054581140d9612040c040c43e02102c0e410009620960808108080f1581e031750004030300c1d03002900900d0004003800d070810030b034031240c03003079262013070503220b03034891051003040c641e4140307007050344d802e103900e004e80c031000240102a0307442c3d9590040004140e0000c100314080d1070107049480c4041d580d21441401d076075040000424842c000c81d6007803428185008000e400038820310 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 300158750 1250 300157500 300157513
    0xa0b04170c0312240a030809150403060b03011125020112020c0c030d02030c030f250501020306130501061b0201051b0a140f060721050705090315011a0c 67
    0x41d8207403450b04030700350f030900306465a000c1c00a00c0090085228920314030801070307464a4100750000702202020b00c400362060000007000365403541c0d02c1140810a80d079000c01c0e2a00d503512824204018a85800d0042c080d62034403a18162110108003032350486280164080c58070301911003242c0070550008012070510141030135820340b00e8440d0014249000408005200790390f400400c040c41c2c2244642030f40103542040003401404080841103807007107141441c0070b9640d0b8800c40807481d0500c004c90b255045a03800c031035441c1d04020040d00254041d040485410700e452294000e0202154401c0c41002d001c1840e00c5170400c6503840062001480c034ac0141402801e00d820030540c60100c2d6a40d40400c4c00ea60070140c00c580400070b0085010403008080c000a0500658a80c240342c1d50f00e03009071181c0203011245a086842401c03403c4844848500d407a010300c81c508209501504607044044200c0c40b134000c1c0c11100040f90042900c4034100c0b0f0001d006083c1402c400c1c02a400185e100e02219107480c042c11 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 300160000 1250 300158750 300158767
    0x4020f03010306050405010b01031b03050c0c030a050415020d0815130e0717031204080304150f0903020114090c06090a0801110909130302150c0d060305010b01020706020a0b0417 78
    0x400365000310301074070340840c10345010300d002801c4031440000a8140740c646255030f941c00d1924015820b010f20725050000d07a644600144031a10700401566034040e12002460504266020000d40204c1d1052601d240d44006291001e0b40c40d00c090b071081400050b0350a0010300103000c0c0841ca218084000b0744800c16141e551070419083d10020004521240c0c0882c004101c042540c001401c080c0c1c001d20301450400007460020040a2800342001c4c2500f000400854140000075000000f0722040030720811480029110640c06028520015009035183c03000021411030f40c040c08610540d88480900035150756041000350307640005880c142c1113074141e0804142042d0920840e01c140924000c0301c0d40f03a90b441c000b0804070000090240241c006660000e400090300051405a20303125a071084001d662102110071282c05a43c00961031103043c05000014010190f215030f259580a9080e11100c036161081665a0025400c000b807204030b4800000e40810717104034030300f400384981411051803c00e19 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 300161250 1250 300160000 300160027
    0x51236030d0509030c0103020301030206090d0201021002070b01050f030a150216150f05130b06090411031c1805030613030519050415090608070815030a1505090303040507090b0402 79
    0x15001084045100010190f42d24907082007100803410b400d19080d4a15030540d80814014060815010300504903d0a0101168001e0114120f9102150021520750310641001039001c0d50a1041d140640848080300303c9609020449401e0319412080c040d0110140390f1b8010b00035030008518125598075209402c000842130038000122111031040800c408920940c0b0030111500600010081034420000d100004c0c01038200f558001021250401c4c1e582e21401d1020b040030310100040c1d4180100013241c50568202052440002c1c2642d4035603440c00b40e602c0ca100c0c01403406004281d4507900840000e201d640000903140d0800780300c1d290050608961030003080d60400e00c3e0001d6000306401040501803002d0200500015451f94909034140320f10f0100090300c403902c0030300444208007490001030141020104608225180034040710007490150a0500401440011420800d4144000b0951441e000429240926000000740c4183c070b24010b401c00007045c0402c541500a9001d10010b031025030b0 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 300162500 1250 300161250 300161263
    0x41b03050c12010209010807031e050a020c0f010b0d02061c060e0405010f020702091801092108010f031110110106090c030f050411100c06050405010905123603 70
    0x8a00c00400d0620000010040302103000c0d001a401a031040c4440340c01c03680d2011031180c100c041410001940b99440c40c0c156000100500c0140719070f4205001e00c41c0041c03040c1d00900101b101d407000d0300c1c0c0305500303030551700c1c240c400c01d03001c099119801c3d1807030802602e89030009003005284003070410b0300000d09110301c03400e030742541d0702800d84108200108400d00c8020301620400000440701145010a00d9000414200004c3c0c0300d4640c24034911580c02c21100258008041d69070060b50303080c0c6681c0c0d51000380120680c014080300000d2044000098088070b20031820342640c2d0f00900c034600c0c078003c01040c4641c01c071086030048108a03c504104d40c44003800e1280d0400b5101c00c1d0b40208903480041409401d4800564441b14024a48010800030032000340c0800498941118030440d0507000c020119100002c49201401d81c520304400c1c4820400154001c620181c41501590000800c4201c0b03107d181c01601c1c100841120300c146410920b40e40007601c0d005000711424003a58002030b841c003103854800d = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 300163750 1250 300162500 300162503
    0x6030a11120403020f0d1403070c02061201030c051305090712020a0909050c0a0e07020a030e0310020f120603190803040c03290105040c23070b0c0915030f0f041b03 72
    0xc000d0000000000014000854409424200148072003001690048144401889c60341041104c007801821540d44100300e40310f210b1610101c03080c55031242450700d00b40146200392842120003030b4649501070310500589100728070440c09000f0680c035040340012006410340089901000d1444007240e00f1003148560070300180580d00030301549210346e0070310403401165005000040011001c128800394006810051030b0350501d015402840c4000100349840115080c00c0ca0f01350004c501541c010f034060b0040c11543d40740030040e803401d0b1180001d054449440c0641009000800ca4411021070b00010041d60840d10500c0c0983e500e5950781c44032450288106100c1e444038a46126848610712409a0a809480e00304c4081003c02d480304000b4204039216064584061411884000704c0c0c480c0d603040c0c904417504100e42e0714261400d03c2d28000350303621986d882032082e030030f0150044840030350005680c0304840109802c1c02c42e848074003042c040040b00070412901070113070100d0340101401f040000c10086 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 300165000 1250 300163750 300163753
    0xb041b060302180a050306060d05030c03120a0f020f18060d0e060406050f0105010c0f0501060905011205060108030310121502160b0108030c0a12090302060712020c01030b06030a1112040302 83
    0x2c603c41e03030340f805008001e90100c51044007a49802e100e5030350042003072500312101301c403d0f92001101c1e14180c0c0c254000c030050740c101804049280003201c400100007502c81d40510408100041240c041c400881c00f4424091000810900c00c80700c0080c44066400100e1400521583c1030121070720390368007540e00c01c005840240d00304005100800402d40030300b58002550280690080d8181700000b09004e500580182025070031400e80801d100c800c2d8003a13406044052410302040d03858004520520008100840b9903200320000050402004820780e4044c0b8070203140f261070140b81002b0000894221082030361944411041c9801c01020b038802010a600c8400d10521520803d00b0b040303036501416440232172181c108001c031809a1401169404426610820f0a40b8190500d8022189001942c10003500704000191080c1070100070100e8880d141d515508a17a0000403036801101510f044081043d00b2510900c0400e0709510075030400c8070281040560523060000c030328118640c0580559055026 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 300166250 1250 300165000 300165007
    0x207050319020f030f0c0d0204090606060503060307090e0d050a03020c07090519060305060a0203040f0519060506190b030a0f0501150f05070b011412010f0c02011b020a0b041b060302 80
    0x450800303c480c2511600101c01030461002107444450b00c405881c84414404c0c42c041e0f2580c021950340d54001c103100d43d0451020041c19407180c1c8040e0803540b059545622070310417200d00084000302d0340100a4840340c0c203000b0b000d80d4a01d01900740c42e41d0f04201d5000301410303028000c3d410130350010003003100242600c1d0b0011842e8200000c40101d42035403000f040390010b00b008402d001040c80002c50030b4004103001c0d0010f9803580c82c2c0c14044034030404082d0003044c501808a400920781802c0164017401070150404010a8840d00c007000b40700c0603489600c40503006802010003185000b90051903101c61180004500c01c2114512182155403d8015003a80011078002d513654641c400c00020703080081d82456842c200e5581c544800507401441a059810038800c0c24494903250121001503c0303011400034052840998042005803002102d0440158604951001d4050901040c2c9610300300726006408020240d445182e1020402001907a071212600030419866190083c0c080c006d19155500585 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 300167500 1250 300166250 300166253
    0x80c0706020c100608030a02060c0705010b1e090a0c0206060d0302070f0605040806062b030e1e040c0509210f0313030302070b1e0313140120040b09010c030207050319 73
    0x11130b09681c001c01c5280c0d00a00144000a40000d0140e03000200d60742001d8540420740f5206014007002d4409030381000c0c82082c510300d01c5254607008124840201c90310756142d40c0f008000000c41711044203110050340f2100c0400d00c1810290200ca00840c0680305881c801742d00c2e00307920440c1c03010321352015000941c0028104642c1c0018490b040d0010000c4440d03a841c9440040009900075a40100d0240310f59001511010075004002080c6507078405020440c6c40008060054100321082014501440c01c082464030150710980884405040082076a6000360310130005d07200c0301103000d072041014841e130044900815003c0020b00742c0f80e1080000640749030b055207030090500c41c49900c401540b4200f440186d0101002c0d00c50126592103440c2425265900c065148070040c0200501912041e10401080c60a1106400c03042c1400d52500c61820400c60005020a55104520420b103441c1024000f00340150f204a82c003294242c000d02c11207204546a500085c20402008511440f4500740180c0c0c90 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 300168750 1250 300167500 300167533
    0xf0210170f01050604270f0b040b01020607020d1b1a04140102070302120a1b20032a010908030a020d14070506070e0d05010906020408060c0c0706080c0706020c 70
    0x6034007004401c0c40390391651529001c1042e500581c0244514114940100250744069a074070b2101d040702440c0c18056250b6000080009002c20107806020718284205501c0c0b0b540000784950080d0754541c000c10840c4510582100d90029818400c0752008480c030352500801c1e00c1543d441c201c01c00016030360405c0d052500c2e00315aa00703552400325441780d00522288021a80110b03940d0328400d500d04041da038880c0010b100300d841d00b2a06a54204071040d000d100b40c188640c003804640c42c4001c3e0040e50307804007040d100305039980d0340e4038035a6000107240d0703c000351203881141008800c1d4001810f00c2c0b1001903c2c2c1e440181180c020303aa0070700060340300d880300700340c1c013944022141044224011441d103800c3e500d84a003a1101001044401803145d40c80300300e010380d1180307000f404406400c00c2c005c0081c01c0c00c070319055010b50700038030848159105560115941141e540c0c00c40e0301c0c40103e540201a820f16000f020b0340c40a800808001c11401c0c14419000841c2103800204044502203000d0301c104c890b03800182 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 300170000 1250 300168750 300168797
    0xf0e060307060c0b04081b0604050a1202070315020c0a151a01210e03130f150810140d0b04111305150d111203041809030e09040f0210 59
    0x124100300f11090b11501041074246440d81158004000b0355442c12145004422580c42c144900000d03c101c03003c00090060104a00811030b1040313201101021207840d0403655001103010142202c518041c4084001400f98014120740210034192514080145c40d010710700400350404803010358503155070300c2d602c2d84540b080c28489582402d181500e100c0031401400c04448240402d0b903401d41d02d00841c0350311002002a50f00c1100701e032807400e80301500c400c402041d82c111442420b22002d48201030202c035500039418144110700c901e042c40f6146107003907075a0480080d0f00510304d801c848c0d10780e03800c0301107103080c5407603403040340030380c542da022aa60b0b5414804000c1500007100c0a0b00c2c074100920114402e9000b084048a83c111640045e0118a08005980c008500243d90f8060941844600801c03400300291080b620a200441c0090503111285015200800c1005000944a518402d01407910641180d002806140c0144981000786d01054018040c810894040303913080304407801c548903840d000b = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 300171250 1250 300170000 300170009
    0x27030204052404050c0d0b01030e0d02030c010b0f010c12210617060603061302121c120605011b0305211b040305070510140d0207060b06120a0203100f0e060307 70
    0x20484c5140c8440a206140178010505205c01d0302c0f8140100c0302e030310a80008564072001420b072018042e86180107956548120324a207119400c025503c00c141c41c0016002c501c4003410784610181030031036660803812034440d000c0d003024072526030808000c0f02017007514521907441804001520505007030f450002105917540c0c054103584402d0400032182c4011820f40c2c0c014960701100500505188009442d0004510005196202c1c21000940c008a040ba40d0312a0060355140e440100c05001d1041c4140c58440c00f55a02003109810140246009035950221003030080c50a142400c0b00d02000346440001c0b040c10f906051006403d01a01d0b4601a281c80380140900140c03510b403e1031a521a03448070b03601c1c400d843c07160480b824100e603130754007420f6200e44030b80c14084916079a4070120b210400942159505031303102031401d40c00b0782d081e051120459009071142145814180d482d58a260301070b41c8000c1405203c0400500c000801e402d0544010003d0400d035139420256140100c1818603240c00d9a10 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 300172500 1250 300171250 300171259
    0x1032c150a090f020907031103040501150e0405070b0901090b130f0504061d0c220e0c030c030a0e0c0a030503210c0703050a03060f0b03071e270302040524 68
    0x1da01c002602c1800f806a0a54140c80d041c0980c0d581500540040460042810340c0580020801c0200b00c81984506030150141090035007082d01c41ca5101d0132140100c40003000e0b035000307840030311844041401130070f00c02c034051528003001c1c0d4442d000c04655400c030b011400805c4104503000d1000302801040c050140205460400c03010b0318040c500200d003950901f0b050a1084445e01040305040c3c030b401190441c400110403003141407041c840c521003941c064480d6000d428170040114290031071300b80480b40103407511680c00e42144c541081c0fa000820030306241810910446200c00143d883d03525880c80214040c2000e151502e0385481a28007e03c0390400301c20107c00304c54100a004203e120070f60751004d4240c80c2c03c48e21141e000070113400038140b6030484134280064180005182c80f03039000440c421701c0241c0e10100001d04003000034544820b542c030030002081019900300002000012080030f003002c0716443e40040c5640350081400c0320b6080d55190366140c0e26110440306405002e6104240000685 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 300173750 1250 300172500 300172511
    0xc03060903020f0d140d09020d05030307090b030f0601030515101d04020a05030f0406020d090c1401021605100203122508040c03151401060302090a05010905030304030201032c150a 79
    0x107074010203c004094440d59170220203e8054944401e0754001141d440d4042c2000c08520004c1c20204c0c0d0300c0d002180c100000505500c0085041c0241c3c42c00c0c0e9010b2000c010301441d054071004015406860020040c1c80c2145440080e5072140d07035111040c111500c42502da20061000400902c0381d50385100e1105402140100813611116900c4012a68440a0920750a025481e50701e0030340003070f104002200303030101d0401c20310806014854000501315000402070464244088005903120810260311706d1103080701c0082080b1030308000c240101a20200d1055a00d8585490310002c000391054418005980e044c1c1d103404c1140740c0c1d440c4061040c2080f814400964500756584007810f511901004100d098015005031301001150001d4944551402e2101125030316042d008000350040941c051084034003a80000f007650146640d030f400e03124042e01840c80e060454005402078030515100c6010429542d1401c5407051002403c01c01d201c0300c001c00392803c0340c81d04030940d50903a8054601d031400f03464030 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 300175000 1250 300173750 300173773
    0x1425020703020a090e0f0d02102f030603010b031b090106080c0f0f0702060c100614060d0b0303042106050a05131b08030a050306090f060310050a090c03060903020f 72
    0x1a140004072465504e000c90b1405224000c242010302c984504203140c0f18444805107038035001704010881400c80c00040043e03803a2408281c507000004014501d862520118801b2401403030f200441e4080d20113000802c000303042c1c002180c542240d29108050310803010f00c541200b840c6c042c1200d4010603152400c00e45d6424003c100170814882c0011907001000300140c2c00340508100410f0741d4455400400303407a110a40c442d10b00c4d4032070000700c80c4000f006d4a480c0c4042080401c01c90915461840a003000c0d0405000c0703500d80340104007180c80389a040c802444002201e21910102d007505528102074000042450f20f003032403d4503006000e19070440e05200801c0034509820504071081c64005a1081000c8400c07801c040c2600700582100c0712a000c0003801948554201000307601424060f15220880e40e1880701da0b00300c0c004141e4090380c0c10340001d092a605904280c01c00d039001020f42e100066151110398481d1400b0407603038421180d06880303a482c1e40615405100c03003844d03080c02c40003414819100 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 300176250 1250 300175000 300175009
    0x720060907240c03020a0b011805091908090a050a0314010e0c1e0111071214060603060105060304080c03070b090c01081501120609051302100e0607020402070501142502070302 77
    0x59200b400200410001c108003031520030807840321386030340080c0086100c0d42c40301200e11400031810070342400941880003291944d540040d199440301a15002e054070406140d403192000d0303201c1450703903611040111001c0307503036610b0200304401107100e020312409400a16030b4403401d4542c080d04a20f9180c221490302c04043c0c480b403245c640801c2c03c0c07003103007650030b41d107200140c031040d2400502e41403601c1080c00100e0302c005030a2840350300e54012007095445425440e00175035150000c80c4d51541580002004000c2c0b401c00c01c1c00755400505c6204241d003404e40c0d120713000f444c640080c070058659160320414821024010301418281e0a02842c040041d45000e29405103d4505403115904020b40c030003e255091010341c2c0108041d0011410500423030420103c00c0f004841c0500090348501a07450b66801d980c1c2c0200d08400d02180b01500c21030800c41c43d5000c0000a400410341034400d5500c803c1c01040d03074901682034074419180007280500d100c01a03000d15200c1810a000d410540d80714001c1400565503 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 300177500 1250 300176250 300176309
    0x6010e060f01080c07060911030c04150e0612010213060e04050f010302120309030a05070626240d0b010806011a070209060a0f0801020304050615060a080720060907 72
    0x20b0800c48041d840c4c3da0004481032148110142095292911140422040701c4d44582d002c00110112010741d0300420400044603490351000381c400003801c2c800c100b4101603141550340b144000f8000c003d4251402202070980c1d1202e0b000b103038918a10801403100c1c41c1c0105d2911000a82038408114500c0c1c1020000d02c18401070001920650000f1107180004104104450750b20101a081e5183d1035200c1c90202e6803003640f402a400400c40d00c60308005c103c20002358540d1101d50b03408a4101984840322080030138144140c1c03d000241c0040d10031403003074645100c0d03a4401c0303110b80f641c01c00542c940a90941000410781141d5172800701710f1803540d8a00f980e0015104031039012240c6a2542d203e030702c005036090705a503110400d81d04142c1c90015640c034065020f58815809941a02c0035661410301070944400105d00d0940c2c004814020300b10407034840d944499201d0621b09140e50b0344a4004913001020f40c08030b400d05c00c80da02030001c10141c18802d100e40700c010310107040b4900d00310003d410140039040 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 300178750 1250 300177500 300177529
    0x30d0b1518040b0a0906170c030109050622060203070f030e031305010e0a05040e0f01060e2e0503030c070317030c03040209041109131b0503120d02040504060806040506010e06 77
    0xc0e03c0380c1c0f212056941d0000e103200204240d0008110155039500100100806003d03003130b0045c0189041c0e5101410103015004450741e03c040a40f19a55542140624850f1120902550f40d80f8924228001508510096007d280b050329440036802403e180203040e01d2180c481400755030800c1c000c5c3d170b00000080d042502541c1c800d081031409000f070107000c1405042c0c1544215406402d0201d800c0720100003044420200d009680240032251711818250b00c141c406a5550804c0302c65401e1038804036189001d8058035294014500c11000d4bd6600000d00d507401182031001d654020f650200700700600b0701450341c1d00c14503240740207041d0700d04104600103034080100702900401d5510006010400215800b2000060040410505041c8020308100c0c1222034001240c2c80d07040c010a4210025580e04294100c0b0001802440c03112070342d402240c65071300f1130004403c44e5038091001007529035860240300042d002480080c0308074902070805619140c03044c2d00100826003544148003880d16800e50008805 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 300179856 1106 300178750 300178759
    0x21061a070b060105030a14010b0307020d020708030f0a09080102040320040b032a030303040803041e11060a0504031a0105040f02160b0711030d0b1518 66
    0x1445014400303007040d0781c15000180b503588a0070055602100202010a00704524092505201800c0e04100350003c0b000c030801204503410444100340c41c0180c8001c100b907178a0624055100d126002c40909002d900042d040c0707043d80a064140001c0014400840d540c0d0340d0b038249500c001e520261241e00e000341081c007a407400c1c5007078010000010001000341c80340c0041d254103807218000160b50849070500c3c0d440807500950f001d100ac1c520450041c401181d607440c181c40d05400c0380d14240d01483e0810850030300b1201285480c00e80001a4000751101542c130721024400b9034031401181e02c01010b03102c410b0f10300314403140b500c50924102c94044e50244044982c0010000507170090f41d520a81c070352114105907001c0b800f05440305800c80c0c698104040d00c9484140001d0865100034a00c440103a11500300c08540d04000fa82c11030f011001c00489400c00004404880500040c610b443c0e108 = true := by decide +kernel

theorem cover : BRFrame.Cov 300000000 300179856 := by
  have h0 := BRFrame.cov_init 300000000
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300000000 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300000000 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300000000 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300000000 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300000000 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300000000 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300000000 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300000000 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300000000 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300000000 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300000000 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300000000 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300000000 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300000000 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300000000 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300000000 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300000000 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300000000 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300000000 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300000000 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300000000 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300000000 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300000000 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300000000 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300000000 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300000000 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300000000 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300000000 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300000000 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300000000 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300000000 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300000000 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300000000 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300000000 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300000000 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300000000 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300000000 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300000000 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300000000 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300000000 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300000000 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300000000 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300000000 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300000000 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300000000 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300000000 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300000000 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300000000 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300000000 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300000000 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300000000 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300000000 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300000000 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300000000 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300000000 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300000000 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300000000 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300000000 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300000000 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300000000 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300000000 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300000000 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300000000 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300000000 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300000000 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300000000 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300000000 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300000000 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300000000 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300000000 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300000000 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300000000 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300000000 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300000000 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300000000 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300000000 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300000000 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300000000 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300000000 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300000000 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300000000 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300000000 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300000000 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300000000 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300000000 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300000000 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300000000 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300000000 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300000000 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300000000 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300000000 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300000000 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300000000 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300000000 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300000000 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300000000 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300000000 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300000000 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300000000 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300000000 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300000000 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300000000 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300000000 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300000000 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300000000 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300000000 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300000000 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300000000 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300000000 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300000000 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300000000 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300000000 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300000000 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300000000 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300000000 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300000000 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300000000 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300000000 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300000000 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300000000 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300000000 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300000000 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300000000 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300000000 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300000000 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300000000 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300000000 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300000000 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300000000 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300000000 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300000000 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300000000 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300000000 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300000000 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300000000 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300000000 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300000000 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300000000 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300000000 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300000000 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300000000 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300000000 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300000000 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300000000 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 300000000 ≤ n) (h2 : n < 300179856) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
