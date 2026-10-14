-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2941
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:11:49.446023+00:00
-- url     : https://prove2.me/submissions/10178126-38de-47f9-98c0-64e1f6b2d6c9

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 528776978 ≤ n < 528956834 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 528778228 1250 528776978 528776999
    0x616020709051e010612050705040e040b0711011104051c050a0f15150302030c0414180309030102040602031c090320010b091512120d090212030304050a0210020604020901 75
    0x104203284040c08010b02c111211030050a0101740c0020000890300d91144c2c0760400f840c01082d41046083c2042070803c1d090000384181d007480248041c18050b213050220b20aa4007650300b0b8880004050024050a0301415281c481e0764498814039000c1d00381e03040c11728001c2207003a6a0b600e40303030740c030070302500010201d80c17500000c00003050700546402009500702d0b00c400913248100e42c54540320220100209103103004041c1054002c20400b4015410403416410642c07003686c0c02c0342d0005052101d00204a01e81901614500075012800d81540c40040c0101e003240d0000050f0400000741d00c2070510258940e651042640c0c00d40d180140400c0440104a118100c0c4200541059501c03100006441d0b0700840020182c1009591103403224a8181c095015428028001c0502d0a07440f802070203e1004016811a10701ca40b21030351800750b6403a00c3c01741c210b40c0c49018002102402408403600d909007801c0c0b4941720310041c01c04a00ca80128241c8181c001e00100700a40700c1c540085c02d034107490b860604250f1 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 528779478 1250 528778228 528778231
    0x224070509060f0705011d0d2f060c0405120715030533190602071202011106040602130e04120c1b03060e010b150703051305040518061602070905 64
    0x1a840841401002846400c3c04050079100740144004180d941c0254241c45a6030306115684e060f54001d031000e03500e090f41208880f42d01341005400c0350048040c11400c84041da107604c256540354001c1c8003d11603005003400243c002d441c02190914100711117044820fa44240314401d089d00e6614141d00f90000b9402540410360240070458400308100b002001c8200d09030036040c0782e01c40e95110213a40400781c20000d954006148150349440c0556041685c081d54032621480303112651040d00d42882c046911409180d507410480c00110741d2a400e003850004c000e50000c507040484245051400558a0741d400b0181340101e401407240b40d612405040102d03860b000351541900d1040301e00b98450b50000e042100d84000f036000f4407000910480e06c109060039100b010081078804d4010070024100c81000d03004035000154103003445a6240d109607a0742c031080101e540a1980a885d0004000312041090142e65440c104d0304d007641c80c26510702c404542c0000422084000580c406201484000800d50205 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 528780728 1250 528779478 528779497
    0x3080112030c060e0d0e0604290408010203130312060501050a030216080f0a0806040b01200c040f06030b16080a180206070303020910020c13050721060602240705 71
    0x100d20401944031001035400d44903038452241c3c048408114611b92203211084080360403100246840c1c03901506805040d50b0b440408c00c0d1040e0141c818090410080440d00244202e100a6440e4500f215681c07080101008095020980c0b100d400000c108040c03080e007003620816124030741000d80c5030718110002d40000305c4440340b12000ca0f01140100e1a003d000e8040001d080010f55651600031a00610800340900744600840c1462054141c40c0c1c0c100c242c80220b12425084032030f98035010f484640ca4904070a00f519007086c501a5420254500da40216042e40d0081c01d0741881912410840d10810039401c00305070004a442d80800c01d4244c8540110ba003200512004450120141e00003484070b9201702c00c00ca002c01d900142c510300608166104684004190000e807079558141c00c02b03d502c90740f600520207046035580001800190140090f0300340d1103030810354401d40310411350440d0f00030f1885000d10720144c0308100072503c030010310803442910f0000d0790500c178601c4c0e00c80d0501a100740d000100c03030303 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 528781978 1250 528780728 528780737
    0xd050c13080618010519020903160b030403140a0c03140c070e0103050c03060106082703032a180d0c0308030910050f0c030619091119020a0308011203 66
    0x30600030000c0c500d0001e0901c000140105041c552001c06112425001c510038036414401086440c54000c1c2d45c02400480120015a039940c680c0d0000703080088504070158242c1d260b16010610115080107075105a110b6103401c0101c2c0c06000b80085140500022140010354200c14203000a108040b0080d521110506160820540c0021380e4244100b40d0801081c00c024000100300f440740c1000701500544059010b044254107140d001006c1041c001d00d01041601001c1e500490840a80f454240383c0c0c16100070780c1c0d03d0f401c003401c2c8050210741003180520095000600000802c070035034100c44803a4181c0302001e444a18440501c401a200288149c1c2c0c2c1707000106000001c6103030000158072681401014000001e070200100f0b080350340240c0b002c101c102c0722030200101da031500710880e0b401100449032080c030411804901d880c0c140b81604903e01140c100340607200030f40400c0003d080380070b441d840014042140040d040b039507007510200190005141000400c41e02c105402c00f01c00040c000d180 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 528783228 1250 528781978 528781987
    0xc090b01080f07231b07090203010b180307030b09010f0e0c06040603050405120403080a030e06060607020909100e0102090a0b09031f091703010302030c1e01031d0132010303050d050c 80
    0x5280030791741c00c001e00e40c0f040c803500c96110000515040c04510050304248204504650408021044501800c2d980e811803078803000d00c0c000c40b603800304140c50045030303c03002410940c42d08026903800303496004910380b10036060801c80b0704004004550703440b440b80058103450800e0b140030011006441c002d4002d6415008100e5400c41150b04074001b40040c5004000050742c0f0015001c0060840d020542c07043d9040d0044070500c00c880d135610701254101ea804450000046d180c031070040c0e08103078281c0700c1704800614200001071050300c1074007e81809001160b001001a541d17030341041030381c03042c61603e0b5816088400750608a540b400e0880c940f8004060740011b1041650f940c45100c010820310404180e04003000400461508101c40c010700c00c42a40d0b8521840300142100c895641440022414035403500901040440d00f40080310b01c650b1050020720076026030541900e13840c9490b500070141c0b07905030b264204070340820482a0b0704881d8180d465924116a10358210300030400a0202e525882c410403 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 528784478 1250 528783228 528783287
    0x3230a0b06220507050705070f0e04080714070906050a0e0603100522032003090f01141c02070308010e31080a030c02060702010902010e0d020a050d0c090b01080f07 72
    0xc61241310f80500e0320390030396940c00750501610340340441d8001c240c3d44100d4641444185075011358240c22507840b141c43c80d01d40d501840e00041451411078a00f0b0588240c41001a45060780d0300b01e4012141c09495400c1e04685840340c02d20049811550160194407000009600c3d01050744032607480360310032095180100314403070040c5900a030000180d00060070b90300b600c4c1c2840f8072203600c0134049072540c000f985440e41e5034021504c90720145040d2818080c51402d0112410b00309001c4030070412030000b03400219154262120025008001d00360001111913001152a0f0f40380c024007030040c1302d0041c103241890520b0350400100028a0007030004900194004d1001500d00800380501c43e6241d00c01284000940400038a040c500400a4045a050081da0710250742c20042268500030181d0352507a81c8050750010503540d54641d0700c0241c2043e01704d050601445032800c412010340381054800c0c040401000d00458081c0400e50f40190b12220120200b83d52501070031085002074000303004500b01f0406d81 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 528785728 1250 528784478 528784481
    0x80f1803040308031f0315050702030405030118060e01020304020616020612160807180603050a02040803040e010e01120b0a0905011103090f0705060f0406080a060f03230a0b0622 78
    0x6600843e031429001c01445076981681241c002464880e00384100c240d0310750340f140c015904e1030442182d1003e1340c0e8004200c52503c2401182d01030000a802408201c10a4407600e2000144a80c1912070070b16000d0034210b046010300840740529001010301c1e0a03c02c2040c4c1d403081240b1401c4003264401d408209060301d200303047d0019481350b000300d00c00400b80075613400b0142c000302004040204120814005e03103218005520801e040e40c03ca0710300000c0c26555140d42c500284160b41000206110105000650520050802d81602c621007040409640d0b20443c9401c00004c80780014140c0406500103000308000f50301c4500502c1c0140004a8552281e8090f5030140c0e106550300d00c8281c001da003d5500c0000f007001000000c1200b80c40c140d21b00380784214946803500441c01017504020341d54010034400c42a940000d4054408441265040750762490113040520b141400c3c510614061100441075010200d10300c1c1c103103034000f04100c0c0582e562400300819040d1700c0480103c000309100b0101e00a01c1107 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 528786978 1250 528785728 528785737
    0x50109172514012d0c05030403081b03030106090905060d0c0f0501091d0105040c0c050102030a0213050f0307030b0601050f03090607020c060a0c11013e030406080f1803 74
    0x4184003110602c0c204120314400c1100740e500d076030500c821102d070804441080c90100340d0542c0140a0302503d580210411502c181941c200509103200104004c410300c4042c0004141c10020f07107074140c600150405965460707020034455500840c68814082048010a42050b64132010041030303c402100159201c054085250300842c14100b0003507024881541c001e900240503082d10450305404000781200220314542c14050240a82d45a0b0607054a283c05001d4082c0c0c507643c0280295120314140c0c144000942040920b145406102c1c40c00040c60b042841543c01a200003401a02100d4215140c807081d84034040e08080c10031508003d0b1841a00d1b0010155000d541942e000e0f000070b043c1900000c0c45c0ad035405000303620550040140d8445c1682041c440b03551581d006200482c0c20111700010789021005a520021103130038451400218486820100b07401c110040f10244000080543c5a9036401503000e80c0000c1400c10b008501e59010404d5000c0d4001403400c44150400880340650b411a0007 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 528788228 1250 528786978 528787033
    0xe01290a0906091d04020d1e0605040317060303190504050a06090513021312051c080402010206090f0c0d050102210f09010203100302060d0b10090305010609050105010917 75
    0x240d0310024820b041c0d001c0d80c00c20007010190b0f81c0d4031030442c20740301443d1400350140000f44120650603050f8204240f80c0901c030088103806c2d584415218480c00d1007005004211021000258821084981c84801601640c011a00a00294180700e0480d00622002206440000c00e10100344800241c0d55a03d10012010308510f640d41d81000f840e08090007080504a2403c00c803081c010700204c1d40c1c10850058005c11203000604816400350700e81045810403054940e0402107491156144054139002202580594803c0e800c40b1016030319201c60580300c7c10085020482c940242d07507038104a113424070820803401c1c080c000051400d02c00103440e003d443c48841090506854106c20028440002c101c2c1d15441000e41000f9840c43c44e085415201995480c01300034421803012820300e4003500141d000c204040005010b01c001d502c2d080902504500007803004462540c200400402c03031020b28041d240c100c5038103850f030480484c10120720183c2189046102d400c2c520031140c2c1d001d0001940040540307805c2 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 528789478 1250 528788228 528788237
    0xc08180316092a0c03050f04090e0f0a030509150409090605071407020609010323010311040f140c210f060a05030109021003150b03010b0309160e01290a 67
    0x61400c0c2c005026900c003140e0302d110f403044110300c281c51040d00c0034000b10f241405140030842150b81e460295410b0150982e942d04444010030041069a0b0b42d602c08001e1401036401c81c0c08444009069541e83e2648000060001d00c6c244075203241c504200d02407001c0c50140d01340c8641410307255900c0400711040c0000c140c4405845400740071129402070b084a0001e08005c0310145421850740208200b48103401c100b504160b81c4204550310503800d0410001c5500070300d1a40c10203561f580c202220a045030b010003e1080345040000e1807240414801e060040715051000c2c0440d07030355941c0d107804c10b4000404030340880c112041d030411111501034041b0703c00c0484001001c4d050500c101030082510300da420141c002ea2600e80703844050f83d10001c3c2010f240600e0310340810700054170a11801d100700c0342d0780001d105200200000c590080784002a5100b120900c2c21a5040c1660800e070142c100c0581c4281002400800014480c0d4440104007140c4451002500d2407000d0801012410551201c04400c0c0000c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 528790728 1250 528789478 528789523
    0xe03071410060f0320060c15060a090b0306040b070e06160c0b040e130201030e07120b0a02093a0b090f072714010303080a110304030c081803 62
    0x2149144510000391004000e500d03407042c190781d2260070030340c880750003a0146017204e01451180e80c1c90070205c031200842d4200b520185d5104035000402c900080d10100d20a01d1104004603072208640b0840f008201e00900819841c0c40e1900e40c001c802202608640410100780c0340e80440b034442800905007800c1000091940380d02908000c5c609501d590000303200400c0c108010880007503c2d15035250081001b02e4103803202c118510050b0004c10078070702803240902850b00e0009038402c131650184901c500030040103c041d0b1b50045082c08903c0340012813544103c41c03240c0f8183e184180803250409084c81c00715203041c3c98022000c030f0403c585600044985848800c2000f0720300c10309004158600d501000240358060134060380400b42c0b003401801c800940400104010282400e4001c125820350704039007220a540c4030b04004020303200446494510509100408442c0d0b81c01c50100e03031040e0b426545500311802540e85840c580d501c2410744040080f0150490702c0039540c24058101060200e24500c800e2 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 528791978 1250 528790728 528790753
    0x30504080f0c07030c12020105040501081816080610150f030e0304181803141c05010603021e0304081c0b041e06060206060609061b010906090b0f06130e030714 70
    0x320195131b0070403541c000b2101c15481c0140d0300700302a1000d44409003030520199a8804400c0454480c0740b440f450b09110f80312001c504008080400825030708664183c1e00140d80710308140051003020f1003815140500005803043c00e80c4034040d401004046450301040c0d24514000381480c40e0041c2e042030520131070000500e035040b2880c2c0b1401c1c2518501d954540e0050103262006451703402009a000b141c0180001e1261000341c00c00e00303050303265030f0f83c040c20401942c66445c010000d41000c2e500360010180ea40d003200480700100e0640b0f01c03d44c0d1007141c8030710b0300c2000ca900c80c080f12500541954201e803940280c00b52552907000320000310301d1400c0c90707541740d0210700b445d02c045e42e025070300c60300c15900040b042c0000c40c0c984204881d900303881070b80c1e00c5985078800d454000b6480989540915954a0b044038082080308580004411601400c00c0b9802525819030000082900b99031456110a002e00c8020f48021240c00a0300c15500c028180da003407104a455a451031510b9201c448400d030410317000c1090 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 528793228 1250 528791978 528791993
    0xa06030b03031b07061d090703020d1103040606030b0906040b011a0c15060108100f1505090307060206040b0c0405060a0c0213061205060709030213051b0c0f0f0f0d030504080f0c0703 80
    0x544c0208180382d0b100311b03480b8045418807801038207410170182c00160b02d03000d03a03840741c100001c7c52411542244c3e07207180c1800c0040c020410360108450030030300003010866041d03000034200e0240e60020604210382c0d187c82005140111143ea04140280c0103011018211105004a0201075580c030351408841c5445400100904401000c918902000407014003424011840c1c0006946140c01003401460700b9040c21341e80760194881031940352140707080c0415096400700c0c580340110b00c140300c2c0640a4807030185544d05401640100354108101340001d00500b840f840140355401d0010704032403045d0081164843c10744510390000c44003e14200145001c01c5004c000f003640c404024900f5000050465000451080c0301072014681c103502c0780086a44031042c04650001200e480441d0340c0d45405214400ea15200c1c0041581e08a00440c5401c00d524400450301c101c1780000c0c48050b000c1301d4002e20082d8001c1c0710183c4181c4040c40107000569401e00c2450080c98910301c03600040201500d145060417 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 528794478 1250 528793228 528793247
    0x4020d021b07060504050d021f2615091003060c0207050f03060c030c0d111b06100f2c011e080109033906020a0e0a050a06030b03031b0706 61
    0x40103a2185070b04125990340f010035102610780c111448103000002d40005036550b4083e60040e0a07280000d072120520f5508007076070070505100a100a000c40e2407131246c0b0280c826048030707140e54503500740d511181c8034074040101c2507210b40d031008041d54030358890b10358104a440b0380c82c0b15800742e840f403d4148441e02c0e051010910f0400c0443c02843d16280007142091103000203041080702003000b00301c01c00709040d5500300340492001c0c0c00c141c035121000407408442c80d00c5807004070084e50060002040d14400325103981d00a88009010034030240303203000c1400f0318441d50700008041c5101d07900d89140090114105c098000c1c5540a80381d40c040703071000e40c10762801132254042d81d4107038505020303040029045000112a6000c0603202506841070064242940e21500b8866012950b400320b01000c1100940c090142c0071480e40e42c20b003400109001f03100c8403407003c1c000c10b5030012500208014a81c4207401080030303c07001030309a9040881081a1488019040d40031440c25040f07200c091100d00d900a8002 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 528795728 1250 528794478 528794527
    0xf0b0718030503090607050a06020a0503100909030c080a0309060603140105070f0c1217040f111c02101404170c0901062001060b043b16090504020d02 66
    0x40309285903960300c41d03881c0f0600c64000d01a8070049008024440140f0810040035000201955a030050640061442c2c0c0704541d0700001e25090100412400c40c2403190748442545901c0e0388102c1c0c2d5464860170340743d82104d481c2504054071750601d60b0004000d030050038002c602c45c0d900684c80c001d96850860940d440100010200051500007050305039010010340c45079604003c0e0b8180c00c110200b421609024290b031075100711090001844108240300c1c2421070440c0c05890306c802214400c0d0100203000c0b15129a801c0c1c1151503020f68000351a00180f80d04400101d070510170700ea41086002c43c011500154001203103207017140410300e8030f0785090001135180301080756000300701c0d07041030b10141c02641c4442081c03c403040e10b0712060840c524258441400780004a07000b0303860340c0d038400710b84031010361030071000d2044000e03490b101c115002c045007010b0310608140c448168681d07a000c410680c100820350f0b848200803245200040303684440c4018080028002c0300503a50704448101840912038280ca203 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 528796978 1250 528795728 528795767
    0x20a0b30100303050306010210021b010b063402040e030307020c0f010c030c1403180a0503060106080103020d1109040c0501020d140d1a04020f030106230d0e01090f0b07 74
    0x108503840050301d040c10190780d458241913440c0d84509004030319100c01e0012218030184002100361181003896012814105808000d00c644c030700706828004207000d51a601c5020f66410200c0b803002d113002880d408011030314821a04001e0032250009003e0f20710001c5207524940001051000301e681c144564840040252103480c40f0b0007210b40001c011107a100806410000c001e00c407001082400b21174911102c0e6100c0031a9100c0c20b0800c2514101905030f00c40c0c9100e240001000a1142000b066443c100d0b00962926031590f807950302404101d44600030f003180c8054000b1250903041d41c8030000384d030003035005140c548152418980060304c0d0503c1c040d24030081c0301203800242a54801c110807101d81281c600404210510780240d00440f05198602059101d8008200c40500941c00c4000d14100d58803070b550b00c100c210540c010a80103d8140b8620f914041c03041004c0d0860800540007a52400340e460000120300149031282c2c05928245042290815518011301035016444000e040c0d0010f0718101 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 528798228 1250 528796978 528796981
    0xf0913020c12030c1e03060a0f050603040609030207030c0f1802093010020a08100308040e1905150a0b090306132406050901090b0616020a0b30 63
    0x901a550b0507503a04542000c4400100044c008804030090311812020500c81c058103154014821100d80c0085036458000e203224000014250182c1c000c1e2030444030b0181039107146440d1621074102520b5084000d8043d44150040000000c586165803401401d20383e80d1400128280080486141c2c845910505030030f0040c02079901e15a65400f00c03126030454142030a40c0c038141d50fa0041e040404095403482e090045620034180028181c0042507035035101d030359100d4280d4036501a0381c0c1c80c1040d4000900190f07420f010078000c425a1000d025005100305114406841c80d201c1804250790f0219407010302c1a10302c42018610f4100f0441c290041c00c0406c4419041094420202e50b444c0001421a48410815807101050203400741d60481d80034031300c0c44295110500080c442002d41403074400c1600820601000162013000d07803080d80b42c80d00d0020030039072a0685044815031180c8502c0c200341c2c0d110080e11400180c0424501c003c08100421041148010003102200300f11902008011010f4021290 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 528799478 1250 528798228 528798247
    0x90c17060f0a110f03041b150c050c1c060c030b1518030d0215090a1a060301060f171204080309130e061003050c0301060b030109020a02120f091302 65
    0x1500507484036406100110350303a101c9074034101410074a031011210003000580e02400c1e85004c002984154041d04070400400032480380c80c40543c100303218180c0f1240700c080034a0720300d40c07141e107100980500450880e00700c1c04560001030040c94210100010301c03580704450000f006403d0040400b1030341107040400c00e407130066011440d542d8035890300c40842d660010b0007041d400c40f41d1515040d1030b04017808950351090140c030041c0d030700c8101040d1b0110307e07241c40f00010000100003d5030783c0440d07801101300c00140a824000982e013400904000c1c4e0554032003401003003852182030105d0003019004c191920b480a041190350a02d848880e0040e0007080030081880905000400c031003038170303800f5184005103c454500c660010200340703141140704e000c0c00d8140504042c1145da0001900d006000340c9107100401c404050032180b00d48201d0003048403e0004000b40b500c00e0780a0802c415281c010f90749160391035104211594850000d80720030500c0800c01c0c040300e080c1004209001300100100714603040910 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 528800728 1250 528799478 528799483
    0x1050a0b03030a0e040204090609090b010e070e04021b12250c050f150403050a141f0515060705011b0c111017040b010501020c0d02180606070c0801090c17 68
    0x41091004d00c032124410a9444c0c481c1e40c11640100030780d240412140761204a41d002506c2080001e40d42070400c60004165041c0000d112806603025464403d05041d140003803102a402a00c0110320a00c00c0b41d000182003038003444004800e040d1680116034485003541c60043c0c03a201e042000b90101101e19070880014003e001c0740c003e03242c1c1200c54085c000d8444000a0542c00310380c0001c0805980810300100704500081c4024010307108040042c050701a00752041c3d61a0034554400e648001c0f0034402148070a815881076400c558680c4501620000d040c4c081000d40d40309440c1261140c6d99980054105841070403803c0c2402013510b880500101241c40354801d500d4181c140c41e1151640121103e0760a014400c0011340c01540000561203103040d043c40094104240701d80c034094010b075403003c441444c10b02a82c4a50307942c01003000c22810243c008035807000e84000d181581100c82000b0a102250385010361100400c1c0610001c140d84045140c41030110b00e8650007087c070038100c1080c114055001 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 528801978 1250 528800728 528800737
    0xc0e150a1217030406062706150c02100e031b12030c0604120e0a080f0c09012106330501050304080a0807030902090703020714120301210203071701050a0b0303 70
    0x30b601d02180c0300c1d200c5040078402014107038420f8861210b400091100c1d130042d0308803500b0003032001400304452544c2e0414a1940d60a0310811400206038030059001468219131500c00c140b03880c50442000190400481d2920410b90042c00c00c0c04c0100c0c9213891246002e851200003201c101c0d000d141005588070201d50f40d8800580020820701c0030114810080c1c0c451050f1003803074600102900d2000e680e0340d05c3c182c1c803086600422083ca02400000211504094004034100c900448010350b0245c403807240030a01a4164404848a82e06e07081000b444200e8601040406d0340c141040d818044250603008881d400710b0f40c0401d0604c40e06004010200303580c407003500d030001514204090140e82d81c01d412802001c108000030740c0720440e001848245036140c4d001d49512485506402c0300f1f0f441240342070f50b50700940c080d2541d180500f040180a010405504038003614803d0b04180102d296a80c000b905051b80c90f00001d064145100c111501c505003406159001034144400304003035410000800d80300d219 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 528803228 1250 528801978 528802013
    0xa020403231903030203041b0b09010f05040b0c0105060909120405041d0105011e0b0403050318010c12020d122913180611120f040c0e150a12 62
    0x50203007450030103440c10b100310444094500401d4000350b00d1490b0281c001e4200b07550a0316900780980d00c0d101401028180c4100b520080051030341031185003401102d10807074043c83c003001c104050200044012142c0d010f000601882000420246020001e000da18600113105c03d489602841200401441c28802c540c20b541c4160340208a20f4100d1a02a0030b24180c2d0364001030035881c00000150310702901c0030f10303242403500d0384010f8041e40d80c605c03040c03802d8040d0380005841e40c2c004212280600b4245800d07007403d1403043c1080c00c0704240c15103130000050448111400507030001304059042036030040741d0f940c138a011000c007004200031036045136034881070404c108011181002c2e10010710307640b544403100e101e95040c130040c06007200580c009910301400c0401242e456042600032440c89000f41c040d00c040001000c14540c035651507100e90b0351b182001920507208014055004900c084020141d144503010034010241608400f00c20712103c46407540c001040945d20340c5444000070548020769402c401c = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 528804478 1250 528803228 528803273
    0x10f05040312090e0f010609150215090f07150801050901150c02150a090e06010819020f120a0c110601051003050a1b0c0b070f0c06020a020a1e05060a020403 69
    0x1541081c280c80f061825080414040340c8281004026901d0200303160685d2810340e1400302c0e2940e6200c0d650a5003100000403000758004d811060030b640e4004032916030206609048915205400c1d4046040900c16007060300d0201c0ba0502609485070031804030790061106850880781503250100c0e00f40900d6104204008000403004944c05650307030145121002409660700b02c0c2e0302c1e400064040d11301c50107486046869915400022160340c015400248076110070040761850b41050b400f048000d5000303550b50b2004850601190030201c0408200500c0f850510b1000200c0c100d408002500942c41c507403860f107165001d000103010725141c2e491644031004480c00c02003165119420400301401c1400c1203000c5101c505014070b401c1d0340e840920b003250070f80549203c41e416204c1010403501004a100a000814216034102c0300180c06039000300311445803841668403403a0340d0341e034613604514484565002504030b00045814000107000700c43d00f1850f40c5008500e00b0740b560f82c50083d070f100d1a10300801401c = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 528805728 1250 528804478 528804503
    0xd0501120f2604090c030b030f060f1306060b030106080a0e1903091205071502030712052110180204030b01030b090307050a051b0103090c05060f09030109060f0506010f050403 77
    0x8206110001e00303480b80d100c0d21507140c2d611401008000c10390040100006424000104903a00b070208030359100b1085c0340301400143d0307148484580b40c03100103000c902950079050180c01c0410150300c01d0001501d84620300c0340d680d502d40100200030b8100500300a03c0903140c1000466a400c000980e46d003007941c10076860b0641b001e503040540b0140d22a0340036003550810b0701d42c064100076000ca1010140c03034003140d5425450300c02203000c07a03582c02049002001010000d1048100070b01603806000c95144c0147c4500794014a0720904c20807000c2607030b150401e5050030b0000c2c00207107000000c0d00c034200c00b02a01181000d1a644500c642040180301c081c2c00b044050020483c02300301881190302c80d640107022030b000010545009030b0b6441003181181e1010001001c8000c466209000b14075030176400c41555009503003050100070359a4404c102c0309541400c2000100d4082d00c0c03e010309468107004020005203a4514031300c0c18161100100120304000400014904094000050b00e05490b0440001c0742070 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 528806978 1250 528805728 528805763
    0x6050105031c200a1406130b0c160204020c1b12031b2401030c0905061e010324050a06080105090705160f140f0f0a0206030405210d0501120f 62
    0x280b2410f4908100d0007414003e00034032039401c440c00d002c0180d0608039483c1d40c0e120750600c801020108801041c0c0301c04540480c6100482d2009410f4091a41940003405c4503954009002c80e48951b8102d021600302d03050401d50f01e040407c1c1300d4000c20099802c02c4e0300c003c00560b03182d01d80c8500702d202e481d02d144540400301c00481c00c026139848002e540492034980003c80c50420070001091008031200048a0000300300400701d0300900d030080001400200b801c2e0000580800e0481c0074640d1389041695600078032455604a1f070803440842c1440013203038171150801c400e0100500c0d0a42005007481290001001551030f0701034400e503c211790740fa20075103032482105910800303040c100001e071500e12490039400a10014440c1001c18014103800c5500740d4501404e56515424030b8402e0744807540140322100b01509016008650040c803460650740c001014030b144100d0940703998010358414001103102d0000649521803107014100a0302801d1584025030396000c40314a0701a4001d0640f52014600c500d2b = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 528808228 1250 528806978 528807017
    0x30e190c090903021506040b010516060b1e0f0301020a0c021504081b031905030f0c0304091d070807050d020618100e010e04090b01120804150c06050105031c 69
    0x14280440c07042c0000145800d0080d5101c2465800200710100900411141d25061040b6000210182c60342c5007410750701d0300490f0701c6000d9980103940b071945445100d01c05545100407042e004840b00b11a41803c4000801d01480709084000180260303c1000f48080c040c4d0411503480f2107540c1240c080d9401503940041500c14015503101d114a84180a40302101d004004150202400c1c1039044500f017850054030b1440f260fa00c90009000c81d0403c0001440b545841e01c001e00e0b1101902c001c5030325295985925004452031404003044440d000c40701e1261b040c41c103112000040a5903c010085141450b001502c440758100c0b000b4802e02c0000781c0c1070585060762110841d030340001020301908030882000645926215100c9034009140712010b80a503140c14440d8841c0c40d82c0000060b41c00f170f800c2c182c3c010102146481e0a41e44c05c0310a00c400560a05100030314182c04031542d6948000400354504441a0388044c3c0201e4400e4016001c51000b2488009180015050b6403505040211410018a0 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 528809478 1250 528808228 528808253
    0x3150e0a150b030f060d061b110a03120c1b05010902042003060904140105070c0501050106020d0e191802070c05040204050102030d0c031b020a120c030f0e0109051c020907030e19 78
    0x40a071030400211200c00c8e6200c0ca10803603c81016110f52024407100d4003029120b03042c0c80f000074041200d8040c00e5001c1c0c0c1d07207680184110603031420700c050802141e4803040700d480b41030002240d81384c0d11445840d0450030503000303030fa10343d104680c000c104050310020700590034000145164001c000d00000242070041e1090003006030700c1e014008200c030703040104000305902d000d1101030385c00c5e600700780001071240d1001400b142040307080c0c0e581c0e180c110000c0041000801d03140700103503001c0302e0b41e800208032a20024004015102d4400c4010b9580c51607240080b03440304903a2006110f5841032100300b10a980100489660001e0004001184e0084110540040011216428150081034050008503400203030001800c1d02602220083e080c544800322810460081c000b030000300c803041844c12142c0100da0120445005050085407552a10f01041d10880c0d1040055110450000c540042d81031100b51140c01c80d4403440c0601ca12543c06104550b11007c0c0522500c500b20300902c0201030009580014 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 528810728 1250 528809478 528809483
    0xf0209062a070f05010513030b0c030912030705090108042105120105120d1103040e04030c1202010c0801180b0628091503050703150e0a150b030f060d 66
    0x40303032140054032007011901d00100c1c1c0195000d900ca07080344210800001c1100803101024200c042c02414200112141e4010741a4201c0c02e2480d00b40120000741e945400c00d100783c001513191a00e030301e480050300780f03444c0b002354285404010800078000c88170380c044111502c9032804c0c20803460a440e0303868507407074494400d001c25a03041d5040127411a4142d1243c018460300441590850349a600d800402543c01c05100321203003903034414055400e0789402102004805d0746201c0c2a281800d698105e091001d1404030740840004136000105010000900a84140b110103031000b00020742c031102c0054496607040c01031480c0009909120301c1001c1c01904680408800504001e46440000d00e107012803090051840c103548201080b5261220301c981c0140084540f80315803200e0700201103400f60010000075203424100740c0c8500010800a000d03440403801059500d505d0542c48c0791805a10302200c0e20110391610400b040c2408101d5443d4020541b90091464104043d42e40c98000000c0c0c090406a07500 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 528811978 1250 528810728 528810739
    0x13080405100e150d0b1c020d030207170c100e03060c0d02071506051002060c0a050a03110310060228020f011b0b04050712151e020c06010504111207030f0209 69
    0x104041c00c08148068400180410b4007400902d82e03038800c2201d98100021b002100f010300380c4d02000540f404140c0b4401043c02801a0b0700304588445c404500c42c0303030040c0717106c801d0360104d1a4401ca80c1007021031081c01d0440303445d10030b0611605400107519403202030610b00c0110350100720992401c85a40c11101d160342d10000710158001030942802c0940308910440380328403101e41020324102c3c0042070300c500c50f03c004050320f4900181004250340d541c0000b82c09008040c1c2e540808603240491400460041e038414070b1103000c9520f0500020700d441c40d802c9100b00d143c1026a80c00f103078202c0c0c82c0404040c45078116440c440090440d0012902c2c0701007400c1d103401079020144014140a050302e4080c0c0914000c0b400c0d80c81e11511003100491070b06d4031030310007007100c20020040794600381d56911a00440b010300b44004640600d503040b40e000e076000392070010742c00e4000000400191071709110b102c0020340d01290700380c00d00400340d0740c003110070350014168001d150307c3d42500840d54565504840294600520 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 528813228 1250 528811978 528811999
    0x21309052d1509010e060403020712110603070e0405180703170c0118110406060806211c110a021807020a05010216030e09090316020607051e0613080405100e 69
    0x745440145043c1c0d00c020b101e500e002400c00c104c0b00007140113442160035800808404c1d00e4506031450039000d8103c10303943c0c00309600341781c40c980e40c031240254003c850a86e2122004420794040008442029048650303050800e4001c0100c09400710f201c0c01101c0d0080c1c081a48102040200f40710344c400c1082540142d4a002e80800100560914003070045001c0c1c90560361084440c801c0c442151050301a020110f2403210004459180c01d48072004c80e4019000258154224950b419203040420a50003143c3d541401040308446e1344401d0111602c4ca01b1801080e024001d900842c00d00801800c100c207140304178030300049445008112192203594000004c43d655008404900005009020100c0004a81449448192074110010b1b40681004030185240c072441c01901d1681c000c9030b4030120307006107003402040086501801200441d10085c1e8813100e1407a140b881083c21302d140100042890f00307811717034000d0106000c40c060b50280c40c0c094584a030100091901514104e41040015a00031001003 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 528814478 1250 528813228 528813253
    0x308010501050d0e06042618041802030a0602040812031e04140a03051b010903090e0a0b060708040f0b1602090601110a120905011418180406050103021309052d 70
    0x807151a089102901c0403050031441105140341031094443c0c611824071400b888044c05d1801c0e0f4444450b800ac0d18285d00d0041c000c550100703040c8201c014080c4c507071560208003040814800d01000303050740c0c0a03c210301d00c0c502e400716544810360032800301d80001010020004040015a0307440900c650b6122044400001d15454010102d503c4490303204004490421020840e2030305004000d104d5a040d203a01c02c122b0304041111f06402002020020038644407110701082d516188010181580541503032a0303101d0400343d4583d0b0080308c1d07901105204004201904e2003c03c0c00c00210380c000c0c5d0407200c540b01130701d0740001200c1c0003840000c1c420003405250081002c100c400c44001c004643c0340d480d1403504a5a0310015203074003034841c1a0f1f041ca80c0d03040000260503c1d01e12006901c2600043c07042ca854101c07008400c4000b141218120f0b0b6041e1703120014410341ca031810344802850b145480600160103259646a01c8500d0b903885541d820f1040d003c2c01040e0040f9452a14081d1900c1c8100c5040b0b41901 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 528815728 1250 528814478 528814493
    0x21308030c0c0a0e0604050405120d060e010608250207030629091b090a120b011a03040c0e0601020109021f140304080f0703020f030a03020a1b0308010501050d0e0604 73
    0x7844602a2031003041040085400c00d540041d0845481c081030b0b0040f980d8080030700011b40f40c001e00c125103c1c05801054030511000ca0050300f40d9080ca034000080ba5403c103584002080c2041e0489010300881030200150b2190302104080d060301e86070414110036403901012ba1402c2d4450700b0050003607050010040e4642d01804d07000f00344c0091103015074110358540c8240328207020280c4815aa01442440901180070480010f09500f5806002106101c3d6200c2290383d03804440c02044420301c0100d001084100002200b01c81c00100c072141a9156082a582d00724009003548104007031a13080d040054550380c000e44c00024025005803000306072102040039030041010300c0d5600004141204040c1c00c1005219098034800c5600c130501d01e240c5250750820b00303400d40042d6401c4085210783e41d510044500184003800401e0490340300941c0340c102c00e00014101440402024092040b10051480443e80c003888a504540dc01c1c20f01e039a8610710741c072a460142c10f030049040c2c00c51107a14140010000704 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 528816978 1250 528815728 528815737
    0xc0c060c05010507080402010e06090102190506010602060106050a0e010e130f2f072a0902031914011a070204290d03080f1801051003022103030a090602130803 70
    0xa40000c20040e40e44200175101c0748002c1da0042c0c00107110a8440001f410f10f200146410795050045a816400074131142001600c0d02c10b013200c1c540c212100411140d034040140501400c05401d10f1400c290042500502007010394074100d04205a05540d0034290300d50030403440ca640001d030014046445d052035000c0181003c4960191f000041004410040d25040c1400700c0108000e4009441c0102d103072581800d141c003d07120440416800c0680c60754190400d00715200131f1540c1e00c000f50300c030316001c401d81d000103181011540001d410f00a21484940c00c03c03809606550400030408094450190103003840cbc043c2d0400290883e240c03081c01036100c2d0300c01c03100c0d46995030001c0f0890715101d080f0381800301d800303c4d010009000c0354042001c0f80c0c075202003050807a8440060004500b0803c0b00c941540c2c00e40f039003035444981e2400c00420900c19400c2008444410012050440f16038030048054241c0d01c0c4401070050041e296102910800c12805030100d50203504c0c8040f01c1b0b06400c2d141c480b0251039a20 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 528818228 1250 528816978 528816983
    0x170709120c060e0a03030909050912160317010308030a0e07080f010f06120f0605040203030d1a03060901060803040902090a090e03120603010b0108060609010915020d08150a0b0a0c0c060c 82
    0x30740c092031a003881d03c0d813000019130f9419900c418000d46003a840c1030140c00040e043c4503050040d00b06c000c2400c003013100a041c505140e100d40c80d140310030038100500540c1402c41c2400343d0040c072800503c08508010100d03900b20341e030f1800c006868401c050303800f400c00e240c580000b00d0601406846030018081500f00c08502c00d00032204010503036440320700303c1181d4410b5100600e00f5440c0300103280440c0d401c0d44841ea006c7e0001d003e50f403910070341d03602c03c0d030440c0c107424030401500d101c0c1c40c02c0501c582010890365901104200080237210f080911640d600d0041c2d20481c01c1d22900022030280c2c540310340d88440002c00407a4410b00c00e10780401c3c035003616034010328894845420400c0005100e854140144914140107840741509901c0307080c103004043e40311f11405410300401c0000003d80c45e40c4c1078444802c0c00c030301d40c3c05050061000e880043c48400c011300301c4401c01c40d05811702c40183d030325681804101c5d0450f00c00c0c191350fa0314115003038600048501029007c0c01d011240020110b4100410604252 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 528819478 1250 528818228 528818237
    0xf060905030606150a03020f16050d0206040b0115050405040e060f0c18102106060e030f2d030d0f06050105180913231c170709120c06 59
    0x1034480c000d26507101c00c2141c0f0140d200708080d4034040441041c00060040401c240350161401100c100c901e9540ea101e200c94141c1001840c0641d002e100d01440980404a2a84003515490070143ca6408042d1018054051816103044010b90150b00032401c913002400050000d20030951681c00841d1158400c03142c47c00944841800258070701c01000c00c44030315241c44080c505062440781c041c0702442001c004e04030b09024000c42d8828022050a01c002c0349844160070101c0e1150074040c0c02050046989840b034029441040003011404020410700103814122610490800403411501c40c1c0c09402d4919514502001503280c0b15482150808418040010302c24000319507207800449036442802441002c0c40d2000180e03244525020b407900707402901e400300700400c0e01c00544641c190440200e0159548904451040f040032006000068410359028007400d45900107941c00f4050600d00e0f003241d55a0212407001854644c040c8100101070314141600f05042001850045090f000c140110340105 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 528820728 1250 528819478 528819497
    0xc19050a020f0d0c060f030b031912030b0a0e0403030216060b0312030c03070c020f031209040b030c0108010312120e1011031603020d110a080f090c1c0302070e010f06 73
    0x3800c1c082803d6000796484507200701c8691500c282240c4004443c20704c40c00b01903d81c070b001600780c1e4040007082c2540ea4040c0c0c0e10380d00c4540501d00864404000e0032208141801c0000e020666610711800808581c03142400680c00da46601c0e040b4000d00c545007101007d02c1400c1c0706d200c280001d81d4440d0003080c10a504803424140c0381d0701160a0340c001105c0225000508100180c0c1d024442c4580f00f000501c094062211b201c14200064100900060079022a06010a0004040c40d080c000c08141410a5001d8824102e02c880024401101400040d140c100c0300101903001c0c5215000100e202002c99408001134032107240015224043c450f500084641055031031600700d140b080c1141e010b580c00002625050204000640c06074000a410424a568400fa48541c1d242180c00404060382140d072680d69500e005d200181c005807003d020740046500284030b00d2031980307a00b0305070000c00d05000c40031442c0a0320362400f2032500080350002d100c0c2c082004000140c602060210b80c069840544170300800 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 528821978 1250 528820728 528820759
    0x408040306062106090213020406020309213007060207020f1917070321140c030a11030d1e0b0102010e07031b1a0703140a08010504020c19050a02 64
    0x1c4124039060480745001005603d400241c0540c004580780d440a0b19281140c014000000100d0308254401c030050780002580c0e260a15118a80f114401c200a07142070032140d0700221680c7c1c5032540f401040c12052049084500c40442c0099444603c050800980d915801482c1541c040d4100c9107040340500502c02c10041c0724546081040c46c1d0040d1150003200c1c203807500001d11b5059409001b0a80d180c060b0304008000b003811a41c5003401414003900c40c9900c5403000d81c0041c0305840b0b40c000708600c01028011074a242c2008811110f0140380340c60442c140410351102c050862141440c0050070a282142ca078140640350400720850b0000110708100b041400001a8260b03183d62801c5890b40d000520144005070382c2107440b560041010055040d0720f52a0510301e168682800d80b034400c038000100b5540c04255101066003404105071320460301304521494090721486042c01101d210355004500d1600c1c959003001801012610240c52040d40b100c41d0038140c0c0c845183e040c05038002d0a079000712000 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 528823228 1250 528821978 528821999
    0x601050711060f0d06030b0609060909120d1d010903030f11071202070e0403120c0e0915031609020408010b030c01020a030e01140a180501030b060901030504021305040804030606 78
    0x500c0e030340141c8196000c0c080801000b250750b01c0010740b00c841e0103041c0084039103200944130380405140306100b50390b80e90404400304112030f5001011144190042400c00c5482c40010030010403a00008807410340f541d0803003103042c01800e404000803007010140704140100d00015000084007078003036101044150010307071902058660462100d9102c1d030f0200b00e02c000198142900030315250f014410744254680b07604071076049504c20f8900b0780005409031030902502c4140d03c900f10f4242c1321410090f01840ca114082505908010b29a140031401c0341c0e0040308a0b10f0030321104043c40d400303004803891152501c1402000390440e0081c0d5500c0d61070f140308403459080000e4845104581600204410411650110385280410340010704100060318200650060f82000d094948050307200c2d81444004190b4200f841e0310254030082c1014101156101c09444160450b14590001e184c08201c87d510b0b030000c1035807600c050b071045989034604070803c018403880c40c0240090741e02c140c10030f00c44e150f5100c0d080305 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 528824478 1250 528823228 528823237
    0xb03160e1e0f071e090e1f080304140a05010c0b091203070903051c0c02090a1b0e09101a0c0c09011e0e040c0b1605060a0c091d07030e070f120605060105 67
    0x2002c1480703179030203015045012001c0c81d030040746020030b080c089456001403e8040c0880d4801185588045030600031110003407244030039044c0c10b0f124051940c3c501000280000742c0101c002e003c0c0c22455000c01c0c2080020f1110f0710459a2650400755281015003000b0f051002512041d2114022444c0aa510403040780741010f8560140d6030700d60b41914aa000c11808040c09400e210215a0700c0449d0a4030380030b2030650605041c01c9407120020442d007071082c4951000020300c080c0d10000000014060b0103070b003c100e0ba03240503422140546420007801103d00c2c0c042c07040c05003507008a03200d000107407c071502011091401028502503800079a1142a14607125043d50b0062075409071401c00d20041748000003801d400c3d6001c030070300d80c400305194490505028050f5943c0c0410b40d140c001c0c40980301c1d00031101e407004100d444410003841d0000e075080e001b03e2102a05480802d6194a1008501001000300001803d10040c4008a0f07680e00c0040c1414000e81c844112030050800000540940c0500240c5 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 528825728 1250 528824478 528824537
    0x300703050715030e061f0e0a09020406080f070b0f0c0106030c03020117090709092f041a090a0c090503030d090302010c0f021e2406040b03160e1e0f07 66
    0x208011b8440f800e50320f802c40c901c0d62858040c4004840006088402101554000c04031041c0008054440b40148405d50f00350350400111540044512120081c0008040c402c940b480550329844211a00c816085440350002d681c1d419800c0c1400402441460790313088080700d20036261a0190024200107500c641c408407903d000982000404005204554220000041c405c2420740c500702000d09021030b0b28a1a041d0300c80351500243d16040003030401d803049800300301c105204642030041c100009012102e000b454080c085440e03404900d60a8040d0000c035000e8640142943d4a44a09008040081c5600c004c1900150b003082c4011604134050f503041c11300da210f140e015050f450094145481e905003041c0f004c2c10b1903c10542b444a079018a001e0100550500603044480c5043c030a0070801545e00300c8151a220f5040f2075503003200703003100481a000b00d611810030215965210904101000f403603c50312801c118801c001c124169502c2900c2c18455500c64403043c5103104029000058000301c401034 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 528826978 1250 528825728 528825733
    0x512010b131b14122805150f0607020307080a0b010509010f0501051b030d0213050604060512040303060b19020105180304090f020c0109050a0c14300703050715030e 72
    0x40440d020b103e104244560704400b4080e5192009004204801c094100c07162000d0200c0307000039804c1d280c1ea41c468a80141c10b5000c0600c07260500c0e004c01d500b00c2d0074207060540b1901d0f40507451210383d15000c0c143c440c400d030002c0680b01400c0c0d40d442c0e50750700e0300c40c01d1504440b40c250701000424103180110040f416542c001d000e4044280c1807600550f460b40c0b040d07280d0032540c05002418041080300b0001400c560032001d00c00b40c0c0715031204030301d20842c81880e000b4a200301014082405070326404003d56015000c0c90070112025121810290002e01894101c0e90003400300040842460307c0d6500003541040c05940200195503802040031502000c007064010103420410081152911641050f514641d51050040ca800c1c03200042500311401079000315419040202024140a00d00d90000f00030016142040c0d0406004400100044d1118010b0700814800c034000c5511034503000d090891070325014044808054490a0241d035810103446441444807003000e101c10006c0c4640190306a030f04100d0300 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 528828228 1250 528826978 528827021
    0x80f0c04050d02030102070f120908010b030307022106070507020f1c38011d090703060515190e0714070b0402030a080406080f010614030402190512010b13 68
    0xb0040c8889002609a034159001e00100020a0103080c1070500c030f40c03259100b040103811a01020781000381d2079010301030070f9142c0016643e154601008039507070340b54101c80314035190b02543c1c5841c08480b6280305540003882540208a9043d40010040110f01d008079188030444101008021112040b010180c4498004d100e00340c000a01c2d52401031401068003c1c150078084900c0d802c203940c90001c0590003a02c00d503400c010000803d11200009043c400c0680d61036131441c104001d540e86030f81520001703001c1c0d50359a0000b11700c10401000c0b4185008020000080146950790043c0040003074040c529411500002064546006084900c214464a0782080c2800e03040e490709110402d0082c420b98040c01482841c20004280500074800740c10951140007050078000c1d90544201c005030404c2042c080c0100f44840387d00404000e4940c4554104c482d5180c0754461075a1070101201e951005812032209030080d10008810340200c440c0d1003040e506500b06041003600702055541140703200c0a0aa040308 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 528829478 1250 528828228 528828239
    0x8030705180f300f1b030c01020d0f020102090405011701110901090306051008010203100305240a051f0803070201030b0a24020c0a03060c020c010206010e070e010216030501050403080f0c04 83
    0x100c0c01111000e110344210f002c481e4441940b07091503141452030781c503074210760f00010114a40251000000328160000e24034503c1c2140042d5030365150640060900c10301c1d405241400d0700c02d40407981407107400781044c040307544d550f9031900402d5100d00c0340e8280b035400c1c1440b40c494015000c00380e0307154407030582d10542d400d450f41d2120002024081e1180f0b002c3c0503d41004070f4a401d090008500a102c0096408400da01d1400e007141080407420700c2004030003400f40c130390406900f40700b41150406140100010035494030103e84100d00f0604c040140c2e0401ea140d40081c1000d008805050024000e8805206c440005810089150100d004000c16840c41c144040002510b02e032406400055500486020000700000140794280ca940210380e0704d80c0f40e91200282c01d50602c8040c3d01c0c004203000a101c01d504160140f002e02c04014036040800c160144040f0451b0310800070018440d02c3c40d416103031003d45038145036003e06000c4800340c01090462011548005144000500c03910606030b1040c04c260429 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 528830728 1250 528829478 528829519
    0x50310080d082710091a040c0305070f060203030f130f050615091605030603150a020406030b09042a0321080615180a2402060915150301060308030705180f 68
    0xc0d02500c664a9408851b10aa0641c101c118040e07805034001140d0580766290841c600010758014500d00b00c807500041002c2500003050302e0b007010220b000e221003903840fa182030301d001c08402d1b1302414411001142c50140700d404070311680507100b0900303458201e401410030702c25020000c1e601c4910018600c1421a020f80c0300c1c902440d0044001400c1d41c0602d400c03195441007013a010b5680c0c20030b2a0703000408001c984e40500c80c481c0c40640a491846c6c0c50704d0030b51123521000846003445000030b0001140640460003a88da0030024660042103189144800442984500e503014641e90105681c0004980c080c07414505d45904101c031b41d00c1d0a483c1041e00c1202e003410903528601c00382c03c44541c00e00400c4c60041004000303e1809000724040c0560032850000b450300d140a400f00c3d03c150070207040c07030500c4807a0100b0b040e4800103850309070300c09854140109006000da0341c40504048004000d001405600c400100411000c1500003001c2400103020400c3c1c0126120f1003076032141700640c02c0c50160030f04c0e = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 528831978 1250 528830728 528830741
    0x3010e15030a03020c040c080402090402151c06050901060c08040306020f0403080a020604151802060715051f050a0b0a12060f1d01090209010e01050310080d082710 72
    0x41012440348440c200012902e4551a101c04402503080385c032a0040c00e04081c442d0700c08040c0c3d1450031803800d05182c2c010807082c0d940900080c2c003038040580c60f40d03d201e905104961072082014088036120055490f51070081035940100d902c01e81d4650700001e0050f03c0350008040c02c0c0e422001003484c0a00d5661103030000c0d4400420600307050010b10002010440b080080c285210290300078008524042c0b610481c008482d51448400318540b4070200a00c000c410000e03d00b140c0e043e034103180d4a804500f08032449003405146160784a0518040000b42004400124444166070b440f08125613103500402004607964014071040103000d12107104c0040c0318540180710820006070004120703844542007003042d080d47d04000c05408040f494010509a400441401403041020031410b0401d824002490410702c03c604034104032010001c240030f00d0400d882000102104001c98022560420018004580803030705007601d0120341d0307024041d58401598089003107100601070010004041c81c40e030020b004 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 528833228 1250 528831978 528831991
    0x1090b270d0309060507020607021b010302270a08010b0d020108060f090c040f0602070b09150c0703030206040212061308390c150a200a12032003010e 66
    0x40c244004210a901884061808101d81e900450694040c0c01c090090b54009004042154071050030058040d0340419444c1c01a4880c2080c6032289459200407406400703030103041d000400c0404e18060301d80050b00c8075000710310403c0d544010026503641a036400c0301d40e43e0140d030340c01c860850401e40c0158403c000043e40001f0050800745000c05000c081080c2c00b80c01c458000d00c001c00046d06201e49204400307030000504c0305100600e10760741020801517450050440c2c076400307543c2500013a807800036068150348070b400d03c00381180c901e81d40c0ca040007540c990341500d05902801c1003241d105500040454401c0c812040e201c045034003143d080c1d891001c1980000c041c101010300c030410504c010b40d4189004421840c8a0b0700185030f40211603070182c1440000440184075440180310b0252450010b415101c03440800d081c8a04604072048505030075004025040869000e0f0501510400140741b1200e001b244299a0800645003003900c041181203c810b00450f010a05000410202c114209003a61062 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 528834478 1250 528833228 528833281
    0x7050f031302040603061407021b01050409021303150507120504050303060907180303020604110102061909050304030606030503180406060c020f0d051c08090309060a0309020a0803030a061701090b 86
    0x350f603510346ea8121070518000505c048014003d0069565040204000b0a918825039200207019000040d11900c00d5201d00c0760946d03004108100d54034054206000103681102d0f010921110003224140140400c8888901061050300d040c4001103403442010322640d489001945980ca4178000c000c402c8000401702000c10001400346c007240351440070200000e510a800070005810140f6100090f807242051907811035211804000b84602c1e040201032144002d1240040c00a81c0713420400d0070342c4183d0304040c001c182403c4002007000000030080c600042c160300c07429190302c2140e08000035a0118418000042c240080b00805498000c5070346000400080024004100a550701e80c20603074032824294280c08942c440d0400c03140c00201081d840400c00018510b00408000020501d000d140b4039201099502c801d41c40454035031070100f00140122408994a0f864582424030141c07599000e503680030b0000c2d421211619005004040526601c03542e4062556241c52040b64840d01103204101040f = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 528835728 1250 528834478 528834491
    0x41511070f09020d0b12010204060306120f030c0309030203010501170607020d2a12050721020d050a020a051204140405160e0604030b0112021c0b04150209060f04080607050f03130204 80
    0x95644c1c00c45000c00840a030002350312545400000390444920340c0c820070f41b0202254420b000602500269111154541451040310469040c1210810040e0300f000750103628060020406001014044401800700d0f021220b4607030b0b8a000c1262213080a100071f00100b248444500f03800240302c080e840d0041000d29511440d000c1e56200c1c050768503202c80c4210301280740001c640082c40500100c0c01d03004060301c10001480d4062101c025a900c081201140401c000862030400c218801d000c10810701d60001c040b0398640e880b0380d8210394281c3c0a88240c0c2d10f007100400c1c1d0180076041c580a02e601c6144060181c0428824003402609e41601294009520100400007c0000789024007014040c0203102d05031036081d9045e00c1445062002080d01e410310100300d060800000d0000084190b00580c1700c0c99901c5074180c115000d101a02031302e4805607004801081d4403200003214002340c01281e24000458031913403a170b1101070342d0750322803030114031081c502c00c10004441d1303e454040c00c000340b031000d0000070f80e1 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 528836978 1250 528835728 528835751
    0x80f0c071703040203060c0403050304090203271605010314011403031219141302010c030509040929090a08090f06040902091203041820041511070f09020d 68
    0x3481a40a0a50707610103021040c0425410308204640c2c3c4070101604442c606411611034070340e6400340c0c0c45440c11080e0008006205c0200130000052100c4c503600704203440010080819842d208001c0c040f48072103031400c0001445600c20700403a12003040901500c0c086909115161000340c96080c0d07c960944810441900c5895940641c0c1b841421a01001c6c01190f07032410031035068034007540c0090004088101440b0b80352000c2c1044085559090070117101107801403800b51124010001001d0b4400e00c1d001e248402d1181c5100f280d81042c5000e140c4d428156114001424944c070240e80000056102c000f41400003082600142945100101050100480d060015005511542080c074406801245c81c40313003810040700c4104100b0401c4041c40c08c0a0800490041c400c2140940c00c102c0c0342c9425210001401c00541c3d240c080c20304980807070b503854440c0300b9914032804595000740002c1c11075600f400711440100e00c00381030b20b04158000001c0e52402c40c440c0c000e074121081d4941c2c1d4603580c0440400 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 528838228 1250 528836978 528836993
    0x504090f120801080d0504030b160c080414030f01200a050706020a3b06070c0f0b12010e0103150905031224190b0a1101020a0309060b030d080f0c07 65
    0x7416030701d5251660500e20341508011400041c0310030300c107040c0018000546e903080b0607079100d200c0d4241d486001110072011607601e480c1001c0a04400b200280c0414426400403007801c2402c015400c442d081c0802e044103600720350094402e011480034000d080700c1c64602c3e0200402100100345080790902c103c5440707080813039004401c04c00200e43c3c0900c1c0ca1850315201c09031050142e901d20080100d04e090104000070211056048a1291400284c014100540000c1d620003605a1491010b00780742c45d502485191703400042840c813215401e000015826050015150689a00c4910b1411314694450004007404540c00129124041400b950001048100e089841902c40d48040b01c00070a0074240100c1b0384400800640c018060184d04403084100650600110340303258100741c0d500c90391004e040b58203214080c800640f80d4000039200e07080070b916400841810340a01d10821143c44a00b04055071a800c2d41041c50104000c240060340c03e140007001154410201000d00b0b04d0508a60f480f000c = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 528839478 1250 528838228 528838253
    0xc15020a08061c11010e040609020c030301050a0f0b091c0b071707030b0102120c010b130b0f0d05150a0e070b070c080c010203070f0203030d090b16080606040504090f 73
    0x100107841c0e90308109603860200700b0b1041203901c2001002c00186591601802480d5412115041c849100705441d030035110b50748540e0041501c00341c1152100705220880d9101e074028809c1c00c0c46991550800304030070311109488000ca8581031921840c086411040c0524185010781d201c05a40d4490344590200d03001c2d42c10248160496070302d0754495041c0c10304ca00c8000c80040d102c10201450080320860f566000502d00c0d0701c030b884220380d064032283c1c4a02403d0141c009025001c1d0030032130103601424010a190051150700c0d101b01e524070441d400ba40d0038050400d001100282040d8000c1e84c03402d01d014182c05a03213422408213040031420000300100940381a5141c0d100a40d90f40c00020b41a0601030041802c07805484c0c0350018203045045c01c40000d40e0b0b0302076400702502c2c42a5018100f011541c00300101e07880c01c1104442802140300505222400200448500e564600d103804150101031113092454840c03000144080c3c28142030500348801400e40701411a440600d0015030b0700460201060724 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 528840728 1250 528839478 528839497
    0x803220e0c0703030f150e2a0703021005150103050417041e0e0105090712141503011a1c03120f0912080606040b0d0b0a150f051204030c1502 62
    0x50b68510316490300a0445140014010907540340c0110000c01240001c0c0b1b000407607140c02120074481c1c1382e443c0200d00381007000c03012100c03580c080110400e110034164050710803140030b60207031082008000301c403e068076000c80e91110341ca040041d01c40c00940c002e91120b0f4103d4003440200201041c80382c0c0141d01c542c0310350004003610311800e5084140c444105100350141a09594103074841d40b411000c0b4404c480e0241c42e89080c40041485c00e426091140d201840d076645448030307a502030074102054040710350002000f85c0294200179a0642c1c05880101040c40344c0000b400715240c1100c1c0c0101e040408142c00300850070070501c6910b44140c1c24050041d0002c03442100070000d415880d0b4074040c10700390628407032407007841030b2348041003841d075134000590742103d62a100603581e6141c3d940d00301740104040d8a10503800020000701042c2c44801412900d44035685848241d81e000403890241e445000704203030018244c0d000000100017900c207040920285104803640307040c1c1403a080080059030081000e070b = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 528841978 1250 528840728 528840751
    0xf05010c0815040b1f1803150c020f06061e060f030f0f071e0905030f0604060f06051f03060f080f0d05070506041214070614010902040803220e 63
    0x703100405600305034020b07074080e0440702001030214030004108401c0000c0c5c11241412285e00349240326502a000f00800c448a607100344413101c1d280c0c0b03040000603281003010329105160600e1a260315000244003000c034071495000384144d903146001c0040d0002006071040d0204615018079a680d12114050079408000605141c2c0720324002d00c0c0f6501e20301000b41070a0160100c0000d1080b6181c11010b040342036204c46608120359010704100307a90904c5c1070b52060342c041c403554642038405403011440501070361040c20140844817000b600c0d1300c15203a103409242d0f0300100130141000c40041c103902d0301c140c6907041c0c1004103105940fa0309154000000354000d403140e0f0000c69190000c400d00340480413031220346003040750500b40c2035116903a541c40000c0000789441140386485100ca03000f03141d00d200820380704580d00c0e51500546070450103000b14181017007211608800209186a02d4000c5c1c6c0c0c01e4031008401141403200411000035101001c0181024011440d0008182d180e00c004602d13108410304002e = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 528843228 1250 528841978 528841981
    0x1703030103110a031a090a020a0303050304060b0f060f0c0f0f0708010f0501180203091c0302180307060c080f0f0a0905100e0a090209031e010b0a09050708060603040f05010c08 77
    0x400501e01001580b185100703d600c0e00c010b200140d2410b0039664444c400150900080d03540c81a014a00540c1c10000307540241041000030406602100451245100d0ba4003403148a8050f03049c400e0000301604e009902200c184242c1c0d80340885500a401c060424400311818036242041c118102042071640b21419040004c0500c0b40d01400d015a040110080d10200215850f0480d558078540d9004a0b0b0440e060f000400311b00c0c10031041116418011015440b201c806500e910050025807008440c260140038101400c1c0c52450041805001c594103034440006c000d1081d0366080c00b0f41d20140c0300d040d43c0e200070b00648061804aa028043e070341681e0b162540c0f43c50400701040a091680b584c80300410110a5240146490750b02e400c0003120501c0501503180c84108000a0900302c00594001a51501c01207440d04900150080b850070f89050390032281481e100c40d41034058460031140907010450001c041155400d102c4004c5074068012000d203d00031003260f48035400d48202e50600c0c0c0c0014550b20 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 528844478 1250 528843228 528843233
    0xc0602042c0c040605040302040f021c0e0d0201050f0601110a1b060905040510031203022206030506034b0601050102071e090f02090907050304050d0309031d04061703030103 76
    0x2075a0766004501d0001050030985024001030161095020080c011901e5804406488006805031281ca10090844c1100b400b00e541003e0010000c0c00404601e500c280d150791003840740107104250240b400d0cc4011605030341ea083c015550f0081d80c2000300018810401100045181c1025180510b00342540d01e00c441032802000405c44100d54022900c218a06401d1105401608003031504496200000002c00e0a118806070020b0040c05154259000002081e43c1002d1900c400c003020385d40b082c2c82c01c201c00c2d105c10b802e040d6207a0305482e0340c81c3d404c0b48041c00322039202c5074150038640f1440748411468000c803005c8031104502141d07860006283c0d2001005001d1903805000300009440c0102a018400c40140740304000c0da0034501c610180d05503070340702040c00d842c40303a0100c410340b010181540000c0d08080c08005d0880d80111425030300b41c06014001c0051500c02d0041c01095134140d61074003190703141c582c05104182c0c03150403000ea0159031404c0004894101c041c1070b001d4180641d002d1501c0350f1450 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 528845728 1250 528844478 528844559
    0x21b2407110d0f02010b04020f04031a01120f1514180607092904060f1b020609040203060f03070801060f0b0c03040608040c030812060f040605060a0c060204 69
    0x180c10302090001181c900340c402500054208100c00c0340e0300e0710f48101d40c40414180d005142c03003488590018000034240481c00101d10003042124803540043d00599008145100014400c0c0102203036400c001d280080460844040d190985000d5070f900c0c085410380912450443d020f200c04004070b0355032102001301000316000c9001da88040c25005d40720034500300800030100c0c8580d01503101e4201c400c1e40311804480f110101002034104410005580c0d03074540d0400b07030650400004940001c1c01d02c00ca24004031001c612010b0210364007410080c11b22824a0400c40603400c01000d540d0010f260402610350390390104650002420350000014038681407049003000241c4942100c0180c0302c0c100203155020f42d0010440e4102c540c40d02d0003401c2a161803600200304007661b032004d0200280800c2d074500703119640707030824080c007811520510359440c030300305210a03a4654400d060b8040024007060444500600c1840c00c0a44260b9006107001c1e2204200c040880d210180300e202c0c2c2d41012400000c03001503 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 528846978 1250 528845728 528845731
    0x606081602010c020c061b07030f17090d031101090b010e09070b1201050f01120f0c260105010e010e03010e060402210705010e040617061506070b0109021b24 69
    0x501c001e000c40050b0000107581c802c0c00c1a0040c1c005c00001070302003101c065145880480e0005841903c03003c564909144192101c80141903804090b581c3c44011a0f40129045031020007020b452445503416076101030b030305285001c0c40210300d552034000c2500024042500e06018181d189010307050f6080c07512005107003440c0c0d03412000c0316100270000c1c09003407001009503604450303046134156000d00c03428004aa41c0c402150718400c505040603a0050040301e42d410001100c0c41d90f40c0e170314480040700e0324582245061400b1200301161040014849544610100d11100c641810422540094040400c2c2141c652210311000c0d5084541440214506560202c08280700081511100e14101e001651140d01c144101814060aa800d804503038450303400a40043c00d080b821018070856000e02691114005c450825141281300c6020102e407034040103032684288c016040e1605a8203240e0380000940c0910610014804c0321080010314800800c0b0351244c5140d2003800f45000340c4403281d2651110780 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 528848228 1250 528846978 528847021
    0x307020d0f0f1d060913020405041a0108160e030d260c04060c0f020d0b091203092503050d02030406170c0d15030b10031a07080402060a0909060608 65
    0x81c010b07455242036404003003607220381030f140700d0040002d0300200014910b210701030b400da4110f107140195590702ca030b071940a401181d10076034050101c013000f040c444040c000c803010241d0104200501103a480205115015180280f0b402e1440001ea10800003070701c0c204401e1038a0f00003401d110030b8181d0480b500c203004070f00303002c02200d035440740d00381204c0c4212540500e020780400c004c002c881d1081400140001010410b801800b01300a4106500b849135040c00210b8103002d042c8142460410740550311022603205450000280044191005682009000c800303d0107140d04aa40701c08408039605011078041412980c008540d100c5c50014050141e0b10300320700d417250030400c403c2088004031000d021501d5145e8011800940c03d441c03ca01d8040004107038201802c0c8400100410082c082420030380030a890140005c20b040b5140c169010740000c2040310190006420700020a0045c20080040e004140302400d061100c0394841c00c41d80111101c4d903110340001506401071020381100c2d1090940d201d031 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 528849478 1250 528848228 528848237
    0x30a1d030405010f0f021908041409060102030306040c020f01061d01120b0606070303020c010501090c11061b070309080105163b06070506040b0a0b09070806240307020d0f 75
    0x20b02e8940043c1c4103800001001003809102e03240c11098a209100005100e203501001c1d01d105030302070910240c0c540260040c0c0c24842015003002030245803560181c0c2c4100c905a00552450365600180300c0034206e10160303034043d807107030744c82d40c900c074032028021600940240146d0151030f80441c21003849410303060740014500b01800241c1004111003a0540742d2240091b41d04903541c5110f41750840083c1306415035140e59510b060700114210074a900030600c4140340d43c2c0c0e0b040c40036024240b855101e0342c0a840da40c44604a002040c0c0ca80380c10480545051802814038540d001da6038500d90b825038004883c080c08a5140d81c60b848403258000c0c1d641e4288882038588030181515510001c035000000c105920a50004022070080316034030002203481085d801000d07a100350501d49490548001c041d507400c0c02c4641049860b100d24241049840e103c0c0074a41d03554020f68a500c02846180d842c0402c9544603200c207203071014140420310008500407409a80240584100c0c0301c0d00a043c40c01c80d61a450400 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 528850728 1250 528849478 528849487
    0xb04140907030605100810050f071d0d03140d0603020114030f061e04022d13060804030516080c070905090304170a02031204090c020102120a1a06030a1d03 68
    0x380300180d8001503aa001500141036200c00c0400d491800d0903500088244c03046800320001106545c01c410b015250000e880207681c1c40c0d4180c01c4e1b41070389400105038440c44607004011010b261610f01250312a00900303121418910351384000840e035218400710320200d52280e40170030131540d00c2100050141c1001c4030031810341c1068090306540c10700181c4001d03c0b078070800440f1450341242c00d00055440900805c02c56441c207002a40c040ca034050280002e01c00c1c0d0343c07210780d40c0b07004102c00c088802c207210702100b40065505050064904540180c000d50402106114104880d105c83c0542c912a84c000e00449882e507000e02c409070b103015002e030000f84580c4d080c04c00744025031100000740e07401c0c4c48400c070350440d0412091200500d000746031507010f5072500c00c00d0b810345043c43c0142c000f4010341d0036508040c400491071840aa00742e1041e50460903041c402640000c443e00100d5000400300048110350074a01405080040e405400a84404844070307a144400142c2c0600ca44103100f00300308220145091 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 528851978 1250 528850728 528850741
    0xf030207050618010305090c10020c12070302010f0518180a050901090c12060908030a06030c060f020d08040203010b28060207030503040605072f04050f100315020408030304060b0414 80
    0xb0800e15403064141606e03200410600c00050041140d180c20140c48081d1385040014029a26012004640d000e944040301100c0780c03c0c1c000c03400078280ea030180c40c1d0b444800e84c40f4038101c03820390000c881905261001c10047d002969035040480d42c0e400d5503c1d85c05c213a801c1071142c440031594041e2801c490350303140042d1400080c00c54180203040f1603a08984001e100d505040c000f014209640e070040100000104002001d02294070141c1664080e0500a045544800341038030b00760059140d21000d80d01030542c01c0d082511030362850398001e20180001c40c0404528011600400d10498845094030401210f1003d545000b03c0701c6000301881e1004000f0140785440b215141e11072806100f040210002d60b540a00c05401d040000c00380c1c0e018000800f16a01600c0f003480640c86811561182d424032010841c81c04030341e03500c1ca004881d042e00d04030f1482e21f150740380b03000c2003008951101d01030780a0100141410050000d10b2040d8026900424a280808100700840e0840c0301e0611545000a050100 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 528853228 1250 528851978 528852007
    0x819030e090402101110050109050f09240a0f020c070513110d111314030d0e0f0f01020709060306020d27030e01230705060604020a020307020d021504030f0302070506 73
    0x11910b506040914000d1540380a04e8280350084001101c05c1d802c10000154a52700c3e503100c035215404441c1d441290740ca520a6454548503180e01c8101e0b4580185c035212090a081d81e40550040c1804200195484a84464006a802c42141001c20380c004007401c20103804e0003031071100000c0c400304080103182e4007002a45807601603001c034200c00d00da880d1203160f00041118200c131301c1d007031a01c0304d800780700e035075400790f11040c2c9103603144c0c5501a01941001141103030046041c0c4c406036000030408440550f50030180f00070940c0e0000120f04503c108100040c034003040e80f082601841c0038903000341c0c2c0c40c20092540c3c1c0075244c0c080d070143c103085151080d20080010b000034076a90719900d80703004d44203140c1040c0101d880480d8002ca044000480400f403a00440c0c80c04020aa114031550030703a12a03a480504000890107851000d00c0960400c0104000500e04109011704032807000b015280d000d9800c102c1d40c001a08150011039144180050a60a244d01001090001c00c800c55400349400140442c040 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 528854478 1250 528853228 528853249
    0xf0c0f090608100b070b150405101206060e15190b0a05030901230915090705060d020c030d0608070807060909050601031829040f03050f040819030e090402 68
    0x1070402041070046682c001c007200040e00141329602241e030315410a400e004070b00c00002d80f584600800484003444843c1030a0003018410f6890b880140700c0c1c24904006c004141180b00c2e01101c01c1c035a2601d010425110004e021800380d10f043c414000c1d011401c2c01400b205a446131071100304400f85010401840300c8200031220401c0300c0d4500240c4030f07103034400030501614040124500c038010310411007245589001855100d0444076084404600c0140c1c010002c501c0c090b194442c0a40180c00107100b6800c01e03500030903a040d13101074010710345200e00d070340e0504540011443c025801d0f00c800d0104820b410400a400c050400400606441c1d4648500034181056a00c40d80f1f1503a500c0c0c00000d80d650780254050121419040618100340e0382510b0220101408200c28003240e040c1022444d14032042d001103240b0660348002608011003558905039195040560303800c0c50148100008030303500c80d05105840440c040400c0003003892010380360280054100550712030140500a00304405030780d031042c111 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 528855728 1250 528854478 528854489
    0x60109050301050f2d07020604231002030705070c15020f300702180406050a0212040f0221010219110a0201030b1c0f1a092a040f0f0c0f09 61
    0x800801d0061060170700403400c0d5054041001c0c0405c580c290b004a0700341d01c100d22a00c10102490703903403040c0104d4105040000641c0340e21404100381e00c5140c503401185c200046003001c50508000f603440c00400e17046070300f018813111940c10b441000ea58040001c00a9042600c3c041c014984054034080c04000515181f80e5048210a60381403054500c903045030301d856000741910240805001d0b907507000d01d00550f402c881d118544000140305201c00d00c02e40d48080341403d8004116120380d218600500044801030341e20440760300c0260842981c1c040c0030032501c103e0340d00140c1c40c4e0040110b454142110021105c0502500d012841006400480c5042c2d031745d682400d0000d445440c202c08110003612034089550300300040310200e014400d1031411490654810a0b40d40b140d144103a256698103041542c843c0102e5010480b1511807883c81c1c03c039800e014003050070541e0b0000100d000038096420420f101c0540b1355a40002c100b060031a40104400c42c52141000740c00441d00410040400040d403085 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 528856978 1250 528855728 528855751
    0xc0b070c0317090604021e010c030e04060b040e1008070501140c280c1e050607080c060403081f030c0605090a18020c160509062704050105060109050301050f 69
    0x44400c050240c40085800b241c2400d40b00d41d01d1804503445580d400003910241e00c01c05099100c1b10042d004020036901403601a074642d20311100995007a5110301c42402029881500d0705c00c04a00e81c090b07900500001d00301800804a14100f1254503241500c8a401881a07074100900510490b42c0107003180500441d80b0f200c079542c42d2108620513040410303100890300301c800d40291562404400d40c2540c01001d00405107220380c0d0f6547d000d00c0c3d00260134095840803c1034619401c000f140323041c4001d800228010048589488e421603d01814540111022030200e00c444081c46041b00c2e401c0c4050740c91042507503940c0801811516441c4400480344154070070002c00040114103030311a0f801040c000c0014a02c2e1140d00c01d0600d100c1e03000394012a02c0001c10313110b40c0d02800118640e84c504201101d002408100c0320b5100c50060100143c0d10282d0710018925502c004240441c1c2c03e0521482540140700005250400100040180500350f200a01c00c2e07040001f44070100880c03a1034a9000500e1001 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 528858228 1250 528856978 528856997
    0x80f0604200d050304150305010503061302030a0b07090905060f18060a03050321060910120305040b13051507030206131103030406030b040501092703030b0301180b06010c0b07 77
    0xa00100710202051400d4000c8080c54030401003090000140050302d030144806e600ca001c1400d400c030102c990034490309500d170f4050070104082c4124180c001c1c008078000340c181d4442100701e440c3c001d0b2103803060324120006940c81c0410800705081e4401e994200004840c5582e4400c841c0001658005480041c2c8014900140c042180d41c2e481c0382087e00116484021340e511030105010310030a603803103464900d00d0710017004001002480c1580310580316070903588142a085042010004083c040e0000480c1440401c100c00308500410f200902402c0810580c0c04c00c85c9401c041c07e00080703098411400e803000700c0900425002a8002c0380865004a40d40c860800d000c80d00e09010400000c14085035405000006010464552540144190100548040c45580d90b81e009000480c1d24401b60082069001c11070000015400401041c0d89402445d021a16480d81c0c000a42110840201002c6140b520a05c0c8420805101c455070307400002424584041d2601d070716102842900202510300300719034100c = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 528859478 1250 528858228 528858263
    0x10f05160815031e060a050601080a02030c09060c0c010f020d0e22020c030316080105130b04090602360d0212012a081807090c030f09060213080f0604 66
    0x310040071002e00070101c034840c04405042d0500c100c107809240c4c400c0c2c0692000102400001d0056034011030040c2e403001d08035071358003101d0ba0003908090054200300c2c030100842000c507620380002c2c080190003040980901c0c0d0748900094100700c08890002d080d50400114504d0761b03a00140d030a0fa22040c2a100041c4840d02003410f00c00958034990703900740c04e0303201140d001001c080000141d8032483c1400e01650055411900c1921105024030500d54800b20300c114060142c41140c01c04580f1038809000800c0c880304640e2924188d0f08252864608002d212144520080054030407a821400e64205480c107800b403a40482c00b40c1d182d144010b0f0181c0c28082044d404200250b02c500500a4a0240d8000b5024042824207204071440c0d007060001c0e203560f001c600c0c3c0c100d240c1d400030392009250004000380f07403800b4940c1002e411425080018184e80d819036001c0761003030780502c0078560303c0f468005a90f100440d5803d412030810307412943d15940402d284480c0070400080c03541d0003070340010342d0380001c03003142 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 528860728 1250 528859478 528859501
    0xb0d0e010606052d13030506071707030b030a1203020d0b01050f04030206160f080306010909021305240301031b12050309150c01090f021005070c05060c0703050d020f010f051608 78
    0x100f10005201c070740051005180d00717101c02c42c541034a10807803d80340180c907220f03800c42d95103009443c0300b4101013424010403c958040e9110750399869003d401e03241e101e5615120b09010240302c902d002d01007a00002c211014081c58410816105400d0170000c0c00d11000015140c424000e5000007409028001003c00800c459107000d0701081354000c01c1c002c42c0c1c108510740b054040d001910303a03034081411520081030140c494000d603600c0c420a9222a08114505002c105200b0407042c2c800c0006071010902c1c1c10900400340003507004c2d43c0940d040d0360291403100e8240207080c06a9026006071a078105550000640110071102142403c0b1620b030075450146148030b902c0d1081c7d00c000d60083d8038241c603020402070307000500120f59000320760008640c071882c2800d03078080c03250309401404000d08520500051400380098281691101c08441e48a80c91380d559a280c801c91034440409640320340407032050480f0034001d0301210303540304200b40b04a05001d0070340724004a40e014450144003000c0000f40d4202841c = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 528861978 1250 528860728 528860797
    0x11100212030c0406080c0319050a18031707020d0c03030c2a050105010509060d0803040809040504030801080c0d031e17011412150412030b0a0b0d0e01060605 69
    0x80080e80d5880c10140c001c545641c0c000d02c00c0c880421481c0e8000f1386558582d4007a02d2007400b421030104012244c1d5001b6074000d10004142840842d81c40c00080e01c10802031203982c0da654420f4681ca100c240d142002200304030402080201103500118144020507400320404080c26031504012807940f91900c4159034040383c5081d0800c0d035240e4441e02d03809562005117009480c6015038020809a601c5005114420008a590a0300545115030100006900400955006000d40c0d01e0354101103110340080d00382c68040d01c064000410b820300501585c101400101c4a2200848581c50800d007641e8000d480420281e00003900f19103111503d048050040c01d4030b500300c40490808803125038580d0001900071040b8a640c0e40a0005d2041c1030b0b84900c03000803050f80442d0719810110f40e41d0b40315500c000a0031b51500c010404c0540328040400651243c28400014011089103661a410184e2200741156549a003210881c0c4c1408002c100c40c0750018101d0781c540d10800344030011249444012801c0304d01 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 528863228 1250 528861978 528862003
    0x30201020c0616120305010608251d0607050f1009020a0911070c06020d0e010203040b030a0908120f160c2a08060115030b09090d23120411040603111002 67
    0x1d65810603940217034581d0140381a140b098603881c0407500d98003818200c0d407046519501d0b202200e4180801c50b5400707107090028503840c6400e4088040e0259000c544030b50071404040314282d10041c030b002c517070000a009810202100340d408001c500700680001c1d81d5804a03108040306140c1d940d9045200401c004100d0348826040910000c40b10f503200002991110080541c2000a8041e41c0c1004d0f02d40c8048102e8003122049110282507803655200c090003405200d80407602d4440c104082c03003002030000c554521944081720b80c04564907010034000d9010205075031903001c02c000e44403503200041030701c00d280e03401d1000c0722011011030b00c0c0c0070101c840390003854101145c10b110301d200004441285403503288099045a0382401110901ea007400040d0409031592811a048054036500704d510a2114091446005200109407040030700c00701d09031381c04401080c07102c000010810090001440c500c0b94042d0003a24100145442c544400300104140013190b0710030b49450300340c2c1c2141842005960b140d0301 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 528864478 1250 528863228 528863243
    0x1407150c0e09190b0a03080f03070315080609190b040f051006030606080d02070f06031e020301080102090a05060f0d112203030f020106050f01030b01270305010b0a030201020c0616 79
    0x8021040c0481a081c09a203500054140703104c6208509000038a01c2c200ca0b444190141005041d56807144642c100038014020540d0790f20348001100c200490460003405800701400403800d241120a080100420004441c41200102100014224030078a544181c00c2810011050101d00d0b00c44c2c03c3c4410640411407090800102009000b0194050021140c0400454008552208041c0d17100c10f03441c850f51a0402e0018020040e41e4000d030040742d80600400140c001c020054145030701280c000383c0100805a5002c0350f0541d1070b0820494070400f0f0182119441c0c144001504030b003240b8070401100f461001c0c0c50f00b11000c101410300e000c4c2c0340344c1503000b0312060161b841907002c040780c8003141c8801c1e400960160315a141060040c42514151803000d84145145c08a180041d0b0141c078403c52500c0c10001161010310200311140d0b0101420041ca01100103070a00d07609043e400d49580c9203250703201d811425400c00050780c0000300500d07034007000d076012038440c81c0c2c0c0e80c141000d03042142c50142109 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 528865728 1250 528864478 528864481
    0x21040f0902090f040b040b310e07032301110409230c0f07060911090a062102030f0d030b030c01020f0304090b0d080f0a080f16051812010605011407150c0e09 69
    0x80d0b4203041407070002c8141c10688c000160203c4000180c9040001e0340d28940c02031282403010071400b418444242d107903d17a02c120321420941000307003140c000c440f00002100d404a402c2c0080100b50094003010640b203103414100d212588000e005040340a46a4a0411030004000c41452480d106560007160011000c0010b0074450424098441100c2107d51040202c1c9000410071340c2c40c1d2081400b6581c0314030103600760078514440c40f20401d000e04001d90307241c41116026031001d41f0400401040c1d001c00c0c0e401103400140d41c01894070708494036a109040d5041184c241f00c40039400000e54040b504c8000b008a42114400046181c0e2030038014082c0140d500010300342c484103078000041201580380d6496400560300d0303c01c0c1c2d4a0281003130f81c8071030b00b01c0100c0820300c407a54451000346c2240302c80d6000f94100b4003003241c0081c03e85c8808e910a8134032139450324000c00c010341c2c020444040c441c2e11041020b00c0c2c40c106130307284507501c60003072607190721907540f6040155060f101d42c110082e98200500707400801e = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 528866978 1250 528865728 528865759
    0x5012c041e2003090a02040b010507080d141305062403150f13050604060515040c0c05010c0807020d0f0c02091e01142121040f0902090f040b040b 64
    0x251541818928692101c1914295104010003c90740300c0c107a240301600c0700382001d6003000040c00c41040040e0411500348042c5012940c0c0310000e0400c480e241d040040c54840158480a5240d001002101d51108040906010440100c0c41c240e2103c88000d103454203209100000f211034049098440e0184107100129620380c09125500b4044d500f042006801c0c4d6841c0c1c014041844042000113010350401d0b008030340060083c0d00895049001007421101c079641c89004034084410309204840000c0344010202c05116081c07040c07031495105841d00b01c0152810400180d550482c580d840380c2000001604401502e118940c00e54805278020041e00b0141818188032404c0440c801180c080c04d907000e00000b50701052a4481c40401d00050030944506040c1c01c40d03500c102043c6408501240508007100c00c407031504841000c3e15410300810280c0369030900b005907000c0c41c1355400c01d0740190300c10401e4220b903540c0c400e02c005500008803408034248240d1004200944002030740c003078100104403500c030b14 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 528868228 1250 528866978 528866981
    0xc030c16170703050c0c06040f060c21020309131416020a08040905041209060806060f0403170703020d14070b0925080f0106050904020f0109150c03080105012c041e 72
    0xc03c0203091088840d2070a00b603081040034480e072711179840b000b070105008018881c011005040c15034011200e2500800d076420104406100411710310005030400107600040d1302d050f030025200215400010051072600c000c41d0005410054484101c0c043d0000501101da0320801c001f80420b43d00400940d21a907a404c03540c400b501c0d0030340d0125440c04c41c80d115151040c0c402c00401c005c8403615540d560f4180c030b8000034080c95510000c904003c00c0020800880410038801f808092400032405560f9a8285401c00070f00f0300000120307603010401e001107858403094210042d20806078000310f4442d0300e615050419440c207081c1201e0000076030850040c5071715031020020020200c0c1c04a01c15245a0b08007003540c24200e61880c0200b44e403041c50300010a01504041d09600c0c4514818108004929203488002d40c400314103080240c0040c0b800c0030071a0070154040318443c01040c082c00c040d102c088245030724050b40c24408428200301c00c030104101030715980d0b5401c03102061400b12601d2810201c040800ca0 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 528869478 1250 528868228 528868237
    0x180106140a06030e070b090303040801060b0d0e030c030a030c0905030d0c02010908030c0307110103140109290303030a0504050705060d050a0c020d020d050901090518040b0c030c1617070305 83
    0x1d10803421060005041c50007030143c4002ca8014002a009950410002030b406d80c100341040c68042c4070500003c11350110902c6240003400c02185820703107a00e80c0203c20820740d0203004d030350072164005100600903800300109a58403000b140c00d003c1441906108200c5941c101540101e9241c404d2a028a18503a00f080c110001c06000381d0f90b00e880f2a481e80c0101c3d0f0390f4032642912401c2d99004004505c045900c800c0402550707803051402158198454035800031610342070f00641c03121a07480350080000e91100310500d00703042181ca502d01e8184081d00c0001c0d100e00004201040094407100081c0070080b040c40303000044c1c04000d2030346032100c0c0400d03440b20042c98110b0b810840c0e9031900081c104801d00001d003403100340d100369004049500d0b02c0007040701c01c2c1e0820702c0c1c4103051021f02040415140e58806035400c1541040c01c4480e2507140500300380e48000e0010b02000007840c070810601252003003d50494048602807070855034104803528182c003031000d502442840d02c0e08089108800c0590000062 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 528870728 1250 528869478 528869519
    0x70312050d1404120807091215020d060e01150e13050a0603120f02010f0605064302091005011215080a0803041a071e050d0c210e0a060203180106 64
    0x2c0940c0e03481b0141540c002c2e91500070348072510001d11310680000c1101583c0725945c002c446003d03041c242d004802206695a680204285c50f80d2280184001c264041038416010102c0c9001a484480d00c0f021440401c0c1120751500c900f0784a400248204a030303504000015071744502240350031240603c008006010140025005508256545040b0401409003900759134000f0f107043d151515a201640c0140d02c0d980502e450f50100304e20405800240100c0c1c0640000380c0020001006440c3c410410b5030400108540305ea040da19905108a9a1003070100e8000b403c0c4e0500000d8291040c201016885100d9000102910804203e0820403a01074051405244280c440030082d0300c001c0801e0000b0f00701101c04200049012800b0000501c0c0300c45400c510790100d003421840c1000c0e600300303001034488030540d02e8003280c110541c0340e086142025455542c0f10080c1010010944200d01140d00c03403d0462000e4801034010020960070b4440524030611902188000c002c403503501c0b01e03282d2a242c8260b00b007 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 528871978 1250 528870728 528870737
    0x905040e030720120105040302030d051f03060c110601180605030304120201032a020a050607020109080702040c020c130903120203070e0d05030904020409051008070312050d140412 79
    0x610a280000206485900d40d204503000409201860003e2540310995103280d4480110800481222400c1c400d590049020758007450303885c2c428201c40400d0b071344094601001c54441c0d0180810203541c2c1102407064941c896004500004422811074078070004c0025060b05014030400005c4115282041005018504d6414003650740e40b1070030103440740214807940ba00928603510840043d8480e60100380400000810f003503016840c620b00340d44107800c284826025a20816006003884010440ca80e0301500c4c80c4002d000001e0650344148190041601c0280515111803401c184180240308000f40d42c94080e210810113800c00417a0405004c5810080d000301d5040c0842c424050540c0c02241d200e5605501c86440c00d40070303101404000101d070041500e8500040c000c481c420360700c0b400204000d01180c00302050b03504108103080c87d1900680d20045242d80141310810008890100d241c1001500303090140d142c0c84090319040c007625824284603c80d0721140c00b0041000315240e94800c50b880d840d50b4 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 528873228 1250 528871978 528871991
    0x4020a050f090c0c120304060b01110d020a030c060204083301050a030b2806030308060307031208090307020a03031d0f060d0b010509030d020105091213090b0d0b07090504 75
    0x1c1c00a2103041c400c0442d0080006000255240a180004c042c00d1082008503600d07111070880100907900f003501c04807803a60700e81a829966607480a01c0e101c03d100600041c0c1404030183c40c000c1d503900c106036801400e1040d09000c13201400340c1c6031705840c0203040c445c0c1540d48005402c40c14034075140140b84a4403100311002000380540d0000210507059840103448800070f58195220b281d981503004245640306800c420900444200c1c08031755020050300340340c010403aa82149805400c1160042c00342d406540b1000b401c00101e488100002c02003d1142000381c000d441e40c402107411f510495202a4015988000c00410160302047c0e44c00c210b15040760306900f8004072001c10103051405900554050b0060017078148034032a5612081400070141003c5241c19412008a1700b8242c40600200c0944d54410401000103030511003000780904051446180042c03400942000702c90074080c2083d074691ba2100c1c3c80c4182c50f0780841c0c140703854000d42250414544903800070408100d1380202c6009500308031 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 528874478 1250 528873228 528873239
    0xf0906090b030606090303072310050c0f0c07030503130311010e010e040b2106070306120519020a05130c0e030f0c1e060403121706011e0504091404020a 67
    0x10036000740c0703451060040c41e54840b4820091581c110584060381400308014400014080c0d010ba60404001003104000201303802840d07070f0a2003d5520a0002c05003000704100300310b040c0d2030480380a91521500103440d0f6031425011441d00003140c20082c00e40c07000144201c40a200e40740100112072007a41c5180e050b040600045a85403d5441100e002c43d0401000d0601881d20703405c1403080300c4018103050355000d07040f80e0030800204c520a1245e8960007140601061640c1400b802010b0078103000c4201030110103076140c5503203025a040c21080700b09c1c180c1d052421990f4151150000300030090884040c2c0403031982140091a180b1401000f1501c40d4407192800d0034007045039900350400c3da020345604811202030181c80654014001e020005488862046036954000782010b540640840c003440d100e0308201500c0003100d0220311402034081010401c40360307482541c1409001c0b0340c51104249da149440141c03030500450b00a0076510342404010914030b0f00301d81c1c155110b18021180030301c1103075840 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 528875728 1250 528874478 528874487
    0x109141c11031b0f100e012403111f050a022803030209060d0905030a08060405100b0702040f020a0315170d08100806040c05040b0a140d050a120f0906 66
    0x1408503116030801c0c00462521081c1414110b00d444420003078070800e942c448000c0f402d1200317a50b4200c010654800d400c01c9540310901c42d513034450b00506821908080000c00300c58852002d0320005140124245405501c0d803100100c0c0c0c2c40d0a1b884140260441680b07480240046d00002144070043c45410750a58460181c1ca541906281e500c101c0b001c0380c0c58650700c007240650301080180341c206030100702201401650348140d000b210300400103145c8415903241e006141d868003900303043c810b60401003030000303042c10180107004880d80c4c84140c5507522910300c0801e015011000643c00c81e03502c04100f42c852181c15402141d03107295203a00b0801380c41d0302e601066107661324150a20301142d00c24040340c50020300400c0c5194000c0c2d51880c10320b141d80c0e03079018a2854400e0440d4120b41c0440b00e84810032807810b06000d054004841214403642c10307800e10b4054000e004e007074100e151241b071512100400303100c000c2c02a02030140d040001c0e4089880c501310040c05400d007a480c0d50300029040440040c489104 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 528876978 1250 528875728 528875747
    0x316080c03060d0620040608090a02030312070314101a120109110c0d121a0f041a030f03070203160f05150f0c010e01060503070e13050109141c 63
    0x1450402411511448107110302c0900c03c0d003084501d80d540b90400855541d240120200780d0700c05821044d0b4590500034010000c80c1c0c00707041011079500a100040040e0390100035101001d0407809910310950391803408030060710220080d8001d4000000c00c0c00700c00b4144508440507611184002ea440a018405044203413060300e228040500e4032100601c80e00600750820040901041c541600301a02c004000b4244127000d48000c01091909240e88210040c600070b5086012901c21100f0740041c0d101c0201d0402a40925090b11441d03a851000c0b6a42010006410706800e001e42164011800c405540d40e8a60113090b080e4402d02c9817200c1000e0300e01a0b0914141a0342800c4a034070f54141c58001440901c5e00d090090020741001403040b9450240300c1c03405000c200b10790388004642c40104c10640f41c00c42c1c405402c200c0c0603400c0a2024000c55080c201120340201090803c520b171101d0508203503006202e814002030212280e1840b0b000615000290b195160031880380555124411000c103448400c3c0 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 528878228 1250 528876978 528876991
    0xc010f080a0b04090b180c010e030a111f05070203060615040b0c010902060705011b181a040b07122a140a0b010602100510080601150e031002031608 65
    0x8940c0c00076054695540001e071980c00e0140000c03d00410568650001d507008503912a4020030650850b200c0c118200705128400c0e80030b007003064201002d0008aa15801e60380c01c003802c10038240d005d25a182d16541070910803034002510591006400340030080413580040740980c841e01c01c950101e592850200502c1074800e64145090381b406140403d141c00315041000b8100040d5078500b44e03000540c440300b000b403124a2003603000141008520a0000a0300301f6040c080c0c1c20003a01541482140303e0b0f06400d0f1003902c0d050102c070300081d1004400001244501d8024a2940c0000b141000c2004184400c10424142a40380c2c1904030000d00403484040210071040c1c1400030341c407035040c0e000c03421424084400c007220009035a42c0000c6911540c00302003007a0f101c000140d1001003c01070041551040030f80151180442001c201d01c1c4c0b1031150b6944c5c0d410302410891125903002c0000c4070380660014009110b028083d58148882215000d0003900211811440e207000c0502c080340043c0302d075922610500 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 528879478 1250 528878228 528878237
    0xe1603060f0f1703040b0414041a210c06040b120703020a05270a06050414030f071a211503010507080403030b190902071a091c0e04051501020c010f 65
    0x1864881c030f0050782d80c0d521900300d4071400100300c089008100c2d50020000b034080710714a0807105152a06010484518040050320780d07042d9001c211907a681c1414041e81700c903002083c1c002c11030100d0882401c04103042c04050f884903000600007941a042030141854107450072f510191955041c0d819020780c0f04130b00001000850400c034180c4c100c0c110031824080e920498036920900a4000003040d03529420350080d001191022804000545281000000840040c0d002d001c2c1504000b400d80d50300d081600860030003042440c003100c0f648c0540019280c02e004441d00e014049113101c00500e11180040d80c042c89007102e685990300c07150405010300c90190440303603104c460603941e503102100107006a01030298012803021900c0500c0303148050b02c40c0a482d1100c801a0b40703940714948007515000d10960304400ac02c264007048041030f0b022030000078210f8a808408408072055001716039008084800f10303409460f00b41401a4080c01a003a0311320300c0c80a800311011010f00c0401550120f01c0c2c40c2d110300004 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 528880728 1250 528879478 528879509
    0x18090a050d02150f0c04081b030d14121302090106080912030c0d09230105010e09121605011d0a15020408070320100c060f1103060105130e1603060f 65
    0x190303000030307040d0f905c16000c055841c1800c0c3c6464002e4117007462125091383d909818019070407203190a00c5894900400307814049000343c4014044041e60203030100a521080200340000c56454024504c46070707950303008068034a40c0d80c4505000d000c081d001c3e10300b85440d21408140325070103401241164010000980100e0a04c1405003001c00a004440000ca4244248141c98200318420316400c0c14000070040c0041020340c109040da0509a400030b003d40341c00c0c1d00905088071441d09150440c1c005007000c0b5600b01d0b003140396040050240154004185450303c6851414803190008540191003074803402c1c001181505c9110171100368020750007031000756001790b1420000101122440e000180d00303100703540c61400103000082d060302d4a030b0401c000800c14144080c1d041003540d03c660b03000d000288a007004070810010300321610b40401082181440b01c0011460890450070600400400c003907078002041e440e00010815070919142041d001007800c4c45004070350b610120140314140c40c001d80104219 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 528881978 1250 528880728 528880741
    0x11a1305040c0909061d090309060f280f0813170c010e01050f06010207090507120915050406020c300f0d020406030b011106070c02060918090a050d0215 67
    0x20200100d002c0d0030f1041c0b2200026160941e0b016a10081174029a880e001198a00e544015440d000f80000075542082100d42c0700f0b9519402610203040f1000c6c1040c0d00c442c0c0c0d442c2d000040f80c1940d600440c0d060101603441c55410350000402c003110030345658400b6985c0f03c04c145525860024031005041c50f555020201c540b410041c05040303c20380035000490f4503140740398030a007107560540c0d4204225468004102c95947c04012420040c05410820806407510520003009078110000c0c40200644503107081041c05800c06604aa00c200c055081003542002d2038204000d40c001c0309007051030b0040f030240000001d099080c1c081c550360800c60f02c1c58004094201202c45a0000040020301c840901c800f40208056101920203040320351030010300218031100240946003282d902649503401841004141540000503001043d41035408503102e012100005541901302480304610304503907010414070940c005205034400f400b6409070b600524868000701d03200c154906824840c80350f04404101c4 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 528883228 1250 528881978 528881981
    0x1d040201030e01020d0207050a0c06021513030302040b1c0f02070c0302060a0921061515030905030903030a050d0c0503010608071209120309060b1c031101090602070803011a130504 79
    0x25030b60502e03000516041c584410413040340c2000c0801c0e2455845500c4002c1049040800c840250540b400104840b000390b03001340984000c020207081e05207240c841c1100806000760103070b0700540b00c0c00c46625118540c120503240c0306411000103180c0e250910031380c86e00704411032085132080340e08291144281070840d024422281d000d01c3c442003c019004600048501910880c0d40c900a0014920901e00f402410300f030040d5040c4040f20008940c403058100b1400c207442a9440140b0f08a080c08501c186881c2001c07030444c080e400700103401d03001c00201d400103e980300c0010b29030440c0d1004100310b902001071085950780024000d20703021420140c040b903810707070041021100b54525000c010954150958038001c0702c40807000381e140483d81f0f40c40858100a8603015122890f481039034840035040700c041c0c50307100c0c210301044044d080c0103500d584400030020a40100d4183ca0b0001c00c2550f5815561401c182d4a0740300340300307580707a1070a180c0603141d694100ea0304981c0005415008220840d00388002c010 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 528884478 1250 528883228 528883241
    0x218030d0f09060e120118120810032603100f090606170405070302042904050c1b0309031915020301060806151e0307020c090f0a0b01020a060e030307091d04020103 72
    0x10360082c924026501c50071824002c7d8005052403004030100c128940c038105983e00c42c1c0040505c00d004003030301000101d0040ea040f5408894210094010400b42000d4071340c9810380c3c460000035410710010400021000b01d0001c282203035030a040381030450380d070342d1704860888400e40100c0e400a1246c040300400c141030404450303002405002517620181d502d500040444030316801e0b4014066900c0c52400055081640b180040d2005071030901091406062160b424840c0541d070000184030301e126451440020015100303540e601800729030f0380d0f2050018014101c207101c001103545a120100000c001070060007924100c44c681e40360703000c6035100c8008209003070024000d41c0300c8012040c030507808bc0301d610507800c1368400c0004250a60701c2c180210006d041190000714603000b40284814002c801071048400d079400190f02000103000980040104d0804440f0f6801510103800c150191021800c0440110302480c82038640862160b520014220040c96458441042004603400034004d54001d4000e81d = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 528885728 1250 528884478 528884507
    0x3010b0405060f041d0601030b06030702150c0d060f090516050d181e0203010e07030201020307110a0f08031804090809090a06050618100809061302030a060218030d0f0906 75
    0x150b05160301c58211509146903403035000e202c5c842c490309004c82960503100d0030810640030b480312031451402480203552540001d20600c010032100000401030750100d4241c3e06d02040c411824802107544407c3e808107000300c1d008000c1c40a1402021400a0f074000c0d440701c01116298071035904010700602007000400f852039448105400300404440000e02c0091590308103041c1c2e0903548444a15401071500319001500900d9050b0310400d030a00150707070000181c540c80d80d801410104140300342c6020485840c0e103640000a1035030300d1140801c0c100c0012001c3d0046a5401015100707180e140d00c10403098a800110180001e08100081c0c0c040b030800c500d07003035070041c9686030100d103069880703001c01c2580d0f05c03104060320650305074048076903c0d217000f02e8550b0254546180182c041e04282c07401c143c940001401403040012030039007510840d00c2c02d00c60706440c9904540c00b107403200340303120317008000404104107280f0038000c0c20116010f060140390361130b041d40303299600c03007404c03a007031010035148643d84207407a = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 528886978 1250 528885728 528885757
    0xc01050f0115080c1c02072609120c0603070f0f02010501060c120201060b0a02070806060303070b180a0501110309010c092607080f0102191b08070f0f050c0109050603010b040506 78
    0x5c0e4a811803112490a140340d059400181e0321111030a040e56402900910f90450800420744483c641c466202544c1e0403050854094804198ad51000c5107000700d800c055942150012080009841e000303881d80c22009002d0b200c20300d0416400c40b08130300321030b002d000d03840124150025810104803243c28841c1440e1807400005256a00c400440300a600152251001684040300600c404442413041580101041d0015401d0908607560413010001c000d01e8a601004401440e64080c2c20801c404003015070890000c00c03141c0c0c10300c810302d00a035104031040f4040f5801e154552000c1031040420720221004881011b401554550508600c01c0c0300030708402041c071400340d012500880c00d02014042800d40000180d0b41c0403041580c038101d4070035440c1d0304140000c1070103072503000100c803040a0186070f000d50000c3c0e4070540c61401c0390110b5407880018000b08252034079042044400201c0a40220090700c561521684e2182040035500c403d0040c0c0381840402d010800c507074200107001d8000003000620 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 528888228 1250 528886978 528886987
    0x50309030c0f03032d041e0c1806080a03082a04080106140312040b13030b100f0801090503070618080c010606121404150f110c01050f0115080c 63
    0x402481d140384040ba035400e03904004240100c0550014024a000c500b50079807a42d0110000c0f5400d0100000610141c498042090385440e090910042038884560100c902d2040684902e202200000541d1980c03500e140703801c170081404280051543c10183d030540d1010200e0743c40d410f40f44007160500424810109102e824035001c5040f850241014003401c000000c0d4041c40d000700301207c1c0313590b10181802a04502242103445a03624102c406413080c05010558500c102401c0c0607170050542e0024060b40401e0081c001140310641c801c60440d00520078042040c0e0301e0341c0304039080350002030300100254020040f0302d00086080e000f032441c2d0711035801000160f24450300d03106410340c04541c040c456070355142814842e0729048400156003136800c0004121015035010030450000015002400c040700b60641802006c40a421408041400210a000d600911300341112550044100a80c0d01e508120006c0c135080300148643d030403514245045407911418031819120040c0151404d03401420822 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 528889478 1250 528888228 528888247
    0x1230c15010518041101030e120d0519090308011a04090204080309030f030f070f020a050409050d0f141c0b100908070b0702100f02012405030c0114030705210f061509010f05030903 79
    0x80103801420102c20020840c0d00c1c00840cc000600c481c080399031122450070300084042a0b0141038a819200745103880c00342c210400d40507403458011680803910440c00001c001c10041404000707040360300030a804440345000060609034481c0181d690b840e440070400c2c086400030a43d09804981e90b02c1c009800c5000b07140d00c03100840c5c140c0b1806101078131507921000521410a500003e2000c2e2461185000200240c00d0605009240701d51490f00b540303d007a80405003074103d25980f20410707400740140850240044038101034100c04040c41482e6a5004086000503d03d0640341183c0543c2c3c0c0c01040300182c1748155800740c0d04025070802e031004565844500000d20110030304407202c1d0848004140c544d01c0d00d04410546050542c40d0307201c0c100314020120154207088031058a4000c200e900700386488038103800502e0155610f00702400c10f1188902c041c08036100011580d00e000e010103640746940755100c02e07142c407030318820300740d4550019144003104007009104d580503540041c0a001500e1405c00c061 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 528890728 1250 528889478 528889513
    0x212010632091017070501120515300a020a03030302071a0108010f0f2c24070e0d120507060e0a1a07020106030201230c15010518041101030e 62
    0x48032000c030348400204091010741c0c111342c3e1010300c1c9074a500c000c24a03e424000000c2000d40207600401c00c503511000442c4513804581003218081001030050a44135091442003e081d2401564504000305940d03e01c031906c0c200450b09424454000d0a60407103585550340440080d07022550030b0f610121103207a02c1a038041503c0c4032034000c04403e000410707402c0500c4a41c0040741c80d080c050081407031411129201c26031700c102c907840c41c0c030084c5440035500118421083e802e00b903c40e50030080d184501c82030120003040c684d28007801b0310070f0360740c4070710001000b03c092121241d5100303400b81c40d9442d220805e03161903100f070008207000791240c1000304007019a040708500d0555010310031607200b400060020b009403103180c43c00c0d611800510080c4070742455500040d00380c540000031500b036401030700c42d049003100c0448100c805410f042c108070395031002c84a4003d85da41c1c1e028001d80744903243c0306035035100508080d041c190156801c94520740d03c5078400070040d0014003240b80d81d045240038192070f485003007003035 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 528891978 1250 528890728 528890731
    0x3020607080f0d0915020313020d0212120301090501080c090c03100f0303080f0c0306220b0916020d0f0e01030c0201060306020301060c140a17030a27021201063209 72
    0xb210206006103d807070642172010001040c0c810f064414070400121282e0344081582c0140c0554032000c2c141030500204159140c5480c2440481c4542d0b07000c0625031107100001c50494100328000c00450740c86e0300045840e103142121705075005d070052002c511101c040800071601b0080c0c0d07030048038005a46100b000340444e96580240e0115040c1c0042040300700c11039496603400f0615284140c40d52030204c000800009680e9240580c4003040441c0a000b803440743c0c00b4202c0400010402c01081c41c01c100303085081410380c0214001805282e07542da00c901d009959856943c483c644680c0c1da0812a000110000d00c1c4904803802159220407000002c11864030066000e40956610241110300c81c2c10070429421603ca01403220350722002000c00800c3c1c1605020660494030550b10750740b034032504c10310406807003a034060701440b21101d505078103a41c1d0307103060a04000348265500031148002145a07400c031462881854040c842040c0c021700d010051113540c00e841030402000079280c841c44000b040030402c0 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 528893228 1250 528891978 528891997
    0x151e070809060906090d0302070201140c060103050f06060901050f0105220626060d0201051b01050a1805070e0a14150103060b0f040506030a02070807030e011d0a03020607080f 77
    0xc2600034404020400d0001c1a0701c100860014440c0d070401c080015542c00c400e60f540d03005c0503030200da200700b16841421100c181c0828154074035156644266590307120542840200c59521070071015004140c00419910700c540c0000307004080e503a203030006110f5030941020003581000f10170440c41080b0785079404a0316110000c41cac4004a064240300024100e80f0f00080c0d03001c254005510114140da85201071a0340c0010140c48000b540c8100d4401a0f40741c0c043d12011a0203031404000720b62542105600c400d12070340c50900244207d454000d01c042890041240242c050303004450705001480030741c202e140e0030a038203c400203580620303940c1c8501142c0702a00e01c01d40c40381c25500075550f5507031715000b11b030041d100c040341e2a031034070b103c000c505211803045210b01400340501200182d00d84c9a01c0e410344030220f410013411640e805032450004c01020700711003840d000c600e12480341d072117000282d0f821208140d00a08035000350342c03c1d9000c10405810510040ba00c0032010040c1c08600303460388018000040 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 528894478 1250 528893228 528893237
    0x30c0a0c06140f0702030903031911030a0c121b0f02031e0105011d0f01060f0c0c290a1b02040902031f0507081009020d0603080f0d05090d02151e07 65
    0x404003e925101040134180c00110b41c424082d280040d0340c0481103407030b000a9000c0d40c0351030083d2000c080d41c02c00b6036440000c0d502d000100e10b0200c940c4e0010140300c4003d224603e03110b00382ca09454180c5002ca402200c0e80c51402100001c4130000d40c1c0d180d00d195038580000d04440900c1d0700c020141800e20038181111505035101c00040105011849a2061448903e04031003030340e00e0046200c0c1c1c401041441000704024060b0103008200340940420148540c00c24881d40c0c41d40e807a85010049214483c0d2404a2107550441c0b20101c1c041c10000d45100f5101651402c91030150071125400c900a18071042e6801a618214003005070b4040007600d0b0008202408158a6580a040801101d0b002000d443c244200c0804001550741000f10302000d59070b0100e401600c2e070180d007803044020308481c0c0006003c7d0200280d0600540d200d40060726100d81041d8051040d03664030a001070701e4a10b485010000340c0d0003422444c01e1140460011540085c003600101d2402c0505140090780c11005c0d44c0e50070209 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 528895728 1250 528894478 528894481
    0xa0c090903081509040b0c090907030b130b030322050301050106020106080609010b090609070329101103070b190507050d1a031203070207270b0114030c0a0c0614 71
    0x54001c41103c0d400760300c5066490424a0801c04102c040f00300a1005000c803513440d000848152007a001d5a5005d80040c160154500c0c20b450041d00819485c0500c0d84a040c554854950714402402601c5042c0b8026014504085c103800c4000a10f00d8184582890440b0000c4045030940302407094500030016580003280d1300d4684010380f810071030054010001c40c2d042440040190300c510080715040042600d51800a81e1510780403401000c030458003421010780706046243d0202c0742c07047d00242d008101c402c40440400081c0c140e400d107420381181e80c520b41041c803030480852000240380b40d0104640c1c0300c05003103101d41d424810444100301d0308040480c2c4040340780d40350018144110f0015405000c1c40d03da2010003200083e82e81d0f03804011070043c0240000000f0a00c501c280300c0c0400a0810780c0707040d1103000092030b05c0b00300744810b500010304c80b600d082120200c43d1720404056940058140885180da210103c0d1803803c1d5014158540c2880104205240010183d00c20380403c04a040c0110085 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 528896978 1250 528895728 528895733
    0x2502011704050316021c0b040302120418090f0503120a0f0207030e1219050f0d0512130f0f3e04050a060b0301060c0501050105010201021612020a0c0909 67
    0xc124034404440d041403205041000103500001211842c1c00d40b1200c0c0260054240300090700103000c882034508840e50009190304010b044005540198425020303100751407403051164000d4040c9204031904450038501fa881a881140d20180f1003074040d035000e813040c1d80503071078461441d0300099120321700c89800b034108941c003003031403080304540c40c2c0d4900c0540c501011510020710000b004142d00740f00e140603184800c0c0d128001c000c010f0120040300d508503190b02c61810300c2a1a1020181600d405009282c0300c041e00a200e03170300300d07409402004c90140341d5440c1c80d2107145100120311011502025000001004607002c4c08149039200e00c18154a0f000e02c50f1041850b03080035440f1a6860b07014085520381841d40d0422044504401050b100001c0b290f982c0c10a05001d05140e0b404240091000000070503502c0d40444440103d600880007400103981c2d03003004a00300d01c1280d10022401d41c0c100c0003000040d000c050183e00c004c8191040f52185e00041c0c807100501011a405200a5035880410104 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 528898228 1250 528896978 528896987
    0xf01020d1d040c021605060405060723060c0702040b041b050f0d1805150402031b0307090e030307020601060801050f13020d1a01180f030b2502010606110606031b0303250201 76
    0x640340a6500500f01403070034010ac0e035240190b02c00240010100540d00110f441000348a41e80c83d503459080313410314113288465865551180c0e009034003490608c0c401003280c1c10140500302c00d103216010440304604070400211110b03003040e1400c090f00c1e581000490820340e0107004010a004000d42c1d0b44890309280d1602524182c00c0c03035600b035001c411090801c00907030f901050a02990b003c00a03503000350007841c0000b80c200112500554500d80c68042c00004811000014620800751a001ca030140c0c0d0301c584e010b6405900074443c103030b480303010350b00c03001c8441c1062340768104035407144e4001508103804509280c00fa10030000e00c1006105041408544035a8803105440c080d50805410f2a00350341010011808a80309000c082c11b0b50311440086140c1120140e0019060781c405001d5044125200600a002c0c01851141c01c00003003444c0c0f1241c4010750042052802007400400401030384410f0100c059440700100e03411945070009000c52240000840010711010090310060610007100c0d200150 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 528899478 1250 528898228 528898273
    0xf03021b040e07090b0a03080f0306010921030509010306050d0311010f0606020307080c030f070303050105090c0c150a1506110d05030118240b0c0c0f01020d1d040c02 73
    0x520860420881c01c0c02c5000c04940c40044c1c1340a2103010071000c18400100c2e080070001d80c40280020030000b6901202c625100c0654000d6609070389900e2040d80c2c0714141820010100025142203500100c00d00000c0d0140008000c909411304011175159a0348001940c140344012003540030500e0318002c03081108081c820305000300c0300000c0070865182000e0009540703024440c0000c065840000780d03c82203000420a49080980d010344a0340d9880241c980240034080038460b2501481060001c14118041c10040d284503003a410020110701107515803245a202014286075038840d0b030b420402039001e009043c0007000d0180d9444041001080c0d40e10703149000042c40700f20040080c14401800018a1100302200d5058801400f042078910b4841c041d040c03102d6100e0408103075002080002c0d00030658400340c40e968681209a07502c1600d40000d0080c1c43c03503000e01003801078001070034070000d050240c0321551021980c0d0501c0042c4900c608082400c40380c0104003d809030f4020070108400300c40401540 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 528900728 1250 528899478 528899533
    0xa05010c020d090605090d0605010b2205060a0507060f0c110f071a03040311100605120c06030615070215040f1e06030c0e040603200a0b030705160f0302 67
    0x10314400c0702195000300440c1113801071801700701001940003260b40d1510380d00c40207190003060400c0296510310702590668802c816600750749100030740914201100070320200440d8400740030755180124031081140c0d15842113904940c90750b9903c5908019000ca4807030b40303040100c00d4449124840c0164829445d004c2d9400920203503070f00c01d43c030a00c50146c454610703100411034840480e46a40700d915003680c1d15480d0401c460301c0780c0b14618540d003c203046900729408840042d10340703031243c100091403941c540b60641d00302500224104041040c80c242102d440012040303042d1054188142070b800202c0074003920f4030440b03400d20082014443d040542c01801e00030303c0d4481c12803c0710345070660844a034072031034450780042c15034031281c13001c40f00c1c0074543c246082d1100a0041000a85901c0d102924440c2e03245d1090804042d901c2030b2015080c800d003a4000c0c0c5804400c060b08554410104640540c40f100c1c4002c0819a00041c40c40043c017500680700d51640b094018002c109244001c3c05a140d0421020 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 528901978 1250 528900728 528900733
    0xf0e13050f2107080a031119020a0b010b09212401050a08030c062d10080c0604030f06110f0d0c170f06042c03120a021201060503061c050a05010c02 65
    0x10f10001040c9100b140e10b48141804c01040081d480291420350f0b009048806445842c0d090129904a03408203420211a100e00103503a600d90322500c59241034094030041d82d400810881d524072462480000c401240e418038011120404443c6400d0004a05550309a00044c1c3c04200140002e1402c03d80e0100a424440011400c00350780c80c84060362644060922000d41542c5200060365409029107007003e040c030300c0941e54041c141540c483d842d01034a441091044c0c007854054405614264007200d080303c1d002522034110203450340360200140301c101160700031510308001c40c0b045c1b01400000ba04000c540040005140c4a928034064243e12024024100e40000c183c20809240d54405109030000410755000903010841d44005104c1000301c40c416614034050340f164069000000300404055407154000c0c2c81c16101d10a00800760b020b1141070b00f00c89100c4100601586200b4405158400c00040041c6000c824003154913460100420084e11035820403800c180a0100074002c410340c800700c6100 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 528903228 1250 528901978 528901987
    0xf07080c03190f0809030111040602031207030c0f12021605030c150403200a021306090b150406050c0712060f1a0a14030a0803070c0210090f0e13050f21 67
    0x11801000f00c00c04400506018020030202d075152800d51240c0b1081003085807081c0e6030f507100c2001a540c0d4004040802001c00d0b140d00080d03020384240103440c00030b046a10340c401c0d24940420203a03541c2e05007449240c83c041c0e09002e0401c1e200d000c1c0203242115401b510282d641d40b0380701c0410740d0820b4118401103c403404604180000aa80100b0701d012000404684000d2411002000c034100001c42034065400654800d8034100d00034103501c10000ca84403503104000502e0342e04140010f5903007041d044400014244020080d46c0d0140b0000c11070750802d0000d0707030401e40d220152034807903e41c0484190749050741e5036a540d40000d0b07a0700c81d0101008408001c80740c03c40a2100081e0310282d07a000d8660042d00d60f40f840c4a407524100450f00c00154032008003510380c5000b403002001d00070300d400309130320916190003d1102c86005080000aa40c0307001544c821860030100007040340d41020b8040f1006100002d044008900180b01d0442c504c0c0d40c90011701113484c0c800c0141c1d001c10b8001002440180700810 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 528904478 1250 528903228 528903233
    0x160c0b04031403190311160b2a070204330f0e060a06050c0c060304060b151201091d0a0b0109050108070e010e07030209060a0504210f020f030f07080c0319 68
    0x60075140125035621300841c2c0c804c1d5a0705805158007c61a40207a81c0c00ca4550610030041124542da10a403010308001c041c440401c00b0402c0011015031006070103110401942c80036040681001142c81a44009c0c03c1c02d41c001099081d815114010150045005024083c00800408004500205901d030101d0303203541444400100c190200c5c3c8281028000009005901c81e0308c1444810003403a0700405c400c1d20781c509410034101600184404070311031710b82c030000d40b035512400b0010341d050380c4c20301c5141060581c20803684c90003c120148407070040d10b1b94444c403000360010801044c600305108000c0c80c5800e5152042d11000e9a2068001100345d4015001c284022909030150604550104044008540b02e81406270024481c0a40080d0405000500008607903000300040040314101c2c020610310701803c0704c0005da01000d90038000c1480c40b542e020f483c0589002007403007a0b020300007420703503003c201491691854003203240e00100e00b6421150000209140c02c2c422010542000344940d4200c05295 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 528905728 1250 528904478 528904507
    0x60f010903020913062405041803090911040e0c180a1d0c040b070b0103030905060403020904060911131a04090302061609030602071a090a0209010506160c0b04031403 73
    0x40c01100002030f0b10210005208043d046061b1a04030b41041a002e103904001c603018001c154081c4a02550900900d80700c00110014500d0f005074140da0741d118418100341d20b03000035150000380f00c80305120a010200c4c00500c0d101d040b5004010f1a6a40c0d607590004440e10400c284141203064410468202d04021210414480c140072001106d12031240e0390f640e94842d0810f015a800580c4481340204519040103e448502416280a51104c0d00321907a99810444580328500009400080c00408240005c1c415000007075024861000100340b04000d40c0407403a071800c0b00c01580704031515401d005100405a5403401211401138805009800c0785880203591108094400000699521400b48003588101c0e4030708007a6a01c45030035940e503025402c103a14004c8204640300090142030002c50f01c26140000d0121141380d01800d0496940c0c03805d810443c45030000100304800c0203080c0c105100150b184840e80c40545030382d10707049849600318100320600000f0440350307813541e901c100668094842c03130 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 528906978 1250 528905728 528905731
    0x1030603083403020303041a0103020d03050c0109021e011d09040b09030f2a0a050a080901030605040f020c0c0604080a0206071a090f0115050a030f2108060f0109030209 74
    0x10b500741e95081d00c41c02500002071440c80c407800480500580001c040542c0400114000c42c099410b00350422441141d030550450700b072200947c0808269410f40010f40103a0183c444c00d0030780300c000035160110360013140340f581900c80c6040441d050061170443d1980c00c00c051288000300140f000d003410301144042042c015024201820704100e0300000385100e1800c0045885800c2d00b000504d4580382a10181c12840d01b160102a44040d407182c40882e0108000521010a40e000340007481e01d040b040e00e80844941c0103801182c105910b5101c01319540d111801841001c0d84c0058005907a0f44002070700740d041035071003040c0303070b20448013000f08000c96480081d8000b016034044541d15528520381c9007400d9048140e040c0605a51078810400000c0346c0080b81002082d1081c000a208460249280000c01d000e0f030f0140d20781c4070103c15401d001050100904515035072107a4511210303802c1d5103000561802c0406403000000320340300f0800c02c203402e0021502c10809400e00300050320034119030018418940 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 528908228 1250 528906978 528906997
    0x90a150b06071e02061b0601210308151e090c03040f12050d0c0315050301020c1906150b071a041a0a1409070303020601140916091805010806060103060308 68
    0x140156400c003070b000703c90740034600541e00510b200d40d40c544d40c40c5042281a5418103038a49802040000101030b10384404940f0034060010541580036140d980c15181450060420000031900d8050a41103864000c02042d04500f4902040c0c2c0c08807100c01044040c840c000d020051000c0180244400169003140001ca00f41c0c0c007550241454203103007421212030044e2210301000c54101510b0540311501640003c100d096095000d8005a403034205240c00d0b441a21200401a401752440c2051011000000300383e043c410b2a0110366a900107081c2d0000041a402484a228000806a041001c0c0940c00c1c60202060050700c915464030f62250280030030380511600e0104005070010b241c960741540940f50008501000d0081810035007a45ca655501d14003045016100c1d86001040c1703070550080096039154001d040301710f01d90703907406d0711100490b180000c0703000c1c0305102501040090b05440b055262003070310040005c056140510a40c500940500380a0502d842c0507010300c04202e106040b110b0521 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 528909478 1250 528908228 528908243
    0x1e090c050d050a170c010b191a0909010e100801060501020303010501031d0703050c0312070b060f21010f0f090203072c0a0507020d0908060105150d05090a150b0607 72
    0x3550900ba81410500c000c0100400641460f0700554100e00d006442c1841e03078034000b0005d00702c0741818840861550119441d800c8000c1c14100559038864980407610058071100300c3c140003001020405e85c690070381000c90703485400230820680000c0d80f0440d10090111900a00c0254606000030303440c4d01c418000c2504051f2141c40f4031900340c41e100c0030f40c4111114241100d0440d40e40e800c1180c0c03a9202c0381d00f854820f02640c0100065040880d064502c0303243c22200070350f04da840386c4040020b1131040c40e07185074012050480580e482d20b0074006204050400c00b001092010740c3d07909080468500b060b17520307901031a0010740409610005005000e8540440d00100440400e901a810000f104026004020011010021805055000140981f03204c0e02150082c0c00003a0090300d4240140c051000755500c6000100014501502c03a0144110000242d80c44c21969440c1c050030f0310f204541105031544444864810804040b58000c420b040f40c48042000d4482000010210700c5407800262216 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 528910728 1250 528909478 528909499
    0x11d131203090f03030f18051e0a0209010608072d1404090f022701051206010c1a04030917100e1c08010f2114011e1e090c05 55
    0x12070296008000300383d00326000014880c0f00d494010040d00780f11099141c200d050189224000f0340c03031703c104105240e01c84040c11004540f0700944c01100c3c3c1d80e04d14683c0034414010b00c500544c80e0002864080c01c4103540d403552a1801c1f1201510124080614034080c0580e002c2e1102c8020811100b11105200c503d46003509219840341c1201d9801140c004c240000d103000c034414144415075000780000b10014043e00c209196150740081c2140c420095180410010001d0328460301c1c1c500801d81d1701000504040e0011801c940301c110880032491752404102c44d2038001d020501d500800070900401820604c03501c6a05450036042d01c4001541004516076290340c0c500e200d007070043c4511400c01400c82c0410b07101204010300100500350038814070314801d01015010541d07403920140090038149500802d2041c440ba0ba5410014a0415110708a9035503548500e04004181d048c0c2d0703442600c2505000301e004100b204050204240180c0c40c4020240b8142ca603200007010343d226402290703000c6848aa05 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 528911978 1250 528910728 528910763
    0x30a050711210309010813021c060905010207030909051510201b01110609060c071103060f06010905040902030a06020705070e0403200a0c050f06091206011d13 70
    0x3028403450001c2c0011004540781500744000006050660303000d0366244800d0710f07542c5290219444252021b504020803552081c1d1600040140c0345001d4401c000015401c240394581c1030881c4c103c0c5208070f00144082800300041e081c140907041c0c00c2580448001c540000c00000a0107004030503e26400b400300c80ba980224441a6841255481d14200c0c295885002d0414a01881d8400076100301e000c243c0c01460001c1719840011b0041c0b06140000c001c044580b16405450702d1034201c42821503440e5401c45101507152818030095004008044104440707052500001d05280b88c1030300030502442c60100c49602503500028500030945d08080d00503510003071381c104142454495005441031065902c10320041540c09400101803140c071010001c01412036400b26920b50345850030140104083d110b00b4805440d1000d011014050001c1c256441d166128020801d60140040070702c60300c1d000301d40104116aa1181c03400801513896a04400c240390840c9036216031000a20040d0082e4a2000d10014 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 528913228 1250 528911978 528911989
    0x8040f09022811010207051509070605030619080109030f0e18040219030c080c01020d0509010806010f020115120506010902070302061f03021804060c020706050403062c03070b09030a050711 83
    0x54001801c0300a5581c0c4501c0e080541e500c0d5800048028070480230710000b5522440491554251100b03581c030285542c5554040140349010740420680140c14560005a929000d115442426200707072182c402b0664601009405002101040303805074400441107260039405814031540164120355403e5079035031a1000202440c0c0a1f0001800901d9240010420b100e000a1900b59158240d00f100e5100c2c0314140704035660b020781d0074480c0c0442c3c94100460300030342c014901d12610407094400007400c070344140b41c0041c2942503544100b80c04c401c02c440d10000e0001c00e00c01140500140e800035407410100d030303078000c3d40c0c1d500060002990050345160000d2203c3d0481240d4003c640050220640d00c81c0c0d9807410903100e0301604e08662040c0380140300da0b80c1c14004940340d0200c030031a03210282403914544580015040d42c40342800d100e00c61000840748152000003000c48011044021501c4080300e1500e01c42c8000050203068407948107000c220001584581258074056001003c0780fa181c5100c0301180c0d = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 528914478 1250 528913228 528913247
    0x515011205040f0605010602060a150303170916060c030e0a0f030b18010507081e040203061803120903040e09030909040618140609150f011511010908040f090228 71
    0x5011318100400001d0b00e0361700003801c0b4000e030500c4200300191036647e85840b03040042c9200003008500d480d041d05a503140100c41c003030391010005003614a82405400d444681d4006a0041800300350b042c02054117140e40102002001c820030b9400100443c14034440005110941c84010802007110000681414005d42112002c09224000344010f0400e90070140200c00125100b0007101c112481c900440c1d1014000d042c01aa0050040c10040c2c88210441c071200c0c92040c950305403880100b015940c181c40c008405481103a03404080d41d150307401d21061507122000540300c00d59662080c408600700b070341c0b40301e14150406e50212000070442d08030b41c0442c0409840c0e180c090440c001003150036100a1011482da40310303811180543d800b8400c080c03400040300d1010781c0d9040040c0d0780000140800d105010b410640c0c4140c6040000d01c0781c480b03616a03800e6640c81c0700c0c12100c031000464104101890400190041c1c508400b0960500d0b040c4a0505569480b00d0180d23007103090000003003405c05002d501c058 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 528915728 1250 528914478 528914483
    0x702041d01061401021204050d030c080d050a05130201170a1d0a0c0f0f0b0a09080d09260303040b1e0112060b10020c0f06090d0b0405060f10031709040c0f02010515011205040f 77
    0xde841d11880070002e0002c0004030346002d841810200040c1ea90011121080c1070310364140c5038a1407400c0440641035101030000d0140802542d02c0411801c90350150703a842c1d22000703001006000001c50b03890240c44800306940650701c03850140e0b03401d0050b068400901002d82e40030548240c1c6030900c0140c01c58001440e940604018050882962040c1d07a0160401d01503807810b804500c2c0114440d0031004180c00710141b00d9030290070501c0460006100565820341011822064020380c41a5000c00c0c05244000c0c0e020410b41c2a4217044201001042c0c041c080350402d0441c1d803601a1071501c1c80103500c400b0140380340e511600209041030040c1e550003040d98260744001d0310101030b09207a450049044e200030f9800360360314840d4200050094810f440243e00c112007004000f1f02e81451552542e00034115035145428100e0103104220036600c40d4418240d010000c1d564070b18112206c0e51020382105c0d0080c00d03641500c0c040034800f0401c3c0e600708500c124114080800000e460307495017410041c003078486800 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 528916978 1250 528915728 528915743
    0xf031202120108241504020d02071a160305010303091503060b0d15080111120c04030618140a0c0611070503011a1c170702041d01061401021204050d030c 67
    0x402c0c0c0c0100000d13500340c040300c85042d004106240200356003401a0459442e0000b201c1c0c1e00b885402400e16030040c04004183c1d20300941020f5030380d518003c1c0e601c4c1d2100d0000c10f1138000c00410903411000889080c0e2980d90703040c01c00c000d50454600610800c10781c054049880e001504a000c25403103903001100401a03103a04640340d01c0d81c03840c502e0160804240060380702030140004100150103118003810008014004c0c2c0c9409a0500c500390503100c0145896880074040c0000000300344c007070103141000c02d0a65200b221040c0c861401c0000e441000061035415484540104d00141605604906945039400d0049100c5010240d0f1854007003650040e40e09942000303802070045506000340440000200d8000c0d42082c0ca041301c00801c504002c401400c6207500034108101c2c1e801c12001410032031f0010300b000c520041d400d140f60007088015207004040f13a5413284100b105052448030300c0500f4109202811180c4101004001d140c01140100c41c490445130307005004142c0a08810001594000c01 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 528918228 1250 528916978 528916981
    0x50a0e0f0316060311041410020a2004141e060409082d070314091309140c0f130b0d020d03120c0903050d0e01050c101d01090f03120212 60
    0x1000c660701d50f8411903001c00d06100c4860a40403525081d102a00c540044021200d0302e180704000c054601c030080d4000b5401840030784404260f00001400844240c00078036055049017009001c100c42445010045a00030f131404c1c0000c800941d102c4032a14400741250711100c1e1038600001c3c005146080300107208680c000b510300c00171000e000c1c64041144c0784407030866105482140d468083d10aa000007130010310a55455100040700c0d00c082d042c1c20b2405031011302100800090722040f42c079485401c1c0c601d40e4051350311801d150340030403070040301c00401e0724140c0d041c000040102b54880485480400310b181c541c222100760b6214556901c11180d0020622107500589041c0908a0341c9142c01c0c0702c0b86d8a0410781c04400a0380103040d890f08680d4410300070108a600c20008565130070320108983d041007030401030103203d0001000744202110b8040c100142d240f0360706003c0c0c82220405001e201499040c5041031000c1401480c02801954140c00c09411983c55449000000c1c440c40c000241d64010060 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 528919478 1250 528918228 528918253
    0xf0309100e0f041a1c060509150c07050705090108011407031e181e06060602070e07050a0e03011e150803040b0a030e1501080f01090b070e060409060603020a090f0303050a0e0f03 78
    0x1940001c21700e00441d0b081110b611641c440d140caa400c401d55065000e0703031140106011100f684000c000d494014420b9840042c0c40720006100e95000ba03101c1561070b0b45906414562003c0700c41d000d90030100c5400e040001000d40c921034a201e03000d5507142d00f44540c0e40d4055501c0719420008015a080e400f01d8040c144400710940392810050401080c0c0e10b00303162840200e001800000c491090384c19103042c1c3d00c06c69413500b20403140355001d621010108614901c0c10341841e1424040d800080d004101d080000c1210b4208100c21242c01b556052111b440030081000841000710031030301550111055035a840b1241c2d003043c4d019200c024600310403440f484e005040055240b10809060318038070000d803804410080e10701c50a85a655001408100326080402c946900607104882e0152018081500307041c2c0d686400401c5420341e44c0aa0040703a00068070302c1d0100e52041c8100c02801c100000112030600f141c074018a43d000b07081524040c41010f050303100300703a910a51203040030310000f0122003603440502c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 528920728 1250 528919478 528919519
    0x5040c03020c0d031b08060d0206030406091a190b130203060109030f05030a12020703081503120706050702060603070b071704080f0109060e0d02190807050f0309100e0f041a 76
    0x5881e00c0c0005d041851a8205101c0c0300e4050240a0080c1341c1c003210440c42c1c08010701e5070b0003c1c01c12140a95108440400501d20359444049100034000b12003807440c007025511034499940006015051500c4c1c0301003e035544203e518240c0300e46c80070b001a01d0ba954000166030040941c0c102034849000c03202c2400030040d002001f071915101e2a5074640721305400110300d0090b4020440020b001ca01c4183c00128580c000c50b403156041e10000702150298080910b00142a50018200382c0324a5154010003115030380412611b50400e00640040c0701c3c8034900f0034480120b005888004000680d80004000e140c0070100988025000d1407068955282d242d01821f80200203a40341107e405003440050b100000011030042c230030101e0703034001d00062016220b2055595040c0c2c5411204101d041c8110130100b40d08100091030604071300010340c1c2c1d0721440001c1010101d41d900410041100c3c00c4421180f0b80c881c601c0c0100400701c00c1d80c010581c28442030321040303000d4000e45804d800940255003000c520405 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 528921978 1250 528920728 528920741
    0x80403020406050108070c0b0403051608040801110c0a0b060103020d1a0316051012090c0f1701021926070906030b0a060801051314181e060105040c03020c0d03 70
    0x319401c0002c40d40d60320041da40b005044803a04040340e8a8410300000c0741c000920303d07600ca8480e29220746000d540d80c01211403484000c0054030707005404602406054024403891150b0305014000d2401e003c22401d41603038410000b40028101655403001c5020f0741d0003901a10266100b116040c42500369214400d81100d0080c00903d110313110725505c001e5803081000511003030b158042c007038068000e420700050302c0f840c10382c1d0001800c10303130740314404c0c008141c1e998100800340c031440229502d0b09161480c02c0d000142c007001c1840c42a4030400c50924035034004141601d404000e820070b0603044d121080c200401041d41d4000c84024404e80c400c00900552003d03010003928170342d0314204008000e400600c114071b40e2a01601021070341c8280148074030b2508003d46200d11607003030340124412660017400354030487d003074940441c5440d000310079401694050000800300b051390704014110a0700800e92664607013061280350302582e40da80518000d03e109030100c0d840c6030100b0341115250700d42500d005001f003d5 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 528923228 1250 528921978 528921983
    0x918070803160b0a050103080f0903100501080102040e07020f0a030f0507060e010e100207050d0e06190807030c020a0c05010f0504030501020c030408071509030803102d140604090906060e04080403 86
    0x1903c0300001c042c01094815141a60b4100030303c2410601d0080c0807100076031151110950604c40c114460a0201040c043d10340a0a445000540c4580c6001032000c00c2d48005040c250640d0409014111820300c00281048140d806180680aa02d18440306803141d20a08401821a9040809007003038404150049d000c1811600111a18401d42550f40c1d07049026020008045800c184a0361411900c540c0c02204810001040309180c04801125880c02d905070100c0c0340046003c0c401001540c5415103d5084400030340d0001c2c080c01051565a8030807814240034035418840410014811603100c0d1007550080c0da07001c03000715603450f07003a480f49a0320b4105100d030528030b102d00b441c0450810500d481c1210110082d4980007180d900b19511000d9640004203000400e01d410b510020b140c0c1001107510300300707245014103c1420b170307a982c9841c2c4034120103402c1150f41c12400b203140101501c0b500700f181c0c2101c87c00c402c002040c05652030f103140540060707488040e9801000741400305001c480d2000700112071 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 528924478 1250 528923228 528923243
    0x90a02010806150d020904020c0d03090506010f0e0f0901020c01090501090b010f030503030705071a1504050c0a020d0e030f010c050d1a010504030602161b140906091807080316 77
    0x41e41c820412203c01a1004801102c44050016424501058028146561b0028405070410044105240c9007504207074050001a4039044a90700f0710800348802ca01500580c0c003400d00b082c2c10001c807071203030103805003c210041c0c101d8000100708003002c0d0b05403a481c00c107480c02441003640030b040030750117886112800e40d007001151000290080220002408499009010754116035a801c000d40311600308140c00d42d4000c901c0450301100078903518202e0710580441600c441c0a0701080c1c103205c101c9134001c1c031490403241d00308000e4a50300c1c0c002948620500092034100911035003078021038241154058107c0782503081069043c65160000f01510f035000403103204000c07644914200200084041d440140481c074100000e0002c603c00780c000b004e81c9040303041041c1c08282d0907590951140105200d50588868080d0240b240881d42103048031054011120801503040040c001450494007a10441780c0794803040e50007100307072400d120610081440c0001e40340c031031410180d04d0342e00fa600e040d803c55008 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 528925728 1250 528924478 528924481
    0x3060b211e27010506011b0f1b06110109110d031202030a0b011b03080408032701050709120c120c0801020409091a0f2d01030c080607080f040b040606030605090a020108 74
    0x102c1c014440e0034890903050b90740785020b00d450704046d0001200c00105403030100c0c42500d01c00100302803106c1264070508a80003e0020343ca4401e0080048255001c40300307559040602080c003007185800184d44a031002c691780382000e44607140580705001c10017600060f00e40040301300030419465902214030405c0a884000798001e5194280650380120f80008020401440108003c11281c0d0041c0d580700c580d120300d00070611891a01c0540d102d5141d4070030442603440d401003100e515441503210300203101c4054200c6107030110381e0359040d4041c01130040f08a10031008904a061111141198001b0704c0e82c507000b1950b554480740400044e043c0000c00782d51450801001c0400c29003015081403103034100d5070145c3d0341504c2d8550080540300104000d0300e802c40d0281c401c0b01090b1001d06000c1e000314032860351014040d181c50481410404020860002d0207040b20400010441598a86900c00e51100360103105a0b55844d041c0c00901603030f0800b0381014544810400d182e00001640300c02c043c002d0700c4031a8075 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 528926978 1250 528925728 528925801
    0x60e070906112109060c06010302100c15270b060f090105090a09020301020c010c02030705070b0c100b010201020f070b041505060f09100506130603060b211e 69
    0x4110392040b2601a80c030000c0000038011680031040c1068818000c014680302035040000d004d40c00003e014500d9400c44001003046151801030754803c0581c078141040c08010588802c44a52a00005c6910309902c80c0c01075001c8009000c0048034070804000003641761002d0b0700b04400705072821200e0764000c2180402034040c5140545130f41d81205e030002d1003601d4647c0d405007480c010384500c190403a0199000c0c400407640341d60a01451101e02007030f41c0295115452410101c0c6400e001d64405680341408200d030302d00c5e060000c41c40450f400c030380780c4002c10034480010041b402031043e520369225220f0046220010055507001c0309009600070309440310300c0060140080d00b114425248540d020306650407400c114140340d20401d50088084c0d00348a070301581c41d0b01103200c99210484000411b50341c0c44050040c190188140d002908001061506042d00c0b480d41071500080c0b408082c1003000c224000424241e0240d02801d40841e04602e055050700309401e818a6041100ea0710300c2c0641c0511124682 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 528928228 1250 528926978 528926987
    0x1051644160306140d020a0902030a090203060a061d0c070b10170610180f0204030b040c0e010e131115040f08030702060414030a060c080a140702060a0c050706060e070906 75
    0x3600d1030802c4520410b52510304000400c2c40040c2d080340c01c0a41c6401c0000e02408609c041c620070300384580007244044440c03040605101d40102910750135864010306001540b0449081861500202c0c000382c0c0544541c0d0194109000f640700003040b0040e582e00b0000c03080094400303071080300c0c25041d02c0c1910440c1301040c9a290b240464170b543c0c18130800c140400c40300d995040c410304105a403180000c0c0b00e50503003103000d0582e84660415501d03801400d0600080100301880c0c1c10090070010540002da50500720a826903190107862180701c0000f103441c1105020392404030140300c4000030001c6281a80e00c014400254009100f141e050001344180040c00d2100402210600b079401060725180c5030812603000d4034100303d0311803d9010700c5024503800000e1400d104039203035100c1302e45914805180c80155007080e124003030003410b02d501c805000e101c580e680001e11150410346100001c507185018800484039030081c03800c05001d0b2410042c00050110440969600505103075690101a5403102016074 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 528929478 1250 528928228 528928241
    0x50103020a08070f05120a0b01140307050412111801050306090102090307120c0b030411041a01021c030b060409020714010c051b031309020309010516441603 69
    0x101099050b80012200e038410900900e1041141c100b45083c9200010b108401c628210b0346c00840070b903201244e542960700228092404144e0840283c51858403140051043c00303284106980418802100002c00c141d1080041d000d02c1e0250401424141021010410310340a00c580c0d0f00a010318804280d0307840c2c1c18002ca801c14000039008051300c5140c800d81d65009a12070506035107403a10000c01042036000500294001c1f0b00507070b013021960504604010484840d010701000c04036007070219004a980100340c12400304034008030000c0d07806c5e000d0070030b074054951104416030203c070004000c0b45c0351740d00784d001d0241c080c020024101c8202120403523071f0072030702500c0d03148001c41d03014003000d4210000c1480c0c102440a40340140e905046008010403400047c1d900001b1502d60080104002948248181030b4003000d03054903054a800ba850002c0d042c44a4802c9403200d0003614203484000104407040c0f00d05000c071504047e440880c452084201d401e00030750300644101e10364850b40120320b01c60700406 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 528930728 1250 528929478 528929497
    0x110309011a0a081f1d0a060c020102040e01090906090204051303030b0d030219060e07140f0406060e1e03030307090609120203030414030a060c0503160302040803040e06120109051605010302 83
    0x10640b414002c0810f80c40c459452190361140f42c2c40c0d80e0b08445d100184e185090a1007900740c02003007041000e01c1c01109490005400c41300b160310521003084a0310185202034112810b8050000b43c0c01454102100a01401300c006900306040c041408010042d08000c151114001d980c00c1003180041001c2120f0300d400d6140141c016805040c103d0007210001c16500c0e83d040c40746000095154029410368140341c0c41380c0c4540c400294a030a1010582003040d98824000703412502086402c1c20b025000d40300d00d01140d0b0301b60082418080b8604141c4442d83d6014040c000142103a0b100c1c0b410443c010800e1203217009290024881c00d4000822452818090f0f84081c0e005010f07505190424400207100f02c00c042c9c10726450302c505550b0744e000c02e0861003104220210390356951366900d02409400c42c901000c442d0101018810042000410004400d031425a08605401c0e6019141c1900182100c01e001c41c0b004c80765407800e4640c6c01080300004114170a018203801d000d0b11325031b8605c019000c83c040e40480c03 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 528931978 1250 528930728 528930733
    0x5031b04030b040303111e070b07050a0801090e0c090f010f06021f150b07060e070f0b090904020303040b1804060509040b04020d0302070b0c03130b07050a080a03110309011a0a08 78
    0x3103030010303000e82c0040080c46032111035142441e51f807010340e180c00b1140c035501d0449000b001a064050014500c04940d015000d810030503e0100c040c2c07c018071030745e414404c0d11000c80d6201c1140e03148403410700189c02494001031420200c1d060071451412050400c0c49500c8529000e01d43c005512400400c1c1803d02c3c50082c4c803000c00d02d039075131300259001e0200c0b41c011501c1e6508602003c108070f2640006046070310300a00c0000307000c81101c07643c1490a91503802081d0918071380d000410a4600354412601110001d46a5007641c1c0c4071072003c84d156020760b4101a00358000424199020511911b142100350000c40c2d0034030007a69a102031101410b002d0b2400741000400500080240c2845c5001c010098868411155015514150210260019900100a6000010880e80400500940d04080c04401314964a01020f40c1d40e259a07440c40380303c0c01003c24002080c01400d1500035400000840902c40c040b660300e2a0500d411802020340040760340c0c142c40d00191460300d6040c0034180c18151280b0a00 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 528933228 1250 528931978 528931981
    0x203421902030613050109020903060a0e030d1a03060412020705060a0c120e03010203130614060303070314040801110301030b130b01140f0a17151902070203010b04090305031b04030b 80
    0x2890310195000620b62500500641c81e02c8151030250f00c10301d4004d008420300161034013030320300401d410103101a10210040d0f08015003000d5111000c0115442189000000031314440d8681c604441c540024100350342c140507503000c00041c044104030341c004003400307076080d12181911030003004610700078980100f0020b44641450707000076195500c04445c24043d400c04807180e0303503650700083c26070b4411554800d5404a900d60001000644d003e84a620485014070569500c2c02001180e40e0303018507440503042203003c94030810910030102c120b03406094400700034024030300c03207141140c82503000f23200032141c0d60340380c00005d80c3e0710062840c8005d1407030340a44040302e164600707600e0f100110b00c1d54680d550b00101049040d41d070740d5203850954005106403042c0000c42e0750050101c034100300390740c0d90180b01c0045801c10850048188074000000c00806080140c44015600110f80101880da00c4c468000d031401078158285a0002c02a40c45801e802d4640c903c06c825225807801e140c003503844014023050641d130 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 528934478 1250 528933228 528933271
    0x1050a200d140a0e0d0201020a0203100e010b030303091207020a0b0a08070915090509090c04050f010905072d091710050106020a020d020f1906081f03021c020342 71
    0x18100b5240d1b401403046600d04032481c1c0000b820a0140b92201119a070b5800d51003084020a0180c0000654220701541c04c518040030410b8a070302c89101c802c0c011a000003551421507603100e070003002910f011345803252200c503240c5014001840540d001404a6030030340000401d00d4001d000e080040c0c0495403000041480e00051001c0600d02401d200c1d0b06009100405829031124810301c0e00c141c480b4542c1c1c0c64154541420f00040300c802620010800c8249601100007064940e4000c0200e00c02c40c0700600e801180b05002ca038516826040036001c5d408902c1c52880c0b69400040383e804400b00510100004c0e46c0e1184141d03540c0f01e518400940080c00c0038006800340c6440c04100032642c6010348091381840709913401c81c0413910603400c90b00204158405200942ea020060181d00741286d00113549902d06580018100c00c81c0e030031074400b10000307140c11441191014480701e8034205000e803034500c1510045001c641d080c5c03c009210301400405c0302c00542c04071100d042180c003440505109040000254 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 528935728 1250 528934478 528934489
    0xa050d02010f120c02100c0906051b03071a0a110c07060810031e060612020d06181407082a01050708072405060d05070501050a200d140a0e 61
    0x40c202c0c20140040d03c16403001c910507502884c200411264041c103860b043c151044412100300003400800c10400794000d1004039000003c0b11040c00300c080e03440400301c80c5204202e2070f501c620140103111909044003002e04501c402c56807406000990000e00a03c072101c032940c0c03800e00415202028951150604000880c01812484d41000a503003201c13190035182d464070507070308240c0d680c45484465110921400e01c500f920509001d09407840220140341d200d0740000c0e0b0401c22101014150030744d10282d000d4041c1000c0303604195180c5c02403c10340041159040d2607110503152003410300b2030086183c0000d100104422559030b0961585518694900b0000110f0300790300000b4048544400402c1030f0302c049844260000e10103942c10034002c0301d0022000d0541c0983c3c2010746041e000b211240c181038001280450400151882842d000c2e441d0360342000101d501a0503002054009400110142c0788814007140c0f0203204042a120030a484c40c4004082004d8400d208000000450340000d424251410 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 528936978 1250 528935728 528935747
    0x42616030e03060c070b07020f0a0201121425030b06160302030708031005041b022107060612050d05210622052d0109022203030f08060a050d0201 64
    0xd01e461000c40030001d0109107448420741d901403203c0350210341c440410100e602c110390321001a10240840c02d042409031903440300c00404c000d052111201020001100b56400740805c407074214000ba00d54200400440c0f001c0c078880030760180880c03081c800710f4a00c6000c0d0241c0d10510201a114901e40700c6800b030840c1e040c0340b1445003282180810085000418038840103540141c1d0950ba03165041481d240c100802c031110f0031850350780c00d134081c45008000c0b030b00803c1c2c05401144a10a2150b51903480310060b500707109581c00107000528028010079070407072400c40401100e10420481d19455aa00820b48660180c503181c84100209000480d1072076001c0c00c03005401500180c46083c212605981d1040403621308102c10356500e03500c00801c02c6115900e03506001d40303000c00103407a0200301c5a89005624940501400c264075800190313080c041060044401e09102841550381c81051b1249801000c0c011910300950020f8078040108116140c480d20050884070018840c40c3c82d00d2090b801542c25411 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 528938228 1250 528936978 528936983
    0x60b09060d020711030a03020d20030a0806040f0e010b1005040515090607140a0c1a16050f1c03050a0c0e040e01060302190f0b090109120c1d042616 65
    0x24103a13074000c154074100400d100052194002e03140560085034014403650082190003040d00714980181014803000c41140c030009800d00d45024036a4130100841c02429007001c1d61410030b46440c1d940c0c4010b42041d0f201c06500d0400310340981c4200d0011600301c5050050b8060182d01981c1e0490800d603540c0321000030200000044e144070700b000c11369140c141e5400700040444029801045403c01000154036403800175028109034402d41e07980c641008500340c022004202c80403005441c0a600f032003003c00000211504440882e02e090380080000b010460b41c80c035200d004a401c180114000c20031074051500d00c08481c2d07482290b0310044100b0080604030a401c0350049550f115004409a2103080440d007a0013070f41d100c204542d915000840d01c3d18034050b44201e0b90b91800b0300000c91660382c4030008030125094400440b14604035410540907070b651590107007a04035104c4a00c40144001400c0031031060b801018490f5229583c506000c1581b1104030f40c1c210307001c4003080a0054805400140c550310760 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 528939478 1250 528938228 528938243
    0xc010912052a120a0803070c0f120201060e0117030901050f0d050703060810052748030c090a0e010f0e0609070e041203020c010915060b09060d0207 65
    0x1d903038051034a54501d0b003607040d2207080002c2c07803003412a050442010b06001001c500074003080c1c01c9034136261500d000c080e05000400140e14108424000c4801804001c242c0102480610214109020703000380480c0c81014031070a0400c00001c1c0d4500c00b10301711410002c07504003461800302d1301401100c07076500c50089a034a01d901400b002e2101e2440d4801c00340308260703d0b1000940c0c0340c00c1c211131900d803a03e0f03c01c1c0c0c42142400c003000c01c010410031001c0a000d10202e4140341c04030b1466420400d040c00f1ba1345100118540e008021401880007144521041c0c540200741010030300742450b0300c6070304036078803056030758059201041200c45401d24907402648840f03026000158092400800b5080d254071500305000b8580f109102c0122a01c00d00c1002d820800d0500189403047c5440710700e040c29140204045c210110004910381d00038001d030126000040c082c4020010080141303428505181c264101a582a181800100c0c2c0e4020050840e50b080c9801440c083c18140c00c84000350295000c0207040300c808 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 528940728 1250 528939478 528939493
    0x21618020403080d0504030305150a05041a130b0f01030e03030f040305161b05090106090306020d02040530010c02100b03010209101e02010c050d0b031e0102070c05030c01091205 78
    0x2810f01800340c00180054078020502d8241418005c05460000d0010b030001c040b210004070056541d2500c14048460a44010130036110840e01510100036100d040c90b004a00426091640c51840d8840c800c0d0200449488000c00000d400450483e03001c1c0c41c8000c0250300c1040440d01e42d25004101d0341e40705110345086480c20f40020020048581d1401c0200d0b0b260380000c4d003a5000409003002003002d004180c1e080c4203158545640206a0740720741c400501620340c0015942d84a0708150111400380401604104806c9044108510041c8103019000f5240404008544c0e00c2c49040c046e0406401ca00d600800011103a80e54040c021309080054075810342d42080303603c55548482c0340014624a040d2241902020b10721601d11082d10814003220859140c80700c802e00480d040300644076604107880000840c03400ca4130121745841c0351002d0a2421080043d107000b0001c1c015002440700780e114007018422290f46409169440ca102100e1502103400c900051120111103605c0c034002600880444401d03 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 528941978 1250 528940728 528940733
    0x507080f180f0c151e031008150106030c0804030e10111e07060305010501230d090803060109050a0e07080c121501090b07020114090a0812130501021618020403 70
    0x8182402d4071640c0190042d2141032454640f4032142c550121420b004986090b0302c4a0b04402d05001e00d070303401d5194401c00b01c04584840e40c40324101003d000d4950440e01c038807890a41d0f141c0304002c24850403000134104154070140c0ca10078401c40380546d43c50749038008450300c0a010403441307806074130090701041200d020761404144108010180001c444007851511800c1207a05424254140c00500a0605140c010045640d0010341c000d402000c0c07411901c02c402d01c0a108001a11440d040013445504000c04030092148040045000b9202601d8802e44e2540d03540c14090b031a1418030840084209500003e07400354010b10055503c4401c1c1ca0750300340392281100000e00200c4c415500009412805000d032055075800240d454003501c070481083d800c040315940024420060f0805001d564000441e1403000da4031040149d001800340310082c1c0e440b00c40d4041c0c03c22616040281c3c244802502e50000007104c3d400411001582c0d000e008500e14002d00304466030185c8400302200a00311903081200001 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 528943228 1250 528941978 528941983
    0x8150303041211031b01080403051605010501051f05030c091f08010f0f0b0d0c0e1c0b0a060e07050c070e04051b030304051305130602040b1c0507080f18 67
    0x7800b001642005000c0841c1061071100d1080e8a00034020790207003c2d0b08010280b615605503044100340303000c8006a4840c541103400d800b40c202d02c81152000503680004200040d003225043c0d0300103503410f200300ca4200c000f140030003c40d6000d00010900810200b004244060010100c600c03000d000c11070f501c010007465580742e010242882c000070344007000501414020340300020040c042000c000b08140e0074040182d420f0300c1140a04121a640c2e612040d03150340c003c140040c910840200761411000030700e54913111584040400306d400750201d400240d211441440360000380e030307281c008100c15590751340c00544080c6d1180c07442805502c511040014200e500c200c00c0d43c8540e200d03501404460500e106045452094804c3e081d20035041032100f44110740750304071845940c0e9103110020a0903214000ca90008502240c4040d041900029003c102020b64000500031141500c44520400c54016100f0040f00d106540900c005022000864510900d4070780e41c82d0000d00c100100342d0b4900c4040703586403 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 528944478 1250 528943228 528943237
    0xf0b030a0f060c0e010f0e010c150e070506070804030f060902150c0d1e0c1b090b10020303010f030f02041d16050306040f0813030807030504030b0a0207050c0108150303 74
    0x321000c1c0c0d6002880200b1001d0302a24108803418140007000405500003c0c01d80c402c0003403080b00304684880c0d0f2043c2ca07031194070100d070b1a540010141100340342800f0240040c084c410010700240c0705404c1e00141d01c0c1041001c44a1060700096050304290440c0c3d81c40325900003e12080d00c84640310260fa03005a510303400740800040d9090720032541c4900e08010582030450f0b614000d41480601407080140400d03001e00e45d2403003001880c18050100091400a00c40c0f07440c40044900b452410320042032031030565010b440803240c22034000324041d400e52422a640c1c0300034080c0c800e40015100c020000505407100388100c4910060012030b110884150b00300d44582e540f0200c9201e5402445003825150586540307030051300040d009442ea900c0c158841c109036613025040106400c40002c0c1c409c041000d4122101c1c05581e003e40cac2c2d80e541d200542002041504640130940380c150071540404d07030080461003102c81c0107170b1200151554481c0100103460401c001009821410081800500560703004d02c01407 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 528945728 1250 528944478 528944483
    0xa05030301082b080c09031905060f10080c15041203030506120a1713030506090d0e120a06110d090b0103050d0e090a05070e061207031b120f0b030a 65
    0x4104000c2d14030880d109960076a00c048243e036149424441c40550302800b11903000d100b68031440c2c1c0d80c10f040c6000c00d18001782c414150a5000f2002d150008014020601a029070108000903503107032521006100307010b0661080a4299100d00003844050900250411024146420160902e07030780d40e0300ea404100c1d080e002240001d541c1c004101040c501492040c1951030444020714084002d5540c0034280c1c0c07641e0041e2449108017081c5500403565003200c1c0e070b010799400000c1d114107007404088150b4465154801c0c80200305014140303945402c15402104401140e9001170101320040c0e2140310041208440c8201c080030100700d42800d00d0b029000e002040c5209820080096165080940c14048083e20000422074004909517203540e54102d11030b08a8400580042d050312106810395842000310b0f12542c04c0400801d0708200c240b05991344602c20703a030903201030010222807000000031112030002c18001c00c1045007210580d07060ba901001c3c0341e4450800014150035202d000038901166481d08 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 528946978 1250 528945728 528945733
    0x1503020a02011b1403040606050d0807050106120f03050a2c04050f04020a1a19030c0806220b03070f030807021e031506130f0c020c12060601050c0a0503030108 70
    0xd2034251542441842c12107042102101c004180d903100c001d1030038210224070800c415005c4041400d20046030b206400400005000445034107c514010307070160030458094685520b0400c0c0010900c3c815000704003416400605418a81041c0d41c050300d058012901400411907002801d800000f00300811384408981400318002144841b020001038840040045055a4101d8144001600c40480e0017094070b2950b1001d00240c0100b0076140c4460041102d4070140c0003020301072444c003940507841001229090340c1c0350041d0740e42d00014441c10800c0c10790b240000689039100c000e495111035000700b440d00d0700101907494681d41d40510344c2118980d40c0094960300c1000480c141140b03402400c41c007200e091914180d405403001c07030000c0d4552603c04012460051001d001603481d584840d00d501da401d040724010820b0007480311800380100702c90070509015118640c0094240e02e001707010000d030340c0801c400801490703684400455403a004a007100d50300344100b495045c00103c007400614080d0100100 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 528948228 1250 528946978 528946987
    0x2011b080c010e060a2307030c050c0601230301020a1d120303090115170a020418060f062105190c15051903061805070e1903050d020c0306070e01020106150302 70
    0x6035082204e03c4a12100c001b94003100340658105c001405283c0e00a4141c1400030780e42840ca54203480030b01c05e9201e200c03028010352001041d00390b003030900710386020b8180b119541700000e00340c20315080f4840c81c0e0281c0f000c0380c420018652000300283c9000c10005018103102c100030507031511645141c2043e039807008a65103c8032110012180c245818000b04640124400e203400c00035000d9071070300c5240303501070b00943d2541c050348940050b4109800310707070368172a0081240304000b48401000300003502466041c0000d001100c013202e5565881c1e00f9242ea0000302805050f4214038295600c2001c0d601c084800588d10400000c2c62080d0220101a02c901510340582e1881004800c000103142202070790107040c64078106000100c40742d039807070301200c1600e80d00003200d4482e07200640f03441c201031b01c1c01b03684104000260803050f08a909564102c80c80f0b44100c450b54150341d181640c82d02041c02c132060301944802e00052201d80b05184145080606000000342c00703031241e03801c0810720140364001c40480c2d00040e = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 528949478 1250 528948228 528948241
    0x809040204090506100e1003020a1e030207030f090605040b07050c1804110d080d0b0102120c0c09010905040210050a120c030b010807030c081902162d02011b080c010e06 74
    0x172503410117003001d841c0c01d0708000b4030701c00010004000c104411013056804038660003581c3c0a061a000c07540b40159645804894400005000c3d5100c3d5a044000495514480050724050544842624607580343c090900341042c20601c1250000003054500b40324080c500b011741c1d103501256601d05070056a8050103482c280c1004680110403002c000d018003e039485802c08100a4000e9400914a018010482204900040307207400740c4a404018400000505415030800c00202c0d0328401c00c040c1c2d01c4046507070b030380c0400f88100e41042701c010350010003204800e918136205000500300030070542485070f41c000110b01403000b210011070b4001c001c80d1f507595081c0070350b68004a0517a40300c20140350074025890038240003015042c0180010850285a0110351080862a01640d200ca0506c0c4e180c0300036540c0c603007011103201810419101a18400d0701180310030f6800d45000c1c3d0b040a406844004e403070044407403400e9401d008110203031365001c01801107007140b140078042c0103c13801c5100028513031401c000 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 528950728 1250 528949478 528949489
    0x8071a091207020609041d0d1d030f0307111909020301140f0a0e0c1e180307060813020409020301090b010302031002070b06091e0c030106120603020d0605040809040204090506 77
    0x403003001c0c0c9151400d00c4041e006940d80000c41e203880308140c801060b10801c2094910306d0121003091000755002d000a810402c9901c49592101c8884140c1e240030030f0034000c000c0c1605c4030500ca44800312500100a440702040d42111841911480a440410580000302040040c0d1000d0f40001421940000040040c2c1919280c2460400c40840c3c01000140c18400010500002880340040130b01c0a0000205007603458030680e125040502e04c0060010f0300e0341628821030b07000481c1440c0342072805490740344a040005030502901d84a4480281546481080758030f2503042c0141207034030603180d60302e0f000141c50178000d0b0f0521031310a21402803654107620405040501414241d070100d44181700a4001c91708080360743c0d401000a42d1509103075207034580d0005035200d01c52810703042c915403501445102c484c600001c41c1203400366502d03107440001c0c3e00c1c802011740704944006075100480783c0c4600c0100f221a4002608980314850300c5181400140119050f40c00561091100a0b40c5000300501b90406 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 528951978 1250 528950728 528950743
    0x15012a083114040b130e010204051c0209100303052d120a06051e010518060316080c0f19030b0411071a091203040c03060617010f110a0c08071a09 64
    0x440f418000355148501150300f010954200c450300a40728910024804000e604075009008040c145818aa0406a040340d045025140c00c0303002343c1c000d03000a0030b0304441c441e44030f0a8a41c1550760506e0941a00801c1120640b0110340e4500c900d041c48a0b02c09010200009000300510608003000a18180c8940c0c8100c60a6500c658010071804a0803030b0740c0c003052071108100c4802401c100351903207c0341c00e45190f81075110007515045840001881f44a5904550820002c0c0c1c0030f644036803c0c0c0d079904040656600410000340c2d42c00ea001e2000c1e0400d0804824034025401c0d4525001400c5507111002a050b41c0b166552120210310000300b900c1480720303400007103040403c2040d40c80d00c1810030704c1441e81da6182c00e12901e6900c6074040042800c00a526103200d00840d008181401601d03203800c11302210210300e1003c1c00880d072900d14103580990b0140600d032166041c035036100d4146400247e040c7c55901405404980040d010005070000444c00403461900300440c904080652801100091a0068 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 528953228 1250 528951978 528952019
    0x10110c0109030c0b0708091201050f090307080712050d05010b04140301091208060a1d0f0a0c0c080306031f0219050c120d0b03010515012a0831 63
    0xc1c025050020030003180481c0b044070b03260700d0791541e5020141808081350103465030b81580500110203800411005400a50154041d095500d078151198100f950703980c414180f005017a44010b01070340b000b0507200c02030242c602050742042c5141034100590002114401d80190f5541c040100b000d0000e8401c000e448142c41c801540200301062954440000c940e008414080800c04c00d88009000703622840c0d0000001e2248503010400000012a90400d900b0f048440203410004040011410390b240d000301481030346a9151070540c0709442c1ca400f503055100400d40d540503c10504428442201141c00220110b19104010f03111016100c41400100c00440c0703036030800609201000c8a10008500c0c0541d140b403001e52995141d401d401c10402414101c44440d42c0740d4079010411900444c10005203251420907a104400e15001f0010142c02c943d00c0603400341e001070381c4080c02c400100c1c0c1400806e21803003111104003642e0349041d8100c4a21682c030f040c900800c0c410540c10015400303440310700360b0fa0740c1 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 528954478 1250 528953228 528953237
    0x1f020606190308030a0605031e0105131a060f060424050c120901020106090f02072a061103120711060c0301060516021f030212010902031506031510110c01 68
    0x80c1d4140c070101c01040140806001400c0000c0482d240001d00c0e44601c0081001509403034619007030140d5020100c036111000d000ca5400c200006406119001c520080154401c42200140c9042c030b8481c800e04000502454010b40781304526000c0c0d96900c0c000d80000c0294140c9003202818017a4500d890035034620160051041c1440501000758010448840c00950346a81c0d640303820a12004134090b003150b921210f41c1c1d40c030b0001e101e140403005400a00e8414080e114400c03211241480181c1c803640c2c005090001e40d84d0440003405494401c1d205202e44a501c6011071341801074404900c0c6c101002582e103003011031410040800f8050f024401241d109811700401c03821036141c01c5000d01140b0502100008400000036520115601c0b03221032a41c490740c6842144604004403000f400030b5000c140070043c200742d00c900025902459008032445040303404000d603842680c0710f05001d4550405400446031901540380c0c14829150b4041640f46040c00e60f861440800b4030031549400d00380c0320034000e810003 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 528955728 1250 528954478 528954499
    0x201110f060402091f180c231608181504030b040308130c0902090f0405090a03050c031c05070801051009051e0306040f0501050c1305100306051f020606 67
    0xa14042080c0b98032640507649409145c1d0350281d00003c01c46200b050b20310018081da00414403405012080240d42d6002c8010804e64024400c165404c0281881408100301381c0202d6501c0d80000c84064008594240401d425180281e600c2c050150002201003803204d908842003025490529001c3d05500e500e030760b0852400c1d09507258114203810040028080c440d5000c00f140c1c05000032034504000c550040145681c982d101c440c11000b941c852520184181d00d210490441807500c0d200e00c500400462004141c610016902a1b60a40101303440e04e005001c280282001d01000e8101070b95081d034650400240f600d0120b101800c90074042e0819402a00010f23004648160400501d0741900d008030f9012000b03407400c4404000d0400324100d0f96806001d500180420032111308454803140d48a00002c2c8050798481a00c000c542c0161a6085000c1c201c140c0300700080d050071503080d082280685008a51030b51035102058011041c0d000d080208040f103825458540e9042c050150030040482d04064030 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 528956834 1106 528955728 528955753
    0xf12050f010e1605030604181b031b05030307030305062706090a0b090112030e0a030f020f060301060f08090f070e010e160c080d060f0b07020111 64
    0x1042034001180c001030940340350b82c3d80302c0700ca42d49050450342c459081102500d9805402000c0881854036000461509584442d82c1c0907000a6011914610315140035003081c1070000510a0072141018406990080708481041c0d805142c041115290b2400142c42d40035440c0403400011a1020b8280340019284078041c8151021510854150f03580c200c3e0034285c49210a68a51040b544001442600d451a520582c03850192a000895401e000e0100d440820250003e59a10310348a0110046281208140018100a5502034159407510340d010f440399854a00300414045c034000003601701c10003084404008542c204c215503041e59168007580740d4560a000d001540a440c40c001aa0301060561a48120a00d61340c4d0b00130480c1551156030094211094510710175450305400144075490098400240809101003503440415100142900c04078014641c1340340c22901c9c08060 = true := by decide +kernel

theorem cover : BRFrame.Cov 528776978 528956834 := by
  have h0 := BRFrame.cov_init 528776978
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528776978 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528776978 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528776978 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528776978 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528776978 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528776978 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528776978 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528776978 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528776978 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528776978 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528776978 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528776978 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528776978 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528776978 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528776978 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528776978 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528776978 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528776978 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528776978 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528776978 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528776978 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528776978 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528776978 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528776978 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528776978 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528776978 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528776978 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528776978 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528776978 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528776978 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528776978 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528776978 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528776978 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528776978 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528776978 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528776978 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528776978 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528776978 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528776978 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528776978 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528776978 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528776978 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528776978 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528776978 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528776978 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528776978 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528776978 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528776978 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528776978 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528776978 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528776978 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528776978 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528776978 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528776978 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528776978 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528776978 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528776978 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528776978 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528776978 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528776978 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528776978 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528776978 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528776978 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528776978 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528776978 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528776978 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528776978 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528776978 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528776978 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528776978 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528776978 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528776978 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528776978 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528776978 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528776978 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528776978 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528776978 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528776978 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528776978 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528776978 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528776978 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528776978 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528776978 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528776978 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528776978 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528776978 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528776978 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528776978 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528776978 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528776978 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528776978 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528776978 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528776978 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528776978 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528776978 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528776978 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528776978 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528776978 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528776978 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528776978 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528776978 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528776978 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528776978 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528776978 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528776978 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528776978 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528776978 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528776978 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528776978 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528776978 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528776978 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528776978 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528776978 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528776978 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528776978 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528776978 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528776978 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528776978 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528776978 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528776978 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528776978 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528776978 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528776978 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528776978 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528776978 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528776978 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528776978 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528776978 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528776978 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528776978 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528776978 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528776978 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528776978 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528776978 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528776978 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528776978 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528776978 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528776978 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528776978 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528776978 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528776978 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528776978 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528776978 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528776978 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 528776978 ≤ n) (h2 : n < 528956834) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
