-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3190
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:56:10.544991+00:00
-- url     : https://prove2.me/submissions/57774f51-755d-443d-89c2-e92245b3e5ed

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 573561151 ≤ n < 573741007 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 573562401 1250 573561151 573561169
    0x80c03041101200c28050d0501060503150a110901050a08040c080d1206090b09061002010905070306060e070305072c030a06050f0a020703050f18150c07090b030a02 72
    0x10b05000300452081c18010411000d81070b140c01a90150040c0d5010ba010480d807421040c40305c500d1001d4500c1050a0051300d62074034412a4030450340380101d50024500140985003544c00107615008078800d41c40f41d507440802c0548034250900c0104107462955501185078060030504078000f54003402200c05040c0100c6507560058024403010300703030350307600c2c0e01061801c0c00c0040c2903000240d1142e802c010b603c000d40640405004036420034040010780001003907201100415031f62045040203a081d4002c2d000398130131507555030018242c560039500c90925070b002c1c0c041440f589002c44003500c00204c800c2d02c60301c5024003c100d10396503000c408201d600c00c0c00445a455010300a415180c45030208959406c200d0940340501c620300229140c82c000503040c88407000106241806e5004201480000364860119045480705086c05038071541c41c0c00708180d40318600c4c2700140d0030a9241108070304c0188200c0c040d040245050044510064680310203500380d07166202c4450f00350303110203a408018640f20b520 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 573563651 1250 573562401 573562433
    0x4030201121410081509120a1103040b19080613020322111206090601050904060608010207051b0d111c1203050403030b01140d0e03090a0305060108060106080c0304 72
    0x102146200c2411500303165948240e4100c0015161844104038030344c003c0c071004a0401d48014001418500602c5550300d4444898905000346000030f000e080c00c40c040c01c140d0121b1000902201d80322078445405440c0307540524030496150a022071201e1280d0721031102244940e80151001c9034904c1408456000707500080d10080b0300c00000400c00000c2c0324010028000140185684840110b102c0f05204c80705900c03034032400c00e0750440e000f001b0200400045950441c0e000391500812035031182005401020141c00142035540000f83d8441403100000d500c44008604292080f02202c83c1030402c0280c84204000400810070140018141e1511484c4000606551010b581c0d0220042d0380345501140c00050f05000710b80e468081c0018541d04d8420001505800e01740f5501c901c40740040c0d1021ba016021000503419240d06000882c18800e00580d80d00440240003468100d40f02d01c0c0898844600340992103151141d03400028145208003443e502402942d13050500d10349130f5845041c2c480a004c06 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 573564901 1250 573563651 573563687
    0x18050405030d05060a15050417010b0303070b0601030b040e06070801230409021c08120a09030c141615120c050f070f0b10050f0906030d0c05100e150702030a0504030201 74
    0x100002e14686c51072035814122a5560307041d0b81c890038542070640307445180d0351202d00350b03143c82c0760001c180e01c0000c112600103410030342c000c1559455500490141500184841c0c00ca814440440101100014883d010b65120f49403000161380320104142c000792a0701c070300e010f41c9a82010300803841c1041e038051220f00d8000340487c00700e5940b01485215070700d600e40c42191120780004003c10044c1102c3c502940084106400780111030107501c0043c903207022070001034403044048000b4584020204000c0d00b107003196000c282c0d0500c0d9276903015800700f116104900701143d074000c15903034001c0840c45005850f001c5512001d080628403152551140c000d0071044a95a24a0707541e0000b24132181c40b80341c0310391308161900507150f081505100b209008014002d00402c600703401e02009590118452440c0312003454401c402c444141003081c03070102d07161034000c2c100e4030f4004070764024500818550800f22072180d450a260300c801c00b0480c0d90b44214082c110000d0001c0c4801d100561041a1150070240d00c40 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 573566151 1250 573564901 573564919
    0x121b080115111e1203010602030304030e13051504150b0313080c0106081b0103090b1612050a0603020f01090b030f060a1e18020c030d0b120a03020718050405030d0506 73
    0x200d03006107002401c6140700c0020f1412407071620b591004100b01c0c100104032010080c190751400303c0127550b03404090801410700c030b269200d01c0302a0710b441081c2a07816211000510090600c0d20b200380960800c5508180114180324100f80b4000720b543d80c40007196030440303c051840d0303142036100207000305200702254425810006210f040100340540409042d50002504071541c001100c0c24404100440443c10705003003800304004a10a40031042d44a03118042c9080b4103490703400212848070896210000039850602440004103c0e64050000e803071094407900c0c2c1c80d1380c151006542c101c00c503120b0f900b4404000c00005164908070f03040039400c03200141c9024038940d00c541c0c01c182621040e90795071002003460b103c108481c0d03500b0020394a00784621b4400314a000955181203460348103010070b110615441d9900c1c5c03121a00d6a660030131080d46003200703540700021240b0b4001d4032003115100354481c162100c1d2002c59004820712802d405254420010341c9040b0040c5280005403600a1905500c1032002c = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 573567401 1250 573566151 573566177
    0xb1203043c0e01050907030605030606040e011b0302190206042f06030415110315010302161b06110c06071101020a02040609020c0f070609051519121b080115 69
    0x2015403000038159040780d040b107039030401c818080756400c000c19800405007020b608000c036407004140660044000c0c0c4020400b0010f01c1e5a5502500700d41c503070825401c4009030880031a962680c05052809407149130421060160034003280d8508003540c025000f06400b4105072000c90000707903d6007c5211004c100c100c10b0a074000000c0b042c0e0800c54083e600c2c031980c88041c0311120445c3c880c4140c40c4032a17030002415820035100b20504072807094410743c18180e0000b00d0185070340c8140c0104e4401640301e0104460102468805d5250008074403e590128847c200400422400400c1034204a41c0242490341014902e0700c1d0400700c020382c61030090542c081c82d11031300090f85450043c6070162031041c030050394848110101c0c0c1c1c034002504441c0107240d08100b40600071140e1244400b41201e400b103039200c0c044001d02900c005284180c01d40c40d0f014211011510f00702d203030001e03100d0521100c082001c000141804501a031102901f402c03110010320f0000050000d400700c0c01441680251924000c04100c2d5a = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 573568651 1250 573567401 573567509
    0xb040b130506160b06010c080d020705011512031b08070204050c09041a01020c030703020a090b060d0204090b040638210105150406050d090f050604060b120304 70
    0x200c0000c4821002c610000c40c014084c44002c5150020001c2c86e02d001c2400080d15101458080c1591401c47d042e0005030600a2120940028a1007004034041e810120380e59100b02c0400341c0c005408402142c1c0840705042c0c1e204044800b00d04154201c03014034540074540c0d080000400006041d260134507402d1003001116165841044103414070004d410044a2038000068900b03404000094402d40c0143c8003440143c07a143c8004084803103486012131010310200004005004441b4a08000c610200700001c4115140c4c002080d80c140a0307408110460f156040c03d014045050b1500c081075122071510880722591140d02e240c1400d0342d0740b00605200c040901d204d002c41c00384502c5021001c40200602c81c030725020119010440090941c68542440d10202030518010140c00f60034280d51007540800388000340840340b444a500c001503460915003031512500800c0d244011902541c00d54412601c403d00000c02c0318145c035000000d00b07920701c001a189004502507004440c4004180200c280307201c0320 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 573569901 1250 573568651 573568657
    0xa12050d09031107050d05030d02030709031b140a080a1101030b061c06050102010e07030303110f270a05010909091112060103050d0302090d02100311030106030903021005010b040b130506 82
    0x1209958114030f21140708800d5250469030b41000e8415240d8900300800070b8000000c4900c0b180b0100001b41e101e0341d503000152480c5000342d0001c4e107803140115440d101c50401740303250001d5640d40c014000340c0080304010310031849218020300400b82d1004480300080340b82040065050b003014940860340301074107000b00305d56800180c0007400302501740341d00c000034014900481015140a1008010200205440d2540e44076240300c09001c3c1541c1e40100d00250610504403000103284010446e614652414000e0342c0c0040903000d4003400b04000f000041500d480001d18007254070507502c801180c3e003400c0d8548003c000c081012101c0121803082c0040b03940340d0042d01100c0c440560090940c0d90301d107042003400c0c028000d030898200f52040002d001c103039484040230101c55030180c0311101c842ca03075004280c000780107620700301c9a0300c04003000000361154103820803078070188039030b09841040d801c0710119000c0c3d030005c4c007a1f045403a805000074000000310380050050080540740c0103010b240c0d10000b00d00103038 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 573571151 1250 573569901 573569903
    0x30606131e08120f03011a21240a060e040608010603050a05061b0403290108010509070b0c03190504090f0617030315090601030e0609030c0d110a12050d09 68
    0x4603074481040b114070148034211960002ea440140740140029030b0b400c1d1440140242e0031325102c90345454100340c12100641d16095103022a2070401e142d05000601702ca1021200340349108140c21034844c0032004070240307403004c0c20003401520009081400035074105001103140c0d034200c1da44050010b003d9209016080056005070050700c0c0b100e00c1402c003203092000042a08030520105d07004501a8180d1508480840341c220000007144d540e0004c07a0300c0022503d003107817000c240d00000081084081036000c1030041926004680c0c4440c0d4850502c05507014000083c891500288aa5a07644c901c5504080006040703140403403402e9100e14051044880700742030032a000e81e50703240500c210340c42003800d5500e4100e400011411450f05140304041c80e9242a49103014103146008158140d0180c0c01040903c00102c0071b9400e1450044003c1c2e0b605e030060007401045114044541c0b5070030f4007030203098040128840c00350604082d5502c07841817030320300704148034204441000203c80000d8a1301ca030141903 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 573572401 1250 573571151 573571199
    0xb03011401121115070b060105071a070f0e0105070209090c0d031d01030921180914060109050315070c171c0227042a020f01050103030503060613 64
    0x9400d8a0801c05000a903c044040c011180880c0411801800d8000c1c0d0740841c1e400301c1e001c1410780d240001260103002c1c80c003009003d1041d4800a440b810300e110704a074400ca4030307542d42d41c082d040ba100003120704109485c0c40c940801c00c100301f04000760502c0d504440d48841e10804469550588002040c4607540c041d00030340028600b420680312066000b0903c8038502024a02444200a25114526481040c000c011906800501d050762098003501711190860340e2242a000e00b640d860381e260002d014464840c1c105a031a14000607029802166002c040d83c00c081c00500b00ca07400d2000141c808030000d00440705100c41510b1302d000041801030a102c00c0317101841055100e44250150300c0404040c074080241d0540144480405880c0b0a41e45000c02c480d004100209206104d0104006100740350a0503440da9843c2c031483c600055401141c0320002a40c0c1c00c803644121042516804c9607801c1c040100011b0301080856000d01d0070384090001056402c440f400c1e02961001809055070050b6036202c14 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 573573651 1250 573572401 573572429
    0x21c0308090f070f0905070905060406030221100e0c0c06040c050f091b1308070b03190905030301051005120124020105060d03030c0c06050f040209091c030b03011401 73
    0x7485600384842500307101890014006581040b50316040d03007400b0301405140b141c1c2c900c00140d07418071509a8200400c00a0a003540c2c594440100402a5001d0700c003407a00360350413490304441801400f07540d81c0306040d00c611410745130741400398805c1c01000140040d200c0031818020b00c55180d800b8024a40a94031135452150200d01e00400d12512407281841c17a031086180d08100580c0b00e0b41c00e22a00103000c0d980385140e658403a0900400c0c2126680d421001040c0728144010407000b49000c010341c0181040f2242000703038480c20b620042a0784606800500c56002400100001d080c0341a000d14100792a0071302d00d0400c180b0084000069000340c0c00224203400802c1400354590b131107100180b110340c0a02c020300162074480003244154409500040402d0b40e910703070b822000741c03048004030300d06035001c0010300c0f142c00e0581c081030131400207441c180d206000200c0840c15845001900b90122512101c0401c0c18006031a4280d0040c50103480300d64041d503c1c0c0050b090714881010915020340001d21203440 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 573574901 1250 573573651 573573661
    0x307060e06010f050904050a0b0907030609300203070201050306130e210403021f03021b010b031507120e190b15040506010903080c160b090108090706090b07021c0308 73
    0x110703e41da032109002d10460018400428000b09042003081d41040c0740410302e84880c41d07814505081c907840503103411300d85030072041004007a07001306207150550182c00c070040340400c0e103030450180d00008140c0564403c02030f00380194000c201031540504001c1c1607824007030b9030035421402d5440300d000d1500c843e00700c1441c0529454601008454100400c01410304090840d8041483c941640c0c403c031203d042c898101c1410140300c0d404850340f2840594102c40c10441708480c141c0a00907400ca40d030301c80d00860683e0204c551403298114416013003035666101c4034441101c03e0008104107032440190b4000d250f032003080e41d40e42c0310700b13071680521501d540c0c8090302e00400c1a4045000c2030540300c2c1b2481c00c2c6800c1c01300b180e902042c0503090380d41000d4440d9480d0b64441905151030942d618003001144240d0000900c5001000070f441f9070740c1c0131b0701d840c00c1940d01e8284281d00c070041c40c0541c0e004200205018490300d003400018002841c4060122070298418481411b1400241c4400301c0c0061481c2003044 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 573576151 1250 573574901 573574919
    0x4110a03020903062203081f060207080c01051201150e0303040f0512010902010c0308090307020d08031801050108031b0c15041e0e04020d02010e0a0f09140c04050607050307060e0601 80
    0x1540c000c2c0300485550040440105c1e17018408049100501000603c0020541c1440415090341d144080300b0140c0c40380300d5550001a40b148194419400d40307000303840c0149000d50250013103402c0070b20080050354040c0e08004c400440e29410400d417200b005510070120740c850728204000c00c0642881d25500c10120701d468200051aa1010740c0605642d0400d400100140d8200d00e40000065040c01d0100650b0740c0c054005103107026003030010794800d111140b90402c2c481000020342c000d034164400c640c65400707030ba0300c3c1500380c0c0c201b8810200c01e607000b00620158070f00c00c4031a10170f02e113030a40e0542d5001045480000d90780750301d5041a01c0500b01c001010000390809050019aa9400c41c45541c840d91a1502070440c17004000c20183c06030030a8018401103a00c6080c080c2c40d106002441d40d0325040e2030f03581c030803540e0846d030041c0c0c440b0382e01d4030010842004110100718443c0700c1c0407215501e040d041c0b805004050b00010380c11981c6200034070180340058103038094203880307034491001040d1035890071001b8 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 573577401 1250 573576151 573576163
    0x140604111e0c0115051e0111070603090b0c030405060c0f04081b010f0c0c1809020301020a0c0c081203060d1e06020904050a111b030405130f1a010f080604110a03020903 74
    0xc4c90b100c13240c0d910100400d40f1212540b829041c500c0c5120742c03202901200580d070904501d03c1c0040f1034000c1e508003080c8603425a12034114507014031100ca60903919902200c60a11054502809503403120001031a51005100207002c1100200300d100e080550b10f4500b0703403a194080c030a005000203a06000d90b420359010045508042551030b282d030100c0c0e990340f181072680200380150820618201d4000c02a01e03800c0d0080700320190301400071952030b40700c9800104034030411401241d86280b0351400045003000000d500e2610468060300764519120305041099161604e90200c0d000d03a80c01c800b038041c4001982006044501440000d640c03445d0903c10030040b41c20003810100c2d070503c0e0000103401e8840140680d800501589001d5004190b4109150b14600441d40800d40c4a41c01d09084103410302960490b00c0191407100050104994811072480380c03c4903c0c21050019221a42e0461190700c158001034104070007070400155035460341c5564a99074403084000d40030075000210005282406c00c51 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 573578651 1250 573577401 573577421
    0xc020f04060303080c0c070b040b2101060203220812030703150e010b1c181104022113121116050a05132408060a140604111e0c01 57
    0x800c01c4400c0c20b5580141100e00041c1440410b00c20104d140d03031400c0410400b55000d41214040785440b1070f5103045105480d80010140c0404480b55203100d40c104c883e10020506803069030b00994105140c06907450510311160b54480c0030b8030049140015880401c1c001001490651101140d0fa4902010040d080c0d41da20178402041401c241020011503180810407410b40e9101d4004654460708e44d01407811f0000f4507408014a00e00d0211500d400e203180d20b0548191510403416014203d0764a02040300301d009001508044c45943c4208101c0304020402c25640040b240614400c14003c03521107010f902481040324021800c0303014040c214102c00c01101d45100030541949102a0901c0081203860a480c03066a001d0300c007103241052085520382001040040c649203150b41040e000b80010110200c605c030b01c0203a40114000304940c0103440c09030090b182103519503004143c8914040c44000d00514080881c0e503d0248881d4203007900d4600360800a40036100762544503000303010a1f608403281000 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 573579901 1250 573578651 573578659
    0x3060e0703121704030f0c05060c04051c08040303030e030c0d024b030f0309010b01080906070e0d020d120801030c0623090102210711010e0f040b0f0d030c020f 70
    0x44900c800d00306801a40358813541c9481c0c29445505118030940e24005a020001c16601130201008805500b110240c41155000c6590760070310a0101c03c4110441c02612010380110400c101c1840401e002c1d400000c101041802140e00d00942e40340a1410301240c0e400e40c80050300f2178410b4034000741c001c860419000c20607c0d200c0b0407090230321050800705050302800c0e6011071a1154060311035541441a99413940d0000b0301c05580b0310301440618001d180c0210503a010680c0100458a070310000182d4034850000c585035640501007000402070540f510756012079220b25854104030008010b108003000c00c2003543c8032040b80e5411864040f00700c0d1256003100040003d41c0c04800d0605140202808040c02c4004400c4c3d81c0301510b20040b810000700c400002956035518501d00b04503080d402c010b12105026806200015000c00011144429540c21090348080200e9101c030b0580703002d174000242c040703008282c00c0460f0240408203112003900300c4143c010070142c0040d5015030822010401c0410310440b = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 573581151 1250 573579901 573579917
    0xa0c110a0c1a03090d1827060603112704060b031b0a0e130e031204061b0e271e09013b1203151503061903060e070312 52
    0x7411140d03070b011064900780400603c6ca9034101264003520408011b81035041040601191003802c402010b20b958660702e010510707101000500a203e8490040e4445402821505d02070200c0d085000c031006804070440d2111200c03040c00303850750383c80c45420010003111500315103d15015111010680403140120700400c410010028520792140e01e20540e1401103500d941100400799445008140020042c01c9500c0002900416140c540460a105511400e8244444e100f03098451b0102070a5080c29008600401da405142f0f00e0115842502280c140d20065500111035522480d0101c081d40c000010044d00e919840c1c0707034942440110303131061564009204540c04001030108007881d09400340440c590520a044c00c1e424031000024084000504803150007522008602440d4026203c0e400300562503802500142032a46610409480c10340401d801c664840080c013010900301c54009520b5161004040f00162041c40f58001041b4020018003006045191001d40061006504424090b1003 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 573582401 1250 573581151 573581161
    0x106200c0409050102090d050c0a090606050403060c02190311120301030c05060a09091e0513030c080d060f0306020409050c2d0d0507030b030706090e0a0c110a0c1a03 73
    0x9503030625100980d0002120406400c1490082c000c0c5901ca551104118605001344040000c0701d8803c3c550880314807052540c1ca81c035400c00c4405030712541c00400c000b0b010400104500d0b80c841c0e4000c000c01c1c01603070807415102d507180d050020901011000700700d4001d1072100b0705104105429901407074282103451541152034180340440c0c01c0c41007074400c21001451a400501c1485a64000c7c20b180c00c007804228220503440560400c89482c14400e20700c0c00e0000740e03000e01c0a001203542650991600c0f80c4401c226200c2c410564026164108495100c0d030000800c00140c0025000840c0107010058903582000480380680d178024161000604051045040c928109005d40101d9121040340c070040c004001d10401a500030070404c80030840c548410009200d406400103d80e02008605681d07a803601c81c5002c0e03c1d040320900400d210310561000180010800747c0c000302260700309040c00c0100414007240249400311103c0304440d500425030302080007021070000e001c09d000005801900710701d00 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 573583651 1250 573582401 573582403
    0xe06040f12020726030c030409020309060c072301110a0c0b0601020105010513051009020d020c01050124180e010f09060b1804020d1103070e0f04060f0308030a150e010620 75
    0x4c1040d811001c085030904c04240c20340c1c10802c41e20b00c01e4130001501d40301c0d503403541200000d4108440034101030158600007840202d02a0440c1c0d0070a0b03010b4a04800e82100d4070b20361048121800081c0c00305c0d0b40e180721101868400d80040c0c01c90321100d56401404030040c0c940005460000760081b415a07041030014029940d4400b0740001d00c5140da04001041e681d03080c402d404104a0343e200300e01c01031000a241c56a14003940040200c0d2a4403c02405075903a54046440c0420001030502202000c01c21407804061040c1c0c20782c4210403400c9115504580c030fa0414030090700080c1d01411449a03a00410800007100c0e001c0c040c010080200a941051841c1c070450036040d0700740c080d041c804c82e070008030300301265203550007990107100b04260f4640304d18140c2400341c102400c460a043c0b250b00b8003000d803011450280511801c2c0d03519124003040c00b901d0365460041704d4102405a100454542044040708010101c681009040030200c929255140c41030160411100300880034140d100c0304052240b80c00c0c = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 573584901 1250 573583651 573583679
    0x60b0d09031b0308070c0c05040c03240501090506090a0b1207090f030302060c031306061514130b03060d0b090109020109090c080c0c010f05090c040b030a050d0c060e06040f120207 79
    0xc01810101e149039094035011f402907500383c0040d40c0c01450304140e0f01016074950300130712290500c0000c03416416485205140303202d41070710075140000c824030014403150406201170405c1f240007414113209075844802110480d00084218000045e280003040031990b44241c0c14002020f68444580800f0f0031074038004c1d1030320001080d10190440c000f02141c014612400c411b46c4030340d00300307604021550b04d61a041416130301860100c0700141401c1100c00203080b01c038003251b00b400112f5009403c51858088941c48ca5040146119484549240c20402048210309074501c5035549000000d03807602e6030320000d0800d50b0241c218074020703450310701040c2c242500000101d82090218038951b407208a10340038640580055118802110306180038490a00c1000820b0710344041d080b6014000c120380c010a040d0740300c052250191990b400030442a103d1030081e802c0c0311003940070f6003000c601c10600908180c5007031810b4400b16640700100d1001420b00004001d0010f204c45288060503025103895076a0000c08 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 573586151 1250 573584901 573584911
    0x8090a060903090e0901050a05180c0f03151306270222020f09042f03150d030c0201270e0c0409050903040f050a0f06050d060b0d09031b0308 62
    0x1956408001c01418000c0842c5030081101211108403850715402c214041e000c142c4094080c1806c0901040340360008a668058000c00c90f0010031540c0710410420051000c00840d01f9011b02a00103510912841c0e2101980305440d001b0034008001414640712040b191130941e122a03100301c07500c095280501906404042c41c0d01100c0c50250010040e141000c219101e0480d0301c40984000b43c01040f0400d42130241c03218245c11a400c106100481843c4000700c1c0c511441d020020f001c22000342d404010316405150171000803040c80c0041c920403000720307250001565007503020650942882e411903a1080754840720400c007809004600d50851a07a08555545000d054001600080091071211088090314003c19004a0a024074101412103903125800382c0940700e1034411201c008945802c007440c20303800311000f0403100d1030703110b00d450300498940d0481d01c2c04050260312040e00041004401f4003030903040600a01c0010304001c1da2801520f040c01d101c3c005501c0d409030324164408240c11060181d804 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 573587401 1250 573586151 573586163
    0x2d0910090b03090d0305010e070804080a0504030206040e0108010b0a0806340819110901030e010b1e0f03010608060a02090105040f06120501080610060e030307050105010b070203010c08090a 83
    0x1004000000380e5000103660041082a031000c8104221800c0000d076041c0c03000010348080169981341c40c0700502c4c1440c200d90401c0414400e0020800107202c0d60020624030401f803820904107a1641c0c0040c1c11940a070b0300c2850701418100050110400078464200c0454045a01184892519207410b849040c02008c212031604030860b1103490f45098135030105200c0b20000214080310300c00e400a4280c11051b038290448580e100c2c03102d00480c241d486048100700351041b40600b441c501400440150040600354686952115183c44054484400d00041d00000c0d1141d6000700462406101c01c2c400600ca54a10aa041c48020408440045207003500500070700001350b070f6101d4241c0140c0d118407581c1d00108501a03c2c030f50002c2d03081d900c40c0c5c1c13610041000390414407c90b60f075426015aa00300a03107400d0801c250301c5608104803070280310545c3d043d060180c10b0724140f01e2191103040c02c4490980c0b041030250300c00901c41d0110b1400b8420945145a00e0030003015034200102015542ca00c42c090042413 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 573588651 1250 573587401 573587419
    0x318010806061c0204060906020f030421052b0912020415151707080f0613060902041202030c0904050a060504081308011a0102010b01050f030a140c2d09 67
    0x1c640c8600c412a02c080d407141e06010034140340f200046009602c03c1c8035050000b02c407904080782d064404607203142d0b520b403660001c50419050048105004045101c1000075814088004000036070612102101040d4048640f1222150300402050080145a10340070000c6400c014492960b80391000400c15405131030000300320410b2040c1d4144900c0580041d00000c08002014007a158018000b00310b4241071000d0603c1a00c402c0740039078080d0001d5940301052210f00c2c0010b00c0178106030618943d820101440400d50940d40c0200c00201d030b1054100803121300c0191300c0401541410440c3c0030b20354000b5526900a49059201d40340c5400441d9002440203407114007040c00e1111030030070b45100003400104584d54603642d12a89000700031174217407207220b84400510102158010301c1065084807068480301c1c0707401c0251044d0010303030380000d09005c3d080d5965140345424488550070f00740700e1050000ca0319603550354085002c1c64540e4600c2c40c42020380d000c610343d21090351400240d0b0711030b01059460080d = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 573589901 1250 573588651 573588661
    0x60c0f181c08030405190f0b040510150f0e1012050c0312030a0b04060f060509030a140c12030a0504030326070e18060319170708040f0803180108 64
    0x85a0a418920074595410110031040c0450340c2c00841c0201e108400301c03540710300003400b40040d090b2503200c00b9040070300d00c0c0d2026010600743d0b16410307031241c40b4005031140c400d801d0100700b08461003460440301c0c003640300c0d400344002c00c5825012000f03426214000c0e410707407a01c200d0f0480c1d03003c2940103024804d1030488004007003010030000601c24090081c03d071400d0311740041070041d50f50000c913a41d0500c182407691060306070920740319050a89280300c921071001802c0c24010b580d581d0120200e1074040c03151400c002c011034070805020000183c540c0241c10480074100406c0f0f4a640c411180b40450340080102c01c0000d07410408540c11264035080c100d114441c07001d58107a065042c05480040c0c50004010402d9003903000719040b40380c4d0070440c0c0080c0c203800758020004407034400f1103136a074242e4010410044801404e075201e1142520413400241400c1c20038101640d02c0d000150102c4007a140420300b030240c00c2880050b800035243d014000c60074083c441501011188481844606010040c40070907 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 573591151 1250 573589901 573589909
    0xa0611030901110a0818041803020d05090607020402030a0204170316110d0803090d0311040b0405040f020910020d0305011a0901030f1508030405030f0d080a050a060e18060c0f18 78
    0x511003074004610365280c0048071b0a80104c004001c08881c4a98a0314007000e00810305032121100094150340200302c072200051060720503a10040302c682d4050b105000b40001a074a034002144904003d070300c0541c583e4074007144903010808550b40b00030700e41c10a209020310480344040140d901a04943c0341c140640107840441e0141294090180084070004200203a1050009260201507080d5804204110b000104441c030b03405640a48183c8200411040100c2c0c60140c001005407508507800510300354070b140024244001c0050481d0140e049042c8a50b5095058400c40d4018101d000f02c0e0364031242d981120300c01900c90300105505141d9103c9106407102645d9112030131842040c001400030380d449900c41aa82d4000d071144a2081c424000d400034400350108504884c4070403078460410a450f1a1400ca0240000628540c00d40d5580c080c00540e01b003024042c40c0c01866200c01c0120f8900c00364034040d05000d0010f103966140001088541c2c2c1d02e0044808480310075800102604501804100003 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 573592401 1250 573591151 573591163
    0x27060d060306090210020102040f05152110050901060503070c0f0605011403010f0c1b0f062a02010c050a27030605160306080c04020d150e01050a061103090111 70
    0x281256031400340d01004214080e0711003450b1a0007160180c814070700d0004101d00342d1065009501c081c0034203e908018505084200c82500c04142c3c003010706203002035081c00c1d4403810130400207040d00d00c01c0040c04642211880c41070040c4c130b400d6401118a6040400180030b91201401030020408401c280b032083c090b80400305039074281d001c4410700455a4a1756008025218000d2080c441d502c3e00c3c01401c0207126510604082034459100e01c000700b03054515103e00111071a105030b40d4101080103140010b5184c1c0f0541030b0fa940300134500c44052102820038000d80030b01c56081b00a580c900001c00205981000c29240000700e50701c0c080c80c242c411102a060b04030461980c82e0140107400c440441040501d400c2140300f1a80d0362400c284a0052078412004e6405605c1074172450b8000101e0284a03051980080c004103d0020011501e0100d81032200c00b00130300c0e41d00c004410f03100c2e440140305502d4803c02510040c4040e2400024981c0e48800c4585c4034401d0050807130520050303e103002c100c18024010303 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 573593651 1250 573592401 573592417
    0x501170c070212010618020705060c0a021f09170c0a14070b040306020a17100b0a17040f1106121302010e1f02010c0507030503070f05040801060803120601052706 71
    0x9044003400f1410b00241c00b03030a5a00445101032541c500c10400b45a491094808040d00640100302585079401d890401c0d510040c0b1540440c09081c92038001c030101062251419200c0030000615601c0c58140030100140c46032010011520411526411020003d0b113021503580180061015242c21103078146007141a84c0706203245a800301d000418400c1d10b80c003410b10100f040d2514a0340315505e06541c141c4040c21184505070755034080d8280014540303a03028201d00c46042c24400c3c000f5450b8031510810200c100e900b11180c07070b02d2a410310108840003a032100940c206039581802c191f09480c14912101c4028a0856500244207003481503a115805210302c1070409420286900c00c240d4503045030340b46003402c501c00b560801c1e1010601d144500304880240c0c0d01aa81c460440c0c0303c011080380c9940004040c502002401e01c000f02d1091400e10401000b848090b0013140d840d0030041009502000041c1450b05104062003252608105042d01e8111703650b1590030909080360040000d03280b0b02404070 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 573594901 1250 573593651 573593659
    0x1a1c060503010e10200d11132405040b071403220e0108071208070c1a0703030f0c170a0603081c050a09080a0f110a050c0108010f0501170c0702 63
    0x820341007038800b0929513044181d000f0103010344030082c1d01e490401d00720303e070b100030806070b04004c0d1100040b52548030b401114180c40640f460030381d00c0101302c40ca40700700d038101c1d122680882d10f0020300c07010b60b40e0800b008400c075030402600700b43c6009802030a038020301e040541280941d02c50714100040c00d20403500b035504c841008950180240309100035210044c01441d5003a580e1a00101d40c005000440404132070700400c0401201d000c0b643d030360040c0d8008903c01c403580400c8003400300c4d030540ca01b9400c250f42d00c0030960868460010303090042c241c034412180c402d601440c1000c940d08080c4e115151a00343d154000c64205151503202002e0001c019590020b0000d01c0081140d02c0d43c00417500c1503820312540c0b4a4280206c1d222030200408640721064000e0100104004100b0f503a4020b2210220300700190034a05441525900c0413030404943e0030f01124550403081d203400301c960300603400501611301074008000307150400001810307036140d82c003038402d2a05504002178000d12808044524041d07000d0 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 573596151 1250 573594901 573594911
    0x2060c07080102040627031509020a08011a150316020f010501090204030c142d0d080301050a060804080a030b0607081207021b0315070c02061809011a1c06050301 71
    0x1e01e000350054002c0f040000c1c0c0052400040540640c001c514480d900ca01001d0840e03c0c42c4d4a00e0f40040d04840800080c607224203860025130751b82d0702841d00801c035000c00822a2441414403292a141203001144644d111107410424070301140c00341c4c0c0d40306180300c0100810924200060746042c8441d582c001c1d4642c00d0400205403880d00d90003400c00c5920403540012040e850782040140300034000b0006030040c0d62402c05902400c0310304201c0302c0a070b072603040f084400a42580400d6420f092183e080d680040001300410503810092000001401c140c641000c0300e0610b0f9484511174810803002000705070320b0341c02c6d03080c031542d40000702d6401c03940c880151a40c1e01e00101940a01302003c6411802600520f5004030582800b0282d4503104000200600103031802c0c00900410401c000c0e0a0784108000404511b0042e21800d0040c4400c140885003070444040c042c0c1080340c1038074140c120207500e584414000c10018218030641c0c1c9060700040b00d885e4000c0165551400501d295404954958248 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 573597401 1250 573596151 573596159
    0x21100302100908070e06100c0c05100306050a0b090303070f0203010b1f090905150402130e130611120601080414030d060e0c040b2a010f0509010b0a2102060c07 70
    0x309641c0c0d02183d43c103606032400180c0d184486031a0442c00c039141c03904205500c00410b10b0a2080305840b01c110302c41d00c8402c2580352140081001140c000c1c1da4030020a503110018001441c1071240c40c002026805440e5140117590301c0070903168007481078010310300c901c1d081041c021950203411115802801070440210900300440c012010f800100c9400d021810614010910782e169009942c4145a5504e08294000c10281070200940c000c0e006011903040e00c3c01c0108400120108480c09006001d0303000040282c41c0c28880d0403540000002d80c9100e03806c0049000d001c44200403c0e43c80023003400c00e81c00690f101c1c100b40483e620300443c14805400700164414580141c0d0b444507050300d071011120007056503840b00d03000f041e01c01c1303018546420310140102c90885456406d0400d0009120005c00c3e801c03a054103400d42903c00d1307240400704a075150010080e24031400d00c21520030350070403070341096000e190808858000b003401200e104c0c0e90400910b0003081d510740070101e4000f50440d0003252880c44d62 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 573598651 1250 573597401 573597407
    0x40c030903030e0705010504151103030103080a0f020d0905040c1205040302100c020708100209401a0f0d0b10060f1403060f040b0607030818032110030210 68
    0x100c0011004640350075501c8107100e5002400b0002da40060319071a25180c00c0140803c2070856207070f01d01081200d1040b8000d5510014400365000354030442e00680c0750139401e4800b818012080840100310f40c003680c0745a03552039001c2c0750a021550705607000211400ca0100c01c0310803100407141d001581d400c150501040550010b000318101060305820408003030061350498032038440d4070881004c4c1e0301c03080c0700381c100800c69401086e10070310007000d15000c0100b02c0040c1184500414010340d6082c052510498480d4804e203c0528040c0224000c01041c040703158807900c4804d402500700d000d29903188411419490320340c2403015503a0444c0404426140500528240c0c103610300035007000aa0b03204843c0d441e40d0107202d2002c0c0340043c9083d140e00f59070f6000700388010068042c510343c1c0d01c20386400d07030100c103030300d0300c43c001c15080740a5564003c2a01d491032200e03542e40090b040c110f450b81d10070050b82c24070b900c5015807200d411804c0080501c841d202d01c1440d400110031900701950003c0e2030b03c50340e422550 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 573599901 1250 573598651 573598661
    0x7080c0702060903250b040303080411011b050604060f020a120e0c0a030f0507120b220c090b0109141c0c090507020a06050f24011808030d060911040611010902040c03 73
    0x3840307905c1010700c648540e01d1406900403484020042600702021400140610f2900848100185480c180709030340e085064210291451069859412500c144421f02542d809a02401740101c0d40c19403411603d22030081c20521700c11400d42c0f06956952283c4211a01030000310701c2c0460007844c041e242d544170704204e122101540c00455542c81040d02c0005d80121031642c0d5101183c0004140007242c0c2c03282465506501c000e00c0442002011040060008040ea90701101a140c01040002c001407d0310026025034050340211400c10700806002103550354a2001c4038140b0348071003003012000d03058078000790042e400350002d10f407032030402d0200900700782c4c00558202121700a0800f1321040d101d000e04446518010307241400b1500075003450490300d80f0103500e900741d44803040c0742026002401d2800262a181c00d500844065040040c0403841e68655000d600041d11440f8402c01202c1d440c2101c2d08194841c5108101c14403030711883d807c3e4208420b5109040c1160041c100744000c3c018483d000f00100 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 573601151 1250 573599901 573599953
    0x804300201020409230c07080f031003060b1807200d0309200d0201050a0e030106030c06090504020c070e0709091424090a050a0b030f06040c08030307080c0702060903 73
    0x40e10740790315440041202c1c8100e0701c5c5070b0031091802c411901c0d00d845c80781c142d6000f50020f4816100401c098102d440e02c11300103602c03803100107186610850440c0b815400351200900e80c1803103100b56461400500b0140411590011040c1c1880850803800d000201030312046d0705411145409501e2045010036010740005884601c903004040360407020b080160840900c00800e603400544001c20b030001540681d004204800e10b0703042200102410200103400d450a0b5001180e402c450008104102604040c5043c06084100c07030540c201007030140da1642c0c4840b0761103102c940704215404030f001c00d40945801409004281814420300f1285034841c130a040050307980d04920529180d207005089114000906030788401450702d10350382c03034040c200c2e0003801001c0e0080800b15510b1111500319602008900c3c503080302c0002800c0c0620709414082c5400d50580e100a8154004100b089880c50748244803540c040c00950846807951028004182c082c041d050891750180b0624101182e510700c1450144100e07 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 573602401 1250 573601151 573601169
    0xb15030708010608131101090b1b1e06060405061f0e1509010e0405040606080a050705041a181b12060a06020c010c03110a0203070605071509020108043002010204 71
    0x2c0e660b40030103d0700b41c1d904803100c1040f00040f0500c680064520f00711410060014900a80301940f65104070300564450100c101c0d41e0003081c110b28862001c10310000c406070590b050002407041d5140442525840000c100c80d101d10b644000064042d51144000340c10204000c60340034504404c043e026144034040100c01e441400f0b80d080c1c0c5818003000904807082081d0680d2070592601c00a01400040c000160040314200c7d128030002c01d204c10200301c2c21b140540903800400c19145807000348130880d0603842d5403503045184500300301425122501260500f01e605051700540d5540c00f0091041e40c94a008000300038040002c00c0c0d40e100000a0145014440495907100c403181c0e554000d0340c0e142c03c000d080e02c0c00b08040002d02030100b805aa0742411a84412007540c00e030b540a0743c00241003200682100d07007c100c0c08544501031080c0e440402c002d448404004101840341030300064044040180002e180104a00c203802410b00e0701c600102c140040d0b80d82110182d40b8100000e0f010350468003405d139003 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 573603651 1250 573602401 573602417
    0xa0506040b1509011230090302040b04020408120a02101407020d0201091707170301060302041a1315020a050a081c18061104120c0306180203100507030b150307 70
    0x9a280c140f2a0604840404001d152005c03e2965109400c51600325002c09030040141c5050030740001544855101000c0e9940c0720f40c80c0e045104000c1150380c04217030a4000d500c1848144000100050750010064504219503222560310000724940400e2400002900342040d6030310f02540702044086004c0d0805409076a8640d4924104a0072541000800307058514000400c80c9a009144000c000320b40c00b840d40b180101810040580c61907100b0303800440040c0d4005400c00c44070f90480c004000c0346002a080c03d01d0700300842c040c0d0200724100d02441c806000c241040c09544c1d0300030845814070f540e1100075586058038a003081045500308900c40040301c2910040d5884c0321025100342d5800010b04940041642003c0d1502c400401205040d910b180004200108170501582e00d6803100c0791162100c0742d03043c0e0441c5032460a450a02200301c3c1080d064440741c800595000c0b800c9134000000000004282d078039050304501400707118100c1604690303401043c000740400c15009620a108035128015 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 573604901 1250 573603651 573603691
    0x1818050403091d07080606070218060301060614030c090a0e1320090c090a03052a0105030c030f0604110a0503061c1a04080904060605070b0106020c0a0909050a0506040b 74
    0x2007040602c00003081900d184500084c0c4007801038506641140c4040c10300c40c1003c809a0110340c6840c1141d0304d04445100d0001005294a000d000c2d60003d00620b02d03054a400810380562070f803600000d00500030020000c244003000e034551500003002415450136000f403e04041e4400305012034420000e0300c40400d402c018040d02184804030900c4550054480c4225a0320a1594842d6420408906510171003002001001c0b030402c1150304100e07030190b4800e050070004004003241001d5101e0569042c02820f104101c040b41e07001090fa94000581c0010a105a403650001002840b0385d0b89845400c072400700b14602266400320140d40700e0361040d06d18401c0c400c1c4100ea800e90203402900003c242d203405981d928410440244281c0d041440340200605004904000a040da80540c000500203100807a08800348040700c501c05005000d140007a18494103048086131031103907a809249001600d4080c00780c00c0290070840c02059036007100c10352f4081c1c141858510901c19081c0c5840080084180b101c0c8 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 573606151 1250 573604901 573604919
    0x50105060a05030a0b0d050d02060a1a010c02030724030e0f061618061e0f09050607050c041d120f0d0e0f1c030e06010305030406181805040309 63
    0x14162400102440e0601d9a5028129140d50009003e19201c0351900c801080325158032403c15044e40c4110050034940094020080c81d1000040c0241001410326402d0f60250b07014645042c0341c01c90a20740010912054000300386401055400408007980c01c03001d0803160f0900e02c0805103401003030707070f82445281540315075284d40f404034100a00c0107400100c00310ba01c03100c80781d041e44030100d41e90038140b1004802135050a001c44080d88200041615619103162a8074a030703294402d00005801c11901c81241404028511421401500d011b04800039040b4280242040300907017050300280309100c606010941550300c1000100202500d00ca0a6103102d105030a10302a01c0d01c1060b0603803200e082c0f007200040c0c40c000e4a071141141d65075014007002012886814800e8010b40310114449200c0000d207007c1c001c0403240400c900400c207420640040c00001d1000c0103d5003201c52518081d950f0000c00002581501c0c010360103030301c805803c0b40085d00c200a160300b11700d10603802510f9400c0c40300e0386e88003c1c03 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 573607401 1250 573606151 573606161
    0x60a0c11130e011109151b07090606030b09070c030f3b031c0c0809030f0c031603050c040509030f030403090e07031e05180f01090c150c260f030613 65
    0x1750b441103100c1610642120303108064403c031040d000094040b004000790ba1410824107400075002a516900148000b94060040ca02c0d1400240e840019900c2c00c0d40300107000303600e055801000c00010741401803600703209003105007c0349111702c500807503e080390400304004007001c0030b05035900044a40e80340061801050b170b0480b480070840820750007a965801101d000c2034a8408580128041c4004031140d00c081100000d0b01d4845e03801400030011500405103015820180c1085903091841c0900000d400410f41d00001c4c4425a000300b000e440c1c480245040d4000c40f0b0550391045404010081415030141040089a892024035100b0f42c5072100301320b050752818485e00e13408034014054802c11802550001d0b500c92074860f00c41029507807a2032018140207540000c0803080c1c3d11000b0386014030440002040051010b1420341c0c4518551100c0030703154004800e8047c2104411000799852969a150400d1120300707040f12180d6a16144098030003a500241c62031130040e2010109200155524820 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 573608651 1250 573607401 573607417
    0xd0c03230f010b0705070b0d020f04080a060b0307140409020307031a04030327020d0203010e0304060518030102120f13050a060c02010e0a081606020906040906060f0e060a0c11130e0111 81
    0x58810a400e0152907c8158400b0512843d030300c0d8204054240e400c10305000c1d00c0070f0f1800c84094005400182001c8055401c00e40125119802000701004200f0003844480d01e9410203541c08100c3d41c1f03980c00003e050205645c006080081d62074100c503100e6030001d035441e10942c46030b1000c00c4020301e5046007010301000190241c421100071201c1d40c0141c607140c00c924181074401000410255000e5074018199005a80040003040c00421000411070301c01c00254106801a4000c600301846014001c1c20b0280c05054502d40100e028045010240d81d401c0c3d10442d80c1d0042e0848100300224034101006084c40c14100006500e41502011214404030b8980d03926038015910a003070000d0700c403c1c003a01024903071040352119401c101c5220325440b0400604002e00c0c080301c0002d152072500754040d014020340001141005882c01e201c40e02580c400098034004007281c506000644e1440c039241d0240d5403d400c00390360107080d100c01c048880c520b079000f8900d16500000280840c4000501d011082c0c010005 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 573609901 1250 573608651 573608653
    0x807090501200d021606031104141203070819030b1005030919060213051c120507050105040c030215070c2d030b010602060c0306060d0c03230f010b0705 67
    0x40420440d0b201c1d0164902d14942040070140c12100c40c01c000d86022802e2243c400541c1000d020300d500440000101d00040c103181c14284005025241184164400d50140d01a8407880000d01503c580311449104810f10002c01140d5944103603003023102e581c1d0060b00380d0745844c242500140040602c00c0c0911652040c000c0c00e81e8404070700b80321054070140c000601c0ba1481d4400d030f503800c2c06032102e030b102c18860607070051340e00590742e681610180c2c00c6140c041c0c000714050500c030302030711001404c018a001c0800340c01021007202103200400c12989807051040c06130803903081506000902034802c1c814001c40e032080b03070040b0182c4070841d14400d46004280001d005181c08140400a0714805400b030841c2c0a07049007a0040b440d055400100e125400f07030410f44403030f21070400510104d07404205247c2c0102ca0700543c5070440c0741c000e002441600c10b61080340301c59a101e000320182d00f40a50080858111400c04640c140804082140c1246038215405410701040c10000250004504100c45d21980c200d8 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 573611151 1250 573609901 573609917
    0xf10060516020613030b090f0d0f0e010203160b33010305060d05070e011404050c161505090307051b01090302010c05101e0c0906022d03030408030105100807 69
    0x4402100481c410341c90aa03040901001103440b8040c18903003110180d0710500c0e030301c00e0390305000060500d81030400c1401503459002007210006650441c1d039940d64802c4070728141843e41030710320040741140680c1c08840000150122441c0400890907541441600944547c44944242045031000340c080b09240961441b501d114614995100f60041036000c00043e00109400b4020703500c452600e1303000e50101c0c888203042d02c01444248041e20114501800440341030100341458183d0901c544a0354080c034040134410590350081101c88003800d0b584102c0800200034a00d448091251240d000b0b90045446000e90740f8201084152060038064030b41040e5503416216003198019501d040d0341c00400e4560344031f840750f41244034450703004031401c060400c0743ca40f00c65000340c44c3c030400b0307941810b08003418021240720500846900003883c494401c095003604003411080e038200c44002c0280c00500307040340000401c001c1400030250055048400941d40340c0310040300e092080360060825981000041c150b8 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 573612401 1250 573611151 573611167
    0x60515070804030507030f1a070f03020d1b1d04060311040509030f0d0c2604200310060303230301060804110904030905010f02120d020307050903030307080f100605 72
    0x8500500600c5105400540c6090340720b0300c80030f10b018001c1e0710072200400c0c0071140204101c414000d0034a0022210746040c02c0d800e10010150109103000030100030140d008c28030010070174190300314100c41261825941003014501c000141055865546205a0030040b55136213900d080c40d210307071070860360420002c1050b2001882044040c0c02d02809550365817000703010001c925100c6a0050003d249030b210300060000e040800508031080d00d40e0304503107206980c2805070201100e00b03a02503010f0b600c1101c040e0a00005808100d051102ca62005c0d0940314002040c1210300c1d860780a042528060380703545200b6118500c2402c0603008104080c1400d00040c401041014011110765400520611884160024980c04681c0400c002c0300c003640080e50441d000c11540d60808030110740d00d00c003440900202095250b10305620310078440800800303030340000044d4100303100e1020b03034000440007019203540e4100201c0013406802c0540f08040703400308041c00700c0c4292610f1080c10080314165101c86081245c0 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 573613651 1250 573612401 573612439
    0x3310111c03150b0c060117060601030905070b070c031703010506070611070b0a0506090c03130f050c06040806090615010c060207030c060c05040816030b010b0f0c060f070e040605 78
    0x19480e09441890384844030550194490b5000c440a4020400300b503881c1e84540407102d18009040e44042c2541d0303100c84000724518004242c2c660303c48820708011500c02d81902d0f0542c030b07000d120381c0700700c56484010035847e040010f00031400040f6030040c0b440003015401c03001a055107100a116969002104111400029840360410f03820101424010740c2030210548444c0e641c007a00721032201c0815039030b4007000203d15040201a0304801d143d01c00f0390841c5414a102401d00c900c4880c0a081c030001c00a81f0f03400c008041281c0d041103480a0100c41e11a6503500015a44120030703954891f890090100252000d03025420203081c201e416560109081a99154400290b01c40641034041142c01c08104001c2030103801042407014065441c1e503551342c41c2c07581c3c0904003141490000b0b1102c80c0b00c401000880c2c5800b0b26a41580d135080303a1183e2319181200000700074803070b01c0a003101c0c5008141c10810114118001c69100312180e1b01c0f44078034141d0640420045414a010711580301e0080c02100841c40341c = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 573614901 1250 573613651 573613693
    0x905100806130e06040624060e0f13090f0203120c0d030e010e070f0603061208091c0f0b16180603021303140d1806090e331011 56
    0x8003044005241e540c400f01a504008003244c003038900d6921109480840c440d90a40390a014a64095840710642400350080600441969851148503416140c5140781d07507450408207191011003081142c0205450036119918030b40400341d205c1e01500310074002c5032000d80c00702d682a00c65200a400606065a800c2e00100700000741c3c1500c0f5135071034048040707544040003d80007620590788552641c61500d50001d094a40700d4021310192006411418002003401c000e030ba81140c411141040030690710744181c000c4c00120f01c000780140c42403d032504244184401618000c0c0c640032600c116801d0004000d58000302a803050305803007007912030100f140520946c01342049a0322291260505956034880504401d8460001c40403070700501c0f00600550f030802c03901a0311b003040707603222258030385032103806440540c0b20f102d52800c090410000652122502ea4a21150307280c01d2001c400480e00ca000307a0398800090507101d8020500c0340c0d0207a481a002c0c003c00005981100020030200e6240c2662030a045 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 573616151 1250 573614901 573614929
    0xf0b0d110d0c0e0906012303120d140a09021003090320030d061d07020d020d0c0804050603040302030a030506120c190306020325030c0813020a03080301060c02010905100806 76
    0x642640d102003000300d100d800700e03405451048005c000c154100240c406d42c103501d0220100700c0450004003c8000d890100700220078034102d1400e40e4540001d0b903160380141c0340c10080324011f001810f04200702c0c0c84903580981445402500d44071000303200000182c00f1142e2500d400740104441c1c640c4c0b03802c109a14000d01e0759640d943c0007580c0c14801090082c10981d0fa25401440500c1003000915814a418801c456031001c020b1008001d4841c0201c00691036668020b400d004100e089140601801030b010103da009060140a103039aa181508000f5102d0300714031078410000342000c02003445440c00e40e003004101e070b200074046c00c4c01410700e40810031000300035042d18a000c0042e00d00040490040e00c05144105451b4540210450f207045107984100541005c0c501414078002000c0d90326648008402d5020300c03400400403903034041d800040c2003443c01e944000c200c8600000041505035000490301c509520030f0700c40120031034550081140386141d40c0744c1400050301e0100060010725082c1c040403460 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 573617401 1250 573616151 573616163
    0x31104050904081602041505041109060703050a0207080a12020c040902030c010f021005040b01150c0302070e070c0506072339060c070311010b0306060f0f090a0f0b0d110d 75
    0x4c8941c41e0f000c0380c140c940c1c4415031400c18603108410051414140181c1036041e01d13203521070f0701c0e103c1402c0010780c140c0a14100582041800b20790182c1c028001c110040281c0395035011110f800800c0d1410f1003210880155000041c000d004c5840803604050080007007c0d5402400b0344054034207403004459588032a4080ca0441c8611800449411040d1044600440c090306a8003600d6051203881184508405d008108100545e2054000300341c2c04900c038415204044401e180c1034685510881d604840c030f803005802030192100340005c898004151000c1030881ea001320520380b00c900e8000c0028084c0032030300100c3e105840c211140e05c0ca204043c103040c0d04540740d0b80c2c00d000a02c403104d0b03c1c81e0400c1100c01111340744c8000356520034140c1151013240300d1042e01000303108881854001c243c0310140944814040d0300c0304910700c043c903943c02e45041c0640c103014116089a24201e0040c0e001f802c24200d0321401103162002c562010f00b4424400e02c3c4064100300301a840f1003070107060210084007100c0c02c0d520 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 573618651 1250 573617401 573617437
    0x19030c021e011d0a030e10260906010b0a021b2202030108150915040302120a03090218040b01030f0807080406020d030e01180b150d1203110405090408 66
    0x5410103003042004007880c0000012080410300b0045040d160070104207410354400400342000940c01465160086029580703000410040c010546800a06031055403502c2c07048401e100310b001c545126541300300c20105c1150b10903640c2d544250b81502c10f00d0081c10050b0098441d0039680303030800031250301400018040f005a03008050418022403141d4880c40441070300000104000707002000b00003d1504030592017559420311002a90340e81691903000041200307598005028540240f01d590607920100c1559650768005140082c010304803460101c0c4903100131713920400c04590380608a0b200d958071122249140e400e5031200b209100d00100e00300e0f99541d080108500003803080c8054802082d0380d8005000038103140d0405000d55804160302007035030307140c803040e40d000d50f14a03000c0c0c0481c26040003144990741c40c1c0325a802284280300c030302c0d240c0101c5000855810411401e071132115440003941c08000d0340c0910740211800d07204901c94a540303d01400007080201d840d850042181c0e4292441c0226 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 573619901 1250 573618651 573618673
    0x20307171b0304030303062304051b0a020705120d02190606031e03111b10020705090106181a030601030f200408070501110a03110f03070c0f05010519030c02 69
    0x20300040703103010510068101040810426400d8042c81c0c020303002d0101d2002c1c1e42c0c07491104070042402c44028607441661144003190030140b52030190401c4000354108142d0350350b0154806956241c0500c1050300440032a0314200c200c080100b00f83d01500c0c035503400b500c84094403600b00440607070171501c00d5660740e036103000000014044140c2e1074942c1082003c010388650150401070140d020750018203a064208502c50300c071404d402030001240b40b004442e181e50303880c140038049107488181d4100580145040001150141c0c0002048014045602c03880c0d084c540c446c0b801150321101c002c109041d22034203002240c2035601a8000c0e80c0361681e041e01c0060700d03541c18215a00262454090203081c3d2030b0014050019100074171400010b4030f001c0c07c010103011000000544c2e81e1856a80290800c507440340c03d03500c846001c0c0110200c205007042229120395940c1010580c80113144a040c3d0120000314001455501a000f640c54905000c1c1c440107454403502d50950280c40750010901c1180102c00000f1 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 573621151 1250 573619901 573619927
    0xb15032e12051606080708130b0a0f021b01050124081b0c0d20010608120904020403050307052d150a0219030e0607030b060715090f08032502030717 65
    0xc4020045641c0381005c0c0c0c1800480a490700c1c03c0034020b01000140160707064081a1028051508409400c40015283d000e051840000f8002d40e84585480d542400d00711400d1401500014141c5608160401c1188044030304034502c048650642ea005c100d0740400614098036500f0044175203030740f88610a20f084070f8018101d0404011004000c08101400d84110b040c8450400c540005040c0c60001c000c5d1a0600300f03429030f01c6260341400010044002051301468072181c050310015a440300c1281e48030701c102d14020b62102346456a80e0360300290201440c1d00490501000180000fa2030041c00d0315400c4048200c0401000424940750706408000c0145000310103080e0f261010406d580c00107911a24200241c18808060103150425051540003c065601c000c1144d07049a8008059200c406d00c2a499101400c400100604160008a803001c14080001c000b54410b4401858540660441c00030b15490481c0d1510803800681c414048040064090b80c5051030f94000c0c0e10740c43c2c0c10b000c1001508 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 573622401 1250 573621151 573621193
    0x309151814030d0f0905060f0106020717010b101d09060d02060c0c1903020406090b0a05063006030105100e130f02030a0c061e0c020f040b15032e1205 66
    0x822960798820f505018001b040c0042034105030702c0081b111441d494104000c0d6100001d000703282d8480210f84040961030002d40c0a0030910001600c08030304014002400ba290b0b401200d101000ea80d00050340842c45e2030b040c410f05101e20300040c03851514414030380900c2020381012801400fa4441d07130f4200c24240e6610366031240102d07507803d0740c0c602d0039081d44103000c02e03100594029200b4504260400031255115900e201c16500291446a19854070b00341607580003803600011024590f024154071141d100d07004045205000640c0280b0558440300b003240542d0600c1d11850303103c40901004508a4051420100c403141e01a6900c2140d2000300c2d00020b0034500c03081011162144841c0c000c2041c542c201c40b00000340f000500340446403224540d4058a4003120040082c41420481004001039680303500c601c041c1c006c040d000600110031020a60701c2c40d80142c0d100b4000103120184240500c507100003801c40015400035518440e031402c89106001d800c0e1401c221114021a80d41c04140c1440001c9 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 573623651 1250 573622401 573622421
    0xb04090501050613140c0a090f0b03060f030c0306271212010f030308060103150b0c010606030b040c050f090609030d090306050f07021e010608030a0309151814030d 72
    0x1510304003c000c0040315125010615640c9003444104002883c40c40081d6611450704812140d592040d00070881d44500c20340c100071102044007601040c1d185a03040070350300c84d40c400c3d26036030b615000200415503500e051a0f4680e0b41640248000781e040d4841c5030901040b020540c3c400201840c1050f445424034241051240044801040400000b034007a8200c60050001403071180c18181503803401803c0b040d001b0025414980c5402d200a0307240d08424403003000b441c41104044e2140c582519060103480d82d41306190000e0b050010300616480e00d440703980600740340c40e20345a01e82030003055003d01e203810010506030310401c10300080c407440c0c800380207088035044943c0d58070010318154a00001202d501814140113040030b6002c1108407900046c02e40c01d00c10240d01c83c04120101d04400030b003d402d23030707801c4007100d800701181c500e44554154100e801c00b0f0788180b11a1003110000e10506040b03450484070340c44034019921038a00854100310014904800480550345442c200d104100d0503241c0c1481 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 573624901 1250 573623651 573623653
    0x10e13060617180a1e06060b12221e0206031003140a0206250c061d0f06091207030813151110150806162006040b04060b040905 56
    0xc07190482c0b45180360b019400380e01c1841e180b1180c141800400d07500c00104400406141d4041400c59003150640e10105407907500c50300a0101c00d03214040c1c07242d01d4000d101015010210400800c1c0d40c0da171010140342551520700c0010008215030317103887c8074942204030140d40d8034078844103a00150b02c0d0740c1d0045100d1400428000c001a240d1300d000360300400004c0c00e1303184036000001000d0059503040201d4141c036090404281c078003482c0d5440841c251104038801060140404030000d0055000400490f2141500004080c1c00c08a1010b1010000c005840d49610002c100401141858900103058882020b0402c880340c40b80c490380d401d070b076a1b80045406075010504001c10003c1994524100d0108070300340c6062882c00319071501041d076600e0307403540390414a515501800c4801c00c0244010303000384035200841d070b11424664200c0301c0e403622141c5100b00080803995032000004800e1030030802a1400801081d1a64442d00c5603080e8400c0030f00200d89898542c0c02d00f5400d03507284e019110f6410b000310 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 573626151 1250 573624901 573624917
    0x30b0a05010329010e0a0b0904051006050414070807140406090f1e09201215030304080a0305031009020d0e060711071401020a051005151e010e130606 66
    0x1040c002143c0350310b0002c6a551804821403039014441405001d41101d00b00c1000c910702e501c5e0300000340054440311058039000310000e030400060110010700d5181260046a040041540714030500050701c3c81c0c40c803000c019000318800b06540e94171036120164001584e14159400e01c0c6190303850741e04c60380709600c00b50000382100424032080c0380e0a0600001001c118030307480015650b40d41d1646080c51148a81d890040da154500c044640345188c803185000402c8001681d900c00d0420701038141513040d81c990114040034558194103040000c202c80c2038404d07900c010041c1110396582180c055000811140e290481e00100051090303542c000380400c29071088001c941404441c1c111450034030002c00c0e0f03008100c14100c04500a013004211081a902030b21211380320301d20b0f9200180d103455514103000b00a842411403404010486501c9103000d08131040d01044518000030400518000002a041c02d4200c421040c41d2950f000d04501e04000001500303e64407a46034080103401c40d515903002a0110b9920 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 573627401 1250 573626151 573626153
    0x30507030b01082413030e102705090a0209180a24060e09100f120b090a03051801090305030414090c1602010c03050904050a0e1504021c020a030b0a050103 68
    0x6000c0904c200513581d01c0303011610000280c2010108000d8900e03140100006041e105040c41620b450b0a6890094074101e003000e00224010400c000d81c441c8840c07920001e00d4001d0803589120a46030460f4002042d039403180d207031101040c001707601c1001c1d2283d1241414040307196260410a00510802055000083e0318155400700780e000c0310b6814100030796034120b05090003001c0d000607080c98006d406950421480d03480c00810b004420050b00f03c0341d4460348588002807210042c01085680034401d000c4059141c6501c081d0566070301c41020b00030049101030020440100041c0100f41c84c0c20300c1490083d48142e5030791509400e551090b040360005c40c00c250410a07141c2014450903030801819a8118944540c004087d54902081c8000a0401c4103c16080003490311031015911442e400800c100454108030451800401100241254500492200b001015282094a445281c0241c0032620390000014600c01e4111403240490380100003031808070205000225251252820b010001255411 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 573628651 1250 573627401 573627403
    0x6030c1c0b1201110d090303020c0a050a03120603080d02030705120f151c060203250c150b09041e050105160215070203190c06050a060e06061206120304030507030b0108 74
    0x1ca4400c050b580c1498081802e060003001118241003106000090741425031500324084d00c60581080814881d0541c4041400390116100c05102e10948400702c1d086280c042940c159803140c800031b4011403081c441800c0b0f1010301d40045a2012a0746480303403a0003031240c1303608400c0c08182c40c180c2d0020f4125040140c05000284a140c4021040320210084040c4403042460f001030741900400c100e8011010640000521030200d668480c183e80b410000c801e0844024400a8450b03c155007000e150302607030b83c20f0f000c0d911420030042806000040c003540c603501c40060b002070000c200e490f90f40411000754045002803180e580204818440b2902c500746030800285048100c010101c0100418010f110519400104448408426540c14003d807550b0f0601a9070b000310402000d003405082804000d42d01029902840c03d0721010451012103031610418421035006046104403200380050106011385084c15082c0c1c03c000720102164905034807566124204011a40121070301003000c0014464004 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 573629901 1250 573628651 573628669
    0x30315030219210506043c060501060801050d02040903021e0319020312041b0e010905090106090e0a030309020f060a050406080c03060f0f01140a091a1806030c1c0b 72
    0x15050f00030a8065125480310394840401420007040c0c40b511742c815a601c100c0600c03440c041c6168100003000d2011070222414130b01c51010004441980c0b4000011a01d140039400c024140c4001611012060400742e003030200030040004287d00f503124074038151200c421014403108610305008003071502c034001c94241c20400006d601ca10700540d001481661115160005c44503841500800a0310031710307038100391440c45001150810310590001c07400105450300c06820079402010144001c206041d61840c2860480700012242e88460700080035010219110350441003085000500c0c91001c60103400004039290b106914150225601280410030780390002c01c9640d11800850b015403541c0340c6440000c000c1d0318040c030f81a20401c400480746020ba442840d44110040c0a00b91007030340c4080742d06000d0022282d0b403040d560410860000d005074200940c1c1075a00a043c0780c0780c1d42255940c603108014440d00300910003074803c04d0a100a0701c403415040c152001c81300d000781d00041d140c0e520728180b2013609 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 573631151 1250 573629901 573629939
    0x61509020405040b10052d0304111c030f0f020705030106030b0402100311040308030c07020d061e0207170304050a060908030a05010509070f050315150310170307030315030219 77
    0x41c07005e43c030040034a4000d021030b884000c0c0e55100d031002006007214585204d942020b803003401c602c08130030001000f003800095841007a040740d001804910210b0032480c84482c981000340080c0605034549640f034098020101940300c5401564845504c0b0070110f400c40382c00c0d5000f5110090502c086c0801d5003001c5410a040c440a440d040c80040c2403800b803040188102e00c00149001400030005203029078140603180c1c1e00b580100810042040ca003820009056255049003500d20301031b01c41d0390dc40b01e05200300d41da8907621448010410b2030440100086401c004c1003550140181c00009002800c140f05d800d948a10644060b41c8a0822944c25030480d24141c214a01840c0c008040c0404681c01c0044a44010140e290050b560340e29440448d040c88003207260076820140c80012902104d001c00003461040d0244030702c04a800d0798a0444500701c084034400081150410401030300803900c40d800107a560101406042191540c0741e000c00d0103451903103032140b803d002e652418441a5031a039010400b44e = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 573632401 1250 573631151 573631159
    0x80a051b0a060f0c020f040504140601140f0f010e060a0809120c1005041e08120f1608060301140a09030908070602030a0809120c160603110a050304061509020405040b 73
    0x1c0381c203101e03002d420005003025850030f000f007a00b40c1070708540d03500300011340c0604040e0051050b03041c149056480031414014940060040070000719207005818110400300308001d1145803952600428416805021894241001781c010001c2c0d0894403007600405010f0140c2da142c1c03c1619043d400e460601e0100c1854800c4281d0802c0007810700000010040c80051300c4c80800283c40c0c80e58034040310380700d40104d601c0482c800308030226014840b0190107400660740704610117201d03a45048440080f100304035005004d891072040300380e00d0503124498607039210704064000100f000c400d221b121400c01086844490503500c490901007007580c803060200090142c400148100c034180b0308069181e0180002041c00c0000c1d0328001070062408000420140c01080012035030303508440d4a094980c2c9142103110401d42c038202c40042c1783d52191041c0e20710a52130002d5142400c070141c00848190303001030820b464154a4404144140442800d440f000f07201d42e280c0180c0c0e03a0700c2d180c1408113544c0e07616049446 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 573633651 1250 573632401 573632419
    0x10306061e14010c140f060f040b1306180b09150118020f09040203070f110c060d0f021b071a03160c02060408070303090306050919020f010306080a051b 67
    0x8030700d026a949000d440015900d542c0c020107060040f980004e001d00c020b001440919880d421844000c940d000010305136030180d511990395040c502015280c10b40e0018554101440090041006480c41d005480c0c4900c5002c01d03554500d40d110706180c0e10075141581d40e100c940003441280030080046c046c184100d00c410000c150b160140c04110f030401c00035001c070300c02c0e00020011034a010300e0048079038440005200b1916030a248200402d40030601d0740780710100e901e84228000c402c1c000103064581501c0107240602c3c0c01044c5a90401600d00300340c02c0303a07010b034091001c00a0380c070640700000c82060700d6400503c050343c54a1065488440c4c01c0d21201d10b282c004000f440141c41c094210754030741100c1420b142103148900c0c4049102403183c1e51200d15140030790000403040543c8442003100700c03809640d06204a8503020215511002d003040300105151307d0942280040c01c1c41901400642014100050202d0340d9107042d6060010482003240c0c1c54100c02e00480c1d140d1b0104401c801c2c04241920000c41b = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 573634901 1250 573633651 573633689
    0x109020a111f02220b0327060f0903120108030904200403061805010e062203092904080307050c01080106051611030a05060402040c030501061413050d080a0207090203072f01021201030606 82
    0x52a52300140c11440d0782080d5a00140484104000711000c007103220054103483d40c0c1d1050071320b80700d0700070134241c6215a003080c410f04101d030412700c400f01b084081c0300600c074070b01407a40d59104001d10010403001e07585560112106c2c04030f2800c1c8a00010b05510101400c9580352a01a600c1e0041c480e0304c059101244400756400417950010300d81e0f0a941c030802c6d021054840120b5400142c040c0c4582c000c1900a0008010132075107130200141264901c640221980a0085030055824504c24000d83c0c0000340144101c00301138858401d8944058001c40b0500030b90381c5c000010a04210049034180d0381a800f030018001103061a12681000b540790b0b107404c22895040940c01450794001e207480c2d103002607001c0350040e40c402d243c48504000304801420140c00c07101d20b103800c4031540c20080c001009406048000140c3d1951030003100e21030490707591030141c00b2500381c11046c2c000b0580c1e1380480103150304110711001c01d00248010700540c1c4100e00480d4456246282c507200351641904802d5081e90701035500b078 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 573636151 1250 573634901 573634903
    0x1501182007021914010c150219090807030b070509040f0c020a0201090503161701020c07060c1b060e060a0203130605030f071403070c0501140109020a111f02220b0327 73
    0x914130180034078085000d00389a040c421520480e0300c2d80005220702c002220307030280c80d810004403042d400302d440f0402201e5031101d006444086600c00546181c00000004140500c141e0007000c10413001000002e4070130a428114086075020800f0030007607400b20460304d0075913800ca9940340080c170044008003e03c8007008544d450b5031090340b281407418607080c0c00c84c401b03030142901a86c6680d0300d408101c0d5402651590001c0020341034807403c0d502c1c18002503411052560315500c030710a59001c0d84400c52850800010300801e03038440f4201d20f0031408140180c101031140140c1400c0101601e40d0360a4032400e000a40195411024002e031007801000408555807410b8001900d91050b603504003e80c00041e6810304a02404040d000b0b0132142c0502d40000c01c80d140603a0160203c40503030350340e5014032000ea441c0190f0390140790070700741e604000c030072510400c22646030004d00480042c00c804003c0381c502000400b4030011946c0088014100200c10403580c00c0c4500041d021600300c15106020141b62541c1203 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 573637401 1250 573636151 573636179
    0x4060b070f081605120405040f090507031707140f010b0d0f030c060b210c01020c18040c0b07030908061b160809060c0601051215011820070219 63
    0x4080140104020322546460200140341640082c140c5c0d11245074580c40c945c556026004091203035140844a03005910180305000609501030000c0c84018216207179010013890b1155210400300b0200300080001c0d807542d00991902168000906001d81404400c0703082d51500f440141c01034803111442c60100e030701d00b082c0c82981e40e0103007001080040107081542c0034190000c0100d40009422864040b20301c10015501c0e1030301148130030f803040c268001c00120307117404064001c164040340052541c009100882c2c0c5031600184146202c040703881e030360030780241550004641a008640d030321a0401802000740300300d9510501c1842a2190301491084580c1c40b409010f0b01d18901d00c60481c02c040810140307070304544e030140f002044180c66010b9020050b0340d030402406100e02454807500040d10008000a0700c04a503213420551560907801e0407407501b2195004809003600d29140c0ca03281035848100ca281d200126000e00c0019550040c50040c403a081c0100f00061b60260b000c4101000002c04500c18 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 573638651 1250 573637401 573637403
    0x614010f0504140a030c03120e041e0f20030a231305010e0106090f060f06080402121c110c090c04122d03140703051605030c12040504060b070f 63
    0xe040303000161980401c0580440da040101b8020302d1380008818080800c980140b0b004d600d0769184401580d4205100c15640000d07510400c80060070140041d6407210303005280c00001010001072422000003900c0b5042e140d054214109100000c02d10401100c0c6019003611a14120865503410560703c2e030a1a0041c00207015150b040f00d41400781e800c000080d0840344414400400900a4607200c5001c60000c080720014000220324105000070078254030703062882120b0142d1141c642d5503540d40c0911581504041a201c1d1502450520b010301c814a01612180c0292568030300d2070b03c2010a0b5001e140c040c45096041c8502c0701001040141c03080802110245c0c1c1c20003100c0c40b010056841c010320304038205c0340341c1e850009403200b988072100f8402c4440103103a406a03840245015070301c1060b5a1501c030f103c0300a40001c0003040780071845002480740c60078482c4104100e0b450308150354071a07820242d101400603500300700080c04005604d0640642c1c0060144103510a1070605160b03949031800b140c1c0d4034 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 573639901 1250 573638651 573638669
    0x31305060f0c010606050a021506062d0408030a081312030e0c060f0a02060c1804050c091012060f06270f030b061c11090615040305010614010f0504 65
    0x14841c0d21061411007a242c580070700c80024007050b0746400001c3c15a400c1960031000522030045172170046046216050300808000e810280381c0183c041040c0160986070588007805c0101401d40d440821807800100700070312450713014548807811100000c0140402822151480743ea1031829008103442d840d414044010030301b4000340c00c5414075062030614400c14422a8821400f00311102c500d0744038802818a4050b643c2503941c3c0e655413a00004c41800340d160088220015065011890b003011b60001c0c3c2c00c403400078481401e01501400044c0708190110721a000606c0040031031019100c0d03030081c0e070068030740090841700d014107003170009241030200c0d21781440c01e0284210f00705584c41010284c4021f4502321001c16492030301d90a06502c807144c2690140d004985009203035440b0399030070503c00b9140340c0c0050240706080512003001160b01700070f4401c5374004503464190352600441001000258031410011490610701820040c0310980307815550306100c07003001c4d02009180d01104640584030000 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 573641151 1250 573639901 573639907
    0xe07080406140f07031e0c081828150203130c0801021801030b0d05070e090d020105060a0501082e060815061e0408060c0904050603010b0a060302090f090a05010303080903130506 78
    0x1c001e4405801244102d01021441c0800c0da00800362300a081d076129417825200c4000b4031540300015680c413410101d0184075850041070104602c070f0303640c54101ca80d5014414107030f00e004000640404a03071090f0380c000c18406000440c1e804020001030440c004010140007103007002a00c00f49801950003c1000e0340c105690740e01d0441003075030703141c06070403c40c1d41210842c0c1c1444d860b981e030b0340102c000544418a20b8400c49090400c09403050203a42e01c0350304003402c0c1908203450180195841e06001c0c01c0e1b0001d64440c90300d000e4011503954808054501a000c6070b0516929242d80604101c1c40540701d80c65010980741d18441640302c40c01101d01003528105615141c0d91030350041e00b00c6001e290000306050184000748600a4000c40143c1f203c2d01c012641001151102c0080608030307030700203001e0394003d41d00b500104a2a8002c1c0e015100301c00e406800f03804403481d1200001c1180c007084030b2010f01240e480005006040d400b16040b40e1000c107820045141003e4009040d09000300c80c42814800d001c00 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 573642401 1250 573641151 573641171
    0xc01140d110f0c010203090f07030c0303031d0d03061d061c05190b06090c03060a0608430c0503120a0b13050f09010204061209020a0e07080406140f0703 67
    0x241c00c655a08000a101c1911610554041400313540705070342c0ca15030344c850b1121100b40c00401050600889a10000e00c3c1d01081c9140c3d41a4040c0c0407160200729441c24890380c2c240c03000024807074146420300c5a6000078900342041031072000c9060419000d500710f012101000380d03a0b1641d12000584007180c01700750401d20031038945035152541042c50b90104458000000c401c000c0d28000083c0603080c2140c0c098142d5592090342c503042d02007111141e41c00006814100300e5540280074280d0083c203c1c03071541d00f40c880c003620006000c0801c00145101500040e1303c5201e44a10032000e100c0007505440e0200d581d56880d19030720f5a80c00f9034041000920f50003808a01c42c4542c60340030190004014048a0142052080c410700508044a0000c0009000c8002031100310381071085500b034a210380c8610001604400402004004c7ca10040f038001c20302c40030102d031380c0300c5410398079104402d15503600300945040d00c1c108042c2c03a1803601000011903540300344100e203540111810340c040000d2030b0015001c685 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 573643651 1250 573642401 573642431
    0x306040f05190c03060b0405130b0403020c18090606030111040303050a0201020909091614030a0609150905030417192006160203060c2d071506080c01140d 68
    0x2480048616900c4079440003c0110f0801110304583c0290010005035160800340001c1d03c3c0100c070b030300d0b100085440c032000c001000340440c2c1d9040303030180c8101c0c0c080003106400b14414104074050140299a4582040390985d01001115444a1305a0082c000c040704a01081094011400300900340500401da50000c4c0303100354142e038262040102012864107200d048141c03249000f09245070001c00900c0040784201d0503c400b10840c007070280040030400c4142d11110014010000300310b42416841049a88501450040115150083c0301950340e0302c1c0f43c0418400c81403c0c0d1700d890340090304180c0940c00d1140745c01d0952401c464104540411040c0466046e07810b540f0706e1180640d1000c40410f8045c1180d80e500090b4031028429011180c00f900e43c010360344058094a420903a040d070b842c444401003c00d2203a80828044400240d4500300401035403454001805041c0444a07280d0f140400c02c010784c1c00308210b078855202030912032013000c480d80f84e05400744039802150246a4854101850300d0003 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 573644901 1250 573643651 573643663
    0x6050d1707031701090c0f0f05090d030e040c050a09060801051e03010e070e0714070b0601030c120e0604030e0414070e010507020301020705010b09010b040e0105040b0f040e1c0207050306040f05 85
    0x70711030140100c0d1703152100b000080c100f11122800107040b106a1802d0b5a0140811525a0361652a00d9041120b0903040144094081008804006403400e120b907860301e0301e00036010300178001d072144c644610001034000c0c44541140c1c49001040b000000400c01074403032080000700b00b00c101103d058403040385000300780501590912501144214000010101000b4074400c0c040d41e641da403034405080540550719400e00a030040542245003240200c0c101c4e41c003a500840c615445414010b145400401d44a011580c1001420000d40c003c0003c01c810581c1c0070f40841c081400445e1f007008440413501c0100d8003144020300180c14415080e0485035560f0140d002c2d42d4000380c3c0240203550312030451030854060100c1c0440313240240c00c01c20012512603e2070083e00c00b611349800441e01241e107050100406000c0c00c11007203801480307040343d09800d52901e0040e4030403d48120004c0026060b14040c0c0983c1ca03581c801c1340340454100b54000c1c001c5a5020840c5d82e0455046075045007019461b050003130600d4 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 573646151 1250 573644901 573644927
    0x1081302090a0501090c0302040f05040e010617030307031d0a02041508030705031c061a0a0306031202150606180d0c0815070207090c0818070302130e0106050d170703 73
    0x250581c040000d081c41c0c1d03401403410383d04221003d02c28040102d80a070103034011030040e4101044000c10500c45403c007580514403040c1703900e0011800076130301c004000074440f003100c4d4066241c000008110b4590340500820031285528038201450100920700c040c0c495a1601e4000e1007940c9421105104481c0c1003070f40c4e009420702c94241c1303680390243e01e00310355aa4003c80102e42c00042203148144030050601c1078408a802d019500800d0000409807018960311000501d030078159101000320200c4c800c0d0341c1c20f20303104055800038854610030780c0e10a400d4440082170f0300d2282c2c2013040141119101d0314901d4481e00d400f610010026201c6141c42240380d2501d42120419218220ba280c0515075801c000500a120366000c1c0c828598540c000e040583d00c21802420101c1d400d000071800d0908a0b4010b04104505ca109980c01c081d04d07680012103a00303030306900c2c0c95030a494a9005170494400e20900c8010708044071004010045550790209002002e440652280e1011402c801810701440d0099068 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 573647401 1250 573646151 573646159
    0x18030a080706200d090302010e03031b032d01090b150d0c030207060507080613020a1e11100225020a03021507120c1a270c030304030609060506010507030503040201081302 75
    0x61060038070050b0013004102c9043d0f00560822781071103040040031085074028400b1100c00644281c2d06c400291082d4406840c101200703282808514034050a603c0300c1d8520b88801e2100c222951511100c0c2d0280e59162004070f110340764070b030750034100100d188048a003803141c00040401c1c20401d03200150000c2c00b0f5081f01402c4281000c0400c840e0310f40c8910f103c0e110b40c0c1c0c01c81d0301ca918203c41c040c05030102d01030085146e012541c024084802c0040c02d990095000003240340501c116044810803d040141c1e0b032441c0d81c409038021551000300c0c03e8003449043c8900158070380c5404142c1d1341d0005030340031304c1c14400070340600f00b0086140100755440049403141c0360003180c82c980045070f904c03004020340e491481c16200a03034071009005e260110184c00c1409002d0304040302140700b1825840e0002c2c028825164801e078403a84c00d09181c40d440c244040c100560051600040000007420840d0503030b40000c145a04000d020851000000d4202c000e80c1d410a40a1034400c6243d03031885120204108444000b07540 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 573648651 1250 573647401 573647407
    0x1e03240d02060705150f0907030b1009020c07050307050102010902010905060f040e0103050d030b010509010f0f090f140a0503070e13051204090905010b01110c0904081e18030a08070620 81
    0x2480b00c000b40030210307a9400110b0400c903a98440e00100074070000c1e40d41400e1f9400148081000c20071f0168a1500110985007901c9403503911040ca0040780d001000000c075030380142108001624091059100130a000c3c0020312100b9800e07800282005003e002d45407040743c4c081901d0104465030360554004c0d0140300e400c0c40c1e541d6100d04050795106580c00340d0340f000a080000c4010603500c5030050360398008041e190070060910111007030750309400304c0c548601080282d000000d0031058606c0941c005015010780f203101421103c05100b00318010307411403402540101c0040100c1074402060550280860301c1040e988407070780c6030480c01c18818809054079410f0205e0b01090700350b01a0f100c004e4452287c0001c1107000b11110064600314024170303604880b50400d00c1807450303e081c044007041e48248203000036071402200c5007900000418038110140d05010124940001c1c50911444040d80201240101040301c04e07580c1e40c001d58860344000404882e1603030041141d002c61076056211480304403d015407 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 573649901 1250 573648651 573648653
    0x2505010c110c15090609030a0516080f0a030e0613051005030105010809011401140111070b07020907020601050604260d05090a09060e0403181a1e03240d020607 70
    0x7501d460014001a000301012120185450b001d01198220f846403100d041082010810205410000c40c00f0b03018091a6054000500240580c840560618030080401400c14104c00d2600c100b0052440040d0312481c000300c0030a4100580e400341080c11138007a03954020349140305c0030b044155444560840c400550b00b014054200000c3c6050312401c2c1e81d8101d0941d41c1002e05402d8400344440c80d43c0c500c0c0080c0051010195400300c034809040103050440700b15030001c90007031504d1036590000d0407061000c0703800404c6240111102e5089555440100803550500d00058000e2095110303200516690303c490040e2003900081920000116905a0f013420440c5500500150711038481c03148506000c0c28003184600d6148114406c1d00e0743c0000540306562980d0301030381c1000f545107500c450481c044500040c1ca02104a869061038035050120791203001803004002c51035410030b40702c04408001d1040014030030721100d0014030030100c88030500742090000c0100c0c49a5680c0c0201940064000454070 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 573651151 1250 573649901 573649907
    0x304030b0c03011401031407050d090c150f05031e06010903050f0c0a050418170c0a0f03020d09031101140c01020a17100315110d020a0e030c030c01052505010c 70
    0x250403200300141c1443d07181307001c4004400700e400c1c003a14144190450004074900e24400c502422107102443c10010b0251700c0f0380c42c0e064a50036607500908521401c0030f0102021a803155840803000181e003400e40c10750a14104188000720644440c441c0076102c40c0009030103a1140c401c0070000c0d50080e003544c0da1046801c808944800b000e05505000c2e0707007521000205410a0700c55050604004280103289502c15502d01781c0c4401011000f2140620900c811f40035540c080c0b00e1020301504c14040741100703074480d15019003085030841f0b070342040c030199120402c08214546001000c0c400c003441c02e034901041480b110030407402416035001c029840414004c41d403a4100b03045080b0000d4442e1030081c3d83c1c1d101c0e6504201c2010700c2c040200402c0d011030b0030300341c44030031070b009805156100d8034001e05090084c03003000120303082400c00f000001d140320145100303401c0c103011070a1818000c0e4090a007031126940041d12034400e94080d0b484189200348000030b80804680700401d500d074400e00a00c0803a024103001 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 573652401 1250 573651151 573651157
    0xe100504030c1a16020708190609050f0604031b020108010909020d140705130b0114161e14010c020d2003030f04030f05030121030e130510061106010e06030304030b0c 73
    0x30700c10200c4645130001e4003400080c2d10400c4801e801c005000720b200900e8000b5850300c030700004940641e01d80800310001003042c40a00c1c0844038000003491249801d0400401c08040c0d0034280c0412021002020b0151b44d0210b07800e0305503070b140c01c0c0c00b003210001c91010403985000300001074000d80600d0303003e0071400c2c00458004100c4404a945201d01d010980d8000e007101c12590f130080c00301f40ea00300c904401c0e080c0031001d85840e100000d1200d0303c1c9071094584841001c122141d12440d40b1041044c2010001402d4a203610114001e008020101e44070300080e64032051900c8a0050080740d8146248000c0001c6400021700020406d4a8690404a600385c004d140150b4045002c242c1201003100000d125034180c0b4121a00d016a81885200c155000314001300806015800c0202094240d1702c241c607842d409403610300359181c001601385400410705140840c503401001c1003012003549400c1010002811606486540c2c00c00d0519440c0d160009155209590009100d517550f841005040c1003a0405 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 573653651 1250 573652401 573652411
    0x30518010504030f11010b09041202032701140c12090a03020a09052505030a09150c091406090d06020c01021c060e1506121f03050610090e100504030c1a 67
    0x2001c0740c0b00e481680c05d0b030030f86801001603500403c03440000340128500d64104641c450241c01541d281c9a0044288850840400d03907040320201c06004c03186c0701c0c5d60302c0314561018074103414041e41002c51000c45140c84200c0011081c48011000c144c0b440583d5500340d0700b40c001c550040a4025285da1110740c0700c0588022601600c00145139401442c0710891620001c400c1d07003550f41c50901e981d0f11400c044000702034400381aa0014101103040840d6405c904c00c04912030700c0c5807074041007140760946090034001032110940c042c0310700340592190380d165490a6007049034081e00140c0c072030310058920380c028000c0380d41c40ca0090302c614084407440342d01580090160744042c690706400c1e5131141002c0c0010300b240480e054100d80c2c100f00820000040381c013043e800c401020008041c03c9041102c40c0440f07105030300146c2d015009403080c00225412143c40c00000d1a40601c180259003840807841d446558030b0000411a0740c446000404040c815032000c0c0c09241d02200c079412504084800c42000001110 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 573654901 1250 573653651 573653657
    0x1b0b1311060d050a06120b010314010b270702010e030d0b13090309180506010c1b180e0c09041a0a060b070b0601020c040b061615050a0507090b040f06030518010504030f 74
    0xb13808281852906c0d180b00d2610740148980c600c076441d40c1e51741814500c5c404440516035503a000000d84594a81c803450f00c0030101c010f50055840800c1c4000507102d40050200000d680c9020080f200c88032000c01540c010700e1050700c0005802e070f90440400c109641002680780202c3c9000c0c1c0d42d0003050307081812041a220542001c1c041d1384e807138140d880b007103403420b6038140d01282d61f80c082c940004400c0c94ad00b01c01218201900079280e0380c0ca039151007136408444008540c02e030720360b280c49c03c2c01101005400c001101c1160140c00c3d40c180350711225004414010034000704421480055030264180c1c000d44c000f000d2250300c50f0366032400b9040c80c1001d294191780190050007207000c0b8a51a290601680b50240c0008068615000c001d01944c0d5040180c030004445d4081080c3c0344a6011361107219540c4104a10700c8007240c2454001da004008a05a41010034005c50a000078426090070140501c03c0d113186050010321900c0b0104120741301840c000d00c41c0c40542c2020304110804d031344041c20307120070400341d1 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 573656151 1250 573654901 573654911
    0x31c03150902040b0301270504080a1106060607030513230405011e180902060c03180907120218030d0908010b06070807080702041508010b011b0b1311060d050a 70
    0x3540c40d406920442c403440b04d8154040c0014803000b6840e016015000307103568a140500070343c00c2052415680210341c143ea0212000c2031308298540c00c00c0a0b0038060034003c0140c6103070301d4000700240c0f81e4010048054100000450f00b8000d0b01007449501d0040d0500b00b20003588140d440c41b666201446c0500240c0c05103040100008602441d0001184881d01202d0741c0100d0504000481b56141c4000b42209400758540c5514000350715994000c001280b00100550380c0c9855903003400c05905141d041c4d0701e0042040001700514103030301c00641861515004805030303941c0300c030502903001d03ca480707100d560780b40c003660303600304030031034114203018100d40c2240000d00c000010300c0c0402507103004402014040050400810000903c00402441501d100410025606c145c0d10b802e203520300026081000907030341d41e10480d2180c0d03801502c0039000348610305503803c400d485540d80600710140500006101c9610790001020004d8070508254010360250181ea2640a10200b032800b0b414151040c0780624501 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 573657401 1250 573656151 573656159
    0xf02041518140106020a03030c2102030a050907030b041b03170c0c0402030c040501210e03041811090d11150a11010b0303191103270f010e0d02031c0315 67
    0x81103aa0491300150003500c42482c46460a07070150080040c2c00081000820b8640f11180c84a4114100c91800342d40050b2240f41040d82da10072550090880f603080d5000840410000711074000f6190300540c0b000134800440441c00c000180303d000303904000c08a006620107111981c0c521409415503540f83d82c12604d000e410001070100703d210548040134405002c1005203c01d50282c0c51010300c0a5440880b9100308024888440483d001d41e56402426000040c2c1000103a420b0031313003542190341f09142001030002d00d03c0d0b403c0715886940300c0701740241011003011051050411000c5a950302c080d042551a5994504a03006913002d4031003080070171840741c0064650101481040c55000c0050000c51030140e22101003a4441c101111160402c416051084040907003130000d00b4407415a254203e100080300464440007280d074014a600940400d00c442c03080741c0c0d1100000b0786c562800d80d4030440120302400031034103001042c0c0c0d165804ca4440f2008084980d070503840407140c1d251110f101e4400310b8035 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 573658651 1250 573657401 573657431
    0x8060c0d0b04060303020c2403010f1a1c090203010f0c0906110703080a050f0f070c03200a18110313050601230913051504061808070f02041518 63
    0x1150102030011f0f4001078060083d030610038400b070001e00c10000040c1d4007070341d0504241d404c1d0b4826045405403951101d8100080b900000290002e580c107480b060382803014151a60315500029400c15484640f00d00405056460030740c010064540300c90400d008907481c1c0d02010340900c50520860300007483c0042c0d4100d080d0b00c0864058280d036070100c44145000304071401100d03070741c000c206002001c60f070400a2410884600740102051807044001864541c51414403000480c410703594101c0107103010310441001d81d104036003007040d5940850f004101905900311040281840e00c1c2e6001c1440e0004244040ba0001d00c480c03500641c4500104c0703149a8a8002030001c0070042d4034046400114400c02c18000d1a0181a0320340c040c0100c081540f08102035107800c2c2c0707000c156003030300784802c4c0ca0b210901007030080078001ca42c05416813000390704d8410110341e00d00116203e440005002035141da03a030002156142d8000c113280c0c0403085104400c0c82c0d11480b18981c0707205c03121410782c81e1624201600030a105 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 573659901 1250 573658651 573658661
    0xf0908031206360a06050a03030c0b0a0903020d0f0e040204140a080a21140d020306031b060922050f18060601080f13060e0706020c040603050309011808060c0d0b04 72
    0x2200e43c154404460307010540c1c44801d000a0034400044c1d17200c03000440c0680b21000031900450283d07655000d500400e09040c000c42e0000303000c440006050810520129400158031854185c0720b150894950001e40000c56400c40ca044900ea030190000400107414401c103c52002103480498008031607607070f1480c6644d603460180c1401411649112140300219002d900301c02465081810507511446a40c11101130a6106074485004586d010041c0410340c1000c11000042001040500c1700b8844da2100080142c000d4071400d900c00c8000803d920346002101a0305002c49000324014400c90500345a0380316640d0089030a00d034405540445046050000102203000c0c0300181c41e0100261620441201d210b08010603103a041060380c50b810b000900c5c1032054035085204000a40301050070420000e0030240809030452040707007421414800701328084221009402e00b403c5c5599171180100c1444a100210751080001c0c0c000e01d010407800890090003001d0781540c8140070040c000e405410001115 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 573661151 1250 573659901 573659959
    0x36010f050709150509030d0309060e0607021e0f010905011e0b0a09020d02090d050c1003020304080406180306050a06050f121515090c09030723010f0908031206 70
    0x14242e2081004242c65561400704204014a885403815210a0100c0c0c500b280c80c5a034140003d65509103901400380c98420300b121110000c0c0036042d10b08007007000a540b4070800b481c0d0341304140096000010ba1904001721171910b1000b00c001d10507101d445c04d00b28000c3c41801c5000302e2200da002440e0800b04901e01c40e07483c041c400200300030a41c60802440038000c1d0495a802c0c01c1143d420000030380142e50b40240480840e00c0b850040c034010802e1010b010746403104c80400030034580180240400186107d0507039040e102d01d4586042c582d0103a55a542a0348091361000e072116140100340014421103406c51400d442041d502040c001b1100c4040c820030340ca007039010b0000c680000103076500400842c0840d58104101c41d451f440302050044c0011800c26091304c4484014000007400102410280300c0d01c030041106a035140310440d41c00307038480c0707d412075070740715904004030f070300301d10040d80d01400440f40030305030b1a41104e4581d9040004640028010f0b90214868204d2500401244c604222120108 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 573662401 1250 573661151 573661157
    0x10f12140f07020c0916030c03060506120403110d0801140109150815010905030318010e180f060406120b04051e030a030605090c070f0501091217090109020904020936010f0507 77
    0x41b95a101c400c0f0020602d40d05e54404064560303100084030340e690b801501c0c80381160424038500703043c103140250603900692490340042c0c00440710b56514031703003000200c0c0c1190384c8070080c3c440c3e00d01c4a000488001031141c10804035515611505802c5541c480910340c8140300301007942e5a07040d10700005492060051060036403660040240907250b90710440c400c0c1043c030041c1030450640c440079000907551788040502102e1003640c031081088583c04894103607000306060768208141824482c4080d07464403c00c3c800b0301440c00200214007084800c015282c0b204505c03035a1040070000007802c20f9113036408040c2010003c1e040c40000300306ca01d044002c45020360910400c4520b80349050b565040400082c4006030750039503981c612207000c0340c0841c3d001100750119a840800d0230541c25005550120043d1040d416607240c81c0c1c8040c010389034423147c181c2181d01107811210f00c0d5660301c03e060341a1a487c2070354011642c000d0100d2126818516954041d00748100240044a036140e02d0008540c0120b45003000 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 573663651 1250 573662401 573662431
    0x17030c0406080106051201090b0103090c060314010e010e010302090714040e041a01080c041a1003060501110604081204021c1202250b0702060c031c0e0c010f12140f07020c09 76
    0x482c0231036600c0003a46080c181008601584142c403840303103950140c1c0c8454003003500c6441c4040b18200304100d143c05401da00520407034a5052410108491005000003409000e010000c50281c900450f02d210400e45554040c039603e0b40c440d003620030f00380380a550072150012480d1200540ea45002c4070141a9200c08005250009100b82040090b10b089110134110035844801c20b40d0742c2d00c1d0659240008a81928007242d603500d4200010100302039400c8030001c58000c4414800003605940c100c0715601c1e20b80c4100740c180e4490780000760125403103103a0541c0b40d00900348441c1c20025480f00403c00721019400740e0345800b0000130000c1904040c5410b000c1003e00459080c1320002101029040d100c0c000b412140c180030f5501c0c001ca2450340002141140c0b0300c5403942d03228a61209015050300005d1100151040001500018154102641010040c80704030002e000f002e0005501452284921300c088507010b0070004140e51050006494410050180c4040041a401c0c072845090080c1c8411400c810 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 573664901 1250 573663651 573663659
    0x1e060305090d2304080106090204140126061f120513260705060c040302040b10050a030902061606090203010507031407030c0905040c0201020c0606030601050f040917030c0406080106051201 83
    0x40f800f92004180509050911000c140814248604130150008040042c1e80300d00300301100300e070042d0b007050b87c0d0704018003018010360725000b00400c09182e001c64000c6c000640c030b4000010390a0150b142204c844101c0100d00c2d007040c607611420b91406e4802a40e0204007644030701d03c0050240c040d02001403c0c142c000c5500030b12180d051100c070720300d40c103d800441c1d0405229689141c2000c4042d00c400110000104060082d890a40318000f00b07603000300c0c2d00c80c03c000440380c0b000c1e150740100b1440b1014159a60120019511504111100d44806440c1040c2e02c105a1820340020801503606a009600c1c0c41c0c00200c200380070344a090000094900404629510020100c018140c200422002c02000ca440005c1c1a02c0c1c42c060890000c11a8002688038903010500030b11b0400000c156520960202d40108041d85443d04080718842d4181c4010913000d2003030801c11050300c038400118852030000800c001c3d0121810014205a032002d546255059a0b01c0c10100c1d102e004294850001000500c0100 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 573666151 1250 573664901 573664937
    0x615030a0f05010e10150e01050702030f030c0a0303150506070212010f15240822052d0a020906120118030915110a110a1e060305090d 59
    0x96031080400002289a5004001640542e642a480740342c107540b4070018000f04419003240c0b10301a085100340c03e0040b80c0c095200030b100120240c410b6052200001d02903080d5102400314a1100f040c3c1c2080781d03500e0406141f02503590003c944143d0000740780141640082c2c1d81c4c5006102191001000d803030034500305408000041f81b11413040b030459941d41c0410308010002d03000c1c05400c0c100000248020303916041c00400c0640d84601c112104108801d41240680c0e0014132954104158030550310388600c0440303285503001712001c0090302511801038040a0560001003400c0410b80422074100305071402100c2c42d5541590321402948032655a001488604040e9001458800315000218180e01429840032015100c294140c00046d840202844005005204031031189614500074145401c0100100d85604181c5401000c5050700780c0b070b801c8695103203002000604101c1502980c1f1210680c200c43d010b11061240c03e01003410003000601c02003003c80c94685000c150340711560b1030035004d2110 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 573667401 1250 573666151 573666157
    0xb0c070c0605042105060c36150903070315060911070201020f12070f08040b0a2f0a0210021e0c0a1202061209010f0207030309061104030302120f09130c030c080615 72
    0x1042d03034514101101044034500712230aa0003150024080301590340e0201842603501045000c0c1c914802d003042210807648002810a007241d802400f84481a820240030790060041c075400721444604192600d0030300d0071810010207215200741c003111030170020003403075648504014600110b00c50b0180101d80c081180d000184071000d100c2e800092030180c842c8408140c2d608441d4402c00050203021f81e07002021001c85426140351000110f059049403480001640d03502030410090140070401c603c00f019900800c0b148560300151140404a03e1a440314281d46640c5240c41c00c3c803a4029000001c2d48580e00301152440d160054038641c9480d24034a1715850300700d0080c0c0b0441156594401d020b44035a035901c0609000c5100c0d94002c00e007401c031800c001003503c0555211452a000c108410400250000345002d442e844c044132890711481100030b4600c0d540641d510907600704d018a12140c3c40025154071501c24001030351420403600c03801220891b00b10a00b243d00316040b20b115207404034200d040c0005 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 573668651 1250 573667401 573667417
    0xf131b230d060509040b07030501170316051603080703080c19031e050a0207170412030f1e05030919030509040207020f12010204060801120503070b0c070c0605042105060c 75
    0x1010540c50f42c0e450104030b015504890545000d000d040502012684c90f0103003500414080301c3c44012070341b40e0302201d41c881c4200d405200c03e80400c50104410000d0500010307103004160f8a150300301701d40c0c0781840d142c80d0b030280f58101c000500c844001082e00d007050003521442d0009009050801d000c00800b6001030400a038029001210105003407106a241e000c0d2030711074900d400c00540c8960142c940306280d2060403541512200061005000703072020700300c8000096415140ca040c03503078030307101059400012158644400d014a420000301c482d402c1401580220084011101540c0d00d18514a03603034070b50081c009001800410091545180a0300a05005400100040045036104001800340c080d030413180d5055075000f084c200300c81d5130040d00703a500609200310f81d040c0c0c1030381d166101c0c1d07200c0c4201c000041042c4078290100d1490101c0c0c1c0140d40ca01940f156886805036164100907000d80c109102c1c00781c2041680083c0315490885117400c6040c1a0300000415240d1284403013038202d5000018 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 573669901 1250 573668651 573668677
    0xd0f051305060a1e02070801140103151d060403050304030f230d0b03030c01060504152d090c0c140c031b150d060303080a020f03060f0f131b23 63
    0x300101c508805039130983d00c640881e0001c0804614100999007500c0c035014186424140b980010400701d60603030300009824480c00000102100c11140070b420a00311194a44260f226400822041540000065000314047d4076084845088510b046905902608a41e0314040074507014240c2242340a0242c9040500600041104209180030a10b07603000035400340282c1e9120344013080345040c9803050000e482020b940702e4000c0c50902d0300e100517008121a180e00d0a03011200d0f805c5940b070041da0032030054a142101130054014019005042003040042590382900c0081109a8401d0026055209020103005850602c2c4d032030b5202c1e0b2144940d903001f9500042c4509092441e00401402083d4950400310700040586c15414002d001a0740104501c40a610400440400816600c01e90354401001c82c0c01981031a907500120b03c04540240e111500220304480041480150341c002e94002d0402041e45540d90225040850710004030310030b01003e206034000e00b000f00340c0d0400000c1a0410101c1 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 573671151 1250 573669901 573669917
    0xd030b010917030d151a09150a05030411030f0c06090301150f0e06010c0c0905090a0c09140f041101080705070210120513020306150d050607020d0f051305060a 70
    0x402d40b03502d6140412000d28940c10003e001c561a07510340c03007801c0e14010703000220212542031410a00c1c00c0c40d82c2c444240da40c10404030721040d00c1e58a03040300d281032a948a01e11a01d5200c111009002034005603407c47d6a10083c030281c23800c509002850f8104485940002c04558a0074010300001c1c0e4080c00050740c05548130b032a14082500c2016102c401001c42c03d0461080620780080c20a07905006880340303041048206995002c81c82e80084901034980024001465480340c1e1700180c500f01308110700500108102000050002182e80544401000354820000990ba0000f00018002e0200c8000345913803d10b100c1c85682e03503c240c81071035201751282417092400e055a000141a400300c0340b18500014101020001117034140c1c040c19030000024042c92031103070525800288c40700c100800d401c4807801c0c180b100705880da4813503911b2903196030494141c407018148500001d44407420300e244c1da4085040d03600300001c080d200d03004440034014207480b03c0b80d440f0b040c0320420050364841042002006110 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 573672401 1250 573671151 573671159
    0xc020301020f040b09030d020c0a06050f2701021002030f0c0319090605150d151a060c0a0204050609011d0c270a080706050d0213030f05010204060e120d030b0109 71
    0xa01d0052014000e10050b207a00e0705d401508151403d031154a02e0011508654444075140c0c0300c108450003544c0780d03410300381d031030300e0800c04500c3c4507001d00d0355014403900e4080302c041502c50b8148148017141c4000c1c0d081c2c134004180c0f0700d603610a9110544508030807440400008003c01b070000c1c0030315000000b0000d01108004011039060507281018025100f0913550000d00c00310502d03100e8181d113194000e80d13210801c030040c0d442e1204040d05651021406035140c0d2070560880044846001d000076004140c40d85580b440e806156803090000400c0f030141e4908000301e01c8601e442d01d5020304030b8013080340b01508204010755803403004001038560b01c1180d100388920040e030700702040030301080809408560584018101041011401507101e004550800c2c030713062000c02d030f020080700c00700014048003580d504134000389495944031f550300140c4144604106403080142c190000c0040f030f9125a10003103240444000c00000520142c090040e99000100c01105079000e50404500070805040102c155070352 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 573673651 1250 573672401 573672427
    0xd09060207030f32060703060305060411190b030a060f081216061d0105010506210c0c030730091509090e0a0311060f040b2d010312030e0601060c02030102 68
    0x10404d0800c80010a030903203584102c0081184550200081c6028010545540c0754142c4521020340040c0540d46560030080261700c503420043c001c51007442c41c000c000ca0303503009400100d40064410011142c10980001011281191018207403684040a0100b03070307960400d880500c0c0d00150301c110080804809540200d072940c480c26101c140c2034070540c500302c00007a0b01e46007100e0058204034800c01c018008585c1c2050034502c6021409000001081c0584aa5900c9180c1b80a2590742d940c03a0b00c00050030743d04004950850100300030070100300300c1c8101c0c001c00b100300d2a0300c2e90818031000070b0311030132041003249800c0514650310103079400c0054110352924030180507a044214640265404901d681c4101544082080c07102002103003e4652801e101e00102042000500b0150500b82c207107001c104400f04001610100b081151500120542c079a032400480e11402d00c03080d1a00da07242150700303400500a0045071f80010b004070103880d20740c0c204401510702d043d4008043c1d030559800d1040035424a8 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 573674901 1250 573673651 573673703
    0x6010e0411130b060d020901030e070e0c0708162901051e04150602010605150c03030402010f121b110a030f030c0c06061415040b0702090402040e15090d09060207030f 73
    0x108211001d687d52036124000340c2038410b00c18011000b60b00c0074104110741042e074580d05410024400c1c840b0b03902c1d220707824051941d004102c80c1410200c1700494030300801491107600c080d00c110040c1c040880305034650707003000503110900c205a00610341d1050610070740c8000d14401d030517200041000803142c0c40305c000a910310580e80c0210025079524001070005182c03020311001c00d01e0710844480e25280115200a44902010780028107026000c80200f07031803400b03007542c07180d40070280000f000b40c1045a40004064603a0300451804512105000044d480011070001d2140303415071550781c3c0803608100b04070024660910002c080003000040c02d4005011405564010710900c07240306803400944c4100001d0359618103291144600400040000c0c20401c8160342200783c04a0b0504150351b00e81c004107010b451034480c5e142090040403840c1d00c10340760b8154200d028180e220111011120440341c1540e046c000e9029040169118410801c009002401c18001c01031294150132240c3c141c4488803030f0210 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 573676151 1250 573674901 573674917
    0xe1e06010f09080f0115050402071109041106031005011202250c0b0705150109020a08070e0d02060706050f06120a080d1b0f020111031003030c060e12090306010e0411130b06 76
    0x11b5190300c0e0f2262119041d1090300083c0c602110118035048090760b5183c00e078004000c0c1240038801c40302c001405d0208011000101540203000e040c0c0d01d2500f07529543ca0081580a101d000ca202420070405816051017a03a070031001c00160280204504504881d0794884058110f407a141c071034002040c03030070141018101d1144160f00424240301d50911060380303200c0580050044a106115083c2c101354888201500200a03060440c15649800049000f40d1b081e4034001c0e4024100296100400c0000c0d0304c11413141c18a162112041c2e180c103420400c80e0a148060403440d5404211240b0100351a20300034080150300d4800010414032a004030180029900c8035072012813000080104200d80a0107035000d0752000440592840c40d050901501c8105103010103020040f002d80c20308200b00320340d0301c04189142c80400300e80c12640400240c0856500800a01c0d000b4000c55000040254a00303095a00680e40140019a07101c03010040c003258120031880511400e4940d100070850f41c441500525440b = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 573677401 1250 573676151 573676153
    0x32303011206092613150801060503090109210201150803040b1c0504060e072709050c090114040612050303150a0f08060601140a120b2205010e1e06010f09080f 70
    0x145c100e01c440e441c4440466840b40100c00f048108014000d0392180586041d94070034240141c4039105d01c500c42e030041c4405000105010311629509507140e18034080c007021035590b41d00034004545c0c00344100703050341c0b072504c11000c0c0d83c1e200b480144980349400e4040c1c10f16078000b08802c039400c0800c2c500c00042d2074099505032000b99550b000c416084e003007800048090122050850b40440e60129140c5070141e41120302c80f130003541c89441d5003c125082c01180d00c49a0001c0c0032010a5071204c064510701b5111074075191041d45081800110321241c02400c3c6c000580110141d41955614070b2402d00c1c00707048034100395009014034004100a016008500042c0c481ca40040c100c5107400d078005031844030414004020043d0034009048143d604c04103020b285603851a010880781201008102c8014190082d0f8041002709000e213280d46807140d028504840e201c010445a680300d005524040800d01110b084086203407000140301c43d40142d43d00c4480501510b4007100e8103658091503810540b98802c16802 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 573678651 1250 573677401 573677407
    0x17160b0910021330030f0507060e070503100603050601050d030e1009080c0111061f0f08030325020d230c010504030e040e07051212070323030112060926 67
    0x100c056811007980044c06241c5503040782c200040c0101d0481e02c641400604114240710f41c0308981c1c0c03195050b02c000c41da0004062165440b011040742e282c000e640186402807251003c0207101c42250300590046a8101010b01041d134200828480d0b92402c6003015014802441d5112466858842080f440c40d03001d40d41c4c0710621410001920704100d210101b8504009aa0758040e148140100b88541c00640c60510402900812100d11050f84080e60041ca0f540d0007002c2c0c00102c0b4007000c8021841344191400d540801c000c8140c8030a40c45249051300401603200c0700c40491034070702405500c0206001c0d241c04a947c0d03082c00c1e2006039268803a4072401d83ca07035100c1d03040c0030425400012021000c84101d4050001140740b100240d950411407080d14401d98040210001e44c009c184801e0413006800e01136a0f640d03212506000c0c1a80c284207087e003241c02c0344814045c03030300203580d0240d906030380d0b035021150301e0410a07450700800362540c280155084000c8248000008101008000000b6091000c075a2 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 573679901 1250 573678651 573678659
    0x20c0f0303070e15090108130803090c030708030c0309011101090506010906180b09130c12030801260601090209030c0306070809010c030603110103020a1407050a17160b09100213 78
    0x70402e4860800e0078051606820011100105403003a1107174480e003840d14144660b070381220b58502502521020f44100c00000c24001c4001001c2541100d014041c0c08844000e542c4220301c0355030348038a10002e00e03290400c3c0b10000480d80705050b44050184040c0c000b0401a0643e10b45d0742c00c00b6400e034884141a07946000800c181c0029140f000f000700d6090104221104215010803040c02c4010544e00e075034180d000210040040c0440480c000d02154030320030039400c0b49032901030080380d802e004810200300d2002580f62030700328120071422501c20b144040c00059283c5000000607400100045615000c0e45a00584680b010000c652080000d80e4810308070342000d1148900f19000c1408280c2018100401440031414009d14140d4072a401c0c0fa00598a40030000c04541c01480f1102d41d500300c50002440c0c01c240721000138505150b07802200c8402003c42484032000842c03160b00c10300c00d07211000048620201b561071200980c005542d6040e2516080480401001c80c0d21001d2844400f0302c1d0510280 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 573681151 1250 573679901 573679907
    0x30e0310060605190e09010b091302211f271a010306050d02010203070b040f051c0314070819110c03040311010504180f2007060b100903060b0301020c0f030307 70
    0x12040c030300141000180001c401c0041524588140523601c4c00f5040000c01c40055107a0208914a411079490210340f01e0300540b2403541891072102c400c4d11802d00c2e0402040040081560f0100d10011680d01403142d02d140446c0210820101c080c0790b81d08a03005141c4180101c1d840c0a00c842c4915809581e00790f400c0e11000140407158244c0045d802036603e214101e0040c0d03000002c4414a82d000418580d9950f06c40c40d011100a0148038001c200d80071300b2034500000e201404140d86a004a900d0522106580352107130005880100c13280c0000070300c0c842c0031030140c4002008070800002190000b0a100170310784884030960780a0b040c040d03050f81c070009040003444031807800c601e054002484c00c01d1900d46040c040d222480781051504410644c0c1d40700084424201c2c1e440400e140080c20107200280101c82000c00d06900800c2c01902c02d64140543e0302070340e00d0144150040e40381592a43e2a007541141c40e10f00c01007a200e84a641c1640d420030181e11041ea0800c140b0001c2402d100045a4900d002d00001b = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 573682401 1250 573681151 573681187
    0x190203120f1b030d0219080f101208070804150306050906180402011e0e0a0b121612050a06030510051915030b040c0810020f1207050d060e090d170103030e0310060605 73
    0x1111423030f50a006040c07402408030001c0701c01c01139041c941c12805080202c1c1c1d80c803841500400b00c02c800140044c850702998054620101c03a600c0401002da41c800c1801324844c030890b002e561240354854440c0401034110360003030b04140113141080e81d04a001e1080391704400c4007003c4001060300003210003600d10300850b90201508000c003104d802c100e03041d160110b400c080982106404401350199000702840303402c0f506048602c0e40c01c00d000d14100103e00c0c1004000900040c1d070f460041106040082c27006d80912401807003a00f00d858580740300381004900401c0e078003212200e250001c00d80000810075003044580518041c80b0b556900703d2078070301280d25000301079170001034407401403000030b1116281c603090314040c03108190750030000d41d62140b040b20140301e442c0e50303c000107181800c00306040030b502101c40d00c50481d0000711a1608416076068503410482402d9002e404036003001800028410041145100c2000c0c0440f0344a00003506082c0558003103802030f42c00184081380c200d400019035122 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 573683651 1250 573682401 573682411
    0x90114130204140f031606120b0906010c1403091206070807021204090504061b020a120318080a0c08070506100e0c0a081008190203120f1b030d021908 66
    0x461902e490032895440d50410055024458103104604070250740f010b1100398100004034140d0300c0416104d01024280e10b15401041c4c1b2080d142000346d680707904010714aa402104161100440a001a0340d510450055181d0401c03c81c0001e21400c95252140b40c041c1b00c0c1c003c001c034007071b0526282440c8000c0242c1c8000b85000d0031903009250360301d61031401030101c1d401d959041801003130590721810121f0180040c3c0f1241300700d41c060000b003007411a90104182d00301502c240301903421a400d05008030b09030703030003800891a49441c2c0714000f00025240c400a14803036800e801c01c01e41c3c414468898000b590401c200c151000c1c1c12141c00c010342e0308000701c08140504040410019141410082055180282c031108000c4c08100e07008124005007424041000b8022a411660041c0d02d5a403450820406000128002e22802120424181000050311424074601800341c1c2080c0c0d00000403000c1d8183c000ca200700502007000550001c440741c0c0001e03e000e12010210340051300b04028000e04584c00182 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 573684901 1250 573683651 573683689
    0x403110d0b04060b0f1e0a06050a0f1809050c0d0608031e07140613110402070302031603050403022d030c0604120c05030307140d051608030411090114 66
    0x4502000500d008251981160704a0f500141001e0300c000441d05c0e06885920b69a0301102d0420b014078803400012150340e00c440251040940035664080540b19400303030701074200c0071980c01c2e420621035600c101c5a194501d01569440d180c03a95599184030201c0304295089242c100b000200b00803100038500400c001002448000c504e02140d00842450800881607020302d0200002850b80134004080c0701075201e01c00c0041a00d0040c142644001d81e03c1d44c4031802203c9181c0c03560303110366042c501032003510041034141c3c000d181340c82e01c0300c0307580c90301a15851022000d1003018440840503842c0c2c90340c070111702881c1429204a0310308910b507299240600300200b520070341c0005141e50250302e0f80001d5400315034085001c00055402c502c4c03da12450080d8000301d42602c008240b400c148103a820009602500f183d09039140f804000d18212590701c540c9442441100c00c4202d0340d00080c0c1c03140c00859000e401036646015541030840091054403003a031041e664402140f044c0007c615120110051500300e80b1 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 573686151 1250 573684901 573684919
    0x30603140307080406030203090309030d032309060c031b07050c18101509030f0f0b0f0705030c030c091e13020915071106070318050409050312101208040311 69
    0x183c3c40300418816400f66108041d00031004c41e80c032107410000d130380b9400030080076a64503030780a0078010b0042215100c4461004c20500000c61001803005200c0e02405d05000508940d81c0c2e41c1111220310341c005060541800f42c103804105451844501903e0403074494406007a540181d0003c10425003503885507a4018070107401030240214100110f101191000400081c0029000b003044e600060184d0001e03100d084040300410130041030480c03a040181c0f040f541c1a8280d100d00c2c0b580c0807842411100b00c0f001c24002c0001c504d1a403480005958400300039a403451070540b60303a003c600c001c06603a004c80100e4091000600715441d0407143c40800300e5220804600b4041d103440081c0026600c68440709410500207001014000072401c0c8400e00a4090f1031317940d82ea41070346001820900c0c00841500c02002440010030246410301508031710681103801181440d01e00c3c4194604141c0251420010400820380041c0384502000301c00c012500444c466522145075081040041045d183d80f144910459 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 573687401 1250 573686151 573686153
    0x507020309010c0809060f043006090501091a04150b0105181809070801060618030209070e2709070501050715111801030e0c01090b0d021207030603140307 68
    0x56542000003440c0c60303040c1d207019081c0041d6602c00d105c0300743d07080140081c80769150f00c1d4042c0180110307110f460807031412034440c038460b5044001d5000c950751095039180030040802c2c121380240c400b8074000c0000150038413880c0c1e64441d00d828146551110640d0230000c00042c06502c00c1c4980c120042d81ca0b0034040084079400090440c4205141d68150907642d030449080c0341c407082100403841c005c0001d0500740e410681011680c0b0101481610103942c02c00c1c60228038a446030181301011000c643d500583c0c107080d542080600400102002d04210310032905002641d1900c0b2044801c0e0707155084950070110580c0170f94160740009000b15581e920824007000266031080c2101e0b03800760010102c00b030303410a08102d00090111566104200403011500e411198a80c407114546050240c80401603103038a2a040c3d030700c80460a101d980443c04d040380421002c0d81a600404d0080d0316280010f02d4a801c103071003521118402d48010b400243d0307940040c01008a420407400319041800d000b9801c1050b5 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 573688651 1250 573687401 573687403
    0x111f05030a0c14030c190c1104020702010c050a0b0916051e03101e05070804020d152a080108060114271302040f0902061204030507120507020a0603050702 68
    0x40900903807881e56680c00788201e03481c07140900060751450822a10380d6400d0008100b083c94120225811050b500d044484009600a01c0050180c0781c0c804290815803110100f040007d4203c050306906001e8900b02100000e28148040d90806203d002c0f1200c040c20314071541b52a107540000707205180d02e03145209100781e985420700b200c2c8581304004880128950034002c03d061219000d620380c0710504205040000d1100103400706c0140058603401c0045644208007181e90030310640340690080741084140b008104080340d4456204d1803080c020401c00c03031001444020025110002c002101c018004425055000b60200d004011480081c101541030001d240b03980c91459045601c03a03071100349100c40d040c8071180b0181e00c02c1d420f420803210b00d1400c942001c1c280d03a2080c4c0200d1096140404c800242055882030141481c1c01034416401c00704052180c00000f8005442a42800700601c40400000c0703c609030b0076041003450340c0b000c1c0c80d18481c1c414440c60781d64a07044642458144420002c00940c = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 573689901 1250 573688651 573688657
    0x2010209090a02160503120f060d0305180126010906080619240602060a2901050f07020d0f050d020d1d12060106030b130209010203040302060c030405040504111f05 72
    0x800c2c0500107035543c01038014405890a8050000c141d170001003043c200420b49100d130544540308442410105540300020090000703104000100410f0042c8420130703d41800340b089084c6000103041c6061088a405059240506400710b038100c507041040c01844140001e0180d5801880100b000341174505081980c1c41400514034400c05a4a54502044601e9003544400c401b10300300101c0d00c4140f10f0748075a00207407030359011a00f200040d03040c001c0007860300310315a1541c41d06d2040c401c520098500b428004560030780c072540c885072000f0740c14404640503230396844060660030302c81c60340440800c6940c50540e0500e2049600321095400880c54100210703004901e880f1500544000781001c11030001c00907117160307600c1d1400b0f00140306440010408a8140d4044ca40a40044801102400c03481000c20103900c5500852401a0002d0004200506081c4050240c4000b07107800c0d03e00781a01c51f0041401c841007260107403602174070072a2480b40c504146020b24000800c03120300001c801c400340c0e0090701c03501c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 573691151 1250 573689901 573689911
    0x20c09040b0f1e10061d130e010603140105010302130501031e05010207230708240c04081617030c070b09010504030f0f03081f0b09040e060708040507060201020909 72
    0x91040002e00410f10542c0b0200007181c041e103c0101403c010159209508544c001c04000c543c8800d0b4000614940342c100c1420380000403c01b10004005828031805807120a81c1c9010540d03c0d100080002032401000e0801321240d0000000c00b1361450042041c002d03000326120395918035260041c800708040b411003095101c1d400d071451010800d030746000e600901c503680000e8544c0722285c0030181400b498004840070144140200d0f0442500c80d400540c4520501502030f1300b51414025012842e42c0d0301d21800e501042003049070781080da45a54603428500e802c0e9801c0e480045c0c2c0a4184803164100c50703180c0802e05003200840c202817034506020b50b900b5590041007600300c0042498021680b2a01c2110090b40c0d11030180d03a0880c0d864030380b400c80e09135849400c90100e40d0b0b1400240140300480c4c200d5255880c01b2107000200352a10321450010b5101c0e403001e0b034202da10703041d480407241402c200043c0110019503038802d05140c9801c0c130604008640e0030140c11640104526006070380c1d01c981064200e = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 573692401 1250 573691151 573691171
    0x8070503040c05061e0d050a050105010f05090405251e03090f060b2103070b06040b0901031b0e011e060e01020d26010308070308010504050103020a180b060316020c09040b 75
    0x540035001d45d02d4902c4076074154411850b1000601c0782c81c15466508114028660102d0a01c9542d89510040d9070000012040c1d44c0066814044441180742607000190020706001035034201401c119600d0402e08807450020300032510a02690705903080c22a9400984004d6107420031088103695078a4004052000000c0d0507640c072020018000c0e41c50524084061050703460802c44401c2996540c1d4807030700b01c0802521010b040741c0029580d41818024a56801c100810114440e807c5540d008d0800300c880f049034030b40c410200f102180d0a5000354215000e010039860828080d80c00030b180c0d080803a490381000c0300704070703440900401e00e0740c00155100d40c3c21603034205000d0014000840c0c89141a44401d6110984c4140e00000b051110240088c2207040c02556402110303031301c4005220680b2003e101c001d4000d00400d004002000c04800030849a980c1e03110041210440310340055015041522540c2d101b6640b200c8000090380c040005003d420f100342c503187c901d03192584602c6079411000f41082da070 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 573693651 1250 573692401 573692407
    0x105010e0603040809210c010311090a051c082802010c0e060f0c0a0803011d01260c0d030207181b20030409020405212d060f0708070503040c0506 64
    0x60356860b5111401100c04007110081e240d1046d6600c0e9440034801d0f100e6010a1504d540107620110000840310000e0015050a04a926140600603240e028102c02c1804e28010300c00c98000031400001492658000c900181d20034041c14180404480720074013090640e0701d0f020413507101c0e54200b0a8018400c1080310455110106030808041503c02c441d201c03101401100720090400c900030020714140c8140060300b01d000c00440a9110340c42000b07000c1c400d00c6c4082001c80016080e1800d40036450200c198084e241081c0490f00450f10346803040360220003580200c2424400745690046002d4030484400b000e004854a070030000301e110442203612020044c01800341c1c010341003411103501e41944031008a0f0354450b650600340d0000e4009020703a5106d4038021011407201d1820007801044800000094400840c00308078a4410039560038072405854002500c1c503220040900000342704181d100200c140030314110380b0003415401c1c01040c01c1d042c44018414000030030300013003501c400e8402c1510b441356 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 573694901 1250 573693651 573693667
    0xf030a150b0a0b07060606110706090b071505090703060b030102071709040e150403170103030824210705100504030f0503040902280e1503060d0506100e0105010e06030408 75
    0x202d1401d140e0000b05000320009103030b40400c021030b0305c9101107500c1942c0320b50119030300c400d01e1030301c854040c425800000c4565200707006810b030001c001c0c18201d114100c1c10201e0860040c2c0b003410349800303d6907184640c01c075042c1041441840d000c1c02c1040355049000318900101c603a560181d5030950541030900103070224036005a62902c0d070081400c2c1040c8002c40301042c8108846a1018404540450000304402e0004596284010035103045c0c981c5500c44281c0c2d40e481c04184c08034081c401c0e120284c0c0003035010b43c0000d19151429001282c04050600d903d948560740c10300380c54002e050380150300400d844c00079052559840016102a00d0b4007058207008a50a41040c0349140203a41000044a00c0080c10781d121407244600207000406801d04100016442e11090343d000c80078501e40307900418105514041490304100031588044001e14102d00d81c012602d6030707441d0031012148003041011103803090215a00903241d040c0107240902c1c0813a4098826800b19800d800060310007045018003003800c40e = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 573696151 1250 573694901 573694909
    0xe120304021c230a1e0c030c06091e14090c1306110d0809060703090512070c1e060c061a09091e06040807080306220504020f030a150b 59
    0xc0c42c040c01c0026000d0442d0b0b80d800c0041240c51000304508034028014014204038101140040d4440d40118031124030800790820b0050112030000219000c6d81440c20100000f000d500601014140541e105850181000904003007900034004180121480110801004940c80400004000700f510740c0d0700c198445105001d414010001d54491a1701c6490020132601d0384001c43c1a8065581401c40b018410900000d880d41d08040d624080340b84c1107840040c451034045d03041a0002441074080700c400c180c0307131414841c054020880c200d91219208008001913042c040b43c90021400c0042d043d84041d00d4204040c2514040500081680740c42c0e0101d900c503030700d0144449000c00d030080c1202050f841c0c060503003610780c56040208540a0303400c004601490031300140c941c0c41950721001c440c1c60240c01e501c61f148590002413a983c2e220220780000b40301c0d1140301c50601e2484a00c0070010446040c24410009070300845440a0f00a40c44000d4803404940b2030744440080444025000039071440d40c202003 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 573697401 1250 573696151 573696169
    0x306040f0b1f090929040c090e06030304081501080f1603031805061207031a0604051e0a0b0909010605030402090f220305030f15090c030603010b0a090207020102010507030e12030402 80
    0x900350303494504103012040c880e0b45d01e0141400ca004000c002c214002d02000b00312072034200800006155040284030307691501d000b254120500404880c201595a07000c01c6c41c16011089066142405c60010840c1c2c28040210800310f8039450301800c107906c41e600100b040c04e98030740f0000e400c00c0400d048844101b05946040400341c64058401a0303103a003980e54048081d80152500800a4540341e441c80c00065200003880100c4401000103141602d40002c02200300c01039060000c0ba00c10f03401d00c01c80c02e640c52448150040202c501c40c56191280b82e001c004040f181644002c0610100f0410400183e42d020406580001408d40070149500e03150048100801d10600c00b850f1000c0302031002c01415044000381d48604008020281c035942c4034074500c110407245e03069494001a240c408107100250340000340d50300c81809070002818026010006811103080c1c0d02030480b2030781c000b80306000d55a080c01007503840b03010380c00c084c491a6a60304c800d546e01d83c0d01d03405800d180680070000c00d04541e508545 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 573698651 1250 573697401 573697409
    0x207031b06060e0405061b0307020a020f04020d0e07031b06050a030f0609020f0408011d12070f0209040c0312090609120f02120607091d06011b050f030306040f0b1f09 73
    0x2c0361000d40f410386049586c8460680d8081d03400b813080320440d1072500e109801c8a00c594220343c054017105900d40d00788a010b001d480449580f042d02800702c0c41c00700c8154860f5a401c00c02100c003e1100e5441c41c10a072164486580c08050b4540240e00c080c803003143c004040f54600c14440c40c00250490000c451440140943d8105030f0700c440c00003c1c44d280090302100a131040c0e400e420020000e00326245401e401d2102d025544495a40188400000c801c0f0400d026083c00390259159102c4254980c1c009032849600300c44c103c95106202a05200b885400918880942c5040c00d0080700a03041c000701501d04034a900c254078041c2000c2040c03004206412440706107240d03000e010040b8840356110352a803150780c2210075400159040f0350010b00c00b0100c200480030074010081a00c1191585001180c29545420b43c141007030340c0c0a0000b0f00025410040341d61400d424401451b2642008400c10098800c0c003020700c5032450070f141c008034a036a18002d0711300d50b0400400e07000c0300b001d902c940107035129105580 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 573699901 1250 573698651 573698669
    0x1e030905090a1509020301050f011106060d020607122606010e280321050f0702040507030207140a030207080c090a02030916060302040f060c20031002041d0a0207031b0606 75
    0xf41c0010000050303000340d41030b40d0044035a000c40070398541c011191142808003c410742e921090208d0194105800d0001c4042d001a009500c2d03c241c0c1c1c0c45e00c081000080d8207480024090000c1d0311042c05508021440841d080b0403280214108480028001409884468030038000b0322104000207205000c102d900c41a241122140f032581ca0404030260034001d4030074000c41603443c1b040c0c4031311403040045030800e4200760142400c14602e80c09000062070b005080c1400d00d6820020000402c140795042010002c004004101040452900030300704030051340301202950040c0c5174854582c1d500701090380d2142c16202c00584030390314400690702c0d0101060301c00d07034080d001c40c1010501035416002001074402a00140c809240e13914000c5070000c107046005008624005644000b03000ba152514901072070047c2142d4010011601c0d84040740d103d40d11001140444004121090230701f1000725034094500082107007400c4183d10041c005004440608010480e442c08403020404194403010141400c04 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 573701151 1250 573699901 573699941
    0x30f0209150915090603181f0b03010b09011505181903060c0507030c020609040f110409060e070c0f0512180913031d041b0c1e030905090a 61
    0xc1010751103602911556005040c1d5000041016035070908441903854050000d030729696803400f00d1082e507030820b030a4010500500b8800d400540e41000030321020701092000251182080342058210740380041c08a015103850401003002980c40d41c090510081c1a003041c640d00c40b014486081d40c0c1d40c2030102d00f5480201500c150b5074150880c40c1450690f03100344003c0081308034500c810b90303190084020040014180e448444d005040c490098a54603102810104059500b0ba41c440e080d42e00c2c21030404000345020400700104091406440010064040f403840c2070300f082c0100030f007600950140501440a068105c0082000c10003c10710b000c41d01081140e1240c204c02e2040a0360048400102c0c403e4030080041000341c0303000008411030710f134103480e03010600245074041c0c0500c0c000e409010342d202c0d55039150810b01100381031034162040c3c0c075030703441c0c01c41901c3c03900d41501403004c600139084521182134000d500083d048060301054440881e451481956044098400707007901200414400c107040d = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 573702401 1250 573701151 573701179
    0x20a081507030e2a12010c031103040f0b06010c0f0305180118090c0207030f0c0504050f15090402040906090b0115030e030409200f0d14040b07030f0209 67
    0x1250540301454000010211034484403401c42c15501030020408aa4100e4842d8145080007554200c0c0c0c410304411203007404440b41c000184000c41d081c5000241c6075100c00b08844206e03070500c2190354401d09d5000e01821403c0c90386840f07100b5000348100070043c280c80000324080f07a01910b044110550301000b6101d0b0340c902c0b8a0000c005030000c00401d018030320900d5464172a503000c0c4411340300d58043e40d58000c3c000c0b8136120b05100640b5400d41e01310300b50b000d4000d0110105040c410300080c014000d064081e900740c6044184000c541c4024040350071602c0c880c00b400400b01c801d84c03490451383c0e0100d8400f804d545039400050000c280d107100041010389810041410800c11060250494082d900400b0507202404010341c1500c0803030329a441d00d0b4000b00818801108a41d0000074510781495203411884042c4020b0380390f070782c400340c10b9104646010a109400b440c1c40d00607100544681c900c15901400c00d9643c100d03040c040504214203258580c410742107802165816210581002040703680744000c0d07 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 573703651 1250 573702401 573702403
    0xf2102090109060f1202100e12071d0603060903040b0304110d0f02030f06090a170d06170105060301090b041223070b0603061e0406020403120e030c0f01230403020a08 73
    0x741307204107003045072103080005815165540361200c031a009802424104a00c11007102d02500080c107403a8440042d0b1500814442d08100f0007000d440401c0b189165840c64080b10703200d06800600c014841c1d0300140422130751400100c2602c0c112403000d14403030f4480d15180341c01c0502c840f03500e41417034100b90f0020780003040c09030301500790600700d0003174080c1d42c40c58401030101d41e01c4002c200d81201169004482a20000f441c40e444402060384c0c00380841c0c248024262410305071a15548844010210b08415010356a028440c1c0d9400200490080040300c07425903c00000c103200a0001e40070300703010076159549034000c2c65010142d405080c0594a0240c01d00c5200d0000d0b04440000e80e88100e0140005a007400c000582c107000700d210180525102d02684c045030410100184201d540c00d800340000000079144100c1c48031541740b90388807201300c010100c0034140f9080440000070f00c201100b1002c0311a80e42c00441400c0c1d42d981e41d03110843c23044203101c451000c0b4407603603100a4002e0325107030300002d20f644 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 573704901 1250 573703651 573703661
    0xf1b1e0306181e05010b10031d0a02030604080a0e150d0c090b070b07050714060114061206010503060316031a01050d030509061305031c090f0f2102090109 68
    0x110801c010002c52024080000070581c0c00d40e4000d00408a021107040507515502180c200e07684200c001164406c0084082540d0410300c26005011071386851100b101010a02d03200940c030904440107020501c0d007900080d54506001d032001d04090300002e601a03131039110346074015000c50702408000300d05c820030641c40360680c0308000200b10f0a150501148280384641c0b43d860490705a1180c050a00c0d0b11900c3c2d443c4152002741844003800b00412607140081c646209208103944410054010b941c07402c0750f0804011051040b8a124410030010355001c128410704040c0c00c40d0081c600035442c0d5a9801c0401e16082d05034001000d48034510500000b0000203040781c0104134090f8841003c20f0b40e0ba00d003405411140da001c000e020901c10322950402b81401d50241114891540d55900016540c0300480e082102c0c98001250214450440c104015000b041c8100102004c0500d198024949040e691540a09015941c540e10350405400032078010302e240395100b10f40040c80e2024650b51401c0c0750000b05 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 573706151 1250 573704901 573704903
    0x604090212070f150e040b030106050915100e1807200f0d0e011d0d0f0f1b1d0c0f0c060703060801020304030e090a060b03150112090f1b1e03 62
    0x42078a20001c55039031303a02d150100e40c107881a1a038100c0c0703d0301c005c00c1101801c07562040755015903840e040041c86e81d03035032003010740954940541626a42644030510004018048120042c46201c0803072040c0340d01c0300d00031480e50303540c4225005055240d1050440348016286e80307005c94400e8002ca690390642001c12803440c480b07222400c543c042d03c800202600c40104003007000c0d0128140c0c2c8180c00c0c82c0c2c1c0c0301d410b46d1014814010415104030748a80d582d00c074a032103180d4041d80c0700d14503911203d040121100d05002020800b10925800302d1400500705155440c454031880c0e00540800890340c1c0745050303800da0f0a50b4041c044510f403654100d125550380d80c0740480e89100000c0c2080000104c101c010320880b8026a05a80c072403520500e8001449034000020304105c0074580d81d0384002520b40180c40103580a4645840d0840c03105240b20001031a0700c501903050004145403059000c0000c40100c440082540d20800c1b10b1030301804202c1120886a0a510008000251060407409804003c0c0100305407 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 573707401 1250 573706151 573706169
    0xc09140d0506010b0c030c10020a030513020a0b1b1b09010f03050613110d23010e0703030c021309050a0b070e0102070b09060409060f08150411040203060409021207 72
    0x990600080040349503800401038802d4102c403005009000b64040244500c005000842e881e04c04055441441c112004110016055000c03504101c0c1b581c1c18000c0540003850102e00c3c00a91318590005a0082c1a51040d500c0c02c0e07800046d1410451041480180c2c10301000c0c0c00d403220038003020742210226038181a070700d03c103908500011400315122490001503980042c0200120b503112007a03848200140706050312600d2610401024a41e1080c2280901d60b02c6080c5d20140e180d8100400440a81d0351502126107074181401245508400200801180e0301490590480c4040340089441c2d152000010000c0c40d0500c4c003500c061150010300340e140248199281e00d45a940d0000484a4280442d00c090041e0840d0f48100034425600c0d0162420030070040145141c680e4540d03420b0104c0742640e04c6184181078141040040000c10f01181c0002d400044140e0214540781e07a540d4146024260544d00c11a0701002140c281d0b03d640c1e00c082c0c203440c0e003d80800e20004c0a03803140b0381c0e1400b0910440501c = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 573708651 1250 573707401 573707429
    0x5040606060f0509150c101b030b0105070204051305030f0a1202190c021306271509020c01061805040b0718030602071103062509050d14100c09 63
    0x40309105000694903290950343d5503007024110070410600354501d41400000c00e1051000103540c400078410030500c83c4031032100003000e0944880c00f0402002174002c40c2c043c145840410811644c00c082185d401c5a812540010a59222040b42e0b008242202c0080d00f00c0c0b20200c1c0f15240000c0c0e00c0e0092182a07450748540168000e20303541d48d026480341c2d001403000000d80c0c0080061107402800d400c0c88151008043c0d02003a0b0f03a104a1900b144c00540c032408550712010402d03c00288000441850013540300d5007482000301c035446070345000a640c4501ca0311b07250300041070100c0f40004e46c860405000c030b0041d40301d002d0188a140300c02801301540c081e05d14030014408a1811800b824180d00e152039615019040c0d1403454072224000d410116050b40c508042200101e980c2e83d040c0019441032008101402170781100c0340502e52120b44001c030b90418041f140c0c2e428445591103281280742c155200718801003040601404a00349001301c0300005515051400030b10500f50448045400d850380400300c540 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 573709901 1250 573708651 573708659
    0x30f03090f0f090c1116050a0509090303011701140403051210051c020a091409070e07082202040c03050a11030c030f0403020a080c030406091202150a140c0105040606 73
    0x8110014400c2d520034220201c010404000650000c0c3c56080e11400d00c004074580c0550028141020001280c10201803454103010b10700c2e02c0c2c0490005440706440703402640c0343c40c00c5501e0b564030042c000c2203841900c008556810f098250009a1001c520a00300e21507404e15240280080e00662000140d4002c8500003c0061040600846c2140d400503c070340390f2440c1c414000004800c103460240e80210200d403010800d500c09018001e4007056650381c0003041e1810303202c10750401c561500003040e007400810901641551088025400100f048030051100000401c044c0d8100540312000b5045410b18400008807170700356000510524598100303102080424500c45070a200846455280302418004503100a00e2042001d03440f41c46401107880c07048280e2a14101c1c0d420051801c10b040d440060140240ea0388541c0030401850f8602d410280c40f99194000380144400c000d03001da0a05000c260410560b2081d0302044080100c1c0c109035682c0c2c00c80110a074040c2001316400d407506130030128006 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 573711151 1250 573709901 573709919
    0x80f0a050d061211090c0d061508070c05060403050313120201050403180f03080904021c2a0e10050d0c0224270c04050c0a03050718090b030304030606030f0309 70
    0xc0603520503412011340056104018503214041c0403481c95090074402040001c0040c49914080d003460080c8506801c50301c00c005108101c01088102004400c2ca01100042c80c00120550401da045c01d05036100d0b52501e001020260000401030540f0701c01c4130488030320540650000707000c1c1b40269a40510000e18950000942b0024401d1040f007071509402040414003100160100c014010070262507c001c01d600c07550a0343c011500c0500e416590080300c0c9580401d1544210183c110141b4080b05107003c603c080c0108020400140c0603c0c0f0b100301004a007803040c42192400102e0301320402c0100c02d03026000703583d17445600000c01c043e041c1910401d089110080341034440d403242184252010400390382020b0307080e6451050920340c400d007210072513965504d00841b44294601c1c00020384580c0b852000606403500174003e8001c2c003134820035010118490041140a8a000b100007180750140440828614403c90744058006482e0000220410146561500c0514000d50740c0e40c4d0100c1e2103028407 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 573712401 1250 573711151 573711179
    0x2180c0d0501120b072c04090b0c1210050609190503072718020d06020d090803190501030818180103050a0308070e0109140319050618030304020303030f04080f0a050d06 74
    0x80c2480000c0a841b030010464040c1c8240d04c0d4942c05030011401c3c00c1180c3c0c5914400b80b096840203040c9802040311420b034038103920360540c0401007107002003c4510302400300341684121241c080c02044589003018107000c41508010007000d010303040343c0000e03541d5100030104c1d00a42c090854002069140001642918003a1500032191401d01c3e003c0495240e08210324240c242004948454081c0034100d80d0034001e00c40c013503d060045410656a14050000b03641d00700c080036028685a14000040c400b0485007801e880030440840c40c3e11940e45800790000d495040d2400f10060209003840010080110208000c24210302c41e8403403440580344d85200340c8800340d000c6085400034a01c03520030090181550400052a0005002c0c4d81c2003082c65414982c035502d003d003060f00d1590220741070040c080340400f084940704a180703000d1404c1d030805600003500c0e4407015122080490001001c41c091203400e108840c0b400304100c1190707551701d2004101420b0364200c0d11800d403905242400015200d4043c0d984 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 573713651 1250 573712401 573712427
    0x1b0e01021b0f0f0109030813050a081908030606090d05160509040308040204090602040801020d0c080106030b061218030d090c1205061f12080301031e02180c0d0501120b07 75
    0xba00701c01100c4000e1000c1040d21400f10390400049560010108a03500c0c003c0c10205800c2d900341d031805d0b00b00014414012a079600100040e4030840000c0241c907611046486031651040641f42c1c0c0f502d540e000a0b07114003503140304940c48030948508804000e400201c40c0d02c2c0001d200b040c0b22680f50f039030080051403002298068046040c4200240051800c0c0d80300b0a803907440b80c0c80050515440d90320440c02c9030000284410225610307642e00084a03004049a03004055900e000d0000c41c06000c007144403400b403040b800e030102e0b2141000c5510171a03004509240502c0580071a601c49108104000162a00001c02c1d00c0c1d083d00d40f1030103d03501442440203020389404c20000c1c00d8030b446e080401d4030400b07295001c620529105d090042014160105c60060f001e0050030006d443e5411802c4c030305a64181002d45c0206440705064100c016201c0e52102c0785c40414034100251559240039169242e40b0426603214025890140007140c2d03021701c1000400d0203401f8098100392503584c2c0105495003450b40315 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 573714901 1250 573713651 573713659
    0x9031e0922140c0d181208070909020a0c02060702040b04090317070c0f081e04061d03010203070f18050d0602070506091203060f120d051b03130e0a1b0e01021b 70
    0x88900350f030505980018170699110344070170b041c112040d00d8440c0413010005200001408100030b00802030703030041c0c54a0141c10b259504510f0b110b203020000e0040004500028080d4034049003170819540c0d40c2d4041c1800d51005403060007081e48516004003070358000440e01c00490004070108003000d22503001000129403101b40d0391401009601c48801980003254520304e14051701c81140c480c03119800140c0014005d58617602490003608a6030410b00b001714984901980c4144100224560300201030b041030200c40c24540074012002e60001c0014044c1d4101c5a00440d9000000041060580c0180309540c010f20596116403980206151103860500910040307a9052000c9800c52602000c00a0180303001023401181d810070207607241c20312903243c5c601408110045180c01e10b0955000720158030251910140d8076001080250043e05d1a0754002c4a40d00341071480010020b10040c1d012201e640c0446404030102a6840c41c020000c1f0040c0218074014011498240c6035071280000d030400e03980e4024 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 573716151 1250 573714901 573714907
    0x1b0f030615050d090203010618060909080306041112091b030102070308010b181224010608310507090605270c12040302070305120309031e0922140c 65
    0x74800c9401e50419258888107036507403040c0700d0041c0ea00744141402000408030740e0610600c1c507102c8100b244e1090384003260781c0d070402c1c61040005003603030120380d4003080455000504203150075546185014290010700111401c00c248584408000340d020340e2000c1d03ca9121306020a46401d05003030b40240b80c00180072170099001403182c60111009001d006004200c17200503032075210700048510080c070000045a0f003045040118010b920803141815821103450040554900f0700d0081800000518861141c0d10324a1076440c119001c01e544949149804198a81c9282a04160303032103186500c0b541c0e09003480c00000249500f4880400c00c90761044100380c04034241d4000707081803600d01c01020fa0700500c00410600c0f4840c1c40c5a0b0072103000358001d6005100a508500e811840d058124246805040050040040042c0004119064081e8054000c00c500d016034809104a01030348048907480f0748070306c001580ca103035140d003402402000f145091100b0071144040503541c4009603000302e1400410 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 573717401 1250 573716151 573716189
    0x702040b0301020f070c050301050624090103150b030711010605181b0705030d050f0c19020c03060108210c0c060703111014181c121b0f0306 62
    0x1690020381440c50180003d4a404803204082507550f02414045034040001c08060000e81404d202e074540c440c4055036112089054036000388100c9201e0200c003001644000743c101c4042c1d119402034000d080d404105407c2e84c83d00c511000d90b46404c101d4001000403a01d0303001d0f0b4283c000c14045c0d4002c60f00c000d440704002449001c03000c5800c0c20014110f00b1440c00a01d001a942604030004000c41c1e80500003540e214041c26440d86c01303440001e002c421940c1850390501c0380340d0102c503080b50580050001c041e0200c0e582040c0a90a0110098100d9814003c10707000150028004c01c8200e145044c100405021501100c64250540116003000c006907000040115017424038500810f16607009040c00401840b40107c480c4c900000c0d080c00f80301035600e5005a102c10000d400c600390b00140210101151707041d40f08a116521440d010300c0f020b4020000c1c90407c0b00c140650110003071041c9601d07041c0300c005405062284c00307407040040500010014004c0c004038034400c1c850303001501c03001c2c0002c01661440d = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 573718651 1250 573717401 573717409
    0xc0206010608070f18061806030209010e0603060414250809030a03050910150312051e0306040e0109050703110a06080a0b0406120c05011e0503040b0c0c0a0c081c02030702 75
    0x403002504c0c05002c031107045516000d60500c1500014680c079940c00f12001401c0ca964030540c582c0760f020105241c01446180d05903a00a000c48064490030b65484e601c03543c0d07510000d800341c130a144020011003440170a2000d0701104040e404c40e84000780500d02002c0000c1d5008a4001c2c00403200009150402d01c00c0c924014401c0d0031298008a42c1c108031090b02018a00d008115034440861000c40c1d002010104208512042042030403038007800c1050816100c62009682d590084005c0b080030500080010703001e0380e440d4002c0c3d070305420349002004031f210b0030f1400556030701d021701066659802c006544034031413800a100109039203441d41c0310381d0341d40c4030404010701811050780c0c035550007030310340c8008030703403d82107800c01c3c0301d0103016000355007881d4944400502070301c02c0d141c0d001e655946070959240c0b00a03080030031660080d031f018403001484d036110320350b1390386600840c80191030718090540c00106001f1812601003c0da0201001e40d50007028590748032068004042151015070818844400580f0b0 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 573719901 1250 573718651 573718667
    0x6030c03070c080a0c11040b010e040f020d060305030d0b0306090a11030a0b04061a042f04030209090307051203010e01050f0301060803220509220519030e01030c020601060807 77
    0x490b061064240702c85035121841608400d0002c1d001803030181070a0700b13001c00000456142c04081e2410000003c4c510002806000001e0401d4000c50f191003050300160800d074100c5050358070440c0d04020b041e0b100c0c0340070b0781c0300e511103c110000f007801c042e0700da1614038000c180c042c0500c0d1740100410303405280756141c044245e0611005541340c000e12100d50b0102e04440c00b680d12451041c280090500390302c0b200406010031003080c041c0140c0c9046811903442c220540003040d16815104980c01c110054850356800d0720031604000d40084a010512901640004c05400311500c610156038034a2055100d80e0560f000902c02d001c0101c611000401c150f0826460034640f100c00540081440d90315909203e01d540d1107000303c143c0383c4607407404034001250b1005042d000740400301e0b007041c400c0c148004611140070344006001a034002c0c1081c2c14081020030407840480f102450051801c98a40d820090320114008120740d0100c2d08040c201c4030458404180d49047e19030b5030f05e0760641034940e91012a0307190 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 573721151 1250 573719901 573719911
    0x103050f0709050d0c090c08010e130503250f11011b1203020d02121609050102161401091203020601052704031b0204060b1315021b0423090606060906030c03 69
    0x6145c1c200401c12040a01a84420150644030070005524106074030b40311010017031002e1036841c500c025200019030702004641e000d4818040311a040d100703580d0441d81e0300c62801030092840a25079640d50410450030301c200d44007902600c0d510304051002c2c0c2d2501c0750042c03031103000308600440110395002c54001e80c0640070901403a000141040b1001070500c0c1c144c00c040d5698680c800c6c09424002a07154010300503000f6000a10141010304140141c81e5035104840c02041c11143c150b20040c86075910800b1600018084901d884a501e0030604001e07449900078050a4064841d803041c4c10003d0054405410302418203441c80d1034256507603203040303420b00c01c3e0201c0021a204165408000f694590103041d02030500f44006a80e60b20380707604c03d1003408a207580311000e8560707421450b10301150042040500c4e49688040c529078042c0b084002001852030080c0b000d001100c0c0001c2d291503400c02003074070748107940800440b40e15499080801056020740c80d0166888107040001070801003102018640003 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 573722401 1250 573721151 573721163
    0x3050a02060a17100812090a091a0a170606010e0603040b04240501090b0a060c080703140a0e03120c0d0509040f0e0327060f1b1006050103050f0709050d 67
    0x1800501404520110b00307603031450900700786103014401070106114907060301b03101c0c0c0c04007403401c03d0400c007040b440b01d00c5105648640d641c0e04a600245050a541c041c40274100411880030301f0785401081d9140c1d0765410a801281c404d00303000403140d5001d4444640101402003c0e2406e603982c6584d00110011300070b004443c2c0c0032900c003e500704518071120252548500c101c1c0419030b98100003512088588601e0054881e440f170341c00c200301d020b81044486800b25007100c1c0c904d5848600d4107054640c030041c503440c404008000122064115070181b2194503280049064980940100c0300c0c20b40700303004100385441107403c00d060b110a058040d030020521110060030104184540c0789119048620200001c0c00030f400000e1079442c0b4104a0007084050405600d141454410b400c0201d4400d0007103c4104400510024641004584603c407003e522038002c03040f41c210402441d0144080c101500c01c00c0d020034242400b2500303032248075030380e28810f41e10b039510083c0c1d00e4074100030003140c0001c0305c07015221 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 573723651 1250 573722401 573722417
    0xa0b0c0d0f111c0b09042003030301030b1801050f01211209030c0f0e0c03060103090501050c040603060602070b0901180e0f0f0603010903210e03160501060f03050a02060a 75
    0x1040150060b9440311014050141e01e804201c04030300b02c404403a4001c5102986041042000f40e500d050301d25400c141c00510301020440000007441105030b00885d6180d2510011000004102c001c0d111940308101c1410303031a01d4100d40900103820380c0d005a03031400161982c040140080f4200c00303242c1e9107141014030301901000c048c0c0c442001e2400e48440020025041030010b000307110846490724000c210106e92040e0041c038211801c00f050001500507940805c000004c20140da120703070807145e80250014000c100780c1c180118900702684c003038455507011900b042000114070340007280100440d1b0f030350b00c80c09103030410034001150113003850700e024103140040f00008110501c0d048000303441001c9080521901e81006c3d00c450301c1c1550010b00142c8070382c0c100b805c80e8001a5210803140610001b6010300303a210000b200c6400d010b0301e40c80191030351a11010401520b506103103040c818413140180020406030b40c0300c00700141a40098000a070840d070042c2048001810190f00034489590a440c180350 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 573724901 1250 573723651 573723671
    0x11060421140409060609080f060403050a0e0907020d0201050a020702010206010b030a0618090615030f0b0606040b220609240e040504050102180613090b030705030d050307020706020a0b0c0d 83
    0x10382c20a82007400c106985040078419982c000c1884006440721200900400108225080e51100300600c01130070003401284404c00d050040c4912140d050004000303014502c0c09000c02585c640365400d401700150300303180129605031490701c00c87e0399203501a40584110f0f03081014104031544054a00420940d881c40000762080c0030316030a4144140184010400f03450504002094a9600d19000c41781141036401300002840310408002c200c0c0d21540300d40d9141e6038000084c0b200c1c051680640d0310864000f4901000854403100034410a8034540303d100c240c2d490b0141190082028000e5a01c1100b40c5080036468030b03d4107103d418071103424507010b80140384010200f000c0e50f03000c0d070341182c5980d004100280346500c100701ca01c00802081d030710380e410704556242d40d2003c00c0c05072207890000359032440c1c0b10000307840900240d00602009011500c40b030080f800000d0840d401211304400601401d08041000c61001c141d00d0481a00940708404030380707464204a03041e502c03010f0140c0015a580540750 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 573726151 1250 573724901 573724937
    0x160302100218210604030816022a221e1b0c060e0d11060f0609130302190813080303010b090609031c031b0c15110717070311060421 58
    0x4d8407561113076440641c5030802000c20a8076400c0034018006541103440740115030f1404c40e4680d4050b07818505207003400e02551004c1410540503404100b809140b2070341c0d6129001168100d11010441c488910300520404c44000088407007400c1c101d00d00ba15100482ca03c2e403813060307801d0f8255a010742c0c0000f031404400d1003034602d800340c80d01d00c00f800703d80940b900a41408007802a2944040640701d03402480c64114000f136030094004140001030b602c80200d80c02814030820210703030942c640e0420164800c1080c1080056a000084000b0040e41c1c40000400c040c01c2c0841039a040f5074030320250700d040080c1c00d420801070342c2000d403600340c061203000490400c120028003502d0729008207440025405918000b4680494001c0f40c000c8140440005600c0028440398107038030b01c65514200000d40030198a00d030400e50320030700300050030760300014603081995242d01e4010120140700c1d40703a40c40c0007690401d58540764201164003a1001b4003020340d4403c1e0b001020b00fa00440015450003016030b030301040305a = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 573727401 1250 573726151 573726163
    0x1201020408060109050c0304050715020109140105060f01180e0a0e0105070c021f022a060a0e040605041112090705060f0405040e030702062d16030210021821 69
    0xe11440d9000b0001000b00751071394071941d40c100c0702c101d84c41469850a0f403a6166211514490700c4003041c1859414191035100f948680c01d9103a212036544c8000452040d124060710007581c01078824103038081c6000c02076000b40429041000e02004041d901c51424002001c000da0040c00b211110b502c3e004071a0071104281300e0240304102a8880c0d40c580a0700c2d00510000c1c101e4540b034155040c070500706810205800050360310100107040c079007a40b403c4082030907000c640d00e503100c0e1540003400480d8041500f9009030605041180540d0f08000b801c0d40d4a00f004203540710a0f4210104031020030950030110b01c030402c00c56006554000715204146d0305c1001c1004d07a841544004d4003454007081c1030000e0710305801400b500c0c0c03825a004600703000858000402c10311540c050503280b201a02d503c2d084130200a0743c0d010308030b607074040740070340780d855100010f00f10340e140c140200e0060040d038610b9442140e440c8207480e007910100002ca80c071490100c1c140650301985a05c920039040000c061141606130070889 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 573728651 1250 573727401 573727409
    0xb1216050913090309080309061608091f020d210b01090e0c04080f010903020d080a14011805060307150e010210020408011416050306011419091a040308030a050612010204 75
    0x40028400f0080c20f0003854030030315400400c215082000f040415640e100191802c0ba500d21441c07000b08403407440c0c1044148100c11586402c00000c1d0340380b4a0a01c030031400c0c4a03841d0415001d8504100310b01074220745080368100308035101c07806940386001001c080d40c010a4614818100511002c0e11119400003c400880c0d0302810100e0001d4280101e4034140207000c2920905d00c001d00c840e40d490740c2d01948600070000000d00b086660b00010740310210a800801946042402d201265616070018051100018824040301c0b0f040c00c010502c1030600051a104582c0301c4080d11104d025948403c4842820310120310b41140300c5ca011864400340503100900c0105030407800000d0742c4020314a072460a0f90010500390110461390080e80041da0000100e0b42e201d0805d103040040310140e0305500e0054020300500300c0000f01141840f80b05140c00020071415113034184100c51201d00c090440510341e105a0000600d040001e0000ca26000000d4000b60340200005100d40c45070008a04114220b80150344 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 573729901 1250 573728651 573728689
    0xf0201090b0c0301140a0b0a230f0a03650f0303030705030406050c22060e030d120509010b0607060b0f010e0d0308090c060c01090c0b12160509 63
    0x410080307611170703200c040b5042c0c06c2d103c101e811454400181070350b000d452215070a100c1408400c20182002c00032450f0450111078107181c445c0c00000d040f481580040c403c01c0c1c0801d24015422058103010700780c002d002044046502624000340004241b02d08160b030031503000c81c2d40c828001c0404215000d841c04442d408a500744800d440d4141080b03980d441c0c24414174081e4000304140a040e540c0705040b41c2d4095040800841e00340c5a0b84007403e4648150040030030030440d00810b0f003000c020300004001c12600e1340d0740c0342c2e08000000c1c020142c0700c81e480360300070340850034491001d030780002d454000701e81c0407041c0e2000140d11001c420200c0d16a0703110032030032103503569103420702240c62424001c21208040c0a180404100842d41d01161500520b5000a400d0100c01c60026a5020040040001400c0302910782034450402c0d0385180c0c06040c401d501111032611405011a04c07a91000640302401c0d420010841b80307031501d030802d540003040b0040150801c5010807003284a520758807251000f2580a034 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 573731151 1250 573729901 573729907
    0x9060915150417060a05150607060b010c1a090609010c021506030a021503100b3c0c030c0705091005011404050613080d020708100c030b1302041a04030b01060f0201090b0c 75
    0x1174a4104a400c020902c5170a0f0903000f840071441c0d2070301c0d820303a00400e5000c6000540340162400589880395404c10007085016102001902400c100c2901c82c0240c60b00801c40d08a034031404001ca098039646c10340300c80180e11213407100d041e4010040600d80c01c1302000e000d94020f41400d03008101456068042c101021500000b0b206455144501c10001048440e5030b16040c15201d0403006098260f0042c0c00c01e444020303407030880007110b030a0001e2454020401c003c0b9a43c41304150450340702d4200c0800012940140c04000400e814820b807a244117521101c5600b40f0141080010368840c0c0c1d0645681d060502d080c04007040b40e8640c840180900c22001014428042c0780c41c606d5441c00fa03040b40c1d40340071908500c40400c650300000881c0c140f4201d4804000c1059480c0040407001008080c1c0010380c0104c000c99400360f00c40c0140d004205981c0b5040c0e0001c040d0b08160f40c007241c4c602c00d0303100040120719194010000148070f030a070b8011606062002094106c501c0d02d030000341031401ea60341c0d42064400 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 573732401 1250 573731151 573731161
    0xc0c031218062a06070e0a151101050103050c03010b040b091b250b130f08092803111c030318020d050106050112090c050405130f03020105060906091515041706 70
    0x30095191722a1103440c0c0342e400210510086603c0040e1807040864003071002e84c1904015004000030712041009100030480d41d81d490034034558a4410704505030081d440c00c00c41004a00f4103008031410003502914400d03298841c2c0501140241004120140c0c54505001500400d450f00750101505040c64039510010b0000e410030100b0320001400102d13030a10080140000542c00602c1c50701d030755400101482d101c10040010070002d44051800d4411400841c458140c1c895803000d0f6402920301034031400f243c0c41d17946001d202c1da07200c1004080d080d44284c02d448400080c40b80d00400030031184503503140c0703030000345501161046100110898981c3d454040c01c4c012542e1004255588003185031040c001c2c8182ca8503266184d000c0c5020b001d01403a10340d0005150702c01540b480c0c0070f240c0d0303011100010410346c0d820024000d21040d00c0c01740c45804000b0100b1054506100001e010b0020b060809012515440070441501502c00034881e000d4000d01c00054451854450110172403501c9002c0c003402d00d44 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 573733651 1250 573732401 573732403
    0x705190f17030403080601031d0f100501080303040f0b0a0b060d0f0c08060f010813020907120501061e03020a090e01060c0605130f150e120c0c031218062a 68
    0x41d036100000c80380c00e000b0000800d9103d1009500100e00b820700064030205100450b035003450300d1001000e07034800d4410301c0c0c000324400a200340c40300c0801e66040000380d8946c40300907242d00c0141d03030152817180001c21520202c0c40e1040c40c40d0b00417038080000104038031018082500340d0819449a01c03120760700c5e44d49a15000c041d01494801d2812450524480d10b0400000f44a441501d0107203030410152030000340f404445a98011801e5400070400150303807514080c003e21815031582a00c104501f030000008509015032001003c0c40100058100b80c0440081c044000390052929401041101c40c400121940900d10f154060b043c180e441003000301040c1000f800f940c1014000440d01e0745105000804148424440303480c2030b0344241c0030300e5038a0086070300300c01900b02c4064008442c05051002100e6500c084010100240000c0650f21003003542c800f0151503944c0303004003a40309402003181180450100e0a849000d0f030000300007600344008240b1100030016020400300741c143d80b0521041881038 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 573734901 1250 573733651 573733673
    0xd0515030c010305010303201e07050315010803070b0a0b0a06120c0905060a0503180d0c030e06120f0a0204030c290406090618050306250509030606060705190f 70
    0x20a083c01d1001703526541e001800c003060740071100720300724940b40d1081422409211480344045244040516111941f4010b919001d8030b00c12984030748154041c0e128426011400c1c1070403100c604001c3e6081140031789030714000060041009442c141d0380c409075003080da07480b01702d10040d100301e54421800b01c64a00440003215036a110305030070301200c0c4004002c40e56581007255510407962900d0381d20307511803016514013401e01c081070840318082c10f0303145094a940003083d03a40300d81c026500d02e0426240c2c2c03028031000b0704c180d035004005014100c0000341841f09941d050303030f008500d00c00d00601e41a62900d0305c480e0f04880d90000c02c0780101501c0c40d22084252810211800038407259441e141a18000c005040c0404921400b42071101030390a05111130545c030600700003008050b0680e2800e1034800ba5040100c1800a21400e011300d40c80d2240062034410700550f820030780040d0003084d0b0b80d00d0300740401ca0750b03410a40088403203101d620000c0c0c1007000510307081c10540e4803c3da800030070b40f442850560442d84e = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 573736151 1250 573734901 573734923
    0x5070e0a05030705040b01031821050315040c0e030106031a280f060b0c03190f020705011b0c080a1106030c0a27080a0b091902090c0d051503 62
    0x100360810034401a03502248032402c44a040f2000a852011800182c025040b20700c1c4142c0e541d002110703c481072100319006c0d80c21174003200c2203031550305020041c00e49842c001544d1840d450764455200c0000750800d13504c0300e5001d0403542480d0002490b44000079094a03c242c100f150061003485150080c0078000150fa0f0f004140300c2c110380d10080800298103418140d108001c2412078840104003020300d5103034422009409d490402c140c2d44c88103c140680d5aa010200581011480c104580080e500c5000944099551640034101c2d5910341001194008a501421310000703209070705c0300d8001a00d4540c5c01c0d008001800c0a400514864109040d059501131f14043c0601401c00401540303103500021600d0515441c00e08560402c0307a5400300403414040300740360310010300c42c41c0f000c00c2204d80000c228032003902c0740b10680901d5a42584082c1c4801c1c89480e04940c00c1d01c070000040c01444c04071402684404c9004405042044180c01e41c8240c58054030850b180c940c1d81da072003100c94101440888410 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 573737401 1250 573736151 573736159
    0xb060a0803030f070306092306040510090c03022109060a0509071a192721022404030c14010c0303020d0908032d070206070c030c0209040605070e 64
    0x86180c1210036880e40310040c00d048001a40ca800076403a00d00a03031003140602142c1e501041120824090040300e6180424034000100310f010000b0414907040c0620303449080303100702c040000fa1410300540301030080340c0451003e1580a0000a801411461285004405902c982c40843c207100c90518200900940352810840c10007007000700700c48002030340d001110006607400c1d040000f0148082c1040c014140d94083c5540c041588031a80d076842020000b90140380c01c10814614051043c10242012503ca00e41a0201c07100c0713640d000c01e42c04226481c0300c0c1d001070483c6000381805104108088091070700490000c90100341842440107006000c40a890b0208207101000b99550020304038a00200c1c00808054002075209203006c85900081c0c03803c2e42c00840d250300c0c0c0c10310380900c00b11141d40541f184c2071306003040040342d8100d072245120b41c080c1c0c10300d80140071242c8030643c2c01c503000d50343c444080d41485040c001d40c41c0140c44000417181320368080c0300b002541d410240002080105800a09445 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 573738651 1250 573737401 573737419
    0x180103060e0328050408030d0b0306060a030213020a030e06180105070906021c02030f0c0715020601030c030b13080309060604060608060325080a0f0c05040501061b230304030b06 78
    0x240c94070100654452950342c65003248081d520b08003102c1301c0c852504032100c0c0780000300c7c50744001c1d407060300f105804c02c208406561041c0d07035220900c0030747c000340d200295000c900c42c0c0003040c00c119207600828403411980b402084800c400380c0d000d46440c009440c0b0504a41c910074141031070f088280314040d0401d40c0da250401c412427402d8002035032200c0d1118244640e00b101d44090b41c2c3d0a000f04101c0c0c1c580049507104a403921035800b1110346901281c840c2c02501e82400a8100d4140d1000c0b4080381030700d1340603000c0c0240c0c074299140d1003009100207214a0500c031902c3e01d280042a005806148a142c07070038010100d600d0200184829201d050784880180000c0c2030034010682e0b008036400786e034011400d0945502d08980001c03031a5007040361b8415a40c0d401744881e080140702c40410f803400d040e40107000124030b0700da5540a100440307100f4030408002418a540030100d1601d100d003c9040280907040c150b4001d440c0300e0b102a600b10002031605d5131648001402c004001640f0149a8002001c030740d0414 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 573739901 1250 573738651 573738667
    0x2060712090c05091302040f06080705060f040e04081201230d0506060f04090c0605043807080c160f091a04020901090f0603020304151b080604020702180103060e03 72
    0xc00baa51600a07144250744983c0003410300303030399400c1200c01140c00420034004042a80d1110000340040d000c2c40c01e10b4010380101061900707102d400c4a403944403201206182600d400d03400507070300b2000360080741c0014040006540340c00c4001109400b0b00f1f5410410710388042030314050080d0307248a83c083c60190034000460408202d022036881da00c94819a40e44860350b00440c000382c005c0810450007840304119450115406034070601071701c00c0d1842c1c7e0820001c01042d1200c0c28060b880c5a842c4400d41da030b08203203052150899075000e054170601c182c1481381082607824109040c00300003000c07100700d4200880100040020400c10f54000d0560110403c03c080c0042c0352145030764540041140074a0b00051843c0250b44540e0340c050042034000000400c4039101c00d4020060350080c3d400350340e46e1441000030a05030b010740c420f140c20a46000142032180000905c150b0310a80e0041c20264010b500380710785405601d807056410030340c140c5001e004000398107601d443ca00302e071200842414a45e009001000b = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 573741007 1106 573739901 573739913
    0x705120c06090303130305130803030f040618050a060207020f090106030c0f0305060904060911100210050f190902040908070614090c0112020904060f060206071209 72
    0xc100b92202800c4550b240026100816040b0851810100207401000107200c0019100c040c60709207556030543d036055400442c0d10003400215181080208085031040030080328800c0358201868041d40c17291a925040000d009201030f81c00500c02c0e00355a41e0043e0540074020040c00c004480d80c480300d000f0003500800c2090300200b0360503c3c4050032039020707008240c81480c002d8603400155a942d221800a0004c2da801610a00308c149449100780c0c0314110b406140062540040036004d811140002c21110002c0c2060155001641445614600e504c0442000720750a140411040c500d40000b40c02001c0d034940080007ca00010844c3c10894150401d4040c9182160302400a40d564a1206d46030100030303006a0005a81d0000380c203003108250301400c0c00100c090000a401741d2a48110351440003c4c0d003045000da480001003002d0564030120301d082c14803072800148000f403020340d940d03 = true := by decide +kernel

theorem cover : BRFrame.Cov 573561151 573741007 := by
  have h0 := BRFrame.cov_init 573561151
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573561151 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573561151 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573561151 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573561151 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573561151 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573561151 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573561151 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573561151 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573561151 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573561151 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573561151 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573561151 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573561151 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573561151 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573561151 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573561151 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573561151 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573561151 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573561151 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573561151 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573561151 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573561151 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573561151 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573561151 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573561151 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573561151 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573561151 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573561151 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573561151 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573561151 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573561151 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573561151 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573561151 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573561151 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573561151 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573561151 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573561151 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573561151 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573561151 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573561151 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573561151 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573561151 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573561151 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573561151 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573561151 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573561151 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573561151 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573561151 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573561151 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573561151 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573561151 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573561151 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573561151 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573561151 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573561151 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573561151 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573561151 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573561151 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573561151 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573561151 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573561151 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573561151 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573561151 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573561151 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573561151 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573561151 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573561151 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573561151 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573561151 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573561151 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573561151 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573561151 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573561151 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573561151 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573561151 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573561151 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573561151 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573561151 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573561151 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573561151 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573561151 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573561151 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573561151 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573561151 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573561151 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573561151 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573561151 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573561151 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573561151 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573561151 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573561151 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573561151 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573561151 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573561151 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573561151 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573561151 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573561151 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573561151 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573561151 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573561151 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573561151 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573561151 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573561151 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573561151 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573561151 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573561151 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573561151 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573561151 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573561151 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573561151 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573561151 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573561151 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573561151 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573561151 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573561151 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573561151 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573561151 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573561151 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573561151 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573561151 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573561151 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573561151 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573561151 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573561151 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573561151 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573561151 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573561151 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573561151 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573561151 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573561151 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573561151 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573561151 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573561151 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573561151 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573561151 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573561151 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573561151 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573561151 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573561151 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573561151 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573561151 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573561151 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573561151 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573561151 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 573561151 ≤ n) (h2 : n < 573741007) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
