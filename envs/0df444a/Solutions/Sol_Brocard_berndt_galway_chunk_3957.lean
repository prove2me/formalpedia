-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3957
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:10:17.600897+00:00
-- url     : https://prove2.me/submissions/be0e9874-6ebb-4ff4-ad7e-8bf3e166464d

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 711510791 ≤ n < 711690647 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 711512041 1250 711510791 711510823
    0x105210304051c0507151209050d0e01031104030b040b060901030c0915050301090c0801050903040803181503070819050705030402042409020d111c050408090a0311031e 74
    0x74401c0c80101c008652910388000c002e48101140020034001048030010000911f654418400b40e419107004140c480303004d400341198202d4000488210702914144681d8401030502051f441e0a01ca580042900544d0050354500b1580c001c02c400c00801c80c1c120f40d03001e131080b24809182d50454032084150100d038004e06440c683e443d4403004070300d01e00c0780c074010040100600a000380c02c41c0c0d290540150301d052103074255035801d0030085000400084240c4003503492140055007011305460741180c103298015003181c0c00c41c1011460b441080c0c180c0c0300440c400d414944a80e1124201503007084034624a8038401d1246c10b01d09428000030a0b8402c0499801c960111400705581c045075448010448125015210f040780c502400240d0903203a0300503001c8005855420010074110b040c039080c0912841c1c001015850880e81d400c400b24019610041e0810b0240d03150390308081603040401c500e030b48540c00030b07a01881d02c003000306410b180402001c201c08900b1204851081090180695510b6400e4601506 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 711513291 1250 711512041 711512059
    0x50a090e0f1c081902031305010e06010617180601122001080a1d0f10051b0a08100b0f0903010e1522050a144c0c0206010521030405 58
    0x810080c0e04404810b01002c2c1411036072410030318054404104a81f07012038a035400d205072801d0211001c2100c90481d110340d00c411000019600c00e08034034030b070002c1c042c03000c3e02500440d841d101c0804004150103040208500144020103080c2008945069110006010b1000c000b031480c50341d001c48071a03000044c0560100d4a07031042d04d10f47e8180800348505003001d01c1030401e80d1002030b800050310990108054002c0107561a41c4041520700041d42c40403d5000c0002c10840c01c1061050310241d40c8a15030816004540743c84041501c001e600016210345483d00c0883d12a1040ca02846281d40c4c503040e000092071840710f581940054650010b00300004d04504188440d0400b650325070844c2c80c5640401a5841c680c010b04c2c0614041d06418020b000d1407103030707600300c188040340f894104007901d11644401106540b1003882c400035464003c00c940d0383c6400d4841c4c1c000a004d0b68040c030f100014540d00074048071b40c1407030140505440800c2158002c0382000c810002c040c40c000c0f003140c05540d0161141d03a0 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 711514541 1250 711513291 711513301
    0x3051612270e0702190b06011805030d0c0f060509031e190f0309150203010f060903030206161e09140105040f0512010204050a0909020301051b1b07050a090e0f1c08 72
    0x814004101e00f9140b05d40300c180428410001540400785c80792000741c07241005600d00815107410310744103000d82074040d442488451540c600601c40503000a1040c0c41c9001e842007569203640590742c041d44c603e1665400401c001c030301c580d134000c42c5040140c2115165401e009040c1000507142c0c501c150f00c1807d01c100380c1c1e44032050b148250003001ea05d40d0488500c000a1004618200081d8404d101c1e66940300c0c0c00040c0880c0c034920550710601182d13056401850903455180442101c9112006001c044c0140501300e4405035404110074150300201f034586203069072030320380c0b005203c0d048034600c1410050b0421060110306a003c00140694805403205004c0f88480025180284625000254851040c08001074000580d406c45a0002e00c260002d000c15140e0310000050034480d10200e9200e84011301040303000c0c88418240c201f500003481c0464085035941c10118024040c603800000c20981c071410a11220071041180c070b0250300c0c2400080507018411141c5000c64051250030108106911011407 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 711515791 1250 711514541 711514543
    0x9010609020f091e0918070f080102090f040c02030412060b040213031a22020d02040e010e061b0f0309010b1503060f0a08070b0703051612270e0702 65
    0x6000e0218035804564032981441d00880c1604281603040c0f180d180001d40e5542c9090400d4402d01c582c20203440c202d1039803102000e64032510380c1580d05012601c52031400282000d12683c102c401404407400050b0707034104807003d002c18407103014481c9016600304a64039085540c00001c8400b11407005a98940c640705920b01180908414082e00c0d6005001140480328082850f2980f812203100d803121801d0803800d0b00808519820850780701000c920380300404a00500380794400c1207400e1000b0f21031001c0c0b5411341d00041c202e802106600c0e405a54501492001060410429401a05c0103454a505c82e100d820780e1200c510800042d43c0d48004040302145113024250000020201c0041001c0864410040c0003201c50300204c44c034502c40c4c42010b0290701c042c2000910350065a1104001d41001401c0c80c9102000c1c0d03100c1603003102080401c1103a8641c1100320080403800500c10300040400910f01c41008008090080c01c250500e200000d034010390514100990045400c42041070b42240d03580c950603 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 711517041 1250 711515791 711515801
    0x9060930121a03060709260d0c0501020c0703031e050405030a0303020a090e1f1403100209180c0c07051801030f0f05030c1513081602210619051e0901 66
    0x250340502c0746000380711180b500681500c040c0c442c08005c031112200c00850390b08001d42c7c54071070444541c10201d688400c9602c210244501d090007603002514041030100c1c0c00d440d100d00c0b070b401507000a8210054482d200480304e08800825a6454698101424240081d07101d1005010003401d0640c00220040140c0c02101042c0081c600c07030302d100b1b446140c092003014814070204a448a622006c2a02044402c040f400010b144d20016005100b4952011183d8000358807154009078455041d01c11b601180c0c1c22003085a104e540c0314a507003511442640051440c085d031541001d80b0580f0800108038070f0404c0448540e0440b90441d0300f4042028050a10140991000300068124040001e002510170000580b001414182d040c030380c4802d565407001a442810703100002080d0f42c800300100b003403036400c5100c2e111010b40000c0520351000711046010300d881c60400301c5105190028000c210750680e40010000001210102c10f000f1460070750784046080c60700041c40355012074400e0100b07212480035402 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 711518291 1250 711517041 711517091
    0x207270b041401030302010c0e1509120f0f03040e070801061e0e1314010b090303180a05030d090f060c112205090c0a120503040b0a02010906093012 65
    0x1601e0b1696181d04000380070303103500030700c020100399200070005840c200300402046411903410f91500f40031307001341045203d03107502d03144400d54030822502441c0c0300e1040c040c41c0c040c041c13040000c65441e460074240c3e61200300c0081c0594280448000104aa42d42109000d03a00d9001e07042071074403000c0c0b03220007030340c841c1ca0a01480c2e4010340352154001c21060700b68040140b02c0016280c0140d0750307a890001400d58071800d283c060301030f00706001c2d80450b900320480654100600400800960b41c85401203451b010b048808500001c4254208024804080d2500d0025080d40d140001c000303140d40c0c03104e08040e40c4145405001d411203e8801e402a5440c5407100f0302c50041c076005000d07900b8400c0600303540d41c00c1c035400117209000351200000c4981040b1000450554001d0185003010b00d403d4004002e5080865004259500d900452780014000e1040aa0f400c0c400c4280c075890f180294200b001d121407030032041d00181d520700c04007004150040111560000078450104000b5030b03964007003a4003100e03245 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 711519541 1250 711518291 711518321
    0x1050c0304350903100b060a030e0c0603070207210f030813061d072c04030c05010f15090218060912011a09160c080904090519030207270b04 62
    0x14942a190b10307840281001c0c581182150010350305000c1c410212130000c3c01890f4001010030900c08d40500a4104e4110703010240c0a54002042600108446d50300c03c48618005811070740041c4040311032062403605207001411b0880d610740840c1d854680a05041401070140203071a0001a4514179440308409002d910120900682443c0d000d40c2140b40c94240017413250b40a030f5000840d42c075100c02010303840e508a1480300b940140c004410035694400c0900280c0402c15091403510206009028410803144007100010b402d14203001c20764110070301c603004800c42074010058a000c0719070904020700c200c802143c042c5d550391201d000080e0322920301c15880c2050b50030400e501032345411009100344080805e4641d812687c0e035075102c013103241e0058801c50001c510b2103040e101c0868041342c0039107101840500000341b000121348071940382035007000d0241507014054601000701541401030708014815240c0441c0415800404550025080b015140c0143c1d5030307460704e070460782e0b59801103586000808 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 711520791 1250 711519541 711519623
    0x121c14090d050d0905030d12020d180f05070b270f04140a060509060a06050901033810210209102003030f060402030403030605100f02070801050c0304 66
    0x1140c45034030f542000010401040318180001605d050101c2d41c03290190f61a600d0700d0100329221803010080d0440c0d6000043d41c0d035900381d0000701410350300715400401c5c01030900c801200440c1c0b802c180b60900540010566440502181518035050381400a914911020000c003400380000444d10310741c0c4088140e54003508000700c0703034042c1c0c50742c2d5000b03801002031100610049072500180200000143c42c0350b60042e03410001004614840c8020b4620040140740c00726003022108d006501d070400b65030751500c401130560703110300180050b68010500054255108031070290850b00c098031707005e4100d248820140c45005000404203656048034104030703008002408a54078804010504040b050000700c5c0101c0800100050310400001d41c0e101e03244681480c505941d541c0144000f0f5000a8800c506042c2c50350030120741c940e9540192100c071002c40d0760b0503198840329100203240074050760000e01c3ea40d14200074403081d00c00500489501075008160b4802c0d18040c0d1040e1416941c1c05501610022100 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 711522041 1250 711520791 711520793
    0xf0301270308090a0c030b0703110324010c121103070206040807180b0603061318080904110304050c19080102030a0204091d0714031e0606121c14090d 66
    0xd16001860303a00035500d250860f6a1040d40759503401d801c0c0300c084c020000e141410400102d4510120b60306c0109440c0100300030300fa4148491594206580152140311070b400e80010241e1402d0400a4107130b401d18088103010644e44401c20700010207a50303803003001000620020071050030170031642080d03405000f131941e440e9981115078032800d150085000c61103941001041050250050201003000208401d1070340d200c0c8001c110720b400b1542040c4134041c0d25204525034120800c450010698007544d196a504c40000c01003108481111600a244a00500502c00845d40000c0c05004101701969212418031b2001ca40b0300030345e1882d034006a0b05600000402c4040030940d00640120340c5030900c2070018a0b00295140480303d00589020401d500018003000b020341c0381c0c2e01030002804060f082d1081211840c044c00030207503401110300c15a80c000000e01400341440180c40d1100e00c00c040c00381c504c400c50504001c3e082e041110310001002840070040d41030600c04030407900700e81c1c0e0082a5000103045 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 711523291 1250 711522041 711522101
    0xc1207080307020c0102061e060109120b01210b0c07080f0c0a15020f0a030f15030609020f0a03081605010b0901030f1a01080a031803020402031f0b0f090f0301 70
    0x208581800044c042c41441072225400099501e004a044080d103510200e0002040361803a03c00400035810412b4180d400280100e01c5070010340440e000b401c0c001400d6042c91080c2c250a003170302d060306062501d10b940d0300c1c3c04200e00c0882c042d00701400030038050380d41610341070000c3c0502960091910756080007801c50084c0c6000104102c02520a02011a001030700140d041c040340504004101404001c00442c10014465071140004d640d205100050504030a145803111000b950400c80e880359a81d071418041d407078015490000c001c82142c4804100d0b0950b170750004640200c96100040600c0d141c5041d0822000390844000d01001030710070000d66030f40e800d19088074a1446001d03203400000103050b80b450580791003514182d40030480144400c1d102030340c08550401c4400940260890500000700060340c5600085005020204480102c050141402400c07200243d00034040640c0400c0303070001c1002da647c1603512002c070882d540101034005402180c003500090302c0355920b50704442c428040e2165 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 711524541 1250 711523291 711523297
    0x405191e090c0e0d240e03091e03030a050307031103040b06040f090c0b0d09080a0302030610090f060e0f0406031b060207051818010504050a140c0a05060c120708 71
    0xa07811030620400d0034040064811007203c007015a0071003040c030b4a010101e020b0058030001c03041c4018134400f480c003070005400100c1e000c807600344000d9000018800b045141c20f0300c482c000301d117991100322900c812800c00250f49120f5010783d101032040103c0001e90307840c000d6100d1032030010100d00065486c585480c00810320321088403080e100f50724126210042003068880c8500300d5900c00940c002031414044034040030b812410310341b1052510340c071410000403070281c0540b1040c810b9450158403420f005c1d01f00403008040031401420001503140800403500d2100c1404100c500500303040c0c0c0e180100001003004052407852141d001401d0044c00000c1204003c2c0e00e10403544000021b064413034490000f02e03110b00c09072045690001c0c0b5941e4440c1d240c0c4c0c4510100d03400000f02c1307003040c10403e82d000700d00d400d41d4012142901e0542103142e5000c00d025420f40c0d01c0302d013800d6110140403800302032000520420340d81d01a0138010320780802c6c08404480104082200ba04200c4074607603d400c80f620b404e10150f4 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 711525791 1250 711524541 711524549
    0x9080706120f020712050306030a081810020f0309060a0903122a051e0c0901270612060b04020c1f0f090f0609020a0f06050a110f030405191e 62
    0x500c1c129000c440482c8502c01c0e20f00305a4000740c034811408500d40300312000d820140003640d050080340d00980005614000030a402c0c0040400ca02819058104000600080e1040e4606540004540b20542c1c42d01004850070010100d03009600c0c0c1c21200303400c5850078002d400003444000e01c085135500054000b40c0400c640503050360103501920009200501e460030340c10340200307940d000d4280e03401f5003400400c210403814920421100103040704000903072100020380c401440101c0140c40d860707150b413030307034425410910407010288035040c5001c4c4410b8140707424030406821150313240754000d07079651540c0403203018908860403503540e16403104061600046000401240d14540141410b103054a4094402265000200046102520340390b40c5c024104078035040344d00c1904200c1c0031410656140700b02000d401160b1390785c4c1e16171000e800d001d0203010041c01d0380e035a80d07030054445203510b941c004100c03003daa0080d0b81e001d07a640000306400d00c3ea001980c20441c10000000e03600149503840e030750910212 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 711527041 1250 711525791 711525827
    0xa02030a0f020915030402060c010207080a030506031c08060a0e0114180403090e04060204030606030605272d010c0519080601050d0b0102030702090c0415050f07030f09080706 77
    0x1450711004401240700d40c10615401c02030045000060740c00407405164803d0024224518280d19107203170500320b0780480801c0b5480701005c01e010228981c14820168000701c150024000d0b040212540305034641c1c116010810800210b0000d04507850340700d100741c010240c1000d10259035860305030750050101d140c0c8100b405070440001c80c259901c4001400c1e401030340c00d51580c02d411b45c1480011320f516103000b0f0003518032a030200b20000005205100d032100844c00740070000360504004500105036440300c903c54444000081048001040104110302105060040450b0181541002c1302d1150f00092419050394a844042d044a58115004004201d0f80029501c910610454103540240c0c09540380b600003001030000300c601211542c4461081c0b201401120b04024140e0300264100f181114480400c043c0441d08005101101802e4090008581881c034201141815042182d0241481c0a01040000165860380900803509400a010f480041e110f4041e1941e6000d014420000000011 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 711528291 1250 711527041 711527051
    0x40f05011a18040b0604080a0b0105091e010e060a0909081b031306030c030608241305101a0a0303050c0705090112020112021b100e031315170a02030a 66
    0x69030003a0011281ca0303601d0724a039864042881001c3c000105130b0413030b0180d00305404100c0420211030030010485050310400c1c601210350304140030711145008c0a443d1805004450a900d0310040202c5602419a02e61806046a075500d040009a490186170b00800016103002d403102c0034012100300801311100302d518900348049498218a03900c0c031034000c1d0b000302c8101a440a103c3d0340e2194001032038a07140ba1902095294481503d00d061484148004a9120740560841d142e000030049081d48501507020444022040383c440f00c2c2c032040319844000314555178190b408146c0c480300700142185031001d070816141a0b181d20b0007900342d40c09803030307012820320034640c0c001800c5c9461720685060301d0301d01d50703c40b00f40680380d8010b42d425402440c1c11043d041d024455003441c401581d440c0d44508445100618138a03411940b03600c110b540540c82c10b44590420020940c9030103050b00400e0440f2854541d4a0b5000e0141a0440e4080d01c01050245018214000d000e60340d000364000d18040c80d600001085 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 711529541 1250 711528291 711528329
    0x2041806081b2205041e0210050f0d02040b0c010e030c0a110a0b03090a0b540717060103020f13060503060403050304050f0604051b060d1b09060905060403120e040f0501 74
    0x10046c001d20003035004a043c034481030520310400261594620105a80c3d0a00303203240d4015059800940181500320008241419450824080c4602c0c1032610750203540307054244100c090301d5a04017000079054482150600f582520348100000c010040d40a1306503e03402c004030f03400c2d00e80d40078030340c2501e01400d00804550390b101035415a0381907016102007160884092061012000002124400305d451062400b080a42c0044400c2c091089090081d041003401e00301e4000910782e2103519031841e940a4801800180c6410006e0711502200710f40d05840700d680c02a50b140501042e801003605405400d0500003090780200145016610860646801d4000c1854039591100c0490700076210f03034000c3c18a00d8201305142d030308080d400405884246030000503180c410035141c0000407181c1e1100c64883d452030559102144402406031072618140c0e291910001030700e01e0086000241000708a550240c081600580b002d201941d40604107114900842a0020090109205ea486010a00c054001c = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 711530791 1250 711529541 711529583
    0x602040302150408100906180506060301151226071a13030c0206180d0f06140c040e060d141c020102090303032706010902041806081b220504 62
    0x400b0303640c1e40c0d0000c00a9141240c2580c0107412040306c2a00c1da9540c1d88071f0f0500b18000c00c284039840303501074402800703203007884d50501d4215800d04880310b2150b80000c0e4103005444000c106682c0e89074110703c0031005854042510015041c640d2000e003090140001e6102c04c0000c0c80e82800351410742046048015a100b41240c0400d0800150003800103610124880052a004003e04242c024010040f40102c085001041000000d14007c0e50240801d80030001080814015120740e0008618203030541c1c10004402e81480c012402550b440280030400204540c565424004083d074214004441c1f182c040d0310b1240e1171b02540f029007001203034a14211001d26005008440c800031019004510315030780c2400001100c0ca0107048004e2000c000300a112801c40d0421805018100c0c2010045e5560f00c0c011404810220084090034402d044c010f00700540da001040c020400302044400c4c110301c00c050300c0001d42811244000708100d060441500b200000305600891080d4404e8010240b03e00480ca000 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 711532041 1250 711530791 711530797
    0xa09090302062a04170106080d0206070c0303021c0e07050406180e0304090207080d140106050a03150f06110601142d030a03030b010f031509020903030c0307060204030215 75
    0x350150384200c0c040358000003d2042c0840c2ca09500080280420400101440c0759202c0e0307200651410405c04442c00908013841180700601c0074100502481d900400069116200100700809000c58101d02c0c030203050280d01102c0183c0300aa1a000030640c50f021440010f040c9407210020500c178015010445040611491003600c9101564420300050200050040c1208883d410210700040c007002845401d18009002c2c01407090718a03903110b42a4280ca101280c403200e404c1e101c04c0030104010001c1030382040494201980c0c5241c0421880400c11801040304140d1b80030b00c2200c1039030540081d42c00c1c2d00c8061817003550b121606846c116640c8684022840540c020322542c803003c0e04684046c0c8100746910888040c0c004401c051105440c140040c0c01d240300d40c0f100f0340200361610403510780d5603801003400018015a040400284600c0300c15140240900c4c0101c503405d82e800140e0650a690030025033343d40129400442c0d65944903803500310065005848204d018540d41031030100074101c03c500ba = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 711533291 1250 711532041 711532043
    0xc0301171204050d020f0306011202092211031e0f011401150c030210050103080307030b03160306050c041e050a0b1e160203010c110c0604051c03200c0a0909 69
    0x4042c00c0506200401c003809404038400ca901072a4002409a00c0e01d040c89668000c0c151501c0c0c1c803039500c003907006018820b000240300610458800c0c90841400c503010300e18810540d000761100300c5003101c043c042440c144a1150f0407410303182002410b03003010742c0028050b1503008114001e010381d120202c06a50010000c0c012002591040c40400446d68400d0340c0003034003e4001e2041703031a07440c8403408400c125642070f0010b40325500c00200f0041055094014a0740011040c0e00400014540030a0084401d07668040140741d15240d10126555180d031030180d03005000701d03180b204200052400a15160f4031684a41e5001e03c40741007002482d10768800903075072100441c0b610030725400780000110500350300c4180300c0c540307142500b8900ca026880c00d1040603244282511405c400d030b0000f0046038908080413190a100c5d99082105000c2621941c500304d00c0c0e40286000f80400c2d01d9240b9040d2060007599801d0081ca0303031003440241c000306c8001103c555105c4250384110f10292100014004d48041c040 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 711534541 1250 711533291 711533323
    0x20c010201091505041e0c0501140301030b040204050a110c030d050c070b193206091b07051c0f08070c0c050d0510060603090c0510080705210c030117 66
    0x10041a040c02030b904030540c4075105110034181130600b405c581480b00c03140c90061f1007101b40c502c41802656000203100341c0300d00c41c440c5c1d0070342158916581c01410040003000240207940750804a4980c94550b0400c1300310044414400380c5030643d0307441311980c941203281048105420f2801103507450400f03004482d1030540090710b44c1d0003a079401148800311140485403600b299070326044200c070701841c0c0c1009100624030128000c2009a080700c0c002c1d0811001c0e03e45445004200c06200301036002c0c480503182c081134484010b0303d580355410300e581400c903031085000010003000b4902815a501c040304d401c00d803d50340c885164507103801c50200c0d000d800b00e00b00100b4248000d401400b241c940101c8c1004800d2080e01102c522001648500d002d840d0942d0007840070903101d4200030708210044004078051f1400341c40764001007003481c000418500b8007605840c01c1c400c00040045d2490004400800c10048808000b801810300500c0c881e2030354000d10508884004a402c00380761850082200c210f950700c184 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 711535791 1250 711534541 711534563
    0x9010905041e050c030712150524030a0b010905010314010203060a0515090d0507090c030b0303040e0c0c06190c050307020a030807200f07080a030f0509060424020c01020109 76
    0x22001e07810003070b204441074500744190501405940e0b002c00411002e42010b6001504a5440d450284c0e80a0a1000859087c038100300c104000482590382da48030b400001000c00c111002c4150109081902c6208017502d0307402600300105e03c2b20599005103041b20721501c1000c00e00f4148140541c200d000503038810390300c420303103403420085032500782601c803d00f0711508112450030039998005400d84c001c2040c100c42c9500200e80807c01c01680b80301c0c1000c86940c505050081520035400030b5140d1089000e56468090b4010100d00c15044c02410350f044d000001046800600b080396030540342c02c5080355003010081c284400c920125124a00ba01d01951044e001082c2101c41e56905a4425000070309450130002c3c6065488a02c008240d00c07607800001540c042c0c101840b9880d1910b0901c81c403a08903800981c440c401100009901ca248814420110b1a2094603400100c3c001a00c510440e80244200700d962a6a2020300d9a1801d4185402600d50202d94610b1099001a4244c40800802400e800001c2c = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 711537041 1250 711535791 711535823
    0x2030a120b0a0e0703060608070e06120903040f0303020307060b010e09041101020f010f1b030c0f050c0a02060f090406090c090e130b0108030d0c08011406131505090901090504 77
    0x2941000d0048400140400140c41d143d12190f41801000c40b04071000030303256201017000f250071182d13054202e0080c3c07821150b84001840420480d11508400d5122a100d800000b00d10140a0041d54003906503d40381d130120681d6418029500c5e00421402e641c16840c00c0c01010056000b8282c0c069144005804000c003580d607901e07036110f000c900f455418190b0141000e458500d50b020b1243c0d20004001140026419240e020303041550040002d01c10103052034215200c01140d0002c84003200010b403031924590703c0b0420302c8060b0401819000013900000c010a40c0e41c60008030308043c210030a020390703041050701d56486c80c003019520390501200102e040300b04c05111a0341c44221a550140110701d080000c07580399540c16100c0e900c26400340890f60000700303004000c0c0c40c0320702400d068081d1615105101d035040030700d1000b03241d402d03441c500e11a940009800480005520b04d030001001c108030410104801d411025045500602c6000d2240780701c5000402e100416110b03c070700458101100112100032 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 711538291 1250 711537041 711537077
    0x7022a01050702030109080d0c120b06042303070e010e060307140105070317010806010e1e0105091305070b0307180b160f0b13030e0d0f031d0402070606031202030a 72
    0x10100e0b06a80654a078900d0b4000306074102c0051000b030810301d01c0007403040b0711280c00820741080e071030204000300d003000c040d4401681e407001603c0c01c1d0b904041e1003d05502e003903411b00c100b05104076486901400b60355000210f08100d458218125907008540040c0e80d920f0740e0815440c2c090394000e140c00041e8182030200c29501c20400340054500c6800d218450b090a00c2c1c0640e051003090348092400d500640050008445803110720f50000c84030241115400011490b20b094414140202e60003127030360900150403000445040e001c001c2d00301c400e40d0500ba07100d44a00b08590300440f44003010840b51030b200c0583c20f40c0c140d0b01d20203c0d68407801c254100b002100b6564092820038005440c0f40c2d03184400e080c007040d114940180980c0070341d2035020340e0020a1030040e01150300b00d00d826110704602905000803a0031988030520465040c07500080d803461400d2403030210083c04044582041c4081600810031419a001d241900d02415090400010780c407c101d070341e44104040c810010b6100f140b4000c4101c0 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 711539541 1250 711538291 711538297
    0x109020a090314030702240306010f03140a0c08090a030801050d031e0909050c07030c0f02040f0905070e28090c050913020a05030d27030b0106020607022a0105 70
    0x412481c00700c020690341d4840d14409006001c0b0f449140d00300090074030031850701c1960511100c8602001d05280c0c2100110402d4602000b09810b050002c0144082c9189101e54400c0c00114050020000942040350401006101451036000419024004241c40c841c000684611300c990503a108240c682c01c2006010600020040840c240014890341ea8001c00c0c85809144e0940700d02d9407208405498040b0500c19920060841e1400840400c40400401c1e41701e501c404585810200c1d814003030041e0f101080081608842006200340f8080c190403c120012540c03004480707401c0c00a060580369106403011010684040540010011603240b061a40c40d801003807105004910440c11f1341e50b1007003c600600002c4401e450743c100711214100441ca0b0510314800074001c103800500760324081c04000f40401c08001040202c607d24005d402d501c41c0c40b5002c3c039502440d80718040c2202e0396540c0c14007a580705d000f90380030005070040c0701020a04110250a503c46040300c000320104000c0c0c9140103480703d41c = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 711540791 1250 711539541 711539557
    0x1020316020111030f030405030a09050109030317072c1306140d050708010f0b031c232116030b01020606060d0e1f0b091b03070c05120307090803030f010902 69
    0x40028070417400040d00310b001840c842c9004001135503454100384c40050140031681c01090600035551024400300c1d030300000900c00034421007141403a50f00d80300c20688110011140000750014490400c414032045c507083d880f0b0460042d25500640e210f030401c45c0041c3c403030a000c0e4011220842d505030700d0a28100142c3e101003400344040e500115182c0864031b0940c0c501031314a80e07803240c5800407078283d401d081040700b043c0b12003a100701c148410780c40c1c03004090060070080920992016400e9810003c8200c1c1110408206100b44041e074000624990512034000c49103071940c5145c0d01004007045000c0d004801a003003059019000b26601c000801c001900a001d40b0480b040e03480e400d9060300007040018030102c0705050a111507841c21031840c0d105031030400010754018404401030000850010b100b4001c05150503c019490303a5400710100d07000080c12030060014441e800001401004c410300443c026040740c1d071144c0e01c590300c81800c156a0b210903076014246144040040154a0180d8050142c031 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 711542041 1250 711540791 711540793
    0x2413030e15040608070e0d1115210a0e0f0703061a0909070e070207142e08150405041211010605060c0114060301090503040e13021e090601020316020111 67
    0x204840c807600d400d198209412076404550028140709403150000ca6140a994084410414100303190344c03004010a11090040e0103051500f002d00c9080b40002c058030f104440740358000400086102c07003007143c600240c0d1420302283c546040c0070a03c00000c290f8000c08241400284201e5285503038150061030000a140e440f4040310311a1885513546000d400c0c0603100c0e000042c04002d0821483c40e00444000d0512821340d4031854040000380101c2e0028214150200c1c0d0010702c0745400c0080800d0f000007a13280c1080200e81c050700800c0b058121100c00e0040c181e00345400426141d680c24003048400a0742e002d072000107007080301d0510610500301c0c1d0007055040400819903a41c0c46020580c640c010885007091651030311105200c02c1c8002000c41d901c408110003c1c0301800f0240ca841e1b07128452070056001c41144180017644006d81d4402c7c40088940c06044241c1d0307601c0c050750105001c00907100f000d110740c10080214445600c000265501c0c0c0a0f000006011030f44260700658000300e003040340c4406 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 711543291 1250 711542041 711542059
    0x301030f020f062a0c0f0904080f03100f0b03040201051213050f032d0306060703031e09050c220c110607080402010215100e061903052413030e 63
    0x2942c803840c000d002e1070320416000c00004241e00692a413002e0350103d03054080d81c03083c54000c1079603980e2400380c00700b06d5080d45c90348081c0d12541020f00ca18400c07400c000e40b0b03010b000030904c04c5000c0c0040c01c1e5001c032107400e0025014640c40d00303285400c5203c1582c0c0640083d00601c0002c2c2c2501c220500190020f00704200c441c2c207003085594030360525a090303c0070b88481d040451302c46010b251844005014540d840068602d885035400c054640f03020250800740184804960320007050301031342c40b40c0b8054405034400e00700c604105103c40080c080d0468200c540f03004a41c00504c1c0350501080c0c1d000c0680003201903107841d03d030014280f4020103c10007281c0401003102040c20b000e01061111301c1c0220015515146103150500000e403130814101401c01d034a03074101c002c02041c1c005d00b003854000cac0d900380c01e6100c455866900004a00625124800c101a0002c031000000c00000148900c03050105641c15290340012001000f101c2d00c0844c1c5100c21068003110180000b03128138000044071800501c1202 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 711544541 1250 711543291 711543319
    0x60c03071205040302101a030307031b061505010906052817010f050901050d03140d110c010509060c0408071208041206020a17160810090e030310090e030301030f02 72
    0xb41c860a89041d009600011640c064500241c01001900e100d12020051100c0603400820b40c2c1e07105000c000b50402030380d0000c404004106050601030036810000c14005103a402c24103080e440c180d4810240441c00c090000141c49004d20180e0351911003c1d41d000200b00b05060181025000c0c1503070540402840005052400300c00658141c0070b002c11082401ea00c4d800c0c8018003c00c07a406130011031294001d2014500080d5110600709654100002a20741b1030b4034078203414001d0902d800758441ca041000c210340b0000c56055101910600b4201d0481e001c4e0b031a0109440080d2051780941c03000e07600b02980901c4081e0b0515100d6141e6403082082a00e05644c84040c100d94100303003882140c500e5000614a10708507130064080700041c001ca092208641444110908a8181250390600340b00f103540c0041c90f040001d665100081280303c00600030346008445a540700d90080302c481c012490540004261440704d07100e0700b904045103000451659003143ca42c020100c0c1c01350000ca0740b080380844020 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 711545791 1250 711544541 711544577
    0x6090f132609030c0a150507020307030c080a0b280e03250302100213050d030210020a030204090612030c03120e070e040620090f010302070606030515010b0408060c0307 74
    0x1407403181c0110168840c2080b1003011308000f0380e40f04a034401c01040c9810700c04405c007815420581c18032400c0660340c03000c0c07a1000c20f040800c19800980b414050400001d0002c0c4007240741e450744d0784501c2e0f04040603aa040304c140d020321102601c03498800c9000400b92403401c016800040b0600601c0101ca0800300c0c90354480700113a9107400c000080f03000419282d0300f0590104403440124030203100960410070b8694031601d003400340348902c0344645239040c0e40d502854003e10500b10100040c1c507055589061a9002030080e5000388101d01125281070000030708030441d0703103900402c83c0d4590f03541440039241b2345040b903903c10460701070400070740d84952050381c10804110b0f1000500d00340b9441401481d160070100200c88400c04c2c4008c8080101720014201c10844080f200b0700e50080300c0d00c0400d90078420049000340910840285100e14084000c01444400120203a8407012000481000c3e81c0fa03110400080c0614821229181d110b0000b10f0000003904001d1684118240740c0100800c41c281030385 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 711547041 1250 711545791 711545843
    0xc0d051e2202030f0f060108010c02060a0216020301090b01080705123403050d090503030702010f0305310b0705070f0215090402032410080f07210c0806090f13 70
    0x200117034001111192414402d0188600400741c0c4402001400385818000c0d4840300010f0005800342d81c006080000314542c10303003d114254001c1c0007004400114580b004103980e0a004081c05031007441030000301c0c0d25041d001c015151801001910002d94401e49100d61000e826010110017051064200d122074040b0000c1c0000314040c1c002012561032030031f0090030f1088144c0025000740c200304504030150b40c1154a05c00c0c510311524000034181e80e0301c81e40c495200b107101c2c45100142d44005001c42d1214100750fa020f003030380c0540258045a00c1e045c4c4152500d2041020040c003580d102100a0054642007101201440301c000c841c0f8540388140000908036402100c0b0a0b000c0050080d0160380800b03242c0100c50f00301d1040d148203500015404000d0003c4a0080c0030311042c035a4031001903101c51003810102c42052480f607014206074030002d900c0c0054903802451500003908000001e0203442c1c06101c4034040d0318486040406600c1e5528601c0e12030150040940d500380704071b200101c010320041a2 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 711548291 1250 711547041 711547063
    0xe040506120a060213120803181006030c1406270d06090302211303081c0c0503040b060109030c06030c020c0a1706010b040303020d260c0d051e220203 66
    0x4016581c0340b800d05c888107041840d0b0084504141030003028000214030030100e80e08281c2004034444400d21442107103140c1130740000c07151103a1341042c1001041221400700c56003940c0c2800c0c0c210380c0d031418140601c1080c0c01040a110340701c0b07049031800d02c041a0100030107500c088014004203c4180d0701d848480540e01800c0c02100160b100c2c201c500f1064903400b1048a41d00d03a091501384c0b5141d11516003030a060310600024081c1c2400190365261220340100c02c501d40038121400f804101ca507000050040d4208940641d20f51501e035001030543c0d84070750b04800030390f6403003d0340c04013090074901d00b10020001e03070f0020401d40c4620f09403030026540c0c100e0140001c1426583e0008400480078016003488010b074049210102d044c40207200203600491840340c02002440c000140c00c25201c2410165892000250a129480c03824444a0301c110402062414482a42840240c0329145c00504414104030440742d44045400441c02c59400301203610b030040d000300c1055000c0c07411071b00000d06104c50140 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 711549541 1250 711548291 711548303
    0xf02031f0f0e060a020a0e0d24050c070b070215041b0e13020f01090b0307230a02101a03070b0301060806010516020105070311010f050103061b0e040506120a 69
    0xa01510314900e14055408500c5140c1000d022102000d080181c0c0c030000500700e42d02c00b82d0082440d8a060f482103016084981e030040c0310f000007044034102280d1300030b407107460000e207401c0100f080980381c01c0034020f01d80642600500c2ca807031321903552620b85015402404000842c040c20710b050520150958a540c0298050344026104844101401c401c01417142c0c00300d100e0380401350412415138003140c0b8040151380c054500b030000d0016840100c440c0221600700c0c210211010090000b116817002050041c1230b11a51403110600d580300c1d0311007450065140310f1340180c3c043c40a2001c00d11454102c1041c0544940c10540041680d80019040034081d03001680300d01804001005942c0e031020080e90403000170700308145410403140421041c003402c490041d0511400085890070103110341c4008111800c9003008104140e8085124000350100303200a0321264104425880c4909920803094204249610f880400e52200014030001e04001020507070301641c98821200c510106101c0c01c80b1640c0300301 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 711550791 1250 711549541 711549583
    0xb0607110901080a17032502010c02010b06040b03160e03030a180f0e0f250e010806030d0f0804050c09191a09011707031416080609030301120f0203 65
    0x15051001c0c0900581c06003030b80e540450700100118083c1a42c0d0020100380e0600c40350f803030b990f286e207050b060750381d40c6151001000c0024031000075581c10b61100d60b000450340c0c0280040210141081818001ca000300d000d140300c1000031441003000000a900401d03080e04120003e11280b40000741180c01c01901c0d10081911b90183c0810b91142d5002000580801e0710803144950910017401c5800c41f009040c90040c40d10100419841f14083c10103181440d60b0b03600740411808808001840b0301102e40009010428000104009103004a0401703d0841183c0c5c40781724003c104801102c0c200c0d00a80160b40300d0044031140e06032521000c148034031510110f0711080c401060391103d00b0444080c401e010001442c00545007400d03560f0241c54504548903500c40074a610180f00c0854108152588020310003450715000351511840400c90100510401910012180e9a201c80c99240c1d60211b0700c0c90400e420420051010300407000c603942d1018081c2e103218840b1f10301075000ca8681403d8800241d040b0f0950 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 711552041 1250 711550791 711550823
    0xf0c120507031220070f021302191d0d0312110909100f03110f12010b0111071203110f100204230d0201140705060a0905071a040e0a0b0607 61
    0x402a0034065004030142044290003421003403043d25540c4066810101300000c952041c00488181130034540c1e00101042403448520ba404e10095000f182a803c1c50400604201c0586008603020010320b070320380c0504c1c9180e1030341508022011702002012014800c2c2c410900c40409414403400300e9140c07013000c2041c1c1c0c8006c504e0802034481e00003000ca1a10700180c01052083c000303c024038008903540074002d203e508490a000482000c4034045040c2c200c880c8541c00e0003d8041508084c411000a03210326210450081c1d20719210b4a460290207200c0040c6141c503030020f03102d022443c40c401d1070300e800e0b501d000d00f909250909044420001065294000c01d003070051282c005018010152a0742202e2100c440300c00128000c03000030507000e4140500070030344a85c00d80c55032045a140320740c44000d6641601d030807000c0300024891164150b445128011b004a030148228004503418401440304038145440c2c14900742c0100001046280a2505c0d0108502c59489460251650318441c3c1a400b404c802e071 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 711553291 1250 711552041 711552047
    0xf0207060f090303060f29041203080f0a0204080c13021b0106060e0402041809030504080307030306031103060c03130f0b0c030601020d05031302060d0b0d0f0c0f03030806010f0c12050703 82
    0x18a800014401680146c1088441510000c0481c40740ca00d60103c5c0c140c11607201c0c200081d004c0c03980030318441d030607200c002410194808a110321441e03800c07200008584400f40000b04901450140c0c00b0264020140031003540f6007400303d101014a40718025180881100358a2440c0880c4459000144c1d10f940b0b051000c6604020340103031714141510114146490400c49810106404400902c1181c1d034480040a043c49641240c000e80b00c14001c8176600c000510b0300400500305440306840b00b81036080c101415140115815011742002070b207060540d1924800400c010108035802c4845044c1070307418a002850703000c00c241c4561501800c45449141000001e0300701040c54462100b000010420050040801c0c01d140044d50780607104035855200301e100700e800408466101c19481680c1d01c45001c1040f201000350a0745621031100c0c204001d948908005240d4120700000b800301d160800042c001d540700d188800b840806c03500e030001000c0074984620f18420701d00005240003510000741c0000303041d0 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 711554541 1250 711553291 711553301
    0x181517030316030b0901091802060414130c0212030a0b130b010f030903021b190b0318010509521d0402040207050f0f3d0f0207060f090303 61
    0x31030b034201480309105035800581d101005001d0054241d944021102292520003403c070b980c1a8040d001c2a0f4031611955415000d0031040f500354401c0b27682d00b10300410341c4100e00880c108500c4940040029514000740c42e0000d410043c9000c0125680303404c0003000703541314004011401d4414000041441c601d00005100d001d00445a41c00c2c14100306840f4000780d0300046088040d18204100a160204000000d1070000c00c0c07854411400c1500e200412810b100100841c02200d151310090b99000d862031100b82038036800c5070843c400350031504040148400342c0a0900b00940c01100600c1082e8141d114214850314807900012050820300104012502e01c49140029140b00d03610100603190007200c1e5200401c00400c000e02840c1c0121b403001c2000001c0004440c80e100317840c2a01c00e541903d42d459603599080050b00040050030001c1140b0820407410b141c140d0034901500300241803080308100001d41426a07404001c80d03820805070010400300e00c25510308240800d40410000114280101610 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 711555791 1250 711554541 711554581
    0x3020d050106170601030506030a0c0905060307080a0b1302060405040e0a0b0901021204021509030604080901081506090f150f0706060f08030a2708060711071815170303 74
    0x85000c1040b80c801c440c10703c440380d0140003481c02003000c4d0344000100303040202455005080b0350019502041038512038202505c60307801502240c81c1603035103c14940d0b880007000b501420080c08100410000c0c900c0c0b42d6178945203030001d050107240c10764403c081030840302081c142c0f00d8560000074a19041111090a294100710140025800c0404c00c4003110001c01014000901c50000440d907940540c0455003900c2c0e440700020182c51062515092485440d03100054050010701c0d00b0000403030150100084030100703000600000d040c94126024072500000841e6103c1c1d000c9100c0b09001c5220303100744014403051440000032030320b0758050326200003a03075016040102c20100d010401c1c40885000826141440c0051500b42e904070644540e2000310844594006000c903902c02000c2821100061074500408560ba44d60f500c0c114222203464450000f0300601161a41001c14031108001603000b43c00c0c018070004000d104244d035a0100f0b01780b00e4441e0300e0001ca036080070080244450f20000001d00300 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 711557041 1250 711555791 711555797
    0x1b060a270f240c23091315030302060c19080a0f0e1006050306010e070c060605060a0c0213060b031602071205070627120f0609080d1d2d07030303020d050106 69
    0x80303c51022461413000840003031000d041000c50302616507500c2883e00c60850b0040d102c1003000c44000351040030484c81e60b010640242c4999004580a07028060460740b1020b85000780e0174149201c100700301c90191014102228a640300c4112a225160510480654007206401010718042400040096500950150b0b2107a00311100402c03003980e50341a215031020240c5050080d50a0500d00b5400602244d080160080300c0030403254806070b0401034952566000316040b1140903c17a00c03400301520414040e401c0300c0c01041c0041080a0342d00c001101d1034009600688013010740b00c1d5019001c43c401035005035400e60021004110958203d01c01400103840d121070407004c203115003480c400307540e0a4410804c06100000c45081482552004c01c0c1d5503a0380880103000701b103403e05050915030008906030b24040d15100481e0007851580410108144600010f08a416820001d00c21a40c00710030100c603144074400304c01514010203011380800703140719450050700e070728041ea001d50407280e0580220082c = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 711558291 1250 711557041 711557057
    0x1701081f1406011103070501020403031701090b030c10110a11011e210b031f0c051e090406030203191a01030203100c0509061b060a270f240c 62
    0x207009115962030b50290b42803d21110180112562510f94814908060200d5102081c0401003580c010901064600f1114500b04540d03211442001100e994403005032b4191b05c0100c0c0544281482c0e080c0b40e200c0310031403e00b8ac0d0f0740b4080315611820410031a90407520f00c024401c80071010760304800e840c0200181d0a4141c00c04c4551508054030407015801843e082c14217402e1980e0101c50144c00015100c0e50280030f036070000ca005903030403103061203001c180841b46040072181211107102c1d40507544200c0703200f00d9202e00201c598034030900d19407041c800c03d03810a403900400b10160700c00b00300001710700d060020405a0400b0030306282025100641d4060015a416401000175075000a40245031604030b540001f0f03100c5420800782c41501c00d10408a80005021856420302040c6614201d0003c1e001da040d0344555481c2504403040314002c40304442e10700900070410141280b041c0d0307410b8400d032041e0b03000100c00301152215200890828194909414804c01c00e842c0160b10303014940880000d8108010 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 711559541 1250 711558291 711558311
    0xc1521010e0c040510050f1902101406130b060c0d08040c080d0c03030c030e010e0106030213060b04030b0c0715020711220f0209041d0d05040b03010b0a1701081f 71
    0x34010b000b017110041000008250380c01500b241c8022551464802c3c8034124064107415400303510303200d4042d4401480d81c40e007c2081729100b007040c9510701c0342c0380040111401400c158580002412168034140c0c008809001c1e01d00c82c010300f00320140d40c1d1512030300c5080c0d8a2401d490481d079029840d8202400c10740240503c0c3c0c0b245074102424841596040c200403444c004a00f4084004021000b0901403941c2003424108522406620102c283c90080e5904a500075a2012a506440440c81400c4a1a41c01c00003000030992014100d07030080b400f1041d4078504081038540720054041015001403039a070025805042226400c14185403550586403000041640140b03088101ca9800b002c6103501e403241280b44008a580d811542c0781e00c070050040080000c20004401d4411001c1890b080034401d03400021481d40c06001510111400380075030034507503030a100789a001d940013081c0746010300045940d407107801001055614080e01c65000180045410810f812240e07030041e050840c201ca180c20012a = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 711560791 1250 711559541 711559549
    0x90203060709031401061d04020d020d0819141b0a05030f04094d0d0608061311010f090e150901090e0703111c060506010806010e030c1521010e0c0405 66
    0x2c02504001c03da0825260b4460000c92b80345954030744000e40c400000d04658040020300000790810300c003021400882d2040040056403031082e0340c12800003020040c4043c070320540e818841d000500c131110342501c2c02c20155645540c80c40d04003044190301c07400041400e11000e2018480c903200040041381d05e01c1201855503440c1c444007070480100050104060011140b050300c0c141341c1c04010844681c07076a42d1151489040014440c902a40055024000220b0b421200000f20103403140e030086e0032603205008100041d00e23003007140c03d0503030705108142200040c4810f591a00310301c01c072001c0001c5800c1080c0001042500c500c160080780345a45000355071158a080051200c0940780d21006000180c0001800074480384034442c584002082c0b040704074010080c56801941c082c11083e201c0c1c1c5500d460f40300040d1070480020038500c0d00b65108403c200660f1400d02002801303805e09001c43c034540584260242c0c800d1014404018280d04030000400c02c0c144019039540e07020386640e02c0d00741440c1c205030000d = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 711562041 1250 711560791 711560819
    0x3011503080306150c0708030318060103020a12030212040603020903160b1b030c1e070e0408030c03130c06030207020a1a03040f170a08060f03010606020304090c0309020306070903140106 82
    0x90b406101d40e0122000c040c203900080b01d4203040007200711400c05640747e0415540382c1c801c680b138014100b428200701c94000c000080c000c2c117990b8000c2004452a0070403050580c4218150030681c1180f00b0050803032400800000200040c04083c0e034050796403180c05060504e083e446400115500803000020080c0c1c0301a142900c0c100d0320800c3c1e240102c0c0c210769444c2442c600035a41c00c00b103540034205113410008001001001c02d441880c0c20340e0036071907484008180745603003120040d100b8002000083c2c020585400256031003540c0a614600e6105140c6034100d442c060b075040070000c280d0002c0e03020198985100d214008140d259a00c1c1d800058100521001e800301510080c4100c09480c0001c080110039082c1c1090a840080140e440d61a00c410051043d0030a0740e4480c00780042c00d000c40c02508042c02150283c1e000c2d40c0046261600d030001810013044940e814804059846036040c0c01a6030501c2a1406003d860380c075920261308504021111143c69402e5041c1c0340e14022080090310004910 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 711563291 1250 711562041 711562051
    0x1513020108161209030201021c020903150403020c010c1e1401060f08070e04080f0315010e030c4b01030c05180915030a0b010611070501170a0920030115030803 70
    0xf0105a03080d0a103000d074064042c2c2c50b40454552040c241321a031146135a4058020214202c046032510408100c0d01c028000c0c1c19940a001600b20b2070040c09154000c2c420b901445100701e4084d040c55641c060703000f80007000503804941c3c5040c0c0c00d503c407c7d0b40100340100b401801c4a002501401894415a01e0340c400b410f104c1e40660078010000101800002e005940b10450494a8150f4034540703800c0c2e40640000307000015000c02d007518441900340c00c2c0040d5201d81444003800d81c8018100359250480c8074500110208a50311181030b201000190080036040420040004d001c0442403500024069035500c0c440141084007d00c001440c143c10640c6038600300c441503c0e002e0442d01c0c0d2080c01c3c00c1c0d4200d01034400c1c0d018811900340360300300000400c909048601d02d40d02c0d220100c00a0000ea900c800c06841180e0006402e88811000300b41000480c4c1d81152071114009280d00d03165403001c400400c4d00b038850882c1030072940e50110f00e0800b8000c2619020b0084110308200c0e042d80c2e20300d0b0712800041c0c8 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 711564541 1250 711563291 711563327
    0x501051f0612090303200c0106062a0203010605030f03030a06050906060307050a120c0c06060b040b04090b0f18010f050a03170c070810020706110a02120a02151302010816 75
    0x3000783c0500d0f0095020708804010400003444441000324860f500f0340c46444540547d41c40c1c10400140988035202d140784c00b0720f520081e88840b034004600c03a04402040101079030b047d543c4001c0003030503541c00c11611361218000000b0b1601c3e45003969244c4201c03441ca520071070140c1e8286040200c3c03681c46000b00da074000c2840c1026a03d88581140c1150700d55483c6402c280302c2c1d40380c20035003d42a43c20a0440c0705191244405100f416140d1803003611a029511a00303150034024007040c0703c4850240c001a28012001d40803010090040c00041d13244041002660f140201d450300502c09030b1054160329001d840b0559490010602d076584100c0d6004c01445031034100040482c80203030540c4144480c1000300350490803100900c054840a000950104108031591032821424410f01814a0107450f00c09041c0e4001d090517130410017176505c80b40d2083c2540b80460003941549000704140801c098020141401ca07980f40c40e58074400980b4003c4094006082c0002c84c0c00c3c0402a564041244218000019 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 711565791 1250 711564541 711564551
    0x11d090319081b071505071e050c03070b0f01080f0a05061b12150f0a0326040308030f1905060d110102011512050c011407060510030b040501051f0612 66
    0x81c0b00b02c190b003c0c51100c201c84590001010740c10b2100e40416207001c3c00c0850f1040116403108071094842c0149086079040e21a2840c201300303071507401540582407115060060f42d250240700e680302421b0003c1203408801e0030b100300d0014050140c0410005459a2004005100c0d00c1d03401c0d20340325501c0700020503e40340000b08058650360041c03454180d596084181a6542c03150034140708403010020725501450240d1041905001240303450441c6800b200c3e0000383c0410040a0310400b000034078131728900b160304001c04100000c002102c401c021482071020100c0a0718601780383c1903241e110641e1002820140e4202801d2205550721040180130321540320414a41104c034000c010707809480f0718035601280700905040000c4200041c01c0920140f44078909842d11038034440019520080700c0c542d80c008401c814408640003503042e50190381c10009480721a10082c4d41c07070350380c4c20034254119012032302c41e51030782e0038062502d400759410050b8002c0700503984155030a201c002043c88021040000510f40c81d1 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 711567041 1250 711565791 711565801
    0xc0a082d041a0f0a0806030616090b0d0209030a0609050601120210030507200a0c06020d1d040213080c010e03010b010e1e10020a0c06022802030f06011d09031908 71
    0x1400480795502e1030b44401586480744c0d44006803045400b152418000d02400d070000700c1c10341940c2c0350006d08074120349980414504107810702d0f0440d003200101440702607007005940941c0c0d8003000421441841480d02040441c403515000c2d043c0031060740614803550b40e480084005a03184840051040803915000175260340c0d030142102d01c4104501c0c0315070803442e00072816105100100302c2942c030303c1c01079001030111591048200ea81d006400740300c200207100802070315480901b0080b5080c814600400160a0001040703900e84a0400b07507000341d01951002107402c0180d600280328400b40c0c14120020040e407400d0784000707854030200c00300c024440d1940ba403821061844087c6054076040c4080d1112000b500d00000203580c421280c02c2c26a5400c2c43e8000c005900752001500320300e091984569007401000351070914180701e032001e100326494000c3c1d440580f16650100030081c002c00001e1007102034200500406e40c03c2c0c1002400750314054004014000b8000a030344012081d418007483c22a510380c2c3d071 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 711568291 1250 711567041 711567089
    0x50f090904171305010e0d05031902030d05070e0405150102030d0b010c060608010b130b0d020f120d0801210c060804240507110a02240c0a082d04 64
    0x31100da1402e0b8000042103034800d00a41c10015015144280c0300c5100007807600c0c00b00481d0301008000100103902c10400010034001c2c04500c0a43c01031980102d9080c64001400501a03850480b0400d0014510702c540003c907103800c0c020150088074000c0221099000780d40001e48902c01c0c40350200516840b6840104580d01c2409110007540e081201041920b86440c60a4007919141c03259911842d41400481e54a200e9480303040c00c4c40100401e0004880307800da0a02c00301454401c400b030f0b0310204000c089401d00d6014045402c43c540280d561418030360504528400360b4621809a2000c0c3d5a104d00203070004100840200a603a1541848142503403580340c00d5521800d4400c8525a000c2010750401480c21260000c0b80240d446840c0c581580070000c0d030990b610a010702c03019510000244d030412a00094030700250000345283e110510b005440d5040d01d262245e0744808a40d850b20001d104000b00510b04501e0280390011403980d502c0780c0071010303181000e02581c00782d102d00380c082c5407403101e032962 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 711569541 1250 711568291 711568313
    0x110328050310090e0c12030702010f08160806060d1b0210110f0d09140102040e0a23100503010603051f02030603070311060415050c0d050406020318270a0606050f090904 74
    0x80e0080c006040040c1000d106c0340c40760014042203022907101309003202c0b1036000d0300d4440c2c07081215140d0302d00a170011040c00c940054010f0400303500043c003000038490600703c0d03001d2030750501c940b402d10003600b00017a540241707409948120514101e02d04030482c0c24521518048400112040880540380c2031480c98410040c1441d10004144000000c2c621004041c10740250041743ca40703905c110020f59817001d00b00c0c00c2d40d1407124039120b0744481c500c1503503d031500014a141c00241040e07001e49103c1d241c0002c01d084508541081c0c800390b00000c00da680f0803040101002d100b030440c2d1030660650800f900840c3e030341c403054000206001100c68aa80040e05c6400541c0c0043c51094114070010402d18405005580100c50000c2c460090240408001d40548211000c1301c24507401985445218110301200307602000c034013540000c0c0b081e204544500140c040c4001c1880b204ea031640507041c9610098210707101a802a42800b109024043e0b010842e0b105a640d1000240c481c407203107a91f145400f21a082e = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 711570791 1250 711569541 711569563
    0x180a08030301080d03061401080f100e1302090c07170706150905090c0d020a0618051005220302030c010309050c12010b0a050616020d03110328050310090e 68
    0x3210100c00024981e20000711682d00da4000d4030308103c119183c00005100c10159561030307000c03c2004c0b0100b8401c1300e481c40001d0f80008107040d40d9900e65210805040c0405040e40e104100310380a002c0c100c2507281c21f030b4180c0d81110f00c5c50081031074400e00d66503d903004121806d80c03508400380031402070103100e056048141260200a11040440e0716030000030010038044d075106a040c80b409200e50344500386480252002d640082501d03c0342e902d840d80132540a0317001c0409180400300c00b0b100003a1a26184170f5030b00341c0f0384183c4070903880d1020344408603100742c03e0140000400758030b04020400f60f02e0115080c004900c0c00e280104e1881c0d4941411032170041c60210240d0041064220060900340650103e50070300000c88000b0045551141040854000c000c0c3c00954000b1000700304005103042c401754064140320342080038081400210300b604542000c29503c500307003a0044550010301d070300451f00d20080c0e002e0070450305600340700c85212031245c41d50045520550350ba0041c1168880100306034103982c = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 711572041 1250 711570791 711570793
    0x50901060b120c16053304031403060103060f15180e01150509030d11100b011d0f06030109200403030509300f010501050306041214040e090a0311060606180a08 70
    0xa0b0001176090b1800c0c1501c0c4070004440307040c1c6e0203400821009100524040e581540e9009000c48290305200c04c00d90026000d60305059aa910008000d100d460920004102c12009011042050200606603d00540a103040088401828003854403d00c40a506440000b2841e1031002210602991107100d610310b802c2d8984666818000d01691040044c01034402c5013003519902503000c20601c0960341004070030303404221008c1038085c03207070b900301011041c801c00200f0420f0581c0e01b079000701d005035000b07803c1001c210b500d40b0200c000e8180c1403d0301e041c3c04001032060700c1c645891a10010302c180100d03c04644640b0030740b0341c1c0107074080745035505a29101521181d144000300102c0641d43d6550a6580741d00380d5420600002458a00824000d11442d00005511644000300f002110102000100204072074410b10007c40c5075000c0c04512803044180000400c0840401d090103800440a000c0181d0141d2120307003008042d48403102503412a40a0bc0c94201c019820341c0700149138141c03160402082 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 711573291 1250 711572041 711572053
    0x706050a1e020a1106070c02060f130f031202030304020a0e0a060b0a0e010206090a02061207091809111e041a0904050106030c0b040b0a11011e050901060b120c1605 72
    0x96100254003c040c0e9800b1078580740492191003440720b4403a84100c88030000310b100d400c854009400c040e0000c100100f004d0301c01c9498101c91492003010101030f500012810b0780d80032424400c020b6121000440c0002c00e000440c258a06640083c4020302d00b40100c00d60501c2d807101149150390340703070801009090a800035640303d40c0605801403000c960450564014400d03000450020000415a42e4800d40c003d0141c0e45801d02d080c032007224061020b080d0200b0070184041c009104d08443c00d00d50303109251b10740e01080c412541d080503542d8840c0a2004d910404505804200f500e6518113140f14229080c0e40104200040e03943c55511150024281134000b101d000410013040010360007101070b42d124060b40480152500303240c10b0640240c0c0103510f2032100402c03503840203c3c0208c00040c10b41c0303510313800030035030041500038000c02c1c9031441e01005000c0c1d203580a1000c084001e00036640902510300750542071443c58440c8091850020300f191804c00b4001403101d02030388a00c070a070000f00760032104803031b4 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 711574541 1250 711573291 711573341
    0x9040507030c17060a0302010e06070c06050a080901020309061803070516090c02030a020a0b220609060501050f0a03020d03051b03090906120a12110111120610050706050a 75
    0x2015082e0503081d5000038881052030503842010031811400b40c40042c0c0403400041c15030f8019070b60100c0300b8000542c0b006040c00010009000840170074060306069807103588a582800010b0014400135000706440e900600810000b1080047d400360b000340b9843c101d640000c1110300403420351080b020080c0690103101c007851545142094100d08844030000200080c01d1a81400c0381c4a0203a169400d005800c241036803008507a1003460280c22080b1581c4882810000c1c194000d03504015030740c00c0300d84540f03a4040c007081c0600c6114044c014102651503040781c12880b0f00080101103503000c000c1c81401d400669405042c81402035420201c0c2a8030f1120071480442c0455076250003201c405440350050380e0000b9194181030f40d2015034503400780d00a04240c0429902c40c080d61a00030a620b0400291000c60517142009004e1221080c007510042a030310010941001c05d06000101242c0c0990030810034505580da020003245d1185411001c0059141c6464078603901800d510500c10b064501d00300f0000b0 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 711575791 1250 711574541 711574547
    0x140918070608010503100b0108011202040f1a030d020d02101509060609080c03011104090c300b03030906030403050d090611030f0f010b04090903030b1c1b0819020102010209040507 79
    0x83c140c0e01d007103040300c1c01c205100c0703101000e80c2e030141c091a0004182000400130342c601d0601490190380300071300104140740c40d480c001045600e58000050307100c1d0008011045800c05105580168046101401d030707411201a002e0368601c1c002014002c119543c9004101999501074107002414800101340300300b594a0f500140700740b4050258400074052064100d4251405100e4900c2c0c00e408145401d081c0b500e0000c01070014150000c2d09002d025034009006e40e800b03800d0a0000288000800d5645009000090345040f1102440e0590090b4001c0060010a075140c105030381d8416030602d8681c0d23503410002c2c000300181100e01002420142018040c1c0c002500d000007840c411030550109062070b0b501c0840301d002d80c2c1400e103d02100b50104010922800000da04049800e9000b824013050095030400400c5603d943d4401880c100c4198148a000b0045518121800200c100d6803091007070341482031080d21060400f141464044030070010300f04690003034041d610b800e840200b040150f0f2030504405 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 711577041 1250 711575791 711575807
    0x11a07060908071406060d060e030702040603210201020c060627040c031101020606150d09080c010b0a060513050103151205281106030c0705060907080d08011409180706 74
    0x440b01d00000c600113003224540003543d40c2c8100310007800442103100da0b0325041e00405201100342041e00040040201680f00c900860340114801e100700f4880c0c4020403940d00000003600f003c042164010024074210700700004003550441011950f03200494080391410341d028800d00f0b40d41070140002ca08110502c4440c0307500c10101c03405034691811a03502400126214402141c0c0e4a030b002030f107800d0811140c4c185401400c2c1000861100080407485030702c490403107070480e0368030707004d940e454441350309403420705a224a009041c581000c9041c03014061030a1110107003406414105555550740415641c10010090020402c00c6405c04803a522801c2243e2a40c0070081045c0d00704003805654212030884040c4004410b0700410350080e9030880e8020003032650300250801d1918001440a680425402c2c80321038042d48616005200d120301c0d058503941801c0038006840240401070004028400004803c400c6100d0200c582044035911055802c0441d9903812031b00315030f44145480456030940110310 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 711578291 1250 711577041 711577043
    0x30a050d08040c120803070c062405041a2209060504031e091a031003050f07060f1d0112110a200f0c010503070203090916030e0f06011a0706090807 65
    0x102d8034503141c000c8a080302140700c80040c628035042000454aa12a01240003414883c0c0e101150503e0552b18a00c15058805880d094a0400311400c008519140c41242c03d52600000724900c000e1100c000103812540c2140e0380b442c0b0160020369100011310942c000c400b8940d2004080110b4200790400510790480300c40b10144403040a00082001405100710030121050450b840704a101402009507107500003801e14951022040c03008800036105000010160780420001d0070080c1c58064020156002c0039181c10902c50b0f419601442c0d01c2800c110078007010030a00380101d0401708105004010208c80740020415840400d1008800f03a100340403446507010800d40d801414003429140d44c503200340040071905980301c00807101d260350151010395071002450058034245582c807408240c2c1d04000b240e0300e900880c1c4112006e0743e100d4140c800c40c015608003100400380f40c038090900c166100c006010b001d41c14080200d520700780030504012910140d0b442042031100d0480c40c6009603090b001414 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 711579541 1250 711578291 711578303
    0x3032604030306080c0906091302030a050d02060702161a090310050901020a1202180d02010c050109032a05061f050a0308040303080c1809060a03240e01020a0e0f030a050d0804 77
    0x7100c4045140043c6c61900a0a00400c10710301901d440703840c2d0b840d0703800400040783c00d80181900000071802c03d0049000b416000c0c1c000e429140790156000741080b11107254164070b019452000d00200d082c2e0701c0a9424103003450362260381c0351442c40010f40b4044406d04941e07416410b110801a5000041d0050840c80e40346031980800d20400303009102c1070740545e0010440000840b032051116190480d2240c0580e801030403d100b003042642ca9030790a40c0e00c0311009501281c100c07044240d0544007284242601c001c0921103030301d0b14000380d4034503448410180c00408504001c0c5c0e01c000a60405680c40c7c03000b013800603d500700300c1d035403494203210315041417005034049181c41000900075503148048800d505400004090300c14100c50420034004070141c901500014183c0c80440002c004100304240c1000c2543c403030705407880300c84407002518028690580380c0e0740140061100b035070700000e4040d95a5021504018420b4610340405d00d0700d0a00da10143c410301c2018942c0032a182c0001c0000d000b580940 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 711580791 1250 711579541 711579553
    0x4030c02100c0b0c0d02162042041712040803040909051e0609060a0c021009051c05030a060b0901050f2d090117100303260403030608 59
    0x101c426500e4010700b840181c248080300d000149600c40410041096521100005090485d1145000d40d020590242250816024180f0003810303020402c1d00c0300164800c58289164480d400b10113074004840003242031103104403000d0a030200301032594102880b52029205600c0307907031741d554001421815000f03042e1a8014000300110506c034000c2120240c0302140021450146030800c581d00801d1200341c00d5505010344031b42c50601d03021440288220201100040500e0305050001c0c5043c060080c2c1280045403900b5003000c40c46401150400e055901060006001d89042c103046007001c0e0303003210701120037040c0750140c004203420a01035405a00581410408552142e01c411a98417a4104181c085102070081c1310301e400046000305628246020804220180b1080d00001c084510300d60742241400452050f0f041e5900c51000b1031000348502071442e031070504000701c4a00500c3d5020113420803d441281900744c0c004d0085078800d4421a0340c0c1c494040c070f81410010010201c900072520180070354 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 711582041 1250 711580791 711580819
    0x1303060609020c0304120302030f0f070317040b070c03140307032c060a021b1f0c03361202061005121506030a050709050f0603070612020a0504050904030c02 69
    0x901c2960f030454510380c001c0d0b280a0030700b41c00303441c60205404120b00710b02c070030058040a1810000a800080c0310386403900d0f2504614034028094402000204292884180030040810305c070302c108079009921824031502401c042d050803625454807542841519100005100c0300503410340c07000c030003602040d06040100c44400210b034400c0c190600c0c0c04023240c0c2305001041c58a800340d40180050010000891168a96418281c0c02c3c51109854600340101751203004e035003a0824003802400310b0803850108140301820214120002e030110411811a041c4040700411171041c000c0341c0802a00302030901032100d1a074000941d5203800701d42450845000c48000201c0b070400c4034814000400040240c9401070810080d540300c440d0092400740e06202da0603250b00400c500307200c0d000203008421004145880c0a0311507045010307005d01010b00941c000d00041000907401200180d50075044000507a0394540c416040b10135010b160489030340080c08105201c10141c1041403c29198820340f10030a80741c2070 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 711583291 1250 711582041 711582059
    0xb060306060306010b0d2d060e070c0b0a0c110a0b0907091a0108090c0a0e0609010b0708121005040c020a02010207090501050a120c0305010501062d050d0509010b0613030606 76
    0xe00c28000317025000d0000a000e85542e40103035005801090841507004100c0340a408003080d010f40c6070760400d60399031050118041500c04158008094186258509696901c800010000605048140343c0d03030781c5000059031103640704d0b180c56903041c0121031a000041c103001c0401501920072132150720504000007880581d500480c5118007a0608814180c42e0741001503038007035001044d0b0b900750301986400f01059901c4404580c06800301d4030400d44a8070b0103d081c01450a810b80144c88005c0040c03100d200000d2141d07003121892580e40001c8000c588451004200043c0075800541c0c0c040d060101d0f0a03d060390008800007001d0003642220388403665041c01500301c0e14207010b21070700440706820a10007819400600003080d48103907490003602d03569442d01d80c2101c1080e080030740002c000099560710302900703801c6086c51075101503801191210546015007a41b054026800c0b1080d00c0d0301c00961a00c00070352040d0b07d00a00502001c1e035607072030042d08041c40c291a000c00c5039003c0c80e02c0030210308001c1d = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 711584541 1250 711583291 711583303
    0x705010807051b121803010605031b010c1104091202190c0b07030903120206010612020a1b110d120210050105030c04110f0d020409060b120a020f0f03040b0603060603 73
    0x1d0103803034161600080e224000e400b840c141c00d0b03002c550700c0356110441050244034000c1141e100e084600b41e5500b0905002c1500799490380c1c0c440b500c254481001030059003c90000721442000c2420201000f0341c1c98a0540c000c0100308000f540d000345404240003d01c40d610068038001241c40e03099079502000c500c81c50000c0c010341c034400b41600485403400d00c84181814001c10700d06000c0d0500120090b944d544019841c209540303040c0058100d040100042c076080102c0481e002580d20703082d400d01c0c4213584024106201c004071030031040d0114070440d050040724a082d207251140580326043c00481030500d800120200044000148510b2015070141255840341d98141c030402406845401d460b4070800014254102251400c2c0c0c1041050003079030704100c40144004980141b0158691b854070712030404a074403991014100395410000c0e40200c1202c10a0f403940010510401078541c07030419145400380c080c415182a02280000074803040c000300c00311162086200320215509a035402041c192940 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 711585791 1250 711584541 711584551
    0xa0c062102212202010503071b0c1d090606040207022205010e0a0608152508040201021513030f0915030e0609010615050307030b060423030609030a120f05011707050108 74
    0xb032103403c003200040d0310400056421407179514088404450b05003500d90840041001216031140320034042001a40700461203410398000720180b00b10b45450f40d4180d072514170040066210300d5000409004560360721100322100d641190b644c11524948041d074030b00811003030186108402c00740300041d05d00c030000e000c3c01d002c0e00c07400700240440300c0400b1400e62610310050410904000a80c0d0000500085121408501c40c00c0303540e02c42442c24070b070001a003070005a1b0201004841c4440030001340030302c0f00104164159042c9400c40046880740300444601c0c030280c0004004009200c0c0c8024034580c1500801c00c280d070403400f074480036203500f001d0b81c3c200d600300c0c854000f400f500c0e40040c8201078001c00242da44084d15090100e1104c3e08400015000d034442d401444400c154442c82c0403100e48021100002c041084e802403031141003940041e5624040c6010000c00c1205003144d6030b4601e07246401c050405c0d444036400b0720070f55031188599601141084040358084c841d5000001d2150b124408440c020 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 711587041 1250 711585791 711585841
    0x1306060806040b040c0e011b060c260f01030b0405010905010e071a0415050304050309101e030b1518030304091b0e0f0402030c0712020115080a0c06210221 68
    0x1c80c0d86d84005486103003129900150f480d501c51641804543e550081e0754100c14941c0e2002d6003494426420144100070244130401510b40404000f2084d500100440c10340b5080b0b005c2c4201135485103401409480c00310001170280d402c010002c2d10002c0005610000d4900082e03e08642111140460b9054062403081e044a0dd00e2103114601e114041c0b001190010702400c1601e03e010092404282651001e000caa0b000948002040c03141b0700b070041d0102e0140c01c041c982800303884c445c5000101b102c8042008102101b00004200c8c8a100060084455144026040e41c0d11559544a104020410014913140c84040f810130301c40d07024400c01241040c400020003030422800c240040c8802500b008180702801e0b1801c000d2032010403001d0b50000c061904079400807989042c0b0405107a41c450580c2c1c8265010b031f000745580000a0b91090305142540c8c0140f810900a1003220800d240828078041d2400181d071000541e44422601401c00800c601d02c030b80b03840492a2500c1080031001601d41c2488040 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 711588291 1250 711587041 711587057
    0x8100518060f01111f05220b060a09060806071404080a20031e0f0c011407032703030906080c0a0e06091201050f0a0b130b1306060806040b040c 63
    0x1c40d280402e036000030404189010440e801c29060b51614000c100c41c4040e104001c4400102c0b41c03440c440c00380315440050303c0c12401c89400300015685a900e13080c14000c1100304c0c080000385280d00c40e91250001404904400d0100c59a901041508c070b40003903981c040028500a00c1c440306802800480c0c085544842c000c2803c0011515100c410174940503032042108142d00000589540400161450780046600710004402240c50340d40b6000c2c599480106541101040d042c1340c0ea0404c04405030082032400d11692000f903854103d44600b00c8800808802c0c0f09030b114590b2890701c6110810680348640c0300c4044864030341c1415954042c4c12946a030b2400820090700e9095441925506540c000103080a0b003002d0b410000a042c20080c40d4013034005a5440e0100078600241c0c010040d04902d0741c400030000b83e070743c40020031180d00c51000c044c20441d0b00c034002010a5112118070f00070070484150100134490f1120401801514181c800c544214200100525180303024414005000e038184c80300e41c0 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 711589541 1250 711588291 711588301
    0xe18060f1626090d020d05070b04061838010b0d0617150c03040305040510091e0e06090105060417030f0c07030309140303030c03060409050d08100518 66
    0x181c54802000880c200100001004540d40c108404803050b01501141c24240c1c0c0350502c502d61a1400960b10042154008031000180030f42140445904c1d5800142000d2141d649060140280195040e200540720810180703a0510107012045001c84400e2160786d04a15074000c05081c100e122010408882c0f9002d000420404000000520780741e80400401300300180e441309100d104c403151090401403504584106030040510030440c690160385030000e03c0c1103083c180c40080081c001d500a950144801507121500759010784409001441441a504246201e21a0b2040503400c948036010070358016601041d420320b002c1d42c1c018141c80d8080c288604151030300082031090329102c00c6500050004000c219a0303100d402c0020310307103e501c050007040e850b459450024515a1207038404034a084000310070714a82d80e40402141d0b046110803a00325201c0d00e640001800030015504020003d10651182c00c859a030800d080e94825580807032400c02280d41e030300510802031014a541e411204101c80090717 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 711590791 1250 711589541 711589561
    0xa0201050904051e0f010612150504110c100b0f040504030c02040c111204080d0503100b030406060504091b120302060610140c0610091a1e06040e18060f 67
    0x107030310000060404c81050b100f60380301691003401791030038140d68050a005201c19500458082e076407101c035020401c40c1c1001010200081009030003868421911214040102611a401e68402c4806130040d111003a80c0000c9080c0188481c0c000e55014110350104c030905443c0501c070361446103401d034640c02080c0e032140c1c1c2080700030581000848144080112104603120301001202d0588507208501c5644074100a021031034403001402d008104001041000494550100044128bc10407002035031a81c80d02c4c50403801606080c1c00481d0805e14103000002400a080151300084200d103441c05251500c1e00c221914002100700e0140140c1d000401050709030034209011000e03040c0e24903104d0081d00840c0f10546441d4040420101a135201c1e2050104d02d04240d05104002c2c286c9440410000f42078062010f400d24201042c0c1d0300c40c04a4070740c030895500440742d807141614030080003581e0f6551120301003c084c000940f03100a460b0420800d07403c0382003001904600810130402d1803041960303041819 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 711592041 1250 711590791 711590801
    0xa020a060e1e3705030a0203120307020c06180108100515130e0c0403110307050112021803100c030f020f041a13121a0f07031d0706020a0209090a0201050904 69
    0x680c11010000c203101d8503200c00b180044002c43c0c41500510940c922214000d034041d078a401091103078008041041c0181c1d400180c001e6189915001c0c161250717107110080e0f00f0420500141e80d004180058090410852030205001c0d845098035a404240c8590040100300c1555004142d00701f00e0841081541030200c0025003560b8042e01c0406101544804252000000a4400b4068680c000c107091003040300040f40c074151402c09400901600f46840c000815000c0d0301c03c0d040b0b03002a0f002840c03080180d00304042600c580b00c050704440b00448042c805100030042c2d07121120010b80f5154801e001c046c0280201e480d280c0110903400d00701410b0882d0500c100f48000780c0360050074410825440003010003001d02c13000f401700084250b03005940d41800c662000f800b0200b0701410700345908000444072048041900030013a41340010381e8611035010180103665051540c8c5e900d20507070000080e0b25a00041002d0254400e6840e4190354849409003a40c9000e040344c004d0200c0c10921108003035090903445 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 711593291 1250 711592041 711592099
    0x307060e0405091f0f09150209030f030f0a0809190b01140406030f06050c13030c030b1303020d11120c070602070807080a0204050c0f0d05013b0402030109050303090a020a060e 77
    0x34104c491b55403201c40d403480380c070031203c03807a5004111100035203028000c3c8900c0131000000345251125058001c401e500c070340d0031418144507802c408142000703400c0242c0ea10b524075405080d1807010850030b100c002400c091180602d0140c1a4925921a080c507000b60783c102da61042c050380f6040400e950f80d0015220040550720455002d12920f10800013004100c0003e60050603251000c509608200d140c100009102da400101c06407006c80000364005024003c030200e5282441c0013040038541c3c241841c01410300f40300ca0640100c1c2c10381c100b0303402085401c22100380303800719690a80e0b1207a0300d07502d840c0148140d030007640200c0c009d84094101608115071044d070101009180080c0e00d40c14001c3e54001e0034001802d0380d07441c001402250341009001401d80303001c0b02c520800c80300081107001040c80c01043d0310b0660b500800440e007103440941000300c1351640b001c107490b280e20f4418622560b41d500490168415401c036100080d25600075100e2881c01c44002e09070b45180248400f40b40054200030034 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 711594541 1250 711593291 711593321
    0x1009050709051e01060c020f0907081f09090c050316060f141306050a020d030e070311030a0623010f0b03012c0a0b1203040815070e0307060e0405091f 66
    0x35004000e0401c0690039806441c0d00d1b00e8010580380c0c280181318605510210950244c03000d801480707004c42e007042c003d80c0c1c01403183c80310f07030a050302141b1424905812640f00c0c20b0380c0781c1070180c40300422914180010079210b094003100c50300162200301a0301f141e030500c00d500c040b69102840078031262150540c82d00b600c08400045d0300d8808e40c5141584844c1240d800007000890200d0319071500d650600080120310b12600e030900c91280da01414903110181c0d07200043c0b501060290004664904ec04103818458014004000308803071b250300403074036101c003400e0100254419800031035a0b0f9424000c07002566000c00c85035045d6824000346505218007803081403414501c01c0c800107003075955a80310a01c01c3c0d01c045008140080244144600000c001c5491503045e0000c0c0b10502c50601c0c0010201036249450703a0035041a12080740503200440050b8016805014100b000724405800c001c5021003c0720036542001643d85904855840d291400c8600d0302c002d11034041d001080c1c0c15500080e14a4444031 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 711595791 1250 711594541 711594571
    0x141306050f0615030919030f080601023906130807060302190f0c050109030905010e0609060a050703050d0905030702180402030c0609210c03011b05040618080a060b03100905070905 79
    0x5040d5841c010500e01c1b00b00d00154240f2400d1680395403220038a5003100007070000345490040c0c445a200703640078003145c0c2080c07103401006015402d100d2440c800740c01300000d042c040e507480b403c4042a084c000c040c003da403814480c42c200011018032920031a2040151071042408605104108840642039224001c040003044494440030400c2031040f40c981c02d105c0e490b445da00500d008000350002c2007a5801600c212010b101100719a100c03c02141c8801e90185480d5a13229514901980c1e54050320800055030362908d80503408205c0008010a00980203ca00d008594109011020301c602c0c01c8600a4041e0081800d030041820008060030100c840103100501242410492407060240209040b68590202c10000d0a608080c86a4504844440000040522140720180191040384100420400c0c81c04c159140030102881d40c3d030103017807100261030b022161030400382c026002c60114284203008040406c0704510142c4144d109207a403103c068910349183c44c140c0c400600001707000500c0e0903201 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 711597041 1250 711595791 711595813
    0xc02070324062d050121050c04030507060201092319050102092d100807050703020102040e0108010b0f0f0a0b09030705040c05030106031a0121141306050f06150309 72
    0x303104040d652101c00d0160b030400900380e500f81102011140e200364180002c81c203444502d03103101000e80d5200d180c0e00001040c030b0b8441255805462045900c0600107024100003c1026903040d00010719003406202c883c00c00304445c168030a40c5101c0c0105520895025042a607404070304c01c1d981c1101c05015000041c101a40500070802181704290340d5041403c0e9068150b80c008204001400301ca402039503d550784810704500603129100180c103030b0050000124000042501c00d40494024002680c0c03000c40c5540d641c01c142c0d01a062100a5600c50962107130303600080d04020011950741e5a0081888d06420f02c0c002610029502c03400b140c42d0103020313400740402d16803254011054517aa81d079070781c180d496151220003002c81e820810041210904241c3c1d881c0e8aa82c01440040040e0390442d000c80c090440440880051017224010101000d1200802c0001c0d4020600c16100c18000c9009111a9a5501c00e031110242c046999a0380b080b404400007100700d40f41405913a020368000200c0f03241c030b094 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 711598291 1250 711597041 711597059
    0x20f030c0a14010801080f071a070f110405090d02030313150908070b07050a0804021203120a06050f15040e27030304020f0f1521190c0207032406 64
    0xc0d00103010007600800b00d40c0865a00028081c0103111070000380c205a107a60240c2034503002c403489000154010750000200d40841d040032100119403103400d0014001c0d49141c102e07000f40218100300d101720300d44800075035148808a54901e041d02e1990185195503107441000f00c120542140a03901c001951042422050b4244142c0700914010301190780c885a01c0c0c80d1100070a0070050502042110074001c51400e0b6800001540d0807542c100c0ea94002c00c4265401d5078514002c03442c0404002d200d00c0700f4000d41c030400c3d030f01c81010b543d0261200750741c0d0302c00d850920080621801c0340c420344241c100070800a42c0c5a40c00d8540d040f6524030f410b00d40d5041c51401c9100820051110071059030000020301c070461405005071119440c0c1525500050300084000819100030502400c2c0d44090000b42c0c0e100c0791007160040c0c81d218410000710001424502038640e02c0d1a20500103200c801d14241e40704040320700000b100c0003103e0b0702c00188039081840e03400c420b040507026803460300f030240c5030b070004540004 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 711599541 1250 711598291 711598309
    0x100e1f0c0309170d061205031603050c01150f05060f041202040204050310150909020d0b06010e04180c081207080d06090203130c05010e0f060315120a030206010b0f07020f030c 77
    0x100f400039041d01c410709110320104039040c42c0d00c101103a41010000d54002a40802074810341030122415007261a020b0800360380900c03812007001c0407035180041c03000d8091302500604086c0c814141d04030404a860f141809060f01c15410103c070322103002e110802115a42d419000141d610140005d0308103a41c2e400031916080e000107940380030755251000100c1640c0c0344640c0c1b0b0003e01181c0c005020222880e0045081610903002c044d10f030098a500141051740101c400c2407507008090001c00820100055259003038080302012200c0300c101800c00184074000060003102070903403030701c00342c40c108665a400d60b0550000035034080a9031281d900007004403451010f10b1141c441c1511169a0140320720305400411110b402c107a0501c5104c00c00e80c07210344c48400c2c40f12078411017030f45c80f29541e499058289175403081d000d03c4e040d40580d80c03600b144241c0a0115040b00860300c25002c846c11a45c80e03100c0d294031802030b2040000c01c010180106405131400e031004504202002d01907131b01c0703c6003a40109643c80 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 711600791 1250 711599541 711599573
    0x1b030a11060c1c11071505031312050a080c03010303022e0606030b030123190b0411090a0e04050a03030207080c0610060e01020309210708010c02100e1f0c0309 70
    0x400d080101c0543c3e83d80110403000c80102800c01307082e0b031509082400755092114690441000404000580208000b4200182d8581c00210307102840001800040c401c5d40412074500c0068080404a880c140e8484280ca045e80e6140d0041c00c8803d0084444150340e018103e9003200d1041c000390980340d0111706209010240159030f8001ca1440340d02e800307050940c1e5200c0c50401040c1c1d081030344060000c14032410b140e08031001214100001c00c0004a08001d44680c2100a80c02481e0000c0d801000c031000b0001c1217014000c3d1426180c00b5030755a040810210704480261154000714604000240b0990061900d28804c10486082a01c00f000862608404550070260f09981c490207111054000413001c2982c0800d10046150001c0f94002c00c0743d1300340071130084c2e0ba0b014521007135687e01c41060100d44050200d00c80208015542d0b010001d40e100f44100250080303a03c0c04c01624140138001c0b64000000c51080b400100020000664030001d0407507038500405c16560b2a03030040010314085480302d1407 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 711602041 1250 711600791 711600823
    0x1240f030f320a11100f0f20070306050c04030b06060f04030b100501031a0d0f050a1a040b01150f1206180615030507021f0609110c1b030a11060c 64
    0x9041d292030200132044400d280548a011040d00c0402c10b940d0000b01200030b17078203501d0002c0c0d8480d1185402e8640711802891030490018000100781251000103030b403000c6034003a110900030798540d45a002c6851145010240c0843c006000089050030504c1c010483c000300314400500d010f61320f4880154a110507a00c4002200c3c04810420a0f580d00d401b8401c4506441950a8203480300e59002500c05819003c000304203100a207005014018240400c00f413403500514203210124103184014584081110300301c50758601c550000c60825583c6100720302d080c3c0183c480703010076103981d0700544800c079604000740059a00c8040204510304e0310b8084001400004901203209410040c40340100c0e184035256500305460700701041a81c42c1e0008040041000c805001030307249130000c0080d0003610240d00410384c0305040110305004600590000c06940c060354050b6600c800703440040c50b80da02d003042d50181d41039104121800100f031900114444a18001b070240746041801e40303072070b824103000d00d81c41890 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 711603291 1250 711602041 711602053
    0xb060706020a020109140606330a021f0213030809041104060302120a1401060c030e190806060102010903050904021803060403080f0f1b091201240f030f32 68
    0x100700d80b65492940440d8131b03e000c4c040034500b180206804203c0c02074207450303684e0700a0280ca8885886486584d4108030289043e03a2000d101c00003035a40c1e18401f62119031240ea820607414042e03020320940e001c60500518082c50700d4030307540b104034070340d0080041194040d0b41d03103028000e5840180001c000a000940b80036840e40b01141104101681c010100c0b44070504141038010442883c40328103044d5212805d01796442005414102c03214901613504075040300401d18002c88000b002c103c0c1d841108c4211048980c170743e84d1800128240c3e095a080100807400510210340303145451f030043c02e40d21010b000d465925081420001c0c1c40d081042da800ea004c039004505201a00a100711480d40c0115608501001e0b401d28600a04002c05c00c40d0041802c0400414070021a03542c0c5010301c007104296500034400c3e43c101403401501c22080c240d0800c00c0400c030fa24002000581d0b1030380b403002c0300d0b00004941c05a034810f0300d5420140c07480d01d0050711490b4100703041010310307424024201e2905525100a200c = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 711604541 1250 711603291 711603293
    0x190b0a0c081204260c030904090804090501080309040e011527051f050603010b070b0402010c0516090b0d080f07170f04060305060f030a0f0809030106090519020705030a030b060706020a020109 84
    0xe488000c0e4886113402410044551040030020131104400e80944001404095070b00380740d5114080c0d0b070003045030542000000202c800700000648580d00c0120b81c2080040da4843c155400c03141d40d401a00c500c4181c1a500b04030181c07410080103945d41241c40c0c9165081c907140502000c40b0001c540e04e080c5c5510101d440c4020100c0d0764100c0d0081c1502b900c0042c42c41d4100b51242851b4007400c20020416035440c1c0c0007804592259807021a640e80c4101200c20300042c0c0000c2c4441030a5a0045018483c940034022480307250882c01e42d07200e250032140540c54012607030496160740c0e201c514240d8281000031000c0345540c190a00602d400b0714090551501c0d582000d0000f4140d5a0103440c05200314001001981e940d580410100c10080d80117554501160062501443c01d000d00d00203603030f0551a00c5000036560000313801191040409001103082d01e031005450740d00701d004940c0b02038005e600c14801008000d00961100f2091035008041c5401c01d40c1d030342c1d692016a0701c01050280142d450f6040c0d48 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 711605791 1250 711604541 711604583
    0xc07090f0b01050909190b060f031504180b0c0912030417070b030f0618070509011404030302061b070204020d09150605100e010507060c03050402190b0a0c081204 71
    0x1001c07400d00e8114a040d01d5000017522041c0040c009110180c00100b51160142d1207900c03d41840502924054565080700b10144443c4c00c21212445400c3d20a20b10790010b150500c16070300a03400c0b000f000b440345070503500c5405401c0001001400b01000070884458a590703500460f415640b800e40042d0754403402d08041002803044200100c2156100c04810f1010340c0d4110b0070b4a40c0000a010348031450780e503d0300021502c10203140905001001d0030300b4014a581e00c1402021518002e0320703422400c2c4064103c80c000c601c2030303200140058020741f0128070120000d000b4031a081240d0401641450682c0e00010201d03030024150200e815901c281c0c500410294a04040f0100d60340101004807038541030110b0061031820091f01c1c100705094510030000e88c040c00c143e441c4c10b81c100c0c00c00c00c012441d160300500182010b40301a0f110322049012000f04050810410050f81c05074030186051950205041d00c0c04018074104641052062000705043e0b07083d80d1440e032096024149580300740712805949 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 711607041 1250 711605791 711605801
    0x190b0417090102030d020906072414090312100305060a02072010030f1413300c020111031201150e0a0e060f061b0607030b100809030c07090f 62
    0x10003054001c1c400444140c0e00031080e0b42e0702c1480e182025a9403110080001c905110f2000011f1140120201200c0c0248002402c281004010b0400308000041420251040a0f04448400c00e550080225042c40007062404a4101c40c0c240b1192040c40d841b0790b9002d0624804440b07a165070307a8081b850300180066803a0280c1d561103503100514801c0840790209000201403080e47c8145501c5101504c0c00a000354084a81659640d1703165016080845820b59900e02542c0143c60110312003004000c44500d1003800024841003255520b6082c60401c03007540c2d000300342d02040c2d05101220b00c0340c030b41144080c0002c203101909104809419170410480308a1020072044840400c5039982451a031070311050707020026103000740c900d58020f40e6000d0010301500c0820903050f41110011818031180322007149649a0f806c1d1072400d4809580d140d010860499800a05095001808008078039109009105984d000036000c4c0a0303034a4080c6441000c0e10781441503129551441d070f01c0300c0170310005000b403050b = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 711608291 1250 711607041 711607073
    0x1b0306010b460e09040f03140a03091104020f0706051003080304050d09080607020312251e170f060d020a12140d090e1306050c0d050f0610050a02190b04 67
    0x320722080c503800c01080403400010001000c00020640c035600341401059505400310b80100c8e0300c3c0ea0f070081c6d0640107000d8100b10800329400c0d02c04010300004e1f8a814000e031103500d200d0a400e50708004058444501918001d003410100c41d014050100108100c0801980f1072401007005001d80c001c6154010506804d907404412036130000300030700160359408000c5076100e4050b2707440e0350400d0b214107900d14000c04a0f1074500c100920109100c3c1e44050700a151040090b03030350b90882c0b160a800c510103850b1081c400c04010440180c660004c0e1ba4049110180ca4102c0740c080e01c0d204089000394041905c1011a80089080300e0480901404104034400010288170708100a0001400c61507000f514031030250181c400c4007085200000c0d0502400b00c80590070980140c0207100504002c0e4922019510814100b2080c60404000401e03e410003400280105400341400c0300c0d41c100a2812602070304070b22070300700850040200c3c0a628810602105070458007503d901c000030f090502c1c1c0f203004800800700c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 711609541 1250 711608291 711608297
    0x301050402130c0306170105041406070e120a0213060f09021213050f0d09050a15090510210c170f0402011206031209081b0306010b46 59
    0x4000040e192082d03841c0d540ca91500d0007140600c20500700ba0094541e40c1c100c1042117000c103c68078000c45054100a01890065220344a40208881119118801200d82c103020030101c640e0400b6030b0030724540b02000940902c05807400c046159002940f02050000c00d210800d4648105010109500520750003c25031458214a4618094406910f110004129124401c0b21940003402c0c054284000c0580e0540c0e00c064903031072008000b000c1c00b219024050340e40115200d01c0e0200b080c40c01c1100051059100d51101400743c6d152108120109110107c42000c02c1960800c07003100c00c00998050f603c0000c00f10f404100032400c10001005a900300070300c00c407000700c48428440300c491061800f81d04190207281081d980600740d0014805014203500c02400c0d41c101c3d04a01e07003da5070000c889020b580c40d150965a101c5106801158801c882030080c90f41070700071800400619000000900d81101c03c060b041c41c0711611450203102513001521310110007020f020041903190800740c80304076608842d007 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 711610791 1250 711609541 711609551
    0x31603051e06060a0c080309011a10021e1e010f15030c0e09030906070308040c0f2612040f1d0f0a090318060207030c08011b1215230301 60
    0x10003107041d07880c0600500d0207200300048180c8444d12802840400c1600701d0b07007190740ca0400c911014000d02c2c01082c26103040821101540651600c41982d0000101507402000c240c490305413020307012203035121056014440d070b4054111446c2c6480300c08031100d42c90000002d10800a000c0581a00c02d07510410513102c2440c8405e00014075a01e2404054442c054543c4501c0d503980c807802455845034a000680c42200032030030f0000c06901581d564421446a0814140540c0d00d140c1c02901c01c10b83c0c0200200000c4006040e451105051440d018030301c0341030100c2e01c10589500c0500c002d0b42c81b43e048286844101c00c02030107140c070314032010800455400d0740300b030b03840c54007100882c81c214015143c10345064032150100e05140c4913410318014003180c5151000700b5a507030440695103510a200840f840c444100b0006101c10040c0720720085100780300002a180b5441d14801c403610342e01a00e64030200d80c0ea40344031401c0705940e1965a4050641d8400c501811050503458185102480d4900382c07081c3c0c140 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 711612041 1250 711610791 711610831
    0x3011b020304063e01060905040b04030e0d080315010e190503060c120705030406021207210207050703030804020d050d05030a060503161a091807090501020d020d080703020f03160305 80
    0x44d040b20104000d00d29031216444801c2c0616024158551200f261a401d04041c0810b0007009607200340954402e842e001009090107050000882c040b010141224505000040c804001031658040300d0105240c24540008158002698403110804480100d151686d0611880c201004165003108000c0c01142c240345054101c43c1480100600f2041049004130100d8108841c54064401401003d801c1c1905490603c8004001d421195140c110030300096000e821441a42d10032106865081000303002c0150460f1820f03100184040d200301e80041648100c000401c2d800c0c0702e02c90301c0d0841950742a40d46e0a03c40e805c00140c60040e08044e00c80e401c4158549441920301d41c0d0b2a048034080100381982410545281166000b00001c40c1c0d04640061810030303500365200100d9104041617160180c08a440da00126070b5100c800100c0d01c056404082c40e0103181740030707e6401b80c2c441201e20700589442040b131a660030075002a2002c580f0421220303e5080015054086c541e8030000140c50711001300c1035 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 711613291 1250 711612041 711612107
    0xa08060a05010f12050615041e050402011b08160809031603021801060e010f1101060608041407060c080c010902040c2019030c050f1f0c030c080a050603011b02030406 73
    0x9820303420041104020056a501c88d500408a40c086005820130100081c0b8000005840111000c0f030000302c07860300110496401f0002e0004039900102440d040c4124a2003c0b14803051401050307410180600103524183da00704180e1812880c100c00000b10720745580305000e1707200010002d42c0040d076041c5005010040d401f240e4452810002d00c0d014007443d030700010940312a910501201090b509100000c25981c4d00451034501844c49103c032150500d4001800e5615095075004560011b04851800c0000c02e899101404070007445100004600403164002404c40785070f601d0090101e030480d8a14400510640241c124801082025041703c0c100300c1f00200803655160300082c2401400120750062000c104401801c2c101d0185c01c40710120701e07a01004150840e41c03650f591019080940303525080d840390150203401c540f03580f035840702500d0714034a001c040c1030300a100c03d4066507074400103503020f10303d5a0040b40002442d006191303181d080c15001003540c080384070301b0401c9105500d420001816 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 711614541 1250 711613291 711613303
    0x40501120c0b121f0807080d020c0f060906030a0204090f061e0503071a0403080c160b07030f11030918060a0e0405150702150103060c08010923060a08060a05010f1205 73
    0x903c4c07001207070740c680d031035410940f08809a401a0103203100d4007001054602c00001c1c1007a100d200341d001c8640a0000c481082611030108441c01d0b0010720601c08080325081400103142c100c5211a4094209a2111088000c0391503408020180035100c5004000702c02c403d8081c3c440291a401007a0383c10341c20b04010031317500c400b1485803c510380c1041d40a01508144c0b40c06440245a01c43c036140c1d581d1403580341c980e0340e440f94090100d0710303070444800001e2060070800403103504541c16101c2c0c613140105840152190822040115568002008410900e5884900300244089042da03010194208401800021700c2960031201e4408088011321010400001da4461140ac1c003145008407543c40000c101e0410500b4041c0040c950b01d04d50020041240725001402071102964407910f02d40c0e070f2810400705036031000500e024085150448088616480100345034452005040d005c0c00d55aa251001d01c0c004040780c04641003a621001440203030440400d0f20010050f100c0428540b41858542d1520340c1 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 711615791 1250 711614541 711614551
    0x80a020c07140d06020d0c1b03020c040f060902070c030308090c010915110f100f4506051006030c140a0e0604080616020d09051509040501120c0b12 65
    0x41c80700b4200541c243d5a101100b030840d0751043d429520f5400708001c45010708482840322010503000c0b0545a034092001c000b00035015055070051414640b00c001b8003004100245080c0c82c00c0d9110b0380e011652400350b000030000700b441814241030b82071035800d0041144101030410f14450b0451442c0c99096030348070a851094401c48589180d02c110446000c0e40c840792518812000c46c000c40403000c002010105034491004201807080c003090280f01d050780304580d40e084c26054038408020000d0482015001600e02d08400a00103c040c2a0018903251104680f05c000301e130300c6a283c10801140300c00c000081001012181018401d1010811015204685d0041d8000d580030012801401603441018170a40501c000781c00c6d00c3da55502c842081da21194120380401c40c1d002500681c41c03d040c4002940300e200c07400c5650311480e2074181010880d07903030220444c0010400c424002142d19966511172240201684034070701402070394510340420903408517031103010540300602c25a890540010500d50b03100d = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 711617041 1250 711615791 711615809
    0x10b0418110f09090703110102010216080a110316050f01090507050618102f061305030d0501151d010e041817090301180f080a120c0c03080a020c07 65
    0xa48036010400040c1c18082c159032040c0e042d8207200100c4000315690090384d01030610003900c2c1c000800107909078840c07130041c440500c0303550380c251000c036902c00090400c0381e04919159030a1203c1da0303280ca146801c40000c0b100040c8100550400300a01000f20350303c50215003000340303c0600642c8800c2d842c4c00452286500444000680300e0042103008084401c0b08002460342c0c86c103410198008001200006170351050345400804951000303543c40d01243c4450a00001302040c4e03032a86a6031200b004a05800c461381d00c402e11680080085502555018003510361000c11220310386480103117681e81c141d0000307400000005101c1303103030b980c840c03010300c1485d034165000310345a605008690000250704402511031001d90f0072508507010309a00a1030b0441c4100d000f03228154100c0c40700039004c1c004900080104884502c9038002842120252022621500b0070764628400e81c403944098070905c880c20000500c25508800030581c0140c200e0341c015509030011418842025000c640d83c4006009008030 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 711618291 1250 711617041 711617063
    0x1106030613020301030602070314130b1c051305070b0f030417070f06060302090903161b08060c031b070807020103050c0405180a0c030b0303030a0b010905041a03010b0418 75
    0x1158844181c019030445074141c0455880d03a590401c2802508084d00480010b0079403c0d20492a040f220261203404a124000c1c641280c0740c581048943d5000300c1c8410000305028100c0c041c1c0c0006445240c2c4218140300101415201c145000b50900000d9009910b0510003408400000205401900c0e031055001a5401c40854512200803041c014200024140307140d211081d420031019402120480c2d1090350000c0040d2504d404064a9002d199040060308440d13503c18408500b0380ba5040711060b155560710451381380c0700c1c991141400301c2103408040c400400410300c01c1d0a0b205085c02082461170342582410642190750ba80054800c0400c042c0c1015112000300350000c16000c116002440c008222500c4802c0c0d180f00312034000000c4030102c0d041d5282c140b000250742d009010310004031034003d026600d1981c442c01000024904001035504019181201007800e482e50f2007111082c1e14038420158050007200d04141c2900c000115003409103041450781103100b07020500c02080190301100d070343c103 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 711619541 1250 711618291 711618301
    0x150f121c0f09031217130302120a0c0f08090a0303021f060302060702060d0608030406030c2303060603100504020d02030402040c0f140a05090621180601120f0203010e0615010309110603 81
    0xa002400714840040b118445c4144a1a90100c2410f02d400c644203400742d0300d40c8002908100c1c1c55010381005500800e40000e00d0b03c00054440000704d00c95881002d0140c1072106640200708541c110360412009640f010f4540c01c194002d290b80300383d1009445605000c031034210390116105010f007200090081601140c48004003003181c11902c0a41480c000302c0e500c03260f40b18030090161181030080c1011501d00380b010040703684000036440065842880c440c0c915111007042c49004d0b8001000541020000d4601141a640b24001070600e00707480c24002d42c481c01c0034010070045402400207403081c03140d051070840246420111208a4452080900345ca85c0c0864a050711244941012280c1c00b0b600082d00c90071070007112a10741c040b046210280740081c0d1329071074601945c0c00c50004011503035000d10700401265000001020b2005d100fa100f1075160095980802c0c02d6411182c041c01090f0010010040c602e107804100d803020400034078041c8220b00c00c6440303504040201c6803115001c2c041c0080041c1c = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 711620791 1250 711619541 711619547
    0x32d090418050604050c12010b0a1401050c0a0b0a1431020a170c03060114220f0c031b0804060c050c06010b03100b04030209150f121c0f090312 63
    0x44100d80140954800307250501d030590706c801c040c480c228401c0d18003040300b1500200503c240141d8500261241c142542000d00548801c821041503d040140810600000000510812030001d104139004003031810003a4100d001d55445040303400500208400b0825401c0c0303480c40e034190003040c06510440700151880000c1486416010207500a81105000104503c0502c0184007a245c0101a60320480b0f00307404054480e070007880341c0c445503890f5002c40007031898a1007000d0801c4084440030701245c0301100342d0310150b03040030044c80703000790392001d2641032250540142c2c50941e030b003148041902403922704094041d002c003401c080c0400b551802c1e101c0d009070050301256007403a0800100c400640e501d100f03480080e80200d030100e00c9900038100c0081c240c5001d006031020790364020401c030b005503600c10b2100c180e03e0452009a602208480068007551214120900c624441c80007a00c01445240c582e035135424203d001c20270420900000c090f000304e6000400e01c1c1a40d510011054580000c04011 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 711622041 1250 711620791 711620831
    0x140f0d18092d18050c090106090509010312050912030d200d0f0207230d0801230109050a0801020702010305100305121804021324020c010c0302010f0509032d0904 71
    0x103807401c905884070f02c105001e40002d0242a4440440d107804280c2e8a410086580229920039190851000401800051003107080c0780301e4a0fa691911a0030314065000080414070250800c072401e401c00140102080030500a0903508c407003142101c068001c40d50040c40a902c10504c400d00d9141d41c805480311080d149070112442141c210200302c19025500042540ea129200f84245252090242d081c207018043c0141030f040300c1e0151400c07010159504c6811122401e444015410071003115804962580e68060b00710207442c5110005032540800e100141c1101e202405000217400480380420006a000031801d91060341d4806083e1180c5007642c1c414030014004840640c06030010402484607000f84144600b03c40c18540d003c0d06200300174902d50101c160404841d0016040b00001016030350141c2d00404103603110b44000180040241048001c640040c0e032b060001d5000000d00100d980d50741d85402219055000d071030b0100c4045040410014400d60f4802c07405135880d42c1529110300000c06d20 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 711623291 1250 711622041 711622061
    0x20309030709140108060c070f022205090c040207050c04180b0103050105042010030509150c03100f060203090405071b03081b090904140f0d18092d 65
    0x4540e8081d4951000030b000d0000c40346288a0340a079040009035500000401902074600d05070242c1c546030705621a410104c58010050303800280041c107802c244410202c0a50000c015100c00251380d003440011942001088950380703129030300500c00a00483d001240c1a0200f00080b500010310009054286d0400080720390060401c0c40404000024044190880d500c00c5118521481c00054800c0c3c92860074148001c6e9550000a41001841e046000f0b6000c150000e9141046452090554002884c40002100c480041a074040244140000d070710007420054040e00c50303164416418914020341d28000d20314114451500d0700089010a0300440d100300c515127141241c030140409071705000e044484146c828807009020041c21039024220340c1305894010400034a8200c80d40c80355103501c1e01e80e40d08055021401c2c0145080311900303080402103041000c04a443d180780441e08458030000c40049a40310900d01810007500380420002e80b10707920702071106205012941c980c0e07404010001c2040d800 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 711624541 1250 711623291 711623293
    0x40c023d09060b0a0b030a050402031c0e030f0708060703020d18110a0608060a030602030618040f170418050403120f0b0a082b030905120301080f010c08010909020102030903 76
    0x3000d4101031020307009415001d018010900c0110030500078060700c002c1501c04c44024900620119803409110b42000c0c0e04a4002000c50f044030762034030085c400104c1c01c26800382c0440e03210004114242000c0c4a450440e05501001e07104091900300240d4594034002c144604055000407182242c0b10342d54884080c00020f1100d5003100c1c0050314024081c01840080a8424050414001a100e02c1502d241c1d01c01e40e0040c0208403614695610140a5080a0030003903004103a44049200581d51441541c0f2850280b94004070781d00090500c1036000210254072109820708110900a060318071444116542c840c280000c0e441c0e495041c11140c09010f210107840050410810340c810110b0358004c41503100c41254140d0019540d0305c40341d9510311810100c1080300344031200070003c0c0441c661144600c0c01d03080c240440d42c4060381d9180c40c1480e075000e4100345a400040010310012800300041d44905001000802905101e4400070300160710511500707051640f0303812844216442032043e00c00140303001c4c0c = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 711625791 1250 711624541 711624643
    0x30a15090c15080a050106140d09080f090901120b060d080d05090607020d0306031203150b0403080d140708220503030a020919060c021c0206030a050411040c02 70
    0x82005810444401c880000040f9101c000c1200d42d4914480c96048650503203d072010341900a481118641080c1c640402c00c0703564400d10b801140300c000050084000c0b40340c41c241c1d9400000100b045081040c3c1010001409000c070b61000138940c484940c0c1c200c0803c40f08222071451914181106104030040318800c0c0d030401c0280405240c0000359035000c3d144580a03260080c02d440b03001c50407540a0301c17024091031080071700689040e02a91200d16a1407050051824454a45030400141c0d40300e98000c031040c1a00080405a400c01441035410400042d01c0d10744080c141404001c180c2134001e8000c90106003010342100d17609240b00b504000c0b440d40082a65124902403820701c0c000e410801090b4051149440c1e860041c03d0030003054400d8a8040d25081c2010142c0d40900c510350b6260041094840c08000340c4002603515407000d1031007491400307404600c42c5010b190a074200740e281c0411074025401e10001c41c0d09143c0100c0d17032080424078400003034246000c21803900c204180b0702c160301328903840780 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 711627041 1250 711625791 711625799
    0xf120a0c080106080a0206030118020c0d08070f03020c0a030e0102190b0f070309080d0509160e1008010b010c150f060b12100e040f0204060302030d090e0a0209030a15090c 75
    0x48040d8008559003200208001503503861815100c21111030000d512200030001407107400307409903200610240e03960703005080c035995120b8645480c020781c2c06a0042902d080070800110717400f100300c03003c0f66428a0154180f464907900c2ca40c0e10421454000c080c020000d5a158041e442003043c2c01c04e80f400d06c070014001c0121801c00b646043c03401d85640310f4040803e80003d003030702e0190240400c1c0b035900080741440c00c151b92410000500c4090060601c501a03822941c0c4100c000382c5200028000c0500c8490b424244030b5281001c0c0c900b20b40c48158241d04240b00d0791110303030704501000c0119030803070380710301c03040f40b01e400c0f0000107010000c26010b10070324280780400d200d2051005000d44030030b01d00219a0076140d1900c5174030400c05610405082c50310325800140080c0304012601e00040c4007510201d1903940329070002e400d20181c00f09001c00220204410801704a10010003500005074900442c034104403203020076142c01e90188084c3c000b80840004c10121030703403a44042c4c0542d4010b10410802619 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 711628291 1250 711627041 711627053
    0x31709150d0e101404022e11060a060f060e0604030507080708060709120f02061c0b0a060806030a06050907030503030103060c0f11210421020411180f120a 68
    0x1c018140961050f6941d0043c4800700d480f82c0718400e50708240000d001e641e030f9403c220640c15498141514584050201158540c18200400a0202d6501c8113602400b011050900d0000d0040c180c02695080c250100b100030041240e043c1038454902d4403102e240e902ca804143c80e4440c6600c001d05a1250590005160101003075180c01d813100441592229100d034002150184217501480d40320752000700c0104005561034844600c010b201030308490402c80b508260b41440d00c061058101d62640f0781803103160514209403207102415080c204005141480000709940d10305591000748010f03a100d001c0380c41087d041002400555024003207a69941c1c491900001600c030069a58010680c051040c00ca0b42c5d008007000102da4045200900d40303d11411101d4020040c040b03002d030404035003080049040d11402407200f26240308400302c00c51101103803050000310348201c0000001c1c0d25041c001d1000c50255801c1072200312000711580e5042d80004d00016503060b0184018200c3d910494503203c041080b = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 711629541 1250 711628291 711628301
    0x1409060a1509080a0507150c1e02040f14011e0b1210030804080a0218010e0f04030909090b160e060415170f0603010507050c0c011211070f110604031709150d 69
    0x900047d4406c1c1c0008105015101c0d40c0031500b00420400c0d4401402086550038242035220038001400481c031022001150300440b074160303060074008000c80c00103124400c2c2021001c0418802c00113040c28003071614014800d903015041407003084d845254082001480c01c6130304e03070f006035400600055440e6a5128505e66880700700074128040da400102028448440112890487c0c004c249660301e40d0344c85261000892500501c118140803503810f010030f01c40078a100d0000b0303040c403d00a45055007042c1075070000070b03a004030018080002001f400c00603078550b0f10a072000c07140300640081200c041c40c02c050b10010003108802c0c01c628103010411880b5410414410b00034402540200701d00e455685084880c0d2207100e49840361a80000010031807944a21540900c2c500e80b007034009034003a0902190141c0764050107054808254101081c4280012815114015502120690315140c41c0da5070710340741c3c820031f0220080d0005001c41c402c0c070343c3c0c2c44141c004001000e15142160381d905d611000074000f44 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 711630791 1250 711629541 711629549
    0x6040b041706070c1101030513050f011e0605010f12093c0b011a0918071b03020d05070813080304060201240312271409060a1509080a0507 61
    0x4824072011a815601914144c09295002242e103154a031480005501508014003001e1020501900d5940811070034024483c003c9400e03000400e2421030440b004c88514400e001c10800fa038a488802c00880e0b800c001c028085d81e8840c140402001d4001d4641c000074031082c9805003256262200e50b1841d45080b10200d10001c00d45040d04108170f5003505030710b284850300c1100070400007601005001000d0740507081507440d00428030851401c031090300410f811581042031085028845000d01c00401e401100550040e944030494031584101038500a6847c9900d0841c101401b80000701c80c3c0901074080d041f15a000c8000e514880083c2da215401541da910910a4a006511704101c44440d0901914280c200302c0700321082507a220b0854560401c0c004c1c2d010413040038407110040ca072056190a03503803000ca100e330700c108044c0c01a251108062107600c400040900c6243d000302000500c2d51a041a5001d451004280510015115a055480840329044200948164041e44080050001d407480942d = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 711632041 1250 711630791 711630793
    0x304060b090708161206170604030e0907050301120c170f060a02120604020906042105011505130b030c0604091505040c1202070302070506030406050a0b01181406040b0417 75
    0x90340d21180120f81000040e00d0050780d00b16480307074036424203201e903c1040389040410000180b1541d910314101072100300302988420354021600300414543c01403203401c0c425100341c1d10210790745440c80004060703102c140601e079505480f551a404c14059006171402c054055503203034071480f10172070040e148d4948110102c4101403040900268a07161513000b5500300300c0e050f05a58800d900d6a004101c00b035042400b045c0e400c01400e003c0055011040c150a14803e90700141c40a4522101d040542c2980d100d804040c00d003041043e410030140e00d95009410108040500c00110030512400080c240000408016070105012030003064100c0554040503a4003203102c204080c595641003030000b500ca0441840000c90f80109601c104200789400420225200344180c840160300e032400900c0783e42041e41d055410b10340c0c071801c03c4600241b0340314001451500b4200800200301c0412011605a10703801603009030540009070120548400c0181c401421140f4900d98071103841c4d01070300c0707101200502c03001d00c6 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 711633291 1250 711632041 711632059
    0x5100b0d0902131a060c01153309050105220602010f150f0b25030c110406030b0c070c05181f030b01091a0a0602030408010b1f030b03120304060b 64
    0x24070285413190f01002011489010001140442040f409401240034001a5500c4200c001d440e60900244480074010680448184503443c01c9200441c1e400695050300d62086520900c0d2441e420003001c1046600900e00f06a0b903841900c2c111070413001d408800382005052500210f40950107400c401142c054080c0100000c6000d400144100d400d0303442142c0f9000b11800301070040c0f110041c0201007412100d8003008030b02c0c82d082c444000c11620303540c0c2500012141d0300c2403010401040078092a00348202c0f010b000040c115222007820385e1015000020b00704001030b1000402034140303d40300c01050018150146400b4900c560a9404001c4841114510344c1da0b900c3c1b184862218480030a80790800203034440d030fa080c0290000106444842d0302500d402d11204545507984800c000c03006080240c1c007440c0c0b201d00d420b203800d003545d00980c0801c1c890082c034440c09002d41c4c0360ba800d003070080116140200e4150396003800311b414458480c4507a40c3c9a5030000401c030900055400403015008182c1c0c00b019 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 711634541 1250 711633291 711633319
    0xd11151c0911010807170705070605091b060a21060e0108032b0b060a020a0303050a020a171314071404090b06091f031104051305030d05100b0d0902 65
    0xc11620700d944000d000741c8020b1403404155100d4001e139584000b01c2c0c10f0200c60414907201550b45c1d071a044075820005400004c009041003c4d500800313401495240c003c101c203d140f4000354898a8000c0182da0060b2008034140071094070803104469402600042502c1600c0b29440b030802600349405141c04a0384008000103407000000100d4000c40741c40902e00c0c5002030f400c645000c3c00210b402c0c41150340c4e070300c5011007121070744c03038400074800702c0c102e5002029024154a006001daa0005000001c11031042c0325014010b50030240d8034410030900408030440e903032103081452111081081c041c000300259101e130924020006005001c1c4c4220304c2d10004c8000c0c41c0d1007044244c40321036000400c3c0c0e00c6010040b545a0800407103041d0070160301d840100c0021001500302480384010380c416901103e0805624115041c0f40c41156080120303486060a110081d1710f84503a01c0c410103107900c410550310300c00584400301038800c00d4041d117101c14003240d03540140a1100090000d800b003e0344901480360340b10f1 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 711635791 1250 711634541 711634597
    0x80309030c0102030a02060f06041d0c040b10020a0303020c010f1514030601030c12030c14031209060103050a12020712061a04050907092304030c0302060109021201050d1115 76
    0x251490031550081002340c1d1800c1d09060b40342c202030440e50704030b03032110302c2c410200d58000780c0b561000840000411041080c581000265080d01510078040c2900800c00507200e0740c085405100c0a804d8140540d42d11104180940101070030500c0b0140d8078584014900d484c52440c41d9081110028541c21403244038007002c05407509000e00c00185440e0f071a03a000c0052446140c200e8000601904245450f0496610341848210301c84407004040d4100003500c561000c3d01d02491500080b010340108101e60640d61744560320700b41804048c028001c1000d441010b9882000700700c0c080c00b44000c040000740d00c1441d1250183c881106015503c80b01c014040752503050606c03840b4440d820610061040300c0c0f078004400c000705200c03982441c6d0742250895450015007500c484d140620300ca5030b200c041c0c04505090090402006070000c9248500410400a4103c001e20508d030540c0c1084440e8081c580d028603080c1d2080c0346c0280610303000180181c441042001c440d010f441005050006003005032080c0d1644 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 711637041 1250 711635791 711635797
    0x906090d0507020f1212030610020105040f0b060d05030408060103210c0303180c180606050a0c0b13020301050f090708070509010e04030908030304141605010f0f09090204080309030c010203 83
    0xd140060010b010a01c09881d2028450080341005401c1600031111801c9040c246091440c403c1031b00d000000c144009414003060042c401c4040744020016418103544a00d454142e40780f000e0010503260000c5083d80d550111456452580802200c0d552640e6506907900c803002480166901d42c4070364040200c3d03009410000355103481c61740d6422001b0322140d07410ba000701001002a18020003615500300000c480200c64400361a14a4005414036610401c0b0004c1e120590404030402005004841c8800e81040c15209550b5020a403215241d4507082242c51813201450080c0d8150308000c2400001340c0c1034654076003d150b0001c04c3c1e504190300e0721039a50340ca007040e208070354200341d0a80040017403621100805401600c02d24140d50a2552112402e185030420307503040d600c49918801280351401c040044019410750007640890352440c4c100041c11030030119203800e00307201d4100050b0940034070924405014204035813003103481e00e0b11031407181d6030f0f03410a16a03280a8807800300c80d12600d40c000420703 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 711638291 1250 711637041 711637063
    0x10090b060d02100815060a0e0f0301090309030f0213020a0e0108010803090d060e01090602120a05100b04050105181f090b03090309121c121a010e04020c160e090609 72
    0x3030f4180b20102118100d443e204024100c2842141c1d810400034241d0f0303080002d21000c1d40c06e0741c4403400d8641d22010003080a04a4807103500c81da16124821000980156240044940042050300c00d01841d001040640048025545041c4d03c0040e0034201507800807115000f1500a9950b140305a8031341009030381e01d01c00c4000240c0c2c4404400d40f0000003e80a4216449020703000c00049041c0702180d03604000e9810416010a10006000400200c00c82d1407244079442840740d410703166a030346410740c25a454400d502070541003000020b0044044001c2e00003104a80c18007515000c0c500d4a050007800c0f00b40c1c400c002c2600040d06000f0001103180b050400c0c2ca00612205024510340000c40342040941d000c12212050300d0700541c282d6810a5030003103500508550300e034030b604402c0e54610015030100c2d03040ba44400000854032804900c0e507648003150381d400c0340d800c0d01d00581d506841070301c440c900b00040441030f111400310b0b036000c1060144080080c1c0214803200845500340c540d4040c0f184c0b180c400441c = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 711639541 1250 711638291 711638299
    0x902032a01090608061c0c0e0f070201021c0c20070504110304020a06030e0f030a03060e0106020a0515060a030501020c0a061103011a09180a0c0e030d05030f1810090b060d02 76
    0x13010540300d00c0d102c8070020426848140c1040c00c1d40190f9524004980254000d01c1c010140e1801c1110005a5480c803552001301c520007107240c1410000c3c81c000030010044e410768030030741d10b00f0100f40ea240284074130602c5509104111001e0700712103210f246c2d01c141c00d01a00e0f00460911241340c0d841c081e5042a00d005650040942030701c2c07030030400c08400400c40b20002c070b0b02c207204046840c0707800d40044c00103065545d0583d90104d061410850b890301d183c541a40301e84210360088603040c1c00300d0000700c1c282d01c1e4030f98140c0780a03038943c80c0d6400080b43d0b03100a400180641d40700140c210240c0b00001003440d8641d1240d4001e2105502c1c080c840703032950000f4820280c0714030085180d40d110903c26801044114001011400fa0a84041104d00300c04811105401c10301c1d1340b000481d08503030b005450f0302c0e005802180100021882c05000600c2400003800480b5481074010115420000000c1118080c0000d80100d81d103a83c0c40064207805400c820805441e818030000202e00242005e400030341c10715401030 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 711640791 1250 711639541 711639557
    0xc0f450e010c180302040b04020702090406060603110c0d080702030c1024080304030f1a01140a1502030d0906060317030f0a0203070c02090402120f0f06090613150902032a010906 78
    0xa021b110203440c11750255a405079003002100d0060b40e4960913175020318000e00c00019000d08084e405411101040d0528000890902c2860940c02000842c100b5442143c03030100c190b925030b244181d203075001d841d400740b100e80584040c400701c81c0074a500588001000141c0b0700c40240c1c0003488140440701c5800761140303a420400050002c80c1c84c8129509a0621440104c400d651440090100f0b507482078002034614103280856201d149485170081c0c4c0900b80e41c6840505444050102030340d82e00c220400d41c1c261940b101560800c0c0305081d030104d0001d6410041070101001c4060045036660710403106003090b02e64400c0411802243d901c00d80380b28040039150b00e04ca07043c043d002c0003001580100100c0c5d20010303c07500c1001c0d402d014003121089050300c800400c40c01c0b038136458440c10303c4001010511154051410002005060740015118030b0300010b0540b4031900c282042006400d04d03e201941511480102c10041c1802184103401045500d0050755148900001120305c86850320544001403804 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 711642041 1250 711640791 711640793
    0xe0108030a050705031c0e0d030b0a050d0f0807031e0c081e1605070503190f031412070207051215040602030903070215070c0f450e010c1803 62
    0x95030042081c54004c0084134284040b864211400d681c0d007481180059803601900c411800081101040e5049981414040c80700c200b00400d40600a610441d0311502c400a0340c00b0a02010320f21424034a50400ca03555903038000d50034060882c210354185500300c0700400d01040b45c803d2250302a40c041650102c011440c11468280c0e83c1d0380090202c00c1180944d50800014184160070f80142141078030039405020380074900410142824841c940c013503800c2800c045180001402c14650000b40d60381401c0016a1482d5405040040d000c0d2101494500d0000c0084c003001c60b40002e10901183c0c000c5546035441c0000319840c644503500e10584a07075203440d20003c9000540c01c1e0300910360284402d030850303080001c142c0000341003040c09031440e10445800564802400b00e000c2d10703800038041101010f800b40e032801103078448801c100d00e071520301c0003000b003280110700000313041d280d030700310049803064031403581c05400c400c01401c481c50701e01c18070f40c83c00340c40c1e16186000d0303060880d9401e20015141462469 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 711643291 1250 711642041 711642047
    0x20607020312070915030e1905030d0e010209030a0309080d05120a0506010e060409060e01140306010303030f09020a082a280806070518060415030b010c05030d0c02070e0108030a 78
    0x1016100f981807101c120300200c2c0c0380c0c80303c1c940804240c5140e0b03008076004034044a028105100c0c0e482c840300c0342046141840200c2c000100b1070351101e10300007000501c400c04060303082c020f000d04207402d5818010161000107042d80122031105483c180c0003070320340104011702e00b40c80b05c3c400c140c500c00500802c039001850710316180d805980c1c13068041c1040040c07642d51100040e01c1d03500c260400b01c00709540c0c03401445040120000c55024113445808071019013090400a652100148402420580c40c0c0004403201090307504030b29400c03a405071040782002d88030000030b5224004a5141158409207803420503080c4400c040784803081d1800341036100803d03400a88840c02c00c15038071440c0c0a9085540001450b01d4040008a01c1244107030b6403281c0b61845284010010003c28079101e206000a00083c4140d2042003402d1140188034123001440b404003000580e201004902c024096000c04614000c0700c0c0c0d460307001481c00c01c01c1031b0300340c9840c41e4a5a542520b05902801200e5030382c0e01c1400340c80c1807140 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 711644541 1250 711643291 711643327
    0xa090e0702100e030408160501020307240204090903030b030706080105130e060c070c060c08030c030a1503140d0908070b0a051905041a07020904110111030f0c0705010206070203 78
    0x103080d2050314414010a203001043e541c0d400080511540001010011100700340250102e0400b44000c44100a18060000755130740601c1070054200c580030a00c2601a04800107151032641341c2c6003040d9100d50359201020001e2084881c00c0d40400d04042044256141c0420420161085a01d49000c00c1c1d0802c000e00041c0410704500002950b5101400d00444100b004014070404180c0803580ea11040307460210540323503c552006c0c0900c1001c880b51800107041d4800d59a0140302c0c3d002071500d0f1780d80c8400c4240a004003040461901180c09004410320504200c013148140d02c030012601002100c5c0011104e19000707213b03024003900003a00500000d0b00304001040f406042d850304500f0410701d42c640b0314080c640524080c0100d82c001a04014808003d102e50701040d80107003a460074820726401003406441c008200030b11191421078a0b40c0300d6070280c8202228a001002101c0c2c4500403d0114400c60340060000c2050348070348403000070b4a42c80001c5151190b0002e130b010358180b84001d14135400c140 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 711645791 1250 711644541 711644551
    0xe07030605070c02090a151e0e270a030801080a0b01090b12070e0601030515030a0609021903030512060303190c0303090b090a06050c1303020105030a020f0403050a05010b060a090e 79
    0x810f1a24090141e0f685c2801280035411001c400202d01501105001e0140301641c0820035440312103040c82d0300c046050740000304592482c0d070700c4203c0c0e0b40d40004c05c10710320003020700d03520240749010748282001c0c01c0040c82d0018544244c0324602c50341d80b214011540c451512000802e4840010300601207030f0400d41045402e030700050608001e00034610700082c00c080c0c254002d183c00f42d10100c2009215a4140989500f0050412203158030504000200342c03200900d0101618881d1281214011511405810b80280d4002001c42003090384a00c0d00800740c1c0e01c51110034004060000104006180110480e4034a4410511030038007844c210b241500c01801041c015814581c0d1400b000c004500705121141c41050030f50084c0440c59117070301e09002120702c054400001140140080c22400400384c04000940f80c0908040303450b55100d50b411b030003030f105510001c3d950020105002003000000244401c0c4c00d44154002c1c008900c8940a0207285c0c050990103e0000b2210a000c00250202c0c0240315005 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 711647041 1250 711645791 711645797
    0x303051e04030b0a050c0a3222081209011d1f110f0c0409140a06020901080a18080c1005101401020a0f060b03101506030c030e0703060507 61
    0x1010201003000301642140e88159031584905080014401d41440780c507601c03044c8209200e05024449000a115400c801200800081c00e00030403403130540081c403604002c0c7c9075649159036640c00140050602c07420802460f90b0301020240100d40c201000c10207511445165541c2c2f401c0405030380044501020b040e034010592010580a8455034a9001c1c01ca10581e11400725000b003e07200680041100b40c29000e81758258210340302d554103605000c54401000241100d002ca862205410b0145050080d400710101c1d61040940704070030010742e5009000c138404262036007400c1d0395883c000300382274450101030f040020300f150f01d60000040f16440900310010320b2200311444641d0301c2c2c03441c01c11607000742c454210241c03d01030104030b15900d050311040101070a10180440c0c481c5daa40300c01442c0e1030003e004003610f441d0180d1494944040219100b03160021205020308000401580c1c0401104c3c0560f0002a04250840240500078014204920840300003041c040e0b14544030f540050801038041410 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 711648291 1250 711647041 711647077
    0xb0a03080a0206010303171b0a17040b160525080d05040f022b0204240e150d0f02150904150e070c020604230402180112020c07030305 59
    0x80344402014140e221003540082601e075046080240c403e030076003003070f40340300304200d800b0807260030004050105c2202290324015120802128180c07003061004082224140000d020030040c041205080b50040361003056410b001c00703205d9801c17034143c407807908031980030701c0c0d03070b003008108070322254000005103010f070600c0d6042110b0703001c405040c2c8006580544400c940c4d14410000e41c50104c00c008001c0c0d40341c1c0341011001e950760001100c10b030342e0004040c0c852a96400080f03504444c0e04403119100503011241c1c0d40c01619a200c00b4a00c8030300740c50819884024072141c07035941c24200c00c05060b4942000360f4070b00c5030304241d0030403e40807000c44904403400010702904850342c0740c900a90040b07202c1896408001d605240031110182c2c3c0c01031200003080350441c504005600c0300b030700f141c096520088020500255643c0070703803500341c3c00c81c55907138019100040d003e1100d02c0e01081c01c543e9000990314072441c0281591110300303038002c2d13031050b01a94014040400001e809a00106288602c2c50f9085e60 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 711649541 1250 711648291 711648293
    0x3080f07031e0504020307060302040f060c0f02090106120506030d0c0f06060e0114040b042304080903120d05090607022d0f01270507030209091c020708070b19030b0a03 74
    0x54915000010300c0b40161210700f03000071440c0a0190101503c61440d0850420b031a01d0424a26209070b403103540d0900800c001c4260500c07100802091029030058400111540e40304002421906d046200f07806803807a14002c43c4041c9404105000c803d001030341c58600b5000a912000c86802c00d484c4111849580d440d40002e400d140004150b0003042c0715162044030105101c04d1001303030351141000e20301ca140b405045510324403600b03034842c080a0100c2c00d12440c0d5500c505c0c02425511135208450792521480c00411018001c40001b008214207140c1c003884103840b103a845a0b034508040c1c441c00d001da0031411022001c40700154020b070a580d041d569102c1000410211281000403084400d0410b945401b001c0d0303040100640d401810040903014800030350013a4a907552110071500000b03104031f0042003c11b5141d41c0410606034400c80c0d0115600045c006440060754031506807281c04410b0044103c0080c0030a2580140e5000e86030f00e1440103040221b9000841c010b003014088103501c0b4500c100040 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 711650791 1250 711649541 711649571
    0xf09090a090209040309150e031b031f0f06051e131401030609030201060e22030e211b060306041112010b0a202a060a020619020703080f0703 62
    0x2c4c0654080c3c1c5440c00100d0801c09400180c01003c075510b010320402d41400b00310307a02c000480e4844410a01e248001c0c4800c1d1400003420f1240c00d0341e0b01e0f144078040c130100c86511459617020488841c1004c0040014a54a40c24000309244860b6a01603180b030300c015600d40ca0420b80f44507401b507003019100003940e0749036820340c2821080c01c0e0002e580389960b036041c2e4030403d03409106000141c41e59041080a5160100c0f5000500c43c0e1102d00d00081e041178502c150402d80103500c1c0020241000b80104040d04541aa140c980800980303030320103520407a03400b07000014001c280001d031818054030180c59543d50070184001340001c19001e0002200c200f02d154259507420800c1406010120140307540c403554458020724041c00c0300395080012a107d0100c220b41a0000b610302e824448162080d0f0102d0b20307118103e04220440c0c5c2003213402003c0095a510a20342c0403600d00e1050b5140074925490846009038102240034144004011030402c4000c11702c1070000c154000d51043d0940303004210390b003200a4207 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 711652041 1250 711650791 711650809
    0x10120504050f1f061406030c130b180405070813020d020d0f1a0705030105010906031505040f02070605010b0903030f1605030d0603020f030607020712051507020c150f09090a0902 78
    0x3588403c03400104a070a041c203409014020320b501206030145a4100000444070310001c2c002000050f03001450701c0d020210910301c0d40041c050030410716150316090070f45020f90105099a00c0c40740f4030b0300d0002041207016181c024000c9054042102c400e0a4a0b82401501c130504141640e002410008400000e00d2800301c50b500288500c111043d401c641c080f542d0040d89000e0b1959091100500052005903800809641114414580030a40c512500c611041d100f000d600303c80d80050600a50718103000042e001042050300c1610b04000f980c0ea9aa42645217000700302043c0d9250308204030700940c0402c0d01c0d0107801103080440901c3c614000326540c07146540d00400070f50f0300c1c20341c880001700107520b00140014105d07841070b40500b905241c520402034941074a130066074104031914209d8001d100741000780010f0510f80500142003070810280181d911030044601c2e5100f4000d10f401c03818112001401c1d2550701521010781420280220200401200018840a140381d5644a52009a40d0340c48070 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 711653291 1250 711652041 711652063
    0x3090c090213081203040b06010309170a0f2d02151f06020303071707210b0f030d021f0e061e0702070614030402010306080304080606010e10120504050f 67
    0x6960303003401448440514420341c0011000e400c078030840c1041c407604130100d9a00513401909070041e0780d640c40040e001020307800700180200c554800d0110044031850000d0a0301e1055803180d0100e0030b841c0c2805c56810b00c488403090801740d0751000c1800309095861304078000005070b005945d0f641030100c00d100d041c1a003c41c2c0809940d00014a920348a0090319941c0c000740c0b81d984003841c40c6180841000e40901d0f4034111144c0d8900c000c100080580d40700342c1c81414003100300b030f07401700d0800c481c5007908010381f210030f000c14824a14840c0c0300101c0e1a0003d01000e40d000107030054801082844680480d68020b0450031259035203035204d10700b4800c000d0206504c2a950a00100b45000448a202e400040014040810355001503410b110703064121003868203681c54400c82070342e030380d54520040300a8090355002c0301040c80049001b24031607201041c194400e0780281e0711600c02c1c040801c01c01003c02e886120910124071050a85481c034400764000e503511901400880b4101030540c0d010354270b0300525290b = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 711654541 1250 711653291 711653309
    0x20d08041703120109090206090f06090d03230310030308090a0f080a021005091f0b03010509070317040e070309111e211e01060509040b182b03090c 65
    0x1401582080c11550644c09008805410041303004140d020680b00d20860b80c0309031103907400c0d40354100266a030070100c600f0142d001e440728004045915001d4a5000c600303203c1c0d80400040145402e0000b42c81c4141c17441a43c034513125082c210310f5500c055940340005001c4502d40d000380c0301c80a01040041003220341e0300d03100c1c1183c25a94202003074000c1c00d20080c284d000c1c102c0c906001c20b10112241c00100400b41c11018151038402c01d82c400e100400612102d8012a003650a01040140100e00411038000302d80c010510205030001401040401e80300e5402101404c802000204003c0c2e8813036842010002d100d50004000581c00310005404042078085813030551803981383c0d903c200d0420084030240030075041d0941c2d00004c0d81201203900ca610000a41c2403a40d03100c0201c0740041003d4008000811000d0403005244c1840e007810030b104401142d8000741011481e681c40e5640c40c00103980040415006090f0f40740c81000c603078000700c80c00010144010035440701d2903240400d5198a405004204c800 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 711655791 1250 711654541 711654547
    0x7060609110708071a0f0708060a03150c05070f0503040f0803192001150603060815070c0219030302061e090c0645060f0f090d061a0a0f05060403020d08041703 70
    0x10001408884020f100c64040d1007400030400025800d11f000036100307000d6282c089881080c400dc2250f0500500002070881861408440144240400100140c0c1c8000740050714230742c1c0b00e50165175a48240c00c60480d40840e00c055041c481445030441a919174142c51441524404443c1058295020b81298245032401400108035032034040c400c48000740139480203000307290f1201e400c480d0244d10080c038400c14040381285480840d52040d0000d20303222008413000e28025280c0c24000c1d0346030811519074206660700320341c9641c803446c4036840c10320404008004051004c040d40c28842290004c849100758009040c54446003140e07a0441005d100b802c13406200c1600c4451118914144801701c0c0590194400300300c05000b59001c00200c0f072420031040b052550343c0d504100802c040c09400c0b4000b078491845c1c001c0b040c40503030906d10401148501141e02507442a144c9803803d6a00c0641c0c4107556024000f0001003005003840380351a43c0035070194180c03505260f910107000e240c0810071801c600c541d0f0000 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 711657041 1250 711655791 711655801
    0x20d020415140d0507180605060a030501032d24230c070b070809030d0203040f03140f1c0605030d180e0f011413020f07060609110708071a0f 62
    0xb40c1402031003240c2116000e12040342034450300e0320390900707020798648244281416030707809150f41c000c00c0050002a01031a603c020700b040060040c0001e0004442404034510406008240720203100144412000c40c10803540303090340d030040c411202c44582c01041b02c140e082a012702e1954840c6400301042d05241c1c0c2d50014107000c400204420007400d110101c2d000b40b01c14000b01c1c806000306a0300c421a420200190703101d20b080e6030711b180103003085010070500000c00c0008109403440b0541945220361113032a10a0049c6c942e00044e0300510170f1910725007406010040312040e50141c00c244e01c04440b1000a500741c0c031080807a0404420f07004d4400400c054405201c0d541d6000d02e2140002c00700c3d4844000903062094079001205010302c140310300c403624400140340c2c0c0e0740c803500d159040c0c400c01c1c00119a01c007844802c080c201d8102040a664403880c0510015461102e4040c0c071501c08903c080c101d01d480d88598800303a1507006210241e8402d003c1c3c00240111540c00522280212000c2c2d8000d40e0510701 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 711658291 1250 711657041 711657059
    0x4051332010504030e0d030e0d08040e1003080a03200309210901080411040e06070e010e030c09012112050304060608011a100e04050c0408010506100e060304020d020415 74
    0x60111500d60701d03100070007010a505c40419501c0400841c3d07040c021b00c100b401c1c100c4581081b0810542d000e40460066020052000024002c0f1079450a03010707440d9494410740300d0560390510024143c002c2c2040303202e1503103119074012200480a030000c41441012100300300c01e180c02c2195815881e5200203e203642110114000c1c2e690722981d015001e18100c4503200080071107801600c02041d01003907143ca0710725603032160498045d00107030700100c1d0032929240400a001d8010800b1030380c0400e107401d2441e03201d4100411a04844e0304050b1a070300345a40303010000d8601d502070128014040e180403800c000050110161805841803650341c9940780d003043d081481c11107015501c110b2141e850a030182c560300c1c0040328400030070501100c0192104034254019201d5941114206901c145450200b2054482c0480584259030846008103d2a034540050000c5480301103021000701c0d442e5482c8107194900340c4000e650062000c1c0c000520100641d000c41d05540300c072540c1c5005400300003001d0100410b = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 711659541 1250 711658291 711658373
    0x105040308070c08070f140d15090303150b070302120a020309090103060902090c070201210e070815090609030d11070c0902030a0c0503072001090803011e0b04050a05040513 76
    0x144013520b03030108600d0305c00c200001040447d00030b80600709400215090041042072000340d40764606046c00880142c1c507000307004003440c0004200c42040036001140982c8420284d80166502d500101260000c880d200c0f0300c10b822014100b400c51100b080701c2c00d16502c43c004c007030780214800d40c804609094107104000000b03a0003041100c8400b000e010b03000150b80d0120f5003103000912a14001e00110b374100e2010050442c03030750301e40c880b0b20519000207840340001940d18441d42005980d0340d041c1d2a40101d1075101c000a0b01c01080e20f610030321040c2080200359011500c3d00c44130944681ca000f040f50b5803501c0418046c0d001122065010003080036100003401501507a080c0e0385040303031440c9031400c0060070030802024124194224807080b900c02090940c80840002e4016070711940329a9a490720b030601d40000c04803c0402c800284c40004c00124040c01c0e2000e80f040101150071943c01c10042c040140700041600c42060683d00246001c5213810b000c2c155041d400200070003141e40d007614118a250 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 711660791 1250 711659541 711659549
    0x1d0d03180b1921051303080a0504020a06050a0c050d03021b0a1e060e0a050309010908010b030a0b2502030408070e060603150a03052d0604020d110105040308070c0807 73
    0x810030000c00c001c2c03402003500c1d40101160030507103a0000f08203000454441c690000802142c0f034082400799031030328038151034130551107503842c43c2c1541c0d15443e148080d21030554009400018444007808424021030180c28480c002e45003100003941541c46080c9421a40c40480010a070f0000708030003101503003001c0c550185556402030400c2c91450b510080869034901c0c1010b21140607001e420100b045070340000710881c003110125000d514079800c0541d01c031343c0020a114007050000000090412041c0503c0d4100e18005026020300d00044d02c0713491b4038110041200c0258800c415030040001c088820910001285a000b5500c96007090302c1d162400ba040c0c3c2020a1f21403186040100036030361501160b500082c0b800012519581c2c14001c50b28841c0da9401c0100980100610b1814451f812105001540360389059080700d03d010404040d00e6005c10344001e50408801218440454001c2c8101e808920040c98000d141c140c0c0da46688440d0f401c10760044880c85410401082140c0040015001130 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 711662041 1250 711660791 711660809
    0x50408130e06211e0106090e011505100e01080601030b0d050601090f02090f120115060e1c0506040b04050f032206030513110d0618060f05090d1d0d0318 67
    0x9840070110155559402c01d54a03043c10070094032582980313020341000005260040d0b0600241c2095900c650103071505010603650350132085800546450038041010507000c075500c134035a03181c2e40a00116828400208124141034503005039004503107030300008200b001d0065000e0042c65041501e0401620541d060b803003e9940180800e518036500d40c44209810308044402801011f400c81f15a030152440c00805030340317801d07c55000181940c1014013002c0c1100c08590b225902441200d9000c1c011041e00c402521540c0882c2c00030307000403c084e81031908207000301d080700d030440c007100059491907000360030710316440080c1800050140c000310b420101911035410180301c0e524146c1050780f03408108142c0a080c54244010001d020746a030001d030701000790002030030302494252041c1c1d04a0302c0c540917803c46401c4e1820700c200a0000a41c802c940c0144004800380800c040d145030b080340c0310f070030700c5210100c1c031010040c1d0001e455036903404840505220341c640001481d84c46204243c8411541e2001c808 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 711663291 1250 711662041 711662089
    0x6080915090d08060a08010c270f090902030f0319020c0306060d02091e1303180612020c0f150601020616051905070606090b0f0a0509010306050408130e06 68
    0x880072011840341c40b80c050714030704104265210400516201825032041030305518200110210350b41c481081440500040c1301810780104001d80000a80c455102d2523001c94080c0c0070a00810f5142c0e0080c0444600040c126007407001002000360540c4e0100c0c200c4c181c0d54495041d010103543e014000c1059800c821005014145040c3c000b080181c128024003d10981416001030420004e4078803003a41e000c40c10888001d80d1a250002c00c0d2107801c1140180c5c0424500c804401a00308281400c0c0141d660a03600c0d2043c0c085032016200107034004d0401c80400307025041182880700010042200341e901405054075003030400d04006401e0100103040584409070070b07079100300c101e07420104562035101112035003e0303039800000c401c503000c1c010702d48001c100074105000029800041d0b00300c0480d56404482c0d0b20003c034030305e0040024480e001d11481d80c04c009948010004030b2070a6101c5035005000754140c0c2c3c98002c0c2c0302101c400103031301500f0007000c019150081c00321500744900c42c1c07030400401c1c66905035 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 711664541 1250 711663291 711663301
    0x10b010e030f03040506161403030123150901050408030d020403110a23010e0310050f071b11030a0b090d02060f0603030d0c020c04020f040806150a061407080406080915 74
    0x249a114602605010360000640700401e080006501c47d501030b00b2019942441c650f0716000340d01c0360700a00c910f5030300c4229030111601d400101440c080c45220700401e0741d440d484c1d1106501d1034a030403da000d141400700038400012508024401401a9126101700594480c114a01182d10084041300e480c0101000f03481409401400b40b4028844070a0140f01581c0c000c00e41c0049071301d244140c2c0580e4150107002c1021710582020303000745000c0c00020501d04402da55500084515500002000c2c20b08906040c00f00040360340d02810715468500034084d19051440c0c1e495042d00c506003a58040700310b80c0300260203024540d044c040150000104443c20025080c841c0000384d0b6801a01c48440d4029135415003240b00c2402000301581180014101b1f6450341c0f05158402c0c0c258005210714070840c05076100103212140407a403c01c030740e00002040104d01c641001022240380440c0d03120948101010030126011030071f42c0c400f038002456255500d018a2034500f1001d4200390400c56921900c540c02005d201d = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 711665791 1250 711664541 711664543
    0x22080118080406110c062106041a040f060b0c150a150506030a06150201090b16081f09021306170f070e010c06140414030705120d090b0108010b010e030f 67
    0xb50032120305140030103c810500003c541068900c0c0700302a4450030010b03140c2500f800240c4158070a5035030448001da190380d28030510095442c01418030b00710f280801000e85c080d28007070344005080d0302803550004400d502c1c1c52160420b0b48c020000700c000e5600c40017120b10740c120700941503070788059840e10a01c00000c4c520181d0002e1925401a80c1c451200440000c1d540100c581c0081d00a000d4540c000941d00340022000e402030014040641e104800280018408900303030040c030050816a0780c521120340c0c0c500401030300074070141d034035138130318400260002540d103419001400c542c2d4640804e50700c0c1140b82030005080280301180a40881c0045802c002014108807103060f8040c006081200307031080c403480120780035054108010b0071189400712403d0310b420360010300703440f80b44944c040c3c007124403000f0360159990044640007481c036480480115007200c3e82c02d020f0b02c007641c403002020a07901d401b9070b2445599942600071481a039501d102c2034509680c0003440220290066005c0c0c070421100300009 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 711667041 1250 711665791 711665797
    0xb071704050d121107090f0c020a08070f0c1206060906090b010e01030f02041d0f25030b1f12050c2106150f092106040b06062208011808 60
    0xa4aa07055843d103e51990380160a480307000001c0d00b041d10800c0f5100c5140c1401042c41011480601d1303d4072018840356400005d8408110383c000e1002420807165036103100c050515400e007100e9110122400144080285400e03c0800d8450300000c15a50b05044040045032041c0d0f100000306800d20030404400d0341c10a51500c2c00c01407c0c0f0740030812448844800c40030344102c0c1e001c101c00d41003c040b80f10990b0100b000d102c1c0100901a02c10900707481c1d90340c00548503501c2c5005010080700040302003809500a034018407060340c000c0e180040105008207000c0c01a90550203140c0030802d0b800d01c01c4c030012031034480c0035880869640314608244095070140902e84181c220400b490a06202160003542c4214144a204442a40e400d91340c0b8285502404280c10444040380034180c00507104485c070000380030300104c80c48420024146070b5511748a805e00020080c20721500300707a0400010601102060070340f55520004c11020100501c0e060041d070849000c8110200e00340e00c40e03c1100c1c001030110080f = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 711668291 1250 711667041 711667043
    0x30a1a1e0405270a020307090606090b07030207150503040515010b0706150306060305030d0609020906180d052406270702010209040213140301060b032d010b071704050d 74
    0x11143e40d6075400b16840c1050812002030788900800501c1c2c0007400183c803600140c402d4080c0c4452580e1a1040d02c00d03145503015000200e220554140030740380300c040c09406814024412100c40307558550b041520202001d4041001800000402c010f20804100551240c03a40120010081d8074148420126000740340005000580350700800000301e46488201c2c0141d43c20038420071045541e850071a541c1d611140404079801e0424800140719032507071013a59001c1101070000c500c0e0550800d00b0100d0340c450700701000d900a40308030722030000c50400c01506400003075441300b405401141c280c1c5d125100c440245500e01c24450400c903529408805800450110300c0c80b0b40c543d020703031943c10040e40a40140c00340c50350054404981c0030407002544452600b1101c00072200e001c2c0c502d21400385420ba0b4001d018000c2c02032401c1010a10329070040000410081c01004860100245d400c0354196910b402c3c4d1146200813008200c58050082420300c0d280d44101c5190304516103443c20000c55110801254 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 711669541 1250 711668291 711668299
    0x1020615060a090510020a1704031e052b021b24040b071b0636050306090a061b0e090a061701060801150506070b060312030a1a1e 57
    0x2c2000610380075402030340c013a010041c20308071180900c1100a6443c0c0031325070207941040e0013402d1700704140e03404811101a01e0f0003485056500416803201001d20100c0c0000303c5152145200d000e41180e01d0005001c01800c890702142800421030300000c0c5401c013107814440c03003d4000101041107658445400501d5949110381e200d0b41c0011094482e07460081da4440d1040d500c0004045080003400700e400d80500c4041c0c1ca01c0280300391104d10031030301d40d0302d040a8522000d0100460b402030744211246102042c0482c4850207280352240046030a000055403503098a5104030304100420094bc0035503400030050314002042c103440b514005240004c4078442900230411240403c2c8000c0450b08400003030300010307001e00e51420501c9076660080202e48a1351001d5440c100e804602039510a2100d0101d0b04010801420803000740c4a103c914000607101c01c0e41482640d03842d001d0042540301840c0f0440b6614000241c102c400c0d415018a000014003440c8200d501d810841c581240f00912001e10010a0b6 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 711670791 1250 711669541 711669547
    0xe0313050409030302070f030c230d031a0a03050604020f010302091302250f0b010504050114010806031e07030308060d020a030f0228030303061505031902070204060914060102061506 80
    0x403c05900900c2400000f40c0903280c04002802459000390340d000106120b0701140c0528102c000c80b8261110320301c4001c0b9403603040b211401c29020b110b5040038503903220011070b204424035840000380d01c410303040d403003103426820480c10001589050441c00d1440102070030290310b8141d03d00005820801400343c1d040c940c990118851a019086941c84a00202d00d402d031a49200c5007401c190035400444101151210a4000041060f0519000b07142c12900c0d07030a4100e802e40414001540c43c03400080c0010703018031407240d00c484814109a180300c119103080028013003c03030a43c1401058400000c080d40d0064111400c01c030010b231580010a03003200d800283c3c503a42880144002900856008292082d03e02c00c0c1d100030302c1141c038201034030045a20a440400038160b41c2c1024080c0801201c1004003c22014000140c1000b12002500300c4d54141d410010310f4140d0581c000f90407a6642c2d040301c501d00b80c0d0b6111f9451290f0a421403590000030900044c50145807140200a00c0900500c106000c3c1d4404 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 711672041 1250 711670791 711670793
    0x1e0b030907120b160c030801050f0616030e15040305030f0f2206170105030604021002030d060b090112022d0d0501080607090f06022e0914010e0313050409 68
    0x610411000d000c030704002e044a601c403410320032101d0400340d8041d0100d40321042c1040402e4010b001d80d019042c4d050311060a640c0c82c1004000c800d802062019420030010010041c200300d07004048104c40d8800c0d03d5400c0007400301c0c8180402140105c42a00d0006810001880803403000401d071110600200b02c66030f034500701400c5280041c02400611104540b0740c048038603075426022400300c140c6807155030b0001d43c2074091486420303181c030a2141c035426130010b101060141c2480400b10a83c00440e0040301e140c440b218454008903081c41d4000003140e92302080c2041e40b907038041880c40071031800d92030550034110324200900303003607070b030890101586441d02d101214001c0e100320030f40c0d00046a00358100b025695842e8801e4803010201c803900700180b01d2100c003040e204026441c19041e605c0320b0303005121000301a50003004e80701c450440c00124603007880c9140000d0680e8040c1d01d440e18400d000720303100c10900170310307403800e4440900c00104590401d018030442d220004001c2c80460310100c502181c00300d41 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 711673291 1250 711672041 711672043
    0x118020306060d0e0703050d0336020a060905090708040308070e0a17060a05010906060210020a1209050c030f0106080d0c0f020301020f21010320011e0210061e0b0309 73
    0x3d80c49200c402a41003e00010030303918003042c44801c80e40240c040d50741c000007459084084841984400c9450803000405809664a800001d80c40791000000d44c0411092038000818030012035220381c0000309103820038000741c00c0c444c0d80300750043c0c800d0a0205650925986c090410398004100074200300d00c1038000c074a19500d0800d200020040300601c00a0f0f12101c0b43d10b55201d40f000c44002c40b070343c3c1c104000001c0e4491035101ea00f00b03d80d20759010704030380d0b002130700c044020b94000000d8204020110001d002d001001c1c0c03048001d0f00c2c0c801c40051911400c00d01c14903080c2500c1c3e1204160992511604001128000c100c2c42030700e1085c1e191180c03003100d051030aa0080031406074040c0d055840400d03048c8460f1a060000c0c1b4051034100c40365400300040c51168850060f090200401c3c00d880c55100107200604a001d030f542d03010701410912280740c1c10080041c0900e1031220300300f00584c08500c0281041c541c600c500c90181041c6032110b42000301801d030940c25131465220b800d95100b0000001080220 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 711674541 1250 711673291 711673297
    0x6010911091c15110a02120909070f110712030f02010507142107090602070e040213020702040e010908090117090c220203010f091103060d080c010207080d020301030c0806011802030606 81
    0x3d440c10030001048038102e000c14a4120445110141c0309221060544202c6002503030806030000700a400c0e50b5803201003c40b00c04d1904000707402401b001c088840c21070300081c4001c0c0c000c1d000d1011600441101402c3c01028038003081221029645040e09102c2c1882d4400b20a0401009440c80142e642100303400c0644051b030314074445200300c10910180604d083d071003000b00701200c0e90f903800c0b5203105072908059078002c8800d40d0000e502001b41280f44c00c07080300507005000340500041000411010441c052825104541c1017100c504100040b500c50a6821110440068401b0348504041d40350642e130b030551305c9401440c810301c907004c10740c4034a4138000031031440000044405019034413940d48442c4180c0160082c081c91080d141003618a00040e408403047e0382c0f00e150001c000100520ba6074031200940e0b400601d600719955020403002c1c010505500040000d12440070005a4941c510301f441581c42d03035190040c00349078000390010040420400345010482c800c40d0401a500d4940e040000e035244 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 711675791 1250 711674541 711674573
    0x40b03030c01021908071119020a0803070516090614040b0d0203120309100c0516080d021201031401090206031504060509011e080c15210906010911091c 67
    0xb6000180d00701c106040e1000c07020a00100d0340b0f81d0440ca07160315509a410311401c4940113826408440007440c0d41d18803d00707400c0d00c94009045090016101c0c080903040d6030240c1020390300342c6c0c06008400d07140e0500d92000e000515401d20204107040c100440030000c0742807025403500c41c7c1c1e199400e0102d19a980c4904e0400154000d080341c02d2100080801d52046e00f00701e516104601982208001c801014050310034240c03540c0d030351145001c1c6a04010782030702040c04016944500e060000b1491118548000d19090701c819401603c039626610780720040e4801c10310030b1500c0380d040034100c0703005031180c0c0e05480c0c000352026801e1440c080980301080080500780c1c002e6611056402c000100045002c500c020100303584071505201c0c0b5190000569a032144504250b080100460070700340c640c44941c05454002c080c0700c0c00b0103458028910500030700b00e00751440069a0011030040008a01034400d10700345084418800d8200303080000080c0c1c40071b100b40c441c04800f04001e8130761420011310074159800c1c5 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 711677041 1250 711675791 711675793
    0xc09090403080403030b1e060a030603050d32040614090a06030504030201050601030b0630010906170a17031305060405071d0c040b09031903020c1507050c040b03030c 73
    0x985480d040007841c4690980b000e40c0424600880c1c80c4c81802c012401c4010f4503002e130b40341e2424010460030b100159004150760ba00300340e0b84200102c0012000c0c801c900c01c0804983e07403c0d49080d1b01c0e401c0c2c1c501d0340e854410000d0200103a62441110010304c44261004c0f59543c1c01c0c1076800c003048080da400548284106180d0044201102240064060b03005078001c40c041d5008002c5a1341c0c0c08010340c21104442c2a50707500038001d2100c417040483e503609922040d0744170201890390100c01c03035601d40400021380004491588424081c000704050502c103680d00c00e520707401420041c540d83c1740d260b1a4070b032000d4209070449001000994803002255459640c07648003044a009140600b0443d0300c8440b10b0182070383c2440c0b526541c0070220360050019019051000c0040d1620b1705d84400b0f280150301c4411515050300030002e101c80340b03030446000c071000700c0c1c001e402034175448403001d04000700704094508490700040244181c50110700c1c0041c070000815070030349001a6070001c0d440003d1841c015030b00c03a0102 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 711678291 1250 711677041 711677059
    0x11100c140127020d0204050a021b0a0311070b0a0c060207120306030203012316032d060905160c2f030601090219080c190512010f060e04050c09 63
    0x106a205501c070703808540b10b02036218003240c2100c0c00a1031000780000040e5220226a00e16405071034180d1041d50003481d0504014501101030000f21601d003d031a01010080d04070320000700c00d02d50031550f0094981da1507000b0b000030034100b880508007801495990020040c0b0001d282c81044480e0b81146d032011340000000d01c2550b40301500a01401707035404224002d5091445c04403001031035950a0958402100f9010502e0780c440c000c0d450a400e06040301d40030146c854081c2c008402c50921030708800328042c502e0ba95840410740d102025103026500ca1180540341ca0200322000350700007889103030784d185460b00e568400c0c000e003071494030845a66a880b01c544900402c090348900e0898209160030381c20303016100c0c160303a03030b07118103040340110288421008420100d940c02c0034401c0492a0340949031100311800e1108400c10701d2031002d01c4068500205000241000303c11200351070542c010200c550030054682d042034030003800c0d01c44040145000c0c6031164040303000410840d09540382c07417074081c0075404 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 711679541 1250 711678291 711678323
    0x190201090b280306140d02030703080a17100506030c071406011202010206150d170d0510030204182d050a050d08010b090306040308070509030f070512070311100c 71
    0x411030200114064000d03000000700b20b00700d0090254400b115038010340390541c034440c80240858040c829070202e81c107014004011001607050030180c800c5070303065500c0c1c0041c041a141d4004001c0c0c40902043d024030384428040025950741c0045a610580480240380c40e1840740c80d0440b8124480c0302c80d554180583c40c00440c8e54405400d035520310500036401c90703101c0d440340081124140d49003010749402c0820301600002050b400d03000180328400c08502d0610b08214008043c049640c26501000340c4022004200f00358030305401030000055940d26401b020010f5940e840f0103445045544010308a5016001c40e4002c84020060030859040815101c176000f01c0d2402503142c00d5054852800b203064000041298039890003503d00c1400050018092600c803a1400e44045c00000c007840208241003190799886e44040c40050082d1911400400446080000700054209aa01210754a9000220800c080b44034400d07010500701e01915908003d00b048641194180c01e2a54007400303406102c1c0701c0c20303 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 711680791 1250 711679541 711679567
    0xd27030308091203060a03230102121e060108040b1b07050303010e070207030c03080f09040911040c0f0206010512120f0301150c110906042403050f0c0102190201090b 73
    0x900c120041c80940c0c540881403c03000406010984496400c45a6031000340b00080f000c0550404115800c4001d29062008200d074909903808100c018100d41901c00c14800344401c10089505114605407010400d072030800b00003401400002c00140c0903404c81000300c0d82d8410400c1100d1600c10107102841da503202e15040c507503560361003882a500c15808500c0040c03080340c40030850704240c1c0da02003542201b203851912a030740b26411046495031540030821000290381c2d5140304a07580c10b40304941851038001013408210868500a0242080c0203509052450440c1e0110b40300b415501c1c103e80d05526098154240b034581812003c0d514174601c40040e8186040488401440c12220f050444440c00a2140001c440e07000c0d220200030010509400c80c9080c9103003844209502c0080130340700158422411004182048480441031503070a603401c820301c24880c0070700c4410f44241a2000070300c032182d07460b00000e55502c1c0c5800e1070923032055407075440c6007103a11501c2c2200c014181ca60f8829100c2921031404 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 711682041 1250 711680791 711680807
    0xb060408010e06100e0105061e0d020406120b03060709031401020904110304060b0d4409130209030706080c07050d110f060c030601030b01030906020301030812180d270303 75
    0x520307413400211000140d80307030311100300d9041e00c01c007629040c1801480b5890116401c0040d2908140000600900000e541d1070701c003800082080c0e540b04941004078003494411996040c40407402038225608100c502a00b0025000883c2d80c460005090383c07081c95411402400b5800d1720380e0380b280c204102e8840b4001d000c405140210f000d007108016850300c1d50308200003484900401082034401d0f00000c2842e1000c1402e44644d003c83c003151483d4042074101010000700600714014003003101150046160402000d0b46230120f42c81d880031460000080000f035500e071601d228100400880310005088000c0500035204840d60040c21200d000c003903800c010b084c06640c002040c0c02807041d45200c0981240029405000d510710840a605e07540782c03103004401a040d01d604260515444100440c0012041e03c0212300840c05048030f16181c07009002d4608903410090420f041c049a40900024101030101c1c0749200d052450130607090042052101d00c0524000c9115101017142416001003459040411 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 711683291 1250 711682041 711682051
    0x40302130c120504050c0a06051c110d021c051603050f06091609030c0305032206050d02030a0612050c03190b130303021207050a091d0403030b060408010e06 69
    0x40c00800c900060a0340d0211402036540c8000142c1400003810345108030381c8590b4015000b00241d031510f17594880072900301452a4130070b000240b0006100700c055401d2251060b400350f07195909100c0325140d6a030406081c000d000524051990005e52030000007400035594041c1010301d1804d101910b02050340b610600b501360742c00404281404005a0b01d80d0369142468442c600045c00000b10340ca50340801c0c2e4004500d403000382d06019400c80040045500c0d40d20b204000c40c0300d00021503440c0c4d014064426513084038a4500068000281c051061139000010350302511030708080184c90703503901c141c580090100c982c00307200a140d09008070000c0c882d011070045500c2c2005c0d022108240c4080f80958400e18400380c2c0900500c00d0b00003c58110385100c50110b5101d8003910b4090b044c59980305001c014000191824004145e0000d21114540d03001042e1000511220b1410406240042d00145a4900c0103000904159079141440b90680c0c2e28400d41c5e002d85954002007002e83d0310703846140d541c4c0800b941c03 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 711684541 1250 711683291 711683299
    0x10201050f070507060506030106050627030606100809120703230306060f161e0b0106051206011121070308060d02010c0b04150c0503060108070e211908040302 70
    0x10000c0c00780810049054010381c03480e55003903d4030884e601c4150040038082d15240d8555224100012295a400b0182814004500a2200307070703202118000841107826603081c1c020b070410300030840d0326510300800c101040d10030b0030301460503a200c1a002e0301b8900703058481c0004241c0403070f05105240d0f001c00510304100c592038050040504540b014011070104507680382e44002c0401100001c0100d110140062078440c0f258014020015030b5843c10086204501d990442400e40c5184244040071740349074018141404c0051414000c8100426200c400610050611020885080954004000182d242207001d0a64001d0345001f8010400300d900542064000a1303100300440c20f0351415940080c00113905856191a161207aa240010050001c0090750100c400d480c1088800c1381901400101050782d627200f1750f4034580702001402c50f07080a064001000510f0540c000c2940324409a03094120307607240451004002c85150340c1c681b15904040c60000c14402a02d1020056540e000d0070680f48200c07 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 711685791 1250 711684541 711684551
    0xf011b120909150b0a030f0b0604350703030c08090a06020d030f15030f15020c0a060e0a0b0712060f24050c0307110a0b0a020604020a05040b0102120315030714010201 73
    0x4203120f10183c215010301040110200800452140254860103450109900200b80805034000207000e54105512413040503840f00404600e000c3c07842858000fa4a0080840c0d41d0380740e400249580d1204c044c0002018444940603031418481c00c5800d80307501008c002c00c41c40135203403600c4009407620180a0b48901203401c3c00d0401e4407489035801040c0c0010801040e40040f00d01e981c50361a00c4030389410040d80c0e0380120144428440007640020480c21030105d009248900d03d80c43e0a6048a01c0c030110b91078542c021050300d100142402c115690002001e00c0c112801c086030904480007450765510840c0d03683e0280c0b100041c1e04102d420245484802c03400c1c03100c1d071f07200c402c907080c0c4a91291001d9a00190810400c450019075030f0b11014034070751400b501c5004115100c500c003c0190740030b0200000540e0000c01004218900885041c0c050001071740c0c144240c0c0c2c69100040d40d2032602d401c4581c0703040300100014413000f180e13076090784002c000202240d4125a170f5035402600302c41c2d00003071980154248 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 711687041 1250 711685791 711685811
    0x1602010608030a021f150f05030c010c050c091510030605030d030603082203020a140411040f05010503190527030a270906060504080c0d020f011b120909 67
    0x300907030312010b60f80e401410038001803945250003006008002002c4d555601210b0209445045201000c0e2018280781c0214a040a04040c0780c1034a002802c4e0421130301c0c000c014001280400d00900098043d20725101daa220040c1c408052010702c12101c6d042a008102b100c10140e064010604032041581602c03d5030142c0c3c90118240d54003408090485401000283c40800003c841d4142c03042880c03203114040c0344c49600141c48118154002c3d0b5191340d107560509281e10b424810380c4c03051480303408401c2c9070900d0700f9592418480d00d40704e850305002005c40091595045070405805803148076404020714544044003a61842c10041851440c036001c0400f10110400041240c40301281a2a26001100034071082c07004564904c04003242c8802000700014948554041c900c090100782d22107a445c1c50a00800b546003441d0031014912414060000303001588402c001c000c4c4a8034203117000c230300380c0ca00c0b00c1c40a040101c458070000c1c500091042c00904007503104600710290b8151403000e201214003 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 711688291 1250 711687041 711687043
    0x60918050a0f0f060504060e010e21130504090303061d1018380f0a090207020604170d09120b01061d1f020d23130e1602010608 56
    0x1418004005a12140003040407801861032041001e1292a00d0202d00714141da0302130550301c0c252070448a03140c60300c448140512085c0074541340464680b00410402e0521048800b080b26000e002c0c0030072140000c2c8501503241400c40201c0500740103002071080721154a0014010510f42c429240120401c44070b840141005811407409400018400e524031414105160703400003002c5481c100311591a00c03400c20440d942d4001c0040751100c20114456030f60207440350461141c4a00d403040c0310701714607841000b580d0303254040b10059034212200141c44403664070208266104681005840ba11024103045e00000000340c4042c101c0200ea6500d02c1a6644074108021000f60550043c00c0009044c010320216200340c1004056003030000ba818126100a80840d050f0300c0305203455a80c055224400452840d01003249900300101460151046a080b100701039240312180789541d40f0090000300380040100b682d8400002e804a808000700704d0a1400511303050070174130346020005d542064000146048 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 711689541 1250 711688291 711688331
    0x80a110705071e0632070f0308073903020c03070902040311090f13020102030d0c05130806011212031b0305040b280b040e03070f0605090d090611120c010609 69
    0x41c03602c1c0031454104442c90102a04458061001e404082880710034007041f64590001003c82c004d444080d124208401c4c010400007907840510098801650007406441a800150001c0f82c14086c4c00e6210b004246022810a11003246a40d81882429408074500140340e0041080364810702e0324202c05821042400000c5e03004884000c5000388180004081a5a00111028035481481603903d4501d210308641c04817841c0c12880c6e000a03d0220703201030311440144c004805009442c2c000c050039803501c1d8480094048000380209500550440c030303181a0f0098008910180750725084049a11003440e00900402c802c81c0c0a0341c2e1165503c001c0703120381903031011503980b02d0b0b8080c00c00301d0305490350410040902031042e030741b6801943e507501c4804000c10074000f07008141c0c0309101c0402518544c0c1080703000c2d90000782141e030041d000068042d405940201c400c1044409501f40302d00000b0000e00c103641480031b0b2401506041c0c0c000940d5060007131040d404102510420001004100052448070220071 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 711690647 1106 711689541 711689567
    0xb0a05040e2d0601051c08030a0e0c041a120c0909010b0907080106090315140106030b0a0f030b270a05010207030e10080a110705071e06 60
    0x140444402c01c1500e4007808030100116008000588650f410321805200e201d4a18060280d906460034282065070480c81007500d900e0f044141c2c0300a010075160114450080486105051609200744801c60010035045a50440007509100c4a02401600030340644980121208555034414076680703e0607454001081c02c0b1009002d1001c41103019101e0414020318100501003541d10545400071650031442000407004801e0b205d4000340520030686c000c02160300004035100390540c0120030741083c20b0f0b13a40d201a640e280d0f4040907003062400700070b02e50500c00c00856128821000c8580030f0483c1c00e5004080301c0ca014408920f0042061012100399401007480418160011300160502c00e09940b03101502c00d03c0380004001c148000e102185840c4d0390402d590030034401d0000e0317a07149548082260401d82d29074800f41c2c940c00d500340c00c42001070942c0101140d69032007030021040c20 = true := by decide +kernel

theorem cover : BRFrame.Cov 711510791 711690647 := by
  have h0 := BRFrame.cov_init 711510791
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711510791 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711510791 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711510791 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711510791 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711510791 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711510791 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711510791 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711510791 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711510791 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711510791 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711510791 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711510791 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711510791 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711510791 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711510791 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711510791 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711510791 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711510791 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711510791 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711510791 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711510791 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711510791 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711510791 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711510791 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711510791 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711510791 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711510791 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711510791 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711510791 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711510791 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711510791 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711510791 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711510791 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711510791 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711510791 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711510791 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711510791 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711510791 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711510791 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711510791 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711510791 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711510791 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711510791 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711510791 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711510791 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711510791 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711510791 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711510791 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711510791 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711510791 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711510791 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711510791 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711510791 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711510791 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711510791 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711510791 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711510791 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711510791 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711510791 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711510791 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711510791 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711510791 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711510791 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711510791 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711510791 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711510791 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711510791 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711510791 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711510791 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711510791 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711510791 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711510791 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711510791 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711510791 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711510791 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711510791 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711510791 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711510791 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711510791 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711510791 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711510791 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711510791 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711510791 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711510791 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711510791 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711510791 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711510791 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711510791 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711510791 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711510791 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711510791 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711510791 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711510791 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711510791 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711510791 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711510791 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711510791 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711510791 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711510791 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711510791 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711510791 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711510791 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711510791 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711510791 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711510791 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711510791 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711510791 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711510791 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711510791 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711510791 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711510791 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711510791 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711510791 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711510791 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711510791 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711510791 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711510791 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711510791 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711510791 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711510791 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711510791 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711510791 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711510791 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711510791 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711510791 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711510791 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711510791 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711510791 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711510791 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711510791 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711510791 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711510791 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711510791 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711510791 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711510791 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711510791 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711510791 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711510791 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711510791 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711510791 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711510791 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711510791 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711510791 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711510791 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 711510791 ≤ n) (h2 : n < 711690647) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
