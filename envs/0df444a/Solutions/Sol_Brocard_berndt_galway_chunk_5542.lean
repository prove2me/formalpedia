-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5542
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T16:12:42.870237+00:00
-- url     : https://prove2.me/submissions/b48b9977-3560-4229-b316-fbe392b48f9f

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 996582733 ≤ n < 996762589 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 996583983 1250 996582733 996582739
    0x1b0703170a0e0606040608060f04020f3a030503060918010905070f06020f0d030c0e09010b090301060905090a08090d0c0b130f03080a110a060e0f24013011 68
    0x21513510320309480340c40c2c00c9590301c0000e40030782d654a84040590035001002640c2100444c0d85040456071001355140c1ca00081806483d844c00c03041e1507804161403545821000e40141c5841480400d8100082d0307035010301c0c2140c281d1115540c13299004100800c0302034140d802d40c200104131040103804201c84082d40d8901e904205c00030380d507440c00c99613160070030b03a029407541142c85411601031084d004401d04040b541000c8004000d91404246183c000340e02c5103841081c041803807065131400303009005c0181040c2c4410300c2141019202c50f601d85864500082c1a24000641c10340d0540721031404c0c1d400c2036003109018502c80d550700403443c002c2d80300c003880c4100340c42a001d02184c030003907104408003039941120142e400c1c0344948a055440040380c0201c48030901c0b0380401e21000400a00660140b0340303644001d00f580481e54292680b403c07812000038a42c000e80400032128000c80340c41e203035046403000079040e4101c0c00050040c60755020500500d5080140d201040340602200040c100380741a01a = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 996585233 1250 996583983 996583993
    0xf061b0d0c020f040b1f0504031b081e120714010504140f16091a1201020406090b160b040f080d02300711190b04030311031b0703170a0e 60
    0x400401c002c485144a1350b0381e0203003030b0548103000301b0f02c000240d181c80320759800e1031480d080e2291280c1c20211843d001c40f50058140e80c0042c04603240034094800e2000e04004001c4e610b25040a0080d15100c90560a5802c00800300d071079010b200c8c0401010866801c004001c02481c00c15040515482c2d808009458041c858044043c00701c0c00005401300c141d54002070411000d5050041d0710015014014080d54416091005000b1720340d100842142c040346034000059039685000f00203040403c0540c03060070800000e20145413040102003440c017416078000c81040c0f003a50f071860582c2ca40d070864480a00902c50118041000100b00d83c010a00100c08401070030711045001a0321140641c03000c0024070034910000800c0c9040e00850402041d04280e4069850910304290307640d200003064070b425101e01078644188014950544600101c0c00c00c1101014a1882c041d0003942101450f0226500c060360005800014184103106505501041c05810711650424410360b0018002da0b0311203241c14018 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 996586483 1250 996585233 996585259
    0x1022a100207060c14040608130f1e03030c320c03030c0c011a10030509211e0903030a0e06070b24040b1804080c010c0f09090b0f061b0d0c02 62
    0x176401c1aa800c0310103503580d0b5410b60396001c1e0f800210001d6810200c44000360f440345d042c0010000380144400c43e007000e000307411a0b400c0741402010346410310442c00902c8000c1d54170150b80c04084044000948481c0d030b480e54000030f41880610b5511610310011110702001c030620201404c503000520310045d60b40c0090083c40c90070f41494426554100355168403202c62081c0c10308860081c0c00030340d44900114280e500240e03a0f000d5071161745105c51480a260700b4002010108000741602141c421076094224030708000c000c8021aa4900c186501c030010b000d58140009000d903500d0303048811190b8004040029418840030110f030744011035222210001c00740f034040c1543d05040c4907694460400030300380700d94a500e2048444142c0701c081c1050b0ba08850400c000d102c0c110090288020a001c10781d1034040c00e8218000080c82160143c20070400c0354209907416040d5a0303025548100440f00719200d03a030b02c020141c400c9141038070b00348040d01d082c00343d291162080e64000b007003968801d00a4500d000038140b = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 996587733 1250 996586483 996586517
    0x6031e070602010e1b0d05280b0a0c081b1903020901020c03011e0c050705030307090329072109030302091c0b0c0c100e01061701022a100207060c 64
    0x1050311080005d20038512a140d1303091030400011020399020381c0949100c200f003c02030003001d21b10314069805101c000052134040054a07403986610210034501004185010407004048543c0035042c078862030b110080455042c5400411500000001c44501c5c065044604c00079010f900304103100d038094000c40e94081e40c2d03410180245006207204011240340c1c5035825042034000c01d0800755900c100182403007a0400144100010340c0640016140d91100c1e51440c03814030101200060340d65103c10b010002000c5481c0b103424a13030341083d902c0c117244d8507922081c1d41042d41c00c0d03035800f07800020f14200104c9505040d0543e00611000c8015111609145558860f4104a500300703074000300070043c0003001400c903da28102400640b65188180c4404414400c202d4081c1d521303181c0c4860301a50354003800c00040001710500c001859150000358103013030941d607011400c0700e98401d12000c24a001c0381c101d41003030014440e03014424a01c84d011525440103007444401460141540300c0400d198441e032041d042 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 996588983 1250 996587733 996587743
    0x90806130201140d090807020307060512191e0501080d0302070c150306030206180405011502030901080601020c04090515060612010311130e010b150313020906031e070602010e 77
    0x2401016444114080303907004444110388030b81e4400d2803070003d110440f2040c6290044c500381e2402651510b0303d50156004241c00c282403540541c0c284042000a07040055040032541d50201a420745280d0212254a0001c060032005150130b6040010050306040c4081c0741e40001e060312290001c42d8003031008850b0540c101d01c2040320141042607144810440c110030f00c004048200180e03e80401c040b6a2507010030b000350031107c20b2226007081c1d12034250141c10719200310b90050207280080d09210010304400307901c2c0e00c1030801860401401c1c41c00207096034000c0000f51851807020b0400c02581d51581845138a48103003a8078000c20a0f41100445c0640c1350900a8542e140c00740d91f62441d1303a9281d640e0f0610100c14010442e60480f41049078030516a45512880002d040000c0001c0390010328441040310101e1003c518044490041c01440303402c0b0500903124050603030603640e240c076036140c6070700080c038040030045040c44490200a600c0700034032010500f2030480d070807500240005940242070a07110 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 996590233 1250 996588983 996588991
    0xc0a030b071e091211060c10140601080a0f1409071d07050f03090f01090f030807030528021303051c0302071e1401052403060c031609080a050706090806 67
    0xa111070b00a001261134000351900c061310901c49141d010807442c01040076904440308070404c42d00a90f0341035a4191150084c00480120b5280c132550342d181c40b000203440b072a0082c10035000c40d60f6583e861a5000c195034080846a00701103250301680c641410740325a52106400385007081c0180c40240c800d80c01c1030044c0d040c001c110b10341b00c841c1480c103162071120031508024401caa0f184181d5403080c50518080c8125104035000304804c0d0911411800c014180200c0500311000b01898081000482c0c2e81c052002a03175880080b4560140b01e02c1d000b0801c1c0079002320412180080031501002040010010381d05201e0008990320240d20700c15500160b040b8010200081d155109440c00818040c00071141006c00e14420030340703220b010305c6601f805403c46104507112000700d61070583c4007080100322101810200c0d0f08138000d04041c130700408100b09901000d03111242280e8a040d070450080e000b0315881000e4040607040b5484004241400b41d07803142c1034031070900881c5951a01003401d030340c042409489 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 996591483 1250 996590233 996590237
    0x70b0a1a27070c080a020304060905061e0a050909010902030f071b021c061d0106050a0308040b0901270e06010306060c110406150801080c060a200c0a030b071e 70
    0x90707000d6607212100844000c106804202c0020686400030b404100900b02140c2e071907006549840c00c0082c040c1c513840954020602c1004c0c2884a000780d180395002143c810003141804a8442280c42401c0c3c50030300410a103164404909000400d440044d580607610a90300c8a008400c3c98541047c103481262400e802c0000c0c100c0001e0b80c00015040c10454003003500b03035010740d801c034038250354442d04101c2d10b10b0b9000c000a070302d180442d50300303800b030034081ca0020345021210b600c106461a0b466444a03c180e21030140c90344404500000180e0240004109001c80c2c454400640170440041900e038801c94000e140d110850712010a960354440d105140c2a6440b40e255101060f0b0145c96814181c40c207600182d41c0207440e034102150500d061004070040122030303100c0c0ea00d0383d4105940c0740d0030980e182c00d074180103030024048114115400340c1c640c1d484540c11003008808a10700c17200f403402c0080c03140301c3c150040201d000000401c030311220703018032a40319070750364150301c3e80c1c1c042034100107140da8070740b40740 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 996592733 1250 996591483 996591529
    0x7050d02090a1e0504030807110303130b06030106051906021605150705010e0709150803070308130c0e0f06240f0903011401080d020d080108060a09030203070b0a1a 72
    0x40000080d07480742840c24034065481c1d140c0c81e03400340d4903000e0759401c1710101c0003c3c02040034426a560080c51003d6003244c40030245003146003c8080a803001c0403503002410104030940401c92a0301d0a40c0f012010b0100942840e81c00070741001c040050700c13140e1040d40018850001804141d2040c10400010744600402248000c5140101ca80d542d0f0000d07403098905561301c4048180c0b01c0c0302003044000400e6104000b190382d15010748202c0010b49558040a510b4004101c5400000e500031011a4814440c0150388509145424444694540c9820a00001c51001e080c40302a80b00d1510040c85014103d9412035006120700001d0141e51804130207030840802405603003800d50440d03019042500c4080c0000451000d03020300e0000008007a0302c5030003590010842e0b41126070381841000c280202c07500f0244159454032a0040d6942d900524848200da510b40d4904200351013402100c0d04190404005251400c3c445154001400950074000048040e1002c0101c0e07402d01020590b0607252410705e4007 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 996593983 1250 996592733 996592741
    0x150b04260d0804061d061012051c111b04050114010e04051306060e07031b020606090c19080703060807180b06040b0340060f061a0c07050d0209 63
    0x280d503441c2c2c00b41084401903200c40344e407691205070400000303000e15980c00400e0070f420524404444280b0b0b80e000400080d00120000d00882e030006080e09030102079031200031002108034401c946246018402844600910000040020300c0310440c8103481c0089400b041180d90710f03031100d510a42d6880c0c0c90703400b24003c15007051003442c103980419031115401d15552a20f0344a03030b460300102d8060703400c14a11042e4003000c1c0007074a545407040b80104030388445a640810980c54019644190003020240300316405c0340000d00508803801964486158600c80c82c02246001001602d00901202c000000914020b00001c2e40040041d8200407254100c150b42d03100942c0104210227482e035002c43c81c0d0821010840060150712940c000d61042036180c040310a443c20741c0650014104614640c00e0000c24201c0c10101d10300800c0003100c50b845e9001c1c20000d404038600442c81c3c05451542c2c41080c00c6401e8199200c1002d10400041c80046011800e0362400e503102c0c1c4c1004a4047d80c000081d4000307010100003 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 996595233 1250 996593983 996593987
    0xf07110a140c060a0201020309070905010b070b0a11070501050402121204230d03090314060709090509070f26010c090537080f0703031e03150b04260d 66
    0x20560111004191110100b090011074040c0c0e00204202005030b60020070880007000030b11017000505011304080c4840c0d40745c00c1142e032080c05031070301c0034041d5040c3d9004500051810f500c4005051203a510440c5c40740c5140c28034038000c100441b000e0340550220b00b490701e0000c6001c101507a05a0307240c0d0201d814181050040e410b217103010320b4000b00c00c1344a0100600305964200602d03901600c29a034503400c0d20308614001c0b1040c80500ca01d17200f583d0020090084154003c49903805803141190000340941e10505030500d8103004da0300100351800031500210301084070700d50f41105444c144c00d4a0611107080740c810381c203d4940040003400039200703400c14070561900841707604920b031003640306101e141003601e0024403001a410300c102002d0307404042000307090010b001181c481d82070740024202291468501404041141e405a00500034181d050704845001c0e5100c20170300b5408500242003030751560113a216550290140400310011401940d0b43ea596002c87d105044c2c2e20000505001e9210a1381 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 996596483 1250 996595233 996595253
    0x21c030207170c090a020a1101020a020714040f0e06150f0a030b06030a0602041e050906030601030305031e1608090f03040302241602040b0a12140c060f030f07110a 72
    0x6040b03454040c4602d40241d660300c01c00320501819a011005030303078a6035400c002d003203240d04014411050340140504a60180c000c90325004840c0308070306035050a07100c03200140086c210512031000c910301e04010160010000101e69103c0d1a4090f98070001200a804218420b01d601c400a541304404460600c001180e024855410001c0078007250700c0070181d56904000e81e005904891400c49804403d80001c041030300001d0010081501c0061040c00d0000201c0d845030014000239003807143c0000031806060042e405210000c41003190846503090005080900104214802000a504801044030100c020406006504c00c0740011860586943d0a200030295000e181c80400820042ca114410f66031100408540c8840010764850a0fa00d204120071100e00c92500e0307001d150b02510601403004003103210700720150801c8290282d00d601d040f0440c602030505d550903400c000042000051244804042c5000340e1000305404002e44e603042d030881e0001c3c80c1200c1d04846074481e91809004c502c115803 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 996597733 1250 996596483 996596519
    0x1305030403060b060f121906080303060415080111030a11042d03020405131703010807120804080a242c0c1f031404020105070228090504021c030207 65
    0x1007818140000e1800d452080d401c001080d1446c0d1b02d0003010840340c1c50400c200e509001d01d8000c0d040051a05200d00e05d9540d0000a007000e003c0c41d0b480000e28020041c4500080003040440c00030710420b00700102c5060160000d9481142141c14807030a441e1652230b5509490990781c0440300655110041d6521290340d178801040c0004484485001001580f15400340911035901d114001da000c0702d551070b00c252503561800085c080c0740c01c14070052040300c2c0c011403d0011030f40352100705003545503641010403151140f50b000200d5481510700004c100942c4130300d00001d18264800480c50003481c0e40240c1c0070346e103403c4000032814044c0440600c074020070703001e1901c1c5040c01e10b04581d00c0700c16520108000754064602c1c00d200c10348624140304110b9041c080ca281c510581007030300c113890501c0c0e07002070854083c22b80c001b4400e0a0900c1154004502c086d0021b501040310090110050f6985460100401c0140c5050303019000d421444030000a0a0545035041941a801440c18500d000394580703091802003 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 996598983 1250 996597733 996597739
    0x8090a021f050d020f0414030a12050f120901050105031501030804050618130515301006060f110d140d0605040f0e16080a0305090a0801020a020609061305030403060b 73
    0x2c45003410708a0184054017601d0707060784203240c0d600d00705004541c8000c031000a0364030a9000c2c446100c0050309075040f0000044207030070196214900c40601c4541070140038081d400140440c01080000302c01500814121136040e029111070380d20307040c00d10701200d1007400054440c2100300002c200a040c96030090104000c08085001e03038901010018a944401c04402003149844409000c403e00c40781c032003091070311030032200040d40c0521542d4800004d050110700c510000200d2090181642003441802403004602c00b04220b01a00d412000c0c0800000700020740000d200d001d142c88070540700190200346018140c40b4043ca0001d028a0196240c1c0003c84a1034500d844031000100c42d101c0740940076400101a0020512488060f0100d1a1110100e01031151841c41103013008200ca0110306c0403001c6070180740c659034510b046004280b00320002d5000c0c200b2507200050b242c0b0480d9000c10010f020b60040001c0d104203446a400c0502c0f860800c1c031b809440ad0300100b0040000074400c0d48040740410003e = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 996600233 1250 996598983 996598987
    0x60904020103290f041e020903030408070605070b070801061b06022a0c06160b040f02090103030f03050c03010b0a2729130905070c02040203150108090a021f05 70
    0x640d00344220f0b025808000c0c034140e2034000c0c0c200d07003481e0076082c12043e02d0080d581000340d4442c051060141154080281c0c0002e5800103401481e070300e09004079405442c3d01c504503084ca590b80d060051003580a90010f8454851070320224070710300c1c0725001c000d040f9210b50741c4142e03000424480d91b0b040b1025200e03044035215801c0000261013516498680e4001c45410f0b4a481903e04516440b82041c40c2c580d8442e03c1040c0400080030011002000044c00982000068940c0e5031580791189004c030b4207000c0a90b20030510301c000020150f008800c18040d20050781c00344496125600c03d5103081c0800e0180d1140b034207050080e182c9151180007440190071100d18040610401042c405280102c590051090910728441200307190700c00e840311450305020b0000f05440c0c201000310305807840f00ca600880781419220310208400c075206403030071030642c1e80042c1708541d6818015000341c005081002c025001c940410000350407900c02164200c403258015000d0035841c40c4d0304061094508052603200144201 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 996601483 1250 996600233 996600251
    0x4080a0c120504060908060f0708040807061d0d03050c0301090c09050d1208090601450507030e160308031f0b071a0610030507021203040f030f0203070b060904020103 73
    0x41c1c600640c80118544481d80d80d41c0c14000c0052007032555030095406c640c00342c0c2c18814021261905c655014145203803420740c0b5161440d01110601c940000176220a00303003000f100c140d4603501c881180ca920034001301e4024004d920720940c02d45200311f442d00710740c3c80144010400890a50050f03980b004ea28940701180c59140c07400120030340341441081d02d48100b80d402c0040141d0308540b105401154040080c4440d61604244a403031012089020481510400d080940c94080c08600024030380e07810f0201d03956074017440c000307402420215032060001c5c1c1028588140301401080c510140c2d403501c1c005004c040d003035486a13001075001404010906500c1e50001b01c9100c81e2000e404050318452001940e22000c5003840201c21128045d14582c0703c07030b0305007404903907074640325416000561801d010806903030302d10003039040c4070b01d107a00a94220030000c200310400c1160204800100d10a4170707034100c03844020600302d03543d00030100c3c0182402540c0c03000c140185003103100ca40e44039105145c0070400d00303c = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 996602733 1250 996601483 996601493
    0x8160e09150c04080114090c01140408060f06030606010e1302090d0807030f020111090d02041109060c0303100603020a0c32010519020a0e190e01030c090c020106060804080a0c 77
    0x70301281c03410000b0002040c1440284020300610f807000c00c2e81d80000c0e40c682441c00c50340e9100c038148544141440b02c0c3c8002030700c13840c4200023138500508164055400d21b11340000e10281e8401e0444000d8401e00403540041e07619801409582524040907014508090304040d052000750300203505d555000e20a04003500000b40100006c20f0620301c00c1d41d600040044003080a82591440756404d0b507d00c4080c004c003002501c81c0194410348640440d40070039080c04500101280b07100ea2084075420180c005080b00c031406000004601882030540541c615564902046040380504954100011303600700000000c03540c0c40d0340080000c1954540c8400f00790900190040b0201c03154820921070351500c080051001c02d8100c40000f90540903001c1d440c010303003010004c0680840c25503180c8239025201658104000f00f419030300107041003011942e410b58481c00c016055400e20f00c5954401c60800100031b0401d40f041c0a400100e502549036203515031100d60700c10a050304910454800c0040580035071000c50b07 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 996603983 1250 996602733 996602773
    0xf0c0705030d0c03080a05040305070219230a0f0e16170a0501031a190f2306100903050307020f031c09060f2d02030403080a0f030608160e09 62
    0x60880d1120003c814080c90050681d200050210050a1802c010040800c0d084002c0741c1040341d0444a050044402c4451442609c030581c0040024030141d1010420f002e607070085080ca00d003000c07552119140c0d50350b0542070500c0a00d00510780031088402c04a0526403c54080805000c8541030142405900441091380d10341e007100d0100e0026140d0004006105d540d5240381150402c0d85071100480ca400000d08659004a41503130b0701881da5130000041c41c86595108080701200c0d0780c10480c0701311120504a00245059580301c3c4142940389004076090f001d02107941c01c50340d014000c2d50400c4030640030000480c0c41c0b2942d10360103008401d11100741800741c19452207001c195489a600d22802c4c140f0091140718072001c11003d100c528031010851500c04500b002c40000c062103a441c407503488080803419401a60b1000300804004a15100704541060000e49442010303501004119035840340c00c0e17130b903c60070f00c00d0903800040c4103400c1c003002a4101c0c01a9011450400b11421040050080291a = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 996605233 1250 996603983 996604003
    0x100209030a0f060b040501090b150a1103070605041b2403060506130f05060903030315011407050102091017070f0e03030412050c0a1a0a180602011b050f0f0c070503 72
    0x3642c0e13100003035041468070b0711400e805482038000c1080250100790109054103054282d800c1d200d540801c40d21300316485114000305070709803503090f42c0e01e408031391a185002e014140c03400c5a50011000c1c00d403107482c110034008800c13205040000042d00410705050100841c0c69801c0404040d04c1e0980424140c803004020242c144a0504000c00d140c98017445c6c9049080380e40003075101da6020015840190340010580c0d80141c006900002d02d440f0403001611003c00c0360900b2856078001050030828020194081c040c0c5550540f01d50800203807a41d0111030a1213036900e1042542d2000b404640410301c50300c0349402001d69414140715410252001a00e141c03c82c1c2d00c802c00b40d030282814042004004d01c4040d400900c25194003005504085000c10595030b442e5400001c40d101051a120b000c0c452150300003901298290800f40036243c0c940280602420b0a80c599a20920101011000e110f141110f0190f0030400c5080d041400000700b00b004e0390320240c3c04141c00e01c100d000c0850507680520500b145 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 996606483 1250 996605233 996605243
    0x19050c2b1823090c0a0e1309171e04030c09150b1801091d060d050a1e03020610030b160519170108070e0c07030c051f140603100209030a0f 61
    0x144891034401c0003c2040000d200b03c49100b0305004041640d608000d51042801c411034048440401c0405107034000d100c241c0d409080c0ca00701c0004c0089510946000304952038840000d00c000303000309000007080e407080d03110003000c6010041080001040c20b921812041000844200c107031940d5030f86041e065040078080f42d20701e24840101d44810368100e80d405004162420950005002c5400d80c08400741e00103082c00c2c02482c80621100c01c1040c2404403034400c540c807800e03550024603029011500e0810110045000d0301c213400c00f1605c0c0f440510380020480381e003d00c4605542c0d682c20b40c80d48510000c2003a0000740b00c821322080007078180b1400d000041d048140c0c2d5841e40517543d404214080030042e0310000e015008181c0620607000c18614030f59001610b49003160341c4070300d80d14040350455130380c00340070780180a0a00d28402e68100c10040104200d029038003881400c092006000d502c24065034483e6241c1c1c483c113507611501c1c955802500300100d000301511201d507816140c00301745000100b000c80d5 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 996607733 1250 996606483 996606539
    0x90d02122206030e0c150a210204030b060427020114070203100c0e06070b0c0a0c060509011d01140f0a1b0f09091b0c02040219050c2b18 60
    0x44130250400856814400131129416514000b501c0010280710340100b590402c6107170300468a4000541d03202201604803504110750702c030b56a043c80306500c02d0640c2d00c0ca10a0781480c1c112848021004603068400400348450f61100c1042d0340107480390b039428109642542e105104810150350300b0311005841a404000c049010445160010600c20380500c101d032144030f051050201041e03000b591664440000d85100f80e54a0000b007094900001d042c40040405060104114004006401070105201c800d41148000e8401d5020f9500380c82d10083e035030f001c0c5880000028400c001001c40c0360f4001903040700c00a0003a500e00c240a0000740c601c4000404200d89001c04007a0a0380401008020302d00300f2001c00048054903d04000701c903908a6103002c10449400c0d078800e41d0754640c1191010710340703140120750f05400b140c0041c0483e004152030038441c0c021649240000080c003081c80d40d40b0380c804a07114030b030648a0036094031114000d44013522075011940e00440c1c1c0040341300400000400d0000542 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 996608983 1250 996607733 996607751
    0x30603202d0f060301080a0303020f040f1212031e0b150a110d030c09050d1a130c090b01020c190801140910060501050f0d0e01050717090d0212220603 66
    0x45002d018401038018a4100010000c0940c007140c0707020a83d80c107280260340e41c960140c00c181a8012600005041420341400207911040c0b10070315030b24148030302051414502000c20940449201710500900d000c0c172800d0b41e000040403603100310b000f14002881042450200c0d481c124498000000303210104410080754811100108502d07000590b540c50240301034045454010700c051f003148035550007001c00548400821045c02c0c02049900341c101038900040c0f0300081290340a05000d04240c503910502140456089154000c01c0480041a001009880700c2402404103808a05064282902d80d0b1900030460420a003c0c403400b40800320034481041c00d020075074900f00340c03100c1b800c010041c1c5082e104000350798110054401c031603c600b0a40303844243e00034000014015041d40c03880b00e07528000410005a0f0000d12070700c43d42040c0200c0c61138580c0e076000700741d60740c110078079400d00503134001c14a5085501540d0f00401540910200e22200361944500d011303000b507450740042011176100c13a092 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 996610233 1250 996608983 996608989
    0x5010e070816061d03060709060906021507051c0903030f05060613050f0301020d05010b03090d08101406070609150506041e2a0c1101030603202d 64
    0x4100940360702800781c11035001041d4205010002c42c402c0406000d201140726048100c045150a1038036030240551b01c552520750002000342e901400f801011071201d42c808550383d440005d4460300510490f0240d4140e4490410a94064110843e41c040c0d920880381c5441c4125054000d072080d02c0d10030784000c80d00b80c0c00300d9140401e0f9070300249418041c1a06024024400c0711400c56202120010f40354070880740b8904022034007a228544001484c103051100024298a2020056101d00c101501b903c803907083c410780449a00301b044d81c0c04030500c410444103102c1800d220f151007143c10b00080600d89000707140c0d17441d807040ea1101039007500c60407820346200000c070155001e8182d01c000700310707130411202c14882039285400c1c1c41480707001000da9172001440b40c840054901c0f400000450344250540300d03019840189040200e800858845484800343c01303007940603004030001d0f03980c0b0000242c00c400c60380010320764000203462459880080d58a0702d02440c04a07403080f1032084000c0e01e101411000881c14 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 996611483 1250 996610233 996610243
    0x314010515070b04140307031805010201050108030307050c0a060c020d030b0427020d0b010312091508041203111b0708030f070b1e0f0a1a1c06060e0405010e 69
    0x3540c01080650741c03410300300c090802201c9030701e80d10142aa10986440c00d00441c0c40403c0183c10081d0b100008061090540104003a0040840440c51106440d02c0e403004a00f40c42c02032007504001d600510229510a0169001c1d1003029410011110002c027140c582d581683c2860703800d400580c0021680c12240ca070706001d0b9010024003910309021003210060014800300d104641a60307200060b071640021590b824000c40d41c1582c01c4032001c1c202d5610b90500151a00c501340c94080890981d141c0040e9140c804132080079001c0d20740e19204040c1e42e0325103956040c41c000a081170201550395610a482002c00c50140c0b400f2403480304d0f2102000c60706a001450050395400c08140d0751b10a100740c1e881a0016400c5605442c1c0c000301c00c1c5440d4413041c00400d1209401c0701d4851804107100c0c1004038140780c00c0c0d0301d01d1090325001002e1084400080202d5210100c4442c416001aa1500c29039040c0d034181360b4400349144201d40c001603007680c03400c620401d4481942e044400c2c0c4d450365104840b500c402c02c1 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 996612733 1250 996611483 996611489
    0x1b190602041502010e2d01060f1e03050d121d0318040e0601061103040801050c07030909140a020c100e240c040e0606070210202418030703031401 64
    0x80001c24122a035a41d96039032900c61825501c007500d400c03640303030300e541b6180300c020036013072030000d0001a441d40001d1804980c0d42c002c03440c11355038000018404a02c4a410442200d80040103002c05801708403040f0f425000316528240385c40c5e00c95808070840e003007161200780d2040113200030b140c8031072450b0781181000b407605500e948039070309111000050003004a0300b0b0781158018104004c41c80f80d0f030302c28242140183d9011825551a000030808203403560740003454080c2c071940d80c0094460300e0f100000304450305106c8440c00c0e0203002000a84400c410750044c51800c60440403212600300306001d100588a40c2807001806030032007884600d002e88103151041c858218080c00400c28070301024499410301613482660310390380c1c4403c0462019208d0394101c414040d0050300c910385120710a0320142070b10808039082801d2944c0a0300028018801203030b12100700103801c2c0310b028000c0080d021900c5420024250a20828005a69050070002080100620341c440d48022480005d1a020b509050005034 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 996613983 1250 996612733 996612737
    0x100e0402061612020d11070902090f0303030c040608060604060203070b0c0421050f1504060902042306030601051c230304030b071404120323160c12081b1906020415 72
    0x1b0100103680c800070554405580740e160b4016240c190301c40001c0c802400c3e1300c07410750701400008103100300c6250b100d008006a8038030780c031208441d440310030900074640b18a1046100682003800241c000407800c52800d500700480003200da00b043c0d250500c4620350700b03007070024045442c14000c0050402c40180800384110801d600984040202c80c54040f1001c003000708018446607581449504564566109602146017054021141103490b603107210385100c140c80140c4244600700000400385420b00c000201200300b120710f1141c004480d580d0300c82e4110007800560301070055052a0802c02c40800203040114000c0003005001c1c10f14080240441d40840d07008800100200824003940304216002c01500e90700d4900107900b030b10602100341500d0101210400d00c41d42c002a00c0c40745100c889140114a80201042c410159443e000c04120066a06004041c10801c1c0408a0003804130103002a500d899001901d400150b51240e4031402044108115411980481d0520030807901521354907803916030f4 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 996615233 1250 996613983 996613997
    0x1513031b0620071205071505070311060402060d0f090206030a0203180105070f0f051204080408070b03061e0102030705010e010603060506030a051c0e060c0d0e09100e0402061612020d 80
    0x100c10b01d0ba12140e00380503c120f0041c0720140c010130490100920002001080729840e00b81440400c02001e03a40305070303030583c001034030642942c403010004501207000d664020005803402c12151100c2e405450f40070b800c0e01003e641c0c0c0941c040540c940200461155190342c0005070f0300c0c0703008000e50101c40d00c919030b410380c10b80c5420100b15a146e080156110480c040381000c2110b4035101504840c1ca1090078224003181d2403003418001041403480242003a1080300e4152034100703803240c0902c2a98081201c070142e2203000d142410b0503640015440844c00601881501e240403025152070b803d4980b6a4a40c01042e03540b8441001840b070581b08890f00808110050100107219854150740c82844842c90f20014209606244801d8043c403040e212581010309000d4448019041d11303501e502c000000d010200300e180b0790603400c501e0715203441c0d03100300360005c85400d10600b0400c460700e07040c200600403600800108060b01e0010b1030034204583c0c0900c01d2001ca14081100c0d00b009007400011803400c4144104 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 996616483 1250 996615233 996615287
    0x9050c12010902070f06090b04030906030c051806090307030f05060a140f061909140714040e190513030207060305060109170a080a2c1513031b06 64
    0x40c00c140ea04480e840c90b0090385456260902c0b03042c2c00021500141058075024030513041103a4030710a42c0c443c82c042d49900e02d0640d40d40200340c0589100f142100002882000300740d0110401410059a01d03c010701400c0c00c0c0410407010901d4548990030030344030084050200d0080003400c00445a02049500042c06050740407515072030a00d801520281c541078100c0002012074442e00170903821403c01a0503007600955441100004180c42040001c1540340080000e10150140343c90001402281e81c0b80c2c0d10703080c5050780c10700e0260f2000c0e0510803145030807003074011222001c2c0510303401403508a200c7c0341104420716020346000d03c658011410300d400e0108001c0e9aa030480c0c01e1004940170405861000024910702070b003072180c0c1100041060f000499880581c581c4215007014451040c2416070a5810102034684202103455415501001042d0202146e640c40710141401e00410320b0190440d0b602ca40c0e50310b0640010b00d000c020740f2400c40b0800c001c45588003241d4460450582c40f4840e480c04 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 996617733 1250 996616483 996616507
    0x20906090108064b0604030b0a0f290a0609090b04021204060b0a06050705030301060302180a06030b041512032f07031103062503020d090c09050c 64
    0x1160040c60500c4000c2c40010340c25100c28440c0320b808110f103c0b0b080040b9400c0c0c1081105101d121090765013201c0c4100e440300c1c14500180030f150140f034004142030708040c40d5507900d200d0300c98020031b10550951940f0000d402d40030a80a6080c0240000c10340001500400d6022403c40d50381130341003440707039940c0d8008100041e0030031850026500385800100d070010701880401d010384500064060b4404803a0100000c0c4078541d40113801d120021078094000c955500412105c07801117040142458000f00f004211050003940200070b09511160200291441000001c002009940c8070a001c20b407a00806103840c40c151003081e003c40107104041c003229080210241c074a240065000302404458440319440b101c080301c04e01e2804803031000c4407610f0a000d0f503180c0c1d283c0303178035110454170008058525030440c9008201a8030821121b000701c1d80c4910342180c0702c0c9180250003048814581c0c00c019040c01070016004070001507001e0780c11140401d141c49417010440f03a00800d1480045002c0c450081520 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 996618983 1250 996617733 996617737
    0xf0604051e041104061206140c0307080f061f02060a1107030e13020f1c0f0509060f041502220b04050d0620040305010b01120506010c02011817100f020906 68
    0x1a0003203c250b801010640224004100e05e410004e50014402c1781c81c810404280c00c068110918440511302a03102c07100249554081940d0800201d801c01000a0300201e00030351496101d5401401d01100c0480c00080c0d80312527280c0415040141c1000c0d0070022400d41078041d4098250508054074584aa07a460040c180143c03d00e85601c44c03068200d0611191005030103943d00b0301076005040b940d400144201c24015010f007079403420b0041c01d102c03640781107818610840b40b20f00740d10317005040141e4400f0300724000d94400810840d0380552500312021040c4846c4054410b084600358250709011103074054181e20070b07495004645001c002c120038003840d04c407803280403000d952104010441c5805024480b8003808015007071480c00d000401c3c008103103c1e0541000b2201c0c1d0080c0c0325511400c0e0804000b00556001312100390110700c42d225824015403040000a55200a04203000007050b140c0c1110054820545201c00050b8401d00359242c800f00c4038490007030b4280142c801145805840004140710f4 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 996620233 1250 996618983 996618991
    0x307180602101a031c090504050c030103020f040e100c020c060301080d080c1e041e050307060c061e060515130603050c0c1c090f1202040c0909050f0604051e 69
    0x1160729028603c01d41e00521022510481c1c0003000e660030650204180091040024041c3c400070312a4040040d240c1014441c440c00340d1a0003c80740d2640c0e00b50380034803c03411031001d60070b5045903030f4030403001c9120824003250506400e50030000c02c0358001c0d808000d280a41c52983e29125050400040081490005030528002c105041400c003541d5000343c07a09407801448405c075181241000000b40d20f21440c0d0041050f91108075892044040c5019900b901d02041d006554055019000038000e0303500801c07203241e006105a001041a2241e100c0650584036070004895006032514410300c40d620b00040e084440d0707544c3c002c11f9800d240008055618070801d43c40b0346024140e131140401d400123180c3c012140c4964643e41214803040c1114100040040345101c05c1000515a14022901c140160040e508840407660100792025068080100500701003103aa4280802c03000d00140101090141501c69441401c0c4801d0a141100c140b0041d00d00041039994420303403210034008011901c100583d00 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 996621483 1250 996620233 996620263
    0x10b1c0e0c1c1502040929010311160c0609060206040f230d090e06040606050316200a02040b01030504050613080f0d06031b1d0408040f0b0307180602 66
    0x20355121100c9030829909042c2c40903181d00d10124901603100701c00d40080c812a20710005c00c0000e4108070140078a40b19040d520040c42a800e01d91504843d8883d40103030082154003110715180c504500c443c440c522250000803114440d10300340800546411051020061000d0300140c0307400e1610703554102ca540580800207100e48031806419510390070b100c00e4001a40c01900c121801c2d11001c0801401c05841842012128a080360004101d81000e00a141c100c070290b0302c441d402c548034031550503001000c15203500100b00607140702018580d080300c1d400685500440140c0f03440f00c80c030300500007541c2ca0100500d0606003842e060200044002625960000411514904e00070003481e003918244940c2540012122000c100c860b45940e803640300340300b100d2240700d000d9115023921a08a01c01074240c171a281d00c0000c0060801d503040303c58400198014429140c0c5440c03d615080b50070000c201540040e0402c540100402c42040e8000c078803201c003031810f40744429180b803a180d40255655540c02420394 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 996622733 1250 996621483 996621499
    0x1b04030b100506030a02120105010e0109030809061317060a09020a0b0c10061d06030f12070309180b13050c040b13030b040f03080a0209010e0d0203030c06010b1c0e0c 73
    0x1e2550700361440e000a0800284450340e41d09180c01084085e410a005048401d440d55000040755801010040d22040048e11120281883c40c0c4618049402a21042e600b01030108212540c0000541c0000007520b050702000200d1150900054a080070050140b0402490441d000300581d980b54522800c0361000d4510a5581c040800d4003800e10050400d560b04981c24808042001000c40c0d040140c1501d0342105440503507121020166a44500184030440f0707001200c40600d00c0b0106002401c2c0c03c0d00904080300d8880d43c5010403c43c000c5040c0c401200c0c940e56440a0305945021b01c2c6a681030b00720301c00180054140413204441078440e0740301e0102841030001d405442c50074228801d000560700f100200d0702d107181a007400908120240e1040f00062980000508c0100140c401c3e268040c9040c2d41d0602d8240d202014002030b24815401640e140c03100388542c020000040000c0342c003030f040002d809521100c0210f0750903203911060307511108803410710b001255001000203004400c00800c40300b02d0 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 996623983 1250 996622733 996622741
    0x20315060906132c0402090708130c03060b1c031d0f030718140f010303050a0507051006030201030e0304180506060405210606011b170409060305151b04030b 69
    0x20342d0380c40b03031901801c1c41511150000412050407828000d0246207034507200c00c40c001d04a01c04203d030b001190025480f020020204401c1880359407800d520161203040e03c0405945920b4040d070100040e0b101b2a0616228840e0f00580c0c104070170710440005280038030740180e0300b050364003422880480811841440e40e81c00e0b1a0103036542c038840600c120b075000e416154035944030040203034000071b500a00782d1320504041e0b4650443c5d4290901070302ca111185054095642103079402c44040c0d00c03040c0d240081000510007400424010303c00c0800204072044c000031240e10358800941507650661814180d60810302040200d006280b40311000842603100004056549000084240c0100d400207504031202284403502d413050340d6103114003009400e00b00d8509540e4000110742c018417035074510180881a03a0000009404103410b01c55024a056105040c41d485944245c00c40d0030301c0c1c0c42900c195204403010748289503000f1071690418119843c0d000c0d800504817405c2c060380310718072006214500da20001 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 996625233 1250 996623983 996623989
    0xb121501051303150b06130b0705030d020a0206070e03010501081b0a090c02030310080a0f0609020f09190501090c051909030b010f05130e0d030914060c1c0203150609 73
    0x120001682da5005010301622803d001e0250100c4085248085283c191050424545101950301d802c140701041c8000314281481070b001a04440c000708c030607110034805928282c003e0b002400c008801c0780e004114500c0d01610040108298a1421380280d2410f0014086443c0c040347e2000000f2810859400094040001c00c10f800140c5d808050802d15282c12404802d41c080700443c0692141050103140a07100c0e0308864031069560300041a0243c00480f000006080341c000c140d582d8001020b9101956109010500050044a60301c2c1c007405c0704900c2c40407012240c4500c5000d8203a8bd9801c100c139100c400340140c09446620f070107245583e1311401d06c000e2075100307846810103036600004110455a4903003114000460b0303800f40c03e20801e0411500d40074940544500805210400010880e01c4420101500104800901030300c1c5c03542002c105100c62a8104001e0b80039a00c980c21180e9a202c500f41600900700c0f036942d0b2488003030300420034804162032007010340d580d1400403203403a0341d204808400 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 996626483 1250 996625233 996625237
    0x40f0e0d0e060f070b012c060f040b030a05030c010c0c110f0d06020f0318010203091203090705090c0c010b01092925050c0105040351060b12150105 65
    0x403c24000c02d00207012420440301212041c125003c61404010070000c1d8010100712032001da01c860008201c20340081d5061070804815004004080e0000404c0311000f0042820240b40c0740c000d64403540700103902251102e007449148101c03441032414446100c896074401c0001194160b401d0700c108010554a200342c0d852149500c94540e22400440d03598009844900c1150411624001c03403ca9520345076003030315410b0003103912a94407040a05820341003a0031034a1580c00c050860301d81481003207800f05181d1103040c01240201801d078500c07038440380f0046916007580c0301005a1130400141c0803082081c00000c0078140407035500c611305803260701c0704260818240c0c058002c0c00302c50310000c00c45100138040408010641c96000d0707401d84281580042c0103540610641c1b100510b04407004d00c2508000d8100740d007100142019010714003840c4030000000440825615041d04424010404401d01d0f03030320781c80340b0030050504c41185803e28100e861402241c1d17400070050440b841003242035a40320380c4541c1c2 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 996627733 1250 996626483 996626497
    0x601141b03190c03080709060e0907030f020c0a0b100303080c07030507020a120201080c0414060c01020409020f0408010e0d0f03050403022b02010f180201140403020a03060506040f0e0d0e06 83
    0x54000440d00181100400324080c580f02a0085505540480c5501d4851040d00c3c080c1c880b183c840c0c480c09002c20081c00810200240030b07408059443c40700220b44c864600007402101e02c00e82c0149000009410210700c070700c5c0050140030b44080444c004000083e0003000990340103851503a602e031240104c3c14145d5240c400c540340254031080b00c45010806074001030404910074002e83c6c0354a0503640c0d10040f5101e612450085079014078400c608044030740303840001014401000700016003001d503070314125000ea8100556224a0741e00c00b003020700c01160244a00c20781c0352250401070181d103003400703000707410f040390044030004041d2240c00040605000300030848955403901844030311000303603058800f00c00310105950801075003014244096111580034640b501004166040d030480040c3c1e0054810210a440c21100780300240300003c050ba0711001c11000035800b0b1040803605103802010041110418800344034020315010552403566130010b400e034421611401e00045003520107000443c9801900 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 996628983 1250 996627733 996627757
    0x2a0203121305040c050c06061219081c05040311010515010507080c0d020f0d090506030703150e090a06180b010e10030203120901090e01120b0601140d0e060601141b03 73
    0x3101c04c2d02c225440002084220700c0381e010b0324850740b540320030450380700401002002540d120207005c00300010211140b00445200d10921480e00d1015020035507403104e02c3e40c6a0354003958600400080c50b1f00028804d0510740840020407140c500405c2510800d05040d624904004010403820f0401c84400210780c49105004112921000400802599509a80441400c50041c45101200d05020b180c0901c2a030f08010840d03801c603590440110000c2c0001540320342002615900040c0140080317004070300030343d817450181600302400e08205013130303910035401031078400c44030202e080108018131035850554a000c0c1c01b90700c090b15000c002003411a0160000395140c0a0070000520b0307054030b01d0050031003120a884421826a0310840d1841d902c80c244101a040d124a00206000a05180140d0f600200c141021100c0b9103105943ea00b0301c0c0c101e9429180925030700c0a800700d090000708503180d030012091174280f40c0c110342190310144601503510b00b0491584d000c0d99000d04003609100380d802010200e = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 996630233 1250 996628983 996628991
    0x1a030f2a120d1b0302060a0f140103050321010b09010e01090b0d021c05061005070c1a1309180807050a06141905040f020d212a020312130504 62
    0x545a070300e980e5080c20307100210360311843c15400c03a050081c00b2a03500f078064024040c1a134030300607040f01812190701c414030469901e02c101000c04a000199a000c2c47c0214019621070012a4403001c0004035000e81885400040004000300b03640c100c221400c080080c0b03000700a44085000690300781074503421000700d05c080032400022000850740a812040401c170380c503c0221000081b86000c0b02c806448540e044a80c1011008a880c09140102040b034407030200014030b19912400c4013030002c0e171203204030f044000c0021712450200007020310002170400398004122443c000e8462801c4840c421000414903200810301c0d00920505100c0d01344400d42145003031069000c000100003c011040b6900407040c126403619840b40c0e01203202c0c0d24402c640c08a0036222132400713a000c100c0d03000d03200401100d0b81c3c0412100242e0100d52524140342d420307010307251440a00d41000c000c50b40c4101c20040010007140221400700945d44c000b480c080b02c4001c81410725a22010b07462108050159600034980043c10 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 996631483 1250 996630233 996630259
    0xe0429090a0213020a051e0c060a0f420902040603090302060f04110d11100503070908121209070f080307060b0103200c0a05101a030f2a 60
    0x45003102050748200c0e0750120f8411008424002c034060700112000040040c00700e5190300344aa250701d1400aa84d5070000d08100f5607865092811104841000340192101208900c020407402034640002c00702c05007000b031421440e000e504500c060080d141c02c002c1529001070002c1071030010500900303c0c608065507141d0312070310054041c00035145e00314010f2280d8070000c4d00807082c4403a0b8502a44d8841002c050040900e000c0050640106a00f41e07107174101c8c0852800d00d60307511990240d0044650320340545914141c040039141c0039655021060325009121401e40341000181200d4000340c02012420450700d03812225450580c40750401410001240c502140036440000a03118080c4524018401145900011415207a46a1014411071040200c00c0c4480c10780f04042d10004030480c2c1210424001c1d1b40303942e031500780c00301c5090b6012596040c03030308802540d840c16960514000d0f401010280d001c0c818642c0e450352241c0c1c8501c540d070240c0010007500655080f4641501c00000e004c0040e03140 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 996632733 1250 996631483 996631501
    0x109080a05030c0f0d1e050f0a081006030b0906090a060e01080303011802090f01030c260a06120b040303110405090408181e010810030209091506040203010e0429 71
    0x10207015242c5aa104007481a84d038824000385008a0a1050b40e44c1410507802501e0407070264902ca200c9014498148a407110700e60070000609a0495641d071307082c4090a0208400200320401e170000d400b050b060685130f10880e105c5d42c00c0d00390072100c1507440d601e40d0755131595200e00400080d04400030120018000040c0e03d44000060340c10b0781c00d070f1481111301c0e0841c5810075049106900303405030020b10484101009600a5000c0c902e05040c6040c00035900990310400d0001c0c3c0040c0303004505401c81401440401d00c164402e01c00608818040b182c075400141c0c454089840d07000308020100360710f070021440c0e05000701d01590700409018140e00e447e42880d1920460a402800a03000036100c2c607409030345545420140506000c0810360a400710f03100c003000440d1568001070241c800c1d50960b13100003005803501c10102e4410810000540f507858a80300c0307030074005103014056070721650062005005402d48201c513190082d900c05424a8011216001c102d1010340403000c121000c400a004c001d0150 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 996633983 1250 996632733 996632737
    0x112020d0813081c0801061215050405101a04030c030206160609031106070206100b090126060a0b03011511160e01050a082d0f060403030906051302031b0109080a0503 73
    0x8000304a103411450b090031000c0390300c5c5900340300300d0002a80c1224950030701032542d4040d81d5130682e404000d003615074865000c07c1c1a15010755030703920489140c06003040607a1045052005069411405914061641c2c0325072000030702c1030001070303c14100024840e07011543c00608400f8241e104c10203000c440000d0038050403812880070700d41038900880000480d8144042a8030f80b043d0b441e04408440f40f8100880007110707070810282d460502c02c1c0f00200409140c1c0800b0031401011042d2204003844c80c20318180048400c040d03120100d21041400144000e4480c4614030700203001c10b1404000c000c1c00c04040903c0d00740c0c03800e0250058180200c0104400801c6c83c00c144c166036099810402d183c0e5641c00c003a940d4001001c824080340c0d40c6103c60002e40c002405171500462212046580000314107084c24107000080e1801c4010a0b52200324000304a598041d595102e08400d49030841000250086610f488005a45401c000241c2941035002d83c01602243c000e0071510f000c0710000c03106407070265a0384d = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 996635233 1250 996633983 996634003
    0x11b0b1e07020606030a030809120c061e130318030204050f090d050a0507020f0a08060708060316080a150e010f050603060a0b01090b030c07060f0c090605030112020d081308 76
    0x2034904100103840140005100b40c010354003e4014081000603450403201018054a41c20060041c8071000380e160411502a2200d005100d0113070400c1d0410181e01c41903513440c68203035001804450104089400c0d00f1408104203605800c010560b40515040d21605480d10380009501c945082e00303000310750080028040c0718071041c400b25a140016018151041d00400d407911f0300140003080600018104015000543c807406003060984ca5141c500103130900c0b0b82168002c00007640300c02001010310b42049081c003841150110700700b4490070841259120b640f07220003d048070386104000c14841d0345a41c8040300649214002308505c092078600c003c06480141d4009202c1c2c816800812402c040c83c0c4a070f00f4008034140c40d0099103c1c9080204682c5410003058810038050511401020803180d0140c0c0e24a4486074500040c020f503018806000c2d40c80c1d68014104012041c130041c4244a48101c0300d4a4407601280c01d40c41002080c90b10100520442a08500800c8012000102005d00182d03109c00 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 996636483 1250 996635233 996635281
    0xb060f1201061404051309021518010f050d0e0c04110c01050a020339120105011e090b0d0b0301020f0417010911010c03020a021f0f0e030c011b0b 64
    0x32640d94200c1220f074142602c16480c141e01c0c040004004610b800d0f9070054180c0b20501c00800e960000c0d8000680d10300801044a8003008005586081e0784290619031000c0304090074991041103205000424901607441c0840102d9510100d0a11506003040b101c0c4000b00024001d00c040c4041440100303842e0440f030415507281d0b00340000300f094200c0500079688220a810f2801d13815000c03040408140310103084002254980340c03842100b01031001b000901c22140000456500c41d4501030005118034000c0800d207041d00001c074400301e851a8490640c2003100c488882c44e90700c420081030304000034542420915450361000540c1a4019640d0340034104980d1012a43c008900f0703840219030aa900040005090440111503031441c2d60007031500901d010f00a10490f004000c655011840184034101700c2038000d89890412109650302411108044803a458201700c182c1e20000840c0d95903e015401c24117014420525190002120214440d100e4106c02c1d50159410514a0148006480700c48188 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 996637733 1250 996636483 996636517
    0x8070e1005043002062208030a12050601120509250503011515050f0c01020a0305040516080a0f030c050d05070512032a1606151502030406120b060f 65
    0x12040c4007441240903000906024200c1d00c540c0c02c00441b5400280425410b800f401440e40101465100c01e10107000b01c2401166645e06100d40030701848403402801003018180001c0100590380140c000819440851020483d900e6030750340035003000001c1d583d41e401c4012020b00e2090051008000714101c8005800800060741000c0c1c509840c0700da41e0180814110b01c4110300313101e052090004040c00c4098a0b002814075101c0b01c2c200c2d003aa409031405c04000381c0c8480c140b10611800740004900c062036111240645440d0020540d11400c1c1307003070054000042c1418174001e05000700e1610302c10a5111094801604440c00c0261194004482c2515030b88140c000d020b21000e80300302220300558003d200001041040c03040115a08054503e07030f80c07090f809000c03447c1c400d440138101d124500d02c2a2008101d240c080720042c2c907803a1241d80000d03000003010b09134600307180d0080116000c0d41c0b0369241c10740c2103038105a00c40d4042c00140010341e80201c00000d46400b031980c4c0001038450201c00c0c050f841 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 996638983 1250 996637733 996637769
    0xe0a02040b09090622060606020114010f0f0b070204090f140c010815090a09060f06030b060f0609150c06190e0c01020d050703030b180129030708070e100504 69
    0x880c504034102d41803c2d269101c400483c0f1a80000207645166090b42e40c0007000c080b680f6a280e000343c4070a41e0080016039118400d1410421030941304d680034010f50f9060900c200e00d0469410f0301111588161038407030000258403c103649030354001180445e00060380c4c2c0244200d80c504145c40e10100d4184034528010449030807080e41c40340c0c0107180280b4440101c08000d107920000c00421000c041c20200c0003594a51107600061414060030304003095420700010340c01e145040c00c00d464074000b000d0314428864940d00c2e0f5401daa0b2070b4280c50102d54245c0c3c040e0000c0003202006200c0e0f20400020145a00c1828204a800091b01003140c03286000280244402c40428000c1a40c80018042da280542c0003c40700c0d481e1588100c001d01400b60081c9004190010300c200400c5048641090b0a9000c400700030050004458020380014018007180c180240c4562a165140301d0380000b900000401c4185400319041170300c0340528200c0010010030884000c000740d10050a5680980305807400707000c58580034 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 996640233 1250 996638983 996638989
    0xb030f1803070206040e1f06030203060f03210906040306050906070e0303130e0a0f02030c280c1e08030a240302090a09210c06060911090907120e0a02040b 68
    0x1c2d8984a5010b008a41400d0030040324008242c40140b0b0300811180000c2c9140c1c2494440c0712035801440d95460041c3d0700c0c1002d4050017080714030341d00001c2c00303540b11542e804c1c80d955009541c001250107400710540c0350505c100028043d481241e1018000030305100500c600d840e0003046043c060101520b03054950884001815281d00502041c0c0c4100c5c2003242042150758030003104d82c5c0d400106440e0003e03420394141c0001c3c04a80050340c0803000048082030000c00070100c07483c07501020b90030080000081750342e250010b00302c1c4040071004210501010700c482007c80e00000c0d120f1a9640300164035100d02d0b203084030b000104040840d42d0b0f43d601154840c4a41d60100e11032502c00d41e500a01658030f19500c4035000340103411411400c446002192950f038120042115850552001d0359841d11024002806c240068464507002924182c4c900f615a03d20801c121003221070f030a0b400d5816003800d503a07854094410010503101d1010540c103182110249840105211000d00d108881c2002042003200034 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 996641483 1250 996640233 996640237
    0xf07080f1c0908091e04060f080d090f15120612110901150302160c030c03140c0f101806031d010902011b06060f0b070b1b04090c090b030f1803 63
    0xd041440c081103816510f00301003e42c0c0d00c0c045d8104400610103071000010400b00e480540c003a800400c042c0360180802032080c400b060030402c640c50150446030419140c154044040d1103042090302401080642c11801108403118034900a5030801400b69240018102880c02800c1202c81c1005454000d410f807402d407071658182c03a84c0d110015000d030081c07101030b0002e6004c900342c44050106600c02d40002070f000d81c4e458001c0c500c989031140003a0701c0c41c5001c06285c0d418142107d03554020039502e9655172524282e00d1404041158042c14460040b40d05903001a000382007581540c101407030210701c44d90903400c680e540001a100c03140e844c1c201c0303d140030b080b0340c03507400b0013400200c03464943d01c80d4854010001429134020800007070503a03516201d00312410540d5100780700d40c14002c1402e00a00014517071242d800310b081c081d0309440252481224030240f05500440c4011661f5150801d40c0c0f0744100c4c001c0340501904003601390b590402e42849200184200d41000c104078a0302e189403029800401 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 996642733 1250 996641483 996641501
    0xf030f060315070f031b022401150e06070b090106081501050303041a04081504030306120f060c0e0303040f030c150c06021e07030816050702090a020f07080f1c 70
    0x42d1042c0395101e8280032210031000c101c02c2010141c5480035140c5030307460380300d080300c00306d5540e00141402880c20700140086138a510020800d0300c0d502c401040348101808201c110356015161400300340d0000d000040c0c95011b200006005044440100184000154080020303252030720101d414645ca01140c003d2514424011150550828401080140d00520701814001200104982400d84440d81c0c1c600d4000006c02030301c4440345460600c130506415110314000b400c0410108401c02d1801c2e11100301443c007081004141039a80ea102c061306d80d2090581160107a0300809403562140c2c0c0307010002404450340002d03036140c0349804001075191000d024401000f0a80d4039000581c0d8041c0d15458025005840c1041083c6400d000b080180910a402044041c0c441e4840b004a8207165000d202c10f11080d040303990038020f0070880311b005650f030f101003d90b0004c10102d015a0301d40f84424035000030300612000074281e40010a0102d035150820000d4003031958040840c01500600700b0307248042c1e5100c25 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 996643983 1250 996642733 996642763
    0x1b05010b0f30010212090705270f150a03050307060c021528050c1e0901020c06031506070317070503060d030c06090b0a09030806090f061e060f030f0603 67
    0xa04402d010881e82040c06070402041e100050801044640c1d000d000b003001c6030aa01680c00150040c8450719103000f00b0304003007920b0a070003030900415080d0b448001c0030290054100d52a100c00159003c0c1c616036541c0070f0b1610181401100d43e6032881d01e942c0d80e8224503070403100d0741c0c100a40c0f466031901c0041c00850402102c0200c030080c1c0c0360800142c000c0e8051000010285500084c1c0312246012801054000e100d03111081c1d40c0c410100d80040c980c0c3d0004000b075000801e00b000b0008103603a001442c5445460103d4026540c0e442380c0d00d41c060582c0303e01c1c44003908850003055030001c1c550843d982e281c140d400d0b01201009035031044001c568601c811a2201d500850340c02030751012901c590010101c1c6481010001080100f81d2112a40034201312994903465403a00c0c415001c0583c0056040c0c3c00003015640d080d01410f11100c150354840340105254020449030504003150703035107104901c4110b040034011540d1500c240141901e6540204c40c4c402504030f03100c010601034140000c688203084140 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 996645233 1250 996643983 996644029
    0x606110c12071809080f090301180b010b0f0408010f0905060901090f06020a11011a032e020913050702010504061b08070f0c05070f0501020d17060609011b05010b0f 72
    0xc0f50700c40f0004400d030240307001016a12044000014243d600074946e104e01c2d121200e403038658000805003950814217084480904a800440003d03c443c0b16050548a0460440b0746032910048080c1003809242c0c0b24005545c00c010b07861004070b00b26803010142602a20075110581c4e0f4201a43d4280d5002440040c0300481c80510382c804105c0d2a40940101006072518005c0e408618281900350381001c9031a000c040710a0001d0680c6140400c881000c52082c2940c002c44101d171300c860400c124480256074950981c002801d07006a42d5858000b0002402540c0300304128146807000070300800040710104c03011440c0803403a4000310000c1c00000c60500c51503175803083d03543e05c50b4801c4071400c11b4542d0240500450a051600050b0180510b13400b0380110589107017500d10f4000020315202003500908140b02444e10020302c00c01c0801040c0303501c801e007644d0142c0c2da05410302c0100e400c800e840e036540c281c030303282001c58004100040d0413a1b51703441400c0320b4100b401c4490b88100111000313040401c151030051 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 996646483 1250 996645233 996645239
    0x15140106020714010908060f090d030b01090306110f070602120f190c020106080d050705150709030b040c05221b050406181203050301090c0c020f0d1103010606110c1207 74
    0x45141c84048843c0c1071402c44051651351070500d150000c25682d8020900000003041100001004403070805043d9103400c5c015144c0e10800a052109140030240031140c490920584902c0074600700e44002c020507030465920946410448001d4000c1c151200ca186c211402190301103000050040c010004400c4003402104002c15010081030501000000d5540322000044d003400148500d0034009860f40b0340656070004c03858281d051074450310003d0f40c00542c039030502070000d502841d408103480e40f1540e041d402c1d4465040c901a504016407000303602240c075443c860004500d03019155440d0750840014030014068107954207004404100f0303030000400521040100350700c104140c0d19400d082451078510b0a440e0f179007440802c04442001c1d40810400001007041441f2441401c216400307501d0a0f484046603a40003421803001040d40c01c3c85825005000b07030034802100418200100000c000b040407a41c0c68201030074007902086100254000c10748040d08508144a10b038002d84046c001504110b81 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 996647733 1250 996646483 996646499
    0x50d0206091309120c02040b2b1e11100801060509100903140606092a0318013605120a0516030804110102030a020d0e06090d151401060207 61
    0x890b54080d00c04103464004020100f0007000909000303a1907659038010380202c500512090711003000105025484d00a049618074403240d2058000542004180c031b400802400c1501c80310104444142408100369140e200304685c0346d42d0038000d548141e6080c001e84509000c00e80d500c0c0c40912940c0c0c040703241044200c8aa180a2002040d20031440c2400380c0b0040c0ca80c3c8034480441801c2811001c6035003c8402d101030303031a1220500368403d2800d000890f041d0039444c52030090401c0b81c44e09100068002c40803c020008140d204102c03011504001c004a0030030300303840c140072001c00c05101c04a6106a0108601d01d11100e294402e840d0440004c008980090504103420b600034100e902c20440c0a0069603650000e084598591500a54814a075802d0a060014842c806500000d042d0b5208111900c511900400d82000c03440c4213003445c140700321034140070a00318454040340315032200d1b0036103c4804211214030303c40356466440c0c408104100403451031403582c22080c024034001d0b91090b40100f02b000 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 996648983 1250 996647733 996647749
    0x60504091b0c140f15010e242125080115030209040305270a0902032421030415020a080f2d0c0f03041d180f03040807050d020609 57
    0x3d0a65084400d005800301a150a0071100c0c040c410003243d03035500401000c03500203c143d07041001c46042100f203c40790052201c200103180c40440c066600d1004d203200100710f0501c0d1403010311841c010307101722141410f84140100340082c04080c0c9007249c203002089080c014440d01c1000c08d81ca10b00b9200140c01d5400700180f50000410403400c0040821009914020106d072450050000e035240682d070319603001c100300c072981850304154060340c4140104010340072148807000074445607030011002c4613110030100d07011591400480342b1003114000c050f0b0004d1000401081101d10700d4203100184000100b0881e2180c6841502404104080c4000041e00d20300e44000c006900d10345c40c90002102d00c8541a03c142c0d04804c0d243c03030800364040380307041d24908184440085466a0806180b501d81082e906682000040d515005130307030941c1001444240e080440038540524640440c0c2000d40706c1c200c0980d07a984a401040c1060142000006a50130840f07103202505900800a41c1001c4062051008203 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 996650233 1250 996648983 996649013
    0x5030d03020d0b0402130905070206060a090c02010605191d0c030f092b1b021302071b14030f0102040803160503070f03030f1406030606040902031006060504091b0c 72
    0x61543c8080841c16a595440107103c1c00c44c0100404d07080700d240032203903412514010810001d41d00454200510350f0b03100c298000035074606020000d490340c000c541c22401000e1300c1d0440354004e209100b41c14440d005c8161040d00311554101606854440d04c4a410f540580990f12003048000034400308140c0703020303508070a500001a408032400130266482060002c0d041c140401100d24110035007184907640084000011107000518040e03003801640403e40080304520080001d660215510040000b8564070b01300b482d0a18403002000e0b5203482501c7c803100d2402d4520b0341320380b0642c01200b0f4802018002d8800b124001c102840c1040c000040907403180000503000ca9446c041002200001040a80400c14160007035900203004402c42a2030300031580290322030084000303034104004150341e0011b82254083c0f025500032404412501c04689008410240e0805003820030101265896105003c2d02c111800001c05215103100440781c440000308801c50840061500d282c2c14000c0340b10071090710b242c = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 996651483 1250 996650233 996650257
    0x9060901081f0902070b0a050702100e07050a030501020904051311100c0209161107080613021503040f02090604091a27030309070509091e010207020a0608041a0105030d0302 76
    0x49100946106078246180b80c11001e451540401d1759010700200110140d80311403401820001070401901c040e580390680e0301b56881d0350703403507503411507038404103000804c02450080c151805c1642c0b20301d00079000c0e4022180090050386071800003184030900a03c0803e5241e000180f54049c1122030f0288805070100000200a102c5062940001030312401c14042c0724050740c5100d28401c00701c81e03800400344100c4011a0050380d03c4900c05000302100420143d40245980340d40e181101341a101180d03e03141e212003104101e0501008100900c0b42040440b42000e100f20342d0110240d40e40e80c1000205e6a0a00e40580548644020003a00b000855802504000781010040061801c0341040b9007181c40c2e46421a0642c00c040144a00c0c1c40307003000404050a4202c9280c0160310b02555201e80ea40c1c4a038017400980e4000c1ca035804064003080d412200000d0300680010201c98407680d014101203c1550200e031811000c0000301400c191a0702d030320341a181c00401034200c0c160755240c1200079401000c031030f401e = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 996652733 1250 996651483 996651511
    0xb0c0f010e01020a1202071a0c0c01062408060a080706080106082404020a030e1006080c040204210c0f1214070311060901050c010510031a060d030c060b190512030906090108 76
    0x4100310460010711030080c0d00e16555036a03000b14619820b6407073340c0e40701040003181a8040d590700d0001752004040303980ca070f03d03102255589071000a1540c400c1d075441002240600c2001082250f070041450b03058407903507202c880c1e040c0c035041002c94043e9010b0004c0d070301c20700038900d00d090145410b8008104030403c5240c00308018545013078140c10151507102d144810340e598802000307240414050044a280b01301d4007141010700c0c056001045000e8400c0c404d2500468196042c100800c029130710010b0500702010105143e120100355001d0f1503c1041610141e10350341c1243c3c550072001650a080e2603000441d0751100105605000381c5401400303405050150a0000f465000e601340700705885411030088000041d451810b1141c00d5069217100c284400790b5800c01c00896489004d50788060a0389446c20303a0402c5414189600140b0030019969802443c0713075003100140d40344100c0030046e680d00b02c40004c0f8003001e410013541c1d00d02c43d0303004160700800113200e10306540d0300403402c05a1203003030810645 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 996653983 1250 996652733 996652763
    0x304170c0c09010f060e010503150135012d18024806062e1806020307050c130b36012d0b0c0f010e01020a120207 50
    0x2090082c0980101d490b12602d041d08000d4036a00c01c0e490300000340f0a0030038901c0c40c20140103408000800c01d60b000c0c18448142410311042e4488594208803031243c5140303010802e41c07882d80030f03032951081c46902225015500030840c501a0b141110320341d8201081c4401a0501d410319208024580050703c2d0b9401d0780c2405100300c0542460290340e80318003040b40d800550514202c2c0c00d00301400345846081120404038425222403c002000d0390800c504032028810142030030f52507842260903a00031030305250041071420300903070083c40340b0700c0002c007441c00c1c0e107405a00c1e0380c404c990301d00500b00c01400c1a4409407000c0340c0c60414024200903134030460000714403086100089104075480004500503264072404031703000c3c140282d411001c203c2c070f101c46440c0f09501d4600c8a00d600c201c03500070300c3c030400b000d140c084407135203218840d050080000701d9100d521a620001407a840700307003102000e0307c15402c20003070114281042c807c680000300070342c84442100c2c5d280070104009400c480011a1171200c00c1c6154 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 996655233 1250 996653983 996653989
    0x31a0d0323040803030f0c07020303040b0d092a091a1302040e010602070e0105090c09060a030e120c06090309030d050a030e0a1401200306040903030908040e18030304170c0c 76
    0xe02c0036043c400000d5a5030f0404466580c100c0d0b00042120400580034092500181c2c1c01204803401c50f0b4481e0034540d155905c0e80e200e42c004140341034008140481180300d03154a01c80f68041d032501004800b020000c12aa1921407900340d4614000241d80031007503858114480c03800c07458082da074801c00b03c001402c00c1c0d2a206443c080200a03000b001c0564007100e0200315810b50121150f0140c0742c180c0b4030741002e00340f21030116003e005000f410303445080003042074415140300360700000d01205040d0484802c0e003002081a0003603401240f01484d03d000b801c002640f1980000b04031506244068003c010000782c00404031503d8000b003035403004040d203a5504447c080f40800401c0b00c81d6002d0421030180300300320001035017118040d104074a01d51001044050000061b40c0076644e1000c0c0940f80450031800c1031408030014517030b40da00181a6200410040b07412042c440f5050710400e500e204803158000311301c00c000d5580c0001c0324004d00402401090860721081d160140ca68111a04200c0d91401e140c02c2c00 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 996656483 1250 996655233 996655237
    0x80601022a0d0c18020906070605070c020d0809010e01111903170708071e080c160609080705150c041a040b1c060b04121403190f031a0d0323 62
    0x741d0300b543d0660300c2444503410310001110244000c510031460b21401c500400c81a00400c0409003c3d60b5071200064042d50040c0c0b05010a40c1e4000d041c62041d91051a0420807500081c400500090030301e820191a135014a00d00700c006040302004100e00c01e0100d50b0031446490404081702040320100b4003242c01c100c290803081c020340702038132113048500c0c0201d4010104051903460f50600980b01125000041d00074243c182c1000b0341800d80365035100710070141e420072841004028982d5140041d00014070030020003410340140301d007058030f64200d0200004403045605480890620704204010842030700e0080101911041c2403001c64101551864100c0c1c1c0c1d900309540c00c5408845030b6103920002c42c40c5100d4480541011942e050615003022004121a1031280d001070409a5801101e99044020000d440340c107101818081315200c0d0110f4001c002400003d00ea00100b0b0a1804076040d841c0c100c491381c204548060044040c40e01c1d40d0710101d5072420340744142d810090b19103195006000c02180 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 996657733 1250 996656483 996656509
    0x1614030a0911060a080402011806120905010e0318090a02030c12060f041119082a0d110d0c0f08040615030803160e04050408071209090204090c0f080601022a 69
    0x150340c07a032071411f4000507050001d9140204507128a10106100f0300350005001441d603402000d000034925150315096004044002c165000e620010542e40d8241f0791217402054410401c0d80d100046807250f1003136130168041564030f0031038070700309000401c84800d0441c101c40c1c0c801401440c3c04401d1440c0e1000c60200d03003607000c500018620008120b20000341042c03030030b040e800e0720303280c0030400d4a0500704540c91003011941507030f46199203000a51000c60414152a58411b40c0c54040000207d25852171480782c1c04800540d50340d600b0450000012400303010000e181d400c01d61911402641d969540700300070300001e00c54061401070014044045980303c4050351041c00180020441c46066403000351884030060b041c548160305002c100000282c1e82c209440e03070198080340300300001030641016aa000d07503542000a20500c00f040c0050390400719080568420181c0d1111749625510100403a00b14908075a0706000d64080f82d240240c0c4601c0d144052826040e111806414413281e0001400c1c400241d1 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 996658983 1250 996657733 996657737
    0xa09030c09020c1b01140d020d1503050d020102120133031a0301090503040510091203120b040216080c01021e0a080708040525050d05061614030a0911060a 68
    0x483c034482c03056010805441c20a058900c0d000c08546240002855000c00d5603030446641c10114401c014810140c05441c18421802024862540313640d103403500d0a1100d00c4281c845104a03040c0700f400c14010700c21690914a0f2100040f8542c0c00e0400328500000380440c071003501d645895003401d0712141001a07070001d0185a5000c03860352045810340019200d0300d51507504c607914203001040040c40020440b8100c45003510407c1e119040a00250380300c1c0082c2c1d003e4501d04060049900c20582e000e03506e01402000c00b14204000034404090104a0240044034081d2401c14190000420f80310303c0503241d513141c490b002502c6c001d103000c08240d00000e0403035030703015400010075000c04152f00000c01a40c01610b034545016113107490f44035196108100070004d0b01080d442d0358200d407103603138007941407016000140611801c0d613098680715513288801c4500ca05110840740555000c2403003160b40c98680c62000718030030704544810440400800c130041080340c9101400115266544030100030b80b111002035 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 996660233 1250 996658983 996658987
    0x140c010b0109270b01030612030816030b1c0c1508060f010813111f0c05010e07060e0f03030909010807090b040510170a170901030605031506060a09030c0902 69
    0x403400142084030207030800401d803070760010f04001900303030680a4580885900804030340f209040005030020040e0360026000f03941a400403c040c56080003e132801600c0c280541d4000c0060200203d04544d071b80e06200c0e5100a80c115039806042c0e041c03050f800e98034003400c10085184d0f51000090340c522030705e44e49600401d01490401055180040182005110a080c109034510300450440e007a2110451700625081190b071080401f515140180f8010002c0c0c5000f4004851400c00083e0104174403144c2101c042d0f0925100c24842e031f0000c54000c0450b4520b4079400300300c3c400c00042001c000040743c1030301e0f0148000d11400456650b82006a4024100c5402a00c9054201001c2d0010344801003074441c022800c00c41030000d445800300d4220102e55403400014802e0100106080c1000c05590780540210020341c1145103645041000305400c80007600c1c20007001ea82c0d202810313143da0221500840316848200020228142000203004541003403a14400582d100d984440d000315243e04200c00c40c03940 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 996661483 1250 996660233 996660251
    0x90105060c0f01021b15090307020607061104030803061c0b070f050c070f030209010f03030c080703050c12090a0e0c1801180902120105041a011d090f090634140c01 72
    0xa0262005494200c90640e41074602103c4081da627121b1000c00a001e4140080c4c00307400c0c40000e074810f10341c100c1341400c160342d907950324208824142c1054810754411039030b40b941c5c0070310100300c5d8110311780b035940c0583c070b21180d07584014055030342a2403c250b49042c0801001800c1380d94038140040720142c445c00d0412514941140148039038400c058008c0120000010700070300c086a002425010001e0b8002d060a5844500340350441e103031301a9030700c80e40d09840780c25030107030b414031522014000c1c242d41038a88103541c42d41c580c00340301a0101a6041e1850700ca04210101211031500c1994001c00010305040c0c0d400300d81c4508414080003590b10004107141c2c081590f0100e00c5081e4201d6004140886040c8070f098900614039105603207403008030f4140000d844c0703c0342c0c02154401901c0c1600300001d000c0a22032806510800f11280115044822400b03420300207141d0386100c1200200e0388004800341010307600c9180743c54440009050300d00052002c07400304090340301d804400406540903000004500d5000e = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 996662733 1250 996661483 996661537
    0x9090507031b0b041509080607120c0c02060904020903010b0909010603150b030d0305060a170102030114030a03050a110c09041b2309041703040305190e090105060c0f0102 75
    0x1c500d01129159001020480701d43c1c6a41990305403405c54038000c1030348210f001c0c2918582c100da0b110404a000c4c041c00c000d05945c1100ca4a245451249400d0102d80c141c41c400b180c980342c3e040d40081d0309c42d0050111800604069000c1c180c4401c002c0c0001514641070800140c40d044204c900010703982d1944814400c01000600c101c0178240b0185080c00005c4043c00002c0e203420202001c1010555100002011940c0d203400c0c0200400c0003403a9081c17240074400700c1e04d010354024052001c01100e0050340310000c4c02d0000340c1030401c5400d640c64a040c01c0803c0403ca44040d05041d010b4468480c800602e03c0701ea0300e5103505805107204aa900045440301c0140303440382d0880d5402082801280720403c40c0a94941c40c542c100c040e070850f00c3c480241d849107841044810100e0043e11900e101200300010035170408010545c82c0c6800ea0444d80101c4a646d0448204041400e12307500314142d04010072003400c000000d00590b03c40181900c80e00858914054226000140d00210a1034142d520070082e207 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 996663983 1250 996662733 996662753
    0xa0b150705010f09150504062414060405010c080f07080d0608010b1801090c140a090f21290403020c0111030c0d0509120708030d060e040b070e0103060909050703 71
    0x6400707031014850714030b080e05c1c3c03c0003e190310040c03984856114000542006a1a403090780d1604810550f0072800040c42081301d00c0b18070320b0142c0c0501001d1082901968601541582c084400580d1010003140490780c4504a54016113014103028109004020014103020040c00120b07241360f5000503400d1919120701d00f1b480b160080c19010300010381101885188035544d02e41512222030011943c0170404104446441e106450100ca01201145e002c03441399020107a00111401d130580050b10f00c1d160321945900101c0c06000c0b1005038403c101100004a202034070021140c089402c2c40c4285904843c1c03100c8102c0c01715001c40050b0400c000805407581c00107041c200048181004604204801203615903c84580c4410005d102011031620010b581c0c0000804e05020500291a1710700d6031505920360303e410591080412501300440854030303c500c0c3c200700d4800e58010125038101d803981d0b4425946c400c014801c0714100b54440d03c0c0402c1e0822107020f016003092003440101106840c500308000b0345 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 996665233 1250 996663983 996664001
    0x5150a050c0702010f0e03070308071b05103002070501090c080115120c050d0b150d030206190e150105130204050d030e0109090509010504380a0b15070501 68
    0x1c07205018000c0983da002160400105132414030003441000300d400285041000e600003020460000740c218100300d00041c1c1d10501c4d0100d8584120f00e42e0f210410080311203280011040040c40001c021500007051810741001003c400445150000380040700d6810f0340d000c908290f92682d11a1030410030030070100040401020307120001c00210421040070149a40c03184640d01749000304241c1c01080c420781d10400c500800000300384821110300c07480d1820095008840700c07215280c078101014410b0410f01c038440441540350b800340482e030341c0c0d65005000d10360341102d5001819544102c880300c22001001001c18000c60034001c00e01c5589041d04200e1a900418840118035005220400880e1115003501e2407440c0d0500345841d10525103001295184519481881c4c91402c2c9800c0c45001c400645c0901d015901a59886d000c03d00c00b6501d141070602c5840c1c1d02000f0b588441b000d0390701e0070050009070340c100d84000000300c3e1500185000501d010613010060215280005103031003003020900c9000e4030 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 996666483 1250 996665233 996665251
    0x1a0a1401090605061210090c020601030639180b0408011505030304062d0e030d090b09060a210c0810080a021c170c10270302070305150a05 61
    0x50b5801c00c80820707842e0140d0f0030380e0b0116550f001d02264040b180d280b188806403030400801c0001c2500d000c4002d45c0c4400a10043d0349041c90400c1c00e40021a15a080708041c07034201c00804440c400d414010010008100400703401c00121805001c200e0040303031000300007003081c1c070b00064849003418062801c4441100c0401d0141c1c1c2d98100030080f6403400300131342d000c61710542484901c5150440c40821050b8900c40504a00800085a2074034070360401c0301c00030140340c02d0f42203500b00612a1003d40e00100c55005614482e003061000c1401450301000521285030645044810400d035120001c0c0010200d48010040c035441e8615202540d0707000c0c0b81235600c54015801e00d08158a040c51061b11003032003040181c003801201c03c80041107042c0f610f100c1040c0c1d511a400c0051011780840101c8940c215400444c0f0780e025203034250100b10750740c0c082c0c00145942d02c1c02d980040b1219118641560f101c0e10000c4055024890000002c94400d2110f401c4d444c1d1105e000450301d2810450356000c982c0300034200781c0 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 996667733 1250 996666483 996666491
    0xc0c0d0206090c04050907210c05011805100e03120909280911030313080c0423041407060c06140114040e010f09080d05010e0405191a0a140109 63
    0x1402c10010700d400b00c075001070780c0004450700e8000303a0303074240011504801e5030701c9201c0b0340c0d01400090224181605d107000340f480c1b0340d5954035980111a00d07500c070039612201078103000060000340b8000d94120300c0c1c40c2c91400d00c50001e030160030100342010040801c00312200404a0f004100b401d1202d6002d9002d12200404800004e1040700d2541041d50046507805103592221000204140401e0a45100034014100d03501e8030712854100b07504c2c42903070040e032185010b41c1070b4080b018200703402048042910825852804058040030740c410004c010026a0f030301c0c210701d80c0c0b5081070b10180030fa18040c0040f86d4a100490003a414840e041d00c207850030314111032540d0001041006810020303521018800c507004101a40654042c901602d101c002c542c8541c1c0c07a20010344100b00700d49004000e00c18029401b8080c580e40c2d17000d241c0b04500200e6004e06150010014030b0500300c0c0c652981510342c0c5c41240c01c000f0813050750f143d0303501c0010b080303900401c803c0d40d0b002000c001310a00448103004118003e0300380 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 996668983 1250 996667733 996667741
    0x2411090a060c05060c0c1e01020a1206080a030e0f0406080d02120f09091f080705040f020708030612072301121b0c0201091a1201090209010c1103150c0c0d0206 70
    0x140e900c60300104084501c50000c06c12490003001800211810135103d00201060440b40740d05d607000350311130b54007200825061900c4039142140e50203030404958030300002c1c016a085540301a5172607401c80749100e034400c0400191402d1076940e441035070068400e2000403d00300b410000041e10301400e0b5585a4510203050010500400c446000c0b241d0307210040d9441003507a124560040d100003c2c01c0c0582e10024000c42010515000c0002c0b000d003100c0080302c040c410000e044a42c00105d100300c0034007802030308042000401c5420811401c40340506610111740d040c40d5a15a070091580340040c81c0c0d0074410882800705601e6903c12549a004400200100100e1003402c041800140048284800340324001c401e00b0b080d0380c0107084440c010100c032200701d08c0740300c40f06032050900d0717000e069503001d007401800010901507401e04c203541c3d481c070301038441d2900000c0795250800d4850403145080d034144a898000c0320031044400e680750144c150740400b1911080d000e031285080c462022005000c41d07110380208 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 996670233 1250 996668983 996668993
    0x60302090906040f030f050702040e0f070f030b04020105030c041a09011412150d0b0a0c0f0807020c0415150e040605030c0303030117011d0706020d08070c2411090a060c 74
    0x84d04055160030540c03100010b50800b50360700e0144000c0a54403508d0800124443c00d404581098460912010f40c1c4003292507c00b81c00340032050f4000a0203407000d050010b4015400b0f84002d6800601c103a10150400b0341d0b400040030510300e081d8010010344001310f014661941c02841d000c800380c0d13a00034170740c1c24483c440741c400359805001881d000c1c42c001116108030f030302d031140030700c0349600c0e0380004030070500345130203500e9030050303d00526100005001c944052898510990b1218058449540070b040454210801c000241200788581c210030030042c903000401024482c0c2c20079041610751101c21003080d500d0b0402040f034140b5840103010380c0040c0c0354110540e030040200ca040d03401d00c8100200110801c5491401841405131001820a1560340c008100d240050300c003044a40503805c440c80030030091000c031100842600c000010a00d00151080001c900c15001d0343c2c2601e00002c441620224001e0308419500540c0c8100c0c3d5012000034030b09040d00341054090054009818081c450604541d14 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 996671483 1250 996670233 996670253
    0xc011a011106070320040f1502030403240b090a240b120a0e0106081c020c010c030521070e0909030a08160c0b0c180103050702030f0c070b03040606030209090604 71
    0x440310070140d1743c1c135064003a00340d020030282901c00f0b144940e0752039944800d4402034500e920701840b07901c03c1056001c101d41c5480001290705403030f07000c0b0300030204c190080000d22085c8007940108071015207400e100451600c4000220340708000c03242c40400e170740500b241d0802003951500c041d40c2e058442000240020950350003180c1455100c00700c0e482c4a0f031f441801c1e510041c15005612003865082c607800240d800e000013010395070111840c0b007240f40d000200d8010f90f5541d0126603c94085041c15402c00c003c24019406000d1414890a035503510002c2c201111a40c010100e42c3c00d8041031480074800701d54100700ca64140d00c401c01e40c004618203520803001402405c00142025110301d10141344a000da031090341d9800e9003a9024140788024100001448120340108281d11134000c0403d490700726640c480c0c0580c0340298015000345241140e02c40c1c5800c51039000b00c0b100c1c0318070300c904280018100456001944594040c0c4000a01c1c43d0451042000074800a01203e5407a80003c051002042d86280 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 996672733 1250 996671483 996671491
    0x1a0a0b03060607060b1c050613120e04020d06080706090f030f0803091203040b160215012c0c0c0705100e090a0f020c070501020c241602060c011a011106 67
    0x2074140d0300c80b0304a143c80809400855a1650040c03000b098a03410b05245400c1c102c211841007064600558980780520325030b03005214043d04195414162b030070a10300404106261440240007d4030701724282842c03a00350f0b69998030400706984040410800c6a5000d603152001e00441d07148504070a14644620360004441c82010706988800400b1503500c1500300044095101d481b41050b1722442c0a0400100324281115089103200c0d40e004440c99841c03010400c0710894032500786031412030342480403421003207010240054000300b83c3c0e00c9116030750804460f01072059907110460f565980010400608001241d8070030340c0103003805080407442580021490003082403e0ba00c4984654503103442a0240401d00380e940c00e0700340300151240c400f22010032400f080d1a003c0c1c00f229a4018058140b20301d000e501144180c0c2c03c6161031704d2018010206008000c400b180d0300002c41d000d9110340014802da40030095440340ca030342d0b94484891409902058104002007403c1208251006585071525448020 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 996673983 1250 996672733 996672739
    0x506100b0906180a03030c1a06010206070c0618080c1b060403080c012706060b03070c0206090a03020307330c08070515190b0d02031507020a050a061a0a0b0306 70
    0x46002c0009440d4a980c0d5154008002c1690940a1762410060081c0520f500c00303030b825141d4200c41a000da59102034060181c001a4000d1400ea55803803c00c03145601e0061007154015181c404c181c80e00d070300409000000b03a001e1414180d86482200c102803030b00001e1006006005c441031800074150340c0f0305003600e04598011410700d6958040b03072040c82c01003c9010f80e1400643e0004000c46003880007030401c0b1410741c4540c004101503500c41d80881c44038001180d109000a0303000b803a200c01030800602406d0505009031040600f10341743c1d030000b410000309070031031020564100f50030400384c0c0b00911000070f26103215210300c9402e154880003c0c040b08098001400740e4000046020402904010809920035803440d0f60b100c07400c20b0080008100142c28901c10164141a40c450162034000002c8811035030081c0108003061a441c0b0304400c0e20030040c0001e05501034404184007042d010720800a4052255000007500d107a40740024800076115294103004101c13202e0140103003542042207a402c850b0403 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 996675233 1250 996673983 996673987
    0xb03120d0e0a03020d111212041506032301020405061909090b010c020927030c0c010302033106020c1005070f0903060e0309030307050c01020c15031603270506100b0906 74
    0x90802c52401d8100407c1c418000740029004200c0c0c50382c00d034038500a61092006180741d41c803d0301d0f24415a0070340d0002814244c0002a100050100720007110103d0385100009400c0c01d50710030000c1c890b40c220080c161180c608851000300a90b40c4450f10030040c001c1400100041c4500800003440f00c403000f08002d0040c2540c80c08110030504240181400c01c070100c050040310303801100e0440e01c03504450048500c0c2e114048251030690b000e4020b80384a010001070300300a66004000071107010726202042c03e09012510905004a983d5000a0401002c0c0340010b004460b0304510800480e98020b00304401c12a035003c10911030b40e88001c0b00411640c0100340400c0284220101e0342c214031a01200035458800001e0040c1005808501c9824211098091b600d0840b840020b105440360031010b2421058000c0001550f190440010310b200380ca01031500003400030082c15001103842c0e9504200c441000311002010810808029440c0d000401d48104d04200346405108506070040110b420322070040 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 996676483 1250 996675233 996675257
    0x612061b040801050411130c120b0607020303040306060509010906050f010c113d09030803100308030a051b091305150607031d0618130b03120d0e0a03020d 68
    0x10901994054040324008118608052501800108024540d140102010000c00f40740803124030811561a448c1c0d1070340307500f074a941c0100030004c110301e407032690f44950140b1807030002d610200b020b48041d511901d00080c00c00e091a08110758214140c2c841d80072a420b1030703000c3c0442d03140e40091150104080c01c20046080045c541940103919503c0c076640c00c080c822003d005142e060a00308509126200201d2907189036040c039418103c1031880344200401c0103484200002060f14004640c4800360601c000c80303581d120303030f90039040354006d032580d01c1101c1d106c0c018042c0c2c03c016103600b54064503450503001d141c5602d09000c1000c4400f0b580304090016511000600180003030f080e81d0580300e00003411160b4030030f00c0b442d024000850305541d0024688449030030f040f031070500104036603000c2c44060b1101c400c0340506c1c0400140388840302081000c15210b24903140e9a07201000b51005203001d1f001020b480c0c40ca0303105010222030700805001d4295000c00c0d4400046900401c503520220700918040e228521 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 996677733 1250 996676483 996676531
    0x60a030f150218210a0b1008070605192a0816080a0206091f0b010309021f1223060102151014060711121e01090605061206 54
    0x6604024882a80c00001c1d02010b40c41c007004480c09206088465076140e0042c90071320b100580310b42000304800d50120110030046580910031981c4440902c8941000d1030b103a050b090705046813640001e0229101041c01c59021011041c081d40e4600b2920301047c4a4150301e00860300c0d00f0007a04482414030560140005024034907044904503070002515441d460f1051070a0780c1243c3c4280d81c5140140a11000f10796103010200c0c40c003020302003040068030307001c0459016800034a550402a07060680d14900e05c0b005031600681d003501c0d200000584c0b444896640405003015054580f03040d511450b003c280d2303c01c0640c1c2810041700c801e40d005d401c09607649060042c2d07d851a4590428007030300541d0104902e242c0300001c5030707050701d00290006140c42c058405110042c014a0002072414005480a04443c2030504400c1e8080310904100c0b03003d050000c80c00001480303100038070071999441c1c4001d10140b0613203008203508050f080d14030b402c034110b4808100e52515005007454142140304403600003c24 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 996678983 1250 996677733 996677753
    0x60a0e15150301060812091318050a0c150203040b070305121807240806031903030b030c01050f0f03061516050f06060114090607050f0d1205060a030f 66
    0xd5003840318000281019081c01010200300c4104600c20f6081110100d0890701c003180b07451000050402c0b403410007400ba000c211001001d4100c020205039541c10019641580360f020800c0a07020b280a000c0748185404d258030b08078000d0b005103420f90103512883d0f50040d0300100302c9040b1241c1c4800701c1e03124240b0b403804840034400e602c103d200309004234090101c2e1500e0744090140450030303141140c0c00d00755a004083c080420700d1004030195100041a4602c0c00c2c011800d19034031080090a86421020801d04c003030001380151800d40009940e11b82074502418100120f01c0c10300804d0805034284501449032402c0b0384a50041c160b00007030080013050040d11260f441c00c9010820200894880c844041c85044800001406a1752882441c2c09006036010120b00a8081c08c01a0740f10341c0d170b0340c003200e040301c2441e4040e0408a0f08198208130038008a5014005420140b01da00050440d5107013494004008416428491420034600f0080c8406039aa48070070030120795100034034680d0040c842c00c1170f00c640 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 996680233 1250 996678983 996679003
    0xd02041e06030503190c20040f0c020d090e010f0b0f070203070905040b100311060702030c040203011e08060702030909060d0203071806090908070803331201020309060a0e 75
    0x903080007800b208016010020308200581d031540e442d8400310f070203021100d04441c00c1000e0301103481c4113803032913200f4003124940044a20150000c94414100b6200c1d00c120f9a81c8d0040714016005030720048079056214659000400c19456040150750402520342c6c40c3d181c0b540700d41202c500e000150180203019a805a41c02250005c040d030340d00d0b40c0e4804071440a400110380460f6015454000107192601e0710034081d00340ca4111030880f00200b010024022113a104407010380e4140314011024000d9034072030001b9800780c009070b0769411038041c41703020b0310044d05103d070040311003904180e00704407101e03500100b940c12840b400c99403000540c0f50302c2c011801080d00741c80084d401d8003c081d27000c82c0001a81c1c2c00070030808206641000070316500d41d00c0301c1c11684020001800c800b810400341e40421010b101540d081100c2c1c03e03001202d03503c0070714800341013800d0302e45644001d00000da171501d00e40388c000840c0c2288452940213614525001803940d0312810001d14900110381c2e00d150403400d004c410070010284d = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 996681483 1250 996680233 996680291
    0x7050714070806010303080a02070c0e060303040f031103010518150c0c0a120905010509010c060515030303070e0f0a15121506020601090f0c051e0d14040318050d0204 73
    0x74607101c8450984400e401d010a9020960b400f02103000350009200312100c840c2c0208101000354107106107040c9040c0d01038016941440284400f00d030b1024803e80c24001140f28800d0000e19a41c0c0b42c050500f9110b004000a800070ba0040140c08000c401041e058404541d5062200c0d07150784850b8580b034113018244a01c2c03860b00c200c3e8000d00c00c0100750b261f200c2100c48030b5150380c40310356500c1e00110350300e114040b043c2d800201d03055140d6000900d02d41205800c466900f10341c03c1348900d200003091075500200ca0a00014003098032502140c202510321203216071f404c1c1c41081d4400e0070a03625080c245c070503004450400c92030346807a8044d031086d94440d1040002c038a582c01d031001e0340da0314025a030310005c0c00b6a0405900e040c2e001042d2015a01c50071400c200c0988929040400d001086003100c925881d565080e108100400703d5080340c14441c3e004074001034a0903809605081c14001c10980c40030400b518015008003040c0003d0741c2d102d038030340c031b0041d4102d1b07010900703074009030380000d2038101c010354046 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 996682733 1250 996681483 996681493
    0x60f09040207081602152a1e150606030402060906030601031103010f0519030c050111070305030f1209060108100b0303070f081e090604090f0b0d031101111207050714 73
    0x20008080d0800314070704e038003c480340d00d01c1070440e60400c1031520036248081c60902020030300e00356101030504c2689103e41d4244c2030350901210454408818600c442d11501c55401c0900c44001c0c0c0508142003c6d0418400c0d5403003400d51400d940442c8181c441e14078120b00c50032000c400140140e120390001c0d0400c00300d02210035203e5940d1110119041603d0160b41c5c8911038040392100441c9103c1400b00031243c0260611340300c6845c0c01d0064400d5650315030740b080e0f14020323200c0100120700f003040105000d14610b66810790300c10103c50045110900039241c0d140703541284004000c0f801000603030401c0c404c650790340019a08a00e1001916521031098020240000e05131185d0a00a04001402004003048951003404504400d00140383c4100482c4036441001480240148215640b140700401b41c607045c001080003800c0002100c00465600031800518010303d021507004080c02003088669803000701d80d00b05402a4001c40710214002d1041040010201301e540602c0010001f0003582c01c00312007520 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 996683983 1250 996682733 996682747
    0x120509060702040f0b011d1e18090303060907180303031d01060b09030606010903120804022b020f1933030b09100503060f04030210020a05071103010b060f0904020708 73
    0xa000c1c14800d504035000c240c1410500c522055000b10442400300001c5c54403802a030300580c8d0500042e0500103050f00300281c02280318451440400342400341d03001c40000d50b01c9141c00000c0001603c801401d5504100141e81111000940740c1760040030360fa4035040128070036031101492401c0b080520513044c420b60030041d0000f05051031400030074580100340d054440e280e0710040103407036011076880014000c01d08600d10320511881000e0084d0480c0c4000c1160030b02c011030328214444002070300c503a410300080101c16002146070509150208070016032b07500e0700c11100f0f18002d1099018a101c0d032421440300d001002d4000102900310403a191142c400c02d8020b000130b40c80200105403144d0994066801c0c40c0205580003468114102280c2004005006a86c1e606102440440e0040d00031020740c030900070b40c40d0040185002400302100e60740c0c0c40d2a2100d5103403c0403030925841c0c400c4075001e41d15080132040c02d6251441114441e50645120350794404903240850000d114010000d068502c0114501c = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 996685233 1250 996683983 996684011
    0x201110409060503060601111203041e110f0415090504020607020a0f030b0108031c0c030b0405130203060f060307151103040611011a1c060908070605040c1212050906070204 76
    0x503030b00b520070550441e00c050baa0100151802c90080f01c1d13520880e4082c10258015070030660007507034010301c6543d10600318017440d00001e100c420b11507012244c900c1d407451018445d0030402c0da01c950440301110203001100100103c1003250f002401020b40741a12000081c01303540b510b20858600585c0130b001801c05a0307503661180703017010913800101c4090481400014803030000000361110080c40e0301c8039011100441c8150f000401e0b41117a25420305403182e000030030f0356079540301d410b1041900c0a4110903006107441014241080100a20185000b400a00c45a80c80020f400400d8a08404114104009070f076029a040d035808031801c04640b000240200754568003603c518000c030b04400c002e000c600d50181201e20f8241000c88501d400140c203c1300341800d4a101e056805620b030007914000341010302512401d0740ea521400003a45c03001e841d142804108101c10020400070031600703030300c040003104a540f8035151701400003c4000f00103011448031036640c0c5940c00c5940e2036034000c1c0700304018601502c1d0 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 996686483 1250 996685233 996685241
    0x50a0f0e31090201090b160b0412021e190c0806010b0706060501020a0203060c0d0914010504110901150309112e0905090a0c021504080c0105060105280201110409 71
    0x810340c401e98a0880e5020010311800780110155050711000000c03400c0c900d0754651a0045540c640070080c1c050050400300f10700c22525800396008040800c3c14252185c0040c0c540701c148005162a04000b04001c9070342d0f1004190713641d000032414041d14440069082441030769184d42c12148590140c800002505034403c030084c000580700c1c40c0203211a680d640b006984030074422401a405410100004415401502c010a0b040003000c4000601038a280c40d164a8129081c200702d41c140c1d9141c00b13000c00d012007810300d00e1036503104940810496040503080032802d10f003c013042040c15200c110b41410000382e06818191840098415640e401d0000384521b81c420710045010013000b0400d089042e29446459468152100030b85203403041d40b180344a00f80104010317081300c5e086000e0b03c21113107000d0f800d40680900580c091035030140c0740c0b03002124040c2116000b0341105d0605c101044820b000c0c420595103003100c144405c658002c003940c0c00b0816030140c010111441503518001502140240151740 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 996687733 1250 996686483 996686539
    0x1507050f0c0906060a050d3c24030312090b0405030a08010902040602580219030807090b160c15020327090f01051c03050a0f0e 56
    0x81c0c141c4151200340a1240c10b11550b0700d0040081e0042200040e0510039801240c0c900c010380d245184100b076544070300840180c600d55008200d41a8689400c00c0d4405030203590704c0c0d0240d0254a05020b09d4240d601403002a080c44000e090105d6000e480c2249000d0350f02444000c1d411104980b403503e8213140903034695204010600118140c8000490015143d2003510284d0304260024100d1030001e80520f003250702220401c00542181d05510003134012000c10b044070f0308204c43c0008922110740340c4024408881da422010031903110854402c880c4446403100813000c4d80505110b1059140c500302201d52040d56040007000160000ba816081e0800c1d1090701d07845c600030300072114000d84230601c8103210480b001807071006a0041c040d0725180c000c903181500106c0d2078240030602c602c1d440008030307003c0081190000c40351600000108220305041802d0228031151640d4458810305540c0d0140081c01184586000c0040e80403804c0d10b001e0003420854a842c5000302042c0580c04ca1082c15841e440700b403a = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 996688983 1250 996687733 996687739
    0x10c03050a0e010e061506041703040528171903080610030912030c210b010f081311011116031e0506010902030a020910020f010b18061507050f0c 64
    0x5000000000b0601c120300c1c1070401c080281900e619501c1404120818a51000361700001c1000001284803000314240c20b4903001d08080d5403903d24180400100d40d40701e034507818250000c4041a04455881411041990a0148500602e18142080c0752a020340c0692000d00d0040044012041c19004207006104003c1154086812088080110f00382d41403144002c00240c143d4480c1c21000b80284c0142600c0056461320300c05066512904040711103d20307400d018503a9481100e580b06591042140725102d00a041c503400e90300f400c4a940705410548007003e0081030650511040307507842001c0401c0a00d50081c200d84005400c0380a811060b4494801102d00041d5005201080102080241d01294019018201c1607181c21000d8002c2e50000b0010014160f0800648021f55283e001c0035034030a02550040034004d83c0e10540d142140c0f1442036562284442015080c140c1a03104038180c0e0100c02650180300746005144041d03880d01410310000c05c0d60069884107460300c280000c100041103022 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 996690233 1250 996688983 996688991
    0xa240512330d11010c0b0f071806022a0a0303030b100e1c030e060319050a0608030d0b04020d24091404020f0a09110418020c071208040503010c03050a 66
    0x60341c54507030300328007006180d00b04000c442071202003403142c4142c1a002d0010b060412084141c0d507201840000e00310f981280d0074000c0c0041c01402d40c1e100c4200ca0b6880c406100040c01103090040203592111050480b80d0605180b040714001daa4511107023007103100f00988608501070701c0c2e140c0074000e081c2030502140149400010300e0368051040008112001c0081d0043c1c89a04092072404440150242c080d0280100c008a40c1510b444500c000c62044140202c1818890b04038030f41c0c04169030020340300a520a0a04800f485183d0000c4102c81c0c40e00084200003c4044120010602901a102c01e41744d0b40e03440c1004140c0c41c1d241700c00c050b41c0c0340c0d040d09117618040d03500e1f10054402c880c9511002c203850018400080c0050030b0044000c08680d0300103240005290769007103450141d8032072441d0307000060408a000c000c404006600c218001712702c00030a500b003c1d4100180d03541d90520384120381007074481c00d20000c140305200b0202d8000d400064001d1200e8004400041c02170042507a6032543c441c60 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 996691483 1250 996690233 996690301
    0x40e0303010f0512030304030801180b0612060906011701060c1e0609050d02010203010317030c1210140a0b19050d230f1b0c011404060b0306060a240512 67
    0x8040100c1f0b105a5141c2c603410407590800382c03071303842d25078250441c0500301c0c0e075401c1040a507a83d460050301040c200c101e41408070749009070038800c1d4640003401d850b041c0601510300c0d0f100714101c0d40302581524000e103411045080582090240c04109a4644600301072080b03514050020b26040000c1442c0a02c04842d51840d19410881c03c0348000d100281808107500c2191002e220704e00700640e00038004401f014184500d01452a8030001c050711030b1051300410b80020070a00c2d9025041005c80d2104031020010640307800d03030700d00d000d1054401c1d03000c40c6d0088901282105015009407031400b8034094080003c00d0f04c0020824144020304072070130401080c4000268029411000c0350300c80c0c5481001c03490400b084021840c10307078002904508940d500d40d4120340c6505900c02c81e8030f2045010b010042100141442810304209002c1c14036401110303840004e20000441c007000060042c850100c44861001d00c81d41140e080c091003c1c514000741168082c00001e110106040303629034410006060880c02d = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 996692733 1250 996691483 996691519
    0x20a24140903070f020406080d170106050f070807030c050a05160f061b050705120105010e0603010903050301060f020304121109060f0109030620040b0406110c01090e0402040e0303010f05 82
    0x2046801003250351040112000244d880100c0c00ca1191000e071022500d5a2600d01c2c00c5d0500c1c1040c03601c00000346a0201d034010705030452000c14010a1103040c01b500c5c08075400c440c1c203401e10036a40060082d0000041d00c4040500c202040420135820405545002a035841d102c2d0301d0b58200f050103d1125240b0750302107100c0001c68030705006c4401d02d0711580c13800522070030007080070f1242d804156064046c00d28002995103414100901c540c80c41d100016840d810304800c91078034580540340c28081c0e850503290500180c0c0004c100d078151180749c1001c0c070340b130011281c1c120b19512640d00b1000d4682e100d0440ba50400200c0c5038140103200b0704a4144c0d02e2652843e0510610101140050b400251841c0d002c20104401b603000d103403c525243d5958034080c01d00f19583c0180c1c0d1155001603030704030000030304221840d80980749000c0400d00340003030502c03001c44400081c030b02c1c20140100d40034031011102140440d95580d100441e400c900c070003506e03202d40e03484c0040700c01c0311420f204640c0120f56542007080f0006c = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 996693983 1250 996692733 996692771
    0x1e06050114040509040501060b03010b0429030c16510b040e0f0a02031603150c020313080d2d21090809041a1003020a020a24 55
    0x40c00c1c08071030700d003000d19040402c0a02980a0b100755401d55840301c01056808507440118041c02c0c865618554440ca420940041d0b0300340c0411030452290445880b0401d00c2c181c10850781c01c51090120292180e40b542e050a0382202034040003801450407044078029200c55080003150014074041c214940c0840c42c4240f1420000010511381d424a8603031100344010142d4405d03055004c0c09000001c40481b040301d4189040301d010300c250710f1588130b4524030045280411485410300c28907580c00e400e02d4a50754814405510b00e10400400d10b485040c0c0c000c41e54400c1040c0c035142c10011904000c0656614040d5850301c02d03004503c030004140449803010758104801187e240c01c1c40304041100c4200042040b9510900741c0514890050228a002caa00511b40201d14820380681e4105d0f940d0501307442040b084540f00003288007824203100b000c2c01c2655800c400d0365100080d600b40503a4400c29000101d00702880142c004064002002c03140c20303415004e10407010300200d058000c201000905a50050070 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 996695233 1250 996693983 996694007
    0x1101062303030d050708100e151017010b030a0b0d111c080d0b030601080f1c0207120b0106030506042706110d060503010b0f030a110604030c061d010908030403061e1e060501 76
    0x142c09e001701d0500d41084e0030329440210051420f85545082038440b03104901013a400340e600c2c0e000100601c201408144904600c0010844107102d60765a1661220f4903028a040320314030030940c880700b02c001d1071000780300c1c0b5420313030360000c1d0080c0d6a004118407600102844002c1d64007070b11684d00042040c1d18000307426403950316100014284d18409415104e1007032010300718401140141030700003454024421585003107a100e0000031541e58180200101165802070a061080d81010602401240018942c00c9000100d52172002010442c0c01c000c801703049094045000540300040301e07000719400f64840000d84004400074070144102030100071031800039842ca0b070b5051b00042503a0000500d2405041c101813005040307281066943d0700d41d8001c07880d00340c3c005800300d44901d000b51060608142000f10210007400d000744401d042451065607805030f400010541ca0b035a58000c4030055518015141c284e81e00d07841406070b44d41034019260454404020310500508040d0041440d60140301d0a0301c207 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 996696483 1250 996695233 996695251
    0x10b130306090807060c120c0c0b070f091809051b06250209011401180b0f070501110c01060e09010b0f01051804060311011101062303030d050708100e 66
    0x102800e54540c00001d281e000403c07075030410108a5400080e000340114007001c0c90585902200c4000503070000207a584809030003007040300320001e0b86e0004a880000e01e8001050b480c021303042d0210040c0a660b402c0454100707040184000340e001c800e0040366000710380380034030890070755001c0101000328a103107601e00314405034400740c240220301d650900c40c8511000c4a4110741e54403814245030300460b812603000c4c2c0202844202081d045642960002d199445a048600c24010190718020a02c4158007611005203540344001401d28107115094101c03207021320014171a0307903880a442e1691030080c0250b224900d28401e020740000e0005506200c0c0f42c0b10b102000c0d203107066040a40d07004450315030203900d07940c1000962071100e06003511a881070b07a000d14400d01c400b40741c41c003260002502c40c0c0c0004084403010707070406d0014000c620348942c4200490800c41c00d07803401c2b01e04c080c001a04500903110071490441c901303400c0040c440c1d4011100e50148121b140c1d91075525440d03500c4104090000c49407015 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 996697733 1250 996696483 996696517
    0x32713020313060908040e1e2802040f08060702030f030609061f030e19050715090806070305010302010e0405090d140d02070308040c090c020d0f022b08010b 69
    0x1045a45a4004540c000c2d808a1048850715440c0e80c0c0c0000c40e0026042500c00c00b40c0401c060000342480c800640c0c0226000b20f1401d1104901020800c101400600401025517407a0701800c0c1304da180d286c9048030301d140d07580641d203440e1101e540c005135819911918420780700b004003240b5898004406c8841900c0444d00607441c582e940000d00c01c00c110050002c0d074100d882040d107450030f0f02107018002c100c6070541d40c02103804580200018604100c00209004410f007110b065000074030001044070444600d5409881c9103460000155200d01c025488084d19024042c00c02620035410392246040c1c034401d80f0341c8003040307090343c00740300c00c0b600c044481e858150f1011036010209401404c02c1412020355014051030180000006000e90300004d00840c0407803009002e0000700804071306220040c00d01d551003017040404448009555000300c456050900488400340c00c602d510902c400d85402c01d900c9031502900b1611040c2c0020882e218030171100040c08030380041240c80c2c5541c103c0c0c41040e07402d18892 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 996698983 1250 996697733 996697759
    0x3e10021312050a032f101d100b19080a030210020a050a08040c0503010f02090a170a080a0e04180b09060105010f030f0b150c06011202180703090506090327 68
    0x2e640007000c01d8400840e0705840103080170f181020041e0b050342c98040c80c00303082600700080c2c0010070b42d650b03491f151b424240c050300d442c40c0302e000000364000070000c00c0801041440c01d0b040403403204c601c05e081c03580e4040f07030b9800f0105401c1c100207071003449288654221031094a0140e41788040b40103490b035450010b8006c00600f450702e881048800e42050003507101022460b51440080e08443c4414080003086401154401340c0340790403e011802000cd01601d01d46201c002d42c041902c2da1075100008100d4480485c5400c038080c4240010701600c000504108005071905202c030032010201082113450750b40d01c200160b414540419114106d030410384400010300c550101c00e40207400026290040c4a5035264600740307a988014081c210312203088117950761210034030300042c14080e050300180946070743e00e007625006803916022401d00700340180603101a602c0d0b610084000d003401c6100500170f40318060521407891000710082110143c40514201c40c1c1c000800402d240c0016494010340c0428041208 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 996700233 1250 996698983 996698987
    0x60201050903072301060e2409130f0c06171608070e0310110307020712050c040504081603110601050f0303030f220318063e10021312050a03 62
    0x5800680003060802c84202d6913940c4c41421207807581d00c418030714103000c014464040b0740c074414105e1200b1040710980402c03805002086a00030040c01101000042c12010300a0288014030301d0342d4680c3c445120f400c0e40d039136114010300c0c081e41212200101c03ca200301180100783e19a41484805402d03031543c403000e9480c0c0c10203030350102c1c0241c02c09403d0301a2986502040c43c0e20701c6005044828640415101d0910842c02403a01c0440e40101c946074007651740740408202c0c000750b4407011000c12100820166242e00e0b04148502550761403101101c411103c0340101500041e07801440d892440c102d40302a07a0341d904000205009550707554160b00100041190415800103440e800000303411055003440e03500c0712203a01c1264000003035000414922031402542c0c000c01100c0024560f6151803131461221400300646507101ca0344094080b40c042d608c141440c00c0042c000d56035081c14500391005009044000341c00307035100b5450800e643d801c068001c41d010300c46051410480707410070010015a01d19581c1 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 996701483 1250 996700233 996700253
    0x90c0409020306180f030a1106012709020a0504140f06040515061605060103150515150c100227040507320d060303030b030a2d0b01030503120106020105090307 70
    0xd0701031507021704c1040407081e0600700000d040241440d51a00607401d04940c01c070b4200f80d4182c100b00310b0303010000e085000703a03628402c51600c152011480040ca614561002401044140e44100d4100303060010582d803003101c0d00c13141803103502e6142c18204690f403050200011a04100c07004402801c41c2028110f05080c141e015210140044100c1e400098198880c0ca00c5c12009900403981400f2074008078079a000c050040310f8118062140000402022078001101800b5681da28040c640011898080304031042142c06030f00003500380c08540d00e203690040700c981f581190500150110f40c802400c81039040c41d200f44c6104240c0da559558030014a880f060150032603880345100301d034103500c1b10078451441c040014403840d2910b0304001002ca1540c034001e0241d94010140a00c030b5003000510341d011039020551252450a10502c08800701c2c0b88201821082c8001c01014100b5201c030000401003140001c001e03d010f0080c0b110b0020207a0317a4010403420703100c0803550446d49401c10702210300041e1000320 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 996702733 1250 996701483 996701521
    0x2100e013b0d0204151716030312140702070510021f110f0301081005060319020613090603050706140319050c07150504031d0102060c030627090c0409020306 69
    0x440b64080303604a03000141555404480c03545080203102c41000b030300c440d9020000d8201c6100018000c2108454041d607141021403202600340441490001c82d050642c0c1e00075000d00315901e0f0807150b03500705143e000355a0202030240700d001d4107171602d260340443e00008074080e408882d000300c80401003040760480090014800c03000318814007032210580302c0401e0400b440c040c042c550000c1515034001c0c946030301600c0010340a140250000104030705031600d4114208205a01654601d0780d4010b844400324540407164400002d003031a05c0c00100c100040800d060f0102c42151b510114191100c0050910510041d110514064451940500081600c1d0010743e40000c0000c01c0314213001703841d1507c541403d03610050880d5147d5600400c0304242d0801049250459403101400c8020404d1340003075035900d00035290f05035143c404400600240d41e944031400700c014540f042010601c480204020400ba01a00d01a600d405142c042410b50b0a0502c19408101d400800401c103988400704440000d0b18885 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 996703983 1250 996702733 996702739
    0x40e0105011e03080d151a030406060e1504050601020f0a0c031403040e0a0f02070210030e060f0601020307030305090f0a080d0c020606150304111c0204320c0702100e013b 75
    0x6030000412200c018440704408100721a200e65174072700f91501808a07241c80c1c00030060403a200d07081c40501224480d8254504100340c500140036165040180e20b042d2000c40c41102c0743c442c0a011030100035200803594103e0703100b0f078199601c1c18a50343d515134032400b841c0207450108603100f00040900e181500504080f9000000040c60101c2980100701592604241800460340700c03030782c0d2441d0080403c011903020031440002c07034840c00c05600003500ca10070070001404054a50380482c1d59000d01b4094989550701003011904641d40c2c500c1c15a0403900a60700b0500d24520b070209202c4054000300300b01d8072900c0c00034040c0c090f003215984102c00c25007002e0001d443c41c003520010450240c44800e480c2d2500c901081d00030004021910400c8140d800a0340800b01c002405645220f090310b180351050b0260904da140e40316943d03240000e0824a0181410207580085428407002402d5008a1403500341982a40e03944050f02070011080600850350003604503036031501210b080000c40e000003805a1546c02 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 996705233 1250 996703983 996704021
    0x90904021903061401080d172e0e100e04020108010e15040e010b0f06070804090e031606060603060605030601021c0318060c030507090f0b0d0b040e0105011e03080d 72
    0xa0312240f088400c00740c5030b44143d501c880c0061004000400000780182241c0c5090906e01048444030426508082c2c44040c036010205041302c424060724190072103881311051516095907071514080754452050b510f109144581460210390410070b10b40303d9120b0354060319884da450346445c4d011034492600411032079458500809182059507140107040c1000d04081c004641c000341881005072003240000b4245c80340004001100c00200d5510a07102100c2d0843e07000191446100340340c07800c40c801c2c5100e81d8044001a006607013040030a60004040e00d0a5a0b820007806482b604103960900c8240e9000340964041c1000310320814000242d04009401441c000c00c9981603200951a011070403801101c11940361030204e80542da1512840707500120f40d180224000d45400000010409107001d00f400c0038000182059000c40c06400c4010300c0c850191003044003818098005009000c00c0c02040e02004116000400300b540390fa505205494201d201c062600301c0480070710004110740e10942e1449010 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 996706483 1250 996705233 996705239
    0x605092a12060906010504060b0a0207051908060f04060513110d0321091101020307030f11160b03330904020d0f03121b0507030509120d0c14030909040219 68
    0x20500c02c00d070003140140b005003010350602e01080241d41722034001c41844142031042100e842c0c2c0c0003450f1000c4800c20703145c14615101c0f401030490080c01a402c481854810300092111625611414620450113004100120b840c0d0580715071901100200140610b402000390701c0c2d070f40ca415401c0f40c1103c0c0c42410034249803440810102800c2e00d81400042000d40c0d500c00b1013007032042d0b6811420392450700340b000c0c0d1710b42038207039402801002c0942c168200300b0800c429030b00c100b07440804c24161800d201001c000c545035a40c0d60103004a9100f00d96400b81c0030704e060210000301c9103007035082c0203461001d1983d61527510040244211400d000303006070391116411744030002080810b210311784028040c1d6610360590240c10302e9801601c036a07078000d607580604c2c003074101d0300345503c0019030390220350603c3c0040e80c80c10344500068500e5140d81501e60280140101c242e43c00ea0000d0b40307c181c141c46132058110f05504010040d03100d000c1c140c0c0440d0485003c4c4001001840e1410074201c0c0381035450364041103991 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 996707733 1250 996706483 996706519
    0x30d0e060709140a170f0c0409240e03130302240306100e04020d090b1027090c0f0602150c030105010f050d1503021804050c0f0307210605092a 63
    0xb80c1503140f44801c0e0000c207840107540700e05002401f40c0b40c03000e990074081820725944420001410850000745c0c0300c0c40005e09450306000d50094540680301c1e80441c0c0d260080c00b10f500440c0003803444101d10500815100c00c06000d0348180d440601c0304031401e92815070b5900814080503440f440c11002c20051582e00c0c1c040e00d640d852029003c09401d05000007a41c44892910040240d4040e0400b596511801d4003040308a0040402c202c2070b100c40300c4181c120703045810103080a45640500102010003141001c50504400540c0d541110800d50880e460702511300c10181925100303844038400c03100104014881c80d40142c80591002c0b1031890114a4642c130882a0822107900341c40c0040c1801052008200354030340b01c070b035800c6441c2d00c040315003215050941d54540d480c80c1e960010f038043c83e107441000c401d50b5420b204820003498044003516803042c130030340c10010480390102e0454009203860f02103006c0c13540004540d1400c1c0e90115103480045840c421074440b1500202036150700025000710010181303 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 996708983 1250 996707733 996707759
    0x140403020405040b090c030303090d1803020907022506050d2007060501050f22050402060904090c080d090302030312040f0804080d03050c09032d010c02030d0e060709140a 75
    0x900031002e5009509100c5c2e841420318580e01c00c054444d9000b4004c2c012071841c0869021582065402c105802840c26003043c443c0340000e50020750b10091640420001c01d4020032600b650012840c0210509801c4200c0c21900807018000c00f00050400e0207805d14504043d40b05080e040d4659903d01c40410882c3c034203048651001408680081d1600010069403e00420700307400f4600c1110040c4507041f601240da0400c4d6034484500140c69210008281551682070498042420245c02400400c020341400040c101c407903c6000c05510421614450062140e626a815264000c02075441e05145c01420303902c80c603003e402178131000d03080d104000000302c4810081c0024a411006040341c107602c3c00010f0216000200301c0007920b074040101400795500480c244a4040120761131104040645000d003690062021284c8450b600c0c05050001389600000949407a501003c1c05100030185080ca43d51151030030b42d10100405d21180c41400f082c2101c056084c90940003400c00c070151a500c0744400703900 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 996710233 1250 996708983 996708991
    0x2061003030302032509150e060d050a09120c1112060c1305060a080402030c010311040504091106180a06050717030403020f0703032001021c0b060412050607110105090706140403020405 81
    0x4542401b104000c441e554183d00e100ca6041410b100b42c40d0101240428160321440500780c00032035842000400d0b403c61035011509040e04a0500c4841c043c2140020701280740da0013041e55403d1100d6508410340c909a59130b51000908440075003242c1e1115506408183c00111140d02c1409500402240e99103403030000d01002811030750340c012582001d00606003002e4110304a00c0c10142000e50340110301e110304c0111400c9a100352400036040c08542828003038050700c4003942e64003400010798071010b248154040c0608a03c110f507007010f5659511025030b4181310700d00c001400d8031555803041c41004850000740d903005010707006a42c07010403a41921070405410303800031800304d246000c00030740364040743d8264421807035040001c40c03030f040d101400d00c200c10302400902928151110b02815880d120041614010301c01d009014041001c039103405500c40030211200c43c0007415000810f10310900500415003d4800c2e54003916845003008070894000303102c0303040c51002400422000005803140d2052030b2003 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 996711483 1250 996710233 996710237
    0x503150907082506050a0c0b0703020d0603050a140f0d0f090b191409030c0910050303040f060f1e141e04091103010f120c0e0906090d020610030303020325 68
    0x412100f10700e0403d88000241c000c4010440240800e440c4030740c0100c1c00c14a0700e60004103c05107991049001c038040d00ca0b8600b41c45145003046400810480001901c02a45200d0088588603480d140710869840706d09800e519220780c441c4101d945070a010306008507405500b40340211605884641c0c8070b44036481500c00810101100f5100003005a0054000c04802895101c291810820800013540c076240041040e201e40401008282b1154400080000038600a02a80e4541c1c0c4c1c1c81e2000da6818078140304038000b1610084031017050b035100e912101f416603980703002d404004804190031992111070a000d2911660708006125440401c2910003d036400400c000c5581c8504000c08001511300c40004603007a00c0d01840144070809c52041c65501343c400d80c0c8600c0d80c1129450601c0030003126642d1010002d03440da2020b0010200c0c0c04556030f0311030905081140c440702e1300000101c0e9211012142d8000c94100d0810600c0042d10a80045401040d544a003000000b00c008000045000d14002900 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 996712733 1250 996711483 996711523
    0x9062109030a0c06050919111f05070602180d080307030f020708070809040b040608010b19060206010b0c01020f040f060e030c01080112060209090f040218060d060209040f0c081f050315090708 84
    0xc20f01e0401380a0140c5160109513849d001c00b011005002d034003920400a014a030040381c0c50242901004c1008903a1000070701e2201c1850f090b04014490381d0041c0d0b402c1c80040d01381202050404041c0c0200d500640d403045021380360008513112010103030010255290f01540345d001d114110785e02c5010341300140c9094000042d51b20032900400049010000c6054026400441c00300a001c5d00850b01e60704440952001d1641c4000d827424823402131145c440c02c0b00020501160105012410b4424201501c1c02501c500a010307140404041d500c034036030603045000070040c00040c810200c110703070310041841c8981409400d00303803030a00040d450302c8100c508030140d0000c00200015481e00c1e501d1003a40c0401c0c200d0f60390740c909080022a519180100f8041e03e03a0b50001074180050312268441d4540c80c0d54084104841546400c004080000988846151100c03900b0345841004580403a5021660020010205140a460501c01003140202141c220740502900040c01c064240052004404d6421100c4 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 996713983 1250 996712733 996712763
    0x1b1406090c010c050a0f020315151201020c06010315060e18011812050307300c090803041a0c120c070e0603150c09062109030a0c06050919 61
    0x80e14003240c03180c040341003102c140c3c0f81c80d01054000c1001054290000091307092803201e40003003842d001e24031030381440b001d00c00420010b410300740d003029403180d110440360740348070140c2031442c1404d07409288030034481d80e0820001000014000d01241e6000f040b1810081100c669440004c00e2040302210040905001d280f00c00b01146420310030740d0300d24100c0c01e14024400c1c0d2940c0700c0c51440ca103544280e0007403000000100310000e0103a0b61404816903085007403154a001ca10700115428000c1c800d8901d05402c0901255540b80514900010b446c030f03003801942814604075100c150701585416441c0c03201410403000040d11014000c10b4071040f228500326688055041c0c00a1900d5100e0f480325104805081c1803060310399011801004c00040f0303104511461320341c072150303d07418840c08120903480326001420040740300710a80030391b0b400314255500c0281d90b503491003450380b00e1043c1c0340720f0400140340e440308400050759640f0158100300724100700c41d0100c9416403140e12042c000c810540d00c0c040c04c0c003680 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 996715233 1250 996713983 996714001
    0x71d040e031207090f060f030b1f230f090a0e012601140c0a031b11070801020a0c0f03110102032401030c2114010627030f031b1406 58
    0x500d411440f1032401d0006503150840c4d01d059003019014031420400808400708070700d03200750440c40318070b10020050821101d40c2001c1c40d03a1b082e41f041003000032621a000c554011201d2419810172100b0020502c0e192001c40c070001c115507800121001c0c1c0c00000d03040080340030046041d43d04e0283c0b1390b07082540c1c100e00c41c401c262010703400d2600ca1550300343c0c1840e131078481d1043c04d2085550449840c0d41380d5a1104100300003900980703010007a83c1c3d02d2058148107440d08960201108006034500800e0b191160380b2000110b09078420850003201241c9062240f500081070403520890a500070f1400c11021100740441609985c03040c3d50080c2c4e00401d07120400c080c9004940d0110303280f802400c0400c4404e142d0440034105540d19285444c40040f0980240b10207081d0360410900076800140c0d40c0425038441c170014014108844012007255612200b180c8844001001d000c15203800940d04c0001c0412941c003114156400301000d410580071001450001d00c8003640f04071190500405040c0301d180810344 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 996716483 1250 996715233 996715267
    0x612090609070b070f08030a09020409150c05180607050a05060c0403021005120712020d050f3309180f0a03020d020a03051204020f0d080409060e010608071d040e03 72
    0x3103c0d18000130400c0f00001401c6a45000c4c0265000c26142c0c1c83e0740d00e42c3c034098010024031501075002070405070b02c18104007089600006951ba030380c10130000d107070b0704180c211f030385000b0300d5070342015082a81891111271038002c000d014000d10071022130b107000a8680d903180c14408107492501c1c41c444040f0b421700031454044400c2c3c0c0c08215600e0510300703211107044c04040c0c110014001800740010714518031a900c000d0340445002c01c1003e1410b000b5030a01400f66204008101d4092503c0507000c40842c10079a402003404000c003021600160003244000c0400000701c8010302440e806440c50858840d10083c00d2100c000c1d504010380103800ca00f1002d05019040041c0180c2100443d0441040c0d04000381c0c00030195601030081c15034200d01640e4910200e4040f01410300c0165011100d2130448080003a400010415902200014040030360741c7c48802600701001e0050602098444000802c941c2c8117400d0000c2900303051241020388900340000c50115003501c980a40280c10009441d0003c10f50961 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 996717733 1250 996716483 996716489
    0x110d0609021804210e04090203190803040b0109060503070e06130c020c01020f030c100b0303210a0f02070b070c02010212030a09110a0f120809040f0b041406030c0f061209060907 78
    0x410003400344c91194028148410003a84a10482e9100149001e45d00c0401c03209a2070b1030302c00402c0d48050f009040003009500201c0301119880c4c00400003280402442c002c450445030003500401c0b4044c20300b032540b01d2101c402403da0b60032030206a041d24001c1d50b580a00305885400350050891540548002800c0440d00301c2401c000b54410811001a00c0d00020f03600c44141d100d04000810303510450000381141b20f880190300b4820342d52120251700c0030345444882c1c01412201e008100c900c074a9441075060f4040c00202501c440c18060003c0c80e11801051010120f43c41403040e50031001668040c010984c0041da0301c82140f41d0344440142c104000303403500180d00c0170304490f40c1078440d03e0941c24030308801150051026442e01450000304001c280001c0c0d440d522401442400140300d50101e1034010103500620038815401c2c00d40c80150004184007240c002e41d000380c050400105842c042c49240c070210300080740c2041c0d00700001a602c058851540d806000d911000e0305d01c0d41040b80c140c3e0300c0d01489070 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 996718983 1250 996717733 996717773
    0x30108010f051605310503070e0912090316091a01020105010f0b07140d12060608060109050411091c06050c1c0f2a1b110d0609021804 59
    0x102030001d5100d502c5400d035030494140c6849582d96490888040e01d50040103044c048030802e1406a000000c4505c000c2010b890b002e0302100c6016945610310300d0340540603a0051403507040407580103685400100100030995026045801607845c101c0c003940a0562a40725468181c2d445150810001e030890040840100910003804954180701d9265801011031140c034802000014000041141962205002d1083c1c2010b88449800d06000030340050091002c111605190482c0418968011480c0c14080d102c10381d1444a15405d0070244130042614034158001c0401c00d10292545580d4080e00c0c460040c5901e2541c0003201079440d0000541e00302400c4038181340303000d22450076008106039208580c0b402c8500f020422003241c1c6441401010201502e401c207071413840e841c94403c1d10480109140c4141b9599103007030f0103080300c0000c0b40f07200480001801c031103204c0001e01c1c6500d02041100d0916000d80e8000401c3c25807680042c54030b2240080d5007000091440c02c0000340541701100043c5a0406 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 996720233 1250 996718983 996718991
    0x10b010912230c0a030f02040f0219110f0a0312060501090e0a05040c030b0108150901020f07020f1c0f12020307030e040c020a060c02031b0c03030403080706090209010b030108010f 79
    0x60361007000004840c100d554424501c000b034003500711010000364070191006056103140584a050203030140c6107214040e80194203002401c0d011603280d1003110714107011b500401c0c24104001000f11035511400143c0032280c4280c0c034a4003140c002c2401400e00b2a0300c82d498144052412441d10825240103a0200d03041c440101c5040000c44850414143d008900400028103a6030300c1c54108858440c0740c2000d0444c00c421b44c00441c4200c0009415541c0080c1c1c2400c1d03603d40d13920721014034207034403580a50f101c1d02807044c00791800608028500c5c559000004100420304401500c200b1a45404008162307001c0078a40c5440052007808004105c401707a151000d1450b10200b03480160000354654405030040b9580da5042d11740310b00c00d20403a100350307500c07150520000228140083d940c0c1c1068000c0c032000e5001001344038480d078002644110803840540918140345c81c3d03440f800d859401181040d1451519038004000503a107400f2624041c00e06001c5194495040050050071240c0500b5030240042c50 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 996721483 1250 996720233 996720269
    0xb04030203120c0a0606060f0206160504051306080307050309150301050916020307020d060605011106090604030509011e020105070e0d2f03190b06060a050a0e011709010b0109 77
    0x1000c68600c5103200120941c41d640e400892005103004c501500113081c0c10314000003c5804d81c1c0c82552482100d015034226482c540710f6180302c2c12000f41404040c4040380040104100c9400d0051381241b800304002000a886030b1386806444c1542d1101034211100c0c0c00c0021080034034584450f00400a50359074010324250360601020400c420800b402080c404c1d200c880c0d101d2502c5208204940b401d0394041c1101c18600c0c80c03440c1240240c0502e02481340030550309250304151020002e181d500c03d556142c0140800d450302c3c1c9040c2c41c1d5601070020681001020720341084007150060000000301d00d66800041ca0b4581803400600d82c44d0001002880f03102c80308003a00100320030303401d981c880c5406c4000200107600c049101c20390b1040842c1c0c0301ca03010300800c490075003048107003098900b0260082c1c9180607941d950b0307000c2014510070084583c010070010b208807103066110302c840c0361410350306040150b10001858101280c0300011034860003183c1d100d60410350b6a5074069030810003498402c10402038a14 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 996722733 1250 996721483 996721489
    0x6020706080c09060d15080105010611030708070201020c0303040b1306050742050603010b030a0c120305130e09010b01021c0c06090209070503150901050f010f140d02130b040302 78
    0x50b004000404001c200d0b600f031907039420110b601e81c480815003001403801034070808400b24058812290b05520741400041c0e114042e210303e002d41c540b01006103184c0302c850350301e1112581141c6030070303811031180081f0001103071020401000a081c5009840e901e480d42a1008400c40040303801040420006010040001e00e0b4084070784801c2c001010ba080c0404006601030200000c40d00204072501e415501056024030250301081c05000103400900180f0340c09000d00d80c0e581d54020b001841044000c00c00c10120b40307000d24065503107100f868580d02d0004010780343e800200c080e4108420801c086000e00000d90400d102e41d4048120a0003c0c004001140c001e0400c025040a1000c080c070400020581c01c201c41c03680b0500806500800e0549039003080c900c01030454004440c0c0c1108035900349404030a170715000504504a40d402094641071241500045400709181080c10060100c2924a01007006c6040050700d03441c0725145005841d9540303004400009451540141840c0f1000c10051016031 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 996723983 1250 996722733 996722747
    0xc050c19081e1306030c0f0c05010b03010c0e01090f0509010e15191716090b030304030507030303020a0210020322020105120a050717040503031f12030507020901050f0a0e07020a0b010b09030706020706 88
    0x1607c24186100d0100942c02c1403405400b844074440c0d4103500c3c0c02b068500240c3c015804540e1500c00ba03a80c5c42415890749010030710380403d030042550222514004110701b00c11400d1256105180401a50116680801040c14000b020740e50704440c508000c02130009003901c0da800d402101e40080145584400d600c41e07089028998081c44411984407907a4100d15242002110010f640c40700c1258461680c0303050040c02034000134142001801030324448128105503009490044604c0e007452104503401440c425a03103074031120b04a05114044c40150010708807640c481d8428480d100c0081f0700b619040340c0090100035414040d4600c04030960a03c40440d1000003a20703800140751000010301c00000c40c0403501b4680560111010407100d40703014040541c004054001d16200359421080ca136203900800503948641d000c055005142c0c00c0d41000121003908070507401c00e040740152a0f8030590b686440384070102c2600450241500000c10b9451070408000311001445c05102600b406818040020120 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 996725233 1250 996723983 996724007
    0x4030512072303072d03140103030207271503050c04090f0f03050c160e061203030613061509180b01090b0f041d06040c050c19081e1306030c 62
    0x41e02c04000503030410302450802213100d51040c840d1401200e100000a880c480607800703100040c0c10051800c0303803011302202c51070623240e0640141084d40e040101d0700e41c0100c561390031103099142c109e098400031075561040b9004101508071420100c0d04508160345041c1429003008d0203680380890f0000850243c11501664923071041d1844454030705810b04644a005030781031200507000d162041102c2d11b1201031808102d0b0310407e02c4c85031690f111000c01424001c100032a44080d001000004d000d40790a04819208880c3c0c404001401501c0b0341d41e882002c60b2020f13100e408a81d20303204c180320000c2151181c0480207080b00040c4520b000b00000200480460701c1540340101000c104244082d0711082510050035104c1c040088800080000c980000000e42d5003d019524040c03030400402c0c030510441d04146101c80c0209003c0000e081200781860104105403404138051208141c62100700e24007440001101000c3c0d40c841d080b10428a209101d258000c0044c136290031300d00e0681a4114100e1445 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 996726483 1250 996725233 996725297
    0x12040f050f210309030d05180613240e01020d0b03010506090c070b2d270316030c0804060216150e090403230409060b040b09040c050f030403051207 65
    0x269224050300c13034590b000382000012040e0500c401c119002c0064000b1960304241c1d0403c80312640c813500d01040b11038401d00c2d03020340060f0032000d4000c400381d84c1500040004000c0c070000603082c0200e800f07407800c80c0c0124006104041d02d44400140c0e034942401a40d404c0503048a4070800d5041ca0030b4801000d00c1904401002c1c00c400c040014400e00400103410700340c01c0f000d508400005039020038a00365030320850300c0c1c0496003074000124403c03242c400c140600300c4032140000d610b405050000590321381c02c40b030011000c000240ca4500700240101c0080c00050103150028110102d02e031190710205170158000c1010751408602035000640d120510840460094600301101d48490400700c0d544500c1d042682000c459481d000d03000e04100c40014002c654201404008064507520142140c0c4210300c15401008014000c8070f41078a8160b00c14000c06041f401c14500d0280405a00c0400d50030848090b0041000850303089103050040580c1503208205290030003400c1c20062829644900384200602 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 996727733 1250 996726483 996726487
    0x15110a050c2b1205060d020d1a011d2223010f0f0605031506010c03030f1802150a200102040f0602030408010c091d04231c03060602031e12040f050f21 66
    0x240720900c41e00910030030b40e6a400030252b6854010318001b105011080251000c600b200180d481212040c0d100c2e030307003d0b142d2400703166005651640203c1c84041003200d600b01281244a4445400074803940203040500d81001c146441040e520b0412508654001e50198114051021380900081890b90340301d03a007428402c81c28940380c203084006020700c2c0104000d0600d8008800d445084014001d076186100715103c104138040583c030f0591902a054904001c01c12031550400202082044501103c02c0b42c4001030400307598009560560619a0024016810005041c8400f88080c05001d08403200c9040c9000b4031031514454100426021400000c01c084140c0482c1c104102c0e5100d000e00107030506109980840500401d61322802c440380101d1091440080350300250780079008000c00c032021600907605080d111080e0303008611840030142c1da83d010802014203400402c203101400385015403c070304980340491404c18984901e500981d0710f5036001000c010038030702c4007005600d511100b01c0b00041e = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 996728983 1250 996727733 996727759
    0xf0705181003061e05012103030203091501150909090309140a0504151d0402030a0b071101110c0f0c0604050d030302042115110a050c2b1205060d02 65
    0x196a00705682004008505160b050321504800c04da40746042c031142a010022644e88601108400c43c0ca417044801c1340400071100408039000380d0240d13900c1085502506d0802550b203c20b0400c400d0240c01413041c036501a00542c0647d03a015003c00040c205207070302001044110b4134040c0028000d841801c1d00e0854034010a804c50711610880c1c40100005841800049182c0d4507030210b03c5254003c003034040c250703030303001400a0800c60380c0715002c0d64001e0081c000ca00d140703844a503240040105528140041044540801d0100b440351020042d160142192200c0d1500291130410741c2c7c401c00c09840c1c0d800941402003a540b4141190102e40003110903010b010081c1c41d007900640202ea000b02c214815400e01c5001c3c0c006208202d12105110700807081580d0740391818402160044800d260007e10103108034012140104010200c500050084603241707541d840c886180309030780c400c0140032440440740030075496400110520000030046024045454080c0118a1013044120064402e04d6030540e51 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 996730233 1250 996728983 996729001
    0x3060b06120a0b10030b0f091008030a0206161d01050904110f040305010c0f05040905060d0203010504050c011e05070f170309031c020a0c06051801020a0207080f070518 74
    0xc1d107040c086641200001e1a0580d030000003810101e00f0140a81c41100c102d5240034400d2041e0494540001c050700c1902103900700340304007054014150b40d00021021070205030f0400810180c01216002e41c01010385240102e10aa0324000840307250307041c443d480c40301d0000c0d4046031403800e00e6802c080c0381040d1540754900c0090040c0c15004002100010002070100580506000800650740030b03500a010700b500c808800c44007503d0201c0c140b40050800e020602039812160011500030751b005040d04070b0168960000303800c642e0180c8003100c0661040c0c0c003801a075600b1803142041c02c0711100005103100b064050240c1148039003c1c0c01000703205a03100c0601049440c0402200b08288025469280d141c0051000e640364007407040c04c00c1c20040a4140e00c0118098000c444941020766540e00b4442010707601c420192a028103003851f5510070a98400440d0024400307800d1080a030f034002d0001500c3c007007146042403031900040081c2c1e004614107000c5904d0b10b0240020004010794100b145544003054 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 996731483 1250 996730233 996730237
    0x20412060b03030f21060312030f09032523030a030906060e18071e060c060902031213120206090904050a0f030f0f020a110d1e0b010e090f030403060b06 67
    0x101c070056100110300c484500d1484050081100417190920606445070000c0595502100202ca05c04201c1000002c0461103034a1030346070010075405c00c80e41070104000c11a0919440340461400c41c2400354000010305c2402080e9600440145030102c044201b1500080c1d00c3e849504514401d064480f4008020080103620a00080c842c0040d10b0741c503030038401464110f442d140c0b803054010b403203040d41c00700e04551443c140046e040005003280070071600d0303c0070554240070340000c15600303582d41d051003502503107041c024070a150a00804850303a4200c84280c294a410154120030903210741c0154070001038440302c0854011910840f4081c0850b07465183c410303c0c1191f40b100c005c0503112400501c4080503040f60501c02140f03a1500c4508100b00b140b11b00300c0e1754428140025120b01c64203002c0701c03814208804100c400c140203034112296540906c441070b4280b143d180c0c0855035440f95400402c124590315001c107400007440750145c50020490350006a076801180400382055030781e180030100642d80c00d03003 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 996732733 1250 996731483 996731497
    0x303031302010c080a09030212030301060206060d0305120c0a0215130b040c0807180608010c020706030c05090301020301170708030703090911070b130b01140a031e0c0b0a12020412060b0303 83
    0x20560341da0028031758001e20300c446038031049015120002c45080c1084010060741e0581c0c80c41ea000b0034450380c8036802c1108a441561041e014002c0410160300c601001c0310381c4501c0ba11417030510503510f0000c007100900c1c01d00d440e6071481c110322840d03040c4064481c005c08110529074002050110b181c850f0305101b0050fa0150f1701c0054144220003002941d04010070041080300c00c81e01c0304004a69452058900b070b51096448400140c00141d02404035074000d40c0509001c0e08a03140103820078046a0220b03003243d00a030421211001081c016010640c0c0400400001d0030701d8a0145041404940c1e0140607503096001c3c4041d481d0701c511445209584003070584103031076001305018026081c42202989a00c0f9485000c0c0e80c0714004000210342d02000340328259480382d0217001000500c0c55034440004803980c0860070745013404200c5101000c562080c612401800c201071009549100420010700582c4907241494110703030052004021011401c82440c1140d600094081400080c41c0700080c11841449 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 996733983 1250 996732733 996732743
    0xe01120317090a06140103080702121614030d02030a082212050c1e19020d170408010501210807020f04020f040602060a0504051c0903020405040809041a0303031302010c 74
    0x708000c40c0c8035001450140c5207000e840e040210b14101d01844c90503000901000d42040c0f8100200001814100c04160307500050006807030404450503145078200c5082e85c002c54041c40340301501d5820385800e200018001800d4002949080715561001c0e0020000425090300c00c0c00300425003516040b00307502003030315540c481c0200b034034210110409840e40d0001401d00100d071080300010004080c01c200398900c2030041d00000c04500005041018000c00ca0907412a0042400d0012000084040441c1e001c0581e4205116444904001e01142111416441024100d032040e0480c00400c403039440b0006070341e421998a507078801e400d00105c1c00413131010600f6904075100055480e007035030954010700203841180d030a6507001d0315006503402c1541c0043d80d0203019504400c0e0054220301000c203454a038200c0d00c0c10300110707940e130301d4000a080316000c034ec058a514070002000b0003185000d00c038041120041c8055a0551054400070079507900000302000d1380950f11031b038a1ba080d03a000c0c41c801c5054641c04 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 996735233 1250 996733983 996734027
    0xa05030426010501180905010b060d05040311010b090a0507030e1c090603061a07052103040204050f0403021c031d0c03070b040b0706180f0303050f0601090e011203 72
    0x20340306000346440321101c031126003040032104650114060240318100d561400300031070006050010b02005140c030350411a00b03507581d10134142c4161544000345c01c1c20700d5000b500180c640761a080181001c5050800741c1e1184c0d00d020b002500c076607119040e01d82c00111060300004c2c04c0c0e80d0600b05800074502d40c034800c0e007513104040400d903200480c450305071050b021583e40d0080b01aa9184150280d50301030240c0898150781480c0750510303941c1c1e0707406400790070b003d20200c81ca50090640340c42c00179464441c0f04120300030b0000070041582050700440f6081840c2c90348862031031409840080d110b0f101302c1c0b015a0207403d40d81035404070364481e03001420762100264440c071550010007800340d41d50301c0e00540385000e40600200000c401d4006029242280c550b40704281c40d2049581e100c80081c12034200002485034500c014501042080b2406124144251000141c5080c211149000800020241410402d08034018005138000c8200701341191b00316001c05504c01c800c1c1c03400341d410946401e0503000413044 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 996736483 1250 996735233 996735239
    0x7080f21190e040f38030604120e060703032304020f0415050a2d4509060b100e1203090405070206160203191209021203120f0112020907020a050304 65
    0xd05c0070168040b260402c80c41103d401c1c0d0303c409884a85500c6041d54160002030000f00030400c04100440341c4034040c5001007008800f94000f03609608204402c1c3e0019135244800034102c40810610007010740c180c8144180c0d881e00c1d60002d228121000350782e60095848600314031400040c444588050320740100200781c590313200c0040d00e1004e0f0649001207241300b003254400c0000041050702000780c81103140d0209602d0019502d03803401c030092003007403041b03c2c452011440c12844c25414071640d22485490100b0001414103018041da10300041a0384a000313900e09820001c0d81000ac2d2903d000d4061354482d01c81d40300580d8407821801607414094100c1d04260802102ca9400329403507100f0110210140c6000390410003c0340d503402404a424240f000a0900c0c10102d4018040741c0c60520b500400031038980c50560100d03d14620409a080c40c1c0d900110703154024800c5405419403100303205200700c40541c500422032050061120020f800303a502c5001141d8114802d01803800115084001c881c0d039159 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 996737733 1250 996736483 996736511
    0x5090115110c061801021c0c08210a0b040f0501051c230307170a0504180e10020a0e0111070303050322030c0210181707080f21190e040f 60
    0x101000b20314014010680220340c7d284c5a00803821a40d01c0e660b80b40c0000c440107030340b0322081c0e0f4000c00b40c01e400c4d0b400329403440c0f0084060031680b500c2140a6000070942490001c20302c03080c0c2d295808462031150134039005122a071144e003100801e400155402e00c5403a82c2505000c40c000b0281401c00070517a2121642d43c40e084000030003880e1a034400c0b01c120004122071281840c40780202040c170ba00107082000300f0000c0d16a54031007110702d203e00702800120042041d04007850200010400c903c0f080d0041050900550014002c202e0820282032034140240c1254202d5101c03c07150000500381300010010500c903114504c0f20340c4a204542c42d2048a0300c00381c1c03c003d0700340c0c0e404207001c070710681550003902c0c4100c2c03084000c1060103904551a404280c148610101d801a1841c05030f03c05200d08900010309401c04c000300340d9040c5d00c5c0300190800d1469103404c100c00d0311079010a846030b070707504212203203081c40d9034500e100b000718241c6400031031400440001006003400b040c2d001181d80c108017860740c03141c2d = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 996738983 1250 996737733 996737767
    0x110c15120c030907060203041401081e091605040b0105120403050708070b040606060c0f17160c050a0b0a0207140a05060403121e0903021203130609030c05090115110c06 74
    0x510541125482c4c3e5030b1300804c80c1c0e6031186024020741c05143c01180309042d40101c41a80c1c00000e0380201c07002040c400c001c14903400200729039000140d440700110b001d0145805020b540a0001920203005a50007074001030175a1007010926a80354401c0e45c00136060504c80c100f91004e099200c80c003d40e568559007000d502c00c07101501c0a5840c5450710303000050031400341070300402c0305a010010441d0550315403210705064404400c500d4006004001c0b5035149014002102c0c59074ac071803100f0182c481d0800082c0a415502600408100c580822550f0318a03034001844100311a450749040d030300300c4005404240f0b000880d511a52700101d01040100801079019401c1e40c03140150742d5070940c0301c100e0315586005c21001401010100f18541401d201500300480caa40504294804036407800400c24111140180c2c5a8003010004030a00d9080c400c00c0b9850115500502088881c1500b075414148520b0403011021940410300070600c5010325510b406101c1450701d004010115920751404890880d004 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 996740233 1250 996738983 996738991
    0xf1f0e18031c060e01120803040c05040f090b101d07030b0307121101090f050105072a150507030e010309140a0c181401140117190c110c15120c03 64
    0x1581c181000410f184c0c030800b04060403039031849141d00714841c40e510759010b29031002e031080c1d500e01d0300c0440206480d1924041d10706010702d03100d40040d0070844c1e4140300e074400d1805040c1a800d0081804104406441028178100c240643c0c60224281e44030800180d0080a000346042c0c0c05020b100300004a1107008895a1159405120b042052a5420004490070400c5024040c0c241045040600041d44914040c0072207502c01c400078142c40d00d0002c0c000d42d000b4050394072444198001c01d0244000c0c02c4e16206a00d40001c2d0781043c5081c0805035601426040381c84a00c241051781e20b104035800e0000a5901c1c0200c0300780801981c0840745541001c800d011010300814400400070001c100c841c4045206040710012603101062603079003840240c1142c0100070380001c8c10011000081d4442140102c00680582c3c2d80d902170030300348506d5603502400d4541e0140e20340b060045041a20b80301d004040b8001c50f03003410032074400300c440d26282082500d0303018408440c010013003210100000099480025805 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 996741483 1250 996740233 996740287
    0x2060a170c07061404030c030f05070c14010e03060c03010e06010504090f0c020f071d040206040e010b09100504051008070908030a02160e041e02030c09040303050f1f0e1803 76
    0x4113603000c91000c52580703801d49004001071281c508003030110b4400d108a000e07462003403400515003851900c550380d813003083da080064111123202800d40d5940c0c0001c0c8280d0802c0064001d040e007032502c11074083c5203000505c60380707880706d0941000812680c4104210b034003400c4c5800c003c0100b207012611210050420810641c0548100e00d0342c0309980340002010411036070044814920700e56010000030100001030022a0891400e00010890b2034941007406d0181020056141d1161050010080e20410142240c42401010042803010380c891041d400c01c15100381c01c0c1b0f01d03819110403400312075140040d4000c507007500001c5020103a059010540d100345c0084400d42c07202c0d1075150350304a085100141e40060800308200030b203803092241080f04811483c00202520008886040480e000a00890b012070000350f0321001c124050560300c40040d00084840408010b522043c0d10203182100d690180e56151106480011861190710040c000060150400c0c0e0742c40d074000e00e1803124181d1901e441c1c540 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 996742733 1250 996741483 996741491
    0x1e06020d0e0d022e1d03130b070b04110114031e06030d21060b1201030303140601081803090a060c0506071e111014060307051c02060a170c0706 63
    0x805100055683c030010f000362414854245140a80f828101030013291401603445402d5a4041460150502c00b004d03860405156200103c1944119000d42a00580d004001c00d0000b807000c129140015940b156101e2410340800c0f00c0c1e81c0050f18280b00d21281c9402104c400130030400100070301291102c0043c0d2101017401503486610030942c903105c03042c82c1180010243c482d0182100000e110075140c404009200042d850b440c2c58003441280d1080c000203020242040c010000c26601d8411a2400301e41c504091000303060440c002000104080c15411203d0080510000c41000600172281180001841d5085c801d0352450081c2c00c4000321a825180d03802158001a610344c042d84401c00485e102034030b01203802085440540e50010000c00c1c50441d842511a02219000b0520608040d0060841411030307902c0c18508251910005801c010b000e181810075101c52801210782103d45c40c0da040f11416103034080200c003141e070034800c0303200103000c41c0c18401404604a400740051001a000f010144 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 996743983 1250 996742733 996742753
    0x321020d0c05190f0507051b01090b07020108010e072109050d0503010e010513020403061805010b03010c051c090b0412120902060d0507090506042403060308071e06020d0e 75
    0x6070b000d005111980344000c04200e2585120380c410f40c078020b080b2646082983c00c00301c4030385806150054844010000d0310f05500500840d40c0c10102820050915012903480c006a650009100102c1880786134200e05c083c0c804a004c8500904032842c1c40c0340c411682803030650f54600640054180340c501983c260080a141000461192080f070703040e60300f406030b83c0a10303034600300030f1185985042e110015110f43c20b000100c001800c0e0300505585c40692040b90100282505000d821110400074661007a0f14254a4042454101d01070fa44c0c9066549103c610845246e2881009400164801800515a203040008226101414101180003642d48810240c042e541c904200c1c3ca5051001c1c0d8001014091a0688615030b000740354008840c0c5002d218080e511802300f0105d0f00590412320706c4900381e0710200e0000d50202c81090041c02685020300c25246982c03200c500300e1180040250190303054542013106903081c043d2140382c0a5000d202190340324001c1010200408820400441d1401aa03c0388 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 996745233 1250 996743983 996743987
    0x90406060908070b180d03020607090e33031606080a05040305030c18120a02281205071508180c15090a03081b060a0606020c0603040321020d0c 63
    0x12200782c2d02848010122a41807118881443e0840701c9a840d280f4424502981036803100d00518484134829001401c041c1011031010b400d0704440c0e00314141840743e1004100d105003030301031a00c400c2010f0128030302c1c009c0520b0f940c00c00d92400c100e070025014441d031103c4a01d80c0020b41c80000849280e950380304a503031900343c040c0068400903240500016818404110021007a400809942020614565114144a0126001640031389809060b600005190010340c1040e07200101c00d0580514442e0b406140600c80001042e407074000c1c4103612581c544807004015040210b00041e0500c00500440032080d05d00041200c02c3c200d07076540c011112280807083c1000000b4a60403812002428510220b0281e0450013807500030320901681706c0000040000450841d1009280007800d00100045a41d42c45001d28500500900040324892800d80c041044690108a851100724200c032640d07500d40b264103080b1014401d0000c030151207178107810164011403040c1e0060070f8189814005020b219100902 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 996746483 1250 996745233 996745247
    0x80a09032709050405030909130c180b120601140405011d0c0408012c190201081906080a0c170d031518060302042d0914190611031905070311070809040606 68
    0xa000ac04122003c3c0160040d90300d905040e1810000000390030b880d28400204100300c02c200a440c903070010300040c00080e851009000c0f02080503541030109514210b0000310324598980ca10014841c0300d030111f0289030007142113600508000c802840081078401d0040380544c2580d0480c1c80d8000800c0d00003085910115949269070030502c80c150000d0ba1680045d120040010103803046410818a080a81c00451044102404070030700100b03010402c078a45110888586e4000005074600c0a90702800c2c20400640070384032075824503000ca98489218070301200000b507900000564030354090000d415010319406101164000c0f601405a42e42056140c40b081a40800007401c0658449108411012540000c45440d1050544a030407007032102c5280e08082200b4801131403850441c0d140e106020443c010301c0d420032506440b1070f00d9400c00c24a102d0b800344840d04410103c41d1100c0000f0445800380e4020a80e09000305000c82c1d46600a14050140ba80030b2050b039845280340001c08200700d846506 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 996747733 1250 996746483 996746521
    0x6100605030601110c04020c0c1c02030d11070909030e030d0f09060c1703130b0c0909160e030f01021c050c090904060204210201080a09032709050405030909 69
    0x64541c510b40700d020044604110782401c82c0c82c03520940c0809102a2291b02c0188220410070002d001411428410043c01560325450400080017800103040982d13004100e0600440990800e4240200000001d43c2000c8055200150883c90700700030340d05254100a00000e0143d04406440c02070001040c10384604545140318030010782d03000024405903006031300d0890201e00440744445480c8018600044542c0b041340c1d5420f03120800507030401040350701c1882c2c0b43c1007444e034140d06003007001800c041020b03000c0c0203100c1e0000034024460200c03454021401002c135440040c013521300d80410b04615071301035031050369201e1640d0581080b00c80500000c0c81214002c0850300074607072606281500304802d800e030240003a02d030154200310018041506002c1c550049411b4100d050040358140005405d9100c0141840d08090070f240003840001c0d400400e81000121f07050303105101a982c2081a41050314607080078003c02c0c500380a006c2401030000207000381c0402102c2205280c1d666001c4044e0740c441c000 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 996748983 1250 996747733 996747737
    0x30932040e0c1918020901090b03010e07052107050a1b0b0103030c080c0f1605030a03090306022d030619030b010b030c0f1b0106050402040e0f0601020f0604050c0102061006 76
    0x301440b140e034600301c43e880c83c24000c00b00e600d01c00c0d680c9075003ca4a100c0c100e2914503102542c00514000e8950308003100c04c0041c0405614a821503140c2440c20ba006c0c50001d0602c0304200d80003e580f5400582108040f4548120109224007032400742e0303019019500c4000320101061040f00c44000c60344616a481c549503074850900901e40e460340e98242c8000002803c119480c00307082c4100000000100401000303200006c0003003210740000b4860313401406140d0403050090f04034031140404280c2001d5003408985e8410801a50744005814070a00c0c2c0d2191442e046400425081c940101d650708000345d4064001110070944180036010703400400540b92000502c0904039800400865441d00007550744202d28042d0149008600c60444d4000c0d800300800c4000d41d400b081900c900720b02c09108100141078155802c5140a04000c0e03045041c02c0018840d40b44c00d054600002d6086e4420b001c20502844444100c87c40d505182c500180c40d156080300060040c4101400114111180096003003290080d07 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 996750233 1250 996748983 996748993
    0x30503070b061206040b0708071b120909020d060f05010c0f0b09190f05010605012606030a06020316032706231005010806030c01140304030932040e 65
    0x107a036585000c960028421a0302019190440ca1604824020b440c8218441d0300f111089140144014003050406069034040085800c03007030180710410341c02e0341da440d5003140c44a071070910740c035030111005181d540103161001d002040241c62480315030000e60503903425a108a1100e61036138011a800c40074000090071001c0080c04074804100408880344d0045081401d66090000c0c140b060884a1440708044039110340b85040300091200031700c501d001416003443c0044201884c00e0514669030201e040d10f410b9255102c1c0440c11582e410007103044065440802591689844a610340c00c0c03410020902010a040410b0f246000006910035141441750700c9080820300c403d5111000148071a0340c0355450000c3c416118441840100c1860b4450354400d615902d40c14200b400040001402070500c40c00381c0e004408c6204141c0c1c100740555500e10382143c2c011f4695070b03a030600701d0321941d9a610400c0340b0b04183c0144c090810300c400c003150305030f20744051900c2c006600000f484126004608900243d03001 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 996751483 1250 996750233 996750247
    0xc05030f0c040801060312110d0917030912011b03050105060d021614011b0e03150603070b0c0a0b131511070b0a06060207080f031204030912050c120106030503 70
    0x40c040466001124206058140750729640e90764210340303140d0000d441c4580980b0944400e541e000100c42e007c000010080c06182c80304820151120200d4040e6074500100b505450580d00810401e960a00c0c000410b2600500100800740d4020804c42030803c80e4007520b10800542c1d00d01a0107100d040710300103402180740c4407100d02c0c07500080d04003880c0c12a0710400000710340085a5003041640901502400010300450001034805c100740100070740d5010302405460985450790003181508040040340700201d410f941e42c0000900b01a010b8120703032544107010070030b03030040c040c00200c6104491251110400d9500d03441031515505104140082035600d00d20302004580403e03810595458810200345400c0200c9a91409002e035070440c1c184418643d504020040141c2c1013010100a0042d0006003c0307180c01c171103100780c0324490804501c03100700c0514046020944200300300c3c40100586080342401e10b290385045901d81d02030342c41c020311078a031001501c1880c0c4411322032002104e6020000b0340c581300f2 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 996752733 1250 996751483 996751501
    0x160b04030f140a230304300c060c0e1003020c01060b180d02012609151905060f04021b06060406060906030b0a0f0305060708070329040f06080d02100c0503 68
    0x4a590320107031040325030001200780d81c0e00e0300000c1d40c007071441f6100101d2403640e05a464452078284980766881036004030a51285190044c00000b141c41c0c100e840850a001001d4041e54289180b892450700081c652210034030a0364941d020b090080001c0000780035095a0303510304801c500802c500c681e542e54001c010005a0315000a180b02c580c0d2040c14180d00001210341040c0c40310788c0c07028480b07084540c1079041210b0102c05001c100003485208245540d54101a4036504e40081c40b50120002796507944003140c03955079000c4102244900040c419035850160302a012440c4d40b141c20102200e01c9a1000714400e4a4030780524816100d5603603d400d600e03407802c40224090080200c184d40c22040c1081c001c1000902410b0900246000c3e030010902d03401c20110041400e10000c00c1e00b001c1518180c2a008049034450710b400c6911071804034800071443c2c0c000090000c000c001040380b81a443c2c500c1c0021907000c085400d1003210445d8003070b01c2040c00200d00000540c0e550880c4440014410000079041030 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 996753983 1250 996752733 996752747
    0x6041e03080a0c030b0a06020a0302160b27040207080405040b10021f06091506090e041211101a120a08040905090712060b27010b090402160b04030f140a 67
    0x2469160201780417295002081c0e15050541115005070024140013051580400c0144003c2603010700380c0254074607104605d045402149072600c51616060080d6500007100c2c500c1841c500301c02003046503607001510301030724207511a1003114012030500c14500918079000c454001d504805030080d000d104071100d40c2d9510541c0891044190941c0c894000c10041503a1107072000d0030a91079244203000303052035000b816800465003c5042c80302c034141080001811a4ee0340140000342d401e0940d4a10381800e0802c1c28264907003201003041d0b14210401402c9017940d500c0720007462090795107043d42c003c9400010340f28002d000000e410803804000400c49805641d03c0b05600c08041d40036580825222042e1500310005180b0a42c0c1254603248114418507060984030400002500191070300071035910884c15103c0140304401c0031000104800d90181c8032070301180c0411002c0c5154000050b035515204041c06c00564083d000104a0003540840c0f078010000100c1489072850040c1c103140050a08490b41 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 996755233 1250 996753983 996754001
    0xe0c121e07122318160317070f1101120b06041e0b0f0c1c0e040b040f0e07080d0306030b1603060905011814010b180604030b040506041e03080a 63
    0x450340c4a600301d001140716084407401000c0c48803003c820b424809000e201d03800300041055440d410400f51804441a070402840841e45d02100c50005800c100807401c5c03540c00b0724800607024129080915040040c540980b464070b10098960381113000b122620401150000c0d8243c50704500f040205001e0b0f000e81c40c051505071000108020802074a418040b40c480c0c2051046e6003075440089500001201c05002c0c10010319191a0b0519001c0c0b86076030b0040c91364640d080c0490041f03540386035100b41501c96400c28804440c1440092154040c42150140e5560780d0348a840780c0d170300602c0d10402e00c05101c0d00a0b042141e0b0004a8101d507525601c000c008000350212000091560b11400040c2200440c000c090007041d02d90744031442e58001c9a00710040d00d0045c82c0200e011000c0f0340c01401940c082070182d4007018506407281c0008681c2c0004980317280f05541000d401040d40c1d0342004108a030000b41103206e01d10407065045243c940425410320703a406100001d011a0340800058180e4210303074001c2d20700e = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 996756483 1250 996755233 996755267
    0x9030809120312090d020a020109091802040c0e010305010905040206401e080709020702040905190215040e1501020c0409111203030903040308070c0e0c121e07 70
    0x281071034192514541c4001c41110500f0030400c108080746000344001d5034406102d0019020322078a65000808510146c018003110664440c02d485c68030016062131401158068801c01107a01c0e800b02c06454941542801400242001c2c000700b050354080c001d40b03020300c0d4003030300003410308a14207800741e42c8200030308400d0f04a80320f180380b840710300040200a545003544440c0141c0884d04200045140814407040d821400d50010004c00c001040010754400300d0342d13059001078552000784002400b0308640c85016126100d07051904c852801601140c8810510031074a0054065000d4421401406039201c0c58032000c00c40400a0000f8200a01c0500b03260301c1403050755240c00038100040c0071555000016924240c0000d0705455605064103401c0c00c0c815101e0045003549098003c082d078900c20b40c040140345500200e42c0c1d2080140260f02e000107415200c96004041c94030690951310b54201c00301a00d00d2101440200f840c4d081500b04070301100100b40c0c0785501569034804180c411444080345030903 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 996757733 1250 996756483 996756499
    0x30307060519060f06030e0607021e0f1e0601050a12080313050102070b01031104020403020a030807020409051515010f0f300b040608010b061207090e0112050f010c09030809 76
    0x2070b07111034500c03580d0080d0070b210188030f08450400200508607506c02c0d1801409602001c1407000e0305d40c000a1034081561501c0310500343d01f020740c0d40c10341403801445481c03e4038851181407020303030221200880143e0f481c0c281280c4081c0e90701e004004040903684224812510070b12010307008070b40180700a69000c510052201c54a036400c3c0d50340c500b2a48150000d0f11404081c000510400004810100c0d400501b21340650600b800c540000700030f0705007448000c3c0310038400130701d00045440315001003a10a801000383ca12006140c03c1c407014105040340c0035410407036003a00e00d51300c560141203204e4146034541d0712107288040c80030003a1822034803002d0703400140200441703c904940c1d0150041c48040700d5524049211f290300c50502050343c0194001c0d80d6a40d0400078004e1b62038840340140c6284540c0e40e1180304d0316446211083c2c40c2030040c1c2c1c03c00389420a1110000c10b043e1030409a090103144035108a9400200e82c1003201c8c22141e148800c0c0001500d400b10400c0420f00f201c019025070000144075035 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 996758983 1250 996757733 996757771
    0x130b1003150e10021e07020d06061e0f0e07030b04060f0b09090109050108061f0302090705032e091a03012a0c02031c0e030a032a020303070605 63
    0x840c4141c0c0340c01e141d00016166020714851600600050100b0100c8800c00e40c02c102000c114000e40440301d00041d041c101d0045400710540d07a4101d40e800b483c1703800c10310800a09441e8021042c080122821216110400070030014441c4580002c000440301c0d040c0803c081130321040401c80183c2a00001e07a9441500c4041c0480e1002e0801e1240004020f18400c040d82c4030104424802d004005134014607c5070302d8200104280c44020840c142e011240724400190040007544000c0030792090380000c1e40090b050700400c0a42500000110700400300031071401c030380c0300303820a2244650031030341c0801d001c9061104003000041e0705500b001079551807a440c0d5454546072030340407a003124903d9111078408500e141d0f41000c10302003880860052511440c000f0208049a00480da0324505502c5c503a038004154900f81d42e08910800b4940000c040007810f442420400f41401070403050105c000d501c1031400ca41251600810a119030800c07190f001d00694208440e90702e848000b000010058910000344100c05 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 996760233 1250 996758983 996758993
    0x40c0e13020f030949181707060203090603041e0503070507060e060901270e150a0b040b04050906040b09091c1b080c12040314210306040c020c0618090609130b1003 72
    0x1b050107010038000c00303d003000589480724608070f1680c1c0308c0815508100143d4665803a114102c07030744150040c40f5001c0308081c202e020341ca080001c6101a18034007006c0398500030490081000c1e8100c41065071010000c0343e507401049100d200d84041075000c00c9c5041041c846440004070b21204508400404240a1b03070342d00c1c0b04000d41e5104032080c0850400b202070540c000c0c640000c04001074641803200c1403c2a0401c0005c50241c0300300d018403031180504000092060b6100d400240b03103614080e0040001d4180303400110b0361180035403003610840340c1c80304094240e2480748220305aa41b024021441c40300050340c94071140f07a441300b4004d081a0245c3c1c074420070309803800301c001c100031449202484840d07500c0d00341903414440b0400e8441d030743c0301ca00782040c1d14141da42003d9a1300108200c0e40055644a404403d030714140340000c280780c02c01c1e03011996100d0156034480b12000f07403806980e85402d955034407041020406085542c108003816100485c17000c14480d4142c154071149030400b07031050070380f40e481d2 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 996761483 1250 996760233 996760277
    0x806130207050c0a0e07090905100f03050a06060e150405040c0f0303080915070f030f0603052a0402090922081308010b040c0e13020f030949 62
    0x66949601c80f100405140c02c0c4001540000c0c2a400d00e11004e904101c00c00900c01c6a05208031045641c4030070100e4002d500c0807160b4801072414204000c0f11070354901d0f01d940c56100e5054103a40031407412400041d02110304840a01c9012507440b0742c469480c4070b9041000405001e007080c2c41c04491908085045c0c9508030a00340514040d4544e1455450040b00242c6090f4101c94000380260b031800600c400f0f25041100c0b2404461681004a4003018003d900782c0144499030010300644600c0b0011100d0403203440341d500650102c054034801c850f229906010581c0720f42080c05400801c00350014080700e103030b2460a01c0484407804280380800050300c0d035081c2ca400c1a601031b5481c81c5000307000c2000410904c54182107040503a814804400700307060207400b00d030ba0a11124003031260128a44180d02c0654100c6d80c051a640003101c0e2a82032a43c60940e0b11000d40181403010100e01c0901c81314050215801041c0890090500142c110300c007804510315003050b60100d0520081c140c03140340254030740d50 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 996762589 1106 996761483 996761497
    0x1e0c0d0305070b07110f070f0302090417040e06040b01020d02121b0616020c011403010308070609060207140d050913050606040b0c060912091008061302 67
    0x18195554451407500900e1206400f0410010300e400c02d09910289140394201e4490701d0101c14405d507581c800d400342c28100d1042c84001c000515041c0122030340148201d40c003801c4000352210300c143d40d422682014200300041c81c1003010303d041c184240034015000344014a04140e030854080d49880304e240110072041c02c001542006001d07814281c0c42d500205804440181c9041c030150803400e210880f0030001802148044c86596207c2c1041e0700720701100200142c6540d00e0f694404819500500c07007242e01c2c4e82c0324a03010010502c503101610510303008036440000f0809290149081040480c1c41d042800020f0107800000d850351844941c0c81da0300d003500015640c4501000071403502996115a00c0c4900000762500c0c54040401e100d405038441c0d40032070f00c0003190030450010701d000f9002516044890703000255a0711748a0091290810005030400c000149403003401010f0340c0c0011 = true := by decide +kernel

theorem cover : BRFrame.Cov 996582733 996762589 := by
  have h0 := BRFrame.cov_init 996582733
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996582733 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996582733 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996582733 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996582733 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996582733 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996582733 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996582733 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996582733 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996582733 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996582733 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996582733 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996582733 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996582733 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996582733 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996582733 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996582733 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996582733 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996582733 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996582733 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996582733 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996582733 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996582733 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996582733 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996582733 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996582733 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996582733 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996582733 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996582733 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996582733 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996582733 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996582733 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996582733 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996582733 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996582733 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996582733 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996582733 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996582733 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996582733 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996582733 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996582733 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996582733 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996582733 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996582733 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996582733 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996582733 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996582733 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996582733 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996582733 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996582733 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996582733 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996582733 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996582733 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996582733 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996582733 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996582733 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996582733 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996582733 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996582733 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996582733 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996582733 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996582733 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996582733 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996582733 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996582733 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996582733 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996582733 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996582733 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996582733 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996582733 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996582733 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996582733 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996582733 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996582733 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996582733 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996582733 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996582733 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996582733 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996582733 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996582733 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996582733 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996582733 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996582733 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996582733 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996582733 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996582733 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996582733 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996582733 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996582733 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996582733 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996582733 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996582733 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996582733 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996582733 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996582733 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996582733 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996582733 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996582733 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996582733 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996582733 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996582733 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996582733 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996582733 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996582733 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996582733 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996582733 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996582733 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996582733 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996582733 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996582733 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996582733 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996582733 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996582733 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996582733 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996582733 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996582733 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996582733 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996582733 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996582733 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996582733 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996582733 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996582733 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996582733 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996582733 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996582733 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996582733 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996582733 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996582733 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996582733 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996582733 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996582733 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996582733 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996582733 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996582733 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996582733 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996582733 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996582733 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996582733 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996582733 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996582733 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996582733 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996582733 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996582733 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996582733 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996582733 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 996582733 ≤ n) (h2 : n < 996762589) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
