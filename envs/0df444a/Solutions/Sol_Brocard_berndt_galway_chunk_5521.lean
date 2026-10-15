-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5521
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T16:08:13.833984+00:00
-- url     : https://prove2.me/submissions/299bb215-f471-439d-a210-4d4a01de65ce

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 992805755 ≤ n < 992985611 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 992807005 1250 992805755 992805791
    0x4020607110a0e061f0f1211040f080c01020f0d031806020d140f07020307060225030c0c2112120c030b0901120302070e070c05071202030c0a05090a 65
    0x40455030000800100252a0000060040c092201180e50450078078014103500c0c81c8001c404481e44c0450310b012000c101d00c50047c6001812110081c101007401114250307a04590382c4150800b00142600c50307010301505104001165401c1400e0000300201030400c49600d0340e902210b5884020151203910401c2121030302e40c543c99220b5401981035403109201140d54001c0c017103880031080c0c22680c0c0e0300001c00200c90001c5050080000307030091441c01090f40c0702c0c03501960103a501c3c0c109051649030071688990008903130301150307070080d0341e6800c10740b03181d00d40322042d81341650100002c104010102d607000103030601040e0744694001c80641d40041c10500580b007000407001c0e80402146010146916180c064014882e5014100da08145a0b030b20780340111070080034158080d0050740845000d1041d400f0244c0c05d503400210720301b4940d09104c4184d0b601407400c101340d004980080060b509960031400c0070030481d1b0f16400c00b290300c0c107500380c00c000104540030070051852a60580710300f020110101c0c884 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 992808255 1250 992807005 992807033
    0x4051009090504110928020c070302030a0f1a090c060a0215040305190c1a0916060201021e09012c1306030308061008070c14010e060906061804020607 66
    0x1400502c410318160404c1d00582c2c2280078041e0261200c1030014100700150801c48048004800c240803810001c440700a00a411141c005e030410f1041c10381c08400359404206208104c0e114403c1d0703454000d0303a4a4071600030f80d100c4a8104461062a0910542410110b1a103525400c10342d5025180c1042000880c901007062800902001d0790310709020505900c0b170000c041e01c1480758880d40522140c25805c0351150314200c80507060380314582209034060890142170303400008440c00c951025001003464403480c11550700c1900943e42c0000d450704203076200245007487c001111849818208804006401c3c1880700e40c41540c0601e0017091000d4904011031400607520020b1f00c00c4001d64a85030310100204100d000a402050705140080e00c580b03400080040401c405554076030098680d2401901d182d1411517044645101100e00709103040c00903c00d0740728200300c000042ca203506020301e40314100103002e040f86000300080c5440700f8107441d82d103804a40081d41603442666604031401c1c8050814002 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 992809505 1250 992808255 992808269
    0x2415030c03110d1a070f020c030a110a0b0301121209140904031808030d05010503120706020703050702060c0105160504080304060e1906210b1e031c0215010806090304051009 76
    0xa2a410400030603581138040c400d114544803880140c00728481aa0703034000344901c0031751607440054004002851071000c9442c201015003003031200c40d04d400424aa0340c200360440e903100c07071a4003840780c04e003c0c0709950040c0c140d0311814441e00e41c030b042074600c0b0b520100320744205000398218004039042500c21b2044900c2040100070f820b84440d25000e18039101d0340000000c038000b0b828040085180d290100382642e500e40240c04480c41c0082e030b03a503100060341142205600b400003e0100030301586a01d0002c00c609001400001351510302000b1800000500e0340309201084420300090115180c000101d400b07442e4141840200804558005000e40c9141002080c182d0b648031310006100f07400605001ea040d04100071913000c203850100d000c0407141c6c00b4251a0b44050341d1344400705110704146081140c4440179054403094001000380d5103100d118076601c03900592104490041105070400407a01404d83c8102500d114100718a03510b94134016030148a208080158095449601442d03001c4020044 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 992810755 1250 992809505 992809523
    0x4090f02040c0e030609191410091410090b1f0f03050303070906020c010c02040b0402070b090c030f0a150c020a06090506010e0c0a080109050c072415030c03110d 71
    0x346001840040c40c05030f40c034020311409010880364071011030201d00d60303040101ca140d541c103040e80720303017a1a180c0e0481c4490940228588619000d0f058020f404d00c15014405000a020901030694902208000040d80c4213147c6032a400c005441004416003041c02e9011003c8421341e4034048a102200a51000503401000c241c000200314011018510800507620b41094035603941030166110050b056a0340d00142400351042c005180603400b0568649000e4030041c2400c910b961490068a0281d6031820603a1104409854910301000398074202c02081d40600040c0b205a61450382c1c030942d84282521064841c804580254800c00980300401d0b0032540a001c407141c1410101c4d103138030080c0600ca00c010023150003d01c40c001c1d1002118500326059540e84007a80c43e081912004000c040c003034505903c4d0410103400861804030003184000f04410340381207000d2084900c082242c1c00f214506c1140402a90100040f44d49000f41000b20707608809103e826a443c0d00006442103440e5000031301c6848 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 992812005 1250 992810755 992810771
    0x801051603050603060f04020603180609070f0506090d08210a05162d09090207060204090506041b03110d0507080601110f0c060c030d021c181104090f0204 68
    0x190340000355a6020881d1020005500e8240906494510840d05000742d20b0024010400504003840110780c850304070410305071071a0113004020300700103081e00c5191042c1c2c0080b0050201070501c400e000024082110018034040840020500482d00f10300050a24400070540d5099107010541520501010500c00c0079649801a80c0800411040e69050b84640504452040140c0150314404000c019081940040c90218040c1a1410000b03111842084900e082c001030504981c00900000b40c4102400768466081c44c05035400c550000341094455410805810045565940c01c500052038a2a02140c9940c8041a0030001d1180b440115049858041044911503215070814040c00d000d0b40e03100c043c04c10b0383ca00c090f40c4014405071515183c111010340e000e9458810300500c048800181036a051a103a0390071401244c0141154200342407103154501400541446402c0303001d0300421502c1081c1d40f0300d03140c00204132030a42c44507000f10f50390f42c0080180020702010000c0726074000c00074004a2 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 992813255 1250 992812005 992812021
    0x30f060e010b12090c010512043008100302010507200a0b0309010c0804081918152006040308070e09040c061403090c190f0902041809032007080105 65
    0xa844840b0020f40d0210910200ba80342d24007140a5140880594a00d0b04084081e10310428500c1c01800403190131b502e00461041101c501545500c5225040c800036600c1c6034891400f811468004003400c11100f40f400c41840140e8008064a420680028000c1743c2d454005580b1011078140c10100c81c1e12200d0480c00040d41407040d0000d51003441880021b1000c0a030300003080e61079060a483c000c00000c018004d54070050003a500320b0010155a14160701c0304400e40d00600340703074206900180c0c0d8200d2041b00300700c040c13500318050280188030150038003c0100403040f244d8941202070030040030090100301140c00c0030300c03a8903081489000100802d079142041d00c3c00005810300c905c6101c0120344000a41c109100403101a00d202e070403840040c040e0003405c5810000c85104882004442c620340301c0303010600d5945803800001400c0d00c1400180d44070305003074407009a130001c544941034050034034410400181c1c3c0300403210103503618003070204126066505a9803e0680607007000c1c44541c600801c000442c = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 992814505 1250 992813255 992813257
    0x100b07050f010e031c090201080411060904021210060203070c271a010311120112020411040306050f0112150f18030302090901090b180a0f110c070f05010f030f060e010b 74
    0x102e682490105e14078080d020701000e98609040180c081500140001c01140300031408034140d400c006d158526020030300c0e00183c01ca0f0040c80e8590f0500030345008001c045c81d003004242002c1d20080c0003d600300300315a502c05050420790301860801d442d500c5101423500c13014407078200903140280024031440c0d00101d01e0345521450a04030070700090070441406008003055046501c654402d00f0410150707801c1041d03001402410320f4040f40c0080e959007200030b42c80c6205020b840558881c2d8808607003420404403007510f03003206800440c40150014001000038221a2030701500341d180300008110b441095080800608980c1d07943c41007041c003600039600301545540141b02c1c901c0308440a01c1681d80718181101118540042141c11207040303907500c10781181a85896a2000460340e0215241500250303120a86d00d210683e800003100100b0001c01c140c2082c0600b1000c2c0205980701c040007450200002c0144203c44203030010b040c0d42d0341101c0c0100c18a5001040a003405058411386540d458402e0621 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 992815755 1250 992814505 992814517
    0x90a05040515060307052209080703020106090b060711010e040e07180204050a0b0d090503130501030b030c09060f04021e03010f1509050603060619030c02070509100b07050f010e03 79
    0x755014010070305082e265401d62840c000e4202400400300d00741884140840e140040b406084034441c82e21000702c08034854003c101d02a84208002d40e00c4421078540039080d0340058002d0035030b41d410704409114548508064403030303c44d00200703514001d44100e401600c0801c2407040040e040b904211420480c86030020303c1d0011108e0b8141c102040c02c0c0207140741001c902907030240f25801404a481002000204c00c041c10240740701e0100090010b209035100b904e154400702201c5820011503408000c0f541c0c1620412032102000d4000d080300902100c0011b60000c0b00525040c4134160040c030207a0030343c4841c1d0544030300300000c4020700c0701040e410f2180141074009206021820034030120102e040030581d44110002c00080d101d00c41c200d0b0810007007041c2504010305c080c6c0c0099007440400a0355480f04140305a02c8042d03100015041c004440c000d0510b4819008180900007150510088803542d406103000c43c1c0321030307401c01d0301c0322032034a840f0f400c100d00d90409070801d40c20b000d100e1800ea40040001c1ca5 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 992817005 1250 992815755 992815763
    0x8070b09061005010507020a0b03100f09050a18020906061e03180c0a081207060f1505190b03130c080604080306040f1a04150f090b10090302030a14070302090a0504 72
    0x20710b1030340d514011540c61207260b200940000390000c0030041030500d070b009141c20171420808413000645402c01c2da00464200e5004419075501c4406000a907c0107120300740507410204244819501e10750042110340c000980a1030040400060454804404005081034209520030990356402d0100c80032460819001c8040035034041c001482d070321841e00c1401c4c0c50495120001801d010041d5580d41050740d00700079010303030b16036888113600090f205852151a091f00310050070500700c41e04000a102a074480c4105901042200d00c1040c044c0e03884100580e940480702d52003010a0060740d10300620f074040c166010000902c140c0b0140020002e803000030354030807030041d1000c0100c400302a4105007940e20400102503c040090700d1441d90341010341000748080d407c1d24410001690350304084620751480d9000d14600f65a800460356585810704502c21032600618100c81d1003411900040d480304840341d001041900c0c0710b4508011000c05014050003103400515008240c82c04c00100c0e80600780460b803c0b1 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 992818255 1250 992817005 992817031
    0x1202040b03011a1903050417030903030a060807140603060f060f0c010e030711060c0703051f15060f1206050a17060915070311130611161d0408070b0906 67
    0x83c0042c10001e03100121980c1c06104a030b400130020a400400c0702900a485071101c0c81d034100c0400c03640c1c500560040d070290b030046680349802000b020444503103410200b8650840802003040c401441c080c8581c031304088603034640d00d490b20030000b44030340c1d191081541c01c1040850005403d25204d4040e1100d541c01d0802400307807141000c41c403a02e031311403108001c01440700c039500c41c03125040c110041d2005590a204481c15140c60707807100c6161100c10034241005000c5c2990400781c40140307004020f96111401e151080260032304c28041e1000d4001404502080581701c00b0909045842e00b24a00904c800f030034800c4016107403800000c046128110701607940c4600340200c0d241e004000342c1e100d00a00003d40034a400d44540c44114042c00050407103014113070301406502c0d00106410300c803000601841e203030000c0781c6a050403414144660500c0001c0c03075098543c1c04100d03010050425a2641c41304024a035959941c901e04015107010701b4101808651300030080008840002400600440381c0070240 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 992819505 1250 992818255 992818289
    0x90f050c0112020c0a030f0c1401060f23121e07030b0121020909030c1608071d0103080d0608030a03140a0b0303070803060109054209101202040b0301 66
    0x701c050340300c0c038207120f130099000c1d00a0301c000c02d102e032040304111289841c01500c1020903855131010110750b0b00c42084036940d0f4000401a02074072a019400030f0814003201a482046400014501c0041400580c0101041c9091707600789001801025401c41405aa4042c4c40c00410701c0550b941d58280011034091245400200d13070303d135a841516251078400242035040020642c20f00101503030240403034450348414441950000001d21079010005082000c00001d1803902d07803107910700581607120000074003203002c02c1001f5805d11120a41907e4000c40c01958500c2e81e40c845100030b08141e0310042c1c1c036010104412203141d5040e00040b0007405440a0382403035840c1d50741400101d45c00e0311340442e4550f01c01c0080b0b03000141c00102855112005052000f0710036a240041240202d560b000002221160010903180800002109a00030351807205480103107400060a40d0a1040204062091200c9050154520b10070701134100003103200c9400351344407035854641d0303011504203000e401c0801d03484081c1 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 992820755 1250 992819505 992819537
    0x80f101802090f010905060d09030e060408010b03010c0305131103100f020307090602060907031b03082b050105010c080310050a080f010e0c011e0e03150f070906120b04090f050c01 79
    0x1c5c0c15510700400f11403600c0320060300d150050000b0703001102800071184620b049941c42030042e00082040200114400075040c04241c00c40c0c44e1791000030181881c00e4140609800d2207554024080e03801048542d100302002d001030b25000c00c0b01400b811117800d00c01c843c900500740b03070003031401844030b81c0301c80c590b06032a000c090740c5030072007202e41c12000c2d4410030301000840c40003035200300c50601151520020f20749036200d40da40b60388041009403140b0002045e41841c8038130b0620186c02003220070340420640d41041c0009090000481c40030341000d9020001c5000390707920440440007003400812004849642e201d925440f4540d0400c0d6072601d528004002d03040040210304410002d00c141d6400703650a0074030b048908211808a80801000103070f03421580f0580342000020451100150280da092404020240012a00600200800c001076000b04211500002c1c944812445140301094002e40200450020070034603101600d200705034024141801008212034400e600c0a81c2c940aa46014101c = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 992822005 1250 992820755 992820767
    0x8030c0d060f05011e1d130f02091518040c02010e0703050c03070b0f0d15080a0303020414042c190c090b0a030f02010e27150d03080f101802090f01 65
    0x8070050214020030409111001324146d0090441d2006282c81883c0d401035041c0b40464402051445100d5070000e01c010852404844000b015144041682e151000702c7e80340d00b051089080c00d0303500543c0c0386c82c40309034010b000b07402c44110750280808450f10a596400c0c026030310b4102d02e0302d00d4000d0045c042e02044031107841c0115400a0f004209191400301d607020704100514441d40700f800d00b901c0105010412600601907108942e01a83d0056103450501241c00451170707000d8030082c401e0f03182c800300b81c0c080019402c1502074181c00e90314004821859101c01820a010418080000820302401d803040000d10310703600c01a518182b00806c20561712000348483c1030170600024000c1c0c240980c1c0b50005600c1140b05181001001e090f508404001c2580c1c02c0150f403141064052000020080045042c540011401507007012030340103400682076100a0400701001d000d54004008103070000f0301e182c8041018030002d00b03000190800e01a5150b02010094004002c0280700700e58135480540198400c007 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 992823255 1250 992822005 992822057
    0x90a06031a040201050c0f030a090909051f110a021b0405100e07051c0207060e0c06040b0c0c030a080703140301061d030c10020a0b0618010308030c0d060f0501 70
    0x1045450070603004001000c01154000d104070304001c070400030104d071424180281003100000714025625203914007000351034540385420181446142240c020041040041c00311004e8084510001d2800440382441000c2c200e0148661101d401c0001c041046031740c006028105180040c1c0c2001c1240380c164100003c1ea074042c0d411201e10980c411092161a9818000c240c03c43d0050034041e1070306101600c0020b40106890202002e41c1c2d022810701c0a21a10b40205500040b038800a4040e0140c203000180f203c0c0901e0250481003500817810003c0d682c2c08001c0083e0529005045030100710007882e11ba8155485000120005140c2c000d020a9607030b81c40301920f0607100c041e1600c4041d101c2001c0c20f80101c01c00108000e03854850030301c0008164580b5072007496041d1459024000c4648103003032045100501800c0030303010745400079210424155822485064903802800c2075680d44552015142e01d00a490b0b24601492514200041e122080750603081219001e8940c0b00d0b02c4000961040701c40c1c442c41c = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 992824505 1250 992823255 992823263
    0xe010602100e0a0b28110405330f04030503030c1c0203011406030a0b100306090c020304030f0f02131b081e01031b03050a080306010306080d050a051c020c0c090a0603 73
    0x10f0b0022800c4041d1043c800200172100c0e099505120180c01d4005059820142c20f409980314009001e21980c2003840710620b141070703214503a80a0060180d400e41d4000110803a003038164038041920300101d0542c00440380115080012251203050655001020f64048020b200049003275456a03004840b040c000c2d64129445040c0228a09000505010240d44010050580d456617540f0b02d99860f903611850030000c01d940e51340044c5a506089240341261030044060003951300500c010800103412038801954694071000c0046540518800f25111000d40c140d0403145d642400e181d6041d01c0b8502d00c90f03104140160fa1491020b4580a0740d0b0390018402e902c0c2400c003c4000340040c00070680d44410040300e10104800c0301400d0740d0b030340c03950f50802c1c0100c0011280300d00000184000d81d80c0c140075440140080101070040d5000702c1d1800b621070310510040c501408400b19283c0740d607680310030354034260100c3e100065550307030018a407403034492400d200c0940c4149403c00c040307031070150913202d4081aa940 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 992825755 1250 992824505 992824523
    0x10e18151b070203010f090b011a07020409050c030303010801090b0106050a1b020f0d060609050f01060f08060f060c0606091b0901110f0a1202150411090a060e010602100e0a 76
    0x24000c0c041d0201c051500450003190810859035005880911400784036811896000034840c0d424540078002d400f0680c481681861101c005071901107600e800c60311643e90440e40081d51045d03030315199082c1640010082c0d814000070000040501c410340100000d117120306150f8015a03210302040d5541c0c040c3e0108480001c0d5004e0807d40c0200007171040b8550b15000400b040346c100f80c00c0001a07030b040e88042044603800d480c1d0104000b0354031580a4030b0380126107840007152942c10001c0050075808161a5102041034080203c0c41d0741e102c4814035004c4010250160b682c641d08030103416501c48060720024000c00c2c640c00064010346140b1090030040c402051428a841c602000445a0700c2229048021501a50300748000e0a5020040081d490b0b01c500340b903441540341344030081e05000a02da8007107081c903080820880000e00a1040c6605920b0845280d0031545400603160b0040a0a0f00444d200304410030011070086d4001403840810206200140b21401c1d03c440440d4650708505e20040503400 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 992827005 1250 992825755 992825761
    0x1b0c032112020a091e0906060e13020403111306031707110108071407031403010e01030302060901020c07052b0b090c010309110f0d050703030c030f08090604140a0803010e1815 77
    0x1810503c1040c0c605c1802040d01c0540c60b40c941c1c1e01169640da228401061040c180220310b82082d40c44500302c8042560114209480c585400000a0240c2c44441c0b00d000041c513240c0c000e414a0740090091034002c01c1c070388002102804950143e0f030040b2015568185802d5640c40d0783c2d842001c0c040e1003018565190011070080e030b040078020383c2001808409202c601c0c00c03540410000100910300901d0004000115540745060107810001c3c041c10307141e0a07900410807a1202c030000110325048560681d600742c4d030019203c40d403200710b03000c5580004032034212504003001e220410040b0742c081c1d10400c0c182d030720140343c080040d0125610ac120040480000d552642417515003140b100b050f420016141c5400c0d000a5503440e0708000080d00114046201548403001745680541e2030480030b402400d00304442d0400500b1255a0707180104014282c4003a4800346441660610081044590149065881c2d5849407802d500e240411242814a0301d0240711400e40c000002031411858004550050f0080c2c07 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 992828255 1250 992827005 992827019
    0x1e05150103061d0d0e060c07050d20010903031d01120c08070816140904021303030210050c180409060f140105150301260c060d0504020915011b0c032112020a09 70
    0x140107010418510700a108000616032206030b02c012b4840d10654420680144080341d881d1744603404001c00b410011450020720010b40c00141c40c2005528040e038841c00c41c900900101c1c0d14414001030f0b410090709242042441c1034100382014060401a2200009075540c4c007809580340014070118800035a4410507541a03a0780c00000b0304800001900c0540b81c200c02c00504400001154802c40c0180c1c40210200751001c05e52241d0b41d00004480041884c00034207040d0420041e180034107003071059a90b4065141008203644c088050b011709a00c0034000407034100c448050001c000d2080602034526141c2c0081c22849000c100c0e4180d443d2040303501001d02550a000300c2c51020740080d46e40758460b40705129526520080a04a1101100d01c08a420714080c814402c4401003d003031910800d11851420120b83e8104082c1020031100d014040b02d040d00605180707010403042d51000c2c0a212107452200c100924a600c28581090309840360001420500500012845200704602c000b801690f0113000c12 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 992829505 1250 992828255 992828257
    0x30e100b011709070f08061e07090b09030a0219030606050301151a120a0506120705010f0f0e060f0a02060c160b2d070210091e05150103061d0d0e06 65
    0x42da020204c850702d03521594210140300c810b40000b1811341c4032500b041070031404503a05403610140550b04000754100504003500c051911b015041100030b010030b2040f40c580f81040750048094009000c0440729883d03240c1441d010107140400d940e05030a0010206250030140a990080d684e0044030804a40c509070440b13070440c401103916032844808122401d80801d180b2072243c055000c001000980342405020040800e100cc44441c50070781040b02e04100c2a038100e01d0302d0040340c40c1c50034040c082550044040320030303c40411200e07070b0005010034a0019200e1034005485030b11108d8084500c0350303c8134a20383d0298003504e404411a903030500d492000180801c80d003030740c010f0900003481e8a10b890009041c4c0e0030034126400583c181c141c0104000c0b0440d0704204210758034031103250030080300c41981c81c2c910060f8001ca20707500d40e04000481c00b100b080010403030031410340107034500343c0c146503102e16040b00070b80003041c0054241d4080b00d07011481500040b401100142d0a5195258105911800c0c080740d = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 992830755 1250 992829505 992829511
    0x2012010e040c090203070315080a03080c030c090303040f0f0509040503070f1104022118060a110702030f07091a0d020103091112031b03040f060c150c030e100b0117 72
    0x1800b0801c0c2001070a5189070016500620f102c7d107000c1400840c0e00380780101c200181d80042d49987c8087c0c00400070170340044200350005d5046408603520707545d0002e9503109101c0c044142e0782602c800100058250300d506607000a88146050080401d030b520030401200d80c0b000d5401030000d0b0010461980041c0d9044809282a4403469051308290500e02c0028126000082c100b03116425103d1114442c9001210035584681100c40a44d00c0405030380345141d40b0b0f50300501d20b103e010343e0340090100e1711301c121003501d0311540d00504980003915848102610744c2d40c140b040344469824640c1c1c511407140e8100f200d49841030080d0211050480d69001100500580c040581d00528818603406280c0c554180703001c0007216040042d55038900128403a5844c04d01120ac85503a50020f2006201e0b008003614540c0c02c0382c40d0703843c01d0504140c05040140700743c00180011001249048840010103805400c0444c0c0f0050760b1054400c1c007080d0441090982c0d9000c110240040e6507181c076450031200c21034030310350 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 992832005 1250 992830755 992830763
    0x70501090c0512100c120615020609240c091002031b030f090108280b01020c0a050d14010e10050910050601050d150e04030509100306081e0f0106092012010e04 70
    0x454010001c0c6c4040032510b0b01d8201001a000c11021442041c2c5c042154a400600c004010040818405c03801c1221017040c2e0b0b80d0407400003561001c20a440c0000042d030702c2e03107400144004040d581024000e56283e012007032000d00082c0d81101409050404002c0d80d25280055000c0c502d001c0743e82d0011180101c0007055100840e014131080c59104944991184201ca442400040d441c40008006403800e810859400e100c0c094510090200e40c072400e0000c4030103a03204440c0c00c07a0184040750f0314050032114059a060780706650248400f039a107034000300d0203840d42800341d51b24900002c841c3d030305607241181e84030f0204104003d00303529541c440c4d0000c04440056112100400e4450440c3c0c0c9240e00143c8003600015004a000b05084c60011464042d48005040c2008840c0c6404071032619001004814901c483c0c01814402001405011406508030788400070040181c4a60b00e445c02000700c112030707580f0010413803003222929624008440084140001c03486482e0b282c25441c90305d828000f84116 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 992833255 1250 992832005 992832017
    0x121f031106070c030804050a05060405060d09080708160c06111c05070206030a06090501240e1f0825020a080f120415112503090b070501090c0512100c 66
    0x80701160381c0c1c1c040385020b188209182c46d5140d01e44010003c0ca142c2513003059101e05001c00082126642d00c0040b261161081d200210300100c0900341450340340641d110140c01100c00041d030310702c0c5411041d4240d41540c421840c00f85101d89800048031058003030300c0c4015180c0d0015019004c9521101c2400803034150500d8154644407041d0302180c099041980c80b400001d0700c0340401e00040f00280200360140000c01b818501c43c60103841440c09904040c0c2000040c490492800d030b045880e40b40908800c04080c0b420403242140c0001c004151400803120024107080d8903088140c0c5020704050140c0038034132036000301002c101d1512084455030152030310364145001003002e59800345030300301034520442c081d00072070700800c80c2050000166581d40c01c03403050a40080206410942c611803040e80a000401c0409104046600d0151560b02e066000781d259032078041a00c80420005400590449100e0300f0406030190740c80d024800001c50301c0c00405c1040d0881056140610090b034004c80c03203c09249024 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 992834505 1250 992833255 992833267
    0x3050a090803130c12050105060a090c09030609110a082436070b03070f09030803040b10080304180e0f0c01050c0c1302071a04032003090306090102121f031106 70
    0x1003001c00c5205c0b0031506c0d80d4503001044540c0c50400b6442000780b8034154144020504200c00503ea0107080c04020482c3d65185461820b101c000702d0000850315024000120554407540700b1943c4000c08210740702c07141000c01c441d170314400040b0307421806041e0180080380f000c003030104101401c0d41c102070480c2c048034203080f001031300d000304000032401041a900c40d1540d90034031001c000e002400400661052150110701000000d10350800c80354401c1d004402c440c62034881040d4840c18030f08590114215100115011404c0c500c1c80e0b540102c46180303070408000c0d01c10121840c80d2100105048031226800c2110002c0b01c07540500c0090051440384000d03a4440c0c00000006014000d000c0d241410140c0d0100c2e1000c01c1050f6082c215940103411081840390345059540280b240d1075401c07104140d4040741e10007201540e401c0042d6403424000030300b0390765a4a06403420034000d42203080b841e0001051480450015149184040501000b88d14510301c12030458850100340c40960b0b0259805c07180070045 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 992835755 1250 992834505 992834519
    0x60e011803030f1e080109020c0a050a060501062d0309150504050d121404140304031e26030402060306010905130e0c06090a050420031603050a090803130c 68
    0x100c0e4051407107502c44403240101264000d19a12960501c501011079200c84540c01c56007100f9038504460b407034100942c0e200c0141a806082031896800101385102d400030140400c1030035000306041c1c0d02c0c80e558850500c3ca4007441803400c00010002c105074140401071b6880e401d440398022008190084003002a041191003c0c5400c5443c111020745d82504070b1080a40410b501503901040318030041400c1c0051581e414413110341c281c02a20081103161540c0c1c5100508106105440003103030020f682d8031114031100e0403829418030440c02160703000030f0f80c45551080b0440c541507600c07860b100c648290440d65103600f44607481e40050041d43c148901c42c1c1d40017401d0790b2901402a5003107516240807802c410074501091504001c1e09405110769001e000d503101035254100540c08880c401c607000b05440300070b8600041026461646042088000410802c1c8480c0c03018200c18001030380c0d501002a951000c10039001c0320389890000b4424401013001c60300d50100d1035642c522950146038041401a60707004 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 992837005 1250 992835755 992835797
    0x20c0d03020a080c0304050627120405040c1701061101140a1a0301050c09130f060b0a080906040305070b0a0b09091608060108070b0a11100506030c1801060e01 70
    0x21004000307900010003508455200701034540050040f036156081d41002c1d960781d41c580304000c0404d510091160b4000d030304000c220000684031003181040d100710500d9008000c0b404e51243c00341070700880c10300510b048030070302c190407503501103585105000441c1d007042003c5680444440241c0350381d6484100d28032451380e112036004e016441044c8005858401644c00459294032213450324402e034940b80400824200c2001201c503004001c50b01401d55001007d0094001c1180e0342004070f1300303490203402080750081e4000030000d04246446d00b21359651000c542c203554100480b40140040c1d011b100940c00246490305c080d8000c030b50346002080410f10200441c00301c3c88100c2c1c052925910150b1608517174018040c240300170b050540c015010381d60505210a0b0340f0112403203400e880c0c0000094025035103100e1a51006401003140581d000c40b51003d50800c080c0005039100c6109018156a100851814120011800d40f801c10340d507690303a02c0c1a40581d1044814029181800700d0fa407050101481e5640d = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 992838255 1250 992837005 992837023
    0x60d0b03100f1808032d34020a020409030c06050c0318070302030303181606020d090501030c0c03080901060f080102040e1e060f06121015030204030b060f04020c 71
    0x80c00000e0100d0310510100a0f40c04014034100d078109031510540114141c14216035118504c0d008000005041121030300700e5482800a4060700303540752050050500b0040311210403040079081080c01e0160140711401c4e0b28030041d43c13a42c0560b0000f03035050014102a0402c107071580c005d0500d140003018a48440e419614202c0c1d0507802840d0020801c9030120000d0041c0c034884070410000e10007e42958003183e541d10025180d42c101d40072040051018850030401120601d1000f0600e00ca40c80da01e2001a581da01c000840e0404544040402f280551003442001e44a00d855aa0381c2c0008003d07031401e962100020781911115501c0d081c0c0443e201650400080007007902d40e00041c3d8071407074070072403141030b010290180e07103040244450000ba0003480c5000c10341103181204d1250045e5203050014840e0300c585078030314031565050000c00046143c0403588100700c90740c1c000303082c9000d816200120308900ca1804020070800f80f0001041071414000ca480c0080710b4040d00052a044004a40740d10b490a90 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 992839505 1250 992838255 992838283
    0x40e0d090f0807050604030209060a05030f060402100f0c0609050313141206071413260106140d1707060204030804061713031b020402160b010510020c060d0b03 70
    0x101020403860407001c11603401081e8480140c5006030514002803560b100d2888040d120b201d586020540f160360f2038000340000c0c00002c04803508200c00c0c041c0e85440d5a13007100c041e0700c0340003102c800c00552802038007880c1002030071b82e9524600c0862665aa002446100000d5030184810b02542a426001c21000380c0070f07001c20400c00e0aa40b40c2d01c81003100341c400d04c00c0840f480d41c12080034030485580002d0340300040c2890040b102c3d10f61060082d80010414070754004007000035100e124116803000d81140c050450010b070028411541c480d01c4801e00381e081c8800d05d0b0782040f245254a4041240b112480e82140081d03200e0502d05005a02c903002681c100c0e80099801e4280004d081043c9900070f030340302d40101441005c0351400d15101007442a040c031207402c09014000610701012081028021202420340d00500454540d540041551000c0c0d00444086402448401c00882c86c0d28000d0320f0184001c41d164018413249060a061203c030350171880200000b03d880c0c0d5040501079509116000c89500d40c = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 992840755 1250 992839505 992839517
    0x807111005070501200304020d05010f1a040f0603110d110d050706090806010b040308070812150301060503120d0e070b120a0c0315030201180807030b0a0c02030301080a030806040e0d 80
    0x2d608040782141c0000c04006100060800c0130110764500c041500d5009804071901040c0456505001d809400503c8041044904c1e200f500114445450103041101000380ca08100b0481c1e901e02d00c80c1165698000502444521034007503070103180854034148207038810b041115410721100081031074921400030465964101c682c05000c802d03440a030700070043c5032140081465514104810a252181b8000581000c0c00011030005000440c0c1c102d481e8003190241142c000e10b0107404c035a200c00c041c50300141c840c2d402c20030002403131716001650000382e030400c40c610b6240100300e41010005040c0444c402a0314061428005560700120010380a200300308103501029180a40c00c01c01101da401180390245440c000c5c40b8050781c483c40c0301c1c51090320f42c2801c000040017000c1581075030501c0b5076070200c5258490303400003104100d02c0c0039080703000f240e904d0000e21401c3e440d00d005989a010034013900c1c1d240e600c2068800e000c03c0c450740090b034229034081c1000400b1074042c0c0401d400e20005d0501c01003c609 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 992842005 1250 992840755 992840767
    0x13030b0a02070501181707060b03031c1b1d040e06040503091801120b060a1502010603050705012a11060a0c030206010501030203070f0c080d0203040b0103170708070807111005 77
    0x700b0b00411440340c5c8205000042203000340d4811104040d05a103c001142c1e000c1070003c104441503000010b1000010100c030340f900d802505411042007890411114030703090040e0031500340001010003d41c0411070300c0340c644813240001e003000d150440484280d8444d03101e040118140006210f01e50040d40104041c66a0b03d081c0f506100d20302098940718050b490315500100480700d00c02d0f1024507811341c00505010326440305000591005d0181c5c0000111600f03200c142141650150f100c40100ca22601c01c2e50307a40c90380d030b100546034012000c81c55052110301ca0701c80c01e4000c0b215406030400600c00d000081040b03080f500482d2080e00110340c0d540201b138400d81003200741601003050b240180401d1806502d0f5107070900d80117202078504c400750410301004400403800c10090a094405c00c0000d1030045440340340c030f410001c0c418102888252090400c2160003440e071514401200c10a5410520542c41e02e02255a10641c0354041c54041d1004cd6907d1055021070b5904082c180d180c61030350361a035441d90 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 992843255 1250 992842005 992842013
    0x2603040b0f040308220512041a091f09090f1409060709090c091d19060e070516020a0602030a18120201050a170c070c05040e060103020613030b0a0207 66
    0x40005440c00494a8001041000107940121030544c880e001c5c0303400c80341c8407070303404040344c1113480e0507000802c42c0c0038030800010402c010394042e008a561404400f502c41e039130200300218510a0070001604203000c0b00c3c0b510b4407003841c0482c8030b80c00c00c03607860004407059a40c0101422105002c082110741c5480781c103440300903050052280d8004034544040d141509141b5000b4051400711310030444990b03155803c0e03283d294000d040905c000c001c04013410f2861015083c1072028404101d441c602e0500200c03048074058041446084143c0340140d030211002e072290032041c3c42c15080a40e10046100c20400e0030360058940c0c818a200400340358000b1904d03840c020101400c62014850410f036503504000040100780d402c640500b40075a02801c1c21a9a0502c0960464000040b1081c0340440307002d440034803007199100e00041404602820340b0401c071989070003c000a403601c0d0b548208a03a0300c094018800340ca040302c010003051100e5900d07010200e0341c03941e403000303000d600712082c0148540c0402c038035086c0 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 992844505 1250 992843255 992843273
    0x70501030605040b010e1311030c220f061b0f0302010b0418050a14010b0910080d051c270b0f010816090f06050d080c1005010b0702010507260304 64
    0x141104a80c2440210301d13240000b440201c008850342e114a6841092061811890313200c4203200f0381c030607091580c130700d042e12007403030b42d5402240401300da0358030001c0006007017a10075034103402d03a000e070b07458520881c2c60003604030b072001c00c51b400da9840f01c5c0d41c000c02da800090308900d0f1410024800d80004c1840000d5208010450311a422203130860705108400000149010034484140c1d035110b8400c062015411140600405110f4142600400c42400f408004510342c00c5031003c8402c210121800c111706a5812245801444e4042c030001425a07107072500c95119400c01e113040700b203c1e04d44418040700314549240c9424408415500c0d26440814000003071040c040a901525441e0700811b000d18182c040d800301100180b04e440e85880c2d035480c00c000c2c1c00c009070b0020070007001c0c000c10034028a510350400c0c1c0c40702c0c0c0c003118500e0b9051081c650300d5242c500050003140e049071001c200880c201456a0010b68480e4002801200c850aa01d603001007851100f100e040003584555004c6900c0c2c0c40c0c540303481303d09 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 992845755 1250 992844505 992844509
    0x1804061d1f080d030504050307020d050609010c0c0809042a090e011508010b0d18060c08060103050609011a0d02030106020a02010f1107050d0602070f03020c041a0d0318090203090705010306 83
    0x1201070322090001c9103000880d00d442040a1130000350540c1c0e581412802c50240075002944021740070280e00c10300000081c56401151204e0082000400078001514010340e12440100411001c5c4124520303894903034014280c80521842c42540e88c0c00440404510b20600340254003c00d0405005204007068104403078050511125408040e40074240b015000c044144100c5a8540d400100300d5a8241c0da038004065014401c9416071500e0b485140904c0030344504484000064100d00004000e92310034080d40380101000b401c1c0641690078012070350002440b45900c8424203408214580e100c142c1c520086000701110f9000e020814030342d00c0010140445420f5440821201c80c01542c00884003150032021654122644402d07076549140c440c01038001d442000c0c080c400304440c020103054010411150300c0c0d074210340410156400d442d0700c0e41c001152684054014013900c0784080001e000e00b0040000000c1e410b80322001507074460908050b130b171040383c2504294011841c200503e58250080340c4c0 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 992847005 1250 992845755 992845801
    0x7120908070605070c03080c10060306050105100e18060312160c05060708040605031b07050d0905030d0c1403040e3c0a091b170d03020405061804061d 66
    0x4c6420b6841c0c44005080c00680405003004800080302e00c00b55208000c140380b0050030480034082e255490805c00f000b080c00748501c078000c50183c1d20700c02c0b100d03110305840c24140c0c4c001400c203510301070743c142d680760380020040485030940305840341c007580c3d5801d0a02424903001c07114101c8e61500c225240200e078a030113030740c48a4010380d011b10981000850400595003903030040d1070595100e41e00c400859081c0090460210101c090004084041c07050205943ca0310822503220b03000043d0361a4280341c0d440c038a0140480000302500743c5030b000103800c0041c100c0d59203400011070341000d0300c50b03040744450982521056002d502e040030510b6914181009441c8030450820400c08403c1041c1c00342c1c80700c3d100149000101a03481c6000e50410074042032045400d8141040300c044031f0f40742d2441e058442801600800701388943c0c405000003c0c860700803101901c8000e03200a052594030488502d40d0012440c10651080c0c6031500441c403009400c03201c0d04540e80c81d40740c940060401458800c000c50b000000308c0 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 992848255 1250 992847005 992847007
    0x60605030f0307030c0201050d050c030a050c09010906032012041106090a0314070b0a030204080705061603110307060c030b01030b151c0e0d030b0108070c1a04020607120908070605 79
    0x5030307003000d0100654035001c1c3c040c203021001c652a0310049400e03204201544010700c0c900424846141c0440025500c5074150f11400c120548480203170140c40d00401600d1400201c0c260403e0240d035100e500030601c000c1d02600b801000f50b2414135006180c0e0080d07000b443c05070103000c0801c018010944d440c8250600e0030341e0301c5883d060340c0201080208070301d800302900132202d80c400d04640041c2000101300a00c4180d0302e42e42c071360b450004028060350291242e20b1a512940c4400b01c1d161a21a0482d0642d80200703501d03030089481d80e501600c845445009801543c00180a101c01042c0240200401020b0369900060800410300000d81202d030700184481c0510030000f44020945600401c945111070092821008510303180203900c0a03080364180da000074056410000d0209405070005120290b0980b150b5070349681d450800c989a05551901410200517894408214503605e54541e0300203002a1600340341800580300c1d0040c040c2060021400607003141c4040010710010710180010380413a00e001 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 992849505 1250 992848255 992848273
    0x309131e09080f0901020f0616200d0813050708030913020a210b1905150316230a120605150d0b1801062a150e03130b040306060503 58
    0x7804640156603d20700045000202200141e00130007610317804100d4042124102d18003542401052201180c21101091050150425480c880c044509907281d4400041400000c40c0d4411281c80c140a000c40020303100b034401643c00f1880900c4a8009842d81c8002142d80d42601c906100d5007400d01e03c1c071103941c0c61050060b1400f46034032122408016410003d0b20020210103645e02000300322200c03403594899551401c91800e41102d03032840049850456400091a800e80301d45c080610049540164000404601103407090140040442002d03075042403c3d40c1a40d4001000310640c8600708502c04180200249000c072102405a0b0000d04001d85100c03141130b52480500c18580614109000000d40729290380d68075850300503240d0043c6c1084112807400c0d5079a0b45000d040401180b0070380c03142d100c951484034a00d032203859203c610264012031020394008e03061011030080c04038021a0200d400700b0400003104c80c1c59911080c0140c0001d500c0c850350b880c554544841211600d03400140250019010 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 992850755 1250 992849505 992849513
    0x9020306040210050903031206041116030f02101d0c0307080c01111c17150603070c031404060f030e1501120309030611033403020c0309131e09 63
    0x44581042e81660410740303400108005a4050141e1800284c05101c040744180880c041c14244c0c0c0e028260a84003002200c0c1c80342c50a01151041c854600344550b500c003041400a4801d00c2220040ea245105640a0b281c000501070155050300c60082c0182d90816a0042055014010200700c1c0000310010500075240540064580154540007130600821400c800d6500c001030046134160070469891410040c81001d02401d261841074011000c1c020040004281c03c0402c1d50312000090000c2040e820350395062801c50b12680129412020444003803003024072249154050310143c070458503882c010a4601c04010101e4600b1000940f0700e900c46101c40c45854683c4030894107642d007402c00c080e071040c0e03241002d490010700f0f42e2000b0989894a0441a6040c0000700034500030482d21003d81d0200050400c40ca540008084040711821540170940100c18040c2c1d0041c503001c022070b030651b814100240e002440104407000d02c5103055171581d50100800e01c1114030642c000e400e02e0340c20080c0c800c41d525 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 992852005 1250 992850755 992850763
    0xd08070602161a071e2a0308090c0d0605090c0a0e07030e0619150e010608040c0503010e0c040f1e060317040810020304020105160c08010605120a12140c01051504090203 74
    0x112042216420b0485010250312504803143c2d0804680780b0320480c15020713a00440c6c1c481c101c080036000940903202042c1e1074040840e40104883c1c0041c140d0700e141d0042e0700d0384002070102401c0102d0511a02c480f5807020745803020081c005200110305c000c220318000d400501664003030104000250008020424404418078140d003000c18400c400088030030151007803405840b42500822160701555000082003540014900e00c210312408044001035580e10900d8240c0b6008611000550010b9441909505055008408044c80002d01081049180ba80008005016202124640d0721203c05000381702076680074085a541c1501d031a0300e010f140c14403250300e82200707040010849400001150642e881201924502c0380400c0000780072449a07e4404212541c9110f49620395080040028903460221044401500d00001520700c1c405d250ba180d0486050303514102050002e807078081c246046010004c0d00c64015000000261b41c100703405919810741104940b40e1044c0e09200c8040e005807400301d = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 992853255 1250 992852005 992852027
    0xf18120d0e030c090c0309160b040503011d0d0320120f060a030309120602040f060e030607030b06041223031210030201051b122110030c050d08070602161a07 69
    0x1207491034032601daa142150410b220943d0745074114038235900100e402d01c5903a00820444608038000c001d490490070b40d1010659954a00c1443e0703411518104041c24001e411141e84010b002c00945d003000742000780c690f5903402034410451300071403100400600702c0300104101d40100381191400725036481d60340d000740b07244801c5c01101980386c50102c080c030030050365130180c0d40509584440c0c074000c0c80e00c85074002d00c1c00c4403500780280300e4450f44011030100d41c003a00c2441c0b04d08001500c030510707090529440c80420b2400540840340c88044401201410a103800f2014070369024201656a13654000c240c4a030111000d0080b015004840c0e00400c0144c4c5c014080384c003829040300c2005104007403140111309008100101041c1e01c00001a4000303000203007121050b0120200e0201c035002d8036100ca1807907007a5143e000c010700ea0802d4000c24480381c9454141c01d600d0a01c9003414600d4801e45507a10380aa8200040550f031480d88031610b20308126403518406140d240c0010000c482e80f030700e41d82c0103001885403 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 992854505 1250 992853255 992853271
    0x12021303120c2001170f13110306040b1819061d060a020c010e06061c17040e0601030b040c090e060d051b040b060a050f18120d0e030c09 60
    0x10180c0c40c000d58000d45455182c1da0304855a84000351009850540c8901103000b41e5001400c451540292006181e210501a84404503040c0003681e4004011404007901102559888005900100141c1d410048284a139125100c800401d042400140250202c5000a80c0c0c0c039401c001d003250f105403406402c01c0100e5412440106108140e81e00800d200c00300f1046114241c00341400700013000d40070b0f030010080c2141103002080401d4840c410140c545d80f0270340c1c8203507000c0c00b00c0440103262442980003038510740c0196080c200c503031250407036401d455000764848c0c404081020301b008025a014801d46030740001c1a24284018003006400030082101409008405100380d00440c01e1030725141001141a84d00804071181c0f01c1c0c084014031074008481c0e6a0341d2050b03041050200a03414044141c0351008a10344480703052032300040d44803e0365000203c1800700c40d20050360391032003a614008050400710524000e00004403950300020f1031027502c50240c601a170b1040c4040c82440e00c920502c91b91010705 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 992855755 1250 992854505 992854523
    0x1802010e06070f170f16140f10020a02011413020a06031a101407050709060501091a0a2f0c01050c031c0b030312100501170c07050f01020f070312021303 67
    0x2501c400f0b0803c60151110007001e041012449030031144011b25903180302ca0080524000c4c80840f605800e95661000301100b076650840340000c0000700c1c241c1c000d410036004500000c61801948054980302450481d0f0b5484003c01c0c4000b10f1041d400c06083d4030b000341106180510038202c03004244000040c404c08942e000f6012130300c1c01c0040601c80c1c01c0e800e800d00848a0003903610449814210b60b01c5e40d00340a03c001d0240740a500141ca98000d1925404944030129511454080b01100e0401c030780090031514180000000c41d685010000520480d08203501d04003407480000314400d0031f2070a024401001d050090270040c682c4258000000d40750494907030403100440c020a080240045e0905426071501888003052040b1000c1e05203100c1481100aa070030880e44642e41e1004480304034843e03910300d01a8044901207843c5400da40d0043c0146401442200c1c0325510909003242240d0000114130103c0b10081244020107a00015950242844000950402004820704c0020ba0024400200b060744 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 992857005 1250 992855755 992855783
    0x5041818120e150405120a020d08071e151d03041e260609010b090420130501091d032b0f02091c0c0509191802010e06070f 54
    0x2205210814108102400c0c400d40d660280e0540066034002d4002d45108902c6c03030300440d94220b40010408142a002440e80380b80315102d840f030b815254441181507032000b11280191255500c900842d030343c00c0b40315201d19944090340000c4041100c002e0740e04549003078a078440e0b848001e0000004d0750f0a449895400c072078840381000b15016400201d602070140035040000c00300005800754100c1d0007036003000017540e0060740e90b0144a0300300c4240010f6542d00401070400300b0003003107460b03c04194070b021040c0240d140a00301c00004403481c0f20f540b13074501c4058556005200c40c1c9124052142040c924a00c83c0400b0103800d05529140e01920101140d580c03031981c900c41c03500560b545294014242035400300160440178815002943c000001540695006010440e4010038032a59140c450b8200e1418480e84d82002c00300045000080c1601c49641c12081c1311010080c1e0134031400c0082c103103203584440d81d44001c0c4000f401401d181c194030b503c200400c0c020b6001089030220345442843d0f10008800f8400 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 992858255 1250 992857005 992857007
    0x61e0a03120c0c1e1710090503070b010b03190c030e060a050103061802010210020906370e0f090c13090b0a0b0723011503061e0b18090703120504181812 67
    0x58641d080d402d172661f09040c1584141f000100c0201704090042c4080b1105a0321182030f13076010310064a01050b440c0884d241c41d8000b40c031b9940541400015440e0100301c4440308200c943c1343c01c1f015a81c035039141d80c0d46d000400411005100d101e0f42d00049058280f640d60042d0000303503d810009162482c120340006030500d00d40e039004111100c1400000215210362001c07416419101d04240c2070307000003001c07040200b00490003101c9030f000c441e40051011103002d8140060043d5900c000d004e1500310340d0180a41249440300c01d0100c00684400c0d680040c24205140401c0000e18499002c03400d071380d0742049010301103038510301c2c642484036008e6000740d01c03d50070601072801081c03444402c440750034000b82c01108002d0942c0199546c103040201207001000d80c4003030401201e48904000f60b0040320f00d003444010a40303003250241d1218020703065400e13599a83d182e68001d000f80c00e0300ca03000030750006828001ca81407041300e0b0700c483c204c0d6201003056000d1564014402c60500d48090721a4204010a0580d1 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 992859505 1250 992858255 992858263
    0xd020d110a21020706091a0901170a0e070b070c060c030c0605040312050603010606080613020904090501051801180305070204150f1d061e0a03120c0c1e17 68
    0x181d500c4844a9010031108414003442d601d034500307031401801408400550903124200300702c25254003144480c030716001c218104505510000e03805050240e07520210041c0307080d600500740304506568010561880c00c0b41c0c41030a0020740e400c021400c11050210384c0101c1c0b0003c005505441c1c850038051000c0c1e00d141410b40300b00075041e10041009050804000030184d008542d00c500795207481c401e20080d2a40420903090b04c05500a44c4005810b420006455142c1040c1c0d000c00004007601c010b01c0c1c6503400f00840e0690b410002c040d2416916242400303c1ea114003d03a0082520450000b04000013401000010500706510090100080803c030380b025981d95911089681e10480300c0807101603500c0c1d40420440d0481e04c9100304000c85404114201c681d1161042e102d078100901080002195110500040c0c3c29544c46c190052005200803000a401a14070740043e13100392103014a0822074900341e03500148580004669078201d9100907205025103421b041511740c1f4100e00460700f0340c582003107032070 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 992860755 1250 992859505 992859523
    0x408070c0305030c0102040501081320060903100b031e15041e05060702070812120a110307080f060d051c030b0a0f050907030b0a030303020a1209061b020d020d11 71
    0x4a03000000c4c0303024000405500a10440c0d100785c13502d0565595012003642c01d01e101c0c640c041c0c060070300c001d03014100d448a0038000103400300c02850b241c20030903c0c0f00400d2900c2802100c941d03190740e660300e507240e8502e010403001240c00e502050b1080c0d1882e1000d4219200c0e03c4007400c45503034109420200301082084030100c5044d18620740c500e10b400c072560406603500d440556444015004440c0040b80542c0045425144121140030151070201c05000350016a41d00400781c5010507510305da240c14803107440005602400580d40c4491007401c10710800140c9642c05846107103e0543d074000140000c00100c0c00d41e41500041c02010350003a0307440410750103411604005a40503100700360108038401c60304420030a0365415250091969070b21801a001c0350140800360b54444000071040001911039001007038020411b1070850402d80c1c0010034823054503c20141104c21503112403002100c102c4404c1c1c0240b089569100825100c4011017029442d1081d00b05210100102c00350400c032000340c100b05041e0 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 992862005 1250 992860755 992860763
    0x50312060a120f0c0b0306101407060510090606030b090c030402191502010b04020307171803190f0f140711030a0f02030f160504050a14040302160b0f030408070c03 72
    0x40d00d4042c0b464001849080820121156101c50300f001c62120388200c1035900c5070078003030301c202080131406205032581c0002003107141d25960200281e400003001030141134018a007108800c0c1e0150304040840f010740b011b44c0c0200041524043c54100c556440920307090f0000d4202a40300c0c0d0b25103460000c41c5829402048101d4401070707000001400b0501c00740081200140c1c1d0703000700900d0600000300410391000380e0f480e0340003031012170500541c0c469014010f5001041e00d807503c41c00006104166066030010440312141110802d000d060356500004d08906800311450005442004203001800060300070040300f45c5840003050460402c20000098942a04011b0458403124444c0c540307841c1005000600301d00a009480c0c04005245c00040c004200307071640152060f07540c2c2400b0620005207070042103851850380301c0c0c102d44078410090001c980640e00036070160802812400c0750b03010703d0407642d102560f151030401280003000003c0c0242c9422640c050304036075031001e0341c2c18044210502074202070 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 992863255 1250 992862005 992862029
    0x20109060921050306031209180115201f0204030204110409140f0f13060c0c03020706050901140c0708070e0a06090c0839040905090a050312060a 64
    0x2040c030048884150048901d05110000c00000640443d1580000d40d0429015405074400c3c1c0e010400c041c01403d0284409070184982404c000300c0058012401c1e0310130100e81040c401e803e800c0507400940c490007504880e000603070300070031000f0281c2d032070012880f02d4045480f403110140d2100c0d4540c044500568000340b0a0010080034401c5241c290300074400c80b1822072800002541d031140f001901c40c8a0000e01c18082d085580b06100c05230203400040018402803240701c0d141c4001281841a0f80220406076505107200c112490080c2c40c01c1032a030002424000c0c1031000c5d41e06030f070340042e40d05281070701c040d6410b4543c445e44030203500d013001e29003161090780103011000c9807035020b8840441c810281d408081c818183c0c0d450349601260890403600700010725500000e41031450000f4100d80c80c080740740c09114980800e28500103c984150001c0300980d90029007000600d449008aa4015100c54040d10441c1404c0e40e481d0380e64420614510032007104440028601d07030300d84514000a0020390b0083e = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 992864505 1250 992863255 992863271
    0xc03040b04391e120602070c030606060201020d050c031317040e092503030c0b090c060309100b04060803030115050c2b0801230d08370503010b03060102010906 70
    0x110034110140100b4901d418600c84a600418088030074004451051a904d000414603481300070295103ea881510030070307115200040081d04e144140030040116900061f10b03512060600c000fa43c40140002840743c01c00cec410300164240d14101c4143c80f0358031403508400c10b100d002c40c03020940a2984070407600e030700d40385c1003000a20b004920031090807145040000c80700d645803401090106240030160000d1040d42030a800121400a8203401c078202e0021241d8140031500018a01d50040380c0e901d202e40c00c108607290160419000d40d900f0f00c1c1c2c0803030f0309102c0d050030011065628007052058007265100c002000001038040c104a4020314140d1080d41ea8040700740a0700b9541c070b84000007200d0540d0a4109500b841c0f442205c409040e030b0007492201c60300d12194803040ea41c441014031481c0d17006843d80084400070741418014114000a226182c40940c90078000b64501440c1c00d0080040c110b040d1902420503500c4411a41520000368502d9165191070004030f00501203640000c08191603c115 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 992865755 1250 992864505 992864603
    0xa120311151f030b160527011d06120601050706112a0a153305010c0f0b0a230f010603020906070210180f0306050c03040b04 55
    0x80e140302e008070424002c0c41909100e03840760081024880542000c1c124004150b5050300d4004801d09108140f03802800e02c64030244040d0704040060040c0240341c4041d451098558010003c440d076541c001500407050441c0c0400300c1d00601c00c0c624507000e076008283c0014982ea001c0c134180c030600703034008004010000041c201c0e85059849110034000c4840045030407680c00496040040c400c2e041030018103c040c00c40d80d10b8050703016032264580b44190b200d042500d9003d4625202c1da03400c0c14030320000e0700d548900001070520032040d03401560410044122803c04904038041070341003181e00c800b114003140d50703c01a040080030301e0310203481021240b01c581d600b41d10700c58032400c0c06031204070340c08066640da9500c164100e100b6400c1342c0b48c00c90703030a0041c540980782c591708107010140d9600303140c8441100c0401c91110301d0050703000300403d04140f04092040c84814403800d58001c200006444c5182015203030748901d450000c2c401481425007081c0e135610100018120500101d01d042070b03019800c80c1400c = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 992867005 1250 992865755 992865793
    0x1b04090812040b060604030f020f0a090e070911070b0c2b090201030609050108072d06090807050a0303140706110c0c0102010b10210b130221060a120311 67
    0x1003c0e0f41c48032100022624034640b03402203d0440b980f02e824000706415550030301030007080600e40c4640c00302070f0a0740082c000c02e10b40100380303c90540c500601121420000104125110f418000300308410a200300000640301c551090381140d180f0101e16120030490214980d62260200c8416211303000d4141c80d08424039540200c400d081c400d880a1245a032584091801c0349c0e000d12440c00103500c001c0d8200a40a2401d5090202d4100b006410390b40e03002e4902e1080e60800d49608c02800104010410840b41e00c081c010100070309001c9072407501c0d907450b5880040000085102152444500251140070803489602108030300890424464072048214a0140c90700e5424070514099400c002186041d4074140c00742d0800d040003a119030031240c4800f5a00040c0c100c144448958007035a4401c050300c6543c54455030301c0c11054103a000350741e40c81030307030150711911f5000c8100003c240c1d00e01090080c15694254100180c400c0c81030740503440c18180c1811100d08030010288021707409040c611a001800e020 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 992868255 1250 992867005 992867011
    0x90602030a05090604050c0d1b0308030618070e01030209310f0203010e070c14120301060e090601120e010603080d0606020c031504030e0117070f1803051b04090812 72
    0x11908000395a5403c030074540316401100c1c01072054005208140483c41c2c0382c02405a40c4d40035800c040c01c80f03000074200c1c41044200c8d4109888401c404410800245024000ba042034100000c00200c10b0601550103031041c0070950314a41495000700e00040552240e100e203441083c249550006051180f01c1d040050b003000542422100b420a50865880c0a00e4002c882c12200605514080740d61850310403110060f9894048a10750900c54a80ea0f8020042103440d113000800511107035a54944140500050304081c2e07498010301c1420100321036070307800401c1002400b540706408540400d0f0494054010b28072070308010040c00700032844003581942a0b0084042d11011b8080b6541e01502e03100709903595a69060405c4203014010002d4006445404008204901070500c02c045c081114400c1502000c2101d000c000214511021089182d01c2441006c0a4042d203540804160440c1c645c2502c501d450041d40c141462050101102c5c0d03280c5501c0b880e800303500036070b045880d070001040f003180c006015 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 992869505 1250 992868255 992868271
    0x60d02121f06020a021c0807021302030f0f0403080420130f0c091211010e0d120e1f110a02060408070e0601180e06030a02030d030608100c17041509060203 68
    0xc0980428080e0001442004c4940c000384040e00301946542e1200024003042002c8440c10014440200143c80c3e1104901985a1540000d41c9a1130b00c0c81034000312100060924030140134034002c2c840442d40220350319401ca60448051000d0340c643d04046006c4a00d10f40846412501c840d02007054031049074405980c2030032852040c44a160403003422902040745008030304040c50040c1c96000090300c65a012400135006041c041001c00b11840080c41d444a0810700340c42964038108403620701e0354009101e5003011402c44101c52000c240354200b1403000840548441408a1031044405208081094049850b80103200319590f80e02c5a9855031140424468580c5802100c404150b00d5802112002041856061100a410718001c0001036042e0701508450b01402004500c901684040c0a034003041c950503200400c400f072078140d44524002c0c0100001d4034092074001500c0304c1c2071307121a4000b04c042440c0c070245041c1c1c4031400c3c0b800c0d00281c0c1c0845807903c00e29016a40c0c0400c14543c010707500c10080 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 992870755 1250 992869505 992869561
    0x80d020610060207062001060e15010c05100c1803081b0f0a020f400203060a092a03060501030608010e12030a0908030c04090c0518060d0212 62
    0xa40e8260102032005005080142c1c0140009018103441441d041400d69100c0e96086c002014000c2e40b2404c440341d5400c40319a240c1e180003081442d68920034a10400d000a207001c40455815450384d03900c4a95031b0981c4c2c845162603403080c092403441191007502c1300c2510380014003025541d00c4e0016060b8080103030003000001d034420382d2660200c0818a0300d102c89051000d01100d41159007003010700d8181c96091940409200000400011403c00c0e0b00302801c90066110201d12004024608614004003908500c03801001080038545880c0c410303804a50090801040b00201d49500c602031598000ea507206e11a4440c020b91640790f41600502e080303e07420b0300c1c00c10845440f150420f00b80c504241d41d006070303548a1180b05400ea49188011948440c482d04001020b580641d80e001e400d034016180300d420381c100442c043c007118569210325074110742d8a050261403c001d4004034044a04664007180c07041c03074089040300e800c184640441d040f0a10441010503280340040110140400c134605281c00216 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 992872005 1250 992870755 992870761
    0x6032a0e04081903020f0c07050f0303040501091a121608010b190f030f090305091003020c070b250f261c020706020309100b0d0c090c0315080d0206 65
    0xd451040c0310300903900808200e10b091200b0310012010568100007200b05035003001400d800d00442405410501a484040c0c80b030203240c6006c108448105076000c0b40301c1d800800c001c01c616a00007100100321602c20701c00c4202140c030800c3c144070a006400030105940d0040013000019413111541d000458220b803240c0c142c503601c801c4c4828080c02044803404020400b0420b10b068035016807000b0308070304040d280202d001c20340141400107441030318800301c0c08640c0200d094440d0346002804ca10840c1d0f02403a0850600502041c1c0030f036620054072590f032901070001851020200e0221703858800c9035024001480d01c1020345841030b46109035540a0700d50080c10300b403048403410341040d000d4a022046100d1420700402c7c0d080e48503030364a40c42104075a5582081707010000740d52800594070800318100a0b210314415803071a40309407080000840d11070540c020340c6500244c501d010980550701120000100341e1006501900240b620b0210106580c1860f10b0005079110005041003805410b5403e03208551 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 992873255 1250 992872005 992872019
    0x31e0307201603230d1403042d06050a0203090c0114070b13030806040504020603180327030708011e0c1206080f161a090105070812040204240b0d06032a 67
    0x10030b01e401c0e604005602c80342400406d00045001d542c016000d41640d45c69080c1b120b000e14840001d2841ca080404034000b603540c14050795204069210740000425071941c54000300090f120007820074042c0c14000388820240d400c400c420162081568410040c030807030b00706600b002815405100003240005c00b4940003442508090143c940900c2c0e010700440d0450300d50304000e03000c0c105240c0d0b105c42d036840240090166511414a21040046842d0108030b0720269441410304055140d0001103890307042005550056180d6580b44582c24206100041d8034800e5440c1100c800d0200d100d580d00032402c0800c0070428004c04504d200e4000d40038800c464180c0303021299100000b610b4416040c001900300d20100407001408001c120700081450325601d04031a40d038034445c05402c41d244001d46113400504220071401d191241810b84080c01140040020740140050350041090280f260480c00c0442e0b422250b050a40041d00a19800103c220b01414a6101d100c0c503c0104001d890169480a100003250 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 992874505 1250 992873255 992873263
    0x201021c020c0a0501023c030114040b0612100504140a09030c021206190e1f111611060f190c060e031e030720160323 52
    0x600d00540c40c144140424031a800d0007500000301d0709010b805200d424a001850030304c0100710340300840b21000646440e0080c1e0a800b1607034198043d000304140a520408105240280e1341111940c42407400d0001080020030007900501c1000c542005020039030a02c641458817a1901c00c40c42c24888042d010307501c0c000c02082d01c4141c4001001c030003280001ca612881d080d00010032050203402e24180e1313114141e0124800444099414903d50001e50520401d50b45e22284102605c010398410300400501069254441100384010008031a90804800780400c140d00641602441803070099158441c0303004000101003220400c85151b04800e001c03200d80d246c00c006540c0d0303c00290b0402820600c7c171148843c104174024440400340400f09450b0b40c0000c800d40154441412a00091034030303103d58000580104845e0400c142c05076806004105005602000000c0c02c02c0030081da0508150411108906010030486101e00b40464801e0203c180890800c000302ca1581c065104c0c40d005540c140001c1d25 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 992875755 1250 992874505 992874517
    0x10c0b01091a090709060c0204060e040804082116050f01112a0a080d0b0301022b0c08160315060503091002030c07020922060c1b0506040311101812020102 68
    0x2040b185c16003031212a10540b601100148054000982c3d5515244450031005c0211002c40d141e1000103400d0004e0781040c00710b50142c2c12220540c0c01c0b000a2205522824064005000b80844001c6921418003030f040000c250030020820081000c0c0020003e1b220099110300000d5030180c00d403444142c00000c00c140700c0b00200380c441018010b10f0044d541c0e044c484c1d500501581d840d07103842e032040e016195400e2005198541d201454942055620482200c4e10505007180a11040c5030a1001ea1360310f07003140702079620502e101401d40c203503508203009600030309032001c1c007010802c910a80402d00c160014010b5001e0040402281c8040f04503074085810f030306c0708036a4100c031003400344440030042c02c0503241c081d000154055040640c01c158000000002c04003481910101d8071424503400280d00604d00103280c4881c896925030495154544a603540d0014100404108016242d409035007014001410311608640090001c410414200d41c081211a001036170448100e8491a4401d8014421100 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 992877005 1250 992875755 992875757
    0xf0606020a08030f1306060b031b03090a0b1b030103110a05060c0c0d171c0e072102010203070b070c02041103090d0c02030309150408060a110711010c0b01091a0907 72
    0x102d50b55900b03811001c5030340e010785079100517040710700302c4000190180108409081600040b9403245032007a80c1c0c0d42d8a0742010050114603104009100c400c40e00401ca0301842c80d0403c80801041d00c030741c00744c6240c1e040ba07146850b99441c000710010003081004d2810420b6181d0440e1511000394403001048040c0c4a038540328042c0e40d101906801c4030307041c082400d0b6409805104902e102442001203241e8690100c400850a00d07401c1e2006030181c54036105010740d40c031000004110f17460a101441002403448032001c010003290b80011403c580c401c00864051036400007180540d420400d80c00703016400c0c040300403889a81030812085618410754103680c4039004440050030307000c00421050700e84044640c000d90b01408201704449460702c0c0c15002e0620449081001c680d03c900d0401c01c2e0b4144080a080329000c00d0829965004104900c400e0750903442e0000ca600c1810f0040800607201000d004070700912054840000280e00c45d065071000014404660240100800314000c1005a00c03040f60400 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 992878255 1250 992877005 992877007
    0x3040203060a0506100c020f0901030b0f012702030c070f0c0303021020030916180f060302060901180f03031e020727060504092a05090a110d0e010f0606020a08 70
    0x200d104c506c03a2071040001400900101d084004140c08180c81e141e09070000d480c41895641480f417020500300c0c0c8140184034000c003d800f003101010200000302c50700190426582d4000c00410003c0b0420f01c00c841c0c031603603c5072a84005240034680745610126920003500540140302d40304054407003500442d1a4035614643c441c0d40726502050812081d00064014071451003021400003112074142c98030806401510950240381c1584002c100035500c01400042200c0d007888020030041c0c450401b17a810301034090801c024541c20448034200142c0b041e070721058004003400400001d064100400354054040261038070135402c81c06070245d83e00e03540c2d403207000010010300210020b402c44100074107014000c0501e0100e101c6d0780d6000050266148064151441c0c400940c0309404c00380c28501550036155503007840d40095180c940082d004040c010050b0981a07100c0f540c0031480d100300000c0f50280c1c3c5400c0c2081051090804601d40200520b0602030119840c192001c56690300001e104542d0030b49c40041b003 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 992879505 1250 992878255 992878279
    0x10e15060307120501090515092b030c11060c0d1116170c01240e0f01050409030c2406140f041d1f050f07020a030315090e010203040203060a0506 64
    0x440340383c90340c140c1e419542c403014040014000e1048202d81c80c5400320030421070a0041031a400d01c0c1c03c112026940034180130200c0c0b54655481c020142d081a94240059030074043d4000fa200f0036180000c0030300b6170144004115141116001601c01c42c840800d04001c02c4003802224901d601c0b6107400f10380100c49429240000030b881c196041245a540740007075051103404d035502802d461644417031141d503030062580b0b4410255104020030007012240c01500135410b2a11800000d40e8041c01650301640d25503074100c080c1405a00201c0c220381c0e012408548250001001e4001501403a20411800e03042203c002a00582c500c501504404000c0ca061126100c03282080010500140080c4201d00d0300b02d0122048c0c034042c01320100944c2e011580d5070002c0e14451000003110401082154148950018060091b5000541e181d4007a45400e00041c10501c211013844880c46560094001c141008100712544e44190081c5015520a030222000b940701d4aa103501030760400c8814a42005031a408 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 992880755 1250 992879505 992879519
    0x2040501051c0b030703030302030105030c03071526011e0515090f0f090108060f01050907050f1803100905060903030105011e09180605091e0109110f0a02010e15060307 74
    0x600840c2c40342050700007503030010240c0401e0815000354029004070380d0110040003d03007018003a8450040044010f40401030600304450f842c2914081002c08001d540a51079198000a41c5840c81c44021354054203100e41c1d40700d080300f001420041c8050f80382c0260f4100014142482c0f49004520f918264800e41804100001d00403100101c01c08030368021344a6007099540d885500807903000c1d101c44005050070b4901618511240c14060340711a000e034880704c0030040707608d0b84130f801d0782c102f1407586425550310000c15244010a0111092041c0d0600980c85007001404255002421981c807650590b4515070f50003602039102c1c0801d102c0e032408103803015050a202070010f4902c0100c05c0c4e00b4103108056585412410100181c1c00b25480c09140c0d50b000180001d103800a0950f500480103201038042c80b0305175101e04000c2206211300d1104645441300517400403554400d4400e6411308000701a1915000300c0024080d042c0600740c401d0600450780070170800b103151018207110b10310140003090151300d0142 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 992882005 1250 992880755 992880787
    0xc050405060f090904031709030306030c0108041a0f01060f03020405130c17010306020319200a1704050a0b0f0112080f0405040218010311070201020c1c0b040605190204050105 77
    0x400380b00c5007042144081d0756a8485180030310700035603c0c034540300d1100800c2c940c0020b02800600340d0703610a004000c91070740c00194480e090785080c47d200c0c429480da07180c03002c0300840e11848000401161003c03c60b2249020000504031142070752200f50720044984142d003288114040c00340c00c41e5036000150307600203080d04450340d542170b40c0ca07000c07555581d8246004280d41e03003038204880785d84e000070034401d1640c000c0706010048175035004204800c4070455840029044160f00c04400700703101007850000680225002051002001910046441c0c50f01d41241c4400350740f501159404844000705d1480c0c3d20304130065040c0d0f10411500d07018880152240252a0007400100b41c8108040101080b00d84840c00a404960810502e0b40000303002e4500140544d07801d45a0300b100e00c038044c0804000b50386e00284a0b00503180c140d688460b0800e01e034a81901408035810082e080411007800c0c0300801c019584114840c00c4e05101a02c0f4540d4052070110503881644a41030001300244107403500340303034220 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 992883255 1250 992882005 992882017
    0x50f0604110c06010b090109081c0906090503060f0916031a16020a0605100902040611010606050307200f030f0c070f0e390403020316050a06051c090f11040c05040506 73
    0x4101042ca070b582e200082840d103c06444d030060403480ac030a0f4100703100e401c0340986000d00b11030f05140b8000c0742032102195a6074801424121800e070742c80e000c2001d246c000d2001040d009205e0301c251010a88908008200d00c050009441100321103200040c59062009400c01034004980d0244c1320721200e40e15803401a02000e012003a4410010b000024543e40398402400181480e8071405448031075080c81e82d0848599a002a05004040003000300d00c0350b2210b07840d0301c5640080340b0022540d500341c905a10300f2000c00003850741d5203c0018048903201c035640161201000740801c403100c05485140e0890030906c00d1280389007001c0340307002090300320307890421051000044407140d0000310401f15034004a407529407000c25480100240034000d40c01d0a1104ca103662a100541c02c5407145080003292030141c05114807810488045217160418100020817800c44811403070600c483c0f40c203800c0003140801c00940895061102071202a190f043c14018200c0d102040d448650a00d4503080c01d10255078440303 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 992884505 1250 992883255 992883257
    0x3020105130509010e04050f0f190c030605040303060510020307030f05210f15030307170a0924030f0c080114190902130501110d030c090306050f0604110c06010b0901 73
    0x241c07804074854841e220080d0003031004084c910000e08050134810708181c0309142e0418140c01140508020800c0090416500308012000c00100801f5080007d03501c055500700a100785e0419080c4818558942c126138286d80003141e8000650303124a030182da583c81200030007401305900300802c4440c240900050407480294038082101c02c045440c140d03e0b031040131038030325211001050030710046241c04c000d080100e69003035008601d00300c0701e031703d03121403035030340d0402e800341e070035000541c20603a01c0c440c0d0b90780307030061491032007071443c010094024401915039030400000007031610403d010f8032090390191584000440c2c4840e40e4503424040d440074104142c4160a030004643d21b03d50000d4141040c04400070102441c0043c3c071180300044000781102075600c400d04125120761601d00c5403c0110321221610b050f8240001c5409a07810103641c4504036900c0544003910341000c000c440141c10340201e00c2103108440c20014840b1000c2d0180c8035015807041c3c0005035210400512003c500040248840501 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 992885755 1250 992884505 992884537
    0x60a1d0105090a060b070f050606030a030503060d030e0307080d0f0e09060f03070b070f12110d0503060a2301022a090402040902040e0a0b060103020f0901050703031401060f09090603080403020105 86
    0x2034006298482c1e0006c07000310742c1286901c0c0380d401806001d001d07030354010008030b0180100a000d610020494040542064403805114061200b0180141c2c40030500c13800280503505e8407592003602d1500da481c0d864811011480c8a00d01034840d038842c002448003100000d04000c030f01e4a8030f03000d0000c41d440b0062195054440c294022400710401c0000d002014405c2000c2c0d40302c910f640c0740c01c5244104081d8000b09010300b458407669280004626100501c50700d140c0340ba100c0c2d0b110000905103020540c07159400102010b5040c4000b812008000c001400030780032200c00600c10744005400810b10806050303400c92014414070f80b8a490561103400c1400104007249088842d000142101d078403200341c0882e80e004039807200800c000320345119403242d0242001c5040c00030126071078255204c0c801c0c40d107040200001d0032000b014029070062400703c2e0845850301141d0384940340585800290368600000c110100c1c4001040c0c03075203020329000d80f6840722010741480c4c5140d0055445801400c04803800e1030b1 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 992887005 1250 992885755 992885759
    0xb151f270911040306060e27012004170102031e1510110d0f0f05070602091c120203030f040f14060408031f14042304050c040c081b030703110f03060a1d0105090a06 72
    0x52030302c04ae030170341c1c3c1c0140c40050b03540c0b4584a0740c0000504510000c1c032903a40103008000a0042458191000c1c031012400542590780f540d07407038031441600c51350442e488020304e103001ca011075004003000c50a031088803c075081c500081030251060b20100d0141d10000e1841e5980001c960320607009014064401d070009420200130000081c0e612500da214550904041c851000902a0340130b031143c0180c23400d0015500d141004180e00c80c8000f0014000340201c0b01e068010300803c401d81e50035541540c080300c1030742c11034140b601d8420410b90041e80c800d40380d251b90018444564a070602c0c8a422200c2414401480c100700809100c0940100c0140070007840d010305e01210341c243d003201140d2180e0710881c041c0070507805000800c02221000980070040010301c0d0100540080e80242e00030b620715281440640320764600200720081e019985094103a00030104511803540004c03c00b5600400b400c44080c010141c80c1e6000303000c110920140c4460605072440100a0390910804c0036421656160300400d03115 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 992888255 1250 992887005 992887031
    0x4020d060e0106090501090f0c08070503010b030411030312060f0613031e050a0303050115030501030203030901030f0b120f0d0f02030a03180b151f270911040306060e2701 75
    0x2d00240d07c005074041c0c841400c80f030b036001d0301c5c451416102c509042070b49030380c28161001801400140280c10309000000701140500c00c030024082110400201140c1d0ba0b0080040b52000b180000d4440d14000c4908210407152407600405480c00c04c0c10840444010a1545d00ca445601680c1448080500c400e1407110011a02c180034064034a4001d031004956545054020b42c078406000001c50101032601005000598000c41150b500b00400d00c0c0114a4a07550340c0c81b000202604081c86502c03e4000042d550052004151242954500d03c1681e100c020f541c0025690b010030709001d5401030b0010004a21103d00a520400320910460000d966021082e82d600060b95410707550440760614550102082d131510320701e00200c0002c44151100d548401c10405864400b8000c41c00103041e1140183e42020800740e003000008001591091012440d20104640386502500003a50018180480450780c03504070722465000ea5400e500005450a80c03080c440c11034600c100000c0c2c61035480f2030324031000d5 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 992889505 1250 992888255 992888261
    0x12160b130302060912070209060a05041b1e080f10030c0306020d0c17150d061107031b030c02060f1209061806060904060b03030715090b06010804020d060e010609 71
    0x6680d01400d2560940c41801c01a1901c800100429069448800c0e210184900b46042e148a55810364203503034680c48100006401403080c0d00195045031601c108482d080c12607075680526400583c40311004071302c07602540000141d043c00464045403182c4003098070b5052850003140d0280100c1101d00440c0d440e0342d2100c00300310250713000780e6025402107100b18888540d0b10889078041c0c1d142c01d0440c02c68100744000081c0240090003000c1c40144000c1003030706600d60302803000143c0c0c0d010301e00304810000410010402d070020b0b8070980000740c040c0c083c0c888244188035a00300c1e854140d00c80101d20452a0700700042980b1410300721980c24420f102c84c1041e5107030290464014079025028007114a00103402280e00c48882c4001d540c0307540641d0510000c1e072035121a1a03005a0809408109108003802203880c41c810b01c3e03001042e241d1141e41070840441688d100010540c0301d8040c509094070360340011222035a043e180a07511140351049480022035030307884134540ca031a0714000b1403030a982d40581806c0b = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 992890755 1250 992889505 992889511
    0x5040c0c0b0112140f0102030a06080309031b040b0310060620100c050c0f0f0c030d120903020c060a0305060f0405040302060a0c030b0406031a010b1911070f03080903070f0812160b 79
    0x1547e40200510030841c41d01e028880141580720011410075410754000384ea0707125900c4002c80c1e03040c80e00c1c1c407041d5684c0703032500208501840541100d081d4101d0501c0c0100900492040500299030304020642d0081810083c04c61303040c0c50802032400d6540c041898004102180c0b16006001c010429064148014091111200c5081014011320a07040703d05d9030500750307030003d010b00c60381107290380000641c2c0103161150480c0010800080d0802e05290a915089510043c281e105030089103402c440ca80c107802c42c030304c00c160903076015512104e03280500095400c2620001c0258100000040d1102441d9000c1d844040c000d01d00490380d500b9140210341220907903081a182d03010910403421303a4400e220002401403628000d40751402c100e903441310100c88040310001003040680ca0b0440c010f00000c00c4014040e000407413000e002507175a807825280700d034401502507009010740603000a1420000039104115030701d00d00a000c0c074500c6e051030014250312603021701c002850003840e404042000890308500c = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 992892005 1250 992890755 992890783
    0x30a080613050108010b040f05090714060c0a1410060302010e060904140702031209030a02070317040308130524040b0d0905010e0c031603030c0215121005040c0c0b011214 75
    0x240f441580c402d02c010b0307035101c0c0c0c8e803ca2072038200030a002c0004400905c04d004c03601d14600e42d0a00d00f40600000d2800e02c10111500454440c40102c0d40910000d81a25910080014212880c5410702003002c015600684406030200c3c0c108007001c1164104003005001442c03004000049500b2100c1c480749454100f41c802600691005c00c001e54028001b5011a07004a0908010741c03c1c0684510b009542e880d00c0c2c0030040003240c1213800314000e402c541c0c0944001d140d215100343d40741e1020800d01d80326103000d4030825202c0c0d002ca0701458801400c0c4a41240c6110140091520705810455118050b51002041404141e540d40307014000ca40c00784a1f08040458000190000141c1711f4101450180340060b48004640c0800c0d0401c0066040040142c0707899040c0c43c011002401112400e20b03030b001c0d5160f07001b103030211082000710200341074480c1410f6071812101000000200d00013142e450044070401400d00840388014010b9004480a01001e41d1085104400c0c0300d8004415070305003251020800 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 992893255 1250 992892005 992892011
    0x607360807060f1701030204091e120801051906080711030708090111031206011b050f070e070314011205071d040c1202130e01110732030a08061305010801 68
    0xc407016a02c410b01d204441428a4081c803132421400c0d02030001c10040c480244165901d8008000300143c4848029003006152120710340d02e801d500341101e01c0c1d10010450300c0091507081c00800d261521803982c0964446003511b05083d2424a1016201c900c1c0280501081c040c01c1485540b10f61020801803c00a100f0310b40b2701d80700c507501d100140c0260403c4c1c10021654105102e042520807118a0441d4044400d20b00f045c0c0100f40080d0b4070b50f02c401012005880c9010303d240d05105e41000140880032a44007110340d213140d9650007003c408031120704003024424800c0c0d10040010f48800c0c106481c03240d00070400c3e900000e50300c01c1140d03030b01c09021140004403c000b1003013000340035650303103000018800342e0302101d2050300c01d81c0003450708495210904040c90f9035400a403a1501c096204403120080111a030780e481c0083c0c00e02c1104010070030070240c2802e40300b49030440441100d04c1070841240c1d19100031400c0c2402118280c0d420742c80103290942002d4089055000c908617801694001c0180700000 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 992894505 1250 992893255 992893259
    0x30504050a3008071b090501060305180708190507150804110402090f0d060902040507021f06080d120b13090209060d020a05040c0e040c0e0109080607360807 69
    0x7800030b0005580000b00500d038100000000300700030300d080f1032025a211001010003c60b0390b004041c00d80c1c0d0303504146083d0b8a0500040350054242e032007580940c44a480314070f0301c0301210004659480c440d0284041541100440030f01400201d107203044203038071607015540040e890712101c1c0c80714082411045d00250066042c041070200819101c0928002654194074240349000441d010514201c0402c0c0160300890b2454180809039000354117281d8010020f21aa04083c18025950400041031703803154010311450b24400394440c400c46040f5101ca0000c1d04801c10690415908510b580402e074181782d84035440d2002d1987d070703110a08000c250300318002076884070b5401032040000000788904c1c042c80522032114050703554544540110741c012500401d0b00300701c9032400c031030034441100c0c01a0018184441c00034103130740003071076080426400ea0b01c60b12259902c1800311350f2180280c520a01007180710b00c000209034006404404004c051100051804c0541700341d400701c807840c0e82d20001c5142c00110013 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 992895755 1250 992894505 992894549
    0x9030a0807050a14210c0c191d150409031707050310080c011e0c0203010515030d08010b16020a15080702100905030405102d02012a0c030504050a 64
    0x942201c1d44e150ba40101107a119150058200c0700f0303000c1038400d00f800c01144185c1070b41d00800400314050400b6182d403c9100011001045144590244181581c2d10700c03081d00d11a698940020301c20401045060f45503440c10050000030310315a007060b42002020b200c41e0414001c10f00081d40250340035a100b81c0d691401d004c0400f62500f1035008119550401022042d144e1ba0113403070403205a41d40c0c0d50f0300101071840c20058903440c04001c0029010350811041105250b04100d22408216050f42664031107544504200d0300c003442401000003914050100003c48500343c0c0c0007409041c4007030710440581e900c44010064401c0344c103084038002116001000042581444907544983c0207017800d10818005985503502c1e030080c1d000d094086c9601c54662445148204071448c000041180c40550683c60f8940d01c62001c3c01c1d50342000003541c00c220059044074107080c2845103a580c2c3c00e03110741c120303005844201c502e0340001c4025400c0000a0101264a66407807100c0e0008045640c6001d14161040701c03 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 992897005 1250 992895755 992895773
    0x21c02130501050d1104021b0102030402040c02150a1107020a0e0613180822180c0f05070f0c0e180f0a050717010f140105040513050c0609030a0807050a 67
    0x445030304141c100301c01001107450320010341e1011903115140351002910a0081002405013400d0852601c003541c0115691b03680650080d4005c07030013914180250700604600340c0c0d03200554030b8401c0007003d401c40046d000c030869034082e401c10184091505e190010b50f03000039016545641111201441e448140f0134a8a480c200d07941140c42580020700c00c2840c80c501507a030f02d036584000900301c07100000701c50580650052f103440000c02d18810343c7d000b264507500c0d1211103013111200c40320b48601d00000c01c0402809900000010b0200756034091802e0010b9492066002810404465001d10440c0c041344c103035651050079124940700c9030f910300c80c0c0c010700300c4440ca407c6140c8510461038000c4144000400c10120b440c4007a43c0c1c000d540d0007005100110064010580d0802040c0c01380c1c81e1140403481d5006600c003280c12268101d8090007203480b9040c1c202d0100b50009030042c2198400724070b540180c14410041d04000c03600605907039008000b901d884031154020381040381c0f190040c40c0b2140411100c01c1d = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 992898255 1250 992897005 992897029
    0x504030503310c2102030319030b030610030c0e0c0d0b060918240303070f021c0516082a04020912010209090702030a12050c270907020309030a0209060d021c02 70
    0x15528851000c92a00400d1f10b9105111007400a007403810110f050740e134003a4110340d00341400038048680d1803a2024a011181c25280400c031000002071000040307034036050305254001e21100003540d00e09900d1403c41ea004192a40095400c0a400c0c001703c4010369880000500300b442c00c0c90021210300c0e00358020200b0040c80c3e01c12000320003503081021000d4400009880000d503003c271506250000c02e0001a140700b116582440c0041d0845120804109000c02e000203076031707254114080c01a4540490b11313240d040400407049019030f14410f4050503500384030300400031100a000180780100d60008a0054140c0f00e58a4040f69000078403803c50b401c0c9406121740c8511548059400c104d0807030350080075403540007141800030742c81c0c41c0070a00c0502e401040b61007240307031010540a40301c012442078509011000781280f16079400340c000703079110b40088111618504020042d00041c0825420090300c080701a041d281c00000754410f240c01611020180300d03000c03090340300052030001c0d0381c41040706145810b = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 992899505 1250 992898255 992898299
    0x5030307050604021207120305070c05010f0c0605100506070f110f0d080f19020c012307080d060b0c1c031401120f051c0e03010504030503310c 63
    0x30440040071034000b16241e900550704499007003003007004513540c0349003c2c1103410800101010881810405030030000a0150b54804c1034645c400a0342c0703c006480d2114161620f5004c150b0342c2000f400015010380c05541d1014180421011154940340440c0d000d03000440c2c03c9504103400c0414405001100050560504d022142d9040040003000441c030700015091008010f0180400c620002e00e84110a444061019200c841410820028000c0d6100c0c1e8880c1d0150100b070111146140da94400d00e00b03050582c40d8003213410720342803041c1e9940e00650f004c40103503d505d5903604804a025028840101740c1421810010b1003020207600d21412024030303404801092503d804280075007200d00d84c42c0b03281100c1404941d145960501e00302640d42c11036000300203003940074226080207081a080c1030210141016a1400c2060544009141c01c030f90080c1c0740600402c2e0b080c00003c5100303010181c0c1d1250821a004500c0079079003012060540c0c02e134800412100909005014404140d116103078500400f89 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 992900755 1250 992899505 992899507
    0x706120c0c030c0c0305030d0f0e06010510180f0801091b080c31020414060f03040228090203010e130c2102090f0a05070c05061f0b030f040c050303 65
    0x50303400190022101040050600040040140034451004504002140c02c142940e5030f0710b001c05158401030144540d00203003585440700586071000d00266550503170300d000d4103a0608148078201035800c00e400e44041050000242c10204e00640700d0740101c00104160000031806a62510f07100c240103001191080c1615019101080190b03400942d0b400100015204d40f5402c110a441c110003481901c1e0a0100c80d800042c095400d060f0180d0040c012940e0800200b02445100740400005126005040d41005010703c04503000d0f160a000c1c2c101600d94102c01b600700d110140b58090000c410700d51090031208c1d40800100f200d20340c60000c04d503002240b4a140710341030f000b0750b82d2050700e030015001c0c122451000342208500181c2103c442400b01d03400820b071005500c2c001d4601a5011022920304001a04245c082030b60240140015010b107a8414040d0105035a803521051399008903040410303c00070310400002d40000074100035400b805014002c1c0703849207018100f1480300c90095201038020380c0 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 992902005 1250 992900755 992900771
    0x513020c07031b1a2209090c090c020c060d0218030a0b07080c0403020102030319020c0114101e03110102240711030316030b2418030114040609020d1202070612 70
    0x2144d00440e108a0038045640d158420b51002c003044081ca0390304000d541500c0d203c0c3c5074050029410088049030400e1109121034400040200d80707400007500450b030022024404215528456005040d04126001140104d8403405000038507041f5603010580f1010101c1080c8914150f00c40640e5501c00d02581c8407502d050300d5680001d64911004000000e152201c0900300e09011140d0101c4049400301c1000b485207040f1a4414103c2d58010788402c04014130310320000580712400c15000d40386a5005007501241c0e032964030783c0710305035210451050444c010b0714200380b2101c010350200500d5680048141581c2d00d41214080c0c0100f1120202108590042c81040310300040300a00c906044410303e00440c034022001e0101d0005070b5851115580c44040201c2c1d102d00c4078010006d0883d005845071140b5503201d0090901d4203c03024191144c001c40c200340000303004181e658204a400c1ca01c00342029410039500e89800c882849400341c25401a04103020410129a2042e80040c2c0c2d4420218100720580d = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 992903255 1250 992902005 992902049
    0xc050d0b0103050705160203010b060c01060f0f06020a290f0106020f060405070909170a030e120405090c0a05120c0406020d03022104020a08060c03040312090b010513020c07031b 78
    0xc0034544c100344907444061001003c548007904452b621000181c082030b203030b45450b04840e029010354000c3c4040b02d1b140007000240c0310b03512662101110390540141642505035100d0f00704600034a0005048100c10200c100c0c90346140000b4a4804e041a404045455041210080c200b05a01c02000e14551115090001046000c5250f80450303542c820001080502071502e0b49008e203050780083c0000001140014031540c054120040c0c9460480c142c0301c01d005481c66562150089000742034203c1410000a0301509040e030041c4401a6507052440c02d1070000415800c5003002110001901000410100040c6030100403c401111490400f5401d058036414148400c60b901c038440c20b1309079a440f01240654852540550290862030b0603180e941c60000c2c029031070b9034001e95040300080c1010f01072490a04030751089640300c0f50b0040c400d10040c3d1802042145241c01c0c624203401084c0e0801c0030842c000e07002c00080c00114440c0001301202414440f116020700b646900c546008000180c004840c0 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 992904505 1250 992903255 992903257
    0x70c0b09150f100513050601020717121c150501090b07110907051c050f0f0103030e0f030c060a1205060a03030f030203040804050d0b0a0e0d0905010e060d0c050d0b0103050705 77
    0x400422001d00d901643c80e003140d1440189258011504a844607114403004501e6800003441010203800701c071701540d61544119911440340300703446002e41158401d0030841080d0300081c03414103001143c1030010740320a42c5440490300e00100a80e04102c01c004100701d1542c01520840080110511050030040700741c60f444202000501c003548103070f1803440011240307030007002660b0820544455010011141c0103840d0020101079491502e20840c02000840c2c1565600c1c0c00c030306995040d614800081310130010300c106094100101981030050040740d041c680c0b41e50b4040c07d8124403030303524055004200701180341120340141006001c2e200458040c8007080e01700c5400c100760f02152500690b2030380c490804030094001c1c2c2d00200d501002e40b54210040c403140150980c0101c8190f1410041b08044c280895507030201050b02401007041c8507404c1001d98085d201500d0042c401a00c56450100c005e01c2c51030843d5012040c203030201c2c80100789010080410302c181c0030102c10a0a0070081c900b002800a40070f = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 992905755 1250 992904505 992904511
    0x4060605121c18050f060f04150e0d0c06080709091a0915011b0f08030c0712110606060d020408030301150f17060d08070f03030506040b0102010908030627070c0b0915 73
    0x340716251700c50507150f180c40c41164a603040c41c500b00707500d80b41c850303100d0702c06180000c41890024040d83d2031440d40d407401c01c0441c0100355011b01a002140d140c100b080d256018010480800d01040950001c1c8160140c040c10031406420704d10341c54410020010440c1111002d40154103080d0500400710090740c2001040000c018112203000d5286014a410001034070300380c0004208001c0841031003404e54401c00500344042c4070340d0503070b000c0c0686100201c031020b00d00d4108020a5102d031000c41c60354100790300281108200420301610701134540819034030b15407080e88540c1c407142d1400303040c50039241d005882c072400ca8a2460411103411008550705140b45001d01840d114000402004080003032010071204855407000040104110030f0501900501d4120ad030b450049003460b12400742980306110340c150041e80060f1840c01c64460701d06000c0500c0c1c500c0080c0c90030000404102031511040c0e220703e0700c5032265990b4121001124501004261405001c1050b240d004011080c0e40408808015034 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 992907005 1250 992905755 992905759
    0x140403051005092104090c0521090c0d110118140103020d060306050f041e020117071106010e0402150405030303040f0c05040212060a0e0601080c0304060605121c1805 73
    0x50b80e8841c00583e40c1400282c00d4003035100c0328840142410b0225801c045e02c121803024204201ca001d941000b81d510b1b2142c1c1008240301a41030410b0f60003148145c20142d04144c2010031110004030703900101c0d03020803103401c0583d190381c08854404544d6034410020450040706d4280030300c4191610f190301100c0d000198204e4140742d008160711752034800d44da000b0402180c00c0a805d0007030381080c403180d42c0820015141621407d030780602c405c5a0640160300c4446441e81a9140d04400001068007401094050310004c10444104110129020208904c40c003800300d1541c600d40504080c03041200c0188240d081c481c090a007400100090b0342e0210682c0d42c0706812818a91490100b4134022070b1a003e10307003000f903106101184464503250301181c1f40780304410940e000b004040c2c44940c001c0ca400740441d00035002500450005801000c1c2c84081c64005100b01e40c081015500d07400061400d51b50224403d420f5405542d20300051101d02914851341801410046110300f80c251042100d10003d015041c = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 992908255 1250 992907005 992907011
    0xd1e030b0d02130e0d0f05040b0702040b0d14060718210b010609051203070c06110f010920010c0c0501052107020a03090e0609131119061404030510 65
    0x4400c0d625003251001d405035000348031200c004003107040e41d801402031070200c040f00d10a6000c500b041c2802000030761030f201025101d81707090615040c081d8155070302c81c24040b41c0158546094030000d4444007801407000344181c486100015080d0380d500d28160008064804100103541e05070442c0c40c40519243c1520010f2103400505405a80d1244c50318560400042611820b6000019002d81c400212020f0312001c440055114a4001d4507a80c1e078018a1009000310210b051704014803405001c1e11400ca40c4084107031aa08c40414820070b0071640d08480948a03248070902000780011101c413075003040c110900340744140300b1315901d514060650318002c440c144440090603801604c603403024009001c4264003015038500e0074500081d21240c27172070412800704041440120304240d104060a116410280c02820280da4440b0240c00e000341380349081d50000300960200c24283c44103a03a401c122032900c2c1102c5410703458090000c00030705001c0c56514042c0c4c420320080c400540041000c2080040d044008 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 992909505 1250 992908255 992908271
    0x1315050d0609020a092319180803010303020d1e2115181b02030703030c030f0f06050f03010b060d0c09080601090e07120807030f020309130207050d1e03 67
    0x10040020190103984038402e120009002284c6400039070f5092203c86c2e268441c80c0b22410364025800d81a988031400d4540c042441c804c995070355002010000410320711206c50400707070310340c80c01c00d0740280c10560050704544509500706401c20000c40b41001c110040d00410048100020000c0c1d800b1a0b9000112256002055030700703049400c450000718840c0320390020b03641e40d40d0f0101c2c96070380001155240d86081081c1c1000315500180002d508104c82d4000c0d5240c8049550102e00406c0040c0c3d150040c1a56004614010541445005c0d44c0c0d980c200c0b0b00040789e82c180000c0210140754200200d20a81c100101444c8603180c00050300d6164a1200300407510500803d41a11002301541041440d403182078000a090511134200629240b440703800c0d00c1d0b0450301d0705e001c2240c1c1071180c2e40282840350308025003000684103070f580030b10000041c81a00e040c401102e000031500d00c1e28007100141079801040f079406020b0244510799080c01c150910540d14060000302241c00d99076a0034070030900d56a4100 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 992910755 1250 992909505 992909513
    0x1418031606210f02040f051516141615200a0b0615070b0a0501051c0210031104080d020c09060901030b040c0b070804030b1005060d020a0c06020d0b1315050d 69
    0x721840003183d458041d522181c6441048103070400794070905100c0c6034082850020007940c881201e5200003000c0c0508840b400d1600d90100300b03a002d0700a00c825110f483c40206224541c0c2014401030502081d07605039040a5900c010308600f5a001003004041c140e0b044500030110010b0400c102c2540200c01070f032180da45d000000c02c40c50b103070a0401e1102c03400003080340030441c0d80e08002e4401c40c0008030810860762940e0501c450920b144a45860110941e030403080940703400440280c40d812f06150205000d50310060005c07140d00140d00030b01c401d03440380840b0700c0002d8051049000707414041d11504190b1620b0400503640b14010b110181100002d4008a01404454215072010300b0020fa0140d030b50301030781d25140070310b6400b41c8001d445078940c0502240c2c41e2504d0368903940445a0041c006800c00480e40344403030096000034514814080460000c4002903907900103000d940018020000307a2074084800d01c6044200344031055500351070410700d60243c4400c0d44410096030415108400100c40c54a4 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 992912005 1250 992910755 992910761
    0xc03150f040509060105181009020d240914060d080a301118060a0908070b04030c050108070906050307031103150f010c0f0210141803160621 62
    0x680d81e0300241031074200140701c200004e40718101c9a05442c0007801c038070016220745c6107050694040500305c001d00010002e840140d0040d0541c00c581c40d60020b40b407079003070b040800c20700c184a0070006001d555040c10020031981e8824043d1100d1954407144045c580100001c68004040c1c800805203940482e46c4000913126041c012031629121208103200d0340c0b0246020b5984a00c03404035000c2500740011510100c501205840c14503030401c0b580c003038641c108400c00071503400c0700c400d40b4204038644800060020040090381d000b41100c00a880d034850440c10071105c041110380000c1c2c140b003a07a1040c03000150b44400c5400031907115143c002d440c3c0d150303200e04070042c0c00c41510340c58511401000380301c0000400c12581da01c1c440111024241241c4503001590b920343c00c2c0c14050301540c503070001e91015060440d4040501e600ba49002c1050202c44809040303c0d4000365140c2ca40c03c40145000000b5080070400741c904411141c80120b802c034940b0500500c00e8a80d6035484010b06800c005407079105007150 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 992913255 1250 992912005 992912029
    0x80612070308180310020a050306090405012018030105010f03061a04020d0b040b031f0906090f081902070b180f0621010909081e120f04050c090c0315 66
    0xd03903920b07a01d9541000c250310f19041400c1092007406544881c0c0c031181d2192080340e00f055601d0303c566046550348800c020102a00070b10603039440d501c0e09500e021309141e1200b00b00800c03203e00103803500d55000b481420150f101a8501c903000360b240000500c854400007000740b0450313a200f480482c03410540420002640e40310f0388a143c109001050500d00c00000d600091400002038800300102e034001030030181c1e1000d481e100807104c1c0550300b44c041c0c510740c86030b000320034464000c0101141e5402c0c280e85108101109035000c1c2d400081c04182d0140707110300c6258844280100748014149282010350180c00381c03050504030100c0c1105104030f200d003078075403c2c0c5220104800034640c0d901d4800c1c0009080e00c04211031484400445054004959414a03118070188550414402801e00b250040c4854001044416000407803000380701895a46030031aa140f803142da4000485189810030b440d0041c81e00802d500b00500c2280301a04000d800600c00080e42e0f40f102018510026a41e6800040384000f00300d0 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 992914505 1250 992913255 992913263
    0x160f0f050111030a0f05010501090902132c010b04030302030f0c16170f0616180902192c09060a0305030c0d18031106071e0b041104020a0806120703 65
    0x440d4041c0902500003d107216005425040c8413200d0f000c01c602045400900549001c254813240620403c0d086901408030f4902000008606907102c0c1110020812080707403240851601030a903442090740110107d00400350641500d00b03003411680d020b501d0f4003400444041524001c960b200e90407008100e0020500b419201c10100b00b602c0342e52031003500c030052035480154071400c01080c0d0034210005e495841140c850702e2400840106013030442d801c0c1200c409044407503020300000f09925105100401c2c25200c0c403119074102d1600d042c405045000700c2d1145034a048800d41c4041f50303469840030f0342506410b007240c40c40c0d02c0344c0e9060700041b0340d180c99403c0540036101c04208080041000100440c0c0000c660703c8402c0b90b04402c0301da0070840c0740c2d240801030400fa2440001c01c1d550600134040c25034a88124071200e0030070440407079200000300d000019244619103c081c44144000482e02614080301a00c0035850100354038405005a007010f03200c40c0c01281c0711800311940c0e45052082402071588 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 992915755 1250 992914505 992914511
    0xe011404170105220c051207080303090313060903080304020d150e03090f09070f0e03280c0b09180a0f020310061106251e0512010506160f0f0501 64
    0x41c0c048203500a007011a007403140300043d6074416040c00355400c400c04400f0340c481943c2542c0ba04050901480203401d4800c0030580c4211000468040d0f020310240d84940754080003161180d1800107407100890159100d00188081c184050010074000760890f51f10a80503a5106403061040c0740100203410303400c4121124030328017821302c0b000000120043c2040700c42110b80044000c0180b0030060a6201922014080341025845440082c040c98110007004ca004096030780c0340d0164a804d1129411160b101d21031150700304002010030403844a008042d00300014082c2c10000500c02007206e42d641060494524200100042c010500c541c0001a4601b01503c003952603060410b4100541ca550b4001c0e1008102340f09032416400c9000500240704281c1010f410100f144107441c640440750301807940004004c1d2310140714002988000d40c12044501c540c0d62640d850700e10307010b564860341068000700d2246a0030058019822545144e8805058200520f03981c41c040c01e04d450030800030045001001942 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 992917005 1250 992915755 992915789
    0x1806020a0302070203120f0316020109050304060305071101110a0c1b140a0909020a1a090a0f080d09080c060a120e0312090d080711120c10060f060e011404 68
    0xe4541c02910f1054030940c104e07101500d80128075403580c000e007000311840801c28030008440d00e10081311108015450700000449107036548905041d03910a4103c0f0740480e071100c0503c261a030303211000444d02a00c41e8020040184a408052182c0c49414131000c2001140c02c841c10502c101c948130900050280101d8001069a4148154500b0942d2090501c20101340b0f00004500015011792414a40d0042480c299035050a902d1901c00e21006002d49900320b01384551101c1c0d403110507809020341031645420020624200c049031908020049010400042100c2007164004c00117106050400c125200c60300c5094560084402090751040001601c2c01e2a61046000902000071b1520315285ca25421070356440521481d550104007003001c0011f60100001809644101a034107050111301090300c0d000c40b00c802400c08039400c004540510703508941101c1e0410051031107954000c140b03001045100d0b9103803c0028055801007080030381407109445400c0c10300054030b0304580c041c00140c290070680b1030f = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 992918255 1250 992917005 992917007
    0xf03140409051f0510080109020d14090f0606030a02010c12050c030d0b0a170c0906011206080601051017070c02040f0c050d06080102090f040b030f07030f1b1401031806020a 76
    0x62000003d00081e18100400800c3c0341c02d20300350060000300240c031410140e1b40b8002c00302c8025440404141c0c030a5a445500c04060020701401c80c0c055515403005140b54050040705030300f002000303000c881c0310350f214940740b00050341c000f804400845d070000d5101da4003d210b50010b131518440c482c0510814000051010034080a55212040005060321014a1141c503040b07a4a00e94111a032658080e90210107500139038600705142d0b560180c0c06260401682c3c2c2c41000c00c1054805a03004004260003140040c006030170245091212103403103107002d5100407990a00c1040ca0b8501500b103030300b0010001c00000039502d5079000750b950318034078150800008241c3c0400801c95040141c0109100e4144200000d06542c1402900d0790785600601c801c0c044c5040d2010003000f48954090030707401d40185c80c0f01181c40c2005018032001035000e040364030751945562402c40048840d4600c01d595401640c031080c0805120007055000d403090a090024442e40f04540001c00c176030540e00021b00b07050000038000200c2d = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 992919505 1250 992918255 992918281
    0x604080307110109050d080a021006120501110f03340302040623030712201902010203010602070b0c0307050706030e0118170f0c0607050a08010509040f0314040905 72
    0x654001c0d5078810040c0b400900444006505210b000da218a200100f4404a000c4c0d100403c0d1401d070500440d000310320000718038005d0781c0c5c2c0703036201c20104451080c00406105081c09100c2001a04481c801e25150f0303100d61581140c04042c25102d91030982c421280d08801d01c080b030003c08070500c0348081c00d80b442140c400402961150041c1d0000506100b0400607025200b100c1a00480200b4200350445c0c1d00e6020845161100386280f500c032540318229100b051800303040802d0808001d4003195521400d0030b0003903100d9908002078104680c0b04100420810382e01041c1c1e041a501d0116020b0780c1cbd015000039080c51801510130203059409040320000d1042c1c0c06a0103c00400c4190b4000d1151711404100d5001181c199131019116000f00d0240317800d40441e04c0014003110513164929030900300103800d0b042c43d0000403a480e1001c9080010300390316490300b2201190050034221590040c51034181d850b00c00500e100440182401241903404080083e8136042e1030141c51401000c00c030a1804145031000 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 992920755 1250 992919505 992919517
    0x314030f0d1b1b0303051314010506042003040201051b030a0305070206010909050c0f190902030709050402031e18160906060e06190e040c080415020c120d06030206040803 75
    0x400b866070090b40304014010501e851011038404014018881103480070340c0504002849401031419a0b40410005206c1901004503030b503590000103245e2410b04103201c02c44200c880001c121166601c41d1140d641e4501d0226940b042e820720f001900c503215045168098410703004225464000460340d40e1101c3e9243d1300044c804c0045030f080f24030990b030b20b941100c121908800041d01640003070b013500410381816800c1c484108400b915249515004542e200310440d1690080c0c10410340010600c030309560701c00381c41005410112821455810684c28101000302c1404040d1204078001d80090647e1401b5240c07103620001031016501011101805012012094000c681e80f16181280c041200c030311400184076101c00150201e40350401701541c00401200d41459034040011042c0000e01d140c0341c501075014044416110325519080518060044401a0070b03400a80392052001c10399140c00090049038109c0f41e4450542da80c50040e111501407c060f0700040d400c40300008002406d41000002484 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 992922005 1250 992920755 992920781
    0x40e04020a140d0f0c090e06011a0a0813020f0a0b0a03180c0e090a12050a020f1617160e0f070801050901030602030a0f0e031b12040314030f0d 63
    0x40182c0c0b5480030903035203640e02c26443d4201c1e40443c801400101c4c808800001c0c68002e840c1e88000f143c0d12000102941c0400156040a404c150010012428480c134085110800d00707c5c2d10b420505407510003444c000009110304a0040e109030b000c800d5440c0c00c00f5440d4400c1c00500110641ea46550307075042c075a40072440e1b0340000782c501041140807074038071000a40c545600c034404480303182c9491841b0768088800303880410310b802a6484600001c420780701b860100920303500c481c1d4603010f807040302a080407082042003221703422071403008807810f0780048820f05031500c0c0c2180785421510310245070b1400c14080900300c9030130105040443c1c0e007811700064232301c241512030086400e50b4811800b00d59a031020304c91660480012070050001485a402856101c25100800120083d038220303441c09885100030440a50b4100140000e400a1614210140c50540c000205100c0d02940301136001807166110103800e04031007804441829070140103c8495070190b01c6115241c50200044800410340650707155 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 992923255 1250 992922005 992922019
    0x302160605090603070509210a0b0a090308061504080304080703141b2b0c0f0b040f03060c0905030a080d0606030c0c3002010f0b0402072114040e0402 66
    0x60503034490002ca5144000c060000b905640f01c082c02039945400c900f20065014000811150300c04940e440b15266001000c80101020045030401d05481c1001030060b10286080c141c8000200c0d800120040e003101b4251346c00018a205002c1e0150203000d5500501c0c15400009800990388034006504010750b0b0207640700e800140069101c03190f075540102e03140221140c5100c1c20448500d0040318510344041c03015a18010500a10040320020401c80800c4070f0080c00f842050000d4030401103503074040e01042540318580b9040c205000500451880020700f600d490340600c0100902c50481e08004045c080c044035403148007450aa540da170800d00540b02030b41d2a120000424902c20300540b842541c05440300342424203640c03140203904400d002d45600c600c40c0d04601e4040102c051481203860b40480c0d00009a903400c0d12941d0094840304400c0d984100c4c01844040302150b0240080d000000b45160b1020b200345040c07a017a90034005a804010703511001280c00121130314901e00d50341c0319074400c5880d4 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 992924505 1250 992923255 992923259
    0x71208040f060509030a03080a02121e060909150415050702061501080c031317042705010501140d110313030806040917090a0302040f020406020717030d020a030207020d030216 77
    0x84596004800130700342d055220702082804603010340c8200390807080038400503191000d05007000305418016503511070302c040016030001c070340d0310000e0885811000c1140c5c82480c5041440d651a80d0703140360a81d503c0d10f0035810340440c040102ca0800415044007682003408103240c5820040d450b44022a00700600001d01040b500c0f196102c0d00308103101d40350840c020390071900d800c60302c0300d1000020b040848200081400701a410741441003c2c00047c4a603d401e283ca80d4040403108421346c660010006500f810700b8014031a40c0e8003c4043e11045031440b0382e480c0c0750340c0c2405a940280101c0003201c1010400003040c0107100c00e6284d100407119001e07448140803904c1e08018001101e10a02019000d9070780322041c280524159001011402d1004241079289512500090200c80624502d04407c55002808000d41501408507000800b13061a5070041801500443d81e20782c852641c806203c40c5e800210b40b1031640c080c0e41500c1e010b54010340307080c800841d6840c4c007a40e0f400401c582025019442080 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 992925755 1250 992924505 992924507
    0x4150303080f1602031603032306010905060903030405040510150503040b0106020d0903060f0f0501410628030606030b030304260a1e0204050f070c14071208040f06 72
    0x100c3e461140700c2c2d5006500d00715200c8801d40111031040307400c40405840309180012461414041d001e0b40440074000032603410800000340c550401507000311b0182d9000c0c8151219a034010040c0c0d400c8070000d440120383e81e41c8181480c204c101b89500079140281210600c50403607580140a144290320844085a0698803240c090381da803114600c41c0c0d0002182060240b000507900e40020716503080d80000130910f142942280313402d40303c09801440116040320400b2112003040c84902c00748d424150303da5002500321982e090b02c00901561014081c21002a048021044c20f00040760041007154074403101121051006019104a1040ca07002908180405205140c0402260115200d80110380301c2016000e07400f201503004003030203040d54054118084c01103406201d8016041003030640b95040f10580b03204020403a000a0840c00321504101c2c01c1019158002d07144201c4039400954001c1340c007030055042481c0c401e9a400c00012031226404040400000901500966010356240c403071264032220 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 992927005 1250 992925755 992925781
    0xf091a0f2b2301210c17060919030804110d02040905060610030c020a02190b0427060b1b2508010b0603090a03110102040b0a050a080a050f07050904150303080f 70
    0x1d076803131104005000709982ca034102496491140b1030a43c02075001d981c0c4000e1280081d070304854408540040003040010b039020f000380918a05008296030000d1501e031002480d441c00140001c20503000b81442050f2a5141e0440b4002c42d6401030041c001c0304040d00d4002e4990700141c0d00d4600414150301e07034034521800f078065a1400c40c0070368000c2800748401e030200302600000c0c0c00360b003078030207100800420248510740003880640391040140301010328404000e10900b8000100070314083c901715003401b200018408a4645032403901070001140d07110b100260509241d00405440740001c550010400a20042c600f004c4803980c0c3c0082242c1c003120810f001e520f1100b124800c0c0c00e03401c05e100090000703001b0754040c0030010040000600740381c1c484055070300c16848040c0343d101103680410b21880c2a0740c8001c90300d50040084c07000380721600340104609004100034104c4400c0c083c0c042002401a200c1d5801780d8000e800446464143c10343c0c0742405800c02900b0b1b1911542130362000001401e140e0405 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 992928255 1250 992927005 992927009
    0xe090705030c1c1b08180c3601050a06140a0f020a140a060c051303060203070e060d0e1509030301030f03090302040c0f091a0f2b2301 59
    0x500c4051a566400001000c0c9500114400400500041403501c0400c4284200c40130780e070400f04142c04581080b50090003e034401841c50300210141040540c0700400880e00154603003095132001c0320f80344c4022011149401244d10005503640d00d20700f51503a8400c0140440c1240d030b050701c0f607401c1552030311000c4924810451181652600c200700000c0510711a4071039a000c44018030640300741d8681c5989500c07408001c81001c0740e03158001e140c9a0188034151140c01041c3e40301c0e040c0304d86801000ca840900349480c41c44003038609a40480025200c50041a0079020800024a05036580c08072030703800002413084e10b0104800e8800d581042000c410301615036800f5118000c000d5003568030310765a40319100003010b4124200007001c070740000103031110b0040c8250b0f6000c0d901c6500d140d84e02c840009106401951200c01c0102d024401d07001000b1074001101c40d0f0340040c100c030680d92203880f040c50683c969500036100c0114003007240021100260f50040e0240780088095910314004c9402c0d0820810080c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 992929505 1250 992928255 992928257
    0x606060302090a140301060f060e01030506010c020f0103090305130306020c06060108010b1204050102041208090312090a0e0a0207050a0f060f06030b070825030c0806030102040305120714010c0c030e0907 89
    0x7503c007401a801e106a40d22000b0b0002000030942d152a029032003401e1505502910114041c00c0c01815a9a09805080d0b80300341e0a180180384a4801d4001520200e020a009810b0540d40c40030740003854070500440d4015144c20924203d103e80da0324142e0000d40c02512060941c0c040c603c0424103540c8100900c504950840580341d0411001148044811b417010b0412180e43d0f40c03c04c4009200300c00300c094001483c1c0902602078031a03100c441890305080c480b041c88447c101040050710300c242d03120f480300350640720201144a02d40e501ca14802000340f24408000e800d87c41045000010005600c10007201c0510070401807140554115440050f500a400002e1000000c134000522441c1300e03c5005034050403102e42c80340c1207510105026201440840c2510019840301701c1d068115810071903098014a05034000c614152550315910303203800b50950460646240000c4134010703c43d90400140c410428503008001c20011000c0280906401440403800300d00c0710180c0000519100071107510900c15 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 992930755 1250 992929505 992929519
    0x30c0f01050f190204030f150f0504020319051912090806071b030c0212030307140f09040e101b09093b030708092d0120010e0703060606030209 63
    0x3c1e2001a0700710605000704686000c0e401d000c0080400c400c091404441801103c41d40d010500e00360555041d030b4036007000584402d060409100043c0c40015a002c0c00c00300800c08894103800700c1c54054105440303210b5919402081c0084031042c08110078001081c2e0020b6220581529074480700b0b90740300c007003c5444201203a07000c007010301d0f0300001407500c1008502c41c2c030745145580ba0550004041d03d420344050340143d4004010005210f420801c0c811001d02c140540c0c0703003800d5040300c000e6400d1040c124500d000e5616000078a000600030000e149040c0c03075840b414031803024010b440ca070700c00718010740302c1002034070240000600802da442821204001c02d244815100d08503081c0e445040f0803c0300c0d0a011100c1340d450518250340600160246038070901ca42070741c440c0003400f0010300c2c030504940c11500a00e001d40740d12540e102c0d8082e0b121b0840c1d082c02c6c0610501e042c94803030317015814402d203602e03c00e5003090040e00d455880400c480003a24070400003000016100d110890032400340c05a640d0300018 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 992932005 1250 992930755 992930761
    0xf070809011b0f0206030408040522050a09080f0922050703110c061b0c070303110601050a050307210602070524090304050103020723070603110a09050904060e010e030c0f01050f 78
    0x4205c1c008560048c001d20019280a50324008100280080307a00910308a55443da06a508409401150b4004400007401d10400c6500c0d19000500d20680008100e40c100000d04c0030301ca41c40d102c101600c4140301c0c01070446002080503441e000f50bd41210345600092400b0f000c0c008070110002500c041100c40f2000300b40654481607641c0d0b004440016250b14002c0c00d00809800d94820400b140256129580303400303002c02e04d0706613240f5280c0103800051051280140c20f00c155200061139204070ba40e5130301e00714035080e80303d40c0001002d140c00d8400351085000160f001d06100c000583c4128103c1594059250405002808245050140c8901c0b4098208120400c4258030070b03000760813103038043c2c0d44070b14100e10b00f42c0600784048880c4104843c13541121600304101074251043c1d022a444480800b49002000c07003004003143c1550090610590014020909002e002d07480050800b010b980200311841d4003400141c2c0c0d03600b240744041a584210000306081c1c40042c000d450107003c02c00130140c5561 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 992933255 1250 992932005 992932009
    0x140618010510030b191509150806060d080706061211100806060423030133060f0804060213081b0105090d032303070e1219080f0f070809011b0f02 64
    0xa03001417545404d507886a00d1021303007036182146034000b090610800101807501040d07841c048119644000036681203001004059150740540c6800141c2c05030507980d683e0303220324003000101500d812224130802107100500401249080c02420100111380c612031900080d02d04903090081100d0164000c0800d00c003c115505265800c0c1d01026440f205642d90512168003203821640300b0740317110102c00800088081c280c030030074204649141010070407145850401202030038081c0030350303203100070011050001000e000c010350654a64240c1d000017034aa05030380f117510599403d9030a00f180641d0002001c0c443d45507006070125907a24901511700480d9540c2da80f800d580107240c505507030000d03560000b10b528062406100462052802e40c0b506517515806a00703100103441139a00c3c81e0002d6124016002e501407840805d0343c00541e2041c201680c0c2c000c0c01c481080315000b03580010310922004240e030f1040024000144c01044400c3e65071400a80c1600c00031b600c192000c000207000180f00e480488054 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 992934505 1250 992933255 992933281
    0x1b0902071a060103090f15051f03120e030a0606030302013e0c0601120b0c070b0f0403030609020408010506040f060308030703180212030c010c020304061209140618010510030b 77
    0x2c140e050500140c01521521800c02c880d1250070121140c03101d0524454420510384926900300c0c4491360241d1628820b04803142403054540400742682030101c64601400d4450703c13006048410140c15628400400d1074410050003075404124059400c040010601d00c2c03c46c00072102c0c80d01c80c00606045100000034105a2a038000b5034402400c0d020401c121130fa86040003e64024401c0000480c00220f050403c542d400d01c0141940c0000d400030080c2c02c01007061121000d8103e803a0035001500c5440c0c0c2d10b0160004c0c031740e42c3c1c044083c1c40c4c00400d00103042c00c41980428401ca8081d1000d211884210040108481d175a003c010640306090000c960428429481300c1121020145141115149a000200548220b200703811080d4030018605210600a00030010011000e000944c145418280050b1009199030035002003583d641190500f4400300d803500c4607000f09144103507002030801d046c81001000020111529560810b03021405d41503051000034126900500311340740d940c4900d2900b00c00 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 992935755 1250 992934505 992934511
    0x6010c03180b070b0f070305070f030c0c0b0a36150b09101e050a21080c06040521030a0506190b090307090501030b0112050f03071b0902071a 62
    0x140154004010981124802c010214903000c2c40320f419041c50055805400c0c80001856401014104002d1080c1d80e500018114400006400c1c08100a11919401c440c2c003002050003606e206580020701c00c00d001e243e0300141c8490302c0c081519806000c564842c02120750022108201c8035111401d2001240c00f1894500c03004440010200c0c020b540e600c00100214005e480180c49040c840070304001180c40d90080f800f00102d088001100240b610b0001100155144205101c5c074224200c0000b410b07005c0440c070b481860340820069140c0d80d00008041d65000220340c211058072400c0315039101401000a0003d2044003219902d1075541c4085c100390140101030540ca8201c1a4480894480d544c95500107000c3e01a42c81c041f600ca0504204051034400d8079408034400d645061700500201311048103450540c0d002a841200e411454a0001c1c83c11440c42c12000b294040881e90070200549071000341000080040c66060894030f82c15050300724030a0041c0245a55404400218107413040805654 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 992937005 1250 992935755 992935787
    0x1e141602121e04120309051c120e0319200105040e0712091401090c0914150a1a090936030f1605010c0f0807050c0c1804060f0506010c03 60
    0x4100b594a04d03003040d0400f038401080380495169034041c01181001c0307038000201c0e01c8070705e801c1c203440c0c0070b42d1188161010304049060810140c00116046030f01d017000851042102c2d45101144001c1d01d040c0000e1540054881200034018241040b00340c0d8801c10a95090304c9000304042d0003515465070903110400700032050348907217407600d96081c00314036004010800220014000b15240e0f00c1840c0440c00001180c002c210307010300c1d2140c40c161100384a0b03561a445901100d42580c226603003c002150010203074801d4202e42070801d024130f58262004080d0a140c0c00a4030704180a44503003019001c0e05006090b14040d0314604242010750704041c640c1c0b003c02c9068001038902d0010113014000c11036021695800020300088140c10411100348602a00c9104034900320f818440c42c01c074002d0159034081d1a140400001059802900400384450808440c00500e917840c07080110b03540010381c000889003601c1c41443e00030002a81d2141c1e004940c440c0005030340700c203601521581d00383c3d00c098142c0c072055 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 992938255 1250 992937005 992937007
    0x50405070b0403080a030609020a0504180e0f0d02010f0b011704021311070c08010c0206131506240f05030a0c11071d070e0a0302041e141602121e 64
    0x40004607030004001440c003c02a413651203029090240c2924801d501513840c0520401c500945540e105041d2015640344880505036082020300d060301501c240160b03000b081c0580c2d4040b00c0c414500103222001e40d40c0d1a0000d110051019a070a41180c5080350f400740031a02e00c15820044d0040302c0b04040c0c0c060b04c0149200d00d003000b05045902180c000000700d2122035000608001400902c40c0801c2c01400302c07100070b000000352400020b48419001c5d25181c0c400d00c101c4902001c000c40b6951181600f9108641005403950b03c264000000506000c01901c00040a6441c0e0000703109181c18000c000403a26058915224194060001d18190004104114a015003190307903507814440c04006100ca6070700f090742c4d0000300003148400000500550b0901c0480407821105d40c8400e1046012250101c50010380c080b0081d0039001240c070800e0031072500e0362402ca40414440e00c104100c502800601a021580c8401001d0990355919039045008103503c0500c004040c032024224221002d2a000900c9 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 992939505 1250 992938255 992938259
    0x4e07020105070b0f100806010b1602010c0501020a050307030f020c120306010e18070818060703021e16050106141e03011b091d071706060f0706020d050a14010905040507 74
    0x3040e2022403d480c00c005180c440b0041c41074052501460b40046c029020140046500d440c2c24110b00b44140ba201320101109802d900040d68006c40b0015003c03a0040003d6548080460008065a008940700c4000c41d10740070204001450302d00c2540d0580b4808801403895a000c910951072540005110904000c00c030f00304120b5640303c90040300950090344041944600704504081d0001c040245080c14a200c1040340b513403200c0e0300040303880d040403803402d005075541866980c41000641d13900c01c1e10040c0200144810101c0c00b84c610201c00c1500842c0204003250301c501c98590501d040509540c0d1010945014950a18145400703020059008000143e4490f040c4012010302c01880785480100c0c0500c8010088411000d41000400018080c82429482d11260240000020049504400350a200000e102d81c941c10121840f04000b1507030152900c06520303040001c0e41c03000c0d1818035410b0178400444c984058a01580c42c2000364001070ba241c42c0c0c280354840b0020b00c0020800d0350700f88a03031500 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 992940755 1250 992939505 992939513
    0xa030e1306090504060b0d03080115030219080402120c030a06020c0c040e0a03080702070605030708070201060e01090e01110f0f0f190509240d0f020c4e0702010507 72
    0x6804000c0c54854400f0926260609040046480030715689004903c00d0340c0f0702d40066031054801c0d0658080d203841c400038542040c000c0b03009018040201741a0008601403100107a00008050702c580c0c42112003c0c802d4044600340c80e140c2080c1d250442d0154800b4001000207031142d0050104e4540c0d42e07041b5030f440300c1d58000150a6460380700740c2c000d4070b401c0000301c407040c554001500c0340c1c8990180010f0082c0b500e0560010190f1000905450811542c3d030041043c4920030340041e8010002da51702043d903541c4400105000b1f1411140c0d140040d0310384241f4506040083c400d941d000100500c079181030161401d00c4a01e141e1188042c0d0142e458200041d86885904e0000c004800b1090750368940c0b50060103052211b408102505500da51032080c0030b09070321060010845900c501007800204200600015500103402140b82001050254100010442c2c4401c2c401f80b0081400c182110703030001c50078241143c00f100d040748840580b40c01254407426100000001c0c03040a1041c9441481c01c0004c9c2c036 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 992942005 1250 992940755 992940761
    0x110d031209080306090f09030403080a0302070f05030301090c1b0224160b06040905100b010e090f090c01050414040c09030b04050a050d030212040f0206040503070b040e010b0703020a030e13 83
    0x1040b00e0342540031043c03003480c2c240710844070f6016503001c40c41503d9040c000d03a01c40e90b034000c84c07200a0204400081d0030000610075010f6a50540d881481e8031084180b520b403d54494000b4010901442e2621005c411450710413844c6484840240b981004107440a400381301d408482e20600b081e5030401807a00010205480e801401000000c20800443c0c1803185400d036080130014254034030580c10514400c010907804a020323071502e0003190300002c5030000d00005990103a04180c03910740c0142c0c050208820900e121038003500c41e000b000c050f5500703091100015580d500443c02844222a030700018171241c0d04059104444001450400c510115602c2d900d0400c07411040f10304507042d402c01140e103c104402041143c003081d546060950408070142070301e004868000300b025103002c1c2400101419902c65004540107001d000d02624031564480c00000100c0c0c0c0284a8460111828000011504005001d565032a075042c1d028190302c010580303040b52030909000007a0b0b40140f54000710300103520144 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 992943255 1250 992942005 992942021
    0x40218090d1d220b04142d01090c1404080c09060103050118050c2101080609070f0b0325030f0b1503010b160f0c05120703110d0312 58
    0x2005100c0382240c800700401c0300d0254104099511140a890070749a03858071460360000e150a4030034124a20000e1030a009071002c550210340091a24026051904905100c03911400c4441e220b8800b56010f032096544507500628014548800d40300144070f001744e55044800b100d4108c0c6041030100102081ca081c00350311660100016902c048550084ad0510710322596004400342001c102562500c40642c6051510411800c46956101c00080510b800e178004c3da0b80c42c01d4400d000c014050381c04030030075203200b0003800348803558031a440000b070780280001040d100342da0140c401070345942c3ca00341e04c021068101030300f4881c2142003541481a03440c041e40d100068816696004105104440078142c100c81d450b01c00c05010b05d0144400c50704c41c1d0016011203046507205103100b960340071303507540000032001e072107034000c0c00102070f0a041d41c148280f416504042d02c0701256240d40c0b0081c14450f00766120514440109200003007a030541a03460599000100c036800f90030003410200444984504a400300 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 992944505 1250 992943255 992943271
    0x2030702090c220b0f0c010204080304060504230303120a1803022503080714030f0d140a1b140c03070b07030b0607050303040f06090b040f03030c0504050d0209040218 73
    0x20070741d0366410245071050110301e10243d800c82003240c1020b10580542c400d0034015180150300241940c40b810003541200d004210761000d482d06d641d21342100074125807061103504c05100280c0c40005c888a03405d4521924180700030011894001e1601e204c2c680d00c0c50090060116030384e188204040c03e0300d640c0c02307460a10711030b602401c100706042a030307526845025141e01016030007102d0b0620001c0c1112040390040c5030010860550003502c030324214518490b50100d05100170f004110310740e11018a42002c1e41c4425505540d203003950315a12100100e0744c8500440240076074800302480c18501a0442c901000c6130000c409142c280f1150009242d60b212540440f070265a603410089107a9241c0300f401d4001e40121815454000d9644030359a4a0002810251034480300b1280c10007048185d074028402d0652000151040745418107181d2a21055403009802190030040b0380000140b00c0e0040b1801e0b42c000803c0540c0352030381034003840203100d030050003207800003400b460441d012850344801038030450701 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 992945755 1250 992944505 992944507
    0x60d120201140907030b01182711010e0913060b030132070c1e02100809060109060b07081804020c21030f0612010f06120308010b03040b0f040302030702090c 69
    0x4900ca940c08182c5004054460729000102c05100041010990604407401c811032851100c0d01801d84100a14070480ca101070103032040c07a410f102e088000800780429015581c860390700340d030b81c000541d07030a41301a15035a801282240014050403109110500d5940104000600140040c0101c0d084410f50b4261124803003203228200703030000c0030700b14140c02092f0503005c100103030a1188000c0d2442550100042c5204024a00c1c0b42601200c15140703d01d45400130050683c180180d240501800e07402d440c1580b40c0e008a800115041140340240c00c22030f2001e4414038a814803d0f100c50000340c115200714420350321030003084402c60fa43d41c00039001c600011005000e9031200a09038240d4900a8800005542014000c000c28400d02c0403da561200050740c0360000d103180e403880b090060070101c540c9081d4a250080110711822001007803840184280c8500e011a6200c090607a080c0c00100c4005002c030031024009610390701c40c1d20810f50024420f004403030400066500041c0210400c803110842d1605c = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 992947005 1250 992945755 992945771
    0x51006050d062718171b030a08010816050a0b0706090807050c120a02131d070603020903370807060f02250b1b0f03010b0a23030708060d120201 63
    0xa920710560400c000d0004030000203241640c3d8580c4402400d00b0985c8851801040340032a00305000c04020200c0450801c0d80e40c0c135080031201a18080e070a0040020a12483c00c1d4403914031105041803082c0c41000700700c80195803070041c4194640c0d00201c802c80f0102d81320070111001038240b0000d010740d181300d040980132521110042c0010820390b00462000c59000311407030301c0962514802c048641006213000701e060450746032404440d01c0290407000b250b206020703001130b0b410791650291450300011019200c00001c030f07c907805169140c041c05108443e02c0c00288e003100705860030000d113900d4410801c060400549882d80b5040360325941c0e0101e02150002000d43d0110b00c04480c0c618030400d100d10500e01c1c035119031203842c0d1001008101c021080c801200c08881100c2200075100c000d94102c1c4c01d19601e44e10381c18446220f03000301124501040c02c44413156008500080009450345111803400d00313594410314101c030103200150041d40c205010740300c044045214850342000b0f0705110707000410081 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 992948255 1250 992947005 992947079
    0x91a0306190c080f04060510170c0405011d0115111009050735010e0a24090b0a02030c040b0412110a08100902040e150403020d03051006050d06 63
    0x2503965260a02000801d508006010b104e903880d4641150f00b1080009041d034505204c0d04d00045590412580b500b803c2c2c051586003040040c00d1080190140d0701445541d82c0c800010003000741c024a260a0b14001100502000c5945401e50a0300301e034134a012100f6140c3d588010b03081501030b00c0410317690360704c400c0c411060282c2001840700800c905218001c18581110381c10400d05a900400658003c04003102d4404800941002e119608003909840526880d46000c1880000345043c0001440c100012150072403680c0c0b003458692500007070402001d5a48be034460009601c01003100342440420b000c003080d02d000142c054030161035042040c511411003418103801007241c12158234400c1030100f600781306072400465004060f0342c3c150f401041c1603546100180c060728459407021140d1080301c410070040014400308901450090702503801c8109406400c80545004a4001618140d0f501003048294800d10040504804100740000c4030740e15048400c07504000c0501800070150285d0180480e1 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 992949505 1250 992948255 992948261
    0x20c19050312090304060917070e0130030c0b071b0b0603061302030309130612081e03010806151f0203190206010311041d0a050105070906030510091a030619 69
    0x483c015400440c2018500b03000281004a9801401d5001481000c18010508100124409803035203180900c007940c1c4a09201c85460200c0d01121038900b8010001d1151140d4982540403842d01552001102110b94032100c1c40c0443c0504003c0400c04e04003000350b01c818500b0a241d0742213100740f10304046030402000301072601c48003401880c400f0340c00d86910320041c5c2d40081207a034400d0091b1544501180100e80314001812180d100400821001005600b004030340d4000745038076264030601010800b10380d561155240400d0069503090303030014001c1580034041326042c1d25039060042200c2c0103c1c50b00c0014400c240c1c42c22100f800942e001141461061501a1410050148900c002c0c48550300d0f603207481c4a210707006041c079402559100200c40c085080d450402445000c2c0d00101c03129a0030724600a402000c0442309640020700c0c004c0041081441390084900a41c000c585c071000c058104406d04004245031505614404071810030042d0648050001c1445040262050049030b48910101403d0f = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 992950755 1250 992949505 992949511
    0x1f0c051603060c020313152d020106232407031805060c12031509011d0105040b0f0f061908010f08010513120e09040f050d031806020c19050312 63
    0x4d5400520242060504c104d071640202c420b09909001c111000c444160740d009009100910082d00b81e88200d50301281d8580c1d141c850840d10b81c001c00c01c541c4d560901d9203546020f00e6415a0601c20341d41944c0c160304c1c240e500c40040848003505641210300002e5a98003c1e44500011030200e40300c0388086c400b080c0c1001c2500000c203010b482e242e10702804551425160141c4903904100c1940210200700e610680d0648080c042030050070781d10712941c6890824508541c021002a056000080042070508050248100415015000002031801c040c1000f68500c9a1140c1d560802424403ca10030f69240c46100d480050aa880700005941000c404284100149d04011490b07810102032054002c3c1c1242d86000141d00302c807246240305490142141c810040c00302c81303580080d03160240005c0c441142e50034600a4415012070300701007030118080e003c0d291002000141188170b0f105280100310141c0052640113102d0b401c0e1480074107080d0503581403481c110429100c5e54804a070009400564000040d0 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 992952005 1250 992950755 992950757
    0x905070e03030c0d0c1a1e0604020732160311030706090b0715020406050d180510110702040e06070f0e0607141509010e07060504051f0c051603060c 65
    0x703d40722003819042d40d1108003a0710102008540304901c0140f01254209280f1076a0a26a81c81c05003091034501903151b00e0520848413800c01000800c00d146400e02c00c941c400e07503211610310803040070288203d4150700c0d1407030b055600a0042d007003100220428044016005d00b44207040e4662421414a0861a0b88410383c440c06070340552004c2c0b000342c2c0c00052280c2242c010003109903882c0c17258904104940644103030403030f80c9400890003040003070304040506890355181a003040001c40000d02d181381707500c00d8031002e45540c00034554038000307045030382000c200450003241c6240381c49a43d41c04201100e51090360303e40150054000d000d0229400102c24a0300350061070150246189000001e400e44142600202a040490035121001500340101c008500b9502c4284045281100c402d48c041c2c91060026841401107038000b184140c01001074070300f502c0028201052540035554030342007442041c0000030902040b003100000150042001042006000d500c0c181c00501d1071400b40c003030303500d0710f40004 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 992953255 1250 992952005 992952007
    0x12010c0f0e0409021c1502030112020112021806030c0412060b090112150504030c02220c090b030a020d0905100b0312040b090907030b10020105150306010803310905070e0303 76
    0x2581c2d540a43e0b01244c1415207a6a40030507446c50304200c50840d601042014034000301c0005001085480603001c042d000b1380303031048840d9030000020f04a1194170790700c401d00c06500035000468140400038503403000552070190300d040d880b080e240320f0840c0b03402e00844040f511801c000c0303000c1c204444158010b220500049203106156a0790038a00d104500c01d4005103641c560019042c1841242030420aa4001c0c000c0c0980201192000c01c01541c2c040c81d128826081019201000d4420040a4122070344441d0f41811921515981c00c00f0758806a4184020764490384408089801407094000d1108020400260300808200381400c1c40d565080d800d030400302c02d00041040b0b40321300d012201c10300e078111000c2005070b480080a50040850480c0c1c1500208825100c500c440e030154071150155181c840000420b500a404040e590b02c0b0900880e2503981043c030442820503030a400b801100c1e03030f20000650004880d80c126800c0c110041d444a00c10303039158002c0c048440c2d0494541900d02d1004c2c0d0240d = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 992954505 1250 992953255 992953271
    0x606030b0a0b1312030309170c0d05030903040305070b040602010b1c02060c39030604031722030c02120d0e06090f0303191103120106080612010c0f0e04 67
    0xc101000500c035110300c2d80d100048441500040b00d1280c1d024101d0001a000b10020a04006000304400803003201e1036580c01e4100c1e9942040c100035a01100300b000024103071071039488000c544d41c4d040a408007040c0e21092101000264081c425500940301d00251a038846242820007800d41c2c0100e07040d0717130080e01c2c030001c039010b0084914a080c14054040e079820742e4a072113820f015840c0c004290791a0310710b10b4056840e001c1801c1c4500c04c1d89d50900d0400e03140e5074183c40d084105912110180e80007004942030300c400c5030171010300d03101d041d5000d0403116050348100d10303564500a410304100c0040300000e0f0081040402c42c9050fa03501005100c100b8001c0c8420703866000b010300b10400c070f02c840501c100c4e00815404200e68525000c2c0b90005c002170b0550352550107001e0410713007000a030f1000f0030205440100304403092500105a03034603402c480b0300744030080e481c14070283c901c2840509001e41080d5006800d001c1c0344001d005c1c0e200341340c0482d610010754000c0044004d001c440e0300000c8502c1141042c3c10307 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 992955755 1250 992954505 992954509
    0x40b07050406050d0203070513060e150c030316021009030f080c0315011110090803153f0613120e0a051203041703031b31180e010606030b 61
    0x1503500c03504c0b402c400103030340742c0301c20a003515140200c040c0a1313000040941e010074040e9010010321310100d001c0c0c3d1030380b58640d00e440e844000b41c02810000040d9600600c00a0781d061581004980c179000c103401900c8101421454800a6910b80d55060b8080b80500300c2005180c0c0d030200a82d0350007240c40d2041e07401d50901c142903481844a6080c5030b810064080a05c40700762506100403501d0300d403200810001d104a62400b5041504116142072400000940c00c10a60a0465481d0070362a0f1421040e2403040f00c02602c0203001710780c2c44806004d000403d00104d40701a041280300d002c0c11000c4100303040c4680c03901c0c1410310200114400020172443e685804070b10b46070f42c03003000290307501112034603c84030b00000304a155004681c85124206940030b640101454040002e41c05060440c41d8003104112080700c4010a120340c1c80401c102045003c2c540406140c020301c03100980c00441e116840e040c0e42c038224081d0440c41e403419840c4842d5078102012414200348140303001800c20707003402d000c80848900 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 992957005 1250 992955755 992955757
    0x11010503011508060a090612060b06030f01061202090a060203031009061d090111030c070506070e0d0618080a03020d1b1e030b0a03030302030a140c04050f0d02040204030b040b0705040605 82
    0x75000b092060982c08503590350744200303a1902819800c0d41c02c0040c66696524003001c0d45071900182e0744130785446400802820a40122445101a110020b103240d1810f001140e5501ba40c0350000180c5a003881610f200f80c2e03402450100038900350380215100d0404407030f1804002c00b19170240e0078592400408000c8801c1c0e09031040451001c804c4043c80701da079072051407030140504480046e0002c03400000c03c41c86d07a1448000e4407100b402401240c40c2340e5981e000c180c0700e507030042120341d510014200726040002d0b450f4104e90141c030605400008000c1c2e640d03580d41d2407601714413240c4002c01d4001c2500d010707012080c07041a0071040100c1510940b8110180d001c1e000c8820000301d00710a60340a04010b4555010f6000985041d101030030003400151b130fa0074000c001750020b8408400082c242022420300130000c8035007074026a00103443ca4909072421041140714040621800d800412000c00c903800369440384058070065002e0706180003070740f401e85040d04014200828203420b0000c10b21042c01030b039038044 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 992958255 1250 992957005 992957039
    0x1a0412050901020c120718020903030426060a1b081308070f0b250e1819090501020414030a0309092a11010b030d0e0f0d02150301031101050301 63
    0x42440ca5482194a00403403c0c004000500307908800e0000741c0454224000661800700e0303a10900b2410040c8011241b58264800c0000f4140c0c954001c2c8010f11400f181910441c540f19010010b0400c2e840d00c0052003414040202ca1022511343e454000c1070f0300c4000e0700c4940d005203100e49048509458a4640403801140d00c40016100d003102050304c0c2e041080e10340610079140d400125616040c50031011031261200c45040311340701086400c3c41c90840500804040340410001032900303194000050700c0e0074007103100600c1e85104005103106260794540c244074624441c3c2c0158005a500ca003030803110011040c80e4030f407041c0280d0000b02003101107588018003c0a5034000380004c502f280d1480100f511040e070104c1c02c903c3e80c030410010011001c2d00142d0b00c100002c0428000e20407502a42e0415031550a01804000450080030401e1880c3c540b92407142c101d800014000d14040e541500458451103205894081d908000001070040c05142c84142d6811142464400e241d0b40c100001c41c3c510b00002 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 992959505 1250 992958255 992958257
    0x5010504121a0a051501080105010c02090c0d1e112b060504140a060501090602120904020f040f140d0c05060702040b040c0201060f0f0608010501120b04181a0412 71
    0x400d1003020003800c41c401010030800d12144482c281442000400144801e071680b1001d95075400107032113154002c003481c0d4100d400503141c0020504d01a02440046000140300b00c1031074208101884051502d4420040320003591b5810108080404080e40c08549200d9140040b111051108056030b68044078183d0114004545525100c0b504107805c03000381c030302b03600031552040c2000000b03100c030030078258402c4c1f05903c0d1080a002440c0e44a0054404907a24011a4016002010f030144500c01504c020a988040940b00610b8210441c02c000c90f2900b0a8019111010081000300158625407482080194048404065140055440c8901d04007d0b100707a5003e4100814001c3c155a9542d001d50640b61000d00305204034140210000e0081c40750340a003418101010740041051000501100103640c0d01c2d480b01e0002d03909240042d44d20448081003581415105d191000558480e4000e980c2601e00011000b6880206803a05490301c0410b9a000e60150140d441000086581d48150705401402 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 992960755 1250 992959505 992959529
    0x10b0f0d06110403241b0507050a12050c06091b09060303430b040b0921120a0c020616030204030501060e060301110703020a110607060e06090d020705010504 69
    0x45460940d018029820319000c503940046000403c0c8040d401c202e20011401c5d41042810a28805558044503e0181810a1120040d80da42851030049000f84034490044080781c805a1031a80c5104440404521034800504041100240e0039800c22015030041100c4000d0203101c2209941c05005c0c4142c582e020344600031020110390a0380301032040750b543c140040d41c141c80e00c00222031888900902d02294450741c2a145010b20000b00541e8003100c1026031106803560325840eaa100c03119104009007006105004d9141840d880c2440d0b8040e03801d02d680e031030174020703251181c0340e40118500100402041c501070402d40108902c960100d450344d80103034008661120b04087c0c0380201d0081c00b03a6000103040390302c0c00402040d180304005040d4485d81d400ca0007403169001180b1800582d004d07030100103015038070a03a102d00000e540721720200c8040901815087c1810080c1d00c070740050360103560800b40390350003600610803100130034000040903407006e00041820b50300c0c000c0000c0c014400c91140301c201400d = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 992962005 1250 992960755 992960779
    0x3071503091401020d0e1015030f0c08030325080f0f18100504060b0d0804060c030519081e071b11060c0706080907050a0303030209030a0507080f010e010b0f 69
    0x100c100b491070344001504001c6454011260380301c0024400c51500504034400d0306d0001c00c1c1000341d400740f40310b000380780e035070107450f140c603595400b140c00801683c05c40d901e801024003c02d01c01802c001852142444000307404003010f4045c205210380e404caa0340d1104109000c801c03c0751406d40f40da96680c11680f40c150800095a854500c8885000310b0003030980c607400380201300001e0f021507410030f41c025400f619041000d014011f00700b190007030003e4802012240d090204000c0715003d260248003150003814060725040690401c402c00584c00e406000c0829a44028401c459070183e0131401c0b01e40e944884448141004a406003101c00d520801103000700300c240140c0100b00407503c9020014802919072500c810410701010703101d03403050080000003030b2640005890110000f50000444801518410302e203425514110043c0d0310003072600780c05100d48600000010020041032005104210140200c017640710303200d0382911030710802d10007540c0c10001c1c07100c003130794070900f18218840003100c0a003102030f = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 992963255 1250 992962005 992962013
    0x80408030402042c070801022a07030204050a0e0c040b0f0f130507020c0112060b030105090a0b030f0d0f020105010e13030c0803010e0402010f0f14090f030601091401050307150309 79
    0x2d060508500611001050190301e00c4c00c540f980c8039084015801d42d1185034885008600301d001e0b042055010350202101c0c0320505003035461402e100c205100603200f011fa100c0e000314080d60400e40d0f0200b0640d9a8820300c2410810030f100c20812504200d5052003019844000034140704280d803400c621681c82805a50503d5030751007110510000d03041b40c213000f42d02d070101010f0340303511809021601040d0b10741070002e4250349510414090f2103034041528111f9090405006502d01c001b00b4414600d950b83c0d8420700b1030394040048507814a81d10703008000040c141030300100302c21314520710b503010340e03040c0001400440042d402095100000d4074102d00c4c030881d0307410300700c90300c08070460040c150103400400840e4400312103a030b491080d4003e80307a00700d54410203c41212075003100031061002400c030080441d4420101c800030314000d20001c1017511828202400681840700070390051400596450b0700d000150f842907181c900408040300903001c0c041c030303114020108048091559007010303aa4030440b0100 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 992964505 1250 992963255 992963261
    0x90b0117040836330d024803033402300306090a06210204050901020a0903065106050406051303081c060501080708040803040204 57
    0x100c1420196036540710503903c041c0041220303031444140119100f10b14a2a0003409550b4500d8481d58442e2080c460b00b441c5803900415041403130451a115003c002514541d1400544c2400110381054004860508040d81c60700504885105c111040d158261031b00d44001c010003940e078418400c400030300c600301d4004000021040324005840054449101e941c10b0654002840c0f4180b160703103400150b611140000c3d0b00040301540c460100b01400410000b412410494105034000750081d501245650312105c2c000d508034440080581003201984604c415442c0c50300642c0e402c0b07406503000b145464180e08008051403880e000c050306107600c0c1d000324040c0c101040b50944954646001050340010303850303030320b54010f9444604240e005030440003001c4c070604c01d100e60b4004c5580741e0b104c0616003881c0c4241650300307411031805107068030305009000010441150013030504c40c0c900d24502c05000c1c42c0c44002d100300c810f01d81086d81002200d208006280d41c10805903a04903420980c9561a680d40d4030004000d = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 992965755 1250 992964505 992964547
    0x1c080706060e340f120203150901230607140601030f03170f070c06060e0f060a0905060105090906040b03070b0d0b030a0c050d2a090b01170408 63
    0x503407850480009046040884124002e1040920748180701c24101c060700031168034644048000704400812840442c0548071039108000390b0305101d544255011800000c0345c0085454111a5801c40e030302c03071600d1910000f41070152540d42c080b4642c2607240c0c904002616511400e2070700421000800c0c00038040d410340010064241a4200c3e0000d42c0c4a190035601c5625400080700450411100c84600c14034800116118801c00001030b4002c3d41c0d0014200c4144840c4001607034074540d80c1402150360071641021520070300040000481c64100082844140082d0343e000354481c502d000217202d440c2e07a000e0121a02c40d142181c8d105210303100c40340094010503c1c0f0a86079070502c1906400103403860300d44041d0503100038407601008410420428540c4400c1c103184010188051500f05205900e0300c1138840d2001c5026424014801501c24100402441500103100c1c210054440822000c1058010100080000e10300128400d0100321036002400024000070002da501180810007000d010700c400e10 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 992967005 1250 992965755 992965763
    0x3b090a0602130e0105061c0209013606080403021b01120c030506011e021005070e1804050d0509030303240d0b041406070c1202190821061c0807 63
    0x256070144100344001c00901c0f88100000f80d8031080000a19113000416a00141d031442061003200a8425a000003503001c05205030500402481480d02180c0d0b01c0c900b03480d07249000c0c0c41c3d031805990740c068502e800402ca500400410600004100001c0d41c08651030121200b014414814080d030140140d4610454402d10785020703190000400c4001d501d90007ca02410007a01d41aa0551030b0b0301d03602c1c080c4010440034401583c0500040b1100319125404158480c40b02d140c008000081d0700001a04c0e4100008070407603201c01304013400b052140c00d10a841d100c072010705042d40780115030804642c8074003004210400302c2910710680b02d02003440001d58250f40c980206120b103100210319010729802c00603901941d50000c1c24000d0400c130100003806a0080c400c0c0d0b100e02c440320b001540d8a00500504090080840c000c295800703081316901a40e03440558800c010386903c1d208401d28403480e400d0940d400c1c03a1148040b1b4280025600c0300340e0340c840d4070000350a80480003005c03814807802c1441060070042c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 992968255 1250 992967005 992967007
    0x303091106182b02060304080f03010b030106260f070309081c0e0613080c0c1003270c060309080f0304060c0f0207030201080105040e011d073b090a0602 67
    0x300c602c00034900b1605541103462074600a02000d00501000043c644040007000c0039103001c001d480c14201955000d446250802c2c03400d50706074042c05a40e0400ea100a036803180200040c0031803a00004543c1951440020180c0101e581f0f030075101c02000040d100d40c0c10f2042c424081291284247c00c80400c442e0400d200c01d954900850b956000070304022651603075280341410101542402203242c03406082c28a40f980000006611800d940340d100342c0710f4039942e1180c030582c0030103501c46112a100004042e2000504520314030403000f0030041d0601024480450001c1030300003d41300049802c10707604180340c0000c00041901e00340300c4902c20222800c0302d4203400700801003001b0b1190414030b0507200954908229041e2640280d9941e13003180402400b191140e401032142c0d05081e4410700e05800b040002041070340201900900360fa10581c00d1040603045403506202d0084d8a10480d1206000c400842886034204141011041400402102481306560100c2c40b80c140c01c111004405070082c00071 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 992969505 1250 992968255 992968267
    0x108012709051005011511010618020903031c09060b040504020109060e011b0b01030201021e030f0f0906071a010503070521010e03030f2703090904080f0409020706180503070303091106 81
    0x8220300c4030b1103800000001c00d82c0551f02e0b01d54030b042c058601229108002250076249011078000a90461440c194140c8014803a521480c004010010040b00450000003020f01c0355003002c0d4261740c10041070601a909080038000140d03485040f50044403482d01c5d00040410000c00101d405100806000a209001c03c3c051800d2045441d079060480e4030036002c0307a0400b412030f0f403001c0310810080b1444925130020b0080d41c000748083e01c02841403481d4002c0c410b01d40240a000201c26030081101a11040145807500c10201d000178545400341c502240206046480c2800207403070300c1050f94181e03220056805088424041c00d41000352801400010b4a0702d030b14000c40c1030002403004588105241141003c0956010304c00d00130b80a0741c0c42060041d52404031400c091000302040600101c4030700b1001c11100400303d6005002d48050a2044800360361490681040e030207480c01103c01d14181c460b404540c0380001c1c000001ca070655a8981004039400095050021410180154858101c074001405e = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 992970755 1250 992969505 992969519
    0x31211070b0906130209040b070306090c020f1e070b0d0e01060b13141c11060a02030a080a0209090402150c0d03050103120c0302030a05220e0105010801270905100501 73
    0x180900c500b0864080756030075900c1c100004094005014080d4221010b1400b10f4003140811000740c0d840207880c01c012441c0c40d81d480c41c45086a601e0105000140c1150150a041c14018040d01500d030150081070100440c1450106031901c1080c419400d040c1c500041e01f030710304212a0441d203130081881000f00091680e411a03810b2a03800b00a6031100170700c0021000c00c03c6102c00580c8100c0c010041c3c001130381d850720040036000d4100040422b407010032098041c00d0040c0d54140c001c040c00910740e40130310f807600d0040358081c0042e80f000c0c1502d0705081c0144807000d00743d00c4603003071030790f1058046841c4403440d07810540700c049034424041100030f40d004880400700c107150513400c1181201d1050341e4140081100c07440841b582e0200110080040e0400c00000040303900c80da0113801481c40d0240c20060030100103010058074001d40c1d2001d000d00c80c00100400066030415451401055514942d04400000d4076016600f00f64100c212503106654034002c6003400070800480d0183c00444408020650b11021 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 992972005 1250 992970755 992970773
    0x30c0201230f0903031b1c11041e05031b060d090b041109070c020f030c0a030c081c0f0c1a13062412051908040603060b0f0703121107 59
    0xb60501041d00ca880100314011400001c03a0302c10100d0040a20203110444446051988110a034002404a07002c505146010a1182150000900700b02a507075501d0025940710840a010b6641922380700303820304000b03d80303003c10300b00444002001d01c07403414010a0002040c3c1d000300ca59811156261a00d550204414405080c6c0164016548690a002c5039401c001610500b02d44140000301c00740810401810202d900b081202c03030040075202101e81c10b00c0072408444ca564400e6400c0126030204001c2c090041c4107076910550500c441d10b282400302100a04501041c004030300820003d134100b84d060048000b410150130381e5007280d05110f4140709181200f01c010380002078401510304000c5810034040c1c3c0c40c0d50081214994814480340d8500401b003890403d85020a8880d030003400f00d4500b1021030f564494030903074070498a05031560f041620081c215483c64200f0000d090703007000408000581482a240903a615291656101c49004945d601601000031504403130f14000c54481c0070000482 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 992973255 1250 992972005 992972011
    0xf1a13121818020c2e02030103030509091005032d01060b03131b060215160c0f0f02150a0e030604020a260f100f110a140712110d0206090607030c020123 67
    0x9403412171924903c03550344040380b1003031100801281e010000a1080d003003c50005601c1620f001c80017942c555100042401c2c1010318546032202c507241c090074000c2200b01c8401e407010405007002084854104000c0c02d10794840a030048074002400300c0180100110043e458007100d07282c1041c901400d5030ba10703001e969a450000160115500503002500341880b00340c103144241030580d0748000c64031032502d0f0350380302440c802e10649020100e51140d20240e1200c13201b048015200c48100e503a5142c21540041811002601c4a0720030741003402403101580d2464a0001512081003808850300c01da4030b0400404807003c03280360b02e81e026000b14048640d0300400d10a1941300c0440051166030b041d84d4102c411143d0000180c2e45001c41031040180c480d01c56280040c0b5940300c1c0391400e141081c5030700e40c001c440040343c03823100004a402c000e200000d003090103414194070f40341c0010300d258144101201d444410044c1801d041542c0c942d2100c141c00d101350840c03480d1414003250b100e20800c40440086c4540380c11 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 992974505 1250 992973255 992973313
    0x2060717040321031a0915040207080a0905130506031518060f010810180f05031308030301170f1b0109050a0e161b0f1a13121818020c 59
    0x940217030314142102c3c0c4550107008010b110000316981c2032414070034800029015500a5400e215010015400380010003001e01c09882d8502c000e0300e41020800781e074080900e12269241001c0620509442c00034103101c5404017845c403660075035211001100140032030507940005100d0700e4140044190240c400301d0607182c500b02070720b007070030030070311300a01592464104640b40711461082c2d04041403145294841c4141b080c000d8031301e841c010000c0c0014155007a0003801071754000000400c102c402c0222400142a80c07800681000050b016035030751a210058903e00258807000700702c04940c1e02c00c034194409020b0003000c1c4a00075454500c110410901142c1a00450310090f100400050140c8441040227030700311500855542c00d56100720702c0301c07035408003104e24802e14115290711510350629188075001c0b001c21102941d059060001648856849590502c100c0c43d4038140c0e4900541d0f482e41c1550000701e1038024950310f0265180003072140303602070f100714001c881c880189181c0d0310007810803030480 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 992975755 1250 992974505 992974511
    0x503060f0303070b190e0a2904061e090206071101031b020102071707120e01050706291e010e130c082a0d09030207080f030901030510030206071704032103 68
    0x2005034845c0032a00c40d8902900c8030380c842c800120005943d81004100030003540080310032821500c246040382c80d03040c3e43c11038081d51603540460400c0e1010756a0b0b80d004101c11014003a200094000c26010b10074400060131440308500401c030113034000d0b080a0001005549208030244c91200000e0003500000030841e1141680e1074100c0c070015003441504d100540041800610f0208c00c0b100350340040c1a071000354140b020074850407002c1025482500300300d1034544418030351132030302c18100c00c2501c0c0140031280c03003440c1848035030f40c401442e1074224031131640c2800c01280403030280c40010404d800c3c5c81e2882c0d007140e0510144854041d4090080d40c0100d40c03014080784640923125488044603a0308624a200c40e00038044040e014145411188410b40039006684425860740003c50404400e000c80c1c0202e9400000c0064095031b241c40b405030302628541c96180c050341194001541446224400350803005480c15203034031160120100c070000c40c0d00000d511801580c00b40c86542032248064044e0110385 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 992977005 1250 992975755 992975791
    0xf06030902030c03030403051509010e060103030504090e0604050309010c051015030b01081b010c1a010e090708030c07092c070608132a030b0a0605121c0503060f0303070b 75
    0x4000051b1801d40354010080c100303060702401c0800b405900100284465900d4448000248606000c00303800780d8002e079981a034590420742c9950a6174401c9900c42d07002d034011400c000200c3c0300803080d990729410910b4080384214150400c203180c040c22494000ca81403402e1a01400c1c051807000c000100d230320445048000743e91300c02c19643c9070207100440084800b050003440565610904881554903c24550b2560100944d074580340c244c1001d812000d54080b610b414040003507400c10110009010400041d0b00e04000b00d02002d44034822841006034035900c60080c810607242d0309410248081c200e60007401c404a203490401ea03034051603c606008681c0307800c00700d11000b0041d42061855500200404c4e8805505a117409540e100360301180054011300307802000040305800858010340488401141c02e900f40404c20500d800300107260f0b95268445d50441a40c840302444103030440405080c0f042c0c4a136244000f01d4038041d40d08401c2075160100084003410022041d039038500521a00c061a52141c1c = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 992978255 1250 992977005 992977009
    0xc10050d1d06090d052b0c0201050103031b1709011115010e0f0606181f0315060507031b08130e0a060801060807121104050112060f150506070c0f06030902030c 70
    0x1107241e20b0750000b42c5c20814a000c080d078000311542e0318601552501400c111403404a011900070700c482070b0040c1d4590004005160307100201d10307100100e0201c0c2d480e4107141e0b50355840c81e0354000d00b812127000c400400c1203555070380140e103126049a00907090b1501c11185810040c50b00c402405403002c1c0f00b4a00c00451158460040a988281c40150a441ca820b2001500b508003050a00555600404100d0840d81c1c68503440c001d00c1542c00c042d20040f40640804c48a2406c1030140d40012003044002d00c11000404e0748007400c00f8500300145070700c0c0320704812818400224880e610a1184031425080b00084c20840c10b01c4c11481448031840c10840e0503202c40c001401d0301c45603c90015264401542449618411105074018070b124603074200190500002003001d44100b60711040704200b1456810041c406c1c18002d00c04001a010003c0010329001c0800449a180b64050640140300101d04082000740c241d18040c0176142960000200075554140100944182c15049009000c3e241d5004424 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 992979505 1250 992978255 992978263
    0xf0308101505160c090c03050c0c03030106081803070809040b010e062a010507030212072c0310050108030904060503070e0430170f090c10050d1d0609 66
    0x598140400d820303040c001001c0c1154140c10203000c641001c000d103103003d00000c0d0704e101068024585000c0105016901040150480f04001d0540384c81c50805c000c5000c1c101e001001712415503189003460346041d146c0705c514000350800040e030816203100000e0b08409125090029214050049800303001e0440340d1070045985006200100d50840300512411894a0b0004141c0030b09003c4d029a0a1403030500281440c2500d6060350000c1c00b09074001038010042105003041c5038081da0505160100d4403c403900103030032580c4090140c00c0a030082c00707581d1444d9014003100001d400c00f060180071f00d58441c41d802e9100da002d1aa100e20803441c103000040d00d03003404200b450171076480b51490891699103855240c58224210340e030100000c80402e003080d4111207214034541d881d40990b0382e0f086042851004d00c12441e000fa04424160600c9001c012030032400155007200c80c82c0556810401c3d44854905542501071002c000f0019810000d100d000d0300d203111140d071a644070340d100310344c1191500c400280c0c07a = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 992980755 1250 992979505 992979509
    0x605090a0e0a0216150c050f030621063117031503070f030c1a0717130605120f070206071803060c0302030a0c30090b040f030810 57
    0x44a09154100484200150790a50010401902528001d00c2403561a46080c02c03500132281c401c596000390f40c000c1310300d11035407950503140d003401803411107071000706d40550000030a114884d01841c2d251181d00f20054416103140d0340301e4000c80d901805c003140c2d1a040c1142a4a001c106903070400c014007090f58181c0140c9912035007000041d8000403030998010450f030310062002c0c0002803080d581c5000c0703031010881c0d900100b18140388680c080b421880c00300c1d000c00c4240c1c070001c0205116149149440030110072541000da214101d185e411413154104001c0c1d000300d600c00703042402c200c88001400c45c1c21000425114140d80d401d0380b802c1e90352400c3d0100524080d94847c0059101400160302a80108031602480c510b412104860950f41c0d9503000a48000364800f4001070380100030310010008034000c0003a109014100140c13050351740d038a68104298001356403c00075108076480c3c40c03200b00e950f01c008241a00075504078507034500303428030080e03282001d03008800003244100091180402009041c00b = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 992982005 1250 992980755 992980759
    0x4021e0310110a17101a0c0d020706031802011713060203090d18030507051c30030e0606060906070605010305160909030824040e01060614090d0212070e0c07020a060509 74
    0x55040e0406c03050150038200d450351003480c000c0400c8601c003000c104004030303441412564000c0400500707140008064600e0202c626502c0902c81c01660b005038ac001c0207a200c41c200c07034202c14120342e0f1250034105c4d0002000304003904840c800000d100c12000081980d01d55a800c07034490015041d00c07201a004504240d05c0090701701c2e08070348800d100929012000c0c1205010b46441034038050303002e440c3ca6001c0003140310b070b03150030500100403100b44030f900c5016840c0103512814208081c40c2c04001d495160100148250b05c50030700010300000d40c1e5a00402d0307038a01c40d0045004c110b19a100e10b032850369200c1d0f61449042d856006480000c0c0405180030703840701589c3c55a6940c50944482c14900e60f492040e001d0950150075803160000c168883e4440d585801d44804004600382c0d01d40f034409030018884101c4035240030020091965a0384030300c80c1c5100d90543c142e500303c035403010948a140c00c118a90300315482c00711062084c062899800e40c041c281c158000c807900e4040b01e031b0303a8005403081e10030021095 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 992983255 1250 992982005 992982031
    0x4020a060809030c1b27010e0702010e0f01060326040b03181b0a0b13050d03030b06040e160f0f0c0201110d1709010504021e0310110a17 60
    0x102405108040c03094022000c1803c880c10f0040a9030150f00f42515681c0e0708a691400d0110940545400c941d007124051455421100900080034460611101401540c19004060b0045542d4510075801030b44001002c00680d05080c1e201e0441d6800303048148401d50b01082c4a03240a0801014460b0303403803100140c1d5107110b2800380307880140551900700600c68104024120061420020140001c51081c0100c04660405c0060343d01000320000b40341c1c01c011003901090000f1000560440ca150085d900116a0898943e1240c5022805401c0e510f150603003048003c100042c0c1c1c4541e00003004e0181c036201c010b005c0440b40041c0102c0b00d0314032000300e15001038208980154058000c80410000320300600d4080c4040308407010729440c2c40700b003041010005400b41d034000c0c50000c0600e4981d41110a1000034040f508090300000c43c031030100000c607008001c03030303150030405035504001c900035410b1083d0003480381403608201c2a00503002000c0e1701c004901c020140d180115000035800e40301b40780c408192 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 992984505 1250 992983255 992983259
    0x181f0c0b0403090b0f0a02011401270608011d0c090712050a0f02040b070b0105030604051f2913090819030b03101b05160303052203050a0f050304020a 66
    0x140d00ca001010348242c0c140034803c1c1c00070503400750302c0000b010000c0c8141c820783d51301c00c0d0f001c000a0031640f1300003c90700c01d0014040140070582c08000b1410780400742d0b03a6607041180601181134020226940940c040d90301e08207119104d4180181108002d07040101940c540f189400305004d0750000880c0d4442c0050041c803281801c00215900480d08003181c9000000e0009030102c4610880e48940c00100310310101044400411004084546c05010142c0152049080c60b03035685030f580494000d10750121405450b45440560030303601c0010030030980d4002181e000d592a0401201e0741045010500840006500d01c00c0d41440e40204165107034070000052400100000c0800300b41600514001019107541c02c060003558108000390102100c4280042c0d071200384c081c5202c07101c40310742100003484420720680c0b010f01c500c2e00401149a03054240030034183c0d100224817540e84c5006001d803030203d04100e000d070241a4040003416404105441d003810603c03895500380e0701404111402507000da102d00c41 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 992985611 1106 992984505 992984513
    0xa0e040f06050a1e090b0d240c030c0e04150302090118061d16030905030c0106080f0c1507020604050a03080c01061d06040e12181f0c 59
    0xc41c9002640040034840c0d145a44140317020325079104040d140e65121030f14460311655000d5038924404a10035541045c0c4a50040703034019061821496486441c0a44101040c4a10544600f40812804010400a48800065418011010b46000005861320600d6902a00300004032480383d0b0025111001220499070008850151107545540546e0006101940046030b0a0440c112114201c10541c0906000c800040480c0f10008403110444010361000c003d545940065402c203c0e112036420390303505400d100199000a00c80c2040310b40341c48020040125510191186050540c1d620004844040541c0140d403035040004013003c1c410000c2c80350030081c0002c114442d04880032010741c294500d40040080e8012a0341d0b1814810311481004801c1d84080c0c1010360701d50b03403007080c038030030749407140c10712006d4014150030004108503d450043c00c0c0c40c860300d0380d40f15941d0b00c0a0f41c403 = true := by decide +kernel

theorem cover : BRFrame.Cov 992805755 992985611 := by
  have h0 := BRFrame.cov_init 992805755
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992805755 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992805755 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992805755 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992805755 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992805755 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992805755 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992805755 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992805755 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992805755 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992805755 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992805755 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992805755 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992805755 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992805755 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992805755 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992805755 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992805755 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992805755 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992805755 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992805755 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992805755 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992805755 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992805755 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992805755 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992805755 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992805755 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992805755 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992805755 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992805755 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992805755 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992805755 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992805755 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992805755 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992805755 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992805755 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992805755 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992805755 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992805755 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992805755 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992805755 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992805755 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992805755 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992805755 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992805755 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992805755 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992805755 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992805755 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992805755 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992805755 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992805755 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992805755 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992805755 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992805755 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992805755 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992805755 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992805755 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992805755 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992805755 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992805755 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992805755 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992805755 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992805755 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992805755 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992805755 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992805755 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992805755 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992805755 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992805755 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992805755 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992805755 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992805755 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992805755 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992805755 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992805755 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992805755 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992805755 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992805755 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992805755 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992805755 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992805755 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992805755 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992805755 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992805755 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992805755 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992805755 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992805755 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992805755 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992805755 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992805755 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992805755 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992805755 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992805755 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992805755 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992805755 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992805755 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992805755 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992805755 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992805755 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992805755 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992805755 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992805755 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992805755 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992805755 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992805755 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992805755 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992805755 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992805755 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992805755 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992805755 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992805755 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992805755 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992805755 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992805755 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992805755 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992805755 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992805755 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992805755 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992805755 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992805755 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992805755 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992805755 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992805755 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992805755 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992805755 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992805755 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992805755 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992805755 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992805755 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992805755 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992805755 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992805755 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992805755 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992805755 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992805755 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992805755 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992805755 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992805755 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992805755 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992805755 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992805755 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992805755 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992805755 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992805755 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 992805755 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 992805755 ≤ n) (h2 : n < 992985611) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
