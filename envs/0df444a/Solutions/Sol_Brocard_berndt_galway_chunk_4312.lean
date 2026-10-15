-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4312
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T12:12:55.042526+00:00
-- url     : https://prove2.me/submissions/0beba9e0-d07b-401f-8ce8-2a5f1db8f760

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 775359712 ≤ n < 775539568 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 775360962 1250 775359712 775359719
    0x114040522050a1103061e090c1908060913030e0301050703150801021c050403020f16030c05040209150309190b0609060102030a0203090d170a0f090906081005040c03050303040804 79
    0x781c0a110340c41901c1c8001000111031100c07141000e44801072a96110b14074200c1702903110601e032041c000c000c1ca000780544407985822a620069503220304420f46031503500301e280f5407c851044001921a150143c031414003910b403403e0502c0a0100e00301d0032400e0003070f207003003541d4151001d00c0744910543c1c1c40d47d00803a010103c1c40455003150710b00c0e000015264010055028140c0f407803000340d098810242c0300080c0540d102d04080381000200600412140100d4550803a151403030003500f003e86c0c0c013807415002010356a1042000701c1c842c88000030f4000709485410785520700000043d550209000b425074480103010440000b0011107060300721a1604944203002c205e040056015a01140a00095203041c5401e080a5681d02841e01114032511620392200100300c000c600c482e14200802c0605a01e40041c3d80c07000d8106a0000d040344001354018000203805121801454103c078800d8000e850040802000000500700042050700c1d01c80c0c41d01e50000021b00c0400040d442140030300f03c5580c440d401c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 775362212 1250 775360962 775361029
    0x905070e0a06020d0e0d150b0a1a0913090c030f0c0f060806040911130905060f010b03010b070f020603071d031207030e0303041e080d17070c050c040e01060e0606040b0901140405 78
    0x80c0d007000d003c0458100d07004ac4c83c0ea03540c030115000a0400c44480100e5440c9600100107003003114001850026a480d0020130080050081d03624a885900d001e80789603160f0a000820915a1040e00d002901c3d0300085409410140d0028440a0042d000c21160f10040300100b07002d803980f507200c104441d58603040d01003400001e100040d00042003040300203181d4907103603800449010600402da104940080c020b0708005090103141c2000c3d40c068207480d140e00d02004050100280c1d144481c0c1c6005034503d600441e442c0100b031514212031000d508506000081c1c0301280e00c0400d10b151550113100800000c03800507524000c42003442c91031020122400d0406001c00c1c1410f60752030388041840b094010301a0098410020383e40d000c1c0c11441c0403180b040c03e5050030f03032801c4844a826900b20b8505800e2011100c03064004c02c0655090030442405500d5200510810748604d104180354150188000c55480d8828040306494004080d1854182601e440c002014a025155580c8085c007081984202c42d02c2c = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 775363462 1250 775362212 775362229
    0x1080a05010f06051f0203090d030305060306072c04091704080f010c14070204150305011a011d04050601050d0515100c030c2a0905070e0a06020d0e0d150b 68
    0x1104881840710700d1030040485c284184940e10b00c90002030103a00608800d20070030994a555000804c1c00081d103180e41405002044117480c041d0090060308001036040d4003a61020004912005081c10700c1c400780407190350358441000c9803503070003038075808600e010400707a400407214070b11002486683ca91a0041035464682c21807003038040c907414001400e402a400510a6500000b8000700c15901c4040d0b00c0024011721196004501102940390f000c000d01c4015809081200c0c0700104294425a01400544101204001a03024850b203180050090708040e003115401c03840606005d41800395041000c030a441d800c072840206d08e0f00c440d0a04840d440c01c0d20460000a0f190705001c204070b04143c40081c41c001090308080c1400c00c1036084503080c184001d1018186441e41401402400d0f10f4003010717000b40070f003560001c0005100a07446401442c089140c80d048a045400034001c4180c0c8040645503440d50301c03035242d80300d008580880c003c83d506000c180c80c4a800000d000035500006810000b403003 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 775364712 1250 775363462 775363481
    0x60d0e070f08060a050a0b06070c06030f140c0d0902030d022109130b15040e010801060905010503031c020d0e0609070b03090c0904050a0203240c1204030e0f040501080a0501 76
    0x1404114070800c840e06012400980190030400d004c22160303078040309840544a256020b6030003c100107001814015500d0240c800c0e10b0490703609102c618001842481a680511004040e40d0900004500e55030510030040c0000c0030b03240004614034855400207424084110003450140e0444100c49002030444e550358252662054202410014210041541440000c0300d8800d001d540d1a003000030780d650b4003030720005181c00c09151b80e0340710b488880704000c1900c203120b82c9080e58201503012525103403d00441d0306886000e001541003111882509007800300c0d1603c1c183c445030f42000f6034a0590042c7c0540100011000024080c9040a2040c140340819035800b221800c20140288100c1c2100400c1460100e841150346180c2c40d207072070403c20f003003104c80b5100a40c184280103040c026040a0240058100007020405a9a41d01c040d0018030b144546112280d12044d81d02c0001c0000740221102d010707048000e010f840740b004480380480c089580c2a08142c03855804010070008003c400d00034500c1c0b4 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 775365962 1250 775364712 775364729
    0x11506120605180c1b0303070f1404030f0b0408090a240206070f0f02150717090d05030c0304080d1d010b0103020903070608060d0c14010f0305041203020c010b060d0e07 74
    0x42c1d003502e08034100c1e0340fa405402902c0120300014201440055550010400c403c00d10940380e03682880000646401a81101400841c0c5803040a448c8608280b0540d02201d820026008441200d0750b22251450b03002042140d04803001e01040ca40d90b2034100c4000c020380b0301d04071071310500e460090003100d0741000d6081a20440d8452001c00520310742c482d50310311040b0340342d003081011305140e0300b4260700b1301800b25140004039000c2d40404c0b074450b901c028100d4044840ea050080541c980280302c6071100041026240410403c01c003103411039000c44001d41d48903010705005401c1020248164007528801111105250280080c4400d000402c2c03043c4038210b032003400e0031850b00e40c4e03810200381c440585210b00003d01c118000010103545072980705121065001030540c01d440d48511b04031080900c0190414002050045a004540e01078840e00c0d000d40c2d00300d2040408030002e0b1000b00d002c0c0d130200c240e010155417039030780c424507580f40c02c2e000e85540081c81c1c0000c0340c0c040c2a018450303c2c048840c1d01c00a00c = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 775367212 1250 775365962 775365979
    0x2012003160308061e060a030b0621090604410d0801050d0c05060a032c0d09061205040204110408061503150a05040c052106010b040605160203011506120605 69
    0x1204100b40b45c012000200c15101141c580003113100a400410001008503086980012035001642000c11040154190700980b25040d0326100411a51190f08540050080b41c1c00303007080751010007412240142c2e188004051864440f030018200710b03165401442405035001d502003003052a00004020301600c02660341c2c03d2240301d10303141c80d003001c481446842d0003030000086c00406240310390012052300ba0304500341042500c0a07540b0800c040c030914244401d0f40a005454144680300f040403208459480c2d94a0f401091040440c0008000c0600b08a9010340d450305004030f41e808910140000345041006000e0306d1400705a0312840118900c40309101e500b2a038140311469041007081038200d4040c8100046c595100e16000504c61040e070080ca41c0010380500d4180f04038035984101199200e130703906850660b603965020100c14041e0f802104013141d818001401c0040c058641c1d15a1903000600214078000d280b07020001ca82090b401250004000241500001c40140200f0307008010965030f804 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 775368462 1250 775367212 775367239
    0xa051b0303070206071a340f030b28050108090c0904080a091a0d0b0a06021b010345030801090e0a0b161701050d0201200316030806 58
    0xd0700c0b4030038148028400c1c503010030b800083c820365040c10258003121403085c4d40c0d241044511298a034010143e4480c120705030300000e110302c051041828146801c15113850f80f0861600070168094a088103500745c00001d021140034948004c00c1581c28448034030f080e040709550402000510341a001080c20a15078000c00f0035480359210718013040d5000340c21a2019444111808080320803902c00ea00c17400b6982c620140e0020480e0307495005001001e107068040100c49444418010340c4803052241e0300268000280c02d040f00072000c03e040d10745035014500080c10482d082001d00701d004010521035902c0c3e00106c612150315641e041400300c0d240c0e25080e1407241225503030340100b82020501503542c820b038494501002180041018440031944030814955a20f4034151002241d1031a1465500103800c0049807101d46103040710135410313140054203030400c0c600e8980054810b605c07500c6a510121000140080d59044180084c0c030790150107030341100026403681001400d829000c0c0c07116208841e85085c2d007 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 775369712 1250 775368462 775368469
    0x110a050904020d03050a02161503050112021f03141005030601120b010b0a200c0a17030909100510121109030303070c08090402071b1502061f170a051b 66
    0x101c050745494001c0d5501d415840403401d241e1041003041c008c1481070b00114503203491404a240302c1001e0f94041145a0742c4828112510350740721400303074120b00d0a003a0600c4004a00800b00e880404030304011400f031003168121000d2440450b9400c4650300903480c1401a40b906200082c01820210700c10700308449540c88200074294107208650203828001100300585007c0c8103034040c01071081c400015a02c030482d60a60700d0710f01400c9024451b04403510080f40103d5a020440c841480e00c2000b1750511613031009002403c00090301100c04000d00e07420014540c0c0d90032070034101800007079803405000000003c44a003941d0784081050283c00003403002c480c09403400800e91790f105c105c1d8585100c9071042030034001e00034460100402d4009000164081c00d2190010522002305000c00b05d800140d583e07003400c040c0b020f03520820800140c01c030074003191038181e50003d0380861800b01c2d007509040581d2800c40340400f04207104c0345005a00400c00d05424449c061104d0000510240300780300c41030b44001e000 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 775370962 1250 775369712 775369729
    0x30408060a02090913020a120506160306210f0203010c0507110105091c14100204030312020403170d060807030f2003100903051903090c0614031303030b030a110a05090402 75
    0x59405105c0d90180281c1503540e080c9001006004014200302841c3c5e803410205e0f1100401c5600280d042c1c9030030440b286403880ba12440003210034500064413001c1c054002041e014212003011b8a01400c00512840569421721644c884200e00d501c031a55280a80e1038901180d401171050300341441818040c6580d01d8a51094088482c40c924045806074500c5251454003da8030040a0a052103124080c0345000b50580c000c2058a001e9101c003814012440595000e80c4140c1c04001c0405030310b50100c1c10b00d00c44020152410718101070000c5006034507640e949203084880da0060303402c110031603044411b011145c44002d00c01100500031900c6040d128002c07a1b590001ea44003d40c50315982c000ca01c051520030303425607007400c151180546c0034031560203005020302032002d025540c03038114101c0010010301403241101840701010865046580e410340404c2d01c0000f00f03400b5428181c6400f20704885650900c40011014404c00b54410710341720210920826070401e400c424080c007803a4080c04050b9417983e04 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 775372212 1250 775370962 775370971
    0x60c0c03040527040c050a2907150f140a1b20070b0307021501080d0c030e032a0f0d151103010e0103061404020f09070917030408060a020909 62
    0x80b54030304071890b4251040d1401c00311808540000d07500c01881300304100b00a000040f19000c6440c0c20721940c0358000740b0310403500c4000d850009030320000460204451100070304004c902483d41c001020500c10040000e450300141c440c1d180355542d650104040d03214000e07290b040740101c0410810002d00d802c3c0291041030f0f80e0010400d00a00c003900c0c83c080d00b400c1c0041c860301c00c07404044d58222a901c0b0640d07480c98106031401000b601600301c03c00d402d18040d51080d130488150900a03d000c0c20504819a420003070382030b003a41081440510303420325072801c01000d0303c0211803008100401b034921556005040401e40028421010581c141d4078503621401007091b429004612443c203000c0d025585c0700200301c294000e0741c0380d200c0400001002182980050304890180c0c40034402140f88044185100c2c03011a00254031410200401d00a03040116241e03901642a0502c121a9a1201c000d04841903803190229110341c00003034140490351041c456103410282e0598290f00b0112840d0000340000300080 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 775373462 1250 775372212 775372219
    0x3180b06060f070f060506060313030c0201090e0c3105011209140a0b06030106060f0c0501060801110c0f160b0304150c0504150e03250521060c0c030405 67
    0x1004124280d4074a400c440c65440d01d000e4042c0c0c0c074190307403074489050500381030300341d072060301e0072000540030b0405004481c814540c110b649040c0024940d01550010104441681000540e07240030445105102c4000e014000c8008100d40712100348030040700c20303071400201b613810300403100102c0b40d10070040d0141301c1900d40900b016100b505032807980b1001080c0e02c2101420b008082d01c80c80315648400304600c5031503801920312559540d01c400500d400c0e00c0061140000040481c0d00300e800ca0380c4201103c0ca41c6d05d01c104008900503940350011030940d1140d500a0f10300f04000201c0342a81c19003000030342c00306100440501400c0d685161448500a4244248502e1420000c0050100040d829001d030b290041c0708803c00c160144104010210307002402241400ba55050200f01d52600501c83c84040d800c00800815040fa40c4800c00d085450065010070751241806c000800c0da03544043c0090345148208a10140341e102c44440c880c68070201031720320081f012003006408112034000c8101ca00303581c002d6 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 775374712 1250 775373462 775373483
    0x90207110307060f080912030403050702041d03040f080f0316081c09170c0a110d080705011512050d080c120a1a1207140109330318 58
    0x1410040c4101148416540d854000c5060204060707402c1254281c1e80201541c3c0c08455549512409917128000c8500e58030100c030a01c00580040d115000505400d403010300041408416403040c4c1480089606d0081c2c4135801c0810f06224940064800b50020041003009003105a01c2c4200741e0313200c5c442d100d0a20307410710041503000d09003c5258203c1301800e8001e8500e0400c06031640e80200200302d0100216010303c40c2c0115101c00003c5103054420f140840c0d0068a0030700015a40c0f101c420001c001003503045042a4441400310719803070054841c0a00030788c008604903d028001080980d102c0d00440d620624041800c80840e4001446640090460804039556162002c0c41940d03402a0800b140e070111500c42005100120380e00a1000040c4150f094854011070b0380401c010b1400100c07805103641d0080d10100110311000e00c01021802041c1480d185280c0c882d404031034407840201c00c2e50075091403040d02c4510300914400d54000140c01c0d1508000e500038000d03c008100040b050043d240c4040d8 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 775375962 1250 775374712 775374727
    0x2d1b0501151e270b03100204030b040b0a061802130509042405070c060209060d02120907060f0504030305180a08010c090f0503070320040f1b020a05070902 68
    0x75485454140c00115103074a80580d1010207582c0701c00082c80c9115070104030200000c094044061800d1080164000103200c01c016000d4040101030035030714240d2501c110005500642d14920043c80a140610100d03441440c03d400c040340403e101600d0b1040561410344200300d641c8101c0b00b001498001d190700503170303111640f02d101c0100410a41040e9070003181c038001c0c8030422821a0320300424100840102c00e0000701030360b001c1f04031641100d00102095501e58800c0c00296507a0003000d07241e100030702e01da04090f511681141280c020044425100c27160f282804070914041050341c00a103c40d00d03103500e1400d02e0450052840c040c52000400303100300031614034080c0c0d150754140003a800000c1d01070114035a5070b245460190421024020224403a5200448c280314204503640c02d44401070700a01d6010710b19501c00303201d00d135801c0345041c00d105030f5060408a603555026500c0c483c02181c01c0407034008d601c000d1003041c5141030358082003998048801c41c2c00089001c94014110b444155005849516 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 775377212 1250 775375962 775375973
    0x16080106080a09051e152a07060203040b041716080a1e050a0e0d02150702010c0611040906090b0d020108090c04020d0f06060c0b0406020310152d1b 65
    0xd001c08004d041d070064000e07005501e001d40f8040721000c01e01c2d070211030b1075800300615030402c413000365846034840c10906074603040110000301c1e40798484540100d01e49881c0c000c0d2140750880c0c0082d101110341500c1c01081c8018454058441500181004600c80c50400710360354607040f01d400104000c00c802004078054449500030b206000c2d19134041030380741640d1041020010f00765400209540c0c013080036442ca0b410700e800d00700e011f8551213a024190940704101c07a00042d04039000220201d040000c42c031403180010309203024800002c22100b11050300c40342000c1780781082d1902904003002c074510b01039565070b95541e080c079010841170302030a080d14141c889000c3c240c1031010f064402c0350001d0000400c141c10440c980d115445444452608100703154031410100c3d5200c11450f8040c04000003140480c000c9031042d8011600451603c207208101c0355500541080c5021001031480480d48000700d100c00003000031401c1e85000303524094808450301c060000343c034401c01c403004115410b4124a60004201 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 775378462 1250 775377212 775377221
    0xf080405031c1206030b0604020c3904020319050403020f120318070b0a0f26070f030605030a140a051507121e0911040f0b0916080106080a 61
    0x20016064032180c030401c000406805030b402d0360841c00151800d6200200b40924030480c0180e03980030b103c400d01782d00c1d640308210294212851943c01c0e4000d6502082d107051007100300301d484410003032070b265910403100400078085400341c1c6454001e500400030003511030b01c1e0100f8960220841a000942c80c1c4490508a1038401e801254100d180329110045456500c8040914420003210020b00f40c00b10a005075103881c0c02c1e2034891b00c1a140300c14050500954040e0a8140c002d189a10f05012295508144655041c2c1c441c000901c0c41e10700001800700b020303070014180800300700c5410f040c0021841c1202182e520075240794040d026002003099614041d00c1802040220b60f000411144480344c2420b8002202c07006071441c102082005400c10a2109540600c9010302240c0f150b694182401c803d5085c00b03001020011505010140c441e64016502c03482906808080d1040004017100700900340101e20360007030404104405da00c020740350041e6004d030b00c007415200103140c410001d454085040c001382 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 775379712 1250 775378462 775378469
    0x314061f05190e18010b0409030f05221d060a050a0513060e01031a0a050402031504110301150f0b090303040302041509020f09153103060e030306010f02190f0804 71
    0x28108005210610745103c42051342181c10100800c40c4446440030003044942d41840200802e8411401c80b100f54080c0c070107040c5006e44010800d001014071807858030354004540000740003e240c1e5040c40c8000344100d031034aa0122094400c5400d903030402c4001058205117201e11032003036544c02a072126128141d00300000501040329103800c1ca503101e04c0c00d04420b1100a11801311441c00c1070010f01d00c01c50b5402440d0090f50041c002c3c29400b0b82420640d9408500140700340c40c204843c0c1d000f0311090b20244104043c900d00800c1d5407004600b03244002010740c0c1e90f6442888180802d00c030441c26a5004812241140d0381141c002503458148882c044050029600400c0c031184042600d002c1500c00100030a5404022500345e458250900d40e404200e005030400c02044c014541d0310300d17911002240e6543e028508641034020165a00e581e045e0995103030486c40d454070340003c0140085560440c00d8100300c41c159001a104078117503090300c034502d0300c51160301074050440c10285000348840c44040b02c000d03 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 775380962 1250 775379712 775379729
    0x51f0b06070c050301110307080f04030302040b160302010506030d12020c010b0d060219050c0a111f090e060a230411071a1b0d0209040e01060314061f0519 68
    0x100c54042c1811800c1c80901c0c07080038007035400c21266107112010f4000f1648181035a0f110ba0078076888942d070b1000e040000500490605a0800001c40c1d160b940c20040c1490001c059820400b0704483e00c0e009007520f40c0940124026800490038040346900100521a80d40940100507152610445200d0162020240040c1c0200e8070202010030701906030020300000c000713000d100c2c00452260100321001d01c20041da181068010038000d10006a50b100c1c0941d079150000e02543c2c0c44007241c100c2d004059234080528003c1000c3da107040015007400c0000503805581252460072141c904640c140811114013819001c0010b0522208d0f40b642e100d5012038003036020340c04015143d02851800011030081c0d4868507240901040005407000e01280101290140740005075041000d00d82e29880030790042d0211a9020b40c41d103007213018140e42403084500940c0240400c007001c0300314402c2c5034108140074022045184901a007030ba984e841481d5080c1c2118000e840350540c40c06046000713070315509107400c024078 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 775382212 1250 775380962 775380967
    0x1703040f05070621180206030a0605011b02010f0c29010501030509010e0c0d2612161e12110301080d0206040c260f15060d051f0b06 58
    0x2806903603200210194032400c111402039840380f1069420000241c14145503420b040380a980d544204d4001d0300ca50f030140411005070a900e50b00180305504102d5500c840596100400c001a40e40311101c4194180034000044c4881825000241342c051041244000c0c04101160401000000d0003806030940e0011030814025548211040c1048028804c00c0d00090a00d404910884418440d07000b5242050b0700500e03003400c011051004a909920007520343c11402c04244030210481d4469114607417501c800141c0e2402451090b00c0ca8407400b4000c82c4500030800003d401c415005506078004043c410305c05c0340005043c202c1140c411044050203203200f4149a52000d07590160000b442c10390f0051400d6402c20311681c00c080783e03204021100a014844500f108001031040343d48070600c0d85010004e42100441d2070811b0754606540c81d03181c06003560007032405a04401021046c01e070020000c6901c0c05100d212501c2c0c041d80e440c207522a1201143c6100040e0304040003640c020b43c04200040c1c600c94 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 775383462 1250 775382212 775382221
    0x306090302010c170f160e18070320040306180f0c05100c0302120d1401080309010813020117090f0f0f10020a080c090102030f04090b19060f08041703 66
    0x203010303000395400c3c007011070410101c4a5100003403030403052040d5140741c2c8041482d0340d01101c807038009a02900f690180401030194144546650600140300e030210881e0041b2030070806030007411100c000822441640751030300c3c0007146507000c20446d011240c0099001c640c921170342242070845590740c84005c0c003c0f0001b50000b800c101540c02d01d001100c0c4100d440255611041e40161600880b03101c00400580055445441071420280a0151108101800030300480044843c07640000d003a0041c7e4004c0e4400708500b4041d42e4001c400c142d0011040ca03200c9220303441c035130010b0480514011007440e03070100c00d0001070840c00100046512116000100c51059a078010f4203519644410000f030000d01909406a04d0030442c1d000f01c80b01c000311a0364014207a0344507904421541c205e00342d024118001000701c0040342c0080340c081d01c0900302e00000014640c2c0a0300405c00141c510740e9121030401000142040300a420915080c1500e88500303007138080d40d4440c50003c080030806945904002000300900 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 775384712 1250 775383462 775383467
    0x2100207050d020f0c0a050405040507030804240201060e0a380906090f0103031209050610050f03070503070b0d0b0409120f020708060109020a230a141201090905030403060903 77
    0x8042080042e02565602144d582c410354440d0f407110081d942040b03032810200311a0815901080c2e10500943c1542c2e01c2649903a214800355105501c100000e20301c107249001149161003100d080304525000030400030785414804170316288000c2c1403000e40346e91800940c0703c9038070303903a4142000400c0f040c003101100f680c4401044000140304046010790103110001d90a8100501281c3c05421421400c00c1103a10790399040710741c560501c6600a200351074500040029030704000c01d6000d80c0000f100440c2050920b81405240c2450b450014800d0b4400c1008002c0c42d06d010440e80305a540384082e2a40c1c407030699112201416001c0210b03070308180340604000c00e200d59038007807a020450503600c0103d2100d200804030f95132543d601410b040380d0400c000400400e002640204100c0b2443e00f4601e1443c1d0400b81c01da1101200506409103100d00003034102d40782c23075001400d10a1004402c40c2181001551000202101c0c014024032050716610241c8506101007001a01c00542e4402005d11258807140f500 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 775385962 1250 775384712 775384723
    0x60f051e030a06090513141903030b010f0c1716020619170424090b04050a0c06031802061308160504200910112e020c100504030210020705 61
    0x7a00c80951600c0c0f404180c1805500403140903881007840d050031340055488002c038003808207603415241d2003041c81f940c515084044c00d204c04075009440c000b403131103115000906201c0a04001c84104400c10b010100059640201046200c8803404142d032104115030140b0841d80700040c0c00fa50180c030110307618695403010030355601600070b5560b035210400100411000b040d80c003690024000d0380202c080101104523540348030b5246410f440301140d14642a1524981e95800b500c050303807250841c941e601c1c00e00041c40d000b440207042c903150070001c003070306400000c84038000c807000240b00301400200059000f140c44030400192000e40180d83c00c07030031600303005a0800b18910501d0700075804c10380c007041038100c0c15200c020b01e140d402e14100d00d410503000800a221aa041450040c084e0100650081d000100040c614064184400b402015501c028000c0c111903001c450403040c90041148844c0300e4000721300b404100300343d003001003031a8071585030903400d000001d024003d10790320120310103040c401d00254 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 775387212 1250 775385962 775385971
    0x7050d21060305010e07080d1b02040f0c030504050105070503010f030201140c0601290403031706130c0507050705030109020d0b09010f0c05190921020607060e07050a0b0a09060f051e03 81
    0x12551b0b45a510b24486440b002c0e01c002c0d400c0480d5800c092130300f188000300004404d01d403000300f0010340030006100b510111940d44c019034000950700c2d4200420070509201c1c150b000314003400c0107810341d0324024200302ea490048c00000d040140340036a000511000800361910b2510703100581d807583d80c441468001c00e01041001d0400907295a00040240184104860030740743c040ea141c1003c20a0740c2601120250003400300750304030406001600b40c003107403445080009c2007613545850b41c600d41d0b81846817402050341c200c40e00c240d1521b00c28000603603039009030240c0e071b50340700061891560312082d00034018050500c42d0950306041218501c40f40e0761000003068080d910504041d0b0401c00700d042180e00e4a885e01908420348981301c03c5580c800c50303000f1a9a01588010031070303844c2004503512803003644c94148520410382d0000300140280e150640d10b00004d800c1520311a07040a280303002c020034511162080f00148042d0103407030710205206000325a9145207080032900c80070740051030001a98811507 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 775388462 1250 775387212 775387241
    0x10e1605071a042f09060f0301152912070203071b031a0f19061d060a080604052d030a0c030201060803040515250803010303031107050d2106030501 65
    0x30902d090200c64960820300c402c40e03229110781020392130700340088130344c01620301d507400406603801e040c1c165400d011f88008e996071802c486564a01c4d0015807010b075403840c1603599854070381072845501c84200f407042c0c0321444091903800465407076014003a4110310070b81c4000f501500340c100d089a000e00c1040f60380c10440388a1400307003a20a2800000404d58141035915008099001e4080751800071400c5041c03210310003d5400290099640280b001c101d4030780c43c0c00001c0d00a90804014082c030303000f44000c0041800c60054000b0346403d540d00d81d01d96008036411031000780c01d0081202d84c81c1c0030720b00d101c0f01c81c0c1d19007044a03a9020a85e0024203440d810b8032044005600b0404080382003070001c0700b580c00710344011f028160a034900002a44158000c2001200100c0410154618000c0310701d4460388668000c83c8007960b254114100102590818001c4650b458401c02c42100002d04c0090310300b04c00e0300b0380d10300003074201ca90b9a40100c1c1700c001da501c0c19510310304003a004001d001065006114010042 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 775389712 1250 775388462 775388483
    0x60b1c110a03050417092224150207060f1b0c0b030402032824060f031703041a07090306021c14060120030408191a010e1605071a04 58
    0x3190b03800345c0c501c598940c2d55000100e0721141e01010404a845260703e21480002181100c5c0d01040841d600381920304025030409400b500300030f101ea940031068400902440034060031802e0030320151441c1c4079006c510342013142030181111503c07948d08620f0b07100780c0d20103410111656985030880b03d50300140d170140c0c40713401015007a0400b1300c07401d07040401c070704450680c1840541741174a80d007082c8610110100d0a0f1000c484c5a14a210703264841e580107052003100004515065080031040455980b0402c0280d007010418400401d550507010384100c500001980215a2501c0f000c4400d21510352008005030f001250100b0025043c24201c4090b441c001c80400c00a51100d1104882520130f542c032074007068032180d001d0001030094641c0e0349109034106c01c40c0c0c42e03e951100d4940c90000b09114507540c0c0002014410304100c0c03141031800620703007030041180c504d50600030610140800608803100525034180340030724140c0034070207484000782c2060641c0078500c1c1200c494540703500c0c125022524030000 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 775390962 1250 775389712 775389743
    0x14090d03030c1b0c1203030b040e0f06010f0e060d1b0e06030d1b06150e09062403070509090709050405010e0105070507031d060d150e0604060b1c110a030504 69
    0x20522501c695940105029295514110441074a09903005e4164205511503560300000d485902480c003054507048010100580702101250906006800640140c15035900030040c074150074642e00d4000d1000c07108030003038138807030b203009909002c0040d01c541c55101446000203c801c01d407940540b003030105806841c00800d810344100e401010142681644600b203500c104041200d50748001c000f0741c04101c1c0881038681340c1010008000701250064a00d41c41030040000d1040c25074a061101650300c6c0c1000314030900d8100180c0c40700c040f402214000e8402c500040d05000040210701d004181d50b1004100600301802c021703000c0c0040707402d8186190b0901c40400c4450748101e003269141034040d070fa01d080100d02a0101030b03403d50800c8902d40d100000f441b07044d080311084e1041603902807008403501ca0b581e10b00513607081607040007480503200303510740101001400651421248501b821403003440881d151010103400400916040c1540800013041950b82139815900c018050740c0140400f1955424 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 775392212 1250 775390962 775390997
    0x81f0f0f06030201180b0d0e010e07150909090b0a0c0509040f020d0606090e0a0c03060b030a09030e03032703190c0e0f10051e03030a0f17041214090d03030c 69
    0x101d0706c50f0032012002041009810005580602184070544001050020b0014883d40ca13102141c0c01c02c082075100050031100913070300100c080006203030508060114032401d803110400d0790001440400010f8440e00242a054400c3e400c864580b03800030400c0100e58440b41f1f02c400250824540c10728254031f40b20300850703503501804120b0b0032147c0200f072440803951000e280b1005045801942001c0c15118080415a051540c3c06107204444a2100044a803400c0c06d00038217031a40c040020f406134104024604040e0510103518003012020300304042d0301041c42d00072074686002e803c800448810f40314420410040500203c40480d448110825121344a503402e20105c454150340703050500e00e4038101001281041941c0480c1026035000b10030321844031202080c00d5a004007003140000c2c0c40d114041c14004d810044036450301204001c944510b18081d9203280903641c2d52559402400b41c00140c90543c1601c680c01c540c0d0702c40015090a44c41081c07494054090400703a602140410b2900024450aa4 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 775393462 1250 775392212 775392257
    0x9071e08150f0402010f031b110c0d08090123280f05191808010e010f02070803040618300c020102070501030f0b0a0305030304110109081f0f0f06030201 67
    0x4140c164070b80c03098840c0e600554480e440c01c001030081c161107440101c0030500d01400004018002d0300c54090701c2d1404c02c11641041c20b1401024499103598550a02140384041943c220b1442801c0a8445000c00042c0206220b04100e0801221350001520001c1e5840d65284d0710399010340c103987c102c030815410400d8526a503c101c54600140081c040282e40b040d40030000300d00300c60103083c510102c00241c403a240510020703412061060b03440c0c11480c200e0b05024441c1c5110510014021410414070791380b401d01a00c006000982456118200502c0c48520121400003040d88443c540d80700c48058594900304c3d04005034100880340c00700581d122401d010305d4603030b07035110750583c043c1000c82c0c1403e0041d0010604500c0300c029250351034101000ba6103813103040002030b500840046441746032501c2c4c1008419030b40131300141001254002088986030014258000080540c0050820720f03061904ca00241402e245540c20742d8100218041c1000007544140145c90007a42c0d05c4030a0030a5050200c40403 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 775394712 1250 775393462 775393471
    0x1051b0909070302041809021f1407082701021b06070303050a330f0e160e181603020c0c060304111801060908012309071e0815 56
    0x90004000c046118036022081990084040c2401420261035100080d68640b0b0f02c0c8401c04103641d0b0714882003e40c030f02000344c0d81ca00280c900100c00b4602d0845001410f076240290183c5c01200b010034000d08204404c015107400b1030000010510622002180070b000580c40c150b62409400b078220318404d07103401031206455101e4090422490310500d59000c4004080040c851001c00d651420000040005d0050005185070303901203410b025117009180043c2c480c015841031070b0201c100902040a80d5481452980c04445550308030405002d06806580b2600b446000d96400f82c3e40c1112001c010180b460028001c980350341c681e03000c80d25099001e40c124885d02190310025800411881d46500d070000c019540075102d40154603851070384c80b01060f141601d51100040c09000440140460350380b140a5200901c90740009000c3c0000d02209154000300004900c4c1c20b2902d01400561811010001900104080045034440b410510a0384590f480140185c840394000c810840b0f174176040c0d2443e0369004 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 775395962 1250 775394712 775394761
    0x18080105040206030f040204150b12010e10120606030803010b0a12050f1302010e090c0a080c13050d020609030604050d0210050615031008030a02060601090b0c0c04020c030403051c020105 82
    0x4c40e1241c450030503074400700030001c90b4001c0d21621400d240320f10038840790004040014150751940b4002c18407900380c0605800c40301d20840300c027080080080302d0103445003c03250745001c1e0100d071100710b00b0300a019114540001e0a015800800000c100c0407840c004d1000d0700c1c6690780c42c00004c50b00c441110076100183c51b42444144a500070803000c003014414007500b68414100a59245541c2000c24180c1400f2140e204010303a0100d014451250403159150b072005c0001c03c0c0701e2030448840220150080140160760080403101008021034407100c3c00c032400703040700074105c6409240918219a8541c024114440140181080c0c00d140d203a4500549020300390042001603150280a2140030356000201040e005000031079000502103070500043c011120194007402d200d1600c6400036028010a900007074044000301b02e0200241408200104421f070b0882d80541d90b89905010780d45580508e401c09800c6010740d0303000e00c0c207200307801d0403103403a048080d0000d001994440006100c80402c0d103955014 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 775397212 1250 775395962 775395967
    0x70c0311040e060a0203040203060105031603080a09170601031e02030303010b07020d0c1d0106111b121f060e01050d080d06030609080307032a140706090318080105040206 75
    0xd005050804058800038100003a5605410303885450610151481e001940d030020601007507003424003640d805404280c005240400c001c52500420020921000c4d011400114406c2000c82c45100750f000280107201500000e0310301c0074074944c0c98850038071007200c600e01a00405000620300c40c2c4210529500140514196860003500b0382e03c07a4840c0c0300803079101c1e8050110740c00180008442e01c015140c1c100e00c2820b400d40030b20b0303000b807104010380101c4140602d507000078160540000da2503014081c02001c0d1040001000d020902d8072030180e0100100b4010b06144c10750082c5101c40c0d00c02540d842d030401307009960740c03100c000c0c03d160400c0c003504d60040d88150213140031400303040c005e00071407880001c0010041e680b0f4980ca000c80e41c2e19402251701540000c02d11403560750500071417001402a00000c0c3c040c4401c1d100c08800052590480014040070403484e14016004d54241c80d080742d00001c00780300180366407500a1203100413241c0d602110700882000709286805115091003903030f001c0e08492 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 775398462 1250 775397212 775397219
    0x714010e06031009182d1118010b090411041203080c0d0507080105130522050a050d08160507231f0f0b040b0306040308042307150203070c 61
    0x901d41e4402008110307461001c0e88002845119842440ea100c21500014010b9280d41e04d85240280ea4040c41031300007020002d031082e5030140880350030495a45c400400b10303912041350302144141d01600500484d01c030244000140c400b00b00802840844011181004400c408070001c88190150303001d2080b66800c0c265203100001d01644100ea002440312001500741802000c1d03890a44004580d884e00144014004010360300b8980847d442c00e041c21441401540f41c00107908500c00d15840103c03241c0b5101201d05424448148215a1a1500141035907400c204524002e08140e0302a1885130b02d10340034285441003240700790140c5120300c0d0300003601059a22110544201000004e4110300740b8040c200c9402010107241102d03c01e5816a0780300070a03004600c08098003102c04c3c001c00341c0d001c1e900301000a4907540d000328038164490342c0360134200131f99219424502d44c1d1100320b200c0d4481c1102c1c1e40341500c2900c900050720404442e00d01c2c200c01c0e81c0d00a030742c00407600ca010703a640c02400000001800d2 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 775399712 1250 775398462 775398469
    0x8060703050705040305011104031217070503060d0c1401091505040b1e0c070e090109030504030209070519080a0f020f0306010f020c13020910030c021b03160305010c020714010e 78
    0xc54202c0c4041c80c0403400c00b912078540508440c19201e8240305540d00107410010400c103c03690800083e140d040905894059042c07031261802c00400f41c0c01048000400581556100304d2040c501c29044004071248a03110358075103c030f1240e0f5040c1103012400240d8001a10030314840c0d840c0f210817031a0b6850341820700d011141070b0180c01c440c0007401d43303481c0d00c50a02c01e0640d43d170025082c4041c9050091141518044c5800074880000e4000030059040003422000b09400c00101d4003203070350540304042140c0d03620508803001d00070203281c00144203038407000401b8240d001c0d00060080b14030180c104175800c00c5040c28000ca1094000c92400c10200788005810740d070055002c0f110043c2280150388108001800040c0e507101500c458001d0103501141c24080e03030401801c11104005541010420800c0b44403011359904109040103100c4180c000da0040b040c1c6052202194074801c81402411207500c1c0e2a10601030041c0300ca0f524010f11444100203024029004521507000c0181c441405500300c180a0 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 775400962 1250 775399712 775399721
    0xb040507050a0e03070e090114100501020c0108130605010f060e01020715050a03091209142b0c080a060b1003140c0c070e0408070215040320040b10030b0307080708060703 75
    0x75a41d141c00f41c5c103000240380007a248400d11071510030000085d003008492040350b084202401205402c1c1c00c0e50b0f804e002d00e0340c0008040b102e200090030462040d66801d10401740401c2d65884c001d182171700745000020b02c0040e420b2100203031040e68803504a070510180049a07201550702c10301d180040d4501416120b1406880100801d031038034500420406456182c100150040030341e0900040c0c0511801c201584020003c0740040340304968542081d86280340410700b210304001c4a508034007000c40040c040000c1d60040a00130044281035480400f55802e2001c000c20741c043c2d1050080f02c104c280c03220450f20070311828406400b030070740812003520b03201d8003910b06800030180c2019034400ea41002ca40381c000b69202d140708610405145503511000d00c10f0121056803404019510003040c0700a000084000103c11421180300d82001c50b0056001c0002c1d010380b0b0311759278107900080840f4000a64507490b401401c0003040a80885900c20340c5c076483c0c070359185e141d803003402a640c100e40c2c0880c1007140320f40c11 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 775402212 1250 775400962 775400987
    0xd1803140319090810090803180a0b0103080304020109050603071233080d212a0903051908090d050c12060109110c0a0b0405070909080405040b040507050a 68
    0x4507810320074070240302c007920003240c030488003c5550490304200c4100104400505101120350601c12100903a403020100d02001d0044040c40c00085103a0703545e40d03c100711014102c0c2e00b0003285c411a584d2401c1c00c030300070341c42660140d0004600e6403003c50035091400807079010301016035a29105011031061100189060020540c0d8005945800d521005c4031501c1300c00000c16000740114160b1922003003174074104982030a102400148410024401d0051009603038150035407001080c051a82c0342c000d18034010982c9000325042102e142d0a542c40e07409407200059038815021140192800300c0d003c004c102910400030a03c4900b080035510b0740c00c03d9000e02409030302c41c5088a400c915490b0000c0c1e840c190f1100449455886032004000c0000380e400b502c01c403100041601441c040c510b2910b42c6d11940e442c5006419000d102011400704581040000010542514204507244003840c0501d0294090301c2050f10075030401d001d0705503510301803013007a009000a40300c1c00d190060032070741501d90481668 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 775403462 1250 775402212 775402253
    0x2060c070525051306090b100212211611030c030d0f14010e0f07090521070b031008061b03010509090a170a030e0c0a140a090e01090201020d1803 64
    0x8400030f1180c699420385850340b10101004109241001d03440800c482c4801d5506200f4072051604450707607078020540d0b02101064181e096130381c0060820590000c003240c48004410311000302007100e124001c0a0f2004511030b0396650f00c2d20302110170f810950f28041c110883d0040d800c10804000002590340c00041d691070311610108041070a44148018024240c0c0801e003081400780c10054a900d03900c0800d40e018080d401c00001e010700b0070700821950140c0100ca908402100029149014400c00c0224010700c00711003038964900d01403500206c042200e2044400b54031504010510482101104044400c1d18081a41c1035a20f002c00700801100080c04100140c020b884402011907020745411815409100701a951403650510090407039000820b810104c0c1c001807002c02c5290f44809100089810b28000e449800711140002401da82199100e43c0d07015180c000c41c0155800706410040035035000340c0a4500c005010075054508102e02d480206140c800c9510a100091072182f40c0c0c1c42c403441c141e = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 775404712 1250 775403462 775403533
    0x4090201120903050403032703020108150d05101a100e0a0909082a100b04060e040b1005010f021009080d0f0b120f151b0403080a02060c0705 62
    0x1d40c040022207102c8041034000940000c1c0034014160400c0b6514811980c003010561a00e0301c03400d64406200081c04001e04202c0322101094035082c6001d2040010280207040451160051821580d5000610303060381072a810700412286c2c807203014039460303a00781000d130813090f48200d0b0005c103c5100ca402c80545a00c680c6009020940000380c0c4601800301c0c1c807406149994104601e101000e0380d9209600502c09008401107140d498400f042603c025116010302140c6000c029000a0190046810010b01541640c0410040c07021140d040307400354010900308030055450300d004441001d80902d12402681c0080e41080003140154010688180210030b2141040001b04100b0300b07641c40000040c25140e250314100031070789883c0c0d102603941042e00700185411070016002c0c5440d480c5d0502e803e10401102800140140102600400d042c00d916160558680d1070f490200c05580000101b0300062060b440001c0080f0204000c6a91080d08030008144990cd50999000c5144040c540c0054007441e1 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 775405962 1250 775404712 775404737
    0x1903051f14150406020703023115080f011b080f2d19050601022d01060b07080c0c0d03210f0606020109060b040204050a05090705070804060c0218070e04090201 70
    0xb0010b031018203001d501506070302d8a940100054031a010b884440c00c4001e8000c00100641c40f03610003120352400802c04144480c207280308003480c51003640085c40d42d0090070b5011f040b2441c10750100d105400b0910600300100c0009030100c1d209102240c480c80400c7c224404201c10000c00c200300c00c07800c22210100c445411070502242d510388001c0e140318030034800c292410303a12082607010701030307000e1000c0c0300405d40c00d8600e81294010889452960f180001c01c8070b41241e0800007900007101a141c0c81c00e52559902d001e01d0408040c0c2e111210a040c50701400308107800a1600e00c2d0144004c0e0b070566910b50101101c0700d40781c44001c2248420311142580c61203805980c40b601e001d504001c00c0680c000080b440d109080010545244002041c400c510400c002c1c805681c9000d90304040e00c00c00e494180c1c681e035400d48266071511509401814810010900141d0b0030f40c4455216141403080c0c8000c0c10b900401d1030303048046c5070250382250200369965102c410908080c1d00500c2c031b40d40145001c004a102 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 775407212 1250 775405962 775405999
    0xc010b031507120e2806110c0706020105010605030601032c03030a1d1209030a151a0f090105100c0c0b0a08070903030f03201903051f14 60
    0x34151090510710801104000c05140c00150745003020000c1e0506110b80030200081c00e4464890b1525002c2d01000c0c0031300a014181d4801d04d0f0110f09a01c001c0c200f210880d2040b41c080a40c00450290f0010701c5103002c04076140384103020b014125203060301e600d81075444100064000e0310065400d607042c0b50740c003c050080b5080b00085100003000d00c1c0042c681d42c4c2041400c0358182d495554000000b02100c6402c07910000000400b10000e040c0c5110b03058640c1d10410020742403512038540a482e041c240400701c111f43d81260701401c02e40c4103604401201080e000709120640f081460302c80c2e8000310072001046503051070800140d1500d010b14240c0343d001015922007801c41000c0d0844140100007244ca90400394101000d550020168101800c0e035603c0c581d00100b40030505510a0105502c800301c44441152140d144000c658019640a03142c0c06091003011918080d40e00c82d030002400c00e07010036a80c8100c201c803015180c64200c0c0142d4040c1c100f03880c0d40d00c1c0e944414442500700440b411342107841c40 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 775408462 1250 775407212 775407223
    0x605120c0c010c0c2607021908060c21061e06040b0a091707030b0a0b0402040b0408011a0103052a0d0c180b3f090c01140405030d050c010b03 62
    0x102d038480c40107007003680c2050080d4085d807018402d011540580c02c0180007942a06490500340e0441e202e0300600000c0d0302d180c1c0700c02205d038028007140c4190300c18032601000b0000a480d92604c614115584001e901003c03c8000600b41c984c140c000e0000200713046071000c0329400304401540505014900307640c907075131002564015005680080c4e074851050210350903227100e241c64842200c005061070ae04507103820021070740c050889025236541d104054070580352901550010300c0800211510740c1d42d902c4240d03000c0c01108003212044020b94114100301e6000c0e201d5240a2003d41705502075600b4001e0041d01c07040816241031601c004280041c0c00d0180c850b02400c0c03100455030b41c1d600c40201048080b1030141d0801d4100c650805c50a0055201d0040d041d010303d450240700210003004241292040807030000c405010951030340144081040080c1c1c0082c02410038003083c0d80b038401042c1d04040b54184d03406a4010640d058000381c0360452a50b100340c001d0028404d1400000521405034000a407400 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 775409712 1250 775408462 775408481
    0xf09120f051c09050f03060c121e01090f051812070302071211090c072d0210080603100b060702060906040b03070c020f0303030402030a080d09051002040305010b0a0605120c0c01 78
    0x3a0503404103000504040d00f00c5c15103020141c00520720342c140341213124804d0040307580800c0400d02d19400140c403017007010340d409680d481e200c10190940d6121181071002d0040c0039045020fa80c10000070611014410418401c1d595031040644060410031079020580c1d4003903c400e400318401d5440120300081c41070000092940b0842c4102d0401001d402484035400000f0f08079099824140a940c000c82c1e12081118003d40346990180510120303c0e0140003a2405c1c1c2c43c010f9040003200e401003140540001c0094080c0307504400711144060f04201107000e03100344103056034001c1014130400c8014181f80024014802009280340d003407e0b03d50713a0032092904211000b5000640f040300340d00035420802d00e0503c0c0c40c0400e13030140d8034500e03198003c070343d40b003144c0700000f0801200051a10024400c591242100a500c42d040d55458080c1c40d5014000e500303d40001d907400c0d4030381448070216146c070881d24030071510036031200d60411030740c0c1d411143c0440700105600702d401400c00c8140241d610030310450544 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 775410962 1250 775409712 775409717
    0x13021308010b0103060b1201150c2306060d0203100b1f0201050a2324060c0f0c01030926070212030a2a060b0f030105010e070f09120f051c 61
    0xe4160b44001070a4801c25804800c1c111030400c02e040078003104d2501c85054841c52072152000c10804601160001c01068014101079640800c9103003085920381e404240381d10007400c882150300c802d400c200282a103028002e60690100040c200010216044000d030310000401c941d440040800300d418694031020310500040c0d65600c2000303241e50451003203005650b240d8240300d000c01c0070b121989480e0740c0b0107015420350150b001e0450801606020500640b244003820041d00ca00900800940d226041130303844c8524052009044600c2d4401d105426006401603c010403001c00c81042c030407803503110210818194001c20182000d45ca41142820000b58008000d41e81d51840300c500500c0f034880700702800c100d030480a0004498038008040b960103141c02403030000340c01c402240098882c40d0035100e80c81c0c1550803e000025400642030140c2d120b24a82c0d2a140ca040f481c900046a003552180190110100b848403080c020800710100c80744120b1051045807820350908048601a00e60114001c00 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 775412212 1250 775410962 775410971
    0x1f090f050a080c07141309150e0312090105090606090405030d09030815010201063c06030203010303020d09060c080a0c0b0c040f080a080904020903030f030a0203040b070c0c051302130801 82
    0x541c043c04220700f4000744842c810407000f40c0400c000144000100020703d01281d6211307440300c020300007041540d440c582c10304542005203203079030440e00342c6035042100c11250590a220000f40c01100600580380300c1d00b65500a000159103d20400a2000e0050300503030b041e120610072184030b50f00500c203604000340640c440c4002440e02001c610f5408594480d4a8116414070f0401c0010385003031f5030094440381003da640b5122911880c500860711001c894a22003030456480300041c40b5800d0350045050324040d40c2680e1210f5810041075490324050301c41c00c03002070191442c15020446041c0131700015000b528010f4070f141c4403502e404c45900c4040c0d480061b0440c000904100c0d50a901d0000002011040090203005c040740d03c4d004400e01070390340801d0089030001104400ba6a05008075505584c0719403103691603051410440e0003d41040310200d03401450440480d45a45c000d03443c0c2c1000f40d6211034180310403030411040c0300e080c0302419001d00c5480d03000e100c1903141001942185001d407400d03d00001c0d = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 775413462 1250 775412212 775412227
    0x210a050123011401121a0d080703090e010b0702012604031d040e0304140105070b040c0504050a09050a0f0809040c2c2d060a051801021f090f050a08 65
    0x5000c0070381a0700031495001520810056660042c60f040600d401298000484d0a6081001030f801c0380454025039120704070b1241360f4104240c090141c01100c0c025a10014002d88494001030000c0d0203000300030307940d003052241c40015071252004401e4030325109400641c00c1c40c01c0e140e24032921001d40701140482c2d2a401f80204007115103500ca034040104840520000c02e61141b501e45a00ca140201c502004080b16070f004680d024004403008560710000c2e0601a103010f083c01c145460303183c01202e225604140110f4940d01caa4052502202d40000103442c011070640c1e10b00b1040c1802400855440a0900c0301301c1c0706960300d1080c0d65208850fa00e501401c0340600c4050741180d40b80f07004a0f41c221044d1207581d40a519a1998484044c240361022000521408460b008800580030380340e502c00c200041402299900138040c2680400c021401c0f0503082482005a803035690000301d40b1a01a03158201070707441a460341040c030003580240d001d090840e41a40f00d103424880ba400c801c1e901c9402c0042e044 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 775414712 1250 775413462 775413521
    0x40506060f0f101404030b0103210309170d06030606080d0e040e061308040b04180f09050d140706060b0712111515030708011b0201050402210a0501 65
    0x1030401c200e08459114104004900241c4400300103010790082246042903100403541050464000e5504905528040d60756444c04800f40c40c18680150031003034420504036041c2c2c0c0603000b181c8105a01800040300b11aa5101d6880190400000049201d031501d00000c041000c51148401070002000034004c0c40500c8007010308020001c1d00380c503026a141002540d081e64001c84e42c950070560901000000040300c0c20200c400307010f00e800400b080d078000200090f0000c000c1e503c10100945044040c82501c0809021104481c0301d044003810b1600702201c2e04821034423600f111108241d80c550f520382003000f05d803505070890f01140c02030307440c2820000e1131701c00b8040d08210280c000303c02c81ca8994240c81c07240ca02075895011803400d00a006008a02042030035110403c0080141005022120201c1c1d0f1074107001c1c00f030f0003c0c3e1311817110000e03001c0c074035800c4a00c103026591280381c0181050b9000c203800e0350f11032420006100006583d014000703d60300001c9080c040c21400d62141903000243c00715070800f6 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 775415962 1250 775414712 775414729
    0x203091c12060e09070b03060d1505010f1e060302030c1e280c0f020d0515040201110f1e01140a020405040b0d020d032a0b01031209050d0f020112020304050606 70
    0x1210f0f80108141081408076000825600303603002d00101c135880743c482c100403880c6490800b10003450f40d00d440324040101010341c2d100320304882c1c4610b428103000d9942c40e4001c00540006484c65520b03441101c050224500940045400c4a0907003884d0f40740c4900111616420401c00c4581c003020100000c0c9120300400301c5400000500c503010b43d07658140c01c102d00240c24080a458014411b0525131490415980c40c141d00c1280140c105040d40c20340c041c00100c0030440001141e049000c90390700d040c03046c208400001c4c0e5146003e030a070700600700910180c00c06140400f5540f200c0311150340f2684414082506401d140c0c0c000c1d541640c02580755401d00bc200310540d4440c0c40340c2070040304024190805690381c0070a40103019054101040030290710b01e1b02074948000a1110108240180700302c400f003040758036403a41264000c13400b0b035540d1400544216100c11046c410381d9807004995440303401080010040c283d056105040c00a5402d00703c01500c0c5c20b98204940564242d0400e00400a19003001001e = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 775417212 1250 775415962 775415969
    0x608010515041b1d060417010c02030301080d120e1e0c0105090a060509040e0d0513150801031403090a0906090e160b0d0e010f06030317040302100203091c1206 70
    0x4061000e8205280700c040403060206051080000c80d0641904650345a07801201d60386018120740e07a11b984420b9002d518428080c0302003941e40c0b81580d4004d115102100b500d06031114000940180f1904210845401194105c8080010307520361840c04a4801080400d120036180c3c100d0342856110041e1441c01d2240c140005414841c00308030341d807403540d65020140e06803051810300980740d813075a50210b0001e1150180b080d020f4411b14540840302504500a0400001000769240c610f0f91a0030380d0083d400124885031000c21102c038010310004d56401e00b00014880424100d070f08018414000071489003d03540004805944c030901030001d0800c500849000d25250310082c11030445d00f041c08209d82c0142d20402002520200388031400c900690080c66062810f80004d01c13440d0031503408580145820310045001c00c059104d00c070300a40e04030780398610564040d0060400320680c010504041d50009000c80014010b848103980015920f04440c100d15800d5a1800308140c1c0c10301140c022184c0580 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 775418462 1250 775417212 775417219
    0x108011109090403030b0a03053009150d06030c051806030a030e03010b030318090717040803070905030607030603060606020f0c040216021c0b130503030601030b0a090608010515 78
    0x1144004505228080719a818010b80760b910782541c8500b000c80007056070304200707a40a017862038000140040014854070001110f000004424407504000190941080520030384020601c1400030034509440c2d030540d401c25010040e46001d243c0304d40e0108440c61500100e602d142d51000074055810071461500d02c80c6102c445200702c0382021000139907070b0504070b000101001410301959009490a40050300742c5031010301201e48504d2124040611a0f4541c0e1312039015141d0900003c0007148034140e00c13007801090103000340050300c0e00d84400c003095000514080078440c465000041e584c9080048922801456800045088c11841d261090b100568000c0045500c1014144182d07017011074030f0313090b00c0411200169110040076074091410f0680e80b01960007500320032010074420280d80440701c4144120100fa010740c0e04c16403038504503030000d800078040d58000c0c0f00044455000354041c5900c008018100c2c4080c9580c0c140301c2007516016000054207944a03400d0180312840600e05050300ea1089 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 775419712 1250 775418462 775418471
    0xc0a0e0f06130906241b06020d02161b0501080c0306030a12051215010f050714010603050304030308060d030c0803070c0b1e1b0a080a0f060f0e06040608030414040f1b08010801 77
    0x201750061540d02a1030f0b50101207512001d1400401c40554115102c48206240554482900000c3d070203803565011010b40741c00441131160f50142202d02120016036105031544100b54541c441c80d509a41c1000700100d0305031003060040f4001c40d607001c03020024000755a441607641c641ca080c00f1148058040c0554100b00b11101019185030b0b0004101d161851b03035440d04070346429040c240070114248401c5411000d520341341c40403003070003408001407050300d01070f495a940c151120b0052001d0469400740240006001e14160000160840c0055030401c4032460502d401d00d60710307220240c0c3c44400341d071012a00800c0b401006441e0750780703034040d6174410165102c8100314030b05505d458186200c2c00e03090300104003071340700014109202c5910214900c100319504000c2261680d1000000e0142801410000103a4100213061843c250141200b0707603c1560107581490700d00740710303980400e00041c405c81d4000d0310341d0b648440c0d0303130a04d2040f130003400340760b2501380151001c41501a10140040c3c0001803d030b410f0 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 775420962 1250 775419712 775419779
    0xd090e1e041e0c140906030c22060e0711070501020d050a020f0d030f110f090405062b14010b10030c20240c0322050607080f0c0a0e0f06130906 63
    0x8115141c0040040d20368070040801d90852001c0127681c0038800c05050324101003c11821082c041c1984108080d0b100e08480e80a80c885199898010b40304d80f50059009950302c1548038464070260000402e14011510890701084529050100340740f0214006a5580c140308030503050360041184854000c0811031034642c0003104000305114406805014a032118041015078031072441e003940021180c010801604000c600c11701c0683c407203080c20382c0d60300c15074502219120010301c00c012030705000070b0624608066961080d4040c08e40b00b001c1c002840a4004400386054044260011080041000d000302d094609685895191411041c0c8010300b81d035010030054212010813242c02480509140c481410801600d03800301000c254000c2c1075000781418400d601e41c010084034001c03c8542501962640e82c0d07417450703140b402803ca00704c002404000c5c461025090000c2f043e01c8402c8003801c0c251421040140d0940c500c06540c0c01200c245984510030841a80019406c03403680d0580031060000240 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 775422212 1250 775420962 775420969
    0x17220816231509070f03050d0905040506010c021002010209040204140411040f0902030c19020102030709060816110a0204020a11060a1404020603060f0907020d090e1e041e0c140906 79
    0x2c2d0070001403101c12a0a000c1032600c60b040140c0001492403840c0099119200d1070100e440d400c01d07940d02804a0110400441c65113818084c0900c80c2506960f2001c8909581d020000090101d000440965508006071801030b140c0340000c00c043d04a00240c101407940702c0051104490010703107640b011040c01d000c00d010f1050ac1550b42c1c8101c40792107402503200d48440c00c042096100e0444138105070742c0560740c02002c05406402461242c0740503215040c540d55510410317074201800b210131444281c044501e8040c0b05000340c12958084c3c002c64129000c40a0640c041000c0342e110b4051100882e041c505080800102041010750000310b100f0b061152032030751002c12044810240000b480f8138400700004640340c03103103c03012207200001045800ca1b4101f141d40a0f40720764000244000051030600003180085424407036074050860740100e1440c07180710b4220540030f004007070030803210840c0d10808280359045445000b010540218641000180b4007036108040601e5070140030300656030b0300100301540c0c0c1d = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 775423462 1250 775422212 775422223
    0xb1017030f071202030d05010e09010b12120a030b0a29070c05040f0f050f180c06190c0609060c09080d0807050306060c0f06161722081623 61
    0x6a00a0600f1048a511001a41580503003042c40c5801450203000080d0034642101c8a4007a141c1d0300d0080080c0480c51090002c00f10b00e20038281400d0740720810480c0740d890300703000074001c840d414500010b92284010000700504072a03880154000e030302110881803510050015560020080380d0640f41c0007107696550300c00d0070280700c1d483c4640d0740c80075075820a2045810019811415076003c124626100c0744041140c5804c0c4c0b85c28501220b244e00c210311441c2c0c00103030720b20003100003401c013400c00b68814054201010240c10260402c000b521100000803114000c4400c580d20441c0c003c03401004c0d07100018117032441c0341c1c014142a0700055040320301c1d641200c2400d07040b0440d840e100385e0340d69410020421a00c142810b42c04148034080a52928160108080d4041d283c0f0320139000840340c3c180c50071101c00c0c29140312200c00104541c0459140c090001c94010442e66480c07142c1c1c07044c3c090352034032251a0040e5404210318412074203c0810010380c48003440b0040c0792500c20154529101d5151a07492 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 775424712 1250 775423462 775423477
    0x1020c01210f0e06180615011e020f030f0901170105060304110a0b0d091b0302060a030e19050c0901060203340204090c09150608160c0b1017030f 64
    0x1140d6038000c03100e00011a0304803c4059030320000b280d03658149a507040710702c8480d290020f03041b4095440404e40d859080d901441c80240d0503511405405120303081040796000300c4559005600c501c00180d80c040744140040e04050210401d800e1304d07403060000242030403547e03030302c10540008035800501c52070380c030001982e404c640c00c2070700090851100c102180740080e071500f20105104011036880fa810200742c204039042d9204140c00344101c0f00390305401050070504e010003540f01d0003c0c002662014844d6008100144416040b60030604006120000b81c1c081a8002d445c1900194850103250034808100ca0040003544025450024a000300204807500d0740b0490f0020b40c510145d84690703071040200b00403141d400410400c07a94050780707401c8100d09440d101d102c50aa04200421507282081039400040300e030680ca6811386595180012441c000d000303550355041c0501181c400c0b0220b0315a04003203124440d4440100000c1e4103100e000210310900c041a40c81c01c0d4800c010785400700101c0c0c400c0d034010 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 775425962 1250 775424712 775424777
    0x16090c080f072708070314010e1e0307150603030215041e020609060301080609071a0a0302030a1b021e07080d1809052401030e0a020910050a09090201020c01 69
    0xf14008a40030a861103641d05840003031502c0b020036204008244103007240d12407500d40e8148209103440c10700761000c420302c10303540382c0003485000c200043c0703005d450300c0050f0500306691500ba16603849900451403d003000e5883da41c3c465040c0109038040140701046e503141d0820107141d1800380d459404210f02409a1460000110701c154110345440f03050302c1e40003a0050103203449607180c4101c50f950307820480781044d00303102d007110000c0c5051000031120071400c14144180d1030038820040680c0a1342c0050300c400e003495601d0294158030b048648080149641036130203000c540c1d0000804000d1804030030b405480c140c1041d5002c001808001501400c0941d80f410600110000159860a048195480800d48604010411130340d500c1c2c003c010519400e01c6001c0b050200f41210045007181c101d4020307032120b42d10540503003016242c14000c4030740c070003038031030301401110786803c045802614a03502c2443c026444011000231982c040c0100c940c812000c0c64026020001c03400c1402c0c192690200718040c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 775427212 1250 775425962 775425977
    0x30d2d1d16141206130309120f0803220b0601090b0f090405061804301209020f0d06021201051c0303020d02090a1214060106022503020316090c080f07 66
    0x3043c0c0b1207100b00e00036504110103580c420b20b0841c194040b480712080046001642840011421094041c4c00c03d001981204850313698650b141da498103617910240800e11042098482800030041010f400c5003510b10804103e0f025061440015100e5109a0401320412005001c0e55500d454040c0c00e94855440480b4085169190980410179103014603a001500084240c1000180501c05c00c1120710b0390312042d80b124840c2c552481895201c4a1305481100007840300740c0d4258105101d4110031940c90006103951046c581100000c7e00d0a5000e56089605540100b14440e07070114050400e80103707000e843ca45602d06299012075441d4042400c010305243d030100303002c3c00d0152298191403c1c00405802402e9560300c45d42da03100b12404d040d034100c0f110145030800702e088045c04034441d81251203039001000400041c2803a110001800c0e503001e0340710072a010000015903420808400c50030180c00c0826a21800c01c0e0002c010750740c1a0b15402d0601c00101d051228450302107240a81c0441c0e2803400c2c04 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 775428462 1250 775427212 775427249
    0x906071b0602070b0903191404090c1101020a020f010b0607080a05070f06060e0105040e0106030b221523010509130501020d0c03050612070305030d2d1d16 68
    0x3e0090b82c00c00380c40720401c441000070b5142c0c000003c04c0701e408194100140c850010004031130019010559880c0c0181c207110800c100c4000c3c0d009034134072180b1400c21045410a480c440d500b280c0180140300c006a00850361007280c4182881241d1048005840140c98842e00c1c2d21165410300c1b848000c1c10030484001050010f0090441030840382541c00b440c00e2001580c2c801549010b50402e01a2520a40c81c2000e80801c244052040340101d0390700c400d2514440e6544002e90b100c242c0d8141c50b4140f100181d043e1440062018200c2580c01d003c03621000030044108260255010080a030001001008000610040da10060999480307031483d0781c0501102800e25040b80603018a001500321181400c24152105800d901300601c500d002341d400f8001900c21807055680c0380282d00c00503000303420070004280184400d804c1840c0722140e240d00c0803000c0c00050621180d640406c5110b21180d07665001c00c17071080d40c2e561f000c1404c40390748034024010007403100142158400c0354402e43c3c050010041125 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 775429712 1250 775428462 775428473
    0xe030309120f1b030306130905070b0903012301060e030d120c03020708030a090b0901090305040e070207050319201f21230c0a08040309050d03170906071b 68
    0x107074411100b01c410079a10102c918100e944d240c2050315070394410000305135a04c00c070640d24441c0d680c1e0590060000c2110900e0301d080c000081c0d020202041e015502c551251045102e40101440d4020780c0a214a40c2c40d85094401803552400c0e01740a07200f074001c001e500000542c801c1115420108520b0002040340304510240d0007881000c0c00241100d002000300004504503034042d1034018010a021000c07656a2001c0d10700701c5035860402404503105020074001041c211000f2644003006004480b8120340b1100028900500000c541c1c2d00c0c202030078031a80c03c00403103c00c0540f01010701155198181c00c0d590000c1c458140b24200d02a00700c3e110440301d0403007481001d401c00049500d20b580080c0448041d1a58054507200001c1c901d6120303000d2644c140b1200500406210707003c925141414481c0c586c1085a68000281c015401c102c0c4940011516954103882007800034803988810132007050100c03003c1500341d001010720946030819800c121100f900260340090a030244911584020400e1824 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 775430962 1250 775429712 775429717
    0x120403080c0d0c030c0311090d0b040606050a291213061515020f060c04060804080408012c07050102060606071704030302010c09080601050d060e0a1407090e030309120f 74
    0x40011280c01c01c06207150f9250181d204c107110f5441c0e0b40d0184121080707420843d081d0702c40d4070034841d00040051101008240c03522100ca0f0802d1056201080300c3d540d4100088100c2c07440e41110302e001844407500000542d0320400c02140300f000e80e41d013030b05210000380803980c0320304e0041c000308102046200100c200102c41c0d20130144c4440c0c40e241701c401c15442c1c0c910308400b0415811114003500c0b4402e00480c2c2e240c00054a030f8802d04802014900c4e040c1003920894400714090000c980441d4107106c0400c05103001c1c0581c84440d0705c510114480c41900c0d6010b02d105075280302c6210480c0c0c03c0104c0c144074599010038551350101058801c560b88510030300d815108003400d00718041c00d4013030115000c01007540c10340010070300c00b0441e61000c02054603200017a40342c400a100d415402180d140c03882000400d603800035050440d01d60151b600e440710726190b0b4400c0551800071024146c0180b8010302c182c4450303106055615503401c00560861030110803069690360b002d40c0000034480042000c0a42030b103090308 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 775432212 1250 775430962 775430977
    0x90609060d02100e180c090f060c010204030f060609020c0c19080106080616080f160c020603041b0909051e07050604080a03080a0902030c040c0212071406060105120403080c 76
    0x42122142803511004010f0b0300e9901300ba5200b4100c2e00c400394100200a4500d0340a0076106144a280c0b5149000300420500300740810381d0006414006484002c100703101900044d405100c84038441585898504100c6e40300f60003608030284140305d0241003501c0000e500311402000d54501d500d410140314001103502943e40300c803000c0c1d8240f006c0481c20f2079010516074001d80201b8148140c40c8481c0d40d040e80d40d00c030b04440300d0030040440700002e0070554a0882340065401242081c1e07003684165000300e041070384211015100396140c86007440c513a040c2040c001c0000d04d60b14504108000040e900d45441c0c001444003488040000100503004030400e01441d0300802e0001c00655613540d940040d075488580120742500868584000503201e0302550180921290b030040c05403031030401980401c00203018035070080d000c5104d0b04a10002c1068280020705900340038400c00300c098440618401e2801d200280110b0400005000e5000070035005441a5042075040c1019035281e6150f942240080c0518070 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 775433462 1250 775432212 775432219
    0x30809011419020102040815040b150a0e0a0506010f2a150c0c14070b07230610051f090513020c0a080409150501140d021c060f06030605090609060d02 66
    0x2c0c41000c102e0f40550040044611034020740b0740641d181e220310300e44000304890141c0a41806400101d0381c2003803c45000c0b0103407008281c040c407207481e6a00081c0b481001c440d03400b150b0b40d980090111941c1c0001407040c2d5180a0b2811121f10340c2c144002c1e484100f013000304903141286c11161501041186298501140b03919181044070086140f0018003800c8910816280350340742c1c1082d80070442d000310b204030940b22980102490103d46680d41c056080040c0c1c0c0c03600f244103103950604064030342400201e0081200c1802114464105801c000006200d20b59046c044080c0b490103001d1560000301541c02c0f16400c45039041301c4e4489002c1c51010b40300b0221500c82034001d840c8950f0070800f04102401c1604c102041c200484040f06800c3c568175111070040c640401c0c001800c2541d0005640010808152140c0c030250a041c50300108022600704005980074403078a40701c00340155000303880c0800042c03400d071606203d4146000040b4044e140c3c040c0c1401d000b03418000c0003030a192a0200c40e01041603015 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 775434712 1250 775433462 775433497
    0xa1e06110c010c11030405091602010216081c050f04060c05190306030b060904200406030f0609121b1709090f01030b012c04030e180603060606040308090114 69
    0x200720850082c5002d0f02c0c65808100c903118000701241001056a041c1c4101030803129541c0c4800034100d9071200c11030a01811903400300010100400c0040d2000700d102c0c4160110354641d003014681c90012046c40584201640c60102044200e08591000a400580082d000180c016400000b00c2d41132041408250b1045100a00c03942100d41c03541c0080110b038055170355018151500000c0000d19401a1800740850303d034400d40e40000c03400c0e008010071510008000081c880c1c4c0c1e0760b03140c940c0041c807032000b078030400d680300e01d40740500c19014451490309a5516180e01c0c02100c1c20300a014031212800301500751901102c000800c40f240404403045d40800901800305850310a814445080342400101d41c5001860000599515515614080303510000d400740e0580125118890f401c900c020015020043c11880540d00e50300d0300c4266021030700c0881505506881c0c42d0043c1880d003e009011507005410070001017002c41c860030161249187c0900e81614129080306080b50240150b040040e844441c5 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 775435962 1250 775434712 775434727
    0x1107051002071725080604020f041503051b04060305100903030b09180d08060a17030f030c0c010b0a03030507141006090212060402070b130305130e0906090a1e0611 72
    0x6800c590307106114007010f1110102c1008000030110303442000c101d1b074004008036005213005950000b49003c0640300080c48154040710340402c40031948103a40903002808111400e00f00341c2041342640f481a50103010603851035030b07801c1e5503000f151880c955160340c2e65024400c252198006a400200050446000b03003042640302042e15440d20180e09c5c58410030511401d440d004180c0944509001400014030a25102e045001c4401d4008400c056000030003e000c101d42c032610181d800b800354014001e49a50218040ca0308448445100600c28480e01c07400700300082d400011141415809210305c84002140f8800d030f442c000000c1c024507c424100b01c0c001c0b0b17024400d503019000c02520801c40d00c0080e03c0c0c03002444120f200304540541117440510005004548078550174040c58460b1504a2030031000d40725414100203290008075007103c000b014040d529004115454004e4864406050424115a6615a040100744582140004c511020f80a00c0420340c420b0840101c542400c580c0c0300320 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 775437212 1250 775435962 775436009
    0xc140312040c0905100e220218010503070609080c01030c3c031e32010e01140d02040507050d02030c0307110d08010306050a0e0316060b01110705100207 67
    0x442d07000392030350b4900e000002840e0000204c4040211440134a1000d0303252100c0281643d070840f0408000e100003e296040c00050301c070860380d0f610320300d980440c001017941030800305810526244c0c0048100100007100b4081ca10380410307030f906120000d0900140d131440c16001503504051a00307002d500a525045056001000d42c0701024000c0180107e4241c410a03805040d800c554000801c401800303240c01c0741849143c0c030f540c8194441310190070f0010025075610781110803c0e6003040d0b44401c4a4901004005080a035014980500881003000c0f9003000100049480712039590030182c4107a4440e03010400c650f0042040364450b40c0d07142800d41d81c03450302e140080720952043c0e0304200010910980da0407004000305010951100301c1d40c074aa4640d1843e1100000b0704800360859002540c0c0e42000f040ca00020402440e800075102104800680c480c2020011101440500c034188808000905081c61020074440b081d034200300c40142a008014200700c0c41c010b116041030402d121442c044141244 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 775438462 1250 775437212 775437233
    0x31009060605010306030c09052e0305100b090a051923010e090a060b2e1d030d0309050307020a0f1503060f090f0f0c09240c14031204 59
    0xa015603001c0c01401e5580c0011030031100360f03110150500200e0001844015690340000341c1006c841035956a1601c4034016a5141e8980c3c01c1d03801e81c00007040303074040040010038410158400c0c103280d0708200010400c004184030b1040140085940340d690000540086001a0010662a40440200504640c0411391600360214a810900c082c0d00c4400000d40c2801044940307119840742805070612420390707500d920207440c24541050380428000c00d2120403c1c81c0258042c2400f801e08454180718080043c007400c81402000b12001c8603c190041450319240017680391000e56003490b00103100304c014280341e400c1d4052070400962088111000065220200188500b0766844601c1841000c08110f81542103c0d068411070030703c070003c2d40c4104141449940003620080500102007858012540c0f04401c40b2416010503001c581d00f060180f1a009983c2081050b104221a40c0e91104d5080c94001e005411314100042c101a20805071400041d01402524014580c68800d000541018175299020a = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 775439712 1250 775438462 775438481
    0x2090a03152016030c0f02060d0f0e010c0912051207060b090c120a1e090308240a05060a0c0b090309010f03051302010f0302070c141c05030412020f0310 67
    0x41002140240801c16070390840f84208030045030300302002503642c0c05440000781c3d030200ba9900305101030107101607140ca4008001c0d8030400c10f0006044200d10b2003020840794074000f4021f0aa142246a0201d0b5401c0303003482e800e445050840d41100701c640c4c03400a1078090340c02401621540c01241d04000c204454120420f1000112003205031661040a001094025010a541c0242d451004100d0b821910342c070000d11003071001841e11070f90451508600c02e40e032300c1c100c0890000d02da510800024010900042c514403440d42048204080d0303400000d840c052142c020b142c401c402c00941880d400e4040c1018000c42c0d640004228190328185a01d2500d039000320125602040c156207c50218078070900ca1244904041090005c58500301c0c4c004680c014089003680c41855070800807040494138900c14540100030103c42550a40324060610804c0c1c44805002000049134805410000b078001c01903909448603031030b40031203800c0c03d0f00008078007202c200800760f0940030f0200d410340f501025030420402c2 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 775440962 1250 775439712 775439741
    0x80d0e0106090902120a0c090518030c070e1f090509010e0a0302010203010312210b010e120c030f03030705160203070e0a050a05010b0405030304030b0c1b03040e010602070b040902090a0315 83
    0x1410031100d1a03915265246c4008080d00c00c0c2c44014003c0c00502e5103e50780081095810000203084d070442c1c98a035038000c100c192401d40c050f80301040040c0200c00300c6a44064500d290140c100446c1c01e8002d40000c05000e02c10f45a9101e00c00220707564425030040c00e8600c108412034401d510a402c02038000d50081c0410307554841d03148428020140903000802d82d0004101c4841c0b1019166541c4600030540074000604010007015114103d5441d5248801c20715001405000982c0017042010315080b440d0f6003800c0e5941041c4100024190401c096907111030440000f0f004000c80343c4000790410350f140c1c00c070500f4061000c050050303800c2e480d0300a5124100b82d071820802c0ea62a0b400a890038000d521030541d142c0c0c27041000348005449041c01a400c01403c615403428204150010010ba00401c001c01d01180d0012a0400041c0b034400c1d0b4072401410b1724000382c0f05150070700124400c1c81c030490160481041d0005640b5113261101c0d01c40800850f001103140080d50b0a41107040301800c0c01840e075444 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 775442212 1250 775440962 775440979
    0xa0b04030b0a09020a0501120902040204090c0813050601050909120a12180510020f1e270a060507050f07060f0207081b0d08130b07061b0c080d0e0106090902 69
    0xda4051040c502031a4005081c01d00142c90b0000442300114a0980c1c44001034035100c050300181c456001070406010030000110307078010117040040001000600c40000c3d5a298a8103c0c00304001003843c1381520070541c0c0740c0c00c1e5552801072a92500c004e11210b19000340001a09038149030380000807000800c0041030a0200181075000669111a00390000c5c0c000c0c0c0114003000b6000304268000c000c800002e10082d42070501406028151201400c070700b1640600005000010210210400c0d00600d06c10444000d001001c2c40442d401102c98080c1005220f800541c40c1d00384101040b06520040300710040310102604d80200a010016800556001d8440c80001180d140d2010030b61058001c410b040d207410f454041030402102c0306425800362002d407420030255030201d40e03121100016011071481c0554480c4a0b2408200701d40c0c0071141a4000000302d10b040164990000096215071f030007104443d115446514800014203c18014804940c42c0000010302c02c01e0f150007844516008a40d03140 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 775443462 1250 775442212 775442221
    0x90b070309030c080c03100b0a05060d09020414010b090f131a091803250f050c01080a050712050408270a15021002070302030d050c030901060f12020405060409020a0b04030b 76
    0x60366070b43c00c05c05c1d159054200b42103445405450b503014000780c00d0004c04041c0d009580d400031404643c03104001c80300640d101c1c010300042d81814068690140c101301c001c42da0310f615041ca4086a40200700f80f1600c140c5918604001a5480101011041080000c01c2142c1c07404090404411041c00480c5400748208030002aa80007920401c8210048110007840c9007580080441c100031718003880100c580b075004508080490843e1543c034020798420390013402c00050000026180090052110321204d0510341001005c940c0701102e820142803046011402d81c4446c54440340500405003214101c0642e03030305008600741c51280c0d0015840c02554a004502d80305c0c0204a0204070340b40891007d64000703101c14240790708541c000c26005001c0d1042e41d00b005041400c1800b510819070710120301c1000481403006009083c0b151310000d00031850301004051802540030751403012130101038030450f0b9800000e04070f51100e07000716440b0755004060360203881e00c8500200594215020581c1c41072007120018 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 775444712 1250 775443462 775443479
    0xa0f06091b0e0105122208031506090a051c060f0c0e03031315260405010b0409051209130905031b0c090a0f1b05091c0f0b07090b070309030c 62
    0x212040301069455a2626581c0c00440d01265400350a90014024200d00781c0c6d80508401c0195071001e00c100041070317590508518800310348500f06482d5120f41001c0100b100c0c103654960f00031b000c0351801d0b184251020444d00c40c0f021035810b00348019100f44d00b050395110003840c0c40d40c000d00801e44a9203840d02500254402e2607560300441c01c035074003101480202841410340180403040341800f5450041c081001250140f0407910000b0010b0036020f207481d080c441041028041c07140b6101050790b007006240c00030f0300c1b2140c4c0c0c0c001c3c001c0d1403800c0a40003d06502103072200390014004181441040c840c00b905881c11558a600180b401480b401c02052501e041c2c01000c42c118011400050078240d40740c031150400801042c0a01ca901e42040c0c0d0303104948211252404c0c01d80e0048096200c20380c660551500b03100810070810090f0684821000c207010010ba203483c0401000c542004070320031650f4444000b038880e400c45400c143e03041c5c42c0124080041581c0a940c0509483c481c1c42d400c0f40150361400721 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 775445962 1250 775444712 775444727
    0x1030c05030f0a051801060e07200606130e15010905060604080606011b05060708271f11070c09060e1311040b060a1709060c0703080a0f06091b 63
    0xa0142e510480d01044a15409401c955040860b541d1000c0d41700e035020140c6800c48103180d22800b0060f00000c1082100c0760082c4405860303138002000c1e01e038051040d0510f40d45030702c0020f05161042e520206015882d03da0795224801141d04a0101c8040c074810305420400c4017401d22440d00c1060801001401c0e07801c080c0b0a95080307501040003070038180c0303c1e00300550b10482c1d07103c01c030f030340c464403802210001ca04104001d81c010076090309d44c00c0a40c100180c5c1e400c20090040ca6203419450716161a094038a400191768843c01d900001c8000c020a4000c1c148000e406a124695440f00b8042000d406011185072500c0884144501c20400c05544101002e03e0030b6040707e8144880c40c0340c440140100c0c0a0a01030406820010302c00100c0c0742c4404000350843e0805c28071100003a9403104a6540044200c50068100492000a080314900714501c40720910650400a00300040e000c041007400a06400c01841c1c11050312060009603150302003c4024540c9c06c1c21a180242c1d03240c0c0c0c00d00b109014010 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 775447212 1250 775445962 775445971
    0xb151806090907060801031115070305180f011403060a03052b2105040609210201200a11190f2a0b07030905040509071a09031f0e01150501030c0503 65
    0x17a030040c2c583ca10745030380c0c1e03501400320010b40d0403d150380e00454150384000700514182d03100381c5801e0381790003070545188507d1803445c4865009205070f00300741c0c039103a80185d010a10307101c0b040d085da03580c2c0d9078050201c1c5007a01154002031152144100c07011403501103003031544c0d0303540e0044060807a4001d0036404695140c4030881c0312003050b0214002580300c907200d4004683c03060245c040890b180449542740c0030709001850b14442c40640364000d2112607982030244140b01a0500700c0b0005145010301121818071401307500748140002030b20f240c18000028000322002d00700041c00c22a840200381455a8500c511560440b0b103410701c009101840200340207030742d41c2c9450100384104842e040c02d003008050b601c0204140c00b40300005000260603500e50084610906036203010f4040d151034103480c039480513000c0e42c3d41e218410b014400280d885d10001100a40c484030300681240c10742007049104001c00440114281e95401c103250031b4a900194039000040b107c00780e804211a0800d07440072282b600003a40d = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 775448462 1250 775447212 775447217
    0x21020303250c02030d0305070314100501030b011115060a0b030f01060f02030f04030f06050c03070518040902060d061503090f08070822080d080708040b15180609090706 74
    0x1454198088545401c00e00c24041820309042c00345035a000a898031800c4210000065151803c106607079034140a8001960000d0260701e4030340c00e18404a054101d0346006642c10907075218402d44190303101c0e030b0000311140d801d503082d0f0f030000b144441c0242c2140001c031000e070300524500000040018900003241c0c070810410b5a000c4182c1d003400801c40d040d03040b080c00300045102c180310941011070010000d100552085500c0554415103281c1201615402811021204014020405019001403c440742607100041003c9011200e0300018005e1440d99000703500860081290302842c4000c1c1c2c01380d0142d0700d05400440f460080410f003103041d1141d0020060440b004c18074031070001056a00541400352107130b51090300b81840300700c0c80320050b0092a0381124907150800c00704460001401441400d801c9840d02007003d141c5694003900c503100150000b441190719200048070501441e04d04056440f004055150b58150040714090086050b10000d10403441180461114240010000202d40954 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 775449712 1250 775448462 775448491
    0x50705100903120c0303022214041b08091e0c0405091f0f060e07050a14040e180106030605070309020312040f0b0a0c020301090c08160503120f1621020303 68
    0x29001103806007190711301182455028091418410782d04604030828009007442110b0072454007005051040c2c111454170f00840c54200003c803161400704110f10001c1003800d100516841d260449880e0400011401c00c405002600038242c4840100700c1c0d1612400c2203400340141e44640204035250f00d41100080d05407250140c090b228150300d03400064810214010005100e540c48207000c4d80c100b02120124001038000515120940e0007008410b03d130004245814245403d091404059481c05001d006640202c030035200615a03007504048041c1d50300c0368060049080c241000380203010715020480c46401240c2001141010f00c1058604440c0c0c2d03020703034840541c900910408194003100c1ea0800b00158904040701688090165000d030922852529200f00e02d0b1080a90800103078030b022160708100b86008012a940008803800b0100201ea0815a40c00391405544001e200700c0300880c5440354020189001e10071116984c8410607804c0883c2045c101001d0b9003242c0300e20048901c501c0321401e5 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 775450962 1250 775449712 775449743
    0xd2033072a02040c1107080f0c01030e0a0f1b170303060402210408030a1404020f0402090a0306090602090907080907060c14010207060b1c030804060f1503050705100903 74
    0x8404214001100840080040701c01a0045815a2071004032400402d00c0103000c0c03402140304000c0000106140c2010308400d9082c00c800c0c0d41c8a444080c26903042645540c1503420a0b182030204405699008900121203100e5140c080c030301004002280500c062514000200d030380080c01c2911a80e1480c001540c5107540e034404001c020342101c001419009c01e150780c00304c003008101c200703140243d00403e4895202d2808850b000e0a0382d103981c80800a44580c941440b005031500040030040140c1102c000d6202e110003000718040415a900160800b810300b0240020302500d54001d1803000d1003038608004d16500c1103802e83e005403040e500e401e6198040c00081100d01e2080100d02d603442d20901a002da200a0742c0c51181c00da80268109030350040d0303200e003502c8243c640b01258000d03030181d4094a203280121074030b0240621100800191420340c07540c00020a00041c0e5101c62a0076411503000c06046440e824910f41c0c5174458081e85004882c40048480001c0c010190002101e500c500c2c0d80609080 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 775452212 1250 775450962 775450997
    0x31515162d05060405060105010c1109221104050901060501050d090201021c111c230f041503050f010e1501020f0304140a0b0c0d203307 60
    0x14510030104004800c5207038040184000c46005480c1c1d02840c02003da41c1858100a4200401a4001c5041c8a4039110840000d8404403c1d04003180044552540503582c800d045120080d120402010301803800c8550400c000c1180480102020140c608007e031390380d120441403c03a045809100d0100e0818031039090440e4285d009881c9203881072041e980c269200912190308403103100d819a000c01d002e840c142c1c2c059030082125808056550140811902034948054400b8065080714540d0901c101c6080c22103541c000d007260080101045c02a030344075070b04c11100000b202003001b4200000d003006c010400c464010429141a2000c0c0c4001440a1329003941e1035a44c015a00c070494150700a0124a0501800900113440101034003008015000c7c000c0081081d424882d4000c2c40103100c0601201c0b00c80040025940f0380c01019082c1060880503d51101041c00e10130509141d041c442c4407c8060140c8920701401070f00203c60343d036140c6040d0415001c113404bc40480c0c41d84001550307406410003185 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 775453462 1250 775452212 775452233
    0x608060615070f1205030612011b0c11060304030207030302071502121812061e04050a032303090706030b0d0b190b120a0308060d0515190203151516 65
    0x2d1003003828041c0d12241303554142c2c1012042640e200480d00200170440e0a0400890300d0344400c407114020031590032210b10810318180102555001c001148042c0401c0000424400813211401880c0a499240614000b9510748035400220018010f0706400142c01c005a070f10045d01e84519000b40c008122014098051744d044044031002540c10100d02c9135958139041110070010310300b20054003551a00d000840b00c00c140700055038150300805403c0002141d40420315615144c0e1601c2d1440041400380408410340c0c3d0202c102070380340000001440b040b5100021000101d075030548080c4840c55680080040070303d0001c0c0b01800b0241c031600000c805099010f8448800080c1c0c0d540022650201800305009070071100394546035030710a921140034160030081e001c1c0c2c00301080321000b440824903030355640c450006410300c150401c12100070501e81c1a04161800710f01140d03050441d22860845020500d80222500c62806401004071210080d07a4800451b007482e41090001c106175540c41e0b98104220 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 775454712 1250 775453462 775453477
    0x1903030f05030c27150a090905101505070303051608040308070311040807080610030210030b030c09242b0f020a06080a0e06130206032502100608060615 67
    0x18071040050904841d402c14142c00b503940400003c05003c401d000501c40602c0e0b00c0c14080300070017014841003c0342644032034010140d913500c01d0080340d2611040c02500500820340c0244220882d510850b05216502c074020303040c2203001c1e59051140d6160603e0700459070520b8a00c803400180100e001401007805a604103130048402d150028440100c0928003c80350400e401c0040c0d16040a0402c02140e43c0c208030290300280e0740c0d01b90b503076920b20b5640000d030b60b040e280754040140b54585141900c0c41d9030605c000c10002d14041c00c1850710b841c042c2d00b201c00d041294a05054441408019000c1d50704207581d00044110310782c1401d003522103116007602030810700f9507402c54140510058500058075208189001080713662907081080c18001d041205a80d041c00703030441541d0090041040f42001074040c0015035805580ca1541c0f03403102c0e50010424444030102940151250001000c00c036400142c1c0086003c4042d03080201e5500c0381e400644809065030b4040c0c0c0049104d41d50031201c00b0003801010741 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 775455962 1250 775454712 775454731
    0x103061d070917070f0b04050625080d051909050705040e0a0f0c050310090f060207031701030b0601170603070522050c03070e19030602030a0b040908091903030f0503 73
    0x20396680b00d103c02040b4640118a1031904006420401100034011500150400400b03141c2414105401b00d003540c081d6000030841081c0030f009208112620031100d15103140c000701d409541c0c488902e00200544426038500b40064a9404a0150fa102c5845804c150681c0a8003030450f05160800b08000350040c0d0700000c40d98000d20000c903000600c1100ca40038681d1081c3c1c0c0030040a0710380400c060504624030264540307107003000c00382d00c0010119241c1309011544030703c0050325011241001c6039034100e100c1655240803000c2002209100c0f6012a85225142c242d8407440781d4910040ca1281c0400d0a44403107800d58080740d030601481c60300d9800e2540c3c1d02d0200d0380c12041420000011410b850084c0d5440795140400800d011505510040c0d0010000381a1644010b504504c50442c200c99005d100250030705502002169902440d80c010300d0303800740000c0092082600c6400d11030410b03801315554a1003025204440070144040716400000c894068030780d440129001d0794156065400100030505 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 775457212 1250 775455962 775455977
    0x7140a0306303c1b08031c020403050d0804060c0e0612220b15090114040b040e01020403050114091c110703021503071101021602040b0a0302030307080310050103061d07 74
    0x4200340f8a0b185400c4040c41c071583c01900700128101000850070910a6515094100348140001c9030000b046801c1e0b51065003c2450302c40480c2d00500c0203009030740004010707020302e800d25101141d01182203406140104030801a80074200320940345440d1400301c2c03e801400038040040c0a50f591008a07078090b101120081c0031503405943c580410240182c00c4400040c00410f002ca1120b031307014101c40e01300c02a10316110a50420030010110030148001c10310454881c00d68800c03646035038219911074a0800029912a526860000c1c040c280400c59802c4c0701c1680d000048019500066910070807012003444072280c1c1ca08081280c100300c1313a5a55032058490000000011f803541e040407195251760015840d282d06080b01c0c02806d0007010100302004d0780c01400004960544805050b4400c0ea040301c000962419400c0840d050072580c1c4d101030750500020605409007c0d000c0020340c45002201e025950781c2d42c9400065040351654082c4c989401820907c0e00d04a0045500b069000400b5080c40e00 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 775458462 1250 775457212 775457273
    0x415080405071a0a020d0c0807142a12010b010c08030a090b0408090306060109050102060106120906060b03011d070206040201050f070f1401060e01080a060507140a030630 75
    0x40c5084840f071180e0741030350b001800000290f8140b1410540c04001e145c500796400c00ca46402606006941011300b03614008404260000800c0040241d0151480c0d10312048401514003044003090911125000740507601d1440031440041c031a40304004016100d4244504080c0c94480e15034000419201045981d200307902c01040050200300d01c618810501d00344d88200701e81c00d05003010805042c060611551510a00c142d0f80c0100d5500d042d1495480c0c00c5c071105a48280c00d00283c800d42902611080c039108003c140060003100a41c16105005003906c2e240907009076802c211201100d114006811640100300158426030040c490210502a1141042102d440b030005c541704008003114045410100070300e81800a003e402cac007c000108401000d980350149554039070264200003040203542d0400241c0a5000781402c244040820201544a9440c14400780042c0014001c1c1115050240c1c1002d00e0500310409a80502e0070080055900381d07190395403e03110766155104503210b40e601803200c8 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 775459712 1250 775458462 775458479
    0x12303180303011206111b073017160c1a030106090e15030d09030212010b13020901110a110a091a0d03300c02030c0a0f060b060301170601050402041508040507 70
    0x160b078285c0d2087c0942891440d001042c032100c04d40c15150614009030f94200c2a00c03004c0d25245818203a0070041226000940c4000400203100781622050403040d90048581030058400b00c00c820380710030b0240410261a0900083e404d4003003403248a0000c2d02c119414411212094442604144130644a980684450000030309206208072078000040403208208150f2401c2c502d50752001c40300d40d0080040c043c21801140f03c510300203140c00c1c20640c001030180d00d203900c180a031304901130744002503521200e0342e49011304450007800442481184906000300b1002000d00c90300724a0a400003807050074448220500a40844600080c0e040c811001144110030440c1d070b84010071890190210880540440c1c22582203a00c060300c040c00710b50040c4107080304044005500481036400880e0030514414500c0c0510282c8544000140c004c5c00200c00001c6410720380921101d00c07540b0303c05444a03a0f07201d4085c00124011031040f8818400d5058504800714042c0780c5035508180107005544025841c0e8800 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 775460962 1250 775459712 775459747
    0xb0a06033c020f09030d09060c2a1203020607080f0f0601030f0606090602150402010e06030916030f1a16050a20071509032001230318030301120611 65
    0x3866410140020300a1031803030f052048540991107400c0c03400502342006002170a04100c8403000704800008c44162014000c1282004501ca01e6010301440d09600c401c8556400186014201e0142c0314000100d5400350003050200c6c0f142d800c1c242080601c0e6618000000c4401d0042c0c444ca05043d91002c800400702d08601992000e010316840b030881c030030302c1c2480003440d10005504d0f524041c22100140130050380d222023600f180d54400c840712900ca44481c1b40300c90501d0b0440004c0035000c0503a6a0000412144101c0d00800c0c030b000380421026200c03480500881c0020803540261450002040803280c540940c0c050446000b151805030016050f544d03410729211204c84072400175070322104040200008280f1082100d4000b0f15203e1a4540396603102c101503444259078034200302d4084060100c90b4400c01c002c912982115204c41152030030038031030602913801500c04a113044050704004d681c590000048a0484c0d00941070303071000581c584c46c1c21004112029024007160001c001401d5141110b518 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 775462212 1250 775460962 775460977
    0xb161e0f0c17070f06031517070f1203120c05070c0e040b1b0a032a081b0903100507020f0717070f03020f04050604020405040e010b0a06033c02 63
    0xd5055070a08208050b6000d042402540caa01e5000e600140001d0400c1c1c2d0010003114003604011400d510101c245100c826840e801462103243c05100341c080701203000402c1030440f0410303101e03583c8031520f50740300b880d088880620140124460111074a0309881c0342c3d100f401518107601d0000d00f019070302d584e0700c06210b40310780c801208045140d0a22041c800c0d03940d1404d0304103c1c0d10281c102408410f50001400d0b00852420b0030905a48902c0706120031201c6240107542c401d00c00360600352885e10b09000e0046902070785c500d1301401244801c46468814042105c01c0c0c5803004000704106010070900e074015100061455003180280c2c3d0004803880f004102e500080c228131502d900024981000c100d2400c3c000b81e20809600030344010030405070322a41e210f1240201c0a0b40d000c181c5503141700105003e40b07d070303511040e040341c44e1045e040701c1c513001903100710b03404602202e10300d81c16503444070100c09455016108403480324103101502c400e50842c000112910040300f240180c00c081400500049030001300 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 775463462 1250 775462212 775462223
    0xd0302030108060a050f040b0601020a080a050703030e0102091e03010b0405280b0d0b04031107080106210209011206090b0f15150406120204080a0501150b161e0f 71
    0x30040c0004401031040a030701985100701007003240740c0382081e01c050060250001d0b0514038005d01080480e40b09124030380d021600008520356a0801100c010416070004600b80c0000b454498070b07040422040c0210f07418101c0042c2809c4500000030303d038030a81d2030314842a0fa41907603581c130703501c040d0b403164011144110007001c14410300194441251582d20803591401024a00d084948401603583c200581041a040500050340d90b44078034058610031128100c051b220f108a603000900514150407003810303152004045030892981401036080c012840790001c1d0b00c0303e068001032050b0200d110903124041c0c011000481d01c0016a01d41010640f0192903200c1d1003c0f9410400c80400280300ea40348080005950b402c001c3c034422240782d4000e008500440040140d50404200824050780548000d80341020959201d81c3c2c81e45403003402030080c0c18242100c9003840400054860044007a150100c01860600029003ea56282032500605c4280c4030320340c5600c1001d20000c903203028201011070384203a = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 775464712 1250 775463462 775463467
    0x2040f080127050304060509030c04050c030109060f080d0c050a0b0109020702150909150411031303030c0906270314070608060d0f020904080903031908011403060402150c0d0302 78
    0x580e5407030301d40840300702940700b007002050701d140001c0c4000b049501715401c501d820b5448280b0080040e060950406010b9840360a1005000c1070030342c038000446c102d80080303000f0000b090307a42820003115a068030a04607641c100103210421036018041100f015881001a5255a038241d81d85442102080e0445441140d0210700c03c4c08500b0b004161004108032014080d0408941c20001246804c6c010031000107480c503148034107101c0e01c80e900b101141200090045841c0e1902511800051320008020750009042c1a21560f00600550010050340d461703075900340c039103421001400c0c0b450002e81d04942208121020000204044540c1014080300c81009001050310700140144001400b40609100340c030f080d10804001103075075005140c80b580c1640c0e074803420350711418403c0d003a001d40c0d81100c0d05400009410021460000c21003101a02552200d03031559899440d59580420116034054055100201040140c40d103580110b441050030200d261512100b400803e0600c829490514040781c0c02 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 775465962 1250 775464712 775464731
    0x114070504060e0a080a025802011e0e1c06050105011803062f0c01051015050d0b060d0f06091a010f020f0d0827030d0e0102040f0801 59
    0x300b43c150210b09000c507500341c2e0f12820304a0003503e610f11903c000748200b4491196031051300d0078154848006c0400c1c0030a200d4600031000c21100e1028410501601e4002000c4500e6001d5402c000c4580b140e0b01079640c03203048400c06070000c10700d00c0c13040003520a100090078640c4c00c40e079412510074600803030030b0023031194801e036460814181c0b241a04514107024000d80b81144964a80d16448200d03070b0131240100300c1c44a5250542060344090150885da50703840010900c20b6200f0000170030301043c80a008012940e1041d1603075005203564042c40043c03149001c940a44984948050100c448038910006000d0b86032400241240c1c1c4030030300000c0348076211794144502114911540000b040c02e030a06014a03d507a2a602101c8000c40812505000c4a034100c04400d078820041d221b0945e034101d040b11605202c4540c007801c01281190798819a0300d034102c6030340c0a8481e10341c01d20030a4040384002e5050480108030440500300070f8494011a42d82444009032034401c0c105140024040d4000002c2c08008 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 775467212 1250 775465962 775465967
    0x11401080a11221a040f060203030f06041a0909061e0402060706021e07080702040b040b010f1b0b0f090706021203010b1308030d38060903011407050406 67
    0x500420203000245003124400035180d416003160000c0310310045044006421921030b0030b101d02960082c014800b01300301855a07001d030180081007564404c03151203031314681e00c1d402242c0c1ca1000300e40c18400c0c0382c910400300380d843c00c054100d07003d01030081c02440580c48145020034018001110344a005d40d02150620104000e055141301c080190381082054520346900440c00c94410584010710b150b074000313542c04110070030b9000c0b10701540302c105080d0b9484005080ca4165904171a006034425413a051941700c0f40d1415100b0100050f106856031170000c91420381c00c2d900e40703403080a8610181843e41c0c020000510510503a07100c1d16115503a0615414100c520619000480e0048820756200c003803190910f039402800c0d03904503070084c05035130780e01e002440300ba00010100c0c0e80138400d0f6120114842d1101c000c103801044541c1103444102c4004e04481d040400c1c9046140c4010b41000b1a0341e45540c46400c100c4000e10600b0300c00740010502d07090085080011403004c86200c4006840410140301c1240d = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 775468462 1250 775467212 775467227
    0x20714011401060c0302063409140103050106201c090f0f03020303030f09100c110120042d031b0902071208070e0406140108010905041a0408040905011401 68
    0x18141c03070034065100a40c0e50280d80e0711400b90001d0f24121100096080c1000c0c41c110803540035011071582c08e891411114050118a254044c030001010503040042d0154480d00c10a412503003d07a03560340c000c21800d40070302c02d030700340e48500f807401c0d0300404102401c54099040d6008048030140d40e01c100040c9030070003e40204ca0b040d000a500807541e101c0800c0982c0d40002600d402c03040b9081c1c02007807900d49406a41c5081d44e812000a41da5040c1441400403980207041649104401c10083c4505061b0551403480d081020082e0311401c20113100031312504050b0110540d40610101800d42d0000d841504004008450b03481120f80e04503018108200248820901c4001d0ac4080025402c0400b00d17a19225141110250b12041001400000306014810b41c05543d02100207403040101d1030f2580302810494220101c00e1b408a02c1100000460f003840e4402d141c4143c1d000720403c2104040820103104684018009850541c0706200205411441e0b1003081c0c001c1c408090085640392581b800540f016 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 775469712 1250 775468462 775468469
    0x10c1e02122122030b04140c130b131b231206010e13020c010c09080a0807081e12060102010b010c080d110301120203010b030a11060d020714011401 65
    0x1d03040258403205040152080c0c40d0b03a42802c2e525280c44010200b000224003035a5968075943c09448100007050049071100240207074051041d602d80e41d505101c500e03560301900044640c2081518000161a05c469400079030f00b80b50050082c420102c241a502e001d031803007803000340349803410719640321040c540103000c0001d80c00382099102d0701142050b0208020340100580321080d03000481c00114160310a446100d02d800000785454580d00001708040300940100390140e00d558a0443e610805c0e0380101c2c00c0504850352a070003854900950768480c12160000542140c808400f4084441c00c0c03030203038100341484008048056190f001d000441c4c2004040540b00ea41036901d00f096406040e40e00c54070382c1c1d034619041b50030035644505900d83c6074002d142000c070b40201250040004a520301d2207081c2e40358003a000310024050003020204150f00d070165004010700014200380038208a042c200e004c1c0c62003111507100142402d00b00d440300c5001e910003905081c580e941d59411610b03188401078640717001d07 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 775470962 1250 775469712 775469749
    0x13050301110903210d090f0602030a05011a0906030c16080f0c070906030b07080405100e0c0f01031b0e13091a01090605010f1404150f0201110f04090b010c1e02 70
    0x1640031320a01c000c0a11480109240d1700b5110000030042c00340070a034116816030b012000b19680d180c50790309500144428090300034481c612500380c0e24a02401070568070113200c0145002e14540b176205865034594044440340301d0055029401c5400302c1c84400140290b0044107420550310303091000304500b03150258102d07084141c9804800d0020642103901e141d80b000042c2419603080e221414180e01d4124803407031248005080c10004802804003041c001d4582c0702c15604142000c8944005605581c0d0300b40e103804145c0107a00c88510202c0c480c04080e22011801707800640290744100c040303001d231403009400740e82c00001e0941e8881c04001e44400c0c64010440d1480802500341007000080c003444c0008180307000c02c203486104c040000100d000301c0303000345031050070007503840c0b002d080c00b804041c140408007015510340840101503c804404658a0040b03035000189000d0030840004000d2a40441c00d504000304500c0ca00d0001e0181c00e040c2001000040460451202e2841044004500b08000600c1c = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 775472212 1250 775470962 775471003
    0x3010b0909100b1c030f0c15090c090c02210c010504140d090b1804020d0606170c030f0c030a150620030c030301030f02060c060114040f0905060a0213050301110903 72
    0x4084c42c24240100340c03903041c40e082100942e21103080700d10868001010704001d1000d415001c50b94003036801503c07103e20494107203620680e0b40701d1030000ca40c66411000301603000310310119904103503491007a8115800349441da00300242020141d007180d030202da0440d206d140c48880c101c03010b40d00b041130309081c0b40301e0720740741c85080e09200b82000c050140c1c0b214101d456151542c2d100700f903590341d0141d840d0301d007480b10204500c6640301801040310380d82d908052000d601300804994030030030550440340b145140741c412181d81d888800210706030b940000d150300c0065a507100301c42403069403955130350018800d60b513071b401c80c00560320780b00c0305da442c1d400c2c0b41c58045500c10044041d140f5030110580341140d41200340b5242c1014240042003035480342d9512140f440c0100743c004156500e121141c01e42071a001d4404010b008001c3d54080111001c900001c0c10aa00490020b80d002c101a0018002a0402283c98407045c0d526004a0300303466508904070300031840031034202d00c641820401c0c00c0708148441c480380c0 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 775473462 1250 775472212 775472239
    0x50616141b01080105030a351306171b0304022101061724070e030307050304090f1e0507030b0301090302150a060b1902160303260615030603010b0909100b 68
    0xa6150003102c82d01c1518480c2d10000d11146104209841c210440240c0c8c01c580e1400a07826a240c0c40d0b00500444001c00c09150078131b801c075102032050a1003440040308400c03100110100f00051500010070490740039032203960040400c6080b000f1851b0b951001c00000c5412420100042140c10b0482980d0100e03610940304c0d0103103030b5030701f0140c1981288000b41c402020340301c02c80200c4009070300d54104d0307425200c001013040c1003050020080044407100b0f80208407000001d00d90009940a00880c000003284803400036007a00c0c0554400b54000359603080000391a514100403a0039600c07402c4040c0c0252700070b0298030883c00c9070700314400d03840000c84404020301340c109003403070700c190003602103901c0000b82d40b013481210203008004002c0c591041340c0c0f035441c0640d079a01d00141514000704408003414580e00c00103900c541c00b50001402030000400b15031045003201810405908000c000580c90740d2140c103500b900f034944000c0306000b9240200640000400d902c661800d4404c080d40302c1e40145c5070100c00c04d = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 775474712 1250 775473462 775473473
    0x90d0201110d050408040306050412032306010e0a030501050c1b1c050c0312010e1501030b0a14061204030c0308070e030703200a0801060f050406050616141b01080105030a 75
    0x41c1c0b101c0c42d4502000403280c58a0501c41c138940101d420042080b46841d080c0001e0103465045050210071954003031140842441d030742008164240a1115040e48070004035403198022840d00c4001140a028906141d41d43c0d00c800b0700359442941c040c0c441800008038501e04401c001d1860800004000080c41c0304442c00c104040e408038185131f5042005808540000c2100083c001c4804c001e40700e44e01303103000f940c540b42e00c254000c109a8094070804241900b91200e54024001c080d00410010500001ca606c0c19041150100c00150307496440a4100000d0444402280700b00d0f001d140a641c031122010711502d0060400721000d032445003401551040f950a60340c00140c60340951307078400703200840c1da1340d509510080254100101d030b0384101c85800109074070300b0542c424030403034a064a0400845a860080c40119032483c01041d400603001c12000102d000881501107010788110001880c5110120034941030015402100c61030700e240007031000d400d60340704015501506084003c0d001d03d150540c1d61 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 775475962 1250 775474712 775474717
    0x20604030b0c07080a2a03080f0606070f06020301050a08150103030f0c0203060421030b060d02071a0f093703090f0e180f03071104021e03090d020111 66
    0x1007082040a0024007100d6491040d1041c881c4e1020f0388680302c660715a0041c10008640e05411503a0500180c0da9550700b0390500c2c1241320681584400c0c05d161500e40d4048421080207101942025080010500098410307406084c194081d890060b2a0b5040c0070802c001c07841e1540c009540c0f0f5005115400480b10301d01185811039502d070802001e0518010025a46150350580c0650305000f10402c110500020600c45203101c1110990948a00e80c0c0c1133040e0101c83d000b04140c0d801c440288144c002c80b180550040005034040c0e0440442c881000f810108d41400480d20110b2080034a400e000c1c12250401043c14143e044511441c030618001c08400c0c4d02d2481c3d80c1c80280544c00340e2030044145070007040400042c203150f4018003050341c1c460790b4001c518603007512103040800c0d460300351085036400441d104000d0028800a9450924151180d0b40d071810705403581a40298204085c20006041b500240b07121546a144151240b500789621030909070b94110f40c005590403c011202506140800c = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 775477212 1250 775475962 775475969
    0x10030b03030d02090a0b074b06020d060609030606121205090f060309010c1106010503062409131a0601142b1b050408071401121506020d030504020604 66
    0x100162155003000000300321329a598081c900d1386d000081e010061180c8284a51181c0c500c016502c01c6011050481041c1c0a85007208480d440140c000e105c507040302c004e1604144140500009414402d02000640440c0d540d540004042220a601001009110f0141c00c1c000c00d40502070254003900c1b40ca8800d8511104c2034140108100050b2200f95981c844850102d42ca001030640c0d40c4a03d0040c25550080a5040021011034042403c00c0301c2c510b030026056040c0c0d40040d020345466115503446403505201d001440b0b076254548408100c49840d103180582c418a030f00104550242030702d00704080800c01082c00940001094001c01107943d8004c04480c01042440b02102d54401407451800b40402908180c140003600040301280c100c6126000445205119001041c001782001003d451702c0c4030380d1040c5003480e000a08200000b100d00760700600c0300e10060412429202040c62004211103030841d240000021895042c0300641c0d04118490351540c46080411440c00d0540001d01c00340034070311 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 775478462 1250 775477212 775477237
    0xa120212090d03050d090b100503070b0405060c0708010e060106120c0c031d1c02090601050a080403030b220603060b0d020d120e151c1107030806061903020910030b0303 74
    0x94400b0400d0300c12001c0f6003104034240d4003000b980241c0c0c60400903118042e590800c103840d1b4050007203008d141c0030070744004554098003207a1500d85031405104040d0441490341c112030042d8440000c0200c004c1c0904042c04900e000601840d40c1802805880e1465541540710903a01d850b180c00c50a54102c05e2050710b841c0c141c14400c1d81c6803154030001c41806420003009401a03000c0320801001c81002440c04000d9108489050441e604e8500441d0036000321010314000030340090220300400c0c082e511508074204054400d106401440b080e0100c1c5481c2103a0400b403283c0d9408007002800070f584200c10740b0803411106407015034081c1d0002020031b081848041c20481c081c50080418900981b1803420b4560060320b02c40c50611490381a01c05a004810200c146c0980440010102403c5102e15001060300c940205e0420000d03440441d070001c0c00900d52034001030304001496603980c1e14180c0412803401076501582c0c3c0e070014000c0c4500740ca561104e07402030600b00031032004036a902105880200315002e = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 775479712 1250 775478462 775478479
    0x70201020d0c2307090c080910021614031e07051605010f050c031209030703080f040201081515131a03060904390501080708060a06050711120a12021209 67
    0x10703d42c841c2805003590003642601d00c0c086400d041603800c14107043c0300307481d0581504c5c0524415001c2d038040c4d11603040c0c90114a4901750b02d401c00038004c481d1b241c0b001156201108d04080d08040c05842d030101449079403c0d10720300400c0c501c00b0020200700c02c1c000080041341d4009454031f80360001c0c00301510358440009109020a0920302c0d01e20030020b0300c0111030041e04002c1030381000015540c0b00e9210050942c00200b035507002640d1a0b40c0241200d0003070341d060303480a01c80da0314100d0740da0b1000c1080d1800c6501103580303240f08440c0e0005101070070f25194010328000c021403030506c00c0c240c0070001404151002405100300843c070b0380c400c04000d03032064201d4081d20182c021402c881e0001d1031041e0301c41c00d40c50f139241040718907103c20340c00f08030036580c1c2a04e075844940c503189010b5508150440303c2e503a109203801004c0c400144a1406405120310420441550090704800101e0707100d61000307000c9032a0300c22010413091203a4140942ca203407a041c000703052000540c00f5003094a100d00c6941600501a0 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 775480962 1250 775479712 775479773
    0x4060507060f090309080708070b040612020702090106120b120319020703082101080f07140105040902030f090d0f02061303110102070c08060a02040b031f080d05070201020d0c 77
    0x1e0b000140100040842001000c51034034000d8103120031170007100341a1048041c046100da20000c4d102c0305403903821110174141490100200e40844180d8000034400d5000d000d08001030b01d80b014881c0c082c00c86074a03141e40794a0a4095582100d03070300d02d07406202e00c11007644445503100206c01c036011946a41340304060035106002c280d181c1800381d03200420302d6078000b80c020b803100414910000c080c1090b2100d00c0c4184d07600c001d240c0d40c401d104044000075402c16801003041c0031511441060380281814810305169075850754030100d030030459100450a0500c0100071032103a041c0503c034242c1425040801c034102203240029940e05000340f0031040c2c085910503100c2410b020303030b1030b2846141c1800000d541d41c205500e444505002d542c803e5900d107210f91004180c0340240390081d00d01784e6601c1401c46042d50740c1c41c0c6040681c4040704146542d1201c3c000b5011071540c106000140302c078503080d02c926960700c40c1840024680058000460208000035007036000013940070385585040c43e10103500e109880390303 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 775482212 1250 775480962 775480973
    0x9050d020a121b05040e031611030106290304080313030201141312080601121d0a0c15050708070206090f060a0315050d050c13180b0a2004060507 64
    0xd640010620350b890b010320004105407280c003da0b0402c2528030561996a41e142400142c5814a0f207003280b54005010f4a0a00d190444006992078082c48080d0320881112002c030342160751a4014980302c0301c11407802840c2c01454615000e612400104940c81c51130b06494013170309800081c001d5541000303494011004d040c03003500f0400014258112080d114100038010001e5110031034411074031804550008102c180c0038250461188006850386001d5003a0450803200508141040300d0b07541084044090001c00c0821106500b20311441c2d5604100e42071144180d404000c2440701d03400c01008108050029080c0d1040c1c40c0e1003581515550740b80d00e180d030001540c03a01d101c4c41c1c050b0032030700210301e40030a240e05800051040300500c0d24019400e4443c410b00c0b40f4030070100000f4106912050701c9a05a04184008054119013000e0004140c5140c00f0079121159500006551401c0d01740140b1050144612840410744440c080b0086d025400030710784011406648244030a126006c00c51130103100 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 775483462 1250 775482212 775482229
    0x140d08010b12071404151d0a0303200a05120a021203060607060b03150a060f080c06120606040314030a0f0e0a060f03020c06011701110c151003240e0d09050d02 70
    0x108103480b8010124034000028008a47ca00400810410f9445511510701b4803c880d4001e90f1f03010794405c000c4040d10b05003a0301880c048a00d000d2903110760350800000c604280800000c0800c107062480d55807000b84002403a11002030300c81d103c59142082400384035030f9900200c5100030742c0700002290300c800070340010341031040390300c0a45510b114050400000d008158444825034129440d441c8000741c56408031980c400284084caa04200704020440586029480c00380c0d00c064024403191925441c0e0b80c80c0b15003d948002144403135400410000c0000b900a17101310511191840c2c075640081500001a0460b02913120741c1c014400059840c040840c4285c04503209107120104852542d6910000a001c490206160000ea5441d0079030900082c62514219410104444010400003820f044800c0407204007600305074140700391034000400a414110044900b150661101c20014190b0b0494403da8615015401e503540005000082007500400841c0c1601c0090faa6a180c1004502c04903000c00d = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 775484712 1250 775483462 775483469
    0x90c0d0f0618060504050c040b0921030a02070905010e250e03161d060d08030a0b130b0a09050c04090b0301020408010501030807060e06010e01090513140d08010b12071404 75
    0x902d08006560100b41c080e4000300c04a0b0740aa03020451070707036074809842480c001d60040c82c0807041f00300b049104500c0d01110f0258042c41c220ba81203000f03d0626102403440e40000140d60240c2c11106041003c0308061181d1801040c0d01074040d282854007000c0d0844461000e40d5000d0403107100d08206540604c80c902c1da41520744040c040320800128860005000c0060348180320b84c0c044d1003007134680440412044180103410141c1501c0c03140d01c20341d881d203d072a00010450450316603611080d40c0150b603040480060190031a000007040042a410310104c55800e4008001481c10001440010740800c1c044904a41341c044000903410b5901c00003e01911613a40034140c01d6007030000110a003c5010000e00300309100b104c1c2005060810901e0075103a160901c980d1540000c9140104846101900019407005082c005076810011595450750500b01c0a401140e01d0f52101c0b280001990300b2101180c05041d144141604041d440c40c011444d581d802844c0400300100f2503564140e0b20551010b80d80034 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 775485962 1250 775484712 775484729
    0x30f0a110c010e07090b010c030f230a0809120409111204030801080d02070b04061b1a010602011505100c050721060c110a11210f0606090c0d0f06 64
    0x201c01030003101c18040c005032400c0d024540101d08000412840c1417280d0884000103071280002e5981d0307902e056810035000e420b541c0030320030202e039446491001c82030980402082011055201e8122000082c591040201601c58a40c803910300140394403401400c0c0d40441d2070440001c1441030302000d0380a00350243c40001c281e401070f11400e1008041c1c00c04103482c182c0d50220100e606020000c04102c2c0e07901d80c9446058400c2d10200003c0c04114032489548481d480d44504d4291002415a601c01003400450880031100c1c0c2814014401c2e20390a00030302210a003100d481021312030a003000100c0d603549406500c418810030321108000c102c0c2c240032103001007220b6204500d120120701c42d0382c0b1700b0b0002018115802864200c0085e07c0700d000329011340003c2c074440c000b08240715041e1b50745a06404103800e81980311031060500030389075072082d20b82c03038050107403c01412820000503000e914050020300b10a08c92548030081050301d584280a941841e44000008034040aa0000c020001c2489030050f002 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 775487212 1250 775485962 775485967
    0x220506060c300301030f03140f071a0112050712030e030f06040210030905031617070c09050c0a080a0c0c0c24140a030e0f07030b01030c0902040605030f0a11 69
    0x501c8a4148400c44200d12104042c11000c0500100c100c450b220174040180306400914400c03010034445c2c044001c480100216051905d0120540e004154202c14004c0307400307241081004500560468801c3d004005c0d0310660460b004160703444a803150294011388d948400315541c40c4050501c1342c0d8050b010580d000e4141c6500d6500300181a4072500125000ea00583c0e01c01001e0b02078510912980c40c0c1c65402c08041e50500e180c2401800340303003501034000c1d51890084001300701408008002448114428007111a00c5483c0858101c151a4002c00e20461150300340650010143c0000809a10400d5a08001090f110280003074415504044c0007900641c8030b840d0201d01120b240040c00401c070181c108140070422070003000c440c548030340b40b014041c0480034030142405e207021f42c02c540340c0300940c14151100300f41d03500111407504a10394402d45895031004010018803004411601c0544200352040d4607040c01c102c1c0151032484041d000c20303480c07131000d40061100e0000398802582814901940c55 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 775488462 1250 775487212 775487233
    0xd14040302040501082109090f0702070305030a031e0b0a1511120c0c0f1c21080105010f0305060906120a060c050307020d1b03080417030109060e0105220506060c 71
    0x25500c0804900c000e02503c01030f0094506c00c80c01e0029208070800003098111107685d41c5080100c03200024200700d0541c81a0240400001c205201801c205c1e4515070780000c4c04c1c0000c00c504801d00c0b99292440881034500100c0311041d480d09a2994141e070566035841000500019080324031944450034500b19003c1c0404020700d05e401603000309407c1d1401801c541c1d000d0520030411403c1000076040036404070040720b0107040d48802d42a4494540e000fa1080f009005e4034400254003403100e895070340c00003a085001840039680200c40500c010f0351901e001c00c864984030020611040703015201901c01d0410303420728400c0c100108052440783e98071084c14010b0540c09100503009401c160b43c0b001c054007500d0104110284100354036026407006119504005502d900e080e1081c0c40d0140c0140c0e40c282c3c0400d040096030000da4011402000c4228001a5561908100301d13200c40c8103800562007101e65081042400246110720303209164003060019168549400280d0117226094514006010715141c40 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 775489712 1250 775488462 775488479
    0x60212010e010e16031d0f0d080f040c05060313021305070306081b06250c05030d171605040f120213020306150c160312030f0203090d14040302040501 66
    0x18100e4103800020001d60342c80b03402c00e00088004031040440c4410804840d16064440c1e0054000303403405d60008139045600321b00550030000b8506290005511030010303642c400f6400070208d540100540d03586900740c102969207000c1445940701d17141c03242d400440031590001e0900800524154000d1458400403110b91304540038001c04c607840008245044c0d0700080000d004588510f50354481d00f203040c40c8d04000c4c010080b844d0401800c1703101c2c1c016110583d03034403040341d00704007030465003d080e00c0c403281c1d40340508051404040032407100800074094181e0722801001841580c024403140c003a4040000400400c0702c4c20b0040b03901a12004000010000342c0301d0240c2e24a165081c02a100540c0d03040382c0c0c2210700f041e844103441d650b81100e4070311030300000b95118101030210300401d0015280d44000441070501e88100c030303801c1980e0030f1696a4500002c00c0d054895400c0c00c41c4500ca0a41c00d5260603c513285d2580842c1d0800814130911b000041d0000e510342003154069640144100182e5840b05d521 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 775490962 1250 775489712 775489747
    0x130e06040c180b0711030a2f09131b12020415060f140c01050a051501020a020a060c17030408040e01060306050f041d010903022a0303071e0602 63
    0x149401240390401d06401c0034451442201c0119040d00510807140c03500f80225104c1e809510145d5400840380d0400c441580c003440039110a034091424001c0031220a100c2c0049256100c521070040c1003100100601034490a0049031701010300407422205a40350304000c9103500c0301c0d550b02c11051250352004180303880e0301c842030514a8000c1d00c0812082c040b10300069142503a500070340b004682548140040540304280408022009800c940d045c514401c07005400d40c0c0080d034141141580311402c00c1a041512800303040310741000d01c0100b4984402d600841c20b480080c2c00307100b081082c40b1900360b040c04021031111144484d45900c072541c80c80d10b07007081341083d0010300406032200b5094000144a038030a005101c140c0324024102c064403100d40080100038001d640850307010314154080034071101420f201d00d0705114044c0d00a080509001140c140b41d01c0003c64006019071494050b09503180c40000580d4441680300703501954480b10300b00301107041c0c58030142c024015400050003841c100701c46001c = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 775492212 1250 775490962 775490971
    0x3030221071701260a060c09060e060307200a051e0f06150f01121d0705041404060b0103110301170106060305070c0b1b04030f0203101b0f05130e 64
    0x150b50300d411100007003504000030280702c1c4011110411005040004002d0383c00450750010708111204410955165020b455012034010040b403290682004810741084004142c40000c480e05441d42c90010009030010342c4810001a00d1241161458622a010019045215006000c40d480d888680304031415400e18448401c0382d6015140500c82540400a2020300030616110800041e1603071074103000700350000705c046a04008501281460200d082d1040b088444100e0b83ca410300301c81128200b82c540304c115401030b030045142c03244000306c184280d18019000303540f100780480c00c04c81003c0120060703d03d1210b00d01300c0d503000000010380b07982e03903041d207803814a2100000c0c014160740380800e9084a40441d2aa008200301c03da803540000c80c402d0081c1c2d4025402c401d801000300078001a0502c5804c190030403111003005803401d00651904200c1d003501c00f11a41c03418080c00030421148a2003070038003d0400c0038085403000680c1030600681c00d9031100c03d10888000f40c625943c1d110419070060558 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 775493462 1250 775492212 775492217
    0xf200a060209030c12120c0a080d050618010510030b0303091206340503071701060e120a02060702150708070c1d010e0711070305030a050408160e130303022107 70
    0x1350b5184250900300d03100c138003810b40d0002030130310206001d0310380c4c0722079100c20309007004c40c046e04d144400000e00c40c2001d0000340008800001c1c492034002c081c8492a0346540c00d20102d845208010401941c50303001c1421110201e150106107099080c01191450041d510595031042c00c4812000507003000003001032007000f05015a0544090382840342d1001801c0004160010628401159007503003d100255041f10940c0b03880b4280d5403814024004104003038002ca00060011091507503a46401d00a441011004001500c031640d03060340095914032454000238011036480144603409040c0805441d02250041e82d480e50300e41e45890040444042030180381c1e00001091000d040d1044100300140c1641d004000b1581c10380c603401d80648440382201c4000c0400d11521b0000f10000d0018409868640c815807160b90f152400c00d1050360070626421000301c0740306050641004420181c5241640055124400c44088211801c1c210041d00c52401d01c001e1079940312444140c1c40c0280303d4524411203041d03 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 775494712 1250 775493462 775493473
    0xc0d111e090c090109090b01021905030d06061d01031121041403030402090c090f060f0c06010b0c07050904082506050618180a0b090607030b010e010f200a06020903 72
    0x3440b005005016900d421400030781d40700400d02104203203901004480105004551000d42021804000f051015808640b190008609480000250b000f040c0c0540880c2c10310f80000700e100724001d00c11402c1720441c203040503104e103d000412141501140e61002c8803190050b51800c402c01c210000c004c06036000c0340c2940081d00e03084e41300000031082d280038540c001e0040c20503807100c41800095400c40800d0315071110170808184090782d0346400601c0c0282c0b01000e540d4a400652a065090050507409980c090000300f000c0244554003107251420340c0ca08446401c0c40e034a45040020041c0680c1e03500c5012500f00d03440001031081842020f401e45841004144102d59a94050040e04070300c040382e1410b1403d01e040170660030b20035a003d10704010344a074215401c1c49456195102880340a81e01010380e6040541807051403541400b550440e14020708102c0782079002180002c0000030240100720412940518480301d41c1c1d1501c0d0144422031200f01203134105225400c1050007540700580d01c51080c0300d074 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 775495962 1250 775494712 775494721
    0x10080f0a0621170702130f06170604020a1203090314100204091506030b01120f0b0d0818060f03070e0d020621060405010e04080f09091005030c0405090c0d111e09 71
    0xb0341e0700b2940500e038050001c62100c0c0c800d01d004805007e003103038404111178607103c0100750700006000e5854002c000e00024059070801d0300521011404640003258000803070130f42240882d800c5480c00c3c048960000707002103102c1f889424241000030805154803041d00000380040c20261640100317060351004043c454816950303140c2a8100d50340c18034601d001c83d080c140d002c10b8105c115031001460003146240815140355100024100749003c10045071041d501144090340c0507904d0801c81c0c414070742030300c0e01c92800d1900c1c0303a00801404020800010800140748414a60715070f0b404c084502540541545d4540c1c411003826030328418400e808003142101500058454034042c0a0103040340d5901c8039504081d1078603201c1c0031550380441081e108507082080310b0700700c3d51151461b55100d280300034101185141001c0c1050304100c5903500a9214609040600c441294086804090004103e507104032040e001c4ca4105020000340c001c1c141e00020140c1669145076042000641068085a45600b00c0e44d4 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 775497212 1250 775495962 775496003
    0x114010b04060224070311041a071506060c0f0f0b251803020105130b18090705210907050a090f0b0102070810020a030b0405040c080c10080f0a0621 65
    0x107804074904e6503580d882d008180360a000768405024180d10000e640e18194031022044624081e0015400c254407000621200344448000c0c031103110420385005014180c40c0c0031005100b0035116001030301440c4150204420041c001c071040707026507884550300c03445142c005089c00c980d81800d001c125030022004a0716122501c12450210f44c1450960b80170844c0d825600111030ba170308004001020014072441c0810240c3e9094041c3c000c8480d11640d0200d01d0700c0c0c00043c01464400680a0f1046c040c0900c10b505031a520030301000d0412555507030034038141da64a5112841c0085950000f504200c00c800c0100300c100c841d402000d1110441c2c1814450582103000481e070304c0c01a8482c5c0303011a000901340d484515400d400a256590031460302054000781400080c04a400c00e4504445140c0628401c0104240a12803402d00100888004092641d41c14000d4402c0c1c400a00824071588a90005501ea501660001000d0a6548088085400c1c00780c54070b01024864202079420066002018a4600 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 775498462 1250 775497212 775497253
    0x501030c020613052d160303120c0909020a05070b011401120e01110a1211042117040602060f0a0614213301050d02060c0114010b040602 60
    0x1945a000b40890359410101801c0c0f81061030307080300d4a0161029807240407940e941114000201d070394101340701138218407031140350503050000540c034018080300410200c0c0e000b10702000c1804e8282c10224003080c50030341c115403401e504c1e0400195940701145240b00a50300102404880d440703403490f6001d0740d8079030002c6400e0101005e04540010766106030520408141e40000320525003000010451702803a200da801e02e600700303030000303000541580510100c6200034000c900c0708611180200345007e04080361412a00c22110510015480504054040000b005100651043d4200050782c07640c0d11131300029183e1109503040803c980b4010301003107200c51544600350485012000d25291048010309101c880468104020510641040f00300410803003030001044400605019516211000660301c5d990140445280c2c1842c480710010303c6283c95940134074070440c0c1c0440d14207895070071580030f850241a854020b194000d45440001441c1401040640282e403265000c0d243d004400007504400348 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 775499712 1250 775498462 775498481
    0x24060d060f060c1a0919060e0a0b1e06100f09030803010e0f071b030e060705060903040918020303370905120c22020d060b04030303061509031b0302090f0907050103 72
    0x60704402d10400e0507154040714480c6d1544502400f007803900d509040c0ca401c280e40004d0981d0b483c07025004101a0303400290711907207103121800c00c0504d18145000840c00c00c0c4604203074002401041c00b13100e65424007440f15000115848451190f8a42c0c49501d030114428003605c002500b0161000840c030100c0c0144100c400c0001c0c02c0c040000d4164144e201101c1500340910701c0c6410090070000c00307011030014440548a4004080155036980c9480b1043c02107a01b56490100e040890a0701d4000698011040384c02002440003022508007604411b034000a64003002502e00142000c1c1101416421240740c4c411500110340c00b1907184c41c0703c0803082d03c9010059400794041c42c00302e01101c403004aea04c0e0700e46c044c4012000040c24120359803441000ca0320160403010074031000bc1800c1040642c1406035501814559525034125081c0d014007504a1440b404010107207035419032240444028030354102d00a58005040703080d581400c90294038111400d0355088511301414501150550107400f500104 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 775500962 1250 775499712 775499731
    0x30305090a0b040f0c0504090303151403100f061205010c02060709050916030b10030515010504060503180a060603081309060815040c030b09060a0524060d060f060c1a 73
    0x1a83c03166618031050700c03190f404640403d0010804290b94440744110800c05210751400030310440380401955000300180d124810700c0c008915900443e4070301107000c05102c4101c1002080d000c0c5034a9810700980b09980011600b0f40c03c0100009c180041504000c1c0364805075029161980c4030100c08072100d41140c092103400c0aa07590100d4144003068610040405051030005500080743d400100c0740c01c1c03040c5000c000070751584240004048400c03511901d01c0d00c24242107240601d0101c02400c5400b0042201d140b00c44442900c0c4810a418010080d000743d0014007000345035220b1074000480d810080c2901005452142e012550040e04d201d6542600e6990005101d0030368150400103480200601c00c0b00c842d60040d4000001580d480002e0340a0040f4a000d060340d403824003500411920300800303490002d452003810031405101c0c141c00c080040e60075210150707690810103010019110582c0424002040e10800080d01d6174021007070000180b040d038a8140070500009111074401c01503810001 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 775502212 1250 775500962 775500983
    0x140d061d1f11070f03021f0c08060f10180305070f06020f0a0206040909170406080f0c03040b0f04050f060c1b030702130b150c0606090f070c03180906080109030305090a 74
    0xc01c000132460780c403007442881120801d00503061b01d080d01a50140035540308946980024110507017040c4500d5029100342c8032000405054000280244403040c00b8100b8071440f110a001d04d100b25034034101c0510b40140407108482d079a442d156410b00d80070b00c1091700500440d40c881004120100e21034030b051390000c000070300342810990848018042c3c1c000441d1300e002038600806800c0854406080104440d07204d07907489180c42c25040603401030090541c000c09200300304203c005010b08600c140c201c91821100032903956503151641c60f182440010380d00764810381c410450b4459441008001c07410269494001c5a2003540c000c1d582c07402040e00c0217600619065644904800c164041d443d02c0c2401000c1002c0441920030201d110750000003000726075000581081000e080c00074031ba5401030300c1d03020b07a200c0515180b40d00920381802d0390f10003020031100b20024400623100c02011005071080b640200100c03999949224000c00c0340b00c2c401c6021904082c002080b6500204000040c1ca810402154 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 775503462 1250 775502212 775502227
    0x7031706060d090f020f0a08030322050a14190519110604030c0303030605060309032b110c060f010e01090f0f02031801060906140d061d1f11 62
    0x400114010559a0000750030b11011202d038110340112510240629007444810039580140300c41c110480d286a80954400642082020030000c11298070a0b041c28030240c00c0c030300f0740c403042400c900141030151052042407010700600100014000303100c1008030448641b4420a00081c01148455001900941007030719003047e4a802c4203d80da10180c0304083311140d820000c40050305a4000d07030070560300710f180c52501b0300425803d4801d800c09400125205421840c149810303c2e80d80c41590040b0880002c00070040d4002d5400602c42480c070540c00806000e50905500c4405c110340094003840300a20824010417045c50315488100e0594072a9003800782c241c0e00304004400a8029501c100c030700e86558136440940c01407240702550142c221502401e481c001414401800d42d0304076001043c07890b260100030490142d105d4410001050265040701481d1051f080c601c000700030000c40c1b0b400340421000c9451300342401184004030030b004150246d031005000000f51044805411407031002c0c1304104181d4 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 775504712 1250 775503462 775503497
    0x1030c020705041e0c020f060c0f161104020f0d18051e0a0c15201b040e01020708030916031a09010e010615021b0604050906011407080a03060602030703 67
    0x20884c3c0880032520800c03c1c0e00f00032030811124114042001a00000a031203940c00c400d012a54202e40d40c3d9036540c0c1031030180e10201485d0700c100e0543d40d0209540070611020815031001034080020300400440d102d1040c03542c2140c03907a00075540c040c081c40c80c100f143c034400c2e402d81c1001000142c00c40700070056151060914040c0200240d40da652900c60109180300080003440603401819441c0d000e14000002010050440c111110010801810150b0060072900c000903460041e0461070b441c0c84140010800072500074494800014280d500005404081c842208001d501600f09482162545c884e681c207042a203054ae400000c14040c45d04203035000d90492015401d8204d8000000000c1a0f45295451402c4034075660211405402ca00821415990107012801000400ca45820090100310700058240c0c8201e000f400d11844490000c1001c40e403051184483c4001c502a4041d0756041c21308102196400001082002234101340011a0b010f00c0403040c0c0b07808503890348039510b05440c00d07087d1 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 775505962 1250 775504712 775504721
    0x10302040b031302030f010204080703030f02061e0a2702121b09070e100c0c0f1424030c0301080601170607032a030911031603080a020703022d01030c02070504 70
    0x143c1e41486030203040c1640c1c6c0c3c028801030005107881c030700038007020b842d41c40c01409640d10801208190342007003040054a07900aa0061f0840d8601c110300007055681e0011840241000d4004c40203084041540c1e40000404094290506001f1200201c1c407a250455042c0d840100301988904803014420b80301050625100c2d00e60080c02d141030502190182130007151034100d011182c88000b4124542100074000880948005000c0c0d11028030b4556007025036034280c00c401d9052540c01055207031480000c02d203100141e040e140b43c0390001c5d80d550b401c0000c0807108941081c02010b4050080384000122200d00c5602402010103a0300508000c1d580c581c410340c0104590800403022030110103000c407a4154a00d0700440170186500d00059011050821000005888031110b000794845101841c0c0c03126040c2004080f40d0b40801c01c1070b81e540c00c1940403820090300d941700079004074041c004802480d141c10700d00c0381c410a41444203071b0010341400c011410703501d8802c40c250140e0042007040c002418503420 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 775507212 1250 775505962 775506001
    0xc09180309120c17100b0306090703080d1b1d010503150405040c0f0b0c060a1103042003061302040b030724020a1509120906080f130f11030c010302040b03 68
    0x2214504980d0729030501303085021020a01060340c020f05001c0310041c03094440c00c400c8460582c0140b141e40b400602082c0d0b20700c000d010107048500c001c501c07109041c2c1a80c101e44000f024040410088095030400035080100c40007030062042d80342140c041095100b001513a100c0d28424002c110800003903c18000202405031043c0c610b03418035800881c9010609440c0c0008041071040380f035680203104001410064003070101240da90400c55200300620000d810380742c100780c05c605142503025031804a500c103620300000c0079803d4020300041082d600220341e03002c5007040c020344003400009101010542c566415004106405148005840001c1610f840304d21451403203004440020190351924a8100c40c9000c0c1000c2542d29150424200410b01e0290348018643d4140f03842150300b06000030300f510400401180503aa5003a000400080d0b4802c0995006e54100908050414203410048185c3d10b0401e0f907940240300c1d450315409107500c00d100321030888851000c0581103803141c45056540075031600e03 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 775508462 1250 775507212 775507223
    0x3080612010e0106032a0f0312050c070e1816180b04020313060b150a12110304051b0102190209040807080d051b070317220c0918030912 60
    0x80c4149042c0310074413a21002c0c1d0701a11858040b90b032204c40c61b5841e043c401c012080b603420b035407008100c0680c40d0340c00a010349a0099410b08900c41c0c55508031500d00030368600c002c2610880c2030020b988409003245a00500303e48000c403001d101c0c0200ca5903070310f052510030a50780700402c00f8200a004003458a940c04c3d10100940400c111003000c00090036a081500c2070008500344502403020045d030b620410050034010b070740503130300320803110340c2503e4a000740c038811780901c000094040081100f907070190a20b0507c01074210380b00d00f00350820300d0756034154900c0000340340031038207401482d5800041c42409181d400741440c0d0148640c0ea00748070a035800600111018481401007400194070100504000e02078090002150318100e20204160312526502e60504282003104c00d012940c410031016040e103842103241e5103a1585492084030504480c16034800040124001080040b5004254110740e8110320902c07800407603007541886420614001404190050b0081081d11048409030410f42e0161 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 775509712 1250 775508462 775508471
    0x150105090610140f03062b0611040b04030302030703020709050c0a050c011d0d030b040504150e120d06060809070605122e150c051209030f0f01050714070308061201 72
    0x42c0e00c25090380e046082013610144012003000303070608041601d40c210040c82c1e045451008100c211121b6011710f10913010301800d84a81c01c03030000030306c0c1710119001000500aa039a545982e07043c003d440e6044000c00700c0050142e00c40c002540001809254010020a8811440e02c2003503c1d0550f0307507034886000c1c0c1200303548406085104184401c10703541c5020034523000c3c10240304842002000c49d12021526442a40f0300740c24040420b00840e4992040003412038002001d900c000880c1745008808004500f442e05d001454400c0f0b0610b64000d4400c984041e214000705899100c0c00c25210a80390007200c00003070b4184104880c805035660241d0b00715032129000c00420803507150100429040e00c2c0c1c4c00795501e1100d80100900074424480c2c2410b03040030b26180c3c0015a00c0d0b41c6d02c580b01c0d0300c6400746409140001c01c0300710065405000b1342c900000340104030f030321080d80c1d030007511b000c0c01c2c044400070301256100074814000320001c0c0465844690640d070310442d0f40d440310100160071880c18400010f5642e00d = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 775510962 1250 775509712 775509737
    0x91504021b0a141218060d0e1213090504080f0901090314010c120e0c1e09010305100e03030f070c080c060f2a04290a030608150105090610 61
    0x7400305200c86070080e10070902041c00c0b83d080c01d152903038a8100780c0003082d00b0031030500100100c000d11310403254121180b607a964403076114030b00a803031a40c1020400380034025010304101c8294000b42807840611030f1000c001c46d80c03026804d0490301c00b154060050f000410911004035405801440713924070505000c840313103889031118400300c0d540040d800c0b0743d07a5607030031180788081c0c0007401d40000c00c0e80b010302030003071680b45480b050b150010445064040da071104050040ea4050b42e00e115842000540404003d60352400d085a0782c218bd411380300e105600e4260321003034441010084a128003001028102281c13107003281160505141f042c151079000090181d401e06203401c0c00010f0180d001822104030b41d0810160481c600b000c9444848102c28000010b081c0507618082070700e0440f0f00e0007100300b0706110440d080e02d0703244c00200300d0251807440000b025580c903501a8007070825074920100701c82840b100d00150101504084c0526035104070b08400090052070003000f0058452206c1c2f80440c1003550 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 775512212 1250 775510962 775511017
    0xe0607020d051c02150c120a20040302190b070b06032d16081005090a0218070f090f052202180306090109120f0504031709040b09150402 60
    0x1400c82c05812a1010442d8580c002a1304004880c8200e020b02c014841c0303400c0054506525108221505100d4821100010514011139010041c0d103107006180909a040c00491140d5a60060104030700c5810070410728002c90350f46445c045e0503600212209071418103a5103c2e0101000001d0059a05204120003000000d481a1603461034844080510080c400c80c200d010f07051183d152000300b90400b21520400c181c000c0010320201022200d6400034060f1200c0c0c1201341010500c200180d08203035442c02c130358449480d80b851248614159501c03240c14100101c0c1c01c0324100301c1881114500405481c090003a4940b0361158600000300b01c110300c42d1070144415031000e903080046201000700305642440c605003020300c46d196200701a40001c01208400703035110808813419542540400c900c1d4100720700e215004504440c00345400604550030b4502201114480d039010000321406a410113075020200d003030640c4514000c0c003184695402604144007408001d400c00c6203c2001750008040304003035201c = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 775513462 1250 775512212 775512223
    0x60403080d020f160b060d02030c27090a0b07080c0d0509210c0f1612030c082805130603050601090905010e0106020d18060509060409180c05010f0e0607020d05 70
    0x441540c0510028543c505000010940003840c460244410454100060f5004102b0301d142100c00c5446104040c283c0700bd102c80011045c4003104010074090900c500648000b841c000310b54400d040c1c401040d0ba9032902103803511400e46410341d01040c103000d52070401c03409030003480e8403103142800c88903414007808041010b101d0582d56500c07030f80701c002801e24618909003d4150350309040401800c1d403800010003000150303105d220307106642c02091524400c140c0310340c1d94081d02036040400300303071a000510f680309003112021042c00f4200007501e51008496000340195241104100c00c500b540901d40582a400383c40b004042c1b604102450102055078030700d510685028050b4018418640c3d81051400382c0340584101c0c505052000b0300000b8220048800e00100603540240303041605e8011000110f01280510b0f0000034400b82804000212444048a507031206802a243c01d85d4840d034400054400e101019a184e001501004840045040a20003010710311b20240c600d82303000003182ca4003030909 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 775514712 1250 775513462 775513477
    0x30f0714070201120e031809010b07030e0603090a080304140d1e110c10020a0501060f121e080309011505040608072309012909010f0c061409030d0614060403080d020f 73
    0xc0d00c0500110123030802001d2503001d0444881c410345040101d440103080c0b512070402052051f140080004c44192003480710410350380d0700840c0b00d61241054a40071000d0411080c001d01c0300d1050100c070000d15481004800080d45c10301a001980301c1c0042c1044981060b4082000602d00c103006450f03080391619054001404000e41c09000ba41c0010300d840b03400c0d03c1c1142d2011566165402090121a1604401e40a4940e205070411414504006404a100c900754401b505114010040001125041d0412040306018025800c81e9589170000c0204484507806818042c0d88910b1040c0b044032291b03030407128500c194003030a02564038110001884408c09801c21642180f900c0349003c4034001c104020101c40c3c501c02006820001070b5030000b00038401c103018260811135120140414003200303902c00c825145034000940024503254444c942da9a00614002d0165440e1030300014410086181e04401d50a0041c02180703828950340b0340280c01d0300404d80d6100ca66600304550f9404020740c100170700c0312 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 775515962 1250 775514712 775514737
    0x70510021506090709050d030c061409010e0105040b011406220e10140f0f0a030804060e0d170705120a030510140a18060b0f030f0714070201120e03 65
    0x25041c030403001c50010070003030046802103500c034080c0100180c00040803025650252191080080207044c06c640c40b80a42101825a510701140044a0f00001c0881840384009000078002203412014050803940215009440c42c00d2980040c84004007100a421034114002c0003a801e15041500000f035100051140340b401c1800d51030104020b1404442c4581d00042800e0501e142034503001d0210103405110200c0c0e84582203140002c10256204850100e140034007420f00400903449141950300ca0f23000380680000302e61400320885051500c681d8034204c080e804800304000011054000080c0d070003240c1c00311018050030a00320941484800640142c1305160f40c0414070742403840340e07807400480d03a030040c0d0001c000344040141180c690040c0b24046608042020303540c011003640c06001042c01d0b8001e6400b1220000345800c241c01d00401550141c2c02d1030304040015110480199002c66070541105e9001c03a0900c0b080b070141d80100c11039916404210310200710b45e8540049681503500401e0040d20 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 775517212 1250 775515962 775515973
    0x3100302040513051b22051b0c0703020f010519021f020708090f0310090609060b030601050d03050c03041508040c51050705010c020601060c1407051002 67
    0x29031a1501036160041881285440402481e0b00e8040e250b0703c49031074541d1170400300d0300c1154158850071181c84c0b1700443c455030300040d1041c1d0200140070341070580f83c4000c42d12000510b1140d074000704080710804d0b01c000b80282540351441d4280f1401e0800400c00c00d0611406001c20103507c03400d6010402440b000d54094458010840b00f19100008641c094819030b40c41800312100003030401c000c44907042c8040750721060005040c03000a1421002203c0382c4801c07401d200c4001c00f045001c1e00700800c420301c2030781d003400311059035000e260b910300c401d2140130340c0041c41d007140b030f0302003800380005085124000342a24601912220100c40b0107040e031007441c000030004070404c402e2245d01c02e01140a005011f9102c1300e0541c1c2269410383c9103a00b40192103540f05a8420032075041580c0b111000c950314030304104048101780d00c0c0003074555001040103403615401d00f18683d03070503440851001e05803140c03901c82e451503004685411aa0b41003441e00c0001e2480f40f0440032425560314400b00b101c81c0c0c00d5900420 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 775518462 1250 775517212 775517219
    0xd14070b0c120f0f160905040902131d010f0b0901030308070e09010303050301180b010e210607111c080a09140a080a03230711030f1c05010b030411090c070204020310 73
    0x181c010600401000c001946045c4c1d1951950740030a0503011a1000c540126070440d450000a420855101d03203109041d15211a2510000b0b91980c0018086412002080400c5580c040380c0166260280300c590b1060b0103500500002e409820380b00d800074268a4035030740d0f000c0c403240404c00c00c100a0308150041100400100311818000555804180c0c0b00841480060f416100107447c5004d070f0780d501031064403040160404150005d5036030000c2c1c2c034a1000c5a0340350610721030180008514443c0b020a03805200041c03d100c104c2c80303501c01100211a03451800c01e6803000725000081c40406c1040741e80c1c140403d980414103504004280c85680519050340d80d81e01416805001c449807004007201001d4030840c0340c1c1d080c2194240b2183c0c8040281452480407070f0040c01e09003180319804100d00e2006000c501c0300d19241d0461512200e00211441c100a1030340c980191a1287c0011a0010146003090030341e20114180f40e8506904030000c55800c90030541241d0000c0c0503600304442540b6102e240d80d5040 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 775519712 1250 775518462 775518481
    0x5031003120c0c0605070c05090603010b0d1a06060c0d050a120c0305070306080106051c0816030203070203061b09010e0a080703030518040b0303030708150d030309050d14070b0c120f 80
    0xc03402054182070146c41c1c1000f9540342050718484c1d10405104d03c003041c00051007528290000c520f8654010441403070103080e803402e010305041c199003826111400000041c802c0c1006002c40303003e000c2d950f0080c00c501d00c4002c0121466842441081d003000118185c0c549002403d0190059011450b1004a0070349401c030740090854405074421942c0c0c0c1e061050030041612a812580d010510109641420102d01e0500d01072500c10134140052880d4281b54000038140e010020b407207214403c80941c0c8070381e107440c0a01c2c2140004280c2201030340104011007065580180c01d501e0070004043c164400300e5070744817141c43c01c1202540c030036808107000003040801c1220a400108070301404641c10010207100c080400d0f960700000b02400203004003500440d00a01445584030409c100c010b020117845030003132800030301800301001d0496080c0304040c0c4050b62180501c04500c015070b44d00c1c1005003491011340b1015000000580356054a9400300400454a0260100c0c2c0788201c0b00940b211075a4242142d40e03 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 775520962 1250 775519712 775519733
    0x4050d080d11210604110f040306050a0b0f010e0102010e01050901060611010213051e04051806060f1f050c0706030603050f031c05150306070e042a05031003120c 71
    0x20b1101c400820040078071241003903a211040015000502001d03980c0710008034004240d400300b0300f00c500401040032803c0460603401401030700d1060600b401130b500c80302c3c2d40e1402e9810441000e58408001c030692a003651080c203c28000c2c6c04c0c148004151040481420b500f191016100280c103651101c0c402d011a80d080840c51040c801d030140210318000030703205125000180d50141c140f1a040c95620b0201c2c40c1e20f032114100c89441d00070400c00140c00c02c1e500c1501a00c200388aa203650340154800100545001c80981780201c1014040c80c580402c40654603a8413281031440038180030041c01440d014034030811903000504400c3e180011180c0c01c48c14024034007030340c200c03040b00305900410450f0081001048800501990040c02040c56121040c1c0c5800c1c80e804580e00d10b0b01032052104000001d6840f00030f8101c0036005036001c024134021a2600c1c0c0c2115024031854030b002c41007d00c001102c600c102d0045610504901001d541142c42e90340c5c01d030300300c01075800110009a95602080500450820 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 775522212 1250 775520962 775520981
    0x2041a12070b03010e13080426010c14090301090c0f03020406150c0f03050903060f01090f0212061c05030d0c0e0603090c0f01140c071d091005040804050d080d 70
    0xc203609481c0c60b038010954030050059a150300a404045800c51100f0588552443d034401c1c0a41e4a0795203680d400c13070002e2181e08000e0360a151080c0440348180d81071054103400c802e0307961000095103401110304240e9100071185a0150359403854070300480c03076040201c0701a140c0040200e00c6141755004200541d6940c0d0030103000c0a0003c0700400d40c02c2c0d00944036885240d0301c129400c0759403400d8241510207020705c58030180c06006603c10040c4012442141c641039900c580c45c100011201c042424040f400b03008804034030100f00b41c02282c03803490080a18220010141e454404e0300420380d6a05045402044200490b10340300d0201c400e25a03003021000842038425160039056180c800e080554852a4042060042007840510010360744036441004c8952181180030f0b6131401900a05541d4000510445422900644000082280c800d507202c0c010342074100105000f10080240000030000070300f0480742150304001c0050242c4a15024a0b005800b03003101d00c1c0c4503180c500d992030030341d40d2004 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 775523462 1250 775522212 775522249
    0x60f0301050f070c02151603030e01020c1915020403050a1a060904230601080a02130902060f160609150c020708100e030d0608032a0d05070f02041a 65
    0x60800a00c10380e0003030540d41c8000c00c0d02d44141c4c0810079001203202c0150071440000303000400529880400c02401281211030302c00da500700700d0b081e80c81080c01c0c202c2c0550070329011240c016140c8a11010344c0040500d8a0703600035868038030313031500b0b02c0842d0782268010351040700d0980003c200c0c50213118881c1d00f4030050242c1c0b030007846440d20b810000100c00200061009069180c1c80508240c5411161004800d68048204440c0d15585540c1032980e5041142c400b00d214482444040080326001e001f030000c1c7d554050856800c0c4036100384031b29402c1c1c000c8454005001404001d05000c078045000751032500b8040d80742d5002c0003500c400712005540c401c034800c1041d503004604c20030210000044510444428060000720403c8002085083d445030f803a000b100103060280214078101e0120050030103421a14082c50350a200d403080d50a0114104520001604000030b02d91245010300010306206100c3c05c0101c1e0a0300c4a980090b0468510345409140d2180c0703100c204003903040207280c80d10500d00f5038 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 775524712 1250 775523462 775523471
    0xd230705040b0c03070c1412030405030a14100f09060506010f0e0402161401060914010b22170705041808030a0b060f0301060221042d08070e060f0301 66
    0x80402509620407449555004100080d1a0000b0320080c0103480302c143e030007140c01444541d9400b00408882103840600e01c103614410076058204000400c40f0201e40c1d025025090120301380d210b0b4402c00d02c03249804c0d83c0d240100d00c0c102c0d00310a035030b100c1c1c404c0c403004096000038450304a0401c01c04030f0b6801031804d41803101c0d901e000506103800802c003a030520b204850141c2c2d50288140401417a8440c0c5100608681d4200c24152600e4410340082e0103844e8507210030802c5611280031010b021000784101c00d800d40c0c0c10005403900524401d00320140601d0b1051400403269a0581d03034025203010b60401e0b605412074481400b030382c070b0540600c04121003e101c00c0030005006031561450741c40050f0245009903681e0400700700e20785802060300c0d094203040f02103584a41c0c1d03d1001170b480e46140b86042e100c191300340002d002d0705c017038030803c0c0c03030550321020451000c660802d00e605074103c510328440200c090138841c0c0010030660402402025080126003014603081603028000c505241000843c8244d040 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 775525962 1250 775524712 775524721
    0x120306010206041b15050d2003070f031103070c02010801060e0a0b3915040b0103060c030605040204090606120501050906130f020412050d1106010b0a0e060d23 70
    0x128640c100d904198204003030440100e402d50080003540c0200180d030106140400a250460701806003041004001d10041d03039082307140810145081c0d10f800502e01c1c14804a81e20501c03a030000300219a40703003000500c107081070711300c1401508112401c00001701c00401c901c4c01c65901020b814014005810149a0305805100040207455180a03500100e4004181624007410b400e42008542140c1004800c14086590a61a41c846000c020034054414007140310030100400305020f10498000344074000d07990031035a60300003602d510103c020406440f0440450f0300d6032a44010030084c2200580042e0081c9040006030902c00800e000000c01c5152000420290b16000b0301903510060440703004c100c0c03550310300c0c00d18000c00064007007241e0b56102003002f140c44031a00340742502c014020822941c1c0411807010803191040100c199051a40000004200c908012006885405910304002150f440904042406600300c1e00c544145291610144030150741ea240c01c81604c41401190190603240 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 775527212 1250 775525962 775525967
    0x5011406130e0322290910020c090f0702100509151f0b070303050c0c0c01110a0609060f2f0d0b040f0b0306060a030b010e070504030b07020f12030601 66
    0x19031044030102921090700c0b00c11080240112031820348000081046801942d28440e5100a140a01070301c00038038a4404c48002c03821400d25140c041001800c5c0d1400c1249424001280354020320701040d0b00c40c100040030165070b0020424890040b000f00e4000340d140010000b0b1904094803801c44032145002c090100f0170101288d226015000c04551200391303110401040b00d504c40705000030340f90440d03480000c60041000303001030800318007958080c001c94840981c07004007071181d0100540b85920a1004101c01d5001c0c80c11a0141c0e084a001e4403410052038503100241c6041d008211005959809450460070251081d1aa2813004140e0340d02041251001c0d0b480e41302c240301c512a201103012410004190454001c1ea1015002820500040b0801d00d609000780030340b00503c5129005440c0024072505016581c001142d41082d20141c0340c1c1d1038a00c0346811480090301c041b00700f01007007201201103041100c0040c0116500e5000b8410201700c020410f060114021204462240402c1400b50a1380d = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 775528462 1250 775527212 775527229
    0x215070f0c0206070317090109030e06030f061504150809071505070809040609020c0303070f1805010c06020c0706081006020d1205090a02030f1e060103020a030305070c030b1305011406 81
    0x1c2c1c0c1955119610b0566040548a43c448410110800004541000407502042d0440078445209494800741c007410541081b606000803600300385084c1c01640040c1251800001914641d1220310b54649440e4550708000034000b0700d01c5201e0b008c10540c80c2889403000081258500030084a0010820840101002040340c400ca0b80081c0c44480042140c4a2945e01c542c0082e000b842c002004540d40c4105003009626600b0071105840820032460b10162200c2c05484980415091610780d10700c2c1e01d04150044d2400d900c10074042e00c03101c0d030074840c48203548010425113000d0411134890400c280f400c07008241c498200390f00820119081600c0046c201364101d854000d1040240402162030341c0e03409a441c0ca40214800c1c0654107110301e18110400400104010041e0440c240c41c081d01045180b1945540741401c3c40004e4000f80044c0e0100702191041014203481e074803c2c0540085203940b91541c60100e6001d461244014809020501c1009000d00c2041010140c03940001c40603d8003400240000 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 775529712 1250 775528462 775528487
    0xe0a0207050a030c0525060f030903050418060f0e0624090f0105390c1311070605070518040c1409040e0717010c0206040c0612090506070215070f 64
    0x1404203000c50410009105050380140c1b0030815200044807224043d81c0001c0c24071414020400402004459070303c24041c5c00d00451300364030390070f1905151507000ca240081c0542e4800c9900c0d601e4201084483c41c802401c0024400184016420305080c02000b18111000c0e1564950784a01182c401881c1d00c003034240d81e4801e0703080b242c101900f03440c640140d81910035480d8941016507000c1c0c03400031414034041e01300304c1445203c41445003090780003005035803507008030b04d96903010310311944185010069800400c00444090314803420f0400340d43e585411780c2ca064852002045000c6100d085080462600020041c0704540900514144c800083c1500310b101d86c40c000100c0c40001c00202d541c40da80c0101d036801c1d120604079114180d4416002042181c200c031518050350070070b41580c1d440c620000d5914003540d00025015421850008140c0e2101d14581c5c030b5003480c03030b1174814030400701d0307014400c00303100d0740e07a0b500904494090380601d0101d821000302610103009c41c10800499583d40801c0c5a03400c0d = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 775530962 1250 775529712 775529717
    0xd112b021e040c020d03110a02100b0a051e010201050c0702060304060f0e10051602070b0d150f060201090317130f050f01050412170f0a1a060d02040e0a0207050a03 72
    0x3090040c0140d00c0054844a02250014103000f14100c409a0001e1010141d100c1542e00300100400d000010169224042c100030043e070088440840301c03049507206007003840700101201c3c2c045944101050a400821003210703494407582c0c1c201d10301560280181d81e488106e8010251800c0066030016809000180001d06079a0b9940344a1105248030781c00f0a00310f280311002c640401c0700d4400a1400340800303c031126a031a2024190107445800024010b090b40c4521001a04141265849500803e8000113054000550b048001a0460b100c00c1c0700c409810ba90b800882c8104c0c160801620070a104028024101c100c5810400c5640c2c130140c0c0c008007150300c0996942500c1e4141807103132904120203958025035203410284001c00882c03400030b042440c8a0744418a42201c101003000300c22100315110300500e5000400a88968820303404080f4040b1450a803038000300104002c5009604006441c007581035002400f4451080d4424249900040356881907290500940e1255207a07141c00e80e00070103 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 775532212 1250 775530962 775530979
    0x90601080a0206180a09060801021b0115051c0f11031e120a110312061201020702180402040914010f150f0909150f050a050105040c0206180c0d112b02 66
    0x4145e44041544000300b8811106102032906c844009000f5442441c03124240c0102a5148640a0040c020200c05200904581c00220b14081c14024540322485281ca14200600d101000145c801d02c44454114010f0310ba40d04181e110070241482c040c142c40704070452003100ca4424502c550001b451b0424084440c0c60503840e014020b81c19038921408400c01c83e0303140004698070b036040c02c02802c1148100c100311029072040e00440304123800c0f44a44000a50807008030003896059400ca41d81168000f803003c2d000050f05201a103031801c0f040c18211141525035140d000b240b007031003540e004656000f01011141c454403803820040b501c01041c54400d0145030b544502d003031020700c01e45a0321181e800c00300700418000c00c0d124900d8503004001c110f0b942ca413040d10340000032038581001c7c0710fa211182090303001461240c0326000145049064010711161512581141c200240c945403600002d0340e21130030414070811aa8010807140e83e02c4a000600d4880540c40300f140f206d000025803824042c0c06484050 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 775533462 1250 775532212 775532257
    0x80a051302150a180e0906100b0a0305070c1401050f1008062406030c0307200a0b1f030305090907080705071209050a06111501080a020405060d0c0b03090601080a0206 73
    0x2103c0c8106141d4104d0409014034001134440c080e1141244260300e10341c11340b4002d41c0d80c4107481500629500070810004000e02005403018000e5100e00e0304030181e400c1403581d42c8029601d1600188904a944000c0d9448806000842524180c80c580000c2411000c441050038152600d0380e40070000d1110584002d070281c00c0a048064859500d400040034102684d2443c190208106540c41130380c00304001461035599003140742c81400ca01c10f0b040120009015002850744401c200c40d2005441d412295a10b00091182d80480c040042e004601c04c1e25a19150214071302001401d400040600c000d10502d00300f00070445a0040848481a40c00207034005684c1c044001115140c015401c115003041c0c12150124869030885803502d0028184401c5505090034107400b900350740300078400c4d010b042d40a04440c00040c900350700015403064000e022403c4484079a2643d641da5442503000320441c0000106000c0012424041c3d01d01414024006200381c1c12198080f0b00c1c0c600c1414048140a2003411212 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 775534712 1250 775533462 775533467
    0xd050606040815010f090207020609060706150f08060c04080d120e0706031d1c050c0c040f05090d0305100b0708090a0b090f09060d020906130903080a051302150a 71
    0xc0c0c002e012142d08640200008510360f40100308280100349207280301c241e00195000d094000c075101290302504007800c02c1059001d1104030b82086108460007074445103105000500c1c0d00d1458010141c41080150f600e2510050508007803028200403a2040100030902210000289180c00c90009160600e49542240b41c040c0c0185120000c40416001d200000110a54140c0041d14904480c290b070300980b402c400c800d40c5c1e80c0c280d007504c4028201800400c140e1982d00a41c041c220620600041e00c032481004400142207400440e03242d0f03641c558850034801039100800000c010032950f4141003006e4201020a00301c0b10300544aa41004000082c41d1002c009148050f503051078409800005a5520703002c3d22903180d0403060502e07016214403c3c10a680e450000c0d11103025400103421304110311140d03000c0c800c0c1000024689500680d5601e5046030004070f51040c2c241c5039002c1e40c3e489640f4102080a1010760710013030143c11645402024400150740c82040130904544401e92b190b42d00c15007140107 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 775535962 1250 775534712 775534717
    0x906010215040515130b07080615040305060703060b0708040515041e05010f0e0f04090f0209010b13061e030b0a0b04030503121b0403170f0c0a060c020c060d050606 72
    0x1001e040312414401002400a040000030740c11101310b0905603600c440700b50141344c021401400140310750740800e000034007a85009030401001303000401e010701008892451540150b1040b04c603940130b50108074540d82d040c410000501500420b65241000d039869035041801786008441c803400c0c40c500c2040304d0405aa0444004101d0f04d0a882d190417225004607600d17280a1059502040a40f40700c03609040c4181540b02a0000082c0094250820101400024180c1c5a01102c60860315501140540e461460b0207000b410803e0a0b596a44000c071414040b62403c3d40c444400d1101d4002c14403680031401e002a800c0c250589800039055901c400002c0740c4a416a02004600c07000207004030600c0b00c0031008007400040d448a808290b114400d01c10100e490004100e02d09a80a0009000041094891404021403551420705040352500002042c0c0c1c01710210400d150b00400da20810031085010301d03118019180090204812102c0200b0300c50b01c1a44490f40d42181d03150000703015541c90905 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 775537212 1250 775535962 775535983
    0xa05070c20210606010206060a1512020d150f080115140a0504050117011a0f13111902010c0e01090b09030304080307052803050409051305010c0e040b010306080304030209060102 78
    0xb161611602c6040801d440e114140c2e41c0c40c0c01401260000b440710f00740440c00d441120000c0710341001c843c051140072101d840ea1000213000c2d0507000c0160a580400c42d00518001815815400402c43e01c0d10300100782d41c9006520612040c1d05000c0002030400c1c1140383c0a00b15082c800c48001c81101c618001003c0000380d4100681c01480c2c00b002103226510b800c00c425118061400030000d811081090525481c407c6c0507080d8820440000090b250031300c8400724038118008107000c15035403c1003211315210b40181c24401078060880400311031660342400742001d092103c0c28a0510700c802480000d04019440c02498054803000801500c1609c1c1001102c00901071a07040c0d0703868030458074040352100300380340105800601d0080e80c10694207058a080082c2a03050316454030385843c0c0562000074160040540ca4100b800322401804150f085c0136865124009a4a8048092040081104669441040354100340c42c024050040d50f8001003110107803501283c2c15049580c1d40070040385490804403 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 775538462 1250 775537212 775537249
    0x15020a0e0a0f06120608060a15030506090303072a11010e2d01080906040318081c0201060b071a0c07020607110109170a030f090506120a05070c20 64
    0x2007000036412000c24104041e5030361640d0307030744140395a012654150b6809005414590f009080410343c004495401186003604a425038800c40d6504e88607141027900c111000e00f06c2d82c00c000204988140d1107042d00c1101d5004020318040b011070030f03011070320241400390000e00581100100c400300d41e0180880c5904030400624116202d401d680f0707071400c48a00300000390500810003205d03441642c092a0001d2092240000410701c84e640c90310b08660b04000724110748110401088041a855010300220f1030200e034001501d00d1b0034a0a21009084031210f80c44050694018413590300051120011814840101c04040031180c90303542a0300c9491142d458000d40c0000005480340070005841c8501c640540240c0b107a1340352503918004036440c0000400801a290400e0590000080c081e002c481582c048500c0d10b00f0401e611800840c0e45540055060144045d8540800101034028041c01d03900880a113000804188079036264030343d04490300700281d5138003415000c800090f1a140d03006240c030790810 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 775539568 1106 775538462 775538479
    0xc030708070f060f0e07061803080310120f050f07120813030206030a0b03120432060a0e041d120904020c0f011e060315020a0e 56
    0x420840d030807940c1403010404103055104031302072041070381800580d0740c8400441c0b501c2c20001d40d010f00104010300e09185020002c1d0041a42169800480c5039141d03115180c40620b000c0142e00300b40714a003400402d80040c00010542000303418001d400340d90303804240200341a101c1000e40114444142e000030000d002500d090010045012304080d202141c58032503000614662050302c1d01503a4a1b101c0700501050300e03043c007400c204c107011a08070320f24103450411203694001c421122012010f41031002814500e1640c0795403000f0003401068143c1d110744d2910301524240c01090854001c500d449a5969110185101c41e22004990002000300903480d0719108e905078032040466810030f40a000d2954a00350422807081c44c00c041d88000328001584480b03216071035442c40e444500c02401c08004002080c2481c030311400040c851000035076076110000007500c040700c20703620460300464107 = true := by decide +kernel

theorem cover : BRFrame.Cov 775359712 775539568 := by
  have h0 := BRFrame.cov_init 775359712
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775359712 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775359712 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775359712 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775359712 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775359712 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775359712 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775359712 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775359712 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775359712 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775359712 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775359712 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775359712 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775359712 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775359712 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775359712 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775359712 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775359712 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775359712 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775359712 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775359712 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775359712 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775359712 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775359712 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775359712 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775359712 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775359712 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775359712 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775359712 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775359712 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775359712 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775359712 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775359712 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775359712 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775359712 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775359712 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775359712 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775359712 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775359712 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775359712 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775359712 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775359712 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775359712 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775359712 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775359712 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775359712 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775359712 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775359712 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775359712 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775359712 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775359712 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775359712 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775359712 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775359712 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775359712 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775359712 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775359712 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775359712 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775359712 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775359712 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775359712 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775359712 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775359712 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775359712 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775359712 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775359712 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775359712 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775359712 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775359712 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775359712 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775359712 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775359712 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775359712 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775359712 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775359712 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775359712 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775359712 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775359712 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775359712 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775359712 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775359712 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775359712 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775359712 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775359712 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775359712 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775359712 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775359712 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775359712 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775359712 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775359712 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775359712 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775359712 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775359712 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775359712 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775359712 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775359712 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775359712 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775359712 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775359712 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775359712 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775359712 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775359712 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775359712 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775359712 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775359712 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775359712 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775359712 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775359712 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775359712 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775359712 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775359712 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775359712 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775359712 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775359712 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775359712 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775359712 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775359712 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775359712 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775359712 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775359712 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775359712 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775359712 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775359712 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775359712 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775359712 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775359712 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775359712 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775359712 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775359712 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775359712 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775359712 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775359712 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775359712 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775359712 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775359712 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775359712 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775359712 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775359712 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775359712 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775359712 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775359712 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775359712 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775359712 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775359712 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775359712 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 775359712 ≤ n) (h2 : n < 775539568) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
