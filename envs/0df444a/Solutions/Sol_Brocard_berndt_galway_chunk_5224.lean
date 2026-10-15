-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5224
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T15:09:38.731655+00:00
-- url     : https://prove2.me/submissions/95f2e414-d16d-42b5-961c-a9146a15eefa

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 939388489 ≤ n < 939568345 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 939389739 1250 939388489 939388493
    0xf15032d0f03020c150a0311040503072c0c0309011407050301061b05011a091803070b04030512090d0e0a08070b0f1908100902090a09050618010b1206030d0219 70
    0xc00001c0700045134042c1022078142407080745032010341001c4006e80c0701000806041c00348210309010703520a1690541c8050001c0c000c400c0c0d0750441c8103e418a126981d1700302c2800500000d414941280c9162411601104000300c00c0340900030a803058081c0649030741182410240100b140c0b005000710313400d0094407071520102c0b0341600e145900441d00540200300740e410040c2e084c0001c0b02e00016442c810403000740031500030031403039018000f0140f03818011341c5049410b80d10354007802c0e4020700980501000740031440e0980030402c2410310403032600c1d01411003d81200341c0036002c1107640550a0003100106824840050005801070585d0f50342e41440d40c4450426910b41742c00d10a600040c1c03107103400d0f20307440710f0550b400c218802c0c020705000d2a64021248c40702d44940c1207014000780e00d039028031611010042003180b0b510207a00003202402c40c5681141013140095442400e03480800c00c0800080c41200c3c488088007103d420100c100d02a244c49014a200250348940b1403204d0066500e40100c0441 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 939390989 1250 939389739 939389743
    0x2030601120b0111060a0c080105030619111b010905060a14010e06060c03120919050c010c1707052b0903080d02040f08060a240b09040f15032d0f0302 66
    0x101388000348088800c0c5142800140703000c0c0c0003101e40100843c121038000300c1c041c500401d015118005c0d810a01442042509404001c3d26416580e101004400c0ac0581c41400b46c95640300b01440780d802c00403070b50214078a002490710b0340043c510040c8a1400c1645241011079060242c1143d400001c0058140c844100040c0300f48259400702d001444002440c03c4516043d009152190703a05000f943c02c140014171501d03180c003a64100091950b044110000c000350301910b03200e04030340e0080d4442401514800d1120078140d002c40001d80301c9900c05120817480c02c94120841c90300b0036046160034100000c1280c050201c81907400000d1400b100440c148600b03c402d039041d20014071a051032184815030780c40000746c84007416100d55400ea820721030701594005000410b00030b03000b1004154202540303007549000d440d42100343c2195105403142c291310242905402204d502d0039081ca06060207134610701d094041484030300744644042070318050b10000d140803d10002c6951790800580142900c0c01d1404074 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 939392239 1250 939390989 939391007
    0x80a0804170f07140114011502101802091801020a02030913060302010c0215090d0b090607020106030b0619030b010806070f020c060f0702060d05150a090b330403080a0e0402030601120b01 82
    0x61a001e05203000000c1601c6134024120230b400d0b40c0d4082e1781400c2c0c619480c0200b903981d128a0000328403074051007400141003100d800c5902025100b04806200d85c81c48030701b42a80c0c40200130000580c00450320054524003007035140b200d510742d40310400c64186182e0002e4560800d40402034468052920250144498201112201d060052403294031030102d15240050f18030a072400c805521811700014540b500502c16001540c0d000044c00d2502ea540340d08000401f03001416145000811800000000d488110701501824010018000e0781c504100010f05070f5030080c5002c003c5510112400c5c01c070b9190b80044980180700020441ea4070580b40c000b01d0050700c0b1700c1c04503440d541d16150030405d450071302c0b07421f82d90a1801105c050988a5a0710080c2c3d0a440e41d6a285681c0320081d140321410040d00361a540c85101701506c041c00a46441c0419240d4541160b0300c2610102c1d0f00146e6600c4070360780108c032500c40100844046040d414144002846120400d0a0a01081d03070b6000384802a07006803061 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 939393489 1250 939392239 939392261
    0x5010c031404053a0801090b040e0c06031504230f040b010515070b090a020405150105041707030c170105010b03010806160207120c0e10050603150a03080a0804170f071401 75
    0x881c4e8440246040203000440900c02d070310b03041d8a0851400c3d00c03454103000d003100d01e401341d00041c01e4000c860380801601e40e101070520340d8030950310342030070240d91254006e16052042101480403500c800300c4d0700f00a4500001c10117620306240c807040100007840c1182c014196101902c0d200040242010034200502c5542070181a8680c1c550800c0180314001401e0f5800a10030b6400780000d03121140c03413070a180388004d115408910240010701403612100600c0074841c00c808100d81401d9a2920394006180d42c5401000e2000850b146503020050309005007401010300101d001c1c6503601d04036619868400203828007407191245201081340510821101c006046500c40020380a80145400704900c48184034515400b030700384000480d62410b030021041101c101a006a280d940c40d540c4c0c3d080581081107950360b2241e6036903004400700300b41e07501400c540032590702e6075441c40c102414000108010f880001d40303042020012002d5060000041e0307540c0b180c1c081440000403231404620b40c05000601b4007 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 939394739 1250 939393489 939393583
    0x809030702150d0c0201060b0a03020f0403020405190e07030f1410050a06080709140424020a080a201b0f030c0a02100509010c080703030b0d05010c03140405 69
    0x1e41d042600e0b140c030041589288008041140e140d104a040e405ea50040c40382c0700d0740c01d50501880c081117010303800500c003910b13400c40620325094403540024100c84094501403a0001c519103103040c2e01805110390a4440d0030440284040d074559540c000c4004040d280003815190101c21f204e000701c00c1048104a400c00850040c441403800b620204010540380c41140c1840c4524000001d0f001d07024403403003a100d1801790401e126a511602c4420101440a0080e41d800184048508040e5681d1001d0300003a00195241d60700b0b030814058040640b2415000030700f514450602902c1c040c2007880480d00748200585001d040d006640d03400074240001c041d01c4042038000021118500100416034010b9180f08440d8103080e0781900c08201e995000f0070580700d01140c050310140c0c01144a03000a044614480d14003c81d540000c41d010600b0301610060803205a9110001c0145480c0c140c00b9625010711000400d500b20302d0980c5506a4403000c400e0246214000d0000030303c112507841c08011450b00364142 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 939395989 1250 939394739 939394759
    0x39060501060201151d0a02030606160602090f030f150a0209031f0c09120618020622060201023c040303050c0106090645020d0f02090108070809030702 66
    0x40d011380b42c1140003101c82e520f15403020030440348055a08800c085c0308607071010b0036030720383c41a0703030080d803001c0c144d0780e030140c0b050010881100000b03c60303080d002e10803000580c503098030105021646034010702940c8a0340248030130302409103001601001515030400c100c0402d484101c0040000d2041211103501400b80f2918488940306045c0e403c0440c0609510400131008103220403545480c8500500740c020b8400c000c950049102d40d00031001111a49443ca00a2a0240c0c001203c50384031a00300100d40c4180028503040005418200004001c940000c2d842c0c030110188808000701091700c11080701c1d00d04400c079940301c0314140c3c14604940d0b04a040c40c1d601c0c0c1c0c6900f005002508050882e901035070900300c0c0030446601c00e00a0b04101c400d0280c0e101281d034103002072401030180d0004030310340031303500b5000d0440c06d2500407040540340d001c1c41d880145d50740010110710041c2c404900a22030038500401500400e6603100500a074080182c0c42d0902550b164005200c1c2507200d032220180d0303c8480a5 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 939397239 1250 939395989 939395999
    0x4180b151306081e06010b090423040302012405210d05131d0103140c04060b0a090e06091803070f150b12060109151d0105010f39060501 60
    0x60b10200c203039281c001c1180d51a00c1c103c1e036880c0841058001007592504841c004001004480c1c020304118800180082404503490380001f840221251009a0049070281804185170702031040038035100811441042074044004070805000951052500481030007510132400900a003901b4841211082642d2042c081a100201150003202d580c8a01e00f982610002c1d610a1000000c80c1211079201c0304080c913071864030792029140710928120928080d00c105001c26617124070501000d400d80c0f20981382c40b101c0b5088000c080c0c1e821134103c0101003c2090900140382d03544240c00d980150064082400840c50a062038114020b0034801003c003107004846104014211304d0561b0341c040031400c10481d8885000400c0888203101c51603041513048500184001003e540110640355036075001c00c511035685820ba03002480c505a54000c0e00f400000040c006582d1015a17501c500c2c216140400300f070460841410952661000a490350380344011580c3c1c95801003003619005075421110130000c5603510 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 939398489 1250 939397239 939397241
    0xa020403140106030314030c07020a0b031b030c19050706062903041101033308120a0512040609060f060602010c020a053307050901020c04180b1513 65
    0x240400c481c0700480c80001000700805106003011240c040d0740d001c19071010004601d886610190221a811100300728050260b1140441d840040c0708030041a582c0b482c00c90491074196074840302c86452402c0400c1408844c250900c159507095035104440c41c0f1000c01c144007034505208070240288102d0a0010014140400b0101c40040100d0a414040424a031400a034043d22088800030804074000a11003044d5110b039110202034500c4442c1024030745000056100203000515002c0100d0040110910005d0803c0c000405444006140c2c90b05184034400042d00601130480d200d0840e40b00c840000e024000303150000410160004000c0211005144e01e050188c00f190142d8805076003480380c1690824400101d11841a0b0013402900c07100d40300e0b44000c6003180900d421b0340f9001000c5280b10b9030402c1c03129450f41c0290a1070f16880d41c2c808840001a060041064945110360300c0c0c1003840400c002c201540415907588250062460303500c0d40c918982c0c003680b00074070715002890105030406042c09 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 939399739 1250 939398489 939398497
    0xf09020304050c0a0518060f1c11010e10110712050102070b06090c0d02071406091b01050a0c11120d09180207020307120f08120f0a062103030b090a02 66
    0x24403d030b03000710403a50184031640d003e611a964002c91685007240c280906c0c0100e13140c210000520b900710030280e01c07000402141c0068a04802c0210314445030341000180d6010341280340007800c20410010160b0002094040da0000400c180f02d090701150404102c20f00649001c0d01c46d05200740700340280c03818924002e40000008844490490380400c00030304d86240641d2188006580341071419290306c401401075080308104841c130200b04040700c608414280b1800784104401002003206084030310709140410441021141800010050504042e03442080c4007040c5802414001d007c4a001011074100030441c2d0020358540140d860400a4590104000c41194509109000d0345503109942100301e10800900960650000c0c0042007030a05180550b00c0a6015000c501010151a10703180b05540c000701c0c10b40c5c52100b44400f0440c3c422000c02130036030012141030081010500380082c03500340c2440f40c2e4440c3d0b403520720b854400040600c00e40100e0002d8802a00009aa04140800704043e400c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 939400989 1250 939399739 939399743
    0x5070201080a050606030a0b01030209060a030b100f0e0609030c1503010f060801080a0609050325140c090604270b090c060a05180607020301092415031b0f09020304 72
    0x201e0800070401042a80c0107282c065840100320500d507032205418040100f050004441c1807503000d1052901035541d91014020302005500e02042d40209a0104001c0d81044100c0c2c1003031011203458482e2a80c0e11038041c1400c10710a4401d0f80c2e40301c8002c00080d16140c524074116911010103c0e112076a0f51410300554102c0d96503026040d4240d0300d0f0082030341d0b004c60074018407446510000b10000400c03842c0d0420790400c0c0c00384c800e40340380103d05495140e420140e002d40388450381a00409408000c14440d00b0411444841e01500e4611074801c0007138039100019040511440d01c401c00d105660341d100e8440004800c2840402010120314508440324040454002e050b50003403d18007410780c14105d08452580d00b0a590700d614000f00380340140c0c0c6900c0b08200d01504004203110920040e1824490a10100c0c011400c039500061001c03400d4045400b00c0400b00d00e080d00303183d04510071006a48a02040c1c80c0d0240f203103100003a03a4003075423820321916801032005103239841001440c141143c0c001c60080d4 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 939402239 1250 939400989 939400997
    0x9060f060501140919080316020312070834050708060c030c071b0b0d290f01050c0a08031303020f010c0f1805040e030d060e1317040306060605070201 66
    0x141c1e500015a01e071000f1061082e481d09003044218036030314102d1001120750510b003008014070f079102c034489481d68110405040140b0a8080c008041d49010024600000d803000300d050301e0102e86545103a200e0107102074000341e003045060380252460752a031071000c0e8144030300000455500c0728101540e88a079030b442460b4260141c0004543c050384144122441003100d401325a15007929507980816008080c50301020000000e0320100d45000c0c0b48000f800d0048171004045103602c4421070401c2c284406c06880104020181d141410315180c840c1c0b03406000b1801d003455a12002c50f0354806042c036a41420040009000008001c0c071480000c00240956001350300300d03520900104082800c03101841259404101010001c0d1203207881090010020150a11500344a55440780440c0c2503c03200c01070880e9036000031030691501e0341e0701d00c50710000b4411008052510306040030000b9085140000142542c0041480128508107a20031580219403041e010030210382d49100003021500042001c80c001 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 939403489 1250 939402239 939402251
    0x10908121b07030b130f1b03110d05070522180314070201090e0712050c03161d0405070512070804060b010503090c010813060e030c0d02060103051f090609060f 70
    0x240600103407000c182d0b0703441407100400340c460242d1045554400c81040300d1240c80303880070701b0010700d0b10b01c501c0e491003400c14000c4003032505624040304042034102c15140110419410741002c05c0c400118a001c50700c003078a000c101c8176844400905218202c840c021078031814010b1500049a00746010744099010741e441512602c054002c0c1d0000e441050000ba0004000d141d09014404140302142d4014119092112103141055504000e0354000c0750310801c0301070040100504489042640c020a40c59441e040d4901d03030710307912545584035070310b00c0b494041e40cbd495001601d403a02407811030312009407030780d072081e05071503c00380051004204a070111155810400255160b50060741524007440c50740d03000c1c3c80e1144141e0011258800d0007001c000701014440a001d0104249200d07a48030107490101030743d82d03140075400051511594801c541d045604c031000400c04520081501268002c8900070040c0c0d96280c034250f5006415400005401ea030310f4050320b00c0c1080019488000a040180018403c17 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 939404739 1250 939403489 939403537
    0xe0a061a09101b080a0e031c0e060c060f0c0913090c0b0304050303070c0203010f141b25030302040504020a08100803040f0e0c070b040b1b04051e01090812 68
    0x241d103160880703c0501c1002100403600190420028010000c914a0105007802c0a10b000a2507c442e84691260310140c20544418039548030f0680f2401803002d40b9081c1c9019031911080b0381d2101c0040202105013400f0000c1032001c0c08907070444071721910081840301181503000d03c4da001094100c40c04c0b22496003c5100194540c05507043da0310994101015504690350028162176038a032000c070807607040d541c0d21542100c65000d031086103e480307150100702580e45001c220b08803058425680300c50a141090044d01d4141c03c00c118091005607042050901a03811303868107401a0140313800c016445400813401101c100c0d80824a1481a42c104054051065a803440140c403440b0303070b01442240c8082c8500c14450a01d643c0303080c1d50465400541e0a140110f1910361484141003541c0031074458100009020044c03240203044c1c0e1514142490b500d01d410314060000704c0c444019080480418002c1e0f010416581c000e146c03800082c0804015900095111400c490059008085c216850090100c0f0605e0f = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 939405989 1250 939404739 939404747
    0x18090403171f031e14011406030105040507051017010902180f0108011a04150801150207151b0501050a05100608040f0807050a05070e070e10090e0a061a0910 69
    0x280101c12402c21190749400c50f00c45502c0c1c44d003169106584422040050030016081c200b003030f6642d0000000024401100081500c2c04502c0504a140319a05080c1404003080c0c021417400c00b203920442c1c0381020001c1c0c1403800e480f00c02a40b149407404400443c00041c168090350020840c41788a845807100c4143e0f2070041200b90201d0a140750300182c8001e0040c08040f18038030070a464442d41c2603000342820b41d18401d42c90000b5510007a80c002503001401000303545049850502d41c0c46060010b407585c9030906401d2118205100d09120070000700701d810f08100c8040d003d104510360380004c0240b000340b42c45a1600c01402040e00c603040721400714a0000b640d42e1240805500607980305420122080064850308035581203c101075a507400381c0716498001a2040200500810304484512420306c0c140001806440c0c800e04401c1c040c115250000d50f03900ea0010000054882c1c00c038642c0e0070764030762420182c010300702908602c291258884d40960541c400002510b00e80301c044460b00c442c100d0b8410112 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 939407239 1250 939405989 939406021
    0x18090102040e01120b072a0f29060d0206161208090703030e1203090919050604090f03030509030d0c4a1f03091104201809040317 57
    0x341070035044202058000b4482d02d500e48109000383d84400c81044200c1d0350b005600800402150111054246001040f441c04d801c19000307407182030311b4001030b500c51003509881c40f8001c000c507222f0082d01004508650303d5206a40179103080ca2020444296145004103d2083c140140004582c500f4002011035000044d44004d80364541d407140c80000c0b0740000d000446070356502c00c0301c00b40800e0101d0402c42c4c94180649100315112000d52407804440e040741c2d802c80d40040d1101c0e000b03e06050003040410b48451001c0b1409a161800180741d90700c0011150442c0a00310416080c142484050385180da400008500c1801d00034001009207002c0c9005a90541c0c0c02081c8140607410b40031040d0b04503102144154441800500310901071090381c1328120718070403a0001100401d54442440040c48810140c1c2541c640054500b040060205040146aa203452a00b03802e5550001084003041880181c3c064805001802d8040103003407500e8050001107420381c060b6030015a10303001486249442c0c001e0 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 939408489 1250 939407239 939407243
    0x40b01020a060e030405090403050d0510030c0501180b0c0304060e0907020a0807060905031306230d02070203010b04050a0b1212120702011803360e0618090102040e0112 74
    0x200319807800d50307440704050542140680301c1408180b00000e0175895205c5071500c10307442940e0700340c1d0711804a810241110700181ca59400c41d50700c6c5006100082464840009030381c000d00300080c2c0d00c10f200c800d1041d40615500020f21000d030100e001034440c0000800b800540c2c019807201030702201c80718240007510504640702030050b805110060080386001004120080c0107410200c0d900c3c2c415101c0f01c1c0745921124000298415000003008aa6840b80f10007400340e02240d1842013030341c1c1250f103032035079030103084844131000782d000400c401156025400000340d49409001844949442d80084006207540800d0b1130140c40241050b034050500440c0442014000a4005043c070704022194030059000511000c1990b5071122010620b104240440441f070303200e6600e80c01218200a01c10061600e02c2c660010350001d07400c1c1d440b00c1035042c07011403002d407116080d0002c102d40c1c0e8080040c5810000d45480016403240c001884140c9806400820a640e00e24002c0f80f071990340d8001070a0090650400 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 939409739 1250 939408489 939408493
    0x3140d090204150503330403021501030308071106240a0302040629040f0e040204180b010305120405010504050d0602250614010305151b0d05160e0d0f240903020c040b0102 75
    0x150b04100070701b948103941c00170b0183c411200548800d44061441c4102070700107802046020080000690340000d8002c2c91f5202880603010341e080c0034403810004908145070010b40c0140c0200900980c50311f280e01801181c00820a00200703944650b1002c1c0204550445005a64030042024103c2e100400300d4003190a04036480181c0d61415401c0705c1010009042240e000b40c4134400a482d1f00c003140b0074500c00c640150301e803605a51440c41d01d43d107480002c1c212042038420521082215a030007000340d804650095a034080002034030325006000344225000d001c01000302c0518400b110001d0b01000b01048c0c460300040000e11541d0b400028106000d10005040754001b0b0390f054090600007508540040c0c5d480307400401c01040001c011603d81042c01e10b21b6070241e07184100b1400156842c485442c0190f281004002121004080343e111003d220001c0c200869140301c4404110441d0302c0102e2850302141e5085643d004525601d000d04190034042d00184203500402280e4039180c42140022107050700 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 939410989 1250 939409739 939409813
    0x20a1805010c1e0204020f0307020d0e100f180f0f060f0207030c050402090f10022d0a02010503041a130b0901060b19020f030c010902100206010303140d090204150503 73
    0xd050411410441c3c0c0c1282c100da000d120700e035000c0c030001e00514041c001d00e4002e0107175048c964000030800303102d1a030701e02c3c8901461146903030b2090300210f030b00d07034820300615000f00118061841c0c82d40804065204900200d00c80700d0001e602002c002d88141a945d6654406803003250300d141c1265a620540005409000441d508104501e4030360300134580301002400142280e181c07080000c00300340040040c84c0143c2c102400d090086c03100f010b5015100090a01d00b06940c0100010a541d82c1c2c00d00030000741031001c0000814144500c031040201040c1e14000540303420b00d81070410b1041c8440d41101181c140e1481000300e13013080c03810b018078000c0c1da1490a500f41000c0c91480d404400411034013215080d8051052210b507440e07024402040400605400803500c4030703e0703106007c0c0c403407c4080c0b41411500070400600003c2da00c6585000c0500b418652a0703216441050480001e14403c44020351151501ca5008942c3d03a140d22424101d6008a06450f56000d81d00742c030350020f40310340003c808030208c030310 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 939412239 1250 939410989 939411023
    0x6050a1a0406051c0c081909080702010807051909050a0806091c0302040819021504060f0c060b032a0d11120304030f0b010f06112d01020a1805010c 65
    0x50050156482d2041c418074413512050140c0c4200c500c0e00381c00400190208080204a0300840c55002d2800c0c8141410016284983c58805850080e618024108109100401c6185100d0000d40f0944801c801e00310040702034908014140a0092050714000c1541c0000040d207440041022885509071001518004216181c540d4a0380c2010418005156091101294500b010403d102650008850315501c4200500400686031518000b0701c004003810070040c00705030340c40050101e102209040031400c195076440c2c510003810000740507941501c034001d05646110081da003165103c807410b0041003040d480390400d02c000c41da031003180a48842111000740c15a0309002a40f400074402580550b41020345a545140c1006480802541c02c1e00f40344c00180440785400000030001c0806061502680c07000384c0380c40e40c880c500051185980a40380451240c014910350b82c80702c2c2c14908a00855442140707683c00307000a00310801d800003c00c0c400c00b012849500882c2c2180b003e5404c040d00e061403410394 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 939413489 1250 939412239 939412247
    0x7021501030f02010e040f020c031c0203060a1206061203031b110a020603100806041b12030e09060d021207090605060403030212130801060609030213090b0a0207050f03030103050106050a1a0406 85
    0xc0c005c4181c0266030f9400c081034103032452018240000c14070019596640513600102006141d8003120200c82d0302c10418400c059890f4000902114000407145104c005207090003002407040c1d134000404881c220010a01b01585540702c59100791403402034080740c00c2c0b4140121484584040795900caa88000758000c05441c08502840e4003a4140101c1076060341ca5036a0141889820785080314609050685102e80d81701d050542c0000d000c203a460382c00450f942c3d1320014100040ca2540324040c01c0c0a01c04a045500c44965482c2e2490700a0b114414444001c40420f03a500c1c0d080c072400361110319100010400d450301d5000c4a08032500b590040420402c0340020700b0999000c0b5034040c001110360500011703001828020301700288055260b200c0710074550f0050040b802d840300780c0312000c40d24140f0b081000802d404030440c0c01680309040162684801c0c41c245e450142c03460501c05107807202100000c10070a0541002040d14416108a03040c02e55607180503403030f1041c005605240344c6090009000b003a1123 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 939414739 1250 939413489 939413507
    0x60604060c1b03034a01020a1a06040b04060518060a0f0b0d0e19030e03070306060e0603010e030c030403062019020f0c0307030210111507021501030f0201 68
    0x40d15280c1c120440c00010800d00c9500350384104e0228001302003529075101044004003048035003003440e01c2c6001345241e80407081c2c02480b1004065980108500d041070b4420810381221742d43c44002100203030b000b0150100440000c9940c0c40c4184c3c18800d210316542014007a1304216038026118190300d8180403450181d0200040905400201c1100001204800c035a07502d002020800c010503900d4920810203425a51082080052544603001d124501034032805031017840c64161801104070089880024149003166102411241c14580301050f00e40b00401d105010702411802040350345a40c0904a449001c5c8518500c580e0f00203100400200340030b034000c1860404400910103045200d1640d8a0307964000300742995480003582d5000405c10f80410148440c04d0002c2c008090304045580026510707012400020701400c0d800e0000c105d401d029005544040c00b00d10284e441c01e441d020743d0b8200b040c9044401c4030061080d5000c02c1c0c00f081c0402d0145050340d81094038040314008980041d103c3c3d1503 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 939415989 1250 939414739 939414743
    0x102030702090f18030412030315030f032115150e01120c020a0213020c0706050f0a030e01090f05030a090e060a0303030509120307021e010e0d110a06020307170f060604060c 76
    0x118224191031301000500c01040541b0a0700890010110309041c010101c84400309642c00f441c80e080414800f05107290b281c89541c42c6c0c140762001250740c0e404661010f40c2c1c8501d1030100700c81e04000f072035840340a034000e15030251b030103141001e600046103c404540d09a19220003d0100310030b4001c1410440b1203400040c1c1c46145801103410a4a06d0340c013007043c9141c030400d2170311500d03804650f075040303140107204003401001245030141c24048507074480c0309544502c10005050554401c50f841c5816000e40001002c01d401072a0745c085000981040b07501c075407103251a480020b510000214505200311201401940041e00c07000a003825a81d098004060251902c4880d101d0710510342103842c0400d0003103121f61401e6018108001840e03080c90a850221004100d00b64100084620380e03c1001484007c610958a0b120342040c8000b0310450400d035a9400c050a85800001003090030350300150317281e100091422041d100c1c3d0f52210389803aa414420707915113034410f20402017000113520590022407424 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 939417239 1250 939415989 939416011
    0xd09060f0c051e1005061e0a030f030503161d0d061503060c031109093c071b15020a0e030303090705030129150f1201140102030702090f 60
    0x38a465462515a0003443d45003243c0c110075641c0b50410f010700003410444110501030155081c507100003031140240900506aa0300009025030141d5101d4170444002d503005469808089a2818000c2059104843c6031030b00c20b000c64003408156105100210b03841200014040b11816240c040110141c1c00302d40680d06d054841c103242d50a0b032400c40200c1c00544c0300b4880083c50001e9018042c5c251140074002890300001400b008a064035031501d01580204105901207001200c4800303503c42800302004645840000640a0b00034203550399068000c034007d89030f44283d00c2c103404074096012003142c0014100c4c000d0305241c005000c2c440d0080d01080e0004d0400c0d00800741110b0120b461500308031265500d941c0603400c20080e504082c40b406218100d1586407100d18100c0c009140c080030001540c19010342031491a013105800300c1c84c04d542c003904c00030b140b442d914200030343c281120b900e00f03010700c0404400220481850758000400c489895038058038106250b55405c2c1c24a0040c800102406551 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 939418489 1250 939417239 939417257
    0x25030f0303022203031d061b240901110301060c030e130c090509341b050a0308070201060f09020c0c180a0b0603040b150d020a06020d110d09060f 64
    0x110301068851010805500343c1a1050b01d103041c020800d003400c041050b02a114815400c03240d8032400103c804045003012451540103542d449180b03071032081010040110a000c00034000075250f80d1246015914150091082e040503494510003444284a200040344200c10500c0019000d0443c1004202008051600c9590084d05200030b50b910014214001605044244021300d44125081d41100c0d0111a50740b12200d1016145103008050551011080c40342e4030f0b81c40200d00c01c01600d04400700f0724460792102345452905a99030a0100800c40c080f80c90784001600c0c4a105105003001c90340c1c9001c4280d0f1446c5002030761402507000c003028000c6801b03404045041515040060b0009448003c0b000c1c01e10710740340001c503013280c5030003050700c0c42100d003002403001065050555581001e500102100410100c10004100c0c0303d96000c000e4001d40d684500040c1c191b000305190350402c0c034644804d010a5a05e210300c03600c45e0584043c500110f4121442031010900c02d4502c442c07040240d0820344c2c1e02c = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 939419739 1250 939418489 939418507
    0x90b12040c050a1805100602030912010b1305220b2a030c040614040b0a0305250f1b0b040314130909030909050f011a160609020325030f030302 63
    0x407102074001e000044140d0400c013a4005841c8106580110740341c20601d4400e061030340c0203403a84030303c0f0f840d64410782c4006040b030302e410000c2d4440b00da0414020300b0448982d1851171043c000d050116030b19640b80501042c1c2100c18030b0341011041c42c5503070014203e032041c0c0d0350120440030241441e40341410307140c10700200c110020b0400011402582c8605c41d1546840c50a04000c010040101100e41d40010902007000025a02c02c29102e03501c803241800300305030707a6044181c074905444050342d071480324101200c4020030740c00c44a07065901405030f1b1446c118081c000c88951300c080003028024070071707080e00f00000c2c08640b0401d002c00314000601907c520f405803d0030312000d11080c0d6000520307101d64034000c5104040e049a000d00003400440c1c014007003440d224841e4032200d6814816200446403d61146001d290a1000c5405908607221840d1582050b81400001440b640108038000d02c04ca40a000c0d40c4140580d02d01b0005541862045895045940c0c0320800160b07410100c0903da001c1c050100c03 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 939420989 1250 939419739 939419749
    0x30507080a0e10150312050c10050a09050109060e0c0a08191b140a050d0506071d0d06060e010b0705030f070317010803090103051807030f0c080a0819090b12040c05 72
    0x40b601303a48481c411508500b4030503410081d0034071a000348a02003081003c1c4a60210f442403000804c0c100c0061540d807400e040c000507200e2440c00070910f51900e03d070f280c108800d9611240c408802201201c0f40307001c0000600140700391038068029903500c080c440c442c25a001c5450000d903103104501050380700e03030300405004643d48150801e4900c0c0f404107844515a01f07211403904001d00c2c0445d82d21514603d640c035507980f1480041c01c00c40420240100030981000d00440301046100b002e00780c403040343c40d14200040101401c2c0240d10056401400004440101400ba2400d0b80d800c5005140341c5601d0b551443d101c1d510404044050144501c00c81550526900b0321a0086c012070001d10341c0c507030001000400720361000307051000741440d0051080001c82c000992500703495125046d041e40c241a82410300028409a2103008140f0404401e40200b10b2000c01400880811074440381505541c0070044c0d8441e00507010304081c0140c10311110f41c1d541500003c02e0b42041c000c4007184076141d02c0302d020070 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 939422239 1250 939420989 939421001
    0x1a240405061201061b031d030a0c0f05030105090102040501021c030e0303250c03020c0f060c1c020f060f07030b1306080c01090e1e04051f1b030507080a0e10 69
    0x492101002401001181d03008821750110401d801e0103881c03c1c68607a0307009002c0300b114020041c0f41130208007203038503d901d040014070380382604020480351460b51002c40b80f24801c1240071b405d00039401c1c800130856511050007540c0c146c65050f00500008600c2c41105071504003c03415502c100760b03e50b0380f81004c0c80403d000030340c0034207424030203210350590080d10007021800010b4540d04006100018002003940850025003c450880b90300100c12030311000100c03503025521034420513020300c80008140c100612100c0280c40d040d502552000b62000710002d80701d401c11140c88554155500c0095906807081d8018004c1150051240c4405440c405590342210401d803c940290703488801100c5040da0807540900c000c0080140d85c107002d1500c42c160100390300c02c901c00c840c0710040b5507010404101003880280310441103480b0b10b0075405903241031100544400f451001c2c0e200400180c0800c4603200f4050704d0b21555458503109280c0c0c4a40c1080700092000342c000840601540d42800d1165000d03000704 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 939423489 1250 939422239 939422257
    0x915120f070c12030b01030605090402130e01020f03100f0f06080703092307090605041505130902030607180f05011e051c0b030c0906090c0c0c0a0603020c011a24040506 74
    0x9605ca00310000502152013507041035201c2d0b08004104401681e1300300c80960048452080030900c090300a0155029004a0300d899a12400110401003114034055006044800074012080f080c0d9484d400081c60f00c20301d006d0740002610315800a0f1300e0074082d41140e07040d01c0c07180c0f0100388140150440c0380495103003003503a02081d80181008222041003402800064041210104080140b50000c864800018032443e80141201005d0700c00300446940b02c0d408040c1c014060310101e1910042c010003105a030111490f00c000380e041d0204a420803410080305603141030310740c0311010440f404034110140300e4550040070084104a40e41825000d4031000018041d5010041401c0d95110b04040c102007240b00801d010f103151a041010681d9101000b5400c240041c4080d595000100740440c00e04401043e075039000a910f031000900d0680c180e004005140309680204246681c95448030501404841c2455000703000c00c910a0310718007084582c2c000c900c102140245023641e504045450f6401c0700d03e907 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 939424739 1250 939423489 939423491
    0x30d0f0e010b0604050a0909170a08012d17120a021e061003140309041e1a03030a0f031503050106231e041d030915120f070c1203 57
    0x103000d08800d0080626450040b00d8007401c041c1000c001c9004060684550b20079140c42d15604000e00512100a4402400d0480416960b8141721400703006680e081c030802e100c80f43c00303018030341f80715801042901206c1a94032001c60034514203412241d050804040248403400389c42c8450842d41070301401845c040b401900641807004040c01d2080207c107044070b507410550050020000741041086040e02900d070b008001500b4100c15031003152450180142c0d203a003103490001c01e003a041101001c8156450300140d003e010f00c06410600c49c5503501d0142c14141c0650040c000361184034040c0040c0284400c0034500040c951110b16030884070064580d000390b60300e035500e01003440012203000014012a01100512501084202c0420b1101d90f4103020001c090f000c6400526165450743c10800e0706981403111401c9801054081540382ea0184004900ca100507800d22030554001000744c034000ca40c00020316205698048040c10316220041c065420031400801000c00110400b1203d802a09940d41c = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 939425989 1250 939424739 939424751
    0x32503061401080108030406111c2a051f0f06030f03020d0216030f0312020d0b040c0e092d07021005010f15030906021e0304021302030c070b04020102030d0f 69
    0x1045a45100311003070398504100c4980010b1103d60b07000002c03075048400501d40f1450b481c007c0041c460030881c80d0303040000f009800c141002c101c0c55022680c038581c0181c074101c03542040501030300e01c80302014012000b89250441d15100111006940c0c40e024907c02116001c904200146041c008440150300111070380d021004000c02070603410031201702c5d0340c1d603107000074855402e40400c00128051680f0000700001c42e41901d000030184100f0047c1a50441440d0942d100c85c508030342da078098000911103c1c0120305c3c00c8440002e051140c81000b010090140074200750385c560040c81258044004400741c810300034480340c921611407510f100362051025078007419032503402400c07807820780c0d00c1a0f02c5000d100f0903500c014440f540ca0501980c01004150600190002180c900711000c0e0044609014a507030345951030603044200700000f5489503108880030501894040d950104900095482c07810b40d4801740050f40001c0d8190380203582140c0140106d90400315020000f0040c1c3c4c48600d80302c20f415803510 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 939427239 1250 939425989 939425999
    0x41403040e09062208031003380c04050d0807080301060c0b06030c0609130605091003030905030102041413020903030307050d050f01030b0a110d0f051e100b03250306 73
    0x70100325001001c0d20400c80340c100c05030340c039401d4040c0030040203890050004080390040944202010080d50702c110443d420002c42d2700241c02560114003a04031020001c0d0b940380385402e4458441d44909100c0c454107003480c2c200030034070100c150011000c64404104010034004104010b02070750007848a0381c1c400107a18210315194264441c0506124001c1d80100a000c3c5613640c1c0a05595803007400381d81c0054411180100100509526480b290b0460074901c02d00003006041116501607038020303110b40074801c1e65001414200d206038410070440318945d074500c1740603280100b1504082030030200c025003803c5180c800030741103920a03107240000c01d0000035410401e0503903009840d8070051412003142250702d15220b02c01c141400505042049a0702c0d000070341c05000032819110303c8010b40c0410441c1500d018100c0c0c0040c0f41c180c61400e40200c54a000203210000480a42d00c90400c00c80c80d00d200c2442c0c1100d07804c40b0342010b042115400c141d82c004405040d0b83c0040d1901c950025900824103038504 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 939428489 1250 939427239 939427243
    0x260c030a0f0c08030c0a03030911090906060315010b0d0b0a0b040902030402040608030705060403051308060c040f12210909020d1a0d1a040c08100203070207060c030f08041403040e09 80
    0x7540182d0507a041480303448012580400d40c0e03c1500c0c0c16040100d40b52609140840084080740001948910f840cbc060000340080025690b00c1482c06030200c4018000c00b09106004500911030402c1406003040b02c99025801c03500842c41d51a00504105d613055100c0207000840c0c0c110b038001e0090340d603000c001c20082d46030034001c5000401d44030010b94544406c3d0b03240c043e00c80b880104051b06100002a103582048054a140c400810380b0409507409428025000000369006201d03440c080b0704400c0010600c02407112250303105540c00144a401c43c00c040e140707030b0008900041541c050080d490000508041c90340020302400114490000d44400588091210a01a2403442e401070040b102d00d00c002880c0b6415842d0070b40c0e000414804961b03101d1030140600e800380d070402e1500e1301070481030940c40e80e800c0e009140508041d40a455038292109000c5904031050180640041d01019210003054018001ca0750481e014084101e0541d0a209040d89140d10a5126980e50801c40081003118482 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 939429739 1250 939428489 939428513
    0xc051e011d01051e0903030f1f061107050906131a09011202030d021906051003061409061506041509090c090306151202101b030306060e0307260c030a0f 67
    0x14821300034160030100c44c0a40da070301000b0306c02d0f50200800b4002c14615007043d50300c111800401c0c55103882554542c82d0090032709410860b00c403411b01ca8080c01040d00d00d80412113520440c2c0103428800d120360100c54803005019205d60241c180500c0c0b407070390000342c1c944581d007502a142d4100540c00d41749042c4185403a11282d10521030454000508071850803260340d015000c403070342080012a81d40c940100701c80c1c0780d41059000030411403504907000442c2481c240204e109500e00401c1e01e0b05943c03803008140344103e0384000540d01440c100424081030312071441080c1c0c1c60107a4030742000700ca03031504114070441e031080038140b000c96948c40b010070030014a03020ba403407102400000c804809207000104204241000c42c02440f5190011504149610801d980c8017402c0700940000c54500711410090001c01d25400b6a600080c5170942400640c100021038104a400030a003001e41820945218035006100c0d103114203132400745210381903141e5010000201128010000201d80010340e03c4d002c9040a4 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 939430989 1250 939429739 939429781
    0x5100501020f0c101d0d0f0b1303020a080a1e0305011404060503030405100215100302010f0e011d28171209010509041410150c051e011d0105 62
    0x4807040d00c0c0e60641d00d80444c8000300207400d0070300d11090400301c100c034004910980c0c00150000180000681807158040b000d5000c0707400303520798902d940c42e042000e810f1a07219000203000360780440420b01c0001e2000c401040a080107160407080074030301780340b00031040745600b0010000a03240e40062000710020503c000610304102d404000d03252601c40480c4d00d81c02907100310b0b4443c080c8685400c1d41c45000f4442555010380d14402d032005490f101c20001c15144890109900041c1144650f07100c05006a0025001150503121050724600c40100030b4079503007a403c0c9164000c0c0052898802000c109181030f100050880304d255440c50814088003030b40040000b141e2100d42c840c3e10754025a41203442114100d072803c2c41c101ea6100c46007400f041c0505000f1165400740c0788030500700443c85280300d2918080d2031805010740200594200221070400724140f000d002600030045010000075502c000c0250b040d101f00000c60340c115541700307140450441c20f880c104a41d448204000d100c1cac007100d1050401c01 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 939432239 1250 939430989 939430993
    0x3d290c0c030613020906060f04080d090303030f0507120506010e040f05040605091603082a21340501050906070f0f050a0f0c0b150a0b0403030e0603130605100501020f 73
    0x30b0f445800145c076200340500451301403440060b408940d0402581100d001d0500c0408954444014210080035004c080c84142c000030328240c2c0d0f00320202914050a4050020f60340e80c14404001003152100606003d04868103100030140421020388890240c50141220280c0025907450213003400019500700801e070314841e8100c2500c1000c040b0008075800705a03900600501e41750107110922032004003800c00091809241d211194085013030004000c2032480c100c3e00f808a0017141030b195a1b8540c00707003688400c560303220310701c0c145c2c090352001071002081c0e6280c0a40c2e4008002d9038a80508650003aa041b6406030000c0041240c0300d0b41092030503845800b645001078000503140001400d0340604008202045401140e040080c2c0c401c1035018180f6810600c090200d0508200c40390503000c1c020303030b81800380c01c584000280829103d01500c045a815440d401d0321072040e4000c01440e80e00041503205c04021810826021810390f100d0341d44540004017012144d503040c2400a0702e80f060030240358441e5 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 939433489 1250 939432239 939432271
    0x110409050f040b130f0b180f070b19020106030213060e0f0c0304121106090c030d030908030606030705040f030803060906030118293d290c0c0306 64
    0x780350180e900c4c1d405001c10308181099a06403400b400b518480c4103025110140309403d018022507a01c4080c040c081d680000c40301c0c02c07101e00240d01d0303d401c0b1911600014000a2003aa040c41c10083d103e003207440103500c000a13040d5143d40c00991001c07071440301c4017502e9640d40d0f01030000710507524001e90000403036510320b202131401e25800010b230300c401803009054084440d0400c50a81c05400030f9004486010305455607483c0810b221503440042a118920900c1802110042ca900074401d00b0b0030160400f800740c0c550b54505043c0403ca03071010303003901c040201c10000001c1c2c142c1c1e4000b2003005107104100403592414020300b0061f101802501d0180701ea49800c1c03003d210405104440c0e0001d0307602101d004032f640c2032101000008011800d041100d0812242044500284030b4203036080103c02607240003071014486124484444103c46108041620140501c0f1a11203011507515400046000c040c00100014405001c2d81214025001c3c9511010188109140900201c2d52041c056200c83c444 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 939434739 1250 939433489 939433493
    0x70209012112090302101701060912260c06040b010603050c121902040806061f140c030f040b2107020d030e0309121f0204050607031d04110409050f04 66
    0x46031541e0800107092400c0d40ea00c0c1001070b80580c0c00003000355002400040e51180300d040144c00c4581c484001000802103100218080340106456410354140428000800410366107040880d007074071b40302c1e40b104000c0e00321400f08400380400812001000001030a15400c00b880c0c00350712150181c201c07000b4181080f0400140710104004da40c80030710241c4008c12a03407240340e59210082c070075044212200c0c0c000900070401c60b0300011194020101500c009125210440c00303040302c058210510390014034150001c0b1081000580a000807a24001c150784c0b60402c00e03041d03e50180d00541c401401d0700d8011038100801c1181cad00325521580f11200030035000740f5240328025142d110301250710b80be040c1d82e0240c6440d10b1004109a45003071002410f691515582da4142c60740c4c84070711602201d90700c3d03451200040241a20300a8800711040074040c07504180b00c581e002d540720824500c11400280a845004050381d1365402135000000c0d1b8a02401d60761401c00d6802d07011760318020050300d0130105202c14440 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 939435989 1250 939434739 939434789
    0xf0e0604030c060b061e0904090c0906080708120a1103160c05010f031505040903090305070806040b0718050d0501020d05070810050f151c0f1406030105070804200901080307020901 79
    0xc81c0406c0035405a40e001180f000170020840320002803c03400d076010300401c524a46601c001c042d584882c0895117881e654641a03a42d6290300d528800780e0502c1071045802c61406001401d02001034201942d0800c81d40307592000304490b5101d8187c07101d11001c0310400595801100e030040d0214140340900140d100510010401c2082e80b090500075035856003800249403043c00715a01565225081d0381d40300e680c5105041e519174058405840030b40c0540c011680190048040321001c100c910241d101b40b91418042000444851764159115502000b0300e100980480c4a61031140c00b03107031202d2100d4102007141903480d61894011502560b110b080d1074010b503554411903560004130314452541e594900d087c1d46101c2c450042010794217414683c0d405040940d50300103141014032072101d6642681c50000705401da07207041e911000490f4050005c580483e110f40d00e91517801030400b090703000d0181031001089103e407003640321101541010400780210b241980b0f0040c0144241c04a8a1808259001c050 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 939437239 1250 939435989 939436027
    0x4020109170616030e2b08013005010504031808070b042d0603020414091905092d010c020d1b0510090609150c0e01030f0e0604030c060b06 61
    0x2002d50f640600d90b50030b2500c69000b21410f80459400d8850004602810f421103c05c6d05500342e42d46c0000c42a0400840d101d072600754101c6100e91a83c061400f075064180340c142c48441001020003030100f4042022031000d0103817502441c0f099640e036050510320302a40784036080c6504404001c1e0803c510402942c0540740c2a2803d0f00c105074900d1900c0d4444482c40020300c0110441a4036040b41440300040c03894050f8060800c840e05070300007000d0700c03158031700700800341008560240c9600380580300e43c1a5960305a1150380e00c800c1c0c20b022140383d210305807040d16106000c1c2c102500c06004100d00d01e007800c1c00038003030314010000030f0008000f40c555054010340b40800120354080414074080c09441401000c1100c03241c41407503118100705440050030180040c0c10000003d0303c40042c0006100c031200400c3c4102a4000450f56890050072107200044010b48064902613400130b803181202d5242400500c331040c001c9101c0c1c0c540c90180c0340c02e0324001c41607684001c40c50744540b82c00d0112000d4180d56100712 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 939438489 1250 939437239 939437251
    0x6030304030b060a050901060207150e1e01120e0c0415060903020d0f081c0b0d030e190e0a0b01120504020310020a1701061d0d02130b0a0e0c03040201091706 69
    0x610126503c1d94007103120100c96500050344103c068000040313051f00425601c0544071a1703061a0603a00030100250b45000c0c11220081e04034405031040150003e21000f0074016120515100c00302c01c001b036a17518291454072209909980040c1107a004c00d19092080050b10144c3c1114a05080c2c035140014101108610010b802185115142400c000a426140c40000e6000103041d445070891401d180740400790000c2078222a281c0a02c000300351401c84000680280d00d81c0d00d4000001d92502440380720520592102950140908046580020500864410b000d00c41d40000c40800f884d00041c450304601c042c9640791850b29040c8030241c0c4011600a0b104141c4000151342e40c1c1410318100c8030701c1d42142215038a03017900300c0080303203450b030052015041d41074000310705540303980f564100700d41d651031502c00035440070b0034101c01c0080050790740014540b034034028401d00c1c42580e1400c080000e40c208a038001115040001008215030b04000001c01400000da01c0140f20b010f944110769a8110241c01 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 939439739 1250 939438489 939438503
    0x60a0609080d030e19050a0308060102030c06010513020702030f0a02180c03040f0c1d0708090d0221071203062108070b1f060207030c06030207050a080a031103010b0c150603030403 79
    0x194925001003081790240103240c0e145500352a1641040b90b19510249811000107040f1408144103610000070b071404070781a8000ba2115074600000c106810041002c1c400f807041e020310a401c0503941c14803c0100c445040b0b40580070325141403041000900c00302c003c15125080303503014031130240669001c2d25405035000b50f03000f030416800c2c00c1004000d00703503034480304075510f2401a03050010980d1000070b0041d582a02c8000c5140c40f4420a50384906241074084010380c00074118072050301c444140380c14155510300c48a03141201588582a22007a000444404241c03549410001000800a01010942c1c0420308420616440c1d46100462080fa14041c244030f038403401003283c82c0316030181200c5c86104480410704190340d07004060746920a0b84019140582105d03000690503000b402101d522581c0040940f0702d110040d946d96044d508071240440c105543c0303c0191408071600001140070f00300f14490203450f80755102c421468148040741250083c0079290070312040340c030000280d4050300d0f44116 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 939440989 1250 939439739 939439751
    0x20a141608041503050906061c020d14030414090115030504060f0c030e0c2e0509090c040e1b03010b090102011112061c0b22020d0b060a0609080d03 65
    0x101035011048288003624003940054005450000c0704450031020700c035903c0c244034aa6a094030281c03940400c44541c0d4000d00038445855840c00954a0604040e1004280d14a070300c0e060317103800200550b5140c02d1099648002010b002c200900440c1d00c0905108070391105640d0b0500c54003250202a01070030b541890744a90120b010090507401890b103a403c409800c1200f04265100140900101c00658055003c0d00c24808a181000024950101c03a0106c06c0410a45130a4852005413031101e5404d0810409002c1c01095640c2e1440590150390f03c09440c544450030260920488880503180758440c1091000c5000441464000d484c11560001002c0f6100c000032030060780500145100071056503c0000c0c4002845814120113019103800c1d250b5800e581c2c034048010064401c2d508010708101070070400030b230100302c49a0001c440041c02e0ba100744100300c9a41d021407040b45010600700c80348401441004a6070400c03482d694002d2a403807030420708441c40c00030029140c2e21020540e1041648031f103 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 939442239 1250 939440989 939441007
    0x1e0d05030c120a0203060a05030f07060809070e0f0f0f0622020408161505030702030304110117070c032c040209010509061b0d032c0705030f07090b04020a14 69
    0x1905491000319104541e40c00783c0741a2000b8802540200c420074401d000407900812281400100100707003005440003010030302d0408405072503070000240701500c5032280c0d0001080c2200f01d0054070b07004007a0180110224203000c1162499103038000c2050086000c0e1908116003940d980380f00e2104c00506401403840b182040440700068410b1750407440c003500c9604421011050f4103604c0c42d04490607484101c1102440b030100711242d00c0309840c1c240c0181c0c000d2020902003004c010341c805066005040a0001d25013207000001c0001c000c60303040012624881400c01810f4200314203c0d1201050904d41c84d52144003c1a0210076051001850240341d001c2007030881031b409201203c800ca0002064a901d900600080421400b5000010380d194000c82110f103101600a028005034803140c00641c90561640c0010403240208900c0010298828444001810341381800a00c004800402c00307030903c982490805000d5450300411103005e544100701811141ea40004000700903841c20002c556031368801 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 939443489 1250 939442239 939442261
    0x60f0e1c032c01060506040b07060509030d0c0203032e1715010f091401030201080a050702011e1409071508070c0c0605030603010c030b0f0d080706020a0e031e0d0503 73
    0x210035111861a41542444440700042c04050300d1416100000c3c02042e4461050000318091445440d1040703106206000000350207800c00c903482401c146c100c0b4208041c02c250081540d00c24111140583c10000074400907040541c2c0c01c44405a2a46000c81c070711500320103982040c0303041e01c64800c040018004041a086050003840f8009040d09603c541950b1100c0c44401642001e1003221a054a440c0c149004090f1031900c8504032601611140707110b5a52200e604043e10000300408110f543e5040c1e00c141103105e544801d103140c00c000d00000b500000f03405041c040c2000c0070303103241c0040c3e10410742041141c6203440482c502c402c0f9803901114544131904261540700043d4801000f050b4441c00101d030055101e4080e61141000303d000744101c000d9460240c00322100c030704000740c111101204000c49030801e01c00c50482c02c0c0c41a10100d1034645207840c0c0d030049070030046c0014001001d82c402440c030303071404100c0841d21040700340c103840e1185c9840c0142c40d03640c40c50b051828140000800010801410f13 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 939444739 1250 939443489 939443501
    0x13122a020121150803030f0906010501021018021504090c030e06130f050303091018020a03020f011b050105041406090c0f0a03060c020c0907050c03030a15050d0f060f0e1c03 76
    0x21540c802c1d00660707160703442d00c3c5e1250000c0324405845521f1400003003d42100140d05812144103801401a214615114401030074050704c4409004040391041e40045e01c0e404480403488a142c5040350710f590410001d1001e550340308a034101007606009000d40030b06004500aa04920742e41c803095058a0f44d031426044032021040b01901500010003040304c940c40103ea40103031815030f0001001162204d1300d042110490b0340202a400c000c0c041000c0c001410549540c003814401410621b24030b1711000929030042d10b0000c001c030703800d945400c28042002400c039003805a2400010143c421840e04600c040c0ea54641105401d101c0d261000560086890f840000005950005000d0114981c4000040c0d83c3e01c00100c0c2e070600441251001943c414420026140700b40707007050140d40b07103482d8115840050300f40c020303404401121080c0700203225511170540d9441179100c1d5402c41140400740c1046400c07584500b00310000c1e1030800c00003080e54500850200961090b445030b4503074500c4c00807421001048 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 939445989 1250 939444739 939444761
    0x30a020d05030d05070c03050a0305090f0d02070311030604150209130c0503150a0f06110708070807181103061e1e032a0913122a020121 60
    0x8200c454824010003000a00c00c9010864003800b00da16011130403541600448006000500c1c14000164440d00c41c0e007102d03070170064031411184140c20780c066480c100f49003054204090780c80700504000300030114000c0790b0310301e000724050000c41c60304d502c402401850142c07800c00003641c005440241d5070343d6140320001c0381c98240d2007085054120341c1f0140c201c0d801a80c86200d010003840b82c45141d8070300190350300d0584082c90450706c80980382460039a030440c00108207441501804102190b003190800140c001032010000400385189802d511100c41d02103204080f03500e0b410440f1000c40c010700101242e41000007941d803590900a040c0c04404040d070340c144040c1c0e1116559000c05440c8001040ca0b044040c011000c0e2031021034038140814411410641a82003044414041151480c0403485150300648549000d440066140c0e50260701172040802440402c0000107018502006110f041586a542d0f080800460516400203006c13074080d00350003020072068844840c0051620342007400c40348 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 939447239 1250 939445989 939445999
    0xb031b0a022401080f06070e01050d0b031c090b0307020a030f182405120109111b0303010f1202180606090a0801020a1b1a061809010914030a0503060f030a02 69
    0x6244155502140310a10480d0030900c80d50340c3c000301c1c040d404511b07a0b001e0030158a5a0580c400b819005444075008001c088803042d0b82e444c444d0403940c0742070102190309030940c41825140d0403000350207071a08034280c0105200c104103004102d0365940005441d2241500341c1010301c0a00340d5035404964000c90081e1000003003604a8000954020100c0c4490380002c0125a2400e10302c07020350200c9242c019100f14154600f12000100902d006951042c0e03030703456415038891314020960031400c1c071000c810440c842c055440080104100750303070030000c50050000042c1c2da028002e041d80020300a40d01e6608074007000c01c00301c00801c019a0f1880119401c0b0840500141201640c4034640c500035007004024001280c0081054032088241c050900c5101d80e0101c00ca16134245c16080074031078140d000f0700c600d40000603101c10502c04401c0296007841414072200105182c00b9038607024407100c584040032002039205000d819400740e0002e080d0b81d0311480540e1002c010040d0900004d28000400f0340c007035040 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 939448489 1250 939447239 939447283
    0x207080c060d0e031b010b030a02061204051c0f0914060a12021e0405040b1f1407020a12031101052215021c05130210031505030601060c0c0b031b0a02 66
    0xd5001d105c00444c010398040f0080007400c0728203040c15241d031808100254030403410803810380400c001403406600640148100d0b02001d10310707050b881507004c01a0107040400c0303800041c10002540112000041c1c05504482294807070f240020039a1030044aa1000500011940d16981103441c1d40c140c0f040c0e20050b05c051000c1c5403410042625560007402407500a90a00584048078140485d821411040040c04420b20414200741150342c01c1c0090042078103100200300c40344c0945d075a0803c134009440340c409403880c0801c0d1494045d01c15a100b5020a540c0e9040504200c0d21b00b2503200406ca40c010707201120840b034070951802c2000c124240310303405109840402d80f45070081c1c030325a00103096030040e0700400030381d00c414a01200d0302d10450b4000b1760140754840d0041816100390004846240600c041c2c0799520340303410005e03003401426000100017a41a040c1001440400d51031100100204480c892a40c20040c24028420f074250703034295018000020725142c1c0c01e100700102051244501070310101 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 939449739 1250 939448489 939448507
    0x2402010221090f07120b090a03140304060f090b1501020a0302070512192a05030a1124190912020d02030f011b0f030b010e1315170105070207080c060d0e03 68
    0x5070088410051b59a0b00004d000120141000110b1031402c60b056120744c1800ca0f13101c00c2503200c4d5400144102c0301a9110052039451903254080c61210912032060401c039458200c1c8402016070034409681d04540c4110140408650086015015684140d030351030786000d010b00c1054034009489a0716080b05010807081800d024420581c800c0310b80d4007013400170090308203890000580d42c1600645a0542015a0900024224030b6404034003080150216110700003022100442844003011542096030000c1d1121280c184455609107c0c0054105204400c0c2400b09844800038682030081c010741030441c1d04025560200080c15003200d01c1d40c02845404440e8502c001da050150320b5500118031903000e8046080d009000d0741da010031040e510704070075a40e100c08000700b003150f224114851556620718108428800340165019108004022000105980056003102c10040421045420000d018000a01d010500324a1004100c1d500758840103511640350003005258042d045c94403000401880d = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 939450989 1250 939449739 939449759
    0x1503131e0f1412040e07390312021e03070e06030718060306032609041103100e01050915040209100c03030f0c0f0c0f08042402010221090f07 62
    0x2225080d503070182c070842c00b02c41d02d03030361a240285e024480c08401c00310000f440540c4079031405a0188081e0451098003c1c1407c0300b40036403900c61000722a400d2a100800c81456003241c00c1d6210321802d00011441c5c0050740d10010b01104800d907600100c2d400001c007055019114018030407031448000c00c90760b036070b06040ca40900743d081017101e810800d002864001070614001d20607201100d41101180200081e248051b01c003245242c1118102e440041c004004241c80320b01c01c04030500301c82c1c0c0d4555070381d003020300700301c0b03400440340d03010b825501c46c0031006000d00d40301c1c00401508048001c00032040851043c0024003c0c1c00794481940c4c21400b4202c0c181c82c116403100404031064000d07241007244540180004054a42a00080c004101608a03000c40c3c0ca101e0b42c0c0941d591405950904070440da290345000c0d40fa03016901580781071505056000703103208080d0413914542001d000071442c08500c00c4813558818500440c24092424443c00a5605c440500001641c00480402e45100d140c8520310780d8 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 939452239 1250 939450989 939451013
    0x4020c0a05010f180228061101060504150506251a0709050306060f04021e04050a27110c010c0f0207061b02150c1002091503131e0f 58
    0xc0d07800e600701508018402c0d6144220526100e0b00b610348240a242d9809004031441291442d400d490450140000c404001103d41c0e030180180b6500c1c0d100c00c0ea5800300450035500c4030b801151049180845400301211240044011640207541050b10b85901c2c803511000880080a4024004000307000302f0b0070803c80d80f6074151b10305641c80044815848510003200c402c0c015000d40380d0903034408404280c552a00c0d800030003003041c00800262038001d12001c1c00d10210840e9100071681d0b00301040c10302c001c0c5416100100a418040300d044080b003519820800b46ca8520507041040b1030b50745551000715604402124105044140280b00d107160303072031000b000c0181181d41500140100b400204010340308286064806400805d0b89801c80103e03000c0040c01d9080e40d0000c0c5440b0401c0002d501560320a1111030210f4851040058403204c00205122a015400c2607000300328008004101510050b260407418168000700c3c0f01107a000c01f0100c1e440d1210342c9010291494130500481000c0000e200800 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 939453489 1250 939452239 939452243
    0x15021c050403170711011b0213062c0a0218060703020a1509030816030221061e130c0908120301081018030c0f1502030702010c0f0207030b060f04020c0a 67
    0x5840300110f80580c086650066034002010307044a40b0f4425055803140980121a4409030b0b00070502d50f62560001d4503e1a00b080045842d50306c0300000c10031070f010f40c20740c1c101c0344940c00080d40c0e1065003012002d00c400b00c004c0c60320084aa0104816186408544412080c10406044180d85410906000c0e64481d0b502c2d90840301c01c6400400c110076003505000d400d400030b034940c4035400113842e0b40c145440070009420b500000c0542c00c6c000c41c0c01218500c25036283c11362840c0d12064850801030700b40b0081292031030104a00142840b601500d9072100c00100c0c042100307501d8001030030301c40c941c4200c4072007110b54041320840c40748509603240040d001c0000c5040b10280022100e44502c0c03450344c602551480200000e2001c481c0e528540030034040c00180380c1440c458607110340c1b40407441c0d442e5074000021164100c1c41560201c204551141c09105014960603207003000c0c0c0001003c000003d65442c06d90200404000300100030554648031100c1407841454020819515400d40c0462550740e18001401 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 939454739 1250 939453489 939453503
    0x3021206031f05040f0c0b19020724020f1b01031b0c03110307060609050603010506090c0f0f04080d0e1f121a040912020c0901050a15021c050403 64
    0xc140c0320714000801c0c1c002800000c20b010109003041a5900042c40000c0c400d0b10b0903180c0d9008000001d40340f804045c003510141100540714030300030700d10000603c2401031100a540c4001424440a02351042c8040d103003028451030030075080b80d080201d0030681c40d40c4600c0c0b0144640d200c0d040c02e4904bc1025036401c003c0a9070208a03068480221040480340f207803690020409040e40400801d1081300c6c0704103064500380c12246004040c2d640c80c411103036507900240303102e81c1c0d030000c2c441203103028054030303402020480d403281c424209204190042e20505000d15010807000400000e03501c002026a4020401d100039101a0140250040c080b58610590f243c0300300941c0e0240c5004010b0031015a1060700301e43e4854040042040b5080300620006800c2e032120105100d40704c41658036805404070643c0700c0c41e607a10740310086500191800c00c61412061040a04800502017034403080c0a0004503a109103c4844040740c00906909000c0168110b0500820101c01e0001d000e401000030802c59104140c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 939455989 1250 939454739 939454741
    0x302090916121401052709010b04051303090506090d020d05060417040609060c0309260105090102070213020a0905031005040b0105040209030c150d061e060215041709040c030212 78
    0x1100b204a9207003a001c041042c107040014020b03810003d11070103d001080d0f004402c0d00c0038042c841d000c1c0f10000c07610006071703a46804d2000b00e54241801200d4001c1c0312852102c080b141d0542e07029200e03600c0f50103101d000fa900840c8000e904d0303851700000c03125160080d065074182c0041c0d003000b584401c01114155440a900800102010000000c407011a140e40c1e0340c01e5101130031b0500488424007282c1d002d4042080e4998085002003069240100c005204503203c1245030303900c40d20600755040204503075003992062240002503100d42c118166289441c40006951300744809040d52868a150003180d01f41c0b0a14207081c40c2c4134503940c0701c180203600814816501c3e070398440400069109030300311982c058010544030312240c100f1145950202029102c84e5041c40c4698455030225040c0c1e50001d941c030b5130368542e02742c000c2d0042c1900d24090003d520181940e01d030f16400307403141c141000d0401050820906032000d0a4105c1c1015200c80b01d034010014084559201c000a02075000981d0794540d50314020 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 939457239 1250 939455989 939456017
    0x60509030a0b2e0816050d11030a1a04051e07030b1e0702060406051302010507150b1215010b040e01170114070e010e03060403020715020c0604080f10090c0b07030302090916 76
    0x40b1074408581008102c008200442d48c2c170030048004c0250415003510030242d1050000d4182d10109119503141201d4a015241c1400c0083c0b429890804a40d12180c1c01c14800103407000204164040d01c2d009074040006446000a0488680114130890311a0011405002e9060303400b0403058001c134003a0030203000d661201c8101160020300804000c0c0813407801c020301400240240c0d582c0c21202011180018020320010104044181c260100c600c0c94000303250b83c4504840241c0c4c42800340c000301a181f428142481040289890180074038400c92001c50740101d1043c80075040726204101d0310300c020016041c00000a0032040c2619030b40c0d030205403041c590101506000980301e10454046c0c1c0141071291400c4512002e01e442d8802c200e00718001c801d4088081d4940500038001400c1c0f4000912040d4141c00030035081280304814035002034201140074012401500d0000c0035241c0040009035100181e00d03007a0001d10170310710b0841d00080c0d440c040000340d10048000f41d504012645071b07800c1240c445 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 939458489 1250 939457239 939457273
    0xb1c06050303160302030d050907050a08010b0312090303040b0a0309110108071e0c0f0b0f090d0f0e0a030b04061d0d020703060506190e010f060509030a0b2e08 70
    0x6809000c1d01a4802d1100310b10440e0351108840e003da01a0055929190082c0d1486003550340c21110303107116501c066010803039401c04403507210040c50424000c01101002100103500d682800360752031519440461242d40c5a40d00b44200d600a003030607030340c03a9600e45070160050045d08903c24165444d100e0040b4202d52075010f81c1c0703401c5c821703520343c0d480020807064200300c10044001c4c1071702c4100b001809049840000c1035481c514906501030b030321032911442d06000540549030000d24a40781038010581c2c441e80a0741020f003c5400708d0b514189070711846210300210721603101c0c2d540041d01d02ea40f09030030310081c0b2040d9403000200d000e02c0304800b8120303003840e0380803641d41c5400040c90005a025000030800300c3e960717621494100c2d00003050038005048918006243c050300350480c426170555403004120010840002ca0010b00c11801d080c2d06144150b400a43c84541c01c02019098440310b01c0001e000d401981da0407a00301c0081d01c03825804031403c41c0c42c0034021089000b440460321400c185a090380c845 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 939459739 1250 939458489 939458501
    0x50715020606040e0f0a0503130f0e010e04031b12180501051213020315090f060403140d0b04110706050c0301050609120f01090f030e0109060e04021608040b1c 70
    0x215001051035484140921000b85012446400035016040705030000c03020602420340418081c0c00290307190305000450103810b40182c0e000f943c048401c0c4400300f03c203d0741a1202811603107881501c100c42e665034101070344c0b0000d210105450728019008264100f01100900f0003d40c081c1d036079100d446130b40208021501410350700885000c21010b00800030466040405207500032120b10720201280d00981c0803034a4854105840b941980a140410070340c0349040207580c4241003000d0003000d280c141501c01410380480c100b080c20b00d580d00058070070710307515454010480004d00584204505107080080d18202c0c0c210f0301d000c80710142007001060074000520107590690340b00508061030841404200004d0107200b80c1440d4246c02204658200284d0038815602258050a4880e50262251030003e049850b0328810703a05001540d0810301c80561b010510780c101d4541030301e005a54141d4902c83c0f0320000d460107401455040005404901d8506490242c10062074010b0014401490243e0748025154 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 939460989 1250 939459739 939459779
    0xe0607050a0815220f0c0e1c0807020405070c1406070e092418010b190c0c2106021b06060d05100b040e03030a1d0c0102061f0b040f030507 61
    0x203079030802140d0750a002a401340d52601c60800008041d0560440b400a440032043c0c48408140081400011401d24102c803025115a040d42c008000c0580d50320b417880c80c0500040640265a01c0d000564620300900c15001120340090b0b40305480c90341d500071079035281d07801c98503000092030000505c0345d03904003466050301815a0007400f94110401c0a403c404014103010750950018080744c8110f94846840840c40c00f0b01090044a982c030148408100c040010f03001d5960100414401104d001c0b6454428038410746841d500c00c070030f11003041040c54101120b525409002c10340700040c0408840e10013900038400b000311000341c806070781d03c9808007d0400b240b2a005012034001c40203181c10480941d000d5013401c0401480000c09249000000d851754000329603404215941c0e09522807000c12424810512410703274002030501d40500e50000f0b451700005020110104040f0364011003001041000c6005000b440700416120b0b40c1c0c90309980180f07480b0740b00c11386080c0185180403034904400007049036160 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 939462239 1250 939460989 939460999
    0x30b01020a03020606060705030f040f1505031e10150905090603120d0c0c0f03020109061a0a0e06120f060115050304081204050f120d11041412010e0607050a0815 71
    0x341d00e5800b801044e1f40180b40444050000300b108030342031701c48503019202810750f240581c2e040a003042c40340451400c0d1104540180802442040001840004d0603d8002c484505d2901d03251680d146a000c0da40706a040f01d0101103081d04c8050007180c0c05900743d012120200c5802555032106420f240d128054034000c580d07045010407995007002802c0e045610010300b903181c041d45408444e00c03031003607009a0103800c40050f5140c1896406128050040a40840c1040a41c0e95a24126000a0400c000394403540c0c0c02c0300320000018503282d0f40c010555454105a2007520300c81e40ba64401c0c651241c1c824000c00c102e1314594250100c41b103100324207a901c0340e54001c034000e1609a081c25410310240300140201d80c00d10409020958204041c801113001642d425034840e220b42d00020309605440301d41200030201017080c0300400100c0460501c0704540712040d610320000071117400c1c00318054000d106021209218800030301a919030711100030042036029548188080d22916102d0a0804c6a9101c0540c00 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 939463489 1250 939462239 939462241
    0x9040915022203030509120f0a29240406050d0b01060f050c062e060e0a1a04090b0d050703031d0f09160207031a010501110a0f15090b090c01030b01020a030206 70
    0x64100010301c2046c0b101f0718002c85a254001803001483d00c9505881160040f6039038660003038031104400e0a0200c446000076007600740c5007555055200000c4240d0603c030b092080036810265484030792110016180261055011160302d09080c0394844007031050700c000501070181d8a0142c0d2080040c4c405c0c51a141018101548645c00d0760704181d40c1242d400800040c00c0146641c0703142d0031500800080c1041e0b1102e400c0300c0b480d0070810084032259440780659142035002d9100d0384240178100e4080d00c2c645600015010342e6480810303070342c40542c0c000601502c00e825001c428181c10180c2810015a42e0350b8030000d05d01c2e107138103020070300061504880d00302c0c071542d0102d00c0d4900700e02d0170201d0004403441101d030318503070b01c0c3c0b038200c2808081c407151402d5130240302c010b01c21035a1200d100c0e00e10620b41001458048100e66945509207641e0714041c1c200852a09512482e4181ea0030040d181034004001d01750904120440945861516101d103011a00d043d040301c0303082d40042124508503815070094070007 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 939464739 1250 939463489 939463507
    0x1b06090320060405031006062a06020d0b13050907091e0507110d03090506010905010806070507151e051f060819090308010e010803040b0d02090409150222030305 71
    0x35000e03101c0c0016034041802d00c00800d0544040200383d81c00c0c207010078045240d91074004090200000d0001010321850710020007070284e181c102c052070650340c5c018801640d07040d4401141e40105805040a540b141d43c095020406010b50380001d03010f04c00b80b200b070383c4d010340d6120380b001c1c1101c52a000104c841c22030000c2d051400103060f4820ba07404911810401200a16090f580e41829007404030303240840d0351081460144841000454090400b00d18108640d504011006565070ba000300550208107001a15030208204035140349425030740c04405003c1a00341e0b2030a0740745003400c800e0030764100d031901c0e00007000305008219502c0e02c8151a2288082c4c5030501c00700311800440140583d021072003040002074403810a02c2040039250199941d04100d5050460b403122501040c1e018100641c0103210902002e041102203484200d284800107035640d10101c00316010f0000307803401400d040038052281000e440c032038004100c2c404103814400c0a44008210023110b0109030f000190000d24140500d00c4 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 939465989 1250 939464739 939464783
    0x219030c0f03020c0a08070e0109020a0e19050612160e0f0f060702060705060f1e07050309010e0d180b120408070512030a0c030b090403021507050f071b060903 70
    0x45241e0291054a81c044c00c0440030603504142c80d88045082d520a0344200503190920070040e0140146003003c5d80f50000c10400181008101c14060303201c0c0c60b203910ba860003440f144070150003e19000c0d00503a140d401c0c82c51020045441162050518543c060302c2c0300701244101031036019450001c1902d0145801c00042c014950003418038550080c200f0400400940e85070000307481710314030410041c4039034035155021444002010307004280c0c102090440f6000000078541195001039030f89032040e10b03540c0d506a1540501140400c8603201d0040c0c1c03c440705680da011103000001401c1c003000449680d0365001c06411845521002d0b03000d0402d4801050004020500911905004004882c0707910030807940011241c0c401d985c15946299030715017008109030940240d10003100200c0b041165881c050310040e4072a400d00b884010345008140000e13003a64014819121054140d00007503880c3d10f030500d00085003440581d0032200b02d2082050000b091841407401000f52a0700040e05c0850818001100c8 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 939467239 1250 939465989 939466013
    0x60c0c03061d0708071514070609060f0f09020319200d0c08030904231603182405090a1b03060f0f0f06060f1b0c03050a030219030c 58
    0x1c600c1068100c0b5203818440400103400038002c4c69000d000014174021002081c101380b01c2c408024040d490700a0b2402c05210015110456084540400d0000040c9081e90080010003c07407000e0a02d01401c195100a9a9000c145018825400c680307022103110003061480e8032104004114048481d1212800c1c8071903444152114805800c124400d0815a603501c0040d6803504511510743c4003181101c16850140200001d4104618540960f01d0844418a04210008080d64142c0b920801840495803003907100c10190807004a02428281262410703c40c190508070006448081400600c0c81c1070302c941c82610b019a4111000307050000580c0d0300c03040340301d00341c4106e0328401d00e4820340000412040e0040301010f01d8420400102042180c20b100308983d0b8044403010780c40d1070244140815030300200c1642c800798040c1000c180078120000c1c0c050400024400c02400400358280c00400c1100006140280c98420313000d40b00c00184000b544070f0003001070740000d00060100c50b42000412a004250 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 939468489 1250 939467239 939467261
    0x130303140403020612100f06050f0a12110409050603030c0c150d0c0c151505010c1509231609111201030507170a080d1e090602070b01060c0c0306 64
    0x481c10142c1daa00060040d80280c0c1041c20340400305001c118842d151854420f0190403c2c0883c168224140380008113640114090304e08260400920f8445641c0140c0c0010003100303100405000201d55011541b4298119215450019080c0b20200300c041c0783c080140c40003400c6007802048850840390410203408491601ea12005030308204c40d5403500a5030081079103901494030340c4102d08401e80307410002a21b1101c410039180e4a80028000c50051003640e00080310790918101014005e03505242d032020301135003d4081d9681c507012000c800c00080642c1084a88081d00b010104c1c51050071845442c3d240d28030356030301102000c11090082c0c0e03003168000d01d480a80320340281d007040d821006505005c14280c0040d03880341c1c07144004001106803060703503201c101010307800307845410156030b10300269029440c45031040a48800c2c00d45030341081e004150680004440f0b05001c00c04403400e1140080d8031a06040e11180b10000012403800c0c020b010699110f0391082c03c0303e14892850f00d0303800c0200994140707 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 939469739 1250 939468489 939468527
    0xd0e040c03050c2d040e0f072c03031b0106090506030a0309151116032603061c1b080705150706092a09061e0e0405010b1206160302130303 61
    0x1d81d14840c440c4402400141030904203c1c41241803e00301c84121f204014408010031086004400021910300042d8207108001d01083c1c0c2d4240b202000a41580500d10b058070b044441106003140d10a015040001101d54100080045448540516468401c801d0b4003402040310703007004004003c150444682c0599061421401015070044060f040600c10340703541100e030a800005100b80601200d00502d2510900700216504880044140c124000140858401e542860f8211016040024220929a03000d03401c2402e034405120440015a440d0098030103d104020012885080441640c1c2200700b6000d40181008410340c0c2e1070004e000866821030700125201e40c1f031090441014410700c2074160542002c00220f050a0700007003158100da222081840180030725907000300b50700b640102510106048203203130340d85074100107005d400303984007131500705c5441403c0c800c0c004004181c0c903000c1c2d002c0b1701800a8000030320744110241d005102152021441040003040002d00841c0314141d4420f0f00e10f4 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 939470989 1250 939469739 939469807
    0x12120a081f032a0609170102070501020c1f05010b030a02030a1d0f06100b040303080a020405060a091e0b0f0903011407320f09040207050d0e040c03050c 67
    0x819241e42405074000c4030048603908140d10040c020306400078544105115070030019152a50041c000e4002d4070940b46d10a840c061800b02040c402e4044485c00b43d0040000d564031000380103666504d1245103101c40b0201e0080400034842000c07406454102c1c1d0301000c0041c21a1100b0b0382440003075002a154408055452a40314011001c16441030b032102111006803003e10503400c6403d0410300002c1c0701001c0c02c203102710203020b0702c001e070b1065805a0b070f094540800c82c0d07603400c41c0c524000c2c407d507001507600c55004542c52000caa44034010340142c4500c070170007c0009090681c1d541c1901094050103001c036405008840111400f07001400503000000c0000c1107403c0c80f01c6015946290070340d00343c4005040c030800c05c2c00d00c101440b011480e21401e008040640e00d4a010004a40c1c0036040d560070ba02480000c80394200c1d070b240d4041d1054550054240c5403101c412040c0680310100d02002d040c0980d04140310780031081d010380700711849042e000320510b01d061202018640e0000c10142801c1454820740 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 939472239 1250 939470989 939471031
    0x30a0e010e03060a0b040f02030f07200613060c0315060f031103100e010605030106020a02010c02040b0306090706091a0912070f090b09061c020405040201020c030d03020912120a08 79
    0x4525070244104c15000100c1c0c201c4e200500c42a1035207140c000851034010428004030548a50800d5801001c0d482e1104050441c40711201d030700082c140000481e80305243c1842281c405007008154150b01c04d003010070040009a1050b0283c800203807600b08010b218540404c801802548014211030f080e180000300c80c80300184082c043c0c1c1040d0b505c0c060392070464000348040b0070b061403c51702515090810905540c901b4070001d42e18090408001d0420450303088060440d21507401410380c2c031400a0540e1403c0c51300215a607511440b5100300e1000801240f8005140d5a4100800c1c0303112030303210080c515002d00b2509114035030500c0990b04500e44200e200004854034907841c80000b80c40c0d6500c0205a0b141034004114240501070b111b1441208522040103180400f108001741c410707030541e404100382e42c1d0350006030304228080744080c2d010302441075030000d910b034141d000306800c80040791400c1d5001c030141c0110341c2d00e0300b20392021070718401c0400200d829180519070300d5030f101401c1c2c904840e001c1403074 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 939473489 1250 939472239 939472243
    0x2091501181214030f0f1309020a05030402030c090903070f110402070c23011b05071e1e0e0f09010219030c12052206110a0c03020706020d02030a0e010e03 68
    0x1640305010344018a00302c4010000141c443c0002200c115000f5414a0354509101c82c051203804100320082000255880c499a03c0d0303a070050052070082070840d151862500060440da00485007280300707000d120411445803801e003003242e01030108c0400450400c1d85640c2c8d408621030311030701c09542015003042105984c0e03a5900041c5942c0d8401d11031001810b03c0c20483c0364900c4502201020040440000480c49991100d0290b1000326884001c0552020904005080c186140c200302e01d10060300b4044120b200d50108004102c0c2c142041c000b20b003035040603071190840c0990003000705c0d0504460104072200c22000f030142e0003a14a0780018509400d0300003400c41103510f000414042502c2c1d540c20103003e500315005604000103600180321900d84109006c0448400b4550390a45041e0916000c00380103055009404a680e5521650f603540348428018181e0f000c0c034102180103104204011415501c04500c80c3c0c2900f41d550000c3d42810003600054401070740fa50038441c1006082a4601007583d01 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 939474739 1250 939473489 939473537
    0x10c0506040c2402030d020f070c0f1505090904080c12041212020a05120313020a0f05091b03160512041109010803040f2c07020d020c0d02091501 64
    0x3150103428902c61600b100350000c107041501c01c50188041c11807100d0155004011562654480395005036550340b05082c5900300c1c0500c14015081c107501d20004221a150031102d08203864a04d22404c41e02000d020341100e0754480d05000603000f0f2410004500000d40460203445506a80d000f17903180b030202d0b600a84040d400641c45103034220300035400d9400f1b00c022245508a40b8840f440500070144540c1c6038581d03a140c00d40040c01c2480000400070384581c0148016024140d4001e000420142d030718405c1c81c881c0d0342c850249921586002001c5004941881c10b503035100900e21030704500750740e0390700c0245a242001d0041e0005102c0104145002ea000c1400d03100c0c880d0788101c2c0b211410070b10300d40510580d01416008590311340d008000600020030892200300480d641d90040201840d03c1c4d40c2d0403c03520f5180504254040d40344000e01c8003c40c0c01144a411030a9190300f180c60700c2c8008402c001064070800302c0a0341110300000441c007190a410900610240d060400340301880958486a0302c3e012 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 939475989 1250 939474739 939474743
    0x30c1c02040f14070c030504050a1701110a0c0602030c120a140105030d02100f02040909050a0b07081302040c03090c1d0f011d0a060b130501111501050d02010c050604 73
    0x1126880120452815114929111400303860401014a040b90f100c00403040242034042800740d0040c0110801d07100e1811540038100280c01c03100901e50b5411004400803104810a0b100e509008551031102445401da5140034482d55560050080c01e480342d200a50015000942c481c20401c400c1c160f0001d400c0b1000c0c05455986d03000034020130500c0e100d0140349030681006100b500242d544488180d400030704504d02034452f03c00007411510800c00341000748a40d500403000c0908010b01d6a041c4900843c0c50b0010300d0240e50301440036901c1e2441260b00d0007084660b4081c0310000d94000025003803540c480c0c42081d0150800081407a4103403030700e91403080030b0361021403203880e510302c450503580040f054140c012003030304010300095040600d0a10f0108541d52154000907000c00003c0040c042034120100400400410503031320480950550000c0340c950180501207892128060300c5050b00148081044c12050003100c4a6400e0408024840800c0c18041c0c1c10000004e26400c08108203020701c0340a24 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 939477239 1250 939475989 939476029
    0x7270b03060415143a030f030902010519021e030a1103031306050403021011040e18070b18030102040b0406023304020a09020a0e01200c0f030c 63
    0x880c00408010698214030250380701500c410004119800750900b00c0c400381c0c4d6088842408070300d008003411102c001000680a0740403600400b0075018001c58410403030f850b00036038440c4144641c1d007070103809a030034144c40280014810400b011009141e20814680340149205480004110560150140314a40c2c101e00c0d4a400c00200707181404e070840c6000c10101200f0340690306502d482c40c800d40b00600c43c0d910150009403964005001c241c0f00380304403c0344055501d410000d40798482e69035940c41c0c00500440400c0400680403c1041e000034600704038103010600100b80c12404e02c40c15410176000004558030481694490801560302070010b000944582403c00c2d45491900c0b10080c50401d00045074140d40300381e00180b003d400c100d9401c0030303141e00c0e401c01d40381300c562220710100394082e03425032020710324920104540c6c5074181e10000c01d000d50031090340e07010407013103480911560200300201c40c16038907400174803040e20034144000f180c140090020152080c0108110204071129415040d0b241c40c2 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 939478489 1250 939477239 939477241
    0x304030912170f042403051f2303061014090f041511120609130b04170708031f150e040b030307050d02100f0b010807080621071d060907270b03 63
    0x70a9251160745e5100c022010b55946c154231205813000c401c48140101c2c959000711403110700c1603d243d2008001c88001c050f084900b540341c80c00701c5180d072040a000340d001e45811403003280d0f040d180a50200c0c3c040d86d103e1083e04610344035a83e981242418010104026a07250340c5640100001200501121081031a1812040ca449010003a1006008110614203000b16080364085903c100c280360740107500400d202c1281101043d243e0f80e40c02504002400c2c1403000040020400b403003101c0a004000412a240c4640d80702c8000d01c800840010140c1b0000745041143d880c58540381d00705140b2002e016007505d1814149407540c60400d11900402000b6901a80302a2500300252160b0801c00603090000c1041d0441f0200003015200090108420003207484081020743e038401b513400c848103c80c1c0b51510803010900c090769807959079504c6400343c000d0b000f548821085101e40344c01c911990300100f0111061782e6020f41503680e0010b8080e094450002020509288050013414401408000c001907071a = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 939479739 1250 939478489 939478559
    0x60307020d02010f05040c05010507260921191e03020d091a0a0302070206210117010213060810150c20090613140c0304030912170f04 59
    0x251340c4492010504107241104000100f200c0381c0040d0192603092805c107658001074140142c2c118010040701c100007002c080600340c000d6480b0020000c0b4401651008003500b0800800459900c0c410102c02044e001800154005020311800313602c16031040d400f0000c0e03540340c2c1c21058125130b0900b508401680c050303408683e819070041d04941c004e0a2030301c06007142c00740003410f940440c003c0d2604a0185500404d2a104560b51303103040d2107440c22181c090442d024140e06803400b60400c28030400c3ca0f02c6504810081040b90103000300d86030148401c4401114a1400c403044130b8000005100703c8020610701004512030300441603185c420301c01ca96a4031074818403820301881c40c5141c01c00740f03035112166200031800c94540c203c4c03081d0b11004c216410b100078040401c9800c007030400c4250000140c0ca007101000320320360162001e14080c500903582e02e00c07099107440e280c8142c0c245041c0c0152013456400200c10320403103800018881c00e903590742001d040c1580e07200d03141d4003c1e000c1c3c10549045540360007d048 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 939480989 1250 939479739 939479741
    0x411030901020d0510081c090801090b06010e1806090a1524170f0703021e030f01080a0b040605070e041a090c03101208040b0f1e0f09040c0c02060307020d0201 70
    0x34001e441010017440c154a030505095079101440042c00d0b900d9032584074409514044ca40c00030082001c10001d214000320b520340707410035003030486050780416105d0942050500b041030035400303000c0e40c240030801541ca40200700308090b24003c01d002003040d1180008141e60103540d13400300080161001507944004510300301c03080c15a141d2000c404201c0c81c1e40002c6c4241641e0280141c115100000b101a16120080228040c1c80b91100c1403071800d0046081030556900e1000943c40b41c51580f00341c0f03400343d80b1206001d440f12a00c180250100d414540440c01160213680000d401c414203051005080a5060221b07040d9400e514804c1e41300e40200341490441d06000004541c401a103400e801d1461900c41c204110b00c0105005c1d4581c19034017010154104040002120054891140d42d95200d0031500b450072002d80c0144007200e803e000490380e10104041180c1924440840340b594079080450000600c0010300c0032080304410072081c5454500541c490380c0045020b02040d6003d044600701094010f8 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 939482239 1250 939480989 939480991
    0x2803030806090411040c0c060c020f07050d03050909070e03060f16020c100e030a0b151309020108010302010503060d06050109020a021e0a06021309060605040515130902090411030901020d05 83
    0x5000d10b078034a08000008407402081a007a1008030341c0003562001049086402041c0c40701c0c0240201d10300207070410030640020341c5070104c0809604541c141500d9000f80686880100d20090114405101124140c9000f41c41c180d407003000c51810156900c07083d00008e00d0203c054030007002144a150a0200380c4018003050800c15202d0300041ca03802c2020004106030815040303014041090050b0024101c0d60705120140856030003500508450a00d000209500f801130043d0603c29105001072100000700c074004d6021468050b1200412a07285030015101540003c18107640040c44480900010320103100300350107083d04810041c0c442a003150040d01c1c10003000c4c250800e83c4950850058080e02c0050101c681560040000d40c5943c000e82c0c4032210081e581c2c000d15480760070503001140f42d6034004050305c1200e01c12180c0d640d852440304607601c0d8a10036180110f52215278820f0030f10410b203540c0c0040075440b070080c00000c1c0c5a0106500301e10503405c1030315903038041e0350001601c10081039503020303103 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 939483489 1250 939482239 939482251
    0x60c050c071203081312140d0e01051608010f05010c0f1b05010e1518031501320306060f060903030706020702040e0705060a0804171b0615030a0b0628030308 69
    0x611001607214048403030b060f10b60700000c20400d520407c0303090100e60191603d94466040500041022409480c003803e02200d007428081803059084078030601c40c54001d030407610210802c456241c01c210044883e8006800190380a503040d0150000107a500d4421041c0c0490a180fa924118106400109800703c40304e26144554403902c011400f080c1e242c0704407541072101c040404070b0880705e980428181404c0c119884040545800001081045084c0c3c54600c9004094440041da0004e038004031060040c1503019090381c02400001c050342803480003641d51340c03002480301e800c054000000070314590050001722407441e00418a0011424030340180c90803003403064003514000e414000490414010100300400304a4804086424000403a0182080d821103030318032542c40d00091007051100304101c025110703612899001540c0c142426420b8110301100070083d01d48070f0f656403101c4c0081180508036950001c0b41c498401c2903075034140304882219007500054505c0d40d2460601400130f840c02019 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 939484739 1250 939483489 939483511
    0x70912151b0e062505070602010507030c0905060c0a050d030b01090b090325230315040c051201061e060206011a0904050a1409280f060c050c07120308 66
    0x140001d01500716400750401036042d00d0007600c0c0c001c03c80c038420044103a04044060014004204e5040c800d01291074800c1d03a090fa0001e100329101c91008074100d414852500b0000b0720741c041c0074005445d1841c000d0100540540846142c604252030300c2e0b0401407035800c1200403940e6000f603240c255800040003401040e50055041c10000ea24022039121102d1111807907000f1201e0110069914000a800010344010906482e00010300c0015007541186014058428030070810b004c184600038411183c410340c3d01c441c0b8038240da40b0345424450540d00f030150051307040d500e5400100b29200d903050500248000c3c0e40b0003141c190700d0244040d08140042e04004171140c2440750812510354110b00300c40da0300c1ca040d80c0001d6280c1c0e039480c1400040000c900b503556007280f08418415401800522005016003004500d8110000104031410341c40c140d8800420503400d03100380201207281540000c00060340350510929107030007042180d08141d1580c10035440407091060710002d042e44601c0c500d41c00020303052 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 939485989 1250 939484739 939484781
    0x60e100c020c03071d070f0c05010e0c090105030c0d06020a020c04090f03140c062809030305040516080604021c080a031a010905011d15070b010e06010f090e07091215 73
    0x142c40317040b40350014504014010300e1a141c514280c4610740d00421107030024000c020394030004491544a044240305288108140780010546182c00304500b40018001481003103c824107642c2c0720040d4210107500010341c0100703003100581e51658001c04000c103100b0316040186841c04e00e40904081d002403001c44494000348a40c0510b0131001035a1500b010030042c09400ca0644a5020840a40b1010301800d0302c6080400d00b40416805400c554000d0f4403c03400d07151080512091012101c9a610956800364841800b0034058240499001c0466401c0010404816060745540007554001d0340b402c1d00180d960840c400b050000c0c00d01d82001c82d032017442c0804d0403130314243c0020000440e1503a4043c02c040c4820441d00e0070b41d518400e42850500d0451101d0f01c504146c20701010048092169640344841080051071940c1306000f041c80007990ba858042009041c00c0740800c403042d0083c69101804000b000105640b404984040c040c148203840329160013292184900581d811a40c01413403c0c00609 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 939487239 1250 939485989 939486029
    0x6151b06330d140a150e0a0b01060c0f1505071205090a02010c050102090d0336090e0c2206090204060504030f0303060e040b010602012307050a0905040606180609050607060e100c020c0307 82
    0x51200d81120003d2601c844e0715090cd00702080d0040c3d1158009040d1090303091a540a12a2a0040b0344104550340f0740d8203000400d10403485c2a40c004462280303490700103417000d20056014103040b04a0b18060b00005003020581c00110b52180c4503040241d0110380064a030244105810603050860050141d040c62500d06104044d07100d02e0446c002c4509954683c02452000c050800030b2540d07261000340640c00a081082407010110b540607040c4c002c2d0b904000011600a2080c002c40d412102160f444a191903e10340b10b040c0d0f51690324904508054032020002452881014800c0c012405070400c0102d552400a0103801c540740701d1090350303445140320750b240e2015400002c01380d40120700e401e2440d610190040121055241600569441480d0450104e00968055840301c0707924045082042902d8589c942618200c03124070960307901842c02c000140005d0281e80006c1c0c802d0643c0400c03589404110b02d0301c074040d540c0040a01d00140e201466056103840c04124240080103183c044140c0c0e07503881 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 939488489 1250 939487239 939487253
    0x190b010207060c15241e1401090305060c0310090e3c030a02070b13140f040e0d03110a020606151b06330d140a150e0a 52
    0xb44658414850140310b2801403000e9140021820341c00c840d410042040d9001510740e01740094400740d00d4000300044041503180c2c0c00103d103480401d40008040e0490700c7d01408803010721001201904001010344004001881040700364020650040390940704d2030042800765801889030f00034840141002600003005401082414484103041c20700400c05001c1c194848800c505865112004200d40c00031a450b01008005420852000d03426103116541e280000d070ba260141e0001086468410312041182d41c0c4040c606101e40071015042c8070501110320001001c403405c9140c685030540084102201c1150b251054640d54043d00180c9402e000d41130400070355401004064a01905100001c8a00f1090700c0c1c040d960404040c10640502e040d40c0003402e5140c14040d034000d82041d042c0490120701f04d107130a036546030081003c18400d007407403c0d1404020b1905110307002510080d078101030224aa603402c0c41055801c034050842c020881445000070811106040b03c69603040c4c11580c0c248000a2030 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 939489739 1250 939488489 939488503
    0x304050c040924020c0a0f020306090703021f030b04090302030c15010617090102070830070c0816060e01091e020a0b0f360301201c02070803190b0102 66
    0x485004007001c4103282451800034490b090142c91a4440d65844001f084a01001c503ca01e51082d0282c03115038441d0640d039541d03200d039400700941c010031b888503000907540341480c07030040187d5915000c141c44454201180440390769040940040e00000781c1c0d41295a010803c66124082614800d2070710361401600030440724018000015490342003001c03481102c400d4050324542c0d0f0f08421500e5446103904c1482040314803410740f42108480c0c0c2d002d4035510b4125140c00301c0c490303105a19044c0a2220700e60301c03001641d00c01d844080c120100001f4036408510300f8441d0b5014040000000a1490010b0070a83e819401c08101c0402035910724402c68010f85904a40f00201c0b0556141641c843da00f0010140684c000c1420304110b80303a00300390030701500e4451035030103071000f804c0405503203c0007804043c5404e8564215558288008128a645100d0000801024140034003040b1104d1b108180c9054010b130380c8084403e0f9413030304010040c01030800c2243e030350080c050b900600410120852400103922194 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 939490989 1250 939489739 939489773
    0x41a0309061b18220207120302070519060905060a1d0109050705010c032001020d0b09040b04020f01051326150a180803040f0506060111070e130b0109020304050c0409 73
    0x20200183d0005840700e8988141d842d80c4030b0484011440003501e404000d4018141c00d6841215960702c8480c4a07019200300c03104d542d04034010302a0309070350620707050b0800c0780c0b0503044481d2a91403130721001045c0188600d40c002d07891b02d5800325244035500da00c0000d1260420f081d0b00e1992401101400141d40065190100c40003030a02c1a0080118181620300b9100307000c444590100448140c0600e1006500400c203004494000b00803103a40542446440c42088400400c0d078851340021401610b403482030001e0f490814540301d850100c0c0a15511154035056100c624000c086040c24403038041c0c103a0b0010b01c141d445e0300042c00161030000212942c0c1e0000390105135002e13644d118421900100c500027403100c5820030105903403803d0900d030001003107032700400c265080c3c0070f03100200340309600c07806e5966031112030b900051401c00c2c204101c0c010034481c090900c0085440178640c03800000d484512060080c840b8101c0140c90740b1300382c14090304002101610b180300354940340c0301d60300084103135814202c0c1d00c0c = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 939492239 1250 939490989 939491017
    0x60501091a04080303041103071203210b040c050702030c090403020a033c030501090b0604141c1a01080102041a03040204140a0b04110429041a0309061b 67
    0x21074821858600c61500321000034000041004113200309543c02d540e85810540454003896595103503c843c10b40030700c0004001503880c8160300c007491211100908d010050410001c0e4441d0464009411641a0742210010400210b4441d0035403800307100035a070281d0140d411b00101d00e0b00e560029140d081c6000000c2c1885856142a801481002c410030f42c1282e401d140c000600c00e220b6030101c8440518201d0b0000a8200000411004114000c5242c9510060034003410141800c950030004c0340c220141030f8001c800a1008090003144100c403251450040e2450250750348050310f2502101d4050b00400507582c0100000c01c00760280e10b02120605c52000401c5449440300d10008028094203800c00804804190a001420020303911075180100e04640401c008a140d01d07226180e80260b105041030390340d09540138044c040b40c107401d2004d070381f0801ea8091b20b01794652012421064004c402e405150b24080100080540100515a0001a00f0842e26004503041921141d0381c030441040c48010307 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 939493489 1250 939492239 939492269
    0x90518040812100807062d051b01020f030c1306020f0703060515030609011a04090c0501180312020c0405090f0705060a09031a07030b0603041a0c0715050708070306050109 75
    0x2003c541c0070741c900501076480c10340c0e000701e5403001d009040d040401c02102c4c03c40f20b1110441120721108959021141ca180c136502d09000300355191000c0c03820006488005550204130034020340d01e00000952003200351200054850b071415039017080c0c51003d50070102c290f5200a404a261320302c00110072040725440721000c500c0d990340d0340240300381c5c1029055154040c440c04041c40410b00040d0803040001d0115181101001143d004020a41e003154601400d420944a4180000d502c152000b00c160600d4180c40360446030b076075580c010f14100c40c0600340300582165884120a140c18000c0d07a401c03440500c001e204648188071425100d80c6540315062140c800002c1110303e06003c2c40121004542101600402246103240c8114141c0110380002c0001d1405089a8042c5003400940b070103550001840042d011041702d811040780f401603c0d50102c03940c180000000a041d859440a4801e001c66010400d424200c3e0081c208040103050719041c1400c0c6002031005990107985042115050030324400c50b = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 939494739 1250 939493489 939493501
    0x15040c030902060703020a06181a0a0b060c0604020103050c1206010c1401020a03050103300e010504034e0c2d0b07020304050d140708060106090518040812 68
    0xc10748440001d40002000c60703100d00b4190049580000240118003d1000f007200c42d0a404101000e40c100a10a01a030200304004c000590301d034541c0002c81013030010783c0504200010b64117810441d504821a40000208000c65915001e0749810000340e108070f42c00c0001c500c0c020042c105005203010304000c1c540601e2401d02c0501140560b41d00d144900071940c07020480070040241209000c26103844140010104808006620706241c0080d540b075641e14003003924108450302c0e01310000300d50400c40c041c000800410000f1415107003550100320418140d910090441c0e0070000c12083c0d090617505850080f001410120884038031800062802040b0340c00b0a240c03044003400d0709244000d01c2030b24031400c8409141c0300c0c0480d1080314090800c058490b912200100c0e940d2186014181d000f40c8600103100000341c100480080301010035058070420b5441d0041103103861000d03400580016007905081155081c001030100d40c1c25903494290f1454505519010780a201c1c1c009030700344a41141d000205 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 939495989 1250 939494739 939494741
    0x11505180a09020403140c06190903170421030f0320030109090219051804060914010c0f05090906120f030c010507091409042a030807051515040c03 65
    0x1551400007005046503907154603a10000b90810300040310503082c5081d50190b9448001034400c0d8050000713005610f0705010407207486280031002c1444040c8840e07104040000f078454000403c95060703505c140d80c2c0b194605031038031002c402c205d043e0718103420680c0c440d10003003580000d10000c103210382d081c042060100d0b14201c1102c505001e0030704000f40000300012881c40c81035000b01040034022103154240c1503a00700d0004540103140304030341e070240342440b40c0d02142c00e040e0f0032a54810b000d184001aa422079864030b10b5144440410211103075520040c800e100ca400685103134145c0300c9442d101e41030807400d4010660040c8050a5917102e1b9505100343d4200b8041000011004480c11007a20b845e1041640600e01a080c2504c03c000883c0c0742c0d104c041206c0c00b4078070f010444040001c200c40c1064403545c580e140442008001030304084800c1c0c20780f4128400364a0803030020b61003404010350303d641e50b0401d1420088100307040c0404046040521441000b00a25030740b219070120b03000510003010100541c = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 939497239 1250 939495989 939496027
    0x1407023705010606030605190e130816030816120e0115030807200112090221060a06080610090b0d0f150c0f120504050f060405030a1205011505 63
    0x1000e0140904480c0c8200101074003d14102d800d2600c0a000f141d465900b04803906003686042161154512000c0000c60b86000ca000c0e00440011141d100c0c1a85546907001554030441140c10400a807450a40815a00c101d030030380d201018065004c035000010600810641030b103051800c3c0031f078031098407692085080d40b000404c03c0304020174220140d500d141c4041d40d5044a1001e40b00ca07820044858000030004600c00c006920594800f00010400500388004002040080c0d130411070800c100b004240c0c0ba5890f0304d090030103943c01020149480400541034075440e07048011075400050611504040c00c1c1c0202007951801503020640c2240314020448400178460068103504061a0007414003000088080700000340400a11180c40060f0003a5941c0c44400381c4580015150131265000700000d900030740e0024420420740e1410140c00d1142886d0500c180c406545541000440d0142680c1200c110b5403010b410102c01e0100390305d45454080038040002c51042807010006840000d880242d80711 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 939498489 1250 939497239 939497323
    0x10e04020f0303131a120f0106140702061614011805160501020a030c0302032205011709032704020d14100305210c06040302100b09010e040f05210d140702 68
    0xf50600e40340110691f14000c5080c840c2c0401714440d001c103041c04d540110304a810183d0003500b03152501d962840542d805510305401622400d03015140e40b4900b45003802000c401000307818620309134100c5410700c5820301c860b03100000d0449024180c20440c0e039802040410031503402d410160508640d6080503404d40c801c440b0f102e055011070f20010500e0000000d030110917194281e88804400c4401748080e8110706058629100d2a4400d11000310010268000710030601d0b100510204001942c0000c10180d800c00040354240310b4a904007042c404250034015a4441a000d98500700c486c59600c0b5140c8071b084018120581500d000c5194491010724011610220b80002c12580e992919040094640700c0d00c00300e03a104c40c0d0904070405040c2c540119024103803054240b8086c403c0d01c6650b030300882d0302034000c012179160040074441070ba0321022080c0d14015814940150350346031078042100084400c00d100700b06c0b0810105003406501540052403091100040b058451500783e402c2c1151203040d400c642e0 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 939499739 1250 939498489 939498517
    0x1107030803070c1a0117060f1f0b0d0204090e07030b011e030f030e0909120904020a09050913020f0405010b070609051228030b010219021503010e04020f0303131a 71
    0x81002c942d404200d050403941b42840c0814203007448091070351614000c0c0c0f0302c464062080c001189802000c0f104007a01c0d0b00801078030f03051283c1c2c1c4880c60f140981090303044486584e070124040102c0b4529014001c0f080518001408d16141959181c0725000010f01407691200083c2c035003014510040021a001f541d00301d070581ca2101c80c945802010303a80080c1c40d4a0051030b5640205401e140000351010005108004031070030100b0f010284030007500301c1034030741c41040305803030b0009581c0e00c40110fa40e014100d01c42d004030400d4a280103014001e0391019806001b603107031500402105102205813503640383c0c4603201184142c8142400c6140040d105040041c104000416015848121240c140b1200404d84500c00102146005404441d023035214503025030000004c40140e207140c400c852840b42e00c0140381c0050020000e181b04455002600b04150300c0c448142400198038020001580b07030441200114607044800805203040c020314410b80c280b200d105002403c8004158080e00d00807110004 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 939500989 1250 939499739 939499763
    0x7121104181218050d110411040e0103030219020a09051308040b0a0e09060d0f05070e01061d10120207050c090703090c1a1b030d09050d0f1107030803070c 68
    0xa00c00600403902140b00c0129040b40c1e82c4003040c03090b035003d10040700c20052904008200039240c0100400b04e0007066039110796624141c8107200090005840a404219104000c5605520b8043d282045a110112000300c10f180d00d00c0042e0f440680050554800f4000860030740c41310300307010040306980c2e10700400d046c401140c0410304001d800080d21092526540d5075810808030414440c0408040d202c0325002000060743e54089030308211100f0105100d070301240c035816030360110307040213060030781209001071003102120f64a03c0403617098103851181194403012012510300c02405900c214012001c1c07d40c4c0120324070040c001c0601010201080140908041e441c0c4588024010021414102c603001d02e40c3d00089804c0c0d0b4075442c00b9800c0d00700c0480a0785800740401e101025000e0030740c3c01607543d04c01040316112044050054282c205d214400a050b030071f4241001401c4035149120810803c2200c10342180140000580142141d0b0030402c03240c1e690b1200c8004440c58400b4081c00341000c0c100710 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 939502239 1250 939500989 939500993
    0x5130b1005030a060f03020612101d071710052218120f0c060b0f120105070806010e01020304031b05151815190e030a080415020712110418 61
    0x80002c600c154041d440030003e0319207602d0100410519400003a41001003401110368400d030960003590030800d0a0310341103c00341e41d0000b04080c5400b100c2480300b0010618103000031250070072200c0c207525052180b560901e180001407040a010030740310f060301c110390070242d60700740000c41c68940d06004194841031050710b4403203e05852420108030110b61000e0344100742c0c00300b544103c10b9014448819503070405403610b41c1c0c5030381c00904801624203034071958180509521b031383d8030b580d0110404008400842d40745060000075000001c02488107040c01464185101c40341e0b40402101c09907984109400b00348072014a85030320500440d0401600800c2d9842c45110760314070a4081c10414040680075000340c01868148040c2e070f40304032680804028140000d041d4070040110ba41c101074130320300d0f02400c0c3c0c030700d1000000d207010042113058030310000c00101404101080900000083d602b400209050707841d00c45140441c0e070801c40c010b40815003601c201c0b8007079526900841900905107a428085460314 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 939503489 1250 939502239 939502247
    0x112020d0603050d0203040f09150f1404050a0501050109030303020708040f0b070b090a0209040b09010f050c12180d140f070b0621030405060a0302070b0f06010f03020c060105130b10 80
    0x500058440c0e00c6500313141d080c00c0d40700000311015140d101c00660785c09454003c140000d4900b0482c0031560f400030200215243c8219100c980051100341c0041c10081c6001040c04222403002c2c191181c201d0400c0014803590b60004a4002220762500d00181c1c0c0f40002c0c148042c441c0116040840d2003003030614000303403040c44180907003059801055548880e80b54920741c0c0d030341d07070302c446100a401c01110700c00034000c40c240600301030380207c842d00046084103105844604943d000c6500c0c0076441004030305520030b20b51101d001c542c064a0300c00c000300c1c2004c40040507a40c600c01500c0400070880780130b80e440c0411003a1002c1e41c2c0b8407040421080c0c0c94142602d085126008100c5450303014421081102c000c2100000d144040381681030301842c036050610003440b6495010046c0d89040c590200885400130340441c080901c162200907400a441c10f008000504410540300401c040500500c00c0ea69980c0001c90524115002150301c4008445848044405450260001d0360b000d010301d51500740c12500 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 939504739 1250 939503489 939503501
    0x3e01060317091009051f05070516140423100b0a0f0305130c090e0307020604090b01090b03070e0d020f030a0b07110d1407030c0b0a020a14120f060112020d 68
    0x1c125075641c086810f50768201c038001d400d03104c0c0302d42c05010800c2c10600d0303031030328842c030300c0e01c002186060784c03912125441e00c0b450b01240d110200140b0300303c03000401591b190080400d075505800c039006d00c20719085480742c05100b40300014175500a142d10022904003a41805080c00030302c0d540386441e0315030078443e4016104810035089400404d003000e0000d1400c0c0c1010545161803584000c1c038030b48690402855070000c0003110b03405803592004200b84130140c0d860b40b020304001c042e100400714000d11124001405e0726550f034841d15017140140f0601c00001e0700240080c00007038041d602200c5207603c500014000e080c0003030115806014500943c010b00022000c1580700d0b10301510f940c14903a601c003d200d0f1f540d04441000b0030001d107e21401d01c01c4c110b0000018004180a454950f00c5569551a20000954281d5044140c030780d000402400f5150480d210419500c51441c14900380200a405003c80100041c00800a100d600340010300985c001c0349000c01d41e4201080440d12101e8810341c481c01866 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 939505989 1250 939504739 939504757
    0x103030f1803030516030e0a03080c0712020d1709091503010b030309130f0b04020a02100506011e0e03120d0b0f041b110c06030f01063e01060317 64
    0x204920a0310164101031507001100d0f49030799850724005850080c4800c40c006010100c0c10082d40d01c048004558500b0b245601450103101c01550710114442183d00e000c407030780d01106001b4491070704a40982e075075400800d00f45802440c609000e0000d840103060034410805030560050320034060186507141150040c40b00e41c400e60082101100803002c02d036072400755400465104103a40d05400c803041c0142c000d101881e00110700070580c003c4c07182c002001d9811040b5800d0050f072120701c03000c2e9080c41c24000c140d00600e00382002c40c12811024110707032109000c0503040d828050100340040490b1010030200c4804140a01e20369243e01011034210081e02c0c48031161480f0b561000400340451a2901c200c0b0580381355403500f8004100007440039124000a184801d02e00e00801d00b0fa0344643d01e4001c01507200b160b001350302004a60600c01d0103006682400d145104550001aa104910340c6000c0d80d41d135480c0124919103803514400c48018090020b40d08008c20f4081240324002d060701c102030141c0340d40a = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 939507239 1250 939505989 939505997
    0x10e120903150f07050d0605030a0302030a180315180204060b19021906090f0c03081e0c07210804081c1106040b0703020403060507020a0c0609030f060b04090b0103030f 74
    0x100b044942040b6044058400d4082461480c1c04605000e001c0c5004142c00300c0c05d95400b10700c10750b44500007400d04071026800c1c1c0150b0000200e20655590204a00c010b0403586100b12040f42d04540740c15008401241107090001d50368402e614161038803200c1102c415030300030003d106031a112800c1c444245c1000242c154460110340312030890500114841500b10304031280c421a88199868050140c02c5000c401c4d5089050f0141040225203070300100c80185010340300c0c036551202102e0041c0c0407605410f03007001034200103124a0301100c0000c81d41e401210a40556003986c2c0c10111401c49049881c1c0400800f03010300010300103941080030a02001c1000820050991307610007050075160401c454103040b02a4122200090000d000c2c02c50040d0040c6641c5001810f103134503590303240d0443d030060f11000007503805052090204540320b2088005064545482220f6600d1999004c1003104003410040040d910ac0902d555561903603801242003640000100e00c50703581d2401d014041c00e4805030244009 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 939508489 1250 939507239 939507253
    0xd030e01050105011d040f090f030f021209180c1605010e060a060e0103060c0201020f0408011506020f0d0320030f041401020304030c03110c0a1706010f26010e120903 73
    0x10398011031098001442500c0040c0702c080c0a45e00f000007e00b8490281e550040d40d800441e00810848000c10303110911079220065992a80f4401a16021801307540e282511002c002011894540d801da410ba250002c862503c150380303440704001e249004540f07168900c100081c100000b80401500314007944583c14060b100240c130340000200940d1160f0140010040b1800010030000b81194810f0120800c03603c001400d10f28001c888030099403050740940c4035a9156010800c45030701c50b08119004003040e00050458203940303003a8544036445098850145a603078804440d0154a8120411000110422031603492405658070b810b4400b0a0310701307482c49241c462030188850300c14401c03280110303050389800403c900305950032101c500071440482050301607500c0744296a103803000d460028084032a4628090380445811a14088050b4096480701e0a8484100101000c0400c110840c0d400501c00e0002090b00000507405488042403500707403885003059182e04071032168003600149004405668030 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 939509739 1250 939508489 939508499
    0xf06050a0b0f030703060f15031b1d0d02030706030e19051903030209030a0302100b0f09180a05030307020a0303180201120b04060e0f040b07020607020304180e0d030e010501 76
    0x680c1032405a461003000802505241c0c00310a0003555018000c2e150104203e5200c20300c0398100000c0c0d070b00100084002c541024102e0741c05008840340d09007200700e40741c05040300d810010300b14000c100d8000d049075420803803181591039110010711600d401408664505540300c0004004000c0b60b001c0000c0360056200783c1a44054000b055208990844c0092500307405204010743d910390801401c805046c0d0802c4981c22548051020001c028000c0d000f4126510380c407183c06003524000d00c0414410510440001c17404e40c0c480e0006a04541d46912402d0301ba1540322000c0c4c41c1c11102c41c40035100d840080b04100c0c2d01e50733000421641c002c1c420f80d0305000b8803410342110743c1017009501c0001c1c00300d6515801103000c1c42040c0c0c4012010303c001000071511175907405982c00014810342e00c802001300710600b00001d0145030510f158000c4260700c005c00040c40d00300300c0252203010f18041c5002100400310882d00c5148641c101005860b5801e05484064a0807a00500240b40849406049500704000020 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 939510989 1250 939509739 939509749
    0x30705150c070f080d0b040c020f06060a0e180c060c0705100c0803160e1314060a030b012304060b0903391504030c031a0c0f090a180f0605 61
    0x94180c0d4000c410f001c1c00c02d41ea81c3c5454182e00a460110f40c0ca03982e8106c1c01605541e03901a41c0d903800d80355009010791043c000d50003420480c1c01441140a04c4080c41c2c1017103003034091040164800c082007414240b202e1028519400c0020030318045910440100b04044242030200b41c503012140c08940d00032580809050580b500030309540c2c00340c07400a05100045801c100d0112103e4510310915128a1181c4060001804004030000701c42c0640c2d51407100c1400c140d040c0701e02c5070300004202d0305040b07464a183d480d00011001401021510260b4806441d210200c0d000200000100100705116098030340e42000036a40100c40342c148a80b080c100b020b42c0300304101e40300c400010f100c50203584020380d44140300003071503c400541d240c112403030030404440c1e1510303500500301451046d81c00355034140c907600707002c0c0c090f520300c40c50f11642d003103203406008440d90041c040320300b20111440c4080c1c9848000c1b00050a105046d40a030011101c4042004203d217a107038001c0407006511182084201d8682013400 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 939512239 1250 939510989 939510997
    0x20a030605600604090614030a0503032d0f070806011d010e012c0307090b0a090504050307141e0a02090106050c0f0d030b0a0618170708030705150c 65
    0x1150001030b5004548400c080356500401002d060401a404440c40502003070565219a00ca8005159504802c2c401100b440c0c881c403c040600724018010842c00e515021780700c1c44003510300041e003960440441c0100c0121480c1d9103200c400c006203690302d4503100a165100d043e080300e00600190803040024840d42c000d8690380c070181080803402050120410040d10b543c1080c1c10503505000007e9000f0510804503101601d010081d2804070410304c110609161070161141c0008204d0b40c2010140546501e8a640841c21142e98040100e060741751801c0090031031060403006082c1c840621082d603030f060000190450701c003100300380d2a441000c044107815220760a001002350301c04001401085002e2041d03000c0d01200d0b05040980300104050004249041044448500820340b5581102c042e85441040400288214140f03050f0f00d440800307030680000c01c14010844042e4114181c1c01200004200c0400039011a40480c0d64400350350070025075031840e01c1d0091140584d00800a081c00b50b10b10292 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 939513489 1250 939512239 939512341
    0x6030326100603050612031303050d051809040c0e07080718050105070b060f120f0111030106020303190f02040e15121c0201091a1005041a0d020a030605 67
    0x3081a50a124045000e0540a000c1c5e5902000b94180301c10700e948180010001102501036000ba041d00e10b00d00a410404a15203440074008144042c0c29014900e140300209170504441145442e40c032807a1425203001d094014000d003220740f6041041d440d03040b40c540b070701541c0b6544451605030031080c0348506449150103500e000500520090001400c0200000d4020300018000782c4481038007000f180744090041c010802070b038016524120465000c0c41514040458008003030f16641c14034501a6992001602c9880c0c1001d04084140920b00039a000c0b00c0002c114071000e541d607036654800c3e9038499a050b20000c0c245060581b01554520303200d10128920031031080075102002656002c03e030015070b000c100340299503c80201c00009144102200080f205095018075a41012089001440040c0d04411702503854044500c15040e1501c000c060508030454036821160a280b022072003e040c030ba4001810303d4100000d110440400d22215035400441c401d1b0903181d4000742c00d4100c5510703911106 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 939514739 1250 939513489 939513511
    0x60d061503051510120e0105090d080903031509040611031003020406090203040209040b0a15060309031e0e061c0507031d070e0c070206091008090705030f030d0510080106030326 78
    0x400c80c03910700484040c4081141c0c4c81002460006c0801400e0035101e0888542c005a00080d601543c103517045040c40742c010b000c40000310304601d4402410000e2050800507980302e81d550310001010424180c014040c4c140c40b134014240c4a080107080020081000d0004901c514200070340440c01d58914801e0300d10454001f01011100e8485468185403560090480c1132007584034040b008040000c400f4034801001aa03800003a03404007410018111001d04520000c0410040300c541d40980c0d01ca15007030b02c811011500c15980e5240100e108828110314400c0c1c400c00c9003010200090b064155109801920203080900304040341140c0207511010b0b680500c407030180681d4040b5007070504110142c00554406404146001c2004002424180c08042c003400040d016808000ca402ca06104e034100404056004158456480812548074040c2607400d210701270f40c4100281001c9840c00d9600020720088000b0003060b0f84905004199881c0140800212450035100c040c0f00703400c100c1c60510401c05481 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 939515989 1250 939514739 939514759
    0x150415320f0a0803030103121139041b140309070303120209090423011103130c030b040305181005180406051c11121506060d0615030515 60
    0x80008040c0e0381841c03590806103580003c41e0001003040258041c500624020300d00d9181d004005000000c504109040c94100001c8805100b0f8210000054400303060442920070806020000358210401c0e0b4859006003488101302400030300c101060482c03441c640d00d1907004007000c2810b0510f44410380300d0010325400b04004101282c411030705030001442c000b0f40507151220010014406076420348013510b042121244c0c80080300c884090140b81030404000034440b004005052448600000382150b41000482c440c24003003016444803030001e503030f01c101c401c0750604050400030310741c0d089078203140a0740701c041c0314400c2586042065410703440c81c0c90f9641441d10a61260181e0030200b04e82030580c1160710358001007031954940503103c1034803030f4050159044200728100011303004400f0414134080c4096641c4801c2030180420074086524000e06030813442d031181e41c08140180304040440c846c6e2840c10001003604182d440b4040c071422010b5a00744019281d0f0020502e010201e200c00d958403511b501 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 939517239 1250 939515989 939516089
    0x330c090e010b13031406101406090d1505040b100e040f020d03031d0f12070c050d1401020d0b031b0109090b0112020406031b14030106030203150415 65
    0x20050010050005008450f16a01d0750750802810941580c114641c201c842045034112440041500070610000d400b030000e8046004070b43c1034864180b2260151031101d100c5020b000c50300346e0b841c0344480503a80c00c00003403404d41000e108106041e10480d10500d0036a10000d515012600d80d6030081d034024256890420056081090441c0c00e4a800c0b4103060321000200e51035050f0340c11440345400d40780043e1069134165402c0b241810a090301105440d801400210082006034072000c0954005a82410700d43d40c11381003454039000e0001d074440b01036000140e0502d154050750002c0c018240300345c04407070b14180400d51891820340311003120b5002030001070007048840a150010441c00006040465a41c8400301c078100c141d92003900808003080d12350751110218900c403450320100740a2032919011080b103050303a0b280540300c18800c032810560040301003005981c01c05021030511000810400c45031084501900340e24220348505000d4803250607801c2c00c041445030004000060000c038094000c5030324 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 939518489 1250 939517239 939517259
    0x609090921080103150203150909150c090a06020613060e100f0b12061302060a1803060e060c0f0403080706111809060607210e030d09050910051804330c090e01 70
    0x4004401510403002100c0000cbc40b0000018014a00b05403515070700d0b02c2003000e203d4040141d0f03200c8030456000008021107208003c1400b03002607802900407904689a01d032880c076004000d000d440040d49401880c10f071030140f66111411501040e02c4021303481700510303c15919050100c481c88659150040f01c04014684140105034542843c180740c0412456143c03012200550394004031000340d507902c5254012070040010075030140803911840c5c030740700440202d00d040303016030700c001401d02d032021901e5801c05c4910b03045460100c41d920400b41d00e40d0003200e05030900c25106016113028407006e502169135400c2201c12940e00310f400c41e810403560500507034030a541a103107085850422000b00c13041c1581350b905000504000401e562480072040c01c120030421501e02c09400202c40180203903042115883e05200d048841c160000e40c07110540e01e505240220288410011064402207140340d03581680d1800003024049044034100528025103a05603904003a50243d00094800500100041004 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 939519739 1250 939518489 939518491
    0x8040b07120e0a080705330907170c0405013501020912060a1803080114010e040c170604050402090408070f2907080106090909210801031502031509 65
    0xc8000d00060b440c030040c04007420040d8144007242c0d442e4002030031009000d410403560045891070b01c0c0c4121200392400c0b00c0500c006680c5000c6455299410000d642c25800703000c504001d024003000342e500c1f140c02a5501e0f464086c6410542e200e540ba2500100b9001c0e48504010441c20449000c040d040a10711000b6440d925a501d40b28040c0d90200599411a106c00c80c200c6031031100c2c44020400c0e810510901c4068035007284100e50601c045110040100341d0209445045805000e15580c81c5418030340101ca99920914006403c5410041880e20065100003c1100d280001342c01c2c804030b4030f8540070041582c4059402a510451032800700e000b090003100180401407060402300301140072940c0340c40c10f450385560114100e441c0081000565442d4494480c1d100342070307107000f0140f581080b80160405040780180020244d0342e00481d0304108514510280c80082c07544103c0350b0b40c100c038000400f130350002d01080b02c840d5040403c0d610240d00c14000e903406240b003c805e138007074070102c40c0c144100444 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 939520989 1250 939519739 939519767
    0xb1f030c1502060c09131e051902090105070305090d0c080706090609050f040e1e0c0405010902120711030d0207060509070b041d130602071a15030c270106030b030106050108040b07 79
    0x282e00c03800810906441f03500301480211000300400c240c58448a5600c01c8451030614100701c500400094100c0d03a800b104640013030350306080c000d490b039076140045501800300203001450050005004030b0440000940401208c1c45592a202415107610040342c0a054502c03800743c1004c4011044086841e0036001ba8808454400440b40321540d484484040001030321a4007500350402044203649007004d01400740580422a070039840c0502103003101c543c03800f00604507400c100001c90858401c107404d1040f240c00106442041d501e8072070a0070554024107040c3c4d58418203224400e000224090707120b0640b000c45003074010b030000c000e1511301e4104454400074081e460302070641c05000c000500300d1000e8682180a038001c104442d0b08036480000f005005444004540ad080d001c1d00c507a542c0010300381e2038111007030301c0c500d1955824010001d002c039410002c03243d41407441000840c0c010750543c0403982d02e050840c020702c1225500c200664110400352005055003000d14000341d003240c041c02520000300 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 939522239 1250 939520989 939520991
    0x60e030c0303011403010b220b06160305030a0509060907030b070203130303080a0b0105180111011b020a11270402310b030303070203070b1f030c1502060c0913 70
    0x10494284103401d42e48244c000180d544c800c0708041e9020f0a09220300e002880703080d100451084e0b00008541d0354490340d2840082c60b6500c4100760600c0d40c9425059030b468019503100861490101d20b0068080d40085624489141ca41070004100d19400031b009c60161900700081c0420a003561103a517070040c8018030003c1584410040384030660007074081da100030741c00b80e518246035041c07013100b0b1015107032008015810003c1c240700c4003400c065080c85059404109007480c4660303425070400d1030b000d0f0070102d01020740e029019501d142000d40100e030102403644a820744800c1e0100300c50401010f164600004540b04400540118801c50b881c40c600c0d411900043c1505103504400301100c107050300740c54208000550303085101c40d5040c0c0c1c40c001c610072001c049000d03600307500d01020000e680740111080540460300700400300c0d0b10210310100d20001c0101601c00084000e4a81c1803c50740c44016100e110f0000040340039901c145440410b19a0244000b801d29510305282c507004c000c65140e40501d824411 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 939523489 1250 939522239 939522247
    0x120209070e180103050f010b0303040902070c0e01031b09021612050d0504080927060103180507061e0206040209072001050906040311030f0412230c040c020712060e03 73
    0x40da0790404a03550035901180c0102c1958103515280c1c1c1050f290400c2c80c44240c2c1040781c6448940da01105032030584482c04001601c82e4850304207000b14804503401200b00000480000c41032059140048008090984004070b21940c2c5140000c124819002c010700c200740001c0d840c9000414505c2c1e0025020014034081303041c000103412050441d1001d81e4100c0340715200041a42e00f509007032842c003540d43c1d0443c0407015071860556a122608000610f114105030362a008900e09640c0c0b0081c054995400030112070000341c403a2005080184503400b03481c00c0003c070115a819051000440503c200d0b4090809803450b120a0742c19505108c200000e001d4014200b400e450303100800348107240c07007148010010100c1d4206420090002510302c1c4200c500ba4104201d403000145503a403c61381221800c80c0c5104258040d030030015010980d0303890300341601100c1440c0400080c0009421503652004903010404110340003403d0780c1c2d0341540e200780000c0d400d24160420220f44142d00480d100040f01d801e0741e1074 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 939524739 1250 939523489 939523517
    0xc08091201050f0a050c16060e010204031709010e0a03200102011b030912020d0206010b0a050415120501090c1d060408070303050d0f0c052703060118050a0612020907 73
    0xa481040b1907003007030f00001c20204050000e00340650343d0000702040e449031801c0480102c052402c51f41000c003505543e16920b050445035000d504541c000d640051000b441110816140702d21a40074030036070750010b21090344a0383d2600e485840f5004482c1d00c4000e81c80f2403540302600f03d40007903a04601c141555a1002d485a00f450483c00d0039030385001d29034000640500a00d4012900c0c1c40003402e2008662102300030802c0d054001441074156a58455050b44444080404403864812500004c0000d0006c01407210341c180c005032801c0707504002100600441ea01c0e06800400c5070002072040c2c0000780500c3c00c004011100070f521141084020705018a80340c0c46000141c500324065104074005040040c0c0d0070800380d403074480e0f40c1d41101e40e11014050151402d400078114003d4680b1105564490b54504a50303001c01071099000c401c02505685071580d41704981024004402104050310303007481d00080d041c0700c0b41e01c5410306450100d01c42040000054003808000310006106509000181c0f895401c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 939525989 1250 939524739 939524741
    0x30a020405090a020a0e220516060e030c01020c0a090f0b062d031509060118080319020c0901060c05100603060c111908031b07060c02120a0c08091201 66
    0x7204200000041410754240d1051207500280c40e07200b021075206e003500340085000e1140c00700901d003c4503540082d00c48018104507080400c0d500844200750815140040d0060b0410801400440c045041c0e03080000b500006a0300c0f441074071070450344440a20b60500502c04941c1c07108808119000c00007849011200204800744d2010340040c0f00303139141e4078003a6684038000c8980389044082140072811420880341003031150800c002000d2140d01140001065079200341181a001103145020900700b594440c0901d840348c2c02007415100c07420000ba05a50440d000146a071b5503000050015645a0f00e00201151040005801210f480c0641446a442951a4010000518081e120004d02c9409010b00648101c801d58080401d50f0006c4811581e140ea022114400d09038004040c0d0b03681e591417800505080070b90302311260070941c1c0881d0175401c1c083c450b801820210481c0d000c44060b41540300c82c03002d50340100f20007000042d0304c06450000040c5282c01a107200303100a01500403d411144100b4 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 939527239 1250 939525989 939525991
    0x2150c0115030b0a051f0905151309020f0111030d020c070b0f040f0906030308150123190503090307081e0d090b0609010503030a030e0f0d0f121a010c02030a020405 72
    0x743c3c001080c00140015802c0300d110f003581040702200007201c0340c0d1203403503881ea020b0140d102e418a195511400500d0702c0021045600114130020203402e00e001400c12854001c2c0302c8850164040e801e01200656154050400c02d14001110f800035410701d0025601e00b40a58006450f80081c0d000b03000c40040c01c0b5131f14102602c403c020100c4e5481d150740c14612086080c01e00390f1310114025003010000c101107908030100d180c001556000403101000e09a0050364042d022440c0720749a0a144240c0d408070749020001780c03809000042903040c41d508030f503004440500040e60410400d170020066840010001c070010900840d10b054002000d54400301da0340e21503008800d0b002c89180c0c50f42000740c204060268611b502c004c040710580b0f003075410040070075980e000e94090141403580d00c9010020100f8208040b03520420b001003296140c0444180040c4540740196a4002180610300514024002c0f0b0044c1c500071100d142c2c00042c21061240112402c0600ca002642c050003214038500140c1c68500543d = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 939528489 1250 939527239 939527243
    0x3042a1406090d1203152d050a06090e0a0e071215060608091c0905060c0709020a0c031b03020a020d1a40080f1c050f0c0702150c011503 60
    0x2503113082d100b40f400307070603202400c0b1803d0f08001c180c1d07024004035024000c0005220074220125803195000c110700381d8044195013101d540441c400c0701c0020103950181c000000d4440039807101c0025280d102c0120306071101d41c140c0f441190003040c818440b0048941224088034051003000c0c8a510b1401c1c4050220b5440790030a80c0054020005c00004407410088050703c1c00c4180140540041071000c0204181500d0098611800c000a0741005c20f100400051015081e00c00085650b500d141d00007a2152902110071008520801c6050355100d1005540d050001e405401900481c3c049600f000110500b0450480b02d03480381c000880141051903038800e100320803014842014080714400d10486003130030034101910340302681d02c17013003e06a15441140b144e81c0c80394000d51100074214400c055406801c1039400200e45000c200e044094a0303030441c5004010240308a0501e45580d0245a01e51140b6a0040d403c0412442c510306114440d80007800e0500000d00005200ea00c00f421a41441300303d5401 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 939529739 1250 939528489 939528503
    0xa0b1e04051509030c0705060a0e04051005011e05030705030c040e070903231c030b1008040c0506180d0c08030c0f010c05091e030a08040b03042a1406090d 68
    0x82c4455040d06402c09908040032100940c00c205024103910f65800c0c05001d1140101e201240580b0580e024000c41d582c0400020010f0042d46042d8054508106a92141c0b0303001821562035481d124040d80c4a840300644243d44103490740e517494000b61140c1e1300160450b41100d07010030001802480c2d80981c02d004400035680d1400350b0b840c5050a007404045d0b14580503450b207200c15409110b42c1b00044d03c3d407500c00c0e038000743e120142c003001d0142c0050013041825070704000e14020030091964400b103101c1c4514400c0c111946102d45450602a0900482c04141d108401c11058a00700b8a00910404a41d910070f04281c000a521460301d54210b401c003000410441c1d1056003503482454003030003059031031503e0f17141c05410400c903140090740700c130018101e2070358608040314400f80780d803001e101c80c5c5800c0da0000e92003507a035552502464110341c400c070742c1519039100d031400820808043d1301c00010000e5607081214071640c101000c0b0440b0719001c1407650352020040060500e6610340d2a125503c450180784 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 939530989 1250 939529739 939529753
    0xf060f1b050f06071e0806030703050706020a060608010203010f12331b0203032403030304031205090111030a0f2003220302030315010302093f0a0b1e0405 68
    0x101602c1c10f000600301005100800140051000341d4003040000290b00c2e1521064076118800031070f003090b0780c90700040c0040c09103002c04180523400143e000c01d95440b80f84200001661a004c4900300e0200303008025030074501c200100488034040704480b141e2030054514940002815204208407444960400b004900c000c1e20646102e04a00c02e0095003041445415035410b45007000035203911004101c1c4024148120f023111034404006407040191102804503030381c0b400c15003006404445d0141042c1c90031402d18000900281c0103000b20103041c00400c00240c199103800c1001c401402d20350017041050380e40c4a81d42d00440b10090000484285038076859a603c0c101454152540c0205011203001c129400d0a0000065800400c895010107501245030328000f038117004901a11503040055440031503201500244007980c6001c064100c0850310650010390f42c840020395811650340702d410030f500014080300118142c42c61480d40300c4210908042c2c0c0012600384840c0c156000e44095505a20400f = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 939532239 1250 939530989 939531013
    0x22505120309060d0513050f0313090c0c03031d120322080a1b0f0506070306120807020423011202011d0f010f180801020d0501050a0f060f1b05 63
    0x510a803461800c40039514000901d404103005224413203688502035992400540c0050804003500311099004064548000b680c940d01507803038002c12031042281d601c44000003142c000500c0341550f0030b10241c035400d0407100c540d10160005d1a060720b4803254072111302000c424040040c48021403030404a1042da4a90401c810598030104845128040403408807000344007048030001075a07403080b0586414000150300c1c6c400c0e01407141803448018454040310714103504104010500901ca0b010569040006641e9105100d40348070700c0a0010701920070800c00903000d8100354108045542c000b00046003601200c0f903400008007401d9201401d082c10603594001150782c000a10301c02c0c2c2603090110380d00c12005400080f8250680c00c03400d07046c41108041c6401580c00b0b42d05104020010307400d4580311541d6042d446c0c0c041e50200184500c00d5250400103d082c1c9424001c0d072080d10360041c0314a5580307007810019107410700d140c040601804450305850b0540204018400c2440e03115001030480d40b40d8075 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 939533489 1250 939532239 939532249
    0x2104060b040c05122701090b060a1503200a092d0b07030e1e0103110c07030803101a0c0607090302150d1b0f11030403110907022505 58
    0x4980252003070741403284540800d03030b000050359061816146001581d45820000784051944c0000003d03142030700d040700104481c0107501c15840c007400381e04152340c955601001c00c40004524001c080711502011114038107580700364070051315030104d0301400a141900c60030040c0c0d160404403044001481b0020180152070494010340e00d05000180041d10002088c070031492001c82c1c80c0510001300001203013403014503205103800401da44d0041c100c254614201c3d41107000390300482e040c2078046410203840900303c44450003190401d003045d80203415894215a6500c0c01c9030b0014103481aa0717030140c64046050030400d20441543d072203111303040c0e65030110310035214200700004200d24148442040c0400c0540c60b02000390002003003410307040382d640140340244001007511580107200c062101c081605015001500405010f403142c0700d03500c6006243c241e4981d644258003006100c40786a040664680c2026050160485060300503140008803d44078032130400004602c80c65081d217039040420040c200 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 939534739 1250 939533489 939533501
    0x9010b071b05090a0c1b030816050408030304120207031a0a1113030b0c070b0a0c11060c090405040c03020d0c060e04020711090406090f0b24031e03210406 68
    0x500d455062400300000c107500340080058000c2905e0308a0740d5820341c45030b00442204107944005404107000d034200248a2001112080d4002c101c032181d1608041c010000c3c0d80840e129400207500d55602e80e0798140340541850f241c4c00c10351081140210008900012404030a503180305103140740c0c81c1400c220410b03038407141103090804104010450908191030310040540c0d4000100380c00d9512511018000d9201c0c416015001450000900240c24003c0c4c200a01c0010030303903180280d40c21042d8078541c48600c00d55401100e41410090041241005d8004c3d80d4800d000d0702000e524070b65260041a03030ba05003000d0441e003180310010107201e07a68200e0400c001200060700c003142810000e42d240c4e019540341a110910600c0f03480e000070104107083e00040502c075800360509259402601e40280d80144c00d88500c80003442400986010a0569903100c4e09000002c00400103410160190740508a07107403229512408100005010040d0b4010380b40c00d00108444034a10a2905040c0b01f012101 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 939535989 1250 939534739 939534773
    0x1222140414090a0f170c0c041b0c060506040f02120a06240327140c15120603010f05150a120b010b1b0115180501180213030209010b07 59
    0xa00c80c02d0050003400014994021544469011080e03401410300360407256040c81001d0000344005621060340c41c01045181081005a0782444046003c09030880e45846080220000039001750150006c695560003480d045a0098400100e8010007074140060740e0101083e000ba04018105001c800384840c481c1c00000c00e40848100c489100d41c808040d01e00c02d40d4100101019125a642a10b400380c8041442041c0d101e54103654501c801880e00f100011003c150154160003450300b8000c00b42000841004000000c1c0d49451602c0440c01c018800040041c10b07145d015076981c03408202e001583c1c40f881e07004062040c01690180b103004204541a207203508500c02000d070a807c2040002c4880320340f1415154005c0c2c04545901c1000d1510240890841c0b410b001d941c24420001403030101403005800340d07070325a440c0c01c0408400803000781c151070080c450205586048018110512580d1b40900251a4504520003d0b16038a40020340081002e801c549400318000a0010801400300400b04841e1 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 939537239 1250 939535989 939536021
    0x7030c0230070311010f09051801080f070803040611010b04090804080c0111070e06033421170f07122a02010503040309080d0315051212221404 63
    0x2a08554070413480d4180d6140f1241401060031b1030141c400c0c040c08040c0080c000250944800c0e100c0c203903507005284000e100721911401481181c1075100408150503054400711002103290516054080742c0684210788202029540d600d142f5169039035038082c55808600914400746c40e2030400c0000c5051002075030500b814000000201d03482030134003103100341c111109610034078015580d05000c40d0a00c0200060034000d00305a140e034828000d101092040550014040f82c3c06494a807c2d00d140103907007005480e00300044000040c070010311000700003101d090106803840c2c100000000c1000c03440e0482c4004039901c112000c0d50b2880254407041c54085030b5445000224085503102400c1d04803503a4440290400400000040506000c0c060081c0180007000c1143c403a40c0c1c141c14000e00030800e0b0810035601c034540c21b400041c1450050f580c190a80300840140c81c01d01400d000100380d580c491040d00c0b00007034400d548040c41d05181201e410003801110428020103c04408200c125685440040c01c50 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 939538489 1250 939537239 939537253
    0x90109120201180605070c021c060b09061e030102041a031e06090f04020f0904060504050f0d0512100f03080715150905071701080c0306090102180607030c0230 70
    0x2408242500020f01d0f412010005098548200485603c00c8000e0b020f0340000c824060f400d84550040a0100c4440c007802003004251400720070014a403000f52005507008130700d000740c0c03115040800026442c46030001d00052030b02e5600c0d6450800d000c0149031b030135070302c1201004001c16001102514511070300560349086c01803400e0400a4000440903120f4411403c60600040454680c130081c8510041c000f02009843d10741460503101400d0100c0b81245d42e801181501104000c0001d0b01300c0703d00e041038a4403030902540c0c412040c2c80a40c0104594140c00030110006205040700c007500d005540a00c12080d41e03101c0e03600b040d190850005000c1610399203030076407a2011404148030101610301003000031801703440c1d403102182d5961106040303164207941c10000050140d00041c000000c1030042c0d080c0c82440e82d811800900303e000b029103c060151407051844c04c00e00e403940091100b41c5c42401c082c000c0010580108052410b42c09007111416020045814180519682900d41212440c010a41 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 939539739 1250 939538489 939538511
    0x706140402060f070825061a0a170a02060409020901080c090108011a090a170d05030f06060c0a15091104021804020d0204051c060b2707030e06090109120201 69
    0x4148104490000b843c40080b40c82c40c1005408800c5030a02c000014140790701c0903000d641c140c3c440080c86000c0b83c0d140d281800050251503034002c00c5c1d0300c9580050141a40350300c1d054292500c402543d8460005010f50341c1e101c00144d0300c0301d014002030421b0120050322003144600150518102809030654100103000758500c0d0303a407080c28181501c0b000782100054040c0591802400e024108201d50f02c20402d0314045061928100310000d80f0002e0f0040307441600561005903602d1100380c5248081c03004082c0010b40c24104200241103148503039080704c0cde250586440b030001620350130300450700c881e40311040407040c000d00240f00611202c080b80c04510301895a955071409030b03480c40e08a4011500030078428244400390741070714010f100140410041411240c04001f002c0c052040407103105c0d00d000007001c114207000751654090700201c8890b2491510054008684c844000c098004050300c07400541c2600005202031800b443d00c1400104415409160504d98100710060100c00c580c500490319007 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 939540989 1250 939539739 939539749
    0x250c021c050120180a0b0c010902132007140d020f0c040621290a0f061d06040621020a090516140c0a0c14220e010b0a0b0706140402 58
    0x29540215610200d603490801010070805d03182d0346c0c00b400080c40c01007603111504006411061600788201e420004a0f02000310040c01c8a412a40080b81c055a85000f80001d640d0f240050400c0e6010302c440b90089401c10807901e14008860104030010f0300b100d401c1d102c101a040240220132041101e0511241d41440c81d50102000788641c101024184480c2d50303001c2c095041c0c6501006040300c00010304d01c104c0b91742c80891418040c0d903805890707842d200d8414841a503c2c4074034030a82d940b078204030250080001c440c000c101c0300076001952090303480300000707400903000f0050810800c03034890684c0c0e40c100a004211819000354455079142d4140000c11181c00350103a41000000000d04280c0d21444041492031814003032141094124130400100d6001c1c00f045072010b0f412142c4000380c0035074888a980501c0700c0440c3c20050034840a8409142105000c40d541018422030b5000b400028113210000015104403116031201c80c503048001181c40034020b107402029217034080c081150000b810aa80881d03 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 939542239 1250 939540989 939540997
    0x30a180f0b24190e150a15170a022718070207061b06020c0c0a080703170309010e01051501020d0315120c0909031d010206250c021c050120 61
    0x1485049066042e80c022043d112091019140c4542103950600d0301c00002664800f45005852051104400010304103455016001c40d1003e01d940f08a03100c001c241100100350340151000881603001e00c4090801c840304101d20700786402810848400001c0c02e010711989904a800c0c103180c40a15000b00031955030002444000c643d41071a2881c413100c200741d00e9225030002c01230000c00b41400003a40f101c00c060005000d5210000c100c819220244c0c1e1054415030f20409448000c00e00340e900400000529291800b556101140d24004a8125941c2681038210f500484070354a040c80042030121440d6410090303600f03014074509003040340c83c902001000b480d035444e203c0c0d003820f040d045a909003084404640324000309401e8106100c0c94031a03180c041e24041080c802c03202440c40100384596250300c0080c2040c055404030003100030858003034025400352152200b440d014000244003510068480303003070041d00107040380619003221240345400c500f07458840303845174050010742c0c110341d41e802c15600460f = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 939543489 1250 939542239 939542311
    0xb0c0705060309010e010614030f07030c0e0604180302160b040e010e0705070b07050405090c18010c1b09020c06010b0309060f040201021501060f08160c0206030a180f0b 74
    0x103684030b03500c3d486881e026264154804a01d0350910302d0024540400c4112404040c03c21016100001d0320000b1983c0d44410380d21000d0a811b807104010811154215400c940001c405000861107a8080e4000010303a0540d00c0c04400583c01114910041c40090003810041c0213134400e0145407616103145a5030034241030294440601151340032425070b900560490b02407991090000ca240d14184201604035006486858090020340d4001050a05d0304c0044501c3c0c04006500b541003681c9190044445141107401187d400d01c0f13060302ca490b12100e0242001c001d10101001690b58016034182c14200101a800a2466001803003803000f13150000c2001039000286200c14034265032a400100c1c40c05040102c51000c0c020310100200d94154003845202c1406d0341c58483d20229192501051201081d80e00010b0008070340740c000c1001071401390002c1d600442502d901203903000c0a20000b06508142010407540c80f007118541c2810000d021280c00c0c1e004100303403c1c40f804100700030149540601c1c1d0000f8 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 939544739 1250 939543489 939543499
    0x50303040612021e1e03060d0b07030e07091e0b0906060d020405041805010510030210030c230405030f03030f01090b030f0a150614032d030a0e0a0b0c0705 68
    0x20b488158a07503041c1e404401061903c0c1c03001001d1030300c59102c00d84c040420000d254501c01d110010035007915007140d0280c180600000e03100c0c02c039501c131944a400701526a808264550304081e42c030070f904102c2400945855000020100079041e03030140340030800c0204c026518100405441390340d840074801940400f0a9809079a1045d0703203030082c0002d01c03030703138020a42c8280383c83380d40c0941c208004c40100019124074002c1000d0340380d9003008100c002441c40001c0d030040b02510910490791290b00103901c415843d0503c40d1300c11903082c0351030880c588a8030454034684000b203820001860204003201043e800c503030107185541132050211407081014044d40311480c2c0c4032000f401030794800300403500d4030710800d40680c4c021200030300e17020ba648000000780809450601201207140074a43c00500c52000004000b0581c80001d44105800c032920243d40e038200382426090703070807000b1050004104a91655446801d0201c0c0c500400c0b4200b0a20740045400100612590245000c0083d408080da0000c0310 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 939545989 1250 939544739 939544757
    0x2105070e010305070b2703030909180d0914190b030c090f18150402070f0b1f0f090b0a030510050a1109010203030609070c14030c0118020639060a06050f130c0e06030f06010201150503030406 83
    0x13f83c407800e095035006e00c010582c000200b207000d034200400380210000031150807c05840440400800d240c58a001a43c800d521001103400110407000844459001a0016007018260b4031054518404d0a00503540c0d15880c2042008440c0c911114101000760111700c99601800c15144004101c802d0055028007681c402c0071050366603c06002c0303402075600800721400c4a407015015000742c1400c4c0c80b00420a8100b03080d603200c422504003521103420040e4004c5046035a01410401101809012001800742d401518030210700413401c1001a03080c110000c0da82c840203200031500b100d1000105c05556106a00418011b070740d0302d4210f5600c1c00c0c3c4491088515010391100c0003800740c225002544185400c1018860b000740491407a21410242004100e16955807080c00942542e03400e401d5800b60311010495140c410580c4005900f180c0340c43c0290380071b20b004010030b8559205070b400c02303c081c417141308002082d0b07824010302c80340401407000200e80701d00e040d004c40e581b4001c41c0523000038000009 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 939547239 1250 939545989 939546019
    0x601091d091606020f070504110901080c040b1209061b040306050a0b06190206060303090f0907050f0a052d03012105070e010305070b2703030909180d0914 68
    0xc048070030b1840712202407039010340c0c60101945c0c50254442001480c01074210009003450306200307843c1401c1c3c1480c079282c03030002c1c0e003801180c05d490014403241e00d002092102084d0721100e000079000701d80e0f4081e190345150904001c69850910300525114400c890105941c0726078800c501a01d00301d90b403003440814991502060680030380700c6108841d07004103000c07402074640c810102081c43d010f1195000d071079080c2c0710070043c15260710072000c1540d04140c80100b80c039240e08101002544c030000ba80740c100c1c20701603401452030199000000e010006900800c030791040302c0007400780c0d5400000b0003541c181014091030750f5003d18001440b442d5013160040b00e0000184192507480e01c00d0561150542d5080f0b038980d1010004001c00380010365062082c082c0119040d000d200845130300141200d8038004451030347c00350440e02211024034030f8160105001054036505c82d4925a402110300c0c034101e801c0d5424a030000c80c0703001610300d09681040050300c41080502103c0740c0a29009001380c68482081180e0 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 939548489 1250 939547239 939547243
    0x70509070e0d030801061701080d050f1608030105090901050402030d050310050a090203011d070507080a41070c051c0b07080702060a0912080a180c0e0601091d09 71
    0x41d030550364101030314080000c201075000841c03605843d0261203000f4400300300c012140c5105024029015241d00c0350b071821828a00400140100c84503445400c1d140c100c0702c10858280840c4200c04580410011006000514104001ea6407051019000300040d14150300065515160403441000744040003001c01d0b40d604c402412131010f000060083e048030b13603031960100002d6109200307006004a60b0102a1801c079410640c80c1e009441c01c3e5509400c118207500c521150360700ca0481c18041c0003c80f203a00c1035109007500d0000d220440091a51100b802456120f100144580a04044810f041044000180e03100810300203a903019540200c002000c42d05d000c4103422000400703410745144604022186074000c807801e2064035a50300391880303910381d51041c10035240c500c200286030100811141d178405102c0c044590b48074030064000f041d0840315040c620b145003010007095803600d40b0402c05001c00004520401c1d04940c3c2071820740200d91811075200c1c10f0500100194142c5560310340481c6501500b = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 939549739 1250 939548489 939548507
    0x913052a0c01140f0703050105101119060c020c0609010c14121605070501140f0a0e0406060e030c0a21030c060c081e090316232d07050907 61
    0x449402048003d50400c03081c501510304403503070001d241d443c40000c1c0d002807007401224102c540240c004003c2c3c046200c0156400e074070003103000d0080d10681042c1c10340040344649030141c981c0501c0e0300081d48250844002c0c108074020a416002d000308215000c0144d81c092098411150441861916032448040003400c0903030440e850500c00a0104803070400c45107000352000d001d8412412140c4850f6540010744890390a910782c01c25210050069050f6154143c009041885c40d619104446440c1280010300f204c0f80754000d10b001580300c1028100905082000602000080302c00c901654034080c1d88a40b103a8070300d5030241c034100400103110105801140c22140807640700e141803040710310700440144504011100c07071141d0840d200031b44403000d0311040d10b64040c4890034059803402c2d4160f04d0b0b500000c1c000440c1141c0c0c040c5075680581c0d542508075245403080303a00d074000c0d1400311a400100200c0c0800481280c4a18665028013940d600c00012050101d400a40e001c000580d1a6001a580849 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 939550989 1250 939549739 939549757
    0x72f041a19080d0801061b051905160b03040210030c1704080304020a050402070201020a0201030509160e0106020f031207030b010314270118020d081e0913052a 70
    0x41104500604080d1540740106454540e8102e54410180200c2124121406e11440b008502805244514081c0762840004c04500035003ca6035556100c1d108008003c50040c030a0340d00b500400540100c0840030b2100e1401007100c030403c582181015000514000798205120781410354031210446a1802215240d17810459020411081d26250902e048581d0013150228815082000082a10300c1c00b8404c0e100120740603070003816400b001d580150002c03c40508fc0d07039158440c0c00251030702c102c06021704101800d94126101c2da1940b421502a02d0f01e000c42c121031009400502850708210f1b07680420710790003800c40c900132414a080100580082c13440c08a00c84d0104104800c10040a40010f14a00900002200a50700c00002c04201e800c0b903c43e811194007155043ea1064058075001d800881090300504255190200b80d4413100106c410208441c960000d001c5011481d900d84088039080c14040f49a090006140c00a1041200003001d40e13840b08103003500802c5501003098100b96160f03d0 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 939552239 1250 939550989 939550999
    0x1080c0108010b0a022802130203011d0402061e0714070602030a050f0f121504020910031a040501150908030f03180708060c130504112704050408072f041a 68
    0x44078203040100e6404030106c041e030103a0a076030309120114025100700d078100c4810303114004194100d601e10800f1454081c1099a20150a00402c1c61150510080200403210403e0042c0e03502c4292800449a407468810800c05030481102049203940110489161f043d4902e429941d8049407005140c69004451040d8419040841d070f0320a280c400d01c0440c0d02400c1721955540c4d058903140100401c1e0705c61004440c1d00b04880248020895009400c5010882d00741940800d4210402000c1800c48030700740d020303000d40c07401070902410480d001041c00002e000301901540c64002e0700303814000b4a11000d440030035000060807e644401e8401d00c503100140c404042519000c2c1040030320403589400c10010301c0800f5900400005c1c00380751034404c40100005070f03210b490400301c103041d085400c40c3c00c20184461800694440c520695954403601d4401c0344030f041b2044d2518654204441c04401d075500404441e5100402181c040e1112200e0100c0101d0884003c96040da1681040701c9000214010755001 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 939553489 1250 939552239 939552283
    0x24011a3a050a2a03020c0c1201020415020f0a0b04020303070f030305060102010f0e0c01050a1106040507030b0618061203040b03010e15011d0d020a081b040501080c0108010b0a02 78
    0xa00000d8000a0284a4009040c403c0c100f00000140000007020281080b00c1e002d0324107828000d000ea000340101c000103200f6207050340b90b034102180c181c4215034070b100050b96000905001035003510134011680e105510050014031031020720b455540c03243c0ca4001d080d65608000250440d80c08208483c9602d84c000d82000d03e03448903242c050003424050300c2590255003018900718060855100300c036000007000c0f00078030400016100640d00e681c00f4445c0502040907050081040c0c03607040101c240600d101d2001070070046c0c40c0d81000c20408101422061283c0460400d40401b50342074801c0e2604800e08898085400408005652461085901141e40c078003003c00001008145400903620414002001605d10ad80e01401168144886a80b0180091821542810b541095030340c0741680c501c003034404010240ca130300e4054030749001c203401039890100400200405003014000c050050030f90000400e0504402e00010b4204201400303036000300280412107070034481c0b08021000b481d007580d124000304 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 939554739 1250 939553489 939553597
    0xb0d020d050114010b1215010201020c160609060e1f030b0a0f030b0109050912072f0f04050105101d15030103061b080606070201030b0324011a 63
    0x40c003401000c820382203d100000144c07041803c01101d5611304a550425925942d004544104030801300c589030440d035080c4908a49114100441c000e8400c1801d1000d020500d403d100800c0541036030888800c2103904001d5030340b11303150841a02c072154000d036880384005050441c124006e210000705142d00000015000901003440d05d50b0b0b5090700e0140406103075176038890000b00280c52041e0340300c400d640e20204034103000380e6020000c2e2480070722407850740c1207440d00d9441100308001d0f5400f981c071100f030406407040750a140c0801c451300300071010345042c8030781c0d890000054880d2490044940c00d00041d80700343c0d840c82c042009654401e03040103080e000c10110030705501155030802d000456949250041ea400e031004010309128009078a0f07910300d242c3d540c80e01e0034000e8035041000300700d06041e11061048007550702484860141103580d0424410389003001c040701208041a4040c254075004070000300302d110001411a40300a000400e4445500c110b00f841001c40c403a01c00c800001160038124200c0e03 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 939555989 1250 939554739 939554741
    0x1b020405010f2309040f0c05040507120c0311030a090c08030a08090f03040305060c0a0c05010e0610060507080906071505040503030a0501050103050f0105130f05090706020616120b0d020d0501 84
    0x20b4854443d84200381c0c1d0036810301a50310585110460b42d0007141c40c800100000d0910b40034260f02482050700708a4140c0d1100841c043c0c400c02c2d42c502002c151407005400081c00303d449030451030002c0f4035090003d0001001d103c2c01a100243c100d0048030b841e100c4034014482e0000e400740c01401c9000131207596110070440182811415504044c55001d0351050b20385529002050354281c9070400c1c007900407603c2c0c61081450316800981c84c6810b002c0301040001c0030840a108076000d11a580010700340f145400300403040c003200a9002034051042c14040c2d403003c16034010507602c00d0001a5640d030360319511030901c80c1902d03007205040c6025030700744000c000800c940130000c0d60143c01400428081a601d9000540a40d0030445460f03e02c1c01d40103004200a10741040d03c500070344220600019007a803401440c0c01940e0084601c01400e40c810702c410814645c0c10001c2a0341f2035617111880155203d4100010040380c826014580f116807511110401c7e0341d941c8051040c07040d030040a8040b40c072001d00d0414 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 939557239 1250 939555989 939556019
    0xd150e2518091d0a0c082401091e0e060601120c02060f090a120906140c0a060b04021b15010b0a0507081e07030e0306091f1a0a030318050103020a0504061b02040501 72
    0x51240c0511030f82e07441000c88109480c07108410220710b80401d623080c84149802800b00000c02c0202245cad60f00203415801c901e101d05a800d4165402410351803504000141c12250f40315050083c4500d4809500c0702c0c15804501260816800b940c4120140c48441d501031914403030301400b07002080301c0b948410025810100724000c486075601d40c40715841038840d8004560040318580c0c0c0d0315400400070f10700040c0c10b6600071605044010001410b05c2004114261242d0990400c0f40107030f408101e04000780e08621400c14010401c07408c80758170340f86407035030020068003e24500608115001c10807804612018001c0c42400450550103034a81d500341c1801000b000e10b02541500030302420006c1010400c0c0811a0134150855010b201800c5452a800300001c0c14100756418110916162220080c0d4a90f00c004006500a44c0c038200406555180303102403411503070019041c1841045150b070415046000e903012619103042c8007a1f020504840148000a00c541c02584186044004500d46012202c0b136 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 939558489 1250 939557239 939557249
    0x1505041a0d0e10060503010605010e0d03030e100902090f0610050c030705060a021b060c03130c1d07110f0601050d05030904050103140d0201060b0d150e2518091d0a0c 73
    0x600013180d40310240b501700c81081c0503042c0040c010502c0f045107420701c1103010351000c0c442d00c1d0002c1e403d0195189a420b086c028000101d0342512601e18a05501d42084403c0e0800710318501c4c544241040ba000a0304c3c4049002c10070140034000c01c4a0052140500994051503000800d9900d189013a11424009501c0040042900d8000144c042c0c0161000105284901014201640342d0385a800010088802c40c80044030040f420325804201084c1481403803e00c0c901072100259030341480b60014004964100c030f04440c6038401d440f005032464000455030f0443d10196818419100da80c1000c6003103118007d0365980260070170000004100c840c9a40900f01034040341990541d00c54560101e083c0c078502d11a650aaa10034007460814a0342607010141c0c400c140100c2600e0742d56030f0441d000d85000111030499401a44294001d681a102002401c03107000b10310b41595000383c14040403200710440e009070315400780e0b1400b1a449503102600500c0c5000a040200c07100d410a070324003020810f10500403 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 939559739 1250 939558489 939558491
    0x6050d0f1703040606031a07090e0c0403021e0901080a110105131d04030f0e09220b0c0304050714090a151a0c07060207062304030c120201091505041a0d0e10 69
    0x300482140c0c3e00d440007806003005a60702d140d080c3c68415609510440940004bc048130208400001131ba2000503483d05010b8202e00d1003143c0001804100d0700701c205074004600c036040b00e40786400069594400d00c05084003402c0107511010562103c65006c0025000000c001c00790303881d862503440300c080415110754401d5641d2034205a40981c200d41c43c91008451980058601004c562a811201d401034071106c07840e410000340b5074503503c074014400300545445101401c0041030000303124041c400c040161400321050b80c0402401404140c20141c0100304004003036840d03441010303420f82c1c008500c0c000c080940036842c00c0a01101406600c2e440f0741c121104034070a640c0d001401d50700103e02c0c80119840c5071038480e080e0010003a21641140841c81081007510104808000102c034400100084c0200540c14040c5075070a10014040d0703101604500b40100c02e0488000c100e99210707040324142c40c90301c82c024652400074021050307580188418668082e003402d280751a0100000f4070b400940c440844 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 939560989 1250 939559739 939559763
    0x150302030a1514060d1b05041a04030b04020405181b03070f080a24232a090301021606020c0d0e100f12110a1206050d0f170304060603 59
    0x3028001e0701e02d1038451400118400c800301102e503c0d000025140c1c0e907400c45000304214035002c1d20707031070883c0007980b141006c01e01c0401d0500028150409201c07603100304035020307841c02e401e5480d280c2c141c00c0018802813040783c0fa0740014030740c0f558aa580483d440f0f01001280c03460781c010040b45040e0390400800e079000c3e00c940980040c0e0301d4410101001101c404201030045a0181e0300d4820801e0125400c56650580c7c455204890503054450011030010b4881001d4040c21581c080c1c101d104c0001e0a025a401601841c0214440c2291901c0030400605103031903564288801c00301e8060b01880c0b5691114a00f01c00d011014440190000d000400014040c1c0b211034542c100c1c02c2d15a141c07040b0480703810608003c88041c000340940f1944800508500300078026901d0203d04c4c1090380c20141e000601c05c1d5000c14800080754008644980e40d030640c850a0081e107041c103010840d0b1000101e409841d6140302c642c3c8000344403405050110303500e07002c1c0405a0324039003410010050300440c032003258400c241003 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 939562239 1250 939560989 939561011
    0x102280e030a020d0305070309031707030f02011418070b2101060207031a0a0b19080c12100b04060b130e13020d0308190618152d150302030a 62
    0x100300303200e80b0350b4001c0c0f909100c1e0392192011a0b454100b804201c050011780d0501001180703680c0850341010300c0c1e0710f00081d903450a501d0003d00b41281074810340190380c18050b241600c007160314109640030460300c035802c20401007030826610b802c0b03603039019000e2628000740007000e0a913040f140c1254281141c030516032603640c0d40780480c0d079005c0a00c0f000c2c200d9888034440c03090070410b911849400010f00c18001c41c001248100080300003064100b08501400410010001104140310f9000c550804a5910b010103a80c004450344501144604188095855030a1021507960764813803000342c5481c054980e03c40300100c0009500051038040d103c442c52540c2d000800c2401c40003401d1200c035034094084c1d09a002d07d50b60a032016180540460301d1030700301080e441c44215240c49240c004001050340c108001402440502c02c41d0940106030389105814001405080082d51840d0f02c400301c01071035001111106120501c12040d82e030000503a041c020790240070590b5064020b503014440901c2c04220100e030300 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 939563489 1250 939562239 939562243
    0xf080703021b07051e0d240f050a0f06050a05151204081c0603020a1202010905100c03110f030715020705010c090503152a0f040e100605040b0d0e0102280e03 69
    0x882e40640e0242005c603c0c100000d2100d54044140d10700008000c18400410103080190f45d4001041c8c03400c15903d101b0802418010f01402c10480b011081c02c102440c10305000c5000c1c50450301615008407001000d0340c25030b03040d00341120720190549509010300d042a140c016a1540200ca60301c10483c2c01544410124519200c0e133800c03680d00034402c904807031a002001007012442c80c0d0070f030b0600058034400121034940d03195401070f50303281d6595803440048070f00d800317400c890603a140034445610a8050b42c20a00d000001c481e5442d0b04804030644c2090020108e001920410078014125428000d0002e0040d0b040840c48059580890548000307058251400402d4841121420110080c10380b121100307907074440c1e052044045400840d0300c3c088400d040a0200e0344154031510341103e11004000070320303451481d02c0c00508a41d241c03681c5040e00c0c040c829541030182d1b500460f84d6036039031020f00d40fa8002c00d5049070044014003450b0720007280000080c403048440301c001640071516400700c2200c94030300 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 939564739 1250 939563489 939563539
    0x509010b0a0c0609061503150e03160209040212030c060f0a15090c03200304030e010206040b04060b06070506040c060e03030405090408070c0e0109051b07030f080703021b0705 77
    0x60360b0b031403400d02034154481030054000030900b681c149942d080c00c41341d8941c000f08000b002d140690000e6030480c883c042c2140072a02a5490314046400520020307443c1c40641c850451030361380446114000e61101e0001800d55028a11042003074840003440700300c401408101345124010303042c0152080d594458024042e2010710b400c0e00008032214006120042060f404212070701864a00001c4404442d081c0240b2404140540040c0c00d401000300820554000710b00460001d003031001c3c10440c10565141a0000d1001c2c00050030030752145400300650300c3e448113403010242c02800300c400030305103401d001c0134585541c00380d5000640c61010844440c02c0c00000c65044070005000d03150075070740c0d50700e03001d00700d8000c05001c840000b00401c0001d4050080000203000e885404400112810005c0c01d2030400e820751222015180740038801100421303000344000b0b070400303c0703400c0c01651a03a49500441c000e1141a18400056940e1560b03111131000c00180741098a4060350288c64520340105507980c1805 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 939565989 1250 939564739 939564757
    0x1c0309021003150f080a060b10140915030a050a1d031c06120c0602150103240e0d03150f082a090114040f05060105040b07020d05160509010b 62
    0x2803605000c40d081ca109074403060403451030030078480f5420b480e0501003080f6441948000781990280182c0d0b002e111692081a061030340846d0701c044510b00001024002d009003c08001da46440896070305060b4a80082c90249880308080f016942c0c0b5282d4800c4008200079500c2c081d00915003010b10074050b02411401b500064840011410003902c012100e11208040c0b5844003c01d40382d103000168440007400801c0554410303c00313801c5690400000a14000300c1c0710104410711180c5004001249540e46401004e03040085824406a40481000050711a008400b0308900caa480396003c0c83e681035000a90081105c1c0380d513400c4503960f0201d0b20146c2c9040c0525171050f08104070090711100705140015804483e082e0703401c1940300e00400034103d103400760320071310649402200403000d40c5081c1c42007600e0306803d060200500d0401b000000c11900550240700d121040005500d0300359030750402c00d0b444141c1e015045030781d5031031102d0404018065510416008010080020030400040401c1c0c802c1d0071 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 939567239 1250 939565989 939565999
    0xc0c03020c1309050d0c1b120f0f020a03061a09060901060e1206072102120415141302010305060603073203090c032518060b0c1c030902 60
    0x60356000400000444603034840c42c00700d0f500c030030a400184091245410700b820700d48a0044854040c00e040001c089600c80e52041002c030740c002404098035110301030001c143c1040c12070070042c0c0285801450601c501c04042c0d4040c00c0ba0302c00004100040e04511001180d2041055403e0549424003103040e205540e583c0e817008105005006070380c42104142070321107004000c16110f00c070035800c40d41002e8041c1d4440d030004181070220001051100d194001113540d540c81185880301641903032400c060040d0009240d0502422255590f05054000307800a46108484010b1402c0906581400781d6030641c0890201c3d080030001801d07803600e46c0a8900c51035040d101c40603408450520020009024148141c04091840d00030000d000c40201031032103070031254024158812a5010149041c0c084024584101800b0890f44404282d103500d000480f4070200400c40e070b9a5208008001500c050f80102b45024000f20300d201622200282e802004400311010486c6080e009004600703682e04968065000 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 939568345 1106 939567239 939567253
    0x1d01091d1e0105011707030204082407180603091a01151e09060c0206090301021c050a05130b2e06021c090308070f0c180c0c0302 57
    0x310707000400741c800c558580070000b0140300c010760150003008440c0000c9100103010f0f405640140ad0044251100003042c501000c0b0040501070b1030040398101c100205040900900985020310100c04400e070b401418501c0907405001e102034219442c0306400592519000c0300c0070012301070110050007001e4507846079001415401e04034004648210000e008a4486070480b206d0012240241010038420b400c500006015008205100741c0650000070303070961210385102002c511102244082199455640c07880d4211082101c00b01030781e002070800600441e80c4081000e5011600008902c240300300381411042c0b5080c0e4500d84000c14030074500620040d5014001c1d2038005d00c4c03203c1074030b411001d545001042c10919100141881c24002220350510121010203070b05103400c071640c05012a40c5580c00301241d0102440b060b41c0d81c5c030300070203e440c0707a10882d60a020280c06600914036 = true := by decide +kernel

theorem cover : BRFrame.Cov 939388489 939568345 := by
  have h0 := BRFrame.cov_init 939388489
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939388489 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939388489 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939388489 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939388489 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939388489 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939388489 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939388489 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939388489 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939388489 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939388489 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939388489 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939388489 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939388489 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939388489 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939388489 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939388489 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939388489 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939388489 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939388489 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939388489 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939388489 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939388489 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939388489 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939388489 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939388489 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939388489 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939388489 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939388489 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939388489 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939388489 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939388489 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939388489 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939388489 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939388489 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939388489 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939388489 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939388489 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939388489 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939388489 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939388489 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939388489 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939388489 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939388489 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939388489 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939388489 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939388489 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939388489 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939388489 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939388489 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939388489 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939388489 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939388489 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939388489 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939388489 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939388489 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939388489 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939388489 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939388489 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939388489 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939388489 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939388489 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939388489 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939388489 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939388489 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939388489 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939388489 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939388489 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939388489 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939388489 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939388489 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939388489 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939388489 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939388489 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939388489 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939388489 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939388489 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939388489 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939388489 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939388489 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939388489 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939388489 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939388489 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939388489 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939388489 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939388489 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939388489 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939388489 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939388489 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939388489 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939388489 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939388489 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939388489 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939388489 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939388489 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939388489 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939388489 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939388489 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939388489 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939388489 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939388489 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939388489 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939388489 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939388489 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939388489 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939388489 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939388489 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939388489 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939388489 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939388489 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939388489 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939388489 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939388489 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939388489 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939388489 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939388489 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939388489 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939388489 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939388489 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939388489 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939388489 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939388489 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939388489 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939388489 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939388489 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939388489 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939388489 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939388489 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939388489 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939388489 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939388489 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939388489 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939388489 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939388489 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939388489 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939388489 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939388489 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939388489 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939388489 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939388489 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939388489 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939388489 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939388489 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939388489 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 939388489 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 939388489 ≤ n) (h2 : n < 939568345) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
