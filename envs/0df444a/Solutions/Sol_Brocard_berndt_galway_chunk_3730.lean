-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3730
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:30:46.447985+00:00
-- url     : https://prove2.me/submissions/4f77436c-0867-4504-9cd4-eec97caed393

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 670683453 ≤ n < 670863309 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 670684703 1250 670683453 670683491
    0x7110f1905150c0316020a05030703050c13090515010608150108060d0501150b03010e01080606100c030903080408011b14090f060403020d05060703050601050304120c150e03041404 79
    0x20001d45241030b84120540c071402d15030242601c0141640400590609616070240208800c14001c668207100c440c2e881d4100b550341ca605110061a5820610001096140400800c001c90010385004503403100c0da9a00c00d41400910058008002d0003440148600c582c44201250b0020600340f4401c05190f01c2e000203013400000822092040241c2c3c411306040004c05e40080c0410a0343ea038201030710544804030005941c00c24080c0241d0b214640c0000a02000001001c80c01a44040c2500c07400031598202195a420540c00990038050314190000010700c2100040000782140f4000040b0103150580840003040040c000d4020400b2070307030003041c020f08840708503100094201d0782ca80c010040200403c1c003134002c42d0310103544046801400d030305002c0e0106016101d10102d5070b00f00003559404005540303a0100780c40c00382006100d000118074250103031081401c0d82d8000c40d5805100418011b0000688480a240400a42020908000000c080c1540300200c0d802258144a03622120501d03031204 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 670685953 1250 670684703 670684709
    0xc0611040e161815020f0d0c1e2604050a2402010e0705040c0306080307140d0306030f0b090c040504080c010c050f030c0318070902090108070e0d151107110f19 70
    0x12113004c0c540c504070300811400008085000030b0b0359135010301c18806000c00400c450103a44400690b4802c0c0701d403e4003080d078800001d0f4058a264200c00c41000c8414018003044180030219400f04404505e50f075030004541c00a003408200d640848540c1155085126441d03030040d42560704001402d42c50720390114244056500c2900e00080800b080d19045016040315400035603030340000100d80c0d0a01000070702e003000e8a1004c03001c81f020b0540014007181180c86500c4080e007a000d41c10300082c0040d03d2036a1075500000000d00310764901c0e1400b400502201c0007a1070845d9010000204040030030300c28000d030751030f00d807807810b041e03051000c01d000b804d0707080c80010b04003980f0045c000002041044042c0020b124a40c480084600712521601042c00035030000b000e083c04958008000703040f031882110010a8440080c4c40940c2002184d507a050720b140f01c58511039040740d143d0111443c4011845c001d410030328094800b000a0043d00010b101030035020040c45130062911130131215a1030040d041c00011 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 670687203 1250 670685953 670685969
    0xa061a10050c280311060c04060c03031b0e15120a020d06240e0d030e12030f1c18020108010e070513031b050f010e010c0611040e1618 59
    0x680c030b40e6110250304001c070500f80f143c0d04040550000c800100350300c4807010354601c291140010f030856100c1d03140d520141100c00307030174080302080b0034042a441a074001c504244282000f00d04040070320340c40c1c84250441c0d00c0000004604d143c105501c0d20b080d140c1e42400030003036401e045c80d020034030000341c4400400420200c0c2290300004c1060360a811588100001c0c880c45401c00024820030070308401c5443c0c140e100d030340051580c03803901885203404490a6021a0f143e11440450306413130741400700350b00800b04e405511340414000700702c4c0308668500401079a0078080c46076415000c0700034802c040312951070401d20f00656100d10000183d800c07218190544820642821050362198401c03245441410480160203034500e2002040012184200320030b01c8280340e031800301a4840c0d080c04034aa610300e9140d40010141154802e00f0350142400f40d07184d50069801264405080d0380310076484d0b005601c5000f90040d10000c0045c4c0d01000c4094080300a00c510b4800340a040e250796003020343c4000e00030002 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 670688453 1250 670687203 670687207
    0xe0d02070b180904140703030503040c060207061e0306081f0f061a030414010c080921030c0f0f13030b1311150715061802130e13140a061a1005 63
    0x1171042241c5c0075407103c140d40048900003a00c034600208190011381e0202d43c0180740380d401291150000ca507042c19100c0680e2011003500d0070841312503039076040440c21020b0581e80c50700460700f580240014810322070030b80840902c0c00700281c5041d0841d400658144141407500c1e600b805000111540c442d24055040c2c1d03555200d446506141c91716500741c0912800540ca40514000071030b030030283e2248196901402d96003c3e86054000000720f05017041c000c01c4040d030400004101c1c0300b0900140240001200046040c508a01801d080701d0340406800c404000884900700100700208407442e038070480350407030440b1802d80b680d0b42c5032104c02c05190b46441400d518003022070303103504602900d0f4020f0300138000d07000700e06442c0c1c4103800900b032601801d00d0a004448809031000c03418021510781e0705050452084661503c608641c8141d4058000004005841844004100c50014034484d010300c01c8068142c1c0842d52030054100d580816a90459040b0f07403254020b280d59080b0016000845810019 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 670689703 1250 670688453 670688461
    0xf05090a0c110a03090306050711060c03150310020301170307080403060b060d05130215070203031b03041a0a02070f0b030703150f06030e0d090f0611030d0e0d02070b1809 75
    0x5900ca80d00308010b01003030700c01c0d00104401d01d9030000c400fa040328011a003c1182d500c6420044980c3c0c440800b90300e101c2d52003680800c40ba003060b1402158800e050b110101c02a5010b100003034101143c3c1c1c0401d0000f02d070040014402013004690a03071880500da00298503101c0039a84011282c0a03622000e000144d0390801c1400c1c5486003c112240810490010452864115034190442d10900c0b402d901a01108102c42ca010200304210307105140c000b001181441e10301003060440b0285609880c400c1c0c002408001207450003100d24070305407000c04d0001c0e61110b889000082c0b9004e519800705100a5248508100c090304510450307801170750500e004a03400012109003241c4008d954004010404032810008100ba4154000c4462510b4403040d1120000c074000c00300d810b669140076a20001091803010400b65014440d10703200300480340700740c0381052640c05002c01101c5481002007010b8001807a0511500c0c3d0600115000e0841004018148010020102f000000142c0c905000d01e010002003 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 670690953 1250 670689703 670689707
    0xb07020705130c0f080c0d0b031203070908011526010905031603080112080f0705160e1609030507050d0c08061e010b0a08070309020d060507080108070f05090a0c 71
    0x2601030400a00000b0101e1054036001c0000c100b034611540024450080c9030303000c1c078031071031050780100d14411066007001d070030a420b01c3c014666000010b45c58030079508029840d01889000c0d52081c01d45456407a80c091405401900f034a160360b68401c000100c0d03040a1002800d054043c003680c0544100d519000311008a03414014840c1c4040500350b480701150201c00564805a400d0300306100f60365038034150b42d8407016002500450000180390a6041c0070301860311080ca0085c007212405001118005000b820b48001002841c1c0c109424401041c410030000c45000c1503a20a580003501e021840c00b850b6031146503d03084140502c5206030b25a8030b51605100e114608000500b404100b43c03a0503040903400440e1510084291440c49084580002041540300c82900e400550a0716140281d5070340c0d0310200c00900c0d0201c812a80000135250a4004c02e00710302c9120304c1056151107440455040030222840c08001d9800014180c0d0118402e02082d00d50410312500081d200c440815004240740d41 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 670692203 1250 670690953 670690963
    0x4020603131b03121701030203070e131709040c0e01021513021203090f0114040b0d0f020a02100f02040501020a020f0111101e020a0503060d06111b0d0f020a0b0702 72
    0x2600c041e103001d81d404010b1000201d181421010302d900c45c1d0080e80400c1038540941134007448081d6150300005000c20202c0c1d28841016030008041e60301c9072041003242c1e41c0904006007039580b40015040800c00d0001410944a249416041418000491505400002c0d5a0b00c0c40c030f40920308070000714020801480da01008824090790003407150800c0850b80d40e510359607420190700d8038400c103620b494405155025a2101124011141c1000d203040d052455007121588805d201c1ca018540d291100303a0524078500c00740400c0007a030340c080c0c4007001154001405075084901d802c0880c1d4810001008283e80000c0e881022940c140c8500700c00c0d00d4120011f0302d5002c031040e80c2d404d09004184001c007505c40c4540c000c1c070504c03201080ca40e609070410820316049004144c86200801c1c010404515549451100506514480c0c203010401004030500054240c000890035084104d82c0c034616861a0001c2c043c208090b07290345400401c1c3c1c2e001c002e00039a42c1c00108400703419403107910082860b1510a03c2 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 670693453 1250 670692203 670692233
    0xc02300102070302010f05010b04030803041407170c0108061e011409040c0f1b0b0c090a0f0b040f0503010212010b030a0e06040c150206010b09010e010c060614180402060313 76
    0x200031502d0310b20504029010b801b84c090258880da103000b00100f1800c00d034900351800e594014603054150303629540d429900030428840d81072640b06a41002409271700c08a200403800c0e40c084041c140f501c00701c1002500520000c0c00e401c0c841c130055050207600241940300000500001d2900011604010307200199a1142784022078109040580c005402034000307030900f03007500b59640c0d01342c03140452012145d042001e4079002080d0384401070210300c200840700064888080010141ca0107550360380d0950a4020482c4d00010400002203020004401d03c4444403000f043c054000b58030381000740740c03000c06030f2005000b100388658001c408104500c40c1607010324080500d030b100303c0d1040d0505091017000300e0001e2080e080c1c0100500102c4003038510104085040b5402a20314a040031201401511680c003140d400c075040120100106010491034065140103042c19828604000401030034070111840f0000b00400b5421694184401610343d04102d0354000240000d04541241e649021000700950b62 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 670694703 1250 670693453 670693549
    0x10031518060f090905030d0509030c010905070f0501051312030903060906021e0903061914010f06022b05090d200301061e0b0a030e0d050c0705010c02 66
    0x40214610303000c0da4404000e032a04046a101c0c042e030b0b569030760410788004e040001c0c40d0740c2040c0007410204071075800c40c9400088100036203081114402e030301801c445180c903003603403164000d074010400b56040c18100030140c0030a1030400d1a009291000024400040c403400300305a07502444682414807d204070400b95a000b42c040c400780b1740900b0032034080d420050303800c030401d82201c4004540003a4072040303605052000e800341c10b0340c1c0c1c0c803034040b001216030035403030f10796219120114400c8000078001e19502a110f008210005541025002844c04141513441800001e50321b4000d814000074246403889560399143c0039946003604404590b0721400018000e101440103d00200900100d03121000d501f8010790007048555a0b803184400404030100000e03240310130300e440c1800004a0346000b09010206818045021403113440700925200f88400c140340041d00119211200d8130043c0003030782c000c0c9424030b0852116082900095101c00c05203025110340c4410f00354481000b60080c0050000c500c0031303 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 670695953 1250 670694703 670694729
    0x3011503021306180e0f04060b1c0308090d180e2d0f0f06010c0204180209010f090c03060e160309020604060903140d050a0c050f100c0e0906100315 65
    0x341c48090081ea250b00d15600d14418090300118020178104600d80c421145038426404946890300d5520003095a451100e402c0b61800c40c01e101321081d00c18854805a04c43e6544041c030b80b51681e503690514070011850020400c09110540c40e01d15003d0701102640c125640c1d00c03281e034803404203103542001c4500d6001e5420f01c4e81c02401542440056451348650915404902140ea4103800d0114500d000c8030304a01040d4065200d90144c20a43c2c4660920f040c42c18451a961050f03400080d4580e100f640b00c003a2041c01c5035002c0c40100b160b80070707c0086c0c503030310709003030040074204080b540340c5400c02018000c00b080742c00320303003140c280c801d820030f0340c48540180500341e84948841d0000d008402c68001036403195110801c00401d2403001804d235101d0301c9203503030381c90800038500c10403903445041290a603100d10800640d00310002c0b0500940624401039000000c1140b001000940151803a0702c1a0380f09481030750403c1000d0b15500180d1f40108503a250001e2803054801c03ea0007010050303013240c0459051 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 670697203 1250 670695953 670695959
    0x901140901020a2d060204050306090c22020909090303040317010311012d020102130f120813180207060b030c010906030f02121003020111030703090e0a02070b160806010212030115030213 82
    0x5c950b004009480d0142e05031420343c1d81d882800d91b40c880700000000d401c910701c00011070002c00d01c003408030000b071040c0c070026150000c2000080c070852015140300d08540c100100744020142c0110080144510441c842c1003150301d151201c44102360306a404e18140201203a12000c030000d000110200306003203000384d0901401c0440000d0003504003180120302e6a05c018400310340ca02000d64500d04580a0000d403002d2030400b9a03e40007a074001500211238140504408a0a01c50850003516240000e070401a101c1e0040d04100042d25610090742d402500b040035520040d9134050f443d2802e840050402041e2500c01c0038044c8003e1150482c0401080700d41814082c003c2218460b04088174004d80c0c07400180d0000003600ca48038401c9010003004100e500300d0030094410544090381d803007058104010b061041c00d4907651030740c1c1e2040320401c40740b4903900744040c4a680c00140d501c0e00f04100384014002c0402c0400d901040784018000d0308038039603041600c1c0c0c50f00c0b032003601285c481c164151480d01203035079 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 670698453 1250 670697203 670697213
    0x12100902210604020a08010e0316030c020a0b130e0402093d09060e09030706090305161113020a140c0c190f09090809060a09050402040b0901140901020a2d 68
    0x90030b5404178401c4281800c00148000140103003a00c910150f07020b14500403e2462020001120324800c070b041c0400000040d000d80d44407000c00303000b01003040b100b17981c8801c648402d824005994024109101103030081c0809a1210303440c00380e00c00319103c000c003003500355802c2c0d880860740f000e130240c029900715050000b40f91803100c0e0f6840444480907028400c4513250030b5040c800c01130032185000349a005210000120b8040e0700011a130f41d010342056860490703880304410108200081c02d41d203000c040d040c2e18905042100d070400d0140c01e00c01085060000d8a10010700c601b283c0300f08201440f00c08140a20001e00c01e20613000c203002c005000c2c441c50031822900b032000c6079252141042c0396007071900000c0e403c0c0240c0541d007442c6070300040080c540312820041000503080383d140c590406c000100085103545561000b04007402400c45203079140c041c404001850149100c0150300310714000d2080340b400b81d0f00000c0c0781c4003050340403c501401d4140c02d101420b01005614030307252003181c0ba80c200010701c4 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 670699703 1250 670698453 670698463
    0x1051e0a1517031c0911090c0c0303071d01140f090307050904050d0219080301050d060b030703060e0705060f030a09080c06042001020f0607031509020c0601090b1210090221 76
    0x210040c0c40c44145200c100f444d14101d03450518054800e64400307200035031500d050449a0f9019141580c05030503d2940c0c6100d40c9560030499041c0c010402c5001500705103221100c240d40d4088003441e02d140101030b50030001d84580506984505100d9002c1054030b09607609004210161901400d11403080c501800c02c0c0d40e46502440318072000d4080c000032081041450002180c080d81c000b2903030fa241d81d00e041c06000707401e000788406981d5295030b00da02c01800e5505128850066004410100d0801d010078402c40c140b10340c03588000c2c030400c010452003030041005401d59600c200904400103a10340c01e8180803460b03100d000c07211025400b5400c01c0004211141e0722200c2d00c0d010281c01c6200c458403080059039240f02072024041250701c8040040c00540c46500081c0c005510f03402040e4509a8808554069030071601010708590000310040c01100510b1044032802002100d414405000703540540f178491842c80c0c2c0200a050300c94400030155202c5202d040302c40a00301c1e64a600c844040521243c40b0 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 670700953 1250 670699703 670699717
    0x3010f0209010908070609030b15030f0d1d01120906150909050613020f0906240d1404030c0813030b1501080f06060406110705090f010801051e0a151703 67
    0x3c1a480c102c04900f010340012444241c0d41d03a500c80a0b280f43c255260108268130081c0708c00e00600c1d260b11131182e03c0d2002e0110201010894008007030070340c034800014041009a1031030002e52884099030441d10b03a40514061800000f101c000220001c0302e08128000e0107102c040b90751015201e40d80050a18007507072040d94001c3c054000d640054540207410992990191800b0b94468020381a0b0081481c14108840d04080c0091805403c0c0e0584400880000c02816022000150220f030000b69529140103940c04000c0780489038074175103000c3ea0301404c420b40102c070190000401140c03000c102041c2c0d01d01c0201640c1c001c0d10744900c510701582288152803101000b01d001a81d04e8000c81d80d071801d49904103006060081c071681c146030801c3c03400c0342d10f47d04050042d107552042140000322900c0d440c0b000d40c0150400c0f4000c2180d5070400c20300a0a44001038800d8800d4031110342c60f003804070001d00089822044510000c02c00c3c2c2516001900b07000b0280d0400309241c0c214030518000800000024407007 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 670702203 1250 670700953 670700957
    0x60e0d030b010201050f042901090903080108011416050c3301060504140117040f1a0c0d05180d11102912060109060f080109051b010306030203010f020901 68
    0x1640d401c4401207082c0c810a483e400c102d0b0744c21101040c0040d040c2c49210b0100000e2444031110700c1e4840d40781d0049002c00b80c0c0700311000350ba20383c20841032552120b84076024000460080c428180c208007103000c0b90034001c008848800040c01100400c0d4401c5040b01e0050120600f210b22032a501e0704094003078442a02c3c4a0b2043d40011013650045034407040f928101c5040b61296400c16207404915203241d2005050541003100c1d800788035000807006c02e80c42d800786014102034501c9082d90314084140e22054294802c4030100c0b88100700000b04d01c4011502c0344200b900011a4544601e6480c2c1001d6400d01c80c80c241d580a1340d2500014207070310981c51408101041d01300d5010300800e0050408a5150305140071202e030b00b43d03010110404104003000421a0003810340310741b11400c0300c0142d050241c20307004245226200c500400890030101d01440180050341c0080010400c59a5002c1e501c1c56801c0d80040c1411281200d10402e0380243d1000b001075401074000e0005420a2110000a6001d0310751280 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 670703453 1250 670702203 670702211
    0x3050304080d0501180614130e01090f060911010206010806040602070f020d0501140606040305030409050405030715060603231303090510120c0507080d24150e031605060d09060e0d03 80
    0xf800809040320191f030090050024426440b0140300c0d50003a03c400c502484180d901e420704080010f480d0015040e00740d00441e000102010749140c13000d000d505030064a41158000340051207001e002107000d940040e03010307000580c1c4d200d40d80b0b05031240140c0a040654000b45800750801400f506410820a040b4101800c40145d40d500c030030404a405075000180c0b00c0e40c800c0c0320501148910b5807160750014012000c0300c0c1001015510003209246200110307001d21746404041101d030f9090300a4122203c40032104000c80110050403d004000c0203000c00c0c0300d202549071100c01e0500030600840a800b0150403030340380512540c0090b01400591442c1207071286000c540401c400d1041040e616421784c05102c0c1482d183c0c48039240400303003400001c490354815440400d0004c10000c04810001010100003021400c01d4410b000b403c0b502034100e119021b5000412001c0d00201c0100c9540180da0f0102d4405469041e42c10520b0010500300d031000b400c0070b203050b8101801000000350307050301001654081c0 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 670704703 1250 670703453 670703459
    0x1e0f130c020c041104050402130e04030c0b0f040305120601140c0109020108060f031c0e100905040b150316050708160210020f15070c022d040e0a03050304080d05011806 74
    0x1c54002001c0c0c014160000c1c0021310907032819030000c0215034107a410050189d603c442c020001e130340013503e01300e02060b04804c04508014050b00000e80c4400010246680c0c0d103060380f0094040e1017108500b00c42c00c484500041d4040c0e0051203140420441c0020440c0c4a840c00e091060007441e410000342d000c55412800981c40d85090180f0508140003d0080c0c000703840c00d8590348040700c581e40d4100c2c051000c120b8142c415501d880d0032074803c6420541e070f02d180e42c5192105201c2142c14610b0024002c003401c0c0407032804084c4100480e030b040a915030b1200c0b8030500d40300040301c25020f1490018010030b0001190f0b231782c0c03901070038180c01030318000c480c11130445030351180030385c0e03658441c000c0061607400181550b000e501f80c00f4100c82d0712074010709002001d035003d0740c00102070508010868a058000315415014402d01c01130701e0154200c2640c0400c0000301c07000c0b603650f8404180100804110740000007404002030315098640c0c881441409220325612091842005802101c4e4414074500d402400 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 670705953 1250 670704703 670704709
    0x207061e140c16170f1b0c0321120a021213150c051207020601090501060306030809090c04050306040809030606180f040201020f101a0f1e0f130c020c 66
    0x118042c02d000b01e1240d00d0442c5102180600e40340039101034440520b60710301d40c0600c01640004103007031301d11480d0070b1b90380b43c0510003a13103d040b18900048000e58841005041103850000c4c64903c9419418a9100440380c1401c40d08940c0c8105a0480c191003e4071042c0500141c860300038044071907034103199002a50341c000c000700c107202402c140600b00103055140c200024203158000025400759141c614500b20300c0d00003110748030b4420b64103880168480401002084001d01c00c50f805040549018000b103843c54441114030701440454500c510700c04408601581a040b003250020440507054501924150074502041d420400d0200d009000c0e80e00010b40d6031030120682e4091125118844609899648080940380d0004000700e040d07204030340600d0001c00003000202c0e1182a0742001103981e14512020084042e0070a80003402840701888031081d03681c40f41040c5514556a40a840c4002c94440020b104028400d001540103115031a0f201404140d68006000a001c1a02154400c0b0421028 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 670707203 1250 670705953 670705991
    0x810090c03060e090c130905010f1107031d0a0603020306042a180b0a0e0414100321080117011b0e04050f090c0f040605031c080f090c060a030207061e 66
    0x2e4641d200c1b00d070765500e20303031000d89a121444040c05000005a00410b14444100b00e8080203040d030241c50001c5480c000301644035011444c81d01c07207008a03042c1c1011010102d074269207180a0380c03060640100c009242c1c0d4907154010090310f00084040280d41040c100a521180000040000050303d004100c6038402007203050076086480e80302d480307032400c1030441c0b080301c40c400d00d5514181d01c2901d4070100d0b0004c0310100c0490307000e0724942050051031469032612a902a00d0055240c80c400c0c40f05040c00996600a204c0c030741114610841041601d0700b00149078010b010b902005014031420544c0740e1515a4080c07280c0f54480c07400c0d20100019100c688207214045012203d650855000190b074944906060b403405010b81c80c09000070989130340b0f590003e81055940b64400e24140ba0211039217500c5c44d40107540a400082c0084185d080f400d10202c211744a070344008100380224000912240b000e40b00f94100c85510360001c60030040c0c441181c0d0018841e40700024040c0b9201d0900303c9070107109400b424 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 670708453 1250 670707203 670707223
    0xc03020d02030a051b0a02120105160206060a1e0b0307031a010c11010e0a0e0f090c01080103050d140d020a080103060f020f090f0d02100201021c06150810090c03060e09 74
    0x68050030400b2a000484000715a96845c100300c0c02000790900050300e48452401e080d900342c10000c1180c0c0380c04200307410281039900e006402c550290003400280d8407420181800d03680100320014440104184a0f00c8940c1107034003030782840380f00104000040358568000c400000003903189140c4242888011240307100d400b000540003614920030761f68150b0180c8410681140c018008003030495a51420740c01c0400102d400311018601d1601300010014180007580a00da401d08007100a0350650700c9203a60392980e64164424000c0081a0b140303507200d4030003501d80b000451082503580d502c1011009002d5a0203100440d06182081c0039001c0303440507070003542c0400744981041c50070503202c00e082200f41201041444d42103195207103000c000d0b80715940c03d41213820207600050381c2e8041a851900c12502c2c03c0000001d142d2424005101d888001e00811000319030500e0000700303d4a032a40c000842d801d482d408850054038003004554aa50581c1003d0112842614412115502d0f10a11900c2d100b400d0 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 670709703 1250 670708453 670708457
    0x203070f0302032d010204170c01050708040b0d11160218010810020711060403050a0312090804060c0507050a060c05060f070c0f030318030801140d051009210c03020d02030a 76
    0x1000711a0128641300503215040d00000c400b16500c0810070103030072688942c101d4200307401e000c1e84100809808003c4200c0342e820a107000f40c54554181c0b900c41250040d4040c000002c1303000200c2218954442d00222110300e0401ca085560708219410107040f400e00c2c0c03030201e000e1003008200482030750301010079504a07140c28002e0501003454a0140c4020743c446c0070b0489150000940d05001500c1c0ca40c040c2016610450040c105a0b000d4140544034911014116034620708003a0300c0400202088295000c403111400d0461068140d0f1814508103040f07071300502e030045000e8000144265000c041c0341d48080c0914165201601c50380500ca82c00e0508480d0100400c00707901c111700c00102a0304007015120700a01c0c001844500501070303248082c1c0c26070000d4000641a0005003c0340c1c4011520070001d030011100c000041e141c65554a03145d4001c007210940c010ba40c0c911b250107000c3d220b81ca0a56083e2100480c0444c1c1c4511000585541800300c130030303001032051503140203009000104407044040c0715 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 670710953 1250 670709703 670709713
    0xe130305091c050d09180b01050909041a041101030c1704020f0d06060e060f0301050f0121080c010e0106050901030b13030e060d0f0509010c140a090b03040f0203070f030203 76
    0x2005100010b4440640304154a030011030a10100c0c0083c40120b141d2940c69560320100d41c0b40034074100064a02d10803901849141c40e00ea0009680c100c0126402c0000c240ca0075580c66803241021030402882c01c0380700c1a500204020081003240c079000c02030b256442600e041000240081046995542c1310040003d05804400820050702d4854014203c3c001e0080400852840956034401920503561018811030b420304d080c41b00c0b914091000a2020006400811a40c5072646442401da070043c882e00e040d006560341c00f01072181e074000b40000626005081a03554000d0004200d009024560094a641d443d211001c94103150000c0c0c00c6048940100c1c1e1000f95444107080c603560b120000d4030071818049080803818040c3c031100060060b81c0003010000511001d0b0004800c2520300040886445914205902008075040340e5440c0900b42d000c040943c07a001006030503a0b0a80e0260040c90301c14201108200030003142400c02e1041900c20782c107a40d012680c41104410308000c0b40002580740d088 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 670712203 1250 670710953 670710967
    0x616120c0203070308070519030e0a2403090203160f141206070e011701060e100203030903071502040f0315060602060610030c030b0a0602010e0c0901060c03080a061a03010e130305 79
    0x16100250040c0c5008009a8012340074996085204030340517001140440c2c20301405020a03d064400b110081444c140100b400d92001c0820412110440311148241a610200c52040d51800c00c0360561400b8200b82c242c04c1c0ca61182240310341c640c4141b00c0c02410380721085002c140d0b070800c50500c0342c168010034018481c0d034550b080180e8602c3d2002e11054104880308402c00c269813009a041e0b8000d00660b01e0300c2d4a49614001841014045080d0f041c0642d8020014054070410020807a50450340050346810109446400c1c0c0010b0310865111081caa41c0d507560110900a1020b0051000c02c0d100703030100030881c1d40c2d140a80c2c507600c080790f0050344030302940c00400c03201e0301941009654088078030700020580c164400080c070340c041e0358201e540141e545000c0d800f030300754041109003108801100c08410540c54240010102c030051100102040b142c800411600706464020b900540f081b020b4071807456680c1c81100700075030000d10a2403540c910050100e0309070404c42c035070321640b290585e860340c0c50115 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 670713453 1250 670712203 670712213
    0xc020c0603130c0603090b07030903081f0b030a02030610090b041710050906063f030d0501090c0906080609010b0c0c061b060106050c0703200616120c02030703 70
    0x500d0041c000001002c1e4900003601503040d03d0142141d62800030b2455454207200794801401001c840616140c1714a00d004650010403440c0d01010f4110b83d840307103d40d0240c015548002a50084422440c040140000d011098000e544200c0c0c4c250f0710b00c0b400341150181141c2c40c0c41e040c07040303201400c4200418800080c1d009201c400303000e0124122110707880031550b88d03030031540215611101e50300000280019498061a194040005424922852000c2d407144034002c0004015410845500004c40b400a00080c401d0304c3c007072060480104415070f5110075440c040d20800c0303007500c0090351007280410360300e02032003040e8042c8a0182c64040280e091801e01125548032240380d8501e40b050040c04007641d951500140503c00302d00c4a90301c0202082c00d0740a180c45410b030400c4090141c02e00c070204007844001000c2041725009450f50800720126100842c031808030142003a0442d07030008844014108429140e02e546100e00781841c2c6036111004100c42030411110000e505800030305040020034 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 670714703 1250 670713453 670713457
    0x503010603051305030703020105101e0902031008060702070501121a0d02041820012102030615031807092007020a092909060904061e020417100c020c06 67
    0x40c603940441003c0c02c43c0c5506181d5001140101d005079114410031845605c1504000028a80440c200c14519100707003c1141d0701d407030b0f805040d81c91903000c40056104111035040030020030540083d16064207103120020348910171402010702080c0d11002d00035111420f48600311058401201201c1c4041a01c0104950590000000d07030340191a46840b0311355100030081480454400e89841440c0c5460018150241301c448203c903050090201d0001c2c4058144100141c841522500042c2d481e601c00f1700048024012400c0030b61028000f004000300254989280d45040300502c0c1262112643c07501494141c1c0c00d03050142d081c0d0300d031482c030301c6854480c488054000d0520040030120003d071203108010485040040c0001120fa51412030341440201011001e6140030a03038201c0e0781445c0c1000442d101210241008104958505180040740010002d904440011003810f6507596540d4119076820b004601c4050650700400e40d80e60307110f8400d031040c41e00004854010b441c41d401d00108001d440c1e = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 670715953 1250 670714703 670714711
    0x1f080c120402010c03031d0a060f2705101803033b0106210c06020607202401080c1212030702030f0a0518120a1104092f10050301060305 60
    0x3140c0c6901c001c401503e40a0b4520b40c0c0d4000380c000800c1b4464043c00e00c03006841e000307001d2b19480342c03504e021092076070050401d0b80c017604804c0351148103c0040b8640b1501c1c10018100214126142182c940e62000d80071501c0c0d6030881c040c6c0d9050005440b81020341d0b1000c004104003030300d0080059606005502102c0720394048161440001503140e179a001400310004c02201481010010101d0b120100112004200040c200c0d51000304480d1604440140010344005610403010b10344404070900e404040280fa000c3c800c0582c2d80400301c0c0c9500d829008039003c00e002c4d00c619030058440c511654144400011662205a00103081080c11b9881c1402503030300c0604040c01314001005405d60250140c0002c003158034040d1358965039442d0a82021140c0040b0141c83d0380705500300c222181240c040000c02a50103500f094105560003081000140140b03605c007401065482e04031021042600200c0c1c0160001c0340c040d214102c007494030b00030860910b0080b616440401c42c144018080c580c441d9200a82c8 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 670717203 1250 670715953 670715957
    0x90303080c0409091104231306090f14010b1005030c1e12071b1211032a0706110a121b0b1918060f02091f080c120402010c03 55
    0x90705480310788000944214103015218100501740c8121581000c0c4900b10250804d0003500c59104140c40c0c05048000c0d003d05510214401c0c513015106019003544440305841c1d00540511698040f403502d8200000b107441c110480d03501c0c140304000e65080000118503992903d645091030350b0703a8115126150b030011100704803001780c062030088085513150024040c0410325100442a0316100310024450300b801c400c0300300c6011003003904c0302c00140c261014a800440a0420300e084481c5942564594055102c030321064107590100240902c2640b000c6020340c045140560b44402d80364801a1007084c0d000809068a5210344840c00101c0c0906d14000d403001c0c407c1c50000c00c0c81080d2200709450406001040d50a543d8032024807091940c4440785030340200c0e0112060101e01640d0001c40d402c0701123054068441d5850354103070079104078280d0480d0284000248142094281d948181091038540c80150010840040c046241c0681c01e00c2070301c6400c518040c18001d50340d145c3c0d00441c0c400f1560a41201 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 670718453 1250 670717203 670717207
    0x10f0207030f06110a120506150d09060f11040f09140112050c031c02010b0a082a060a2c0303030a0b03030d09030e03070614030109050c070b09060a1b090303080c 71
    0x3400104c808010040c1180f15036a86103040c0143c00c59004440002c0d198a201d100b082810095414690044d2918403c0392400080d03460501d0070110064000011254042c6240c45508010001044081e00684280030070420440d509ca6003590b003100d024400166060010200401c003200e0707080c0071180e4891240042da0b01c0c046400e004070340350540b8510300c041030400000c0e03680b07512a42440b409441820440303451308903910741400325440d0003144600c1c4041440c0380103a000c00b0564481c44441e8240c0180602d5503c0c004610014401c80700c60320701440020741001c1032200e40c0340240001d4000718009028614584414040c0c40042c11080c4500360103000600c424080e0f13052501c2080a003d01a494001c4083d4002c02014100a10703038029100303128110407440c1d170090340d89042c0c90640702e088100180c252600e1034240344902540c04003c050800e20000c0120f030500204c4c88501458684170180507140000c03d15080f0324440780c03854070014642d60800c1010a01c14039105030464051407070302d8 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 670719703 1250 670718453 670718471
    0x60b010215070306030b0f040b0f0601030b150408060106080408090f0418060e1c050301032003030408070e070f0509040f0f0c030207020f0f030a0803190c0309020f010f0207030f06 79
    0xd405481200c00401107680c600c410418801c4020405600442e87c01001e655840c4c6541c4a030039012015004403d0b071801507001a0380b40e4083e500002101038010700c400b00300041020011540c3e4898011413083d4004c0b031000240441c00f0b90f01050050358090344031401e101d1760340d0600803600c00d224842c0e81c1c00340c0ca881c4180c6128209800001a0750301a001c08030f01c642c0c03d05645440c060011030108901c05030541a41d401640c04000c0d00c0c1520342c0074207610003000350b80b845000800d41d903980c00341d8180000100080d50885c0010140304452080c0d045411a076104c000a0311001603615180b03003c200100804007481c60316500c1400c3c40490824009890707a00410241c00301c504c98004c0700d01090313000075031300f0951501201c80071703108604460b514040c541ca4008203460f012850030040440d14080003284003404074511030407201c0d007943c1007042b481d0685200240600f9280c03c06034012083c64040c0310581d4422100010140d16940061104500d950360b003980c4603500791015609296101245 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 670720953 1250 670719703 670719733
    0x30201081305070509250e0117060a080d02031b060106080708091e0f1b060712050c010c0306031a040507150207031709091503100c0c0606081f060b07060b0102 70
    0x89401180c0d00020300c0c071141c08103891a1b4640b0756580084041c0900b04c88030600d1030307a22806100c9034022440d46900c0d9512280041030351310520740c11003055070140b045070741ca01fa81d0020240c05610080c402018215803518070b0b40761901c40038003400c800144003200044080e4020008503400031428401c6404080e802d003501c0b084014a06035100d041d41200b9040f51102d4010000d40072003680c88020751100081d440006031a600c00c004004003011910710140c40090302038029286007880c0b4000900c0b0102401d80d0080090495020403104209940d2040302c81c2001c1c03a54444c0f08651000c024410103091019802404260f0f2182c44214490f0f200080001b903005d0508400f00ca20126100d0344032002503082218024004181403019000b00302c007000f1903940001c42c401c252115003000502001e15079403c44d003c00ba00d070300c0685020b080032800211a05c00284031380c603105d050039007100490700c004072100588032680704204041d10244034640111314545e0028410210500444081d400c880c203036 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 670722203 1250 670720953 670720969
    0xd02070311120c0c0f030d0305041b15091d1503030d06140f100507110a150815031917040e07030e162303030417010207020a06090302010813050705 65
    0x1005145460108983e121001c0c20130507206245001c8031500c0441e902e0a0110366100c025065800400d83c4034004a014013500201985680b0300912140303268603250b08440e1121048072016500040c2c05113000603c0c02c1a081e4140000100840129059101c6411203500c9140c0c038110241c0c9030000b040b0040b4010715610400c2c005008028102c3e04103401401000504034500d008180217465000080ba69503600038122140c096004141e40301514410020540100700d50304504604160794800a50540c0c10182e40c600c1000c40c20704c400e5004c0e100000f815182d9040c0700d0000340404800d24007000203500034880440c8080c80703944a5051665030650070040700e4058074550003007641c0d20300f242d8050b94240b00442c1c40b454210800c4204500e8043e403412428080850b0703940032860b51086100030398003401200c00400744003140c07844c142d0310100558000d40c000c0c00304031b00c151390b0b800c4006803090103000410101d90b0141c40d00403055a0301608040d0a448145045503580100c0d00081881e94880c01d07 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 670723453 1250 670722203 670722223
    0x3050d02070605040b1008120c1002120a0f1a37060e060f0409020d060b0a0e0f03010b0306070503090a0f0c0503012a031e0908030906010902090102030d02070311 71
    0x400407519041c507040c4070117006809055000310082d0624180142c01c00040d03910403460065814a0340c88007480c01c8541801e03440342500f00701c01e00028290300101d01400000c1d0040c41502c60801c14044503a8061044901d4000600e906100a6488000502d8001d0650b98421031058910481144001d100c9507085140f007852140b420030a10280075440e4010301c100c507542c806131810352a00c030480700c429846004610801c0d0310b4175000a611184034049030000350091074803882c8151121070f1400050200f08401520900510796154401e0340c9180c1405040d540d6100030703010f883c0e05d840307003c41203a080d88002e20b80c1209124849100000462818403a0034450090b44041d21242c2082c0c2014250346070740800290344005035052a0348088428410320001c505424001000c00d05840441152030b804128191260314192900c2c0600c0305c544000e5200d01070b2003007a034038240c0e2221100b030220700030b2101140c0103a03c2803100d880c40d400164010b1042500078140f604007180c0092440d460008189 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 670724703 1250 670723453 670723463
    0x9012604050f1501090902030c030a03021c050f0403030e060f0a02100c0815100215010902030915011d15100e1f020309101704050d080106030c1b03050d0207 69
    0x420441889028440d891411100030050b03e210f403402c80340b0a020b100d060080c403a00940d80c40a0004550301000345120300c605c0a0b081d20f0080e515400c1c040c1d20ba8070701d0202c11080b01440350022188a00c1401143c104400000d4218146400c41d101211658883c07074090b608003004018905031044000040d1108104540c01840d0341500743d2541000d13510040000e80c180400c400901030403804000741c0c035190300d00559054607a01144d0300100d24100100c25226881c48410b0000b181e01e000b581c0046100e10800c0741182e00c0381114400e050707180781c0244203100003540301042d4401c90700c00104035070f508228016400046005507100042c102c0700103240400100301c000c9603403a0541054003001001440540540c03805c2181d00c50080c0d12485408052031003030340e400c181074104901505041c0d00050080c1c01d05a81c40c6484d00e0480da072041ca0035244e80110340418000103215100703000e1000110215500c081c0c0000302607030304070601010060214280702c42809546100c107081c0c40034000b114019 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 670725953 1250 670724703 670724777
    0x120403030212071a06061303050a0512030f13020102010b060a020d0e06093703050708102a0e090a0618020928120311010c0f0e01050901 60
    0x618010b8500401001104040d00050011402181c0c00044080500c2580020f0031440d54071031001445a2041803005055444011008414484002010f007500d40c49607044881d2204002c4c5616594042200c0b20182d032411034001400d0803042c412490a0944103000200d0250941800120741d900100c03c104010b900106c5141d110319482035450300b110108fd82d0183c985807080011840203038603108840c17042141341c3c050003c081110030b0741030342031a1444070341c40e80c45480780b8003a501c0d141075103e204000d10031491100c040003040c0c468805001c5009805107074030010020404d82c110540c0c401042030183c0d0802c000c401c6d44825240c2c42c03040021120020305d046c10400101c04245084013480c200c50300c140603600b00350b103462080000c01da80701082200c00c0410031403c1520021a60040380c90f038440a60020201030308008080740d00405d441c02800540485001120000481d890010018401040d8681c40f54060f2009050320b88042c5030060000b8107002e416a03d2440044500d40c070300c0343d0 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 670727203 1250 670725953 670725959
    0xf120c0e0f040b0f06070309080307050a14060105010e150705010c0320030f060d050717010203070e0415051009081605150a0c11010c0f031701060e130b04020c1204 72
    0x2090650700d405030402c0320304000d076416030000314a5002e003404c0900e0085500145800925014000e414014600c1c0030850360388401d60f141c516101d481c154800c40300b01110701188401c00c0c10200301c4506039801a0350b0106480311110801134962000d05038100c9240c2d00300610070114600380526810001c05460210340c0301402d41800540104e21070b00510108014024030040c02424448203401c044205d64940c00381d111804c0480c10b002103030348080340640951444101ca003006402441c4645000d843d443d00d003495075401d01c030546180d03481c84000a0702d846400c3c401d034a0320400c908141c020b545001c0c950141c40d4841c0b240790001e690841c0250803417400f4200000e1038a40e01c41c11500502da1030361803c00c524180c000d804019401c00040c002c079040380c5045041e1744108050030760950001c840c0c0d4203003600f500b406445112004118150b4011540020401501588400170308040150628014550210b5080300400801d840b007a4096020030189050080c01c105802c030354408500030a9803030707103 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 670728453 1250 670727203 670727209
    0x602031608010f080c101e03090b0a0603260c0f0f010501060306180e030d0507030f0c09051e0315040b090106080712020f010e120703050f0109020a05010f120c0e 71
    0x7505034065a00c000c00c0c1d20040c44a04804a01c243d28090b0641d0f054081641d81031003034900c1d1403404070030b064000e10400380101c0b40d94180c0100c101540203504040c0c0303944aa000e20ba0540c0c41600010b000ea00b11204502044259581c4d403902445000756030a0411001000c6141480c000c0010031081d030340a40d071041070b401003e1160740e00400303083c1800c10440e40f6000e5a03030f0031140e4003040192140e0b69085910f2201c50240304980c40b14503404810000ca15003210041c005001c00c00c101c5400d580b80c20001c00300715010308220b0301500c400826008020540403180200c0004071103141d034142c098946000503280c9491005030295114000c840128078107000100c0c01c6071400e602450107948045400c01489000c0034000d280c8640603142895941c0003000103952240800f04500c0d0004075440031583d003600045800700513680301d00c0a407500c040028010310300381c60000d40042d601003400d1000300050360040f0112020300059060018004a4030740015044864901d181404a0400003030342c500f0b45 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 670729703 1250 670728453 670728467
    0x2091f0c20130e0706120f060e010611010b0102070b0f091002030a111b06071109100906050d0b0a0b0d050109030201051608100608060310060807030521030a1806020316 74
    0x5151204200100500011030380d621954885c042c02e00c180400f60003088030380c64025910382034400c3d031309105407a0340322000c0c0c100b60800d1041d400040c25640340e05100744018000c04151400c142d005100242c20300000c0310140d445040480f0340c1c0320080090607107503118116400080441500a1916074024410107801d00b0b80c0348014201641244c3c401058145174894070015102064030352a4403030000c6c3c13810081c2d8502c900c210360740c05040101004a804c0c0110309540545503071007130078441d00e80d90340c0030b0115100258500a0800c40c00c0d500051120b41254409503450000170481c1e0034242240e1981400c5035a060800e400503510740701000290009841e2200c21916640f40244803031801449215007003030740740604001c0011403008240c1c550f808029540019241c0e260401169680740c0000e030f5600d280780310071900c90141e50b00041140c2020008039000010746032241d0b20710b941e01d041c0c0758000c1c03400c10300140103a075042c0c1e268400b050f4070f0b201461098115000c680c09001e502c841c060410 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 670730953 1250 670729703 670729729
    0x1807030602182418030f0c0a1505030415060302190302100e01120e070b0f040e0f2a07060f0c082203030e0f0a121202091f0c20 56
    0x310266605800080c143d007030000d09100c0603192080d11002c100342200d515070000081c590f41449503001c0e001e5a410003246100701214212400c1040540e1584d48615648026035a50081242800000c1c00706160000035082c0c034003a4000061032a4680e40000c801f186c2044000d01d142418078414411030a0058050200c1c4d2041d003446013165025900081440c9a80d03820307203c0050700d410010281040400408000e002020201ca03142c0516412035201500f091185402400011b00840c004012081c1d199015000e0005402d204156501a00340b40096125101c00341e150200405400f1807014428803804030061440800c8810400000801002d000303041e0040c0750700b00b415039219013192032240b4001c25a150402050001003801c0d514108084451440c0c02401040c00841c1049412803502d480c1d190143c881c0b100c1c01465071a6182280140045160403030812038001042e2910405210002c40052034851f1003001c41d40d40300c003000812002c44120719240d5404110003450610088081 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 670732203 1250 670730953 670730959
    0x140109180c03030c060b10050c0105060f0312210123090c1804021b060f011508070e03010e0109050303010810092d05030c0c090708070206010905180703060218 70
    0xa488064a8000341d0180381d100040500000904050410400360400311050034001c1011285180c40000908030303034821400420554a490300140044c5000f0380700c0a484a1b01600801030000c0c0740390204007030343c4075070ba0000101c51034070031a4216202114086019010006a081c00d844407024482108401d18200c503218640b00780400041d920241c0944a040d0180d0f102e00140700c10750f00101e8024410b00c4080010341a2034100d82603604000a021800b41a4500070507803141e9803038044c00f03050340f480c008610002c0c0ca00c402103480544203140c51454481e004000084a8640c0d060141c00c48801d0300c4100e955400210041010401c28030041d45010303070010052000320031641c0c0c1c25003445203500d490342000310072510382d50381c0c0c00840101d01083c0b07500c0f0046991300c207004002142e4822000c80414468410b2200080d0395900c00c1520b80d0142c4219001800c4a17401c2514840152000800b000088581810b5203840306e002040020700540c000c0d80010394407107c404012244180101c480b81c0 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 670733453 1250 670732203 670732241
    0x90905031e0325050f0d1d1f090303060b0d14100503100f06170105060418230c1008150607120e06040b0705030901030c1b0308041401140109 62
    0xb030800103140c041d110380c0b036484050420743c1c0510b1405a84074000c44000ca8200c80c3d0104942048024580c060846d5603c1c1e015626401112140ba5550703840c0c441c0c0d40c0d038038030009152940082d4142900b203500300312301ca8100400c00c6901c88001040070b4001c041d010303a41640310310246900903600040941c0002201d402c8400325818813010070307524803500c2058800b007541c45641000160700780c0d220601030000f00c500c117081e80040700f01d068040c0c4002d881c6144a02c0c602000c0540d0724003000000c04c01c01d98440b51418401400b1219005648041c003141c01c034501851020440d96640c140b0f850401c0001c0351201e610074104201d039681011003681109004500412640e40070a08503514455419800d250003c00b4a001c8004034006024a034130490040d607001c50320408000c4040f000d440d83c50401e903400c10204030340310400c0310352131080c3c4500400141c13280b07614808244203502540c0d0050003100541850740c3c14880090840d810b40c242004424590401801190840e001c0c80c40002c40e01c4803010 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 670734703 1250 670733453 670733461
    0x309080c0f0d060609090f170a210905061608010503030a020a15060302030a0b01050108060108040b010902180a1203080907180504020d05100510050913110307090905031e03 76
    0x194101e0103480d01900c50071805807420308200c05504800b024115244082c0045202d925044015040f412000c481032160b4042800c042040e40080c0d40d00f10080790740300c0310511030415100d49214214031203042c01350344485801000c40c40400019024000030f0451114a11042000074107410041e00700360f1098000308050040030f64002140320003a07420269080c0711150080d140e4000b00010ba000a401d0302408000c0000e000f8401d501e82e0480b40c00380c0b9140915500d1030011550324104031401011a0307986801800456025406000d00940f2444d080c0d10049000c0b000078013000556020900c0c000078400104101a44038044d2604a2041001014418203042450102c090080300038581c2c40e99880c00101550b507203c01f00f13040a5040021340b5190341c01c15145c040a440110f5000c64a0100c0c80c100003101e0402440c40d81c071035998100341480c03000150b510b0442c4081e240c50300c154980304000c0f020075402214032590f488244074800450b51841b243c07004003180301040070f20241c400c100740108 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 670735953 1250 670734703 670734709
    0x60203160206090102160b0304030e030d2a0c030b0a0b03030f0301140105070f0b09072c0c09060307031b030506030604020907090f06120e030306030d0e1807020a0309080c 75
    0xc44442a81211030a8694580c0700c0101d1600c8000300020f14005420f00002400030740308030007180100c0c02a91040700011400050565800078198a6000210020420070340000c690604513450702c469003040030451101d458a00c100c03005a0803e0f5001d070005020722001030014440c1c00103403542070b4040c41c1002c010b401ea0012a020521038901800c0030745a003c0d03c070368820011902c403150f000020240303849a0f403c166012260488081040780720b8021b0204a00700c50000d481d1503072140e180901c44500280441060b40341010300804640c1c47d060107000443e80e0791030007642c41001c00c0d940000700349512402130140070308950f0340e1109041c5080207006190b1008a5115440350701592052001d45030f84800301c515424581c40300e55440f80e402030100c2c51a9125034030358206020702c081801501e001d40d40c2d59449101c01e6801c5c65141d0300207a4900c0781e0340c0c0103c00c074014040004000d00c8914503501c2d41c041d10380740c0445800c0b0050300300084103420076400c00e15800180c0b2881c001000d801d1700075004 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 670737203 1250 670735953 670735987
    0x604030803060a091b11030f18040e070608040c090212010902090d020301020d0b090c040f050904240207060510080601090b1212092701030609110a030804050a060203 73
    0x40645103140010014680d502c410500400500701c2c10010008990025248108000c094180708005280c840112440000000c103441d46202c00039501d40c501000200c0b0500d0090303080c1e00c15a0032989450750b500c2c00600a200c151700412003902c0f048107a1400d0310744020f0b020b0310303604000b050034414080188102e464091090640304400720042c0c0c0d4030780c48070005e400105040c100030b51560000894003200c1c00f00c0c0c0c0000d8030700305050303d80710030b2622090170b0b0300d80358015809035129950910348100300c0c52078401403085d0000e002d881d100549200400c516200008034061000c441030300003038540c2c104281403141039804a130380e420210b003050030b10741d4031500d5000600c00c0880d11512610400c400b0b0356104c0ea1000154484811524269034400d10802607800c64010380e0702c07070303d0844143c81c100140007070400c092a001d42e55043c00d42e82140e0f606002400c1c014010740303501d0703007241405a241d210204d048000e98010410551a9403504040004100e000d40140085410902c01010b90fa520044 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 670738453 1250 670737203 670737209
    0x207060801140904060f1b020c04021c090c0f0e1801090302060c0307030204093b06041e050f060105130902030c0f030312071701090c05121816050406080703020604 72
    0x3881002070b440b24149400a0f0075411021b00e40070b4a0040911a65107580707018000000c4581c003900d000c1e0105c01c003003004038015584007046542d41c00c440410382400640c072240380c65200d050f03003017441a1940f150001c2135040e0b410805201c070009040c010300c01039811400c4001c0903180001d100e0341c0203942e8000d48800d80944a07280245000c03011130724460107901a1790243c94a00c40401c1880198050b8810611042c1c01c100300070740588032107401d5400e10031103100804860500400498460707549040a0a071100c0000c01460038000031640001e10900108000707880c4e1000900c129410310007000040752404e540d4408003441c10004c0c41c01038801151074640314004985044840e401c03000842d0441c410075480400c02900841003160b030341c0d00007500030042e182c1d47d1070002c0280e0721a06401c04a80036a1700c1800400e00070300c0f0020700f10414684265200e00c03044501142000c1103c00c1e03501d0086a0481403407200200760041c04241002c0c45510001d0000d41d0003010a585903402250340c40c850f80c0 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 670739703 1250 670738453 670738459
    0x1e05010806220b0a02040b07080306090601030504210e09011d06030601140103200c060a1802210127290106050d020c0a03050c011d06060118030b0702030406020706080114 75
    0x1d0f000403515000c59041e40c1c01003101050003641c4500905e0800516441154810301c00c0240b4400b00300c19510900c40d0900c51548030180b5610f03104108040b0b08818801c1c6843e004000508081d8441c90329010070141c001e09203100d100b580209201c0080b0302c0b90030003d180e00c0c081c1d807003600104000020910305200075202030800042c00102e50307001c11007010300115000e0480c0000270741803160802c0062068890340c05100200300b54009208001c030758030000000a98400d00d054807003001c10611010a140141d84403000050044a800311401032540840b40c514a20a0090800e070a01c2000d011000e20000350010540c205a94102030342e1140b08180a90801c100d0007046800714510107904848420400c8411190420602d00e401400b030f0f40031651110b640d5003410080504000400443c60030700b156100a00b40c90b41d038850045800c02040e8070300c0c88082006250000105800a0785180104d82d43c0d0302843d0740e40d050a4019181403c176510480800031080300400c1030164030140c049040a0803 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 670740953 1250 670739703 670739723
    0x411010c0b071805040c0e1005070b01090507170703020405031005061e1503150f010f021f0b060d0c030e120a030207171605070506130b0702041e0501080622 69
    0x3024507911400c090313007040760464038240c003900403160841c13018602044200e40590391440000f40440d41c6024254005190351500c20040c00a108503030002d5900040b070745030480300807950b6410a03a00110030b5401c0d42c0401c2d0300240501c09400d0901c074185080ea6815401c1c0000d01b0f02c0b1001c591920107405003074000e03100c0c12070301c4030640d07450500c6078028070f203412030458590504000ca40c454000c0707144c000d440340c0d5000120585a502990b00042d031950150041c210b00c0344005090041e0340040c140024215540b5019040d059940001a14011607003950000b51580e07885009802c032002001211099800121084043c0d903c01c030445002c1103440c5030250302d4500d94074000040c1074000484410314130700030481a81910000170f00a0b0940c1c0290200c82001d80e0b5001400f0349480360807840e060b0120072213410f21001c40204000e0400f03e10103040000c501501b0031154001c0b108584407090090b480310700411440c203041103541c0e00b0442e0151090301102402d00c605203e420b002500600d00021 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 670742203 1250 670740953 670740977
    0x1d04020901031d0c01020d0c030f0815030109062003101a07060908070320030406030e030d020f0415021506010e04060816090e0307050a031809060e0411010c0b07 71
    0x4640c000401040c3c500c0d8522100c2031240a40c41c0e100c2c45010703c441c0c01403142c048400180d42c403030040380405641648650300031112800e4101c0c0d034104002e008030b00096080c55008c00d292000d11507101c01e14040c440000d00000c00e9003100c400c1400c500b80700048424181b0a02c030868540348081c60455071000b0460b0014500d00c00b50062600403000e0262910707242100c10020302070820000e040540c4260794110101d0700410003605000f4032600c107414164401e0100740001d9000e40e00c03465102190f0403ca078140807a41d405501031f40e00140030b84900c10004142000806076101f4550403060060001e0425644017800c1c000414100a010354100704141c4015002500c0b1580540701030000300c41038070f5402c0c2850300c02c0d024005143c418682094545000301442010100507102216800b00c0540400e131051b4404444020006a403c14141004080080c285400e4031034200189030112402e04c062a0a0610013070040740c00d45040e041c041d051042000042c409540e66a210015040000c15045 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 670743453 1250 670742203 670742207
    0x140c130b160b0a020702041416050a090b130317040e150d060c020d020d0e0a03020103090c0b030108070f0b090a0b1e0304080705061612020a110312040c061d04020901 73
    0x700220094000d548050078044112810740041640c1402a6020312112a10284144103c50101c86c0210641900c0c943e41e02003900c10b00082907940750515260301c50a849840b071100f01c1c2d01c02040d540045180c02020010055002440c04950400406041c10301c1e1405000c806e070241e00824041c0c8103d00412100304940e2003083c03000110b50002e030100300303101c008036019680b04a20ba0b003d5015200d407e403184d0071144aa0100c4990900190000c0c1e50680385078015006060000812641c82d1055400854032210100140d8000d03c1c0c0c082c0140251441d00c6910f80031084141c02500e0214420070080f9800d031a8000380e0f0040320701d0405da456030758030101011020141131050260003050f00000780011b00000701f0281c41c0c041d000b00240c030110f459940b1403138000c5400c0c070360000201c1c040802401c640c2d0481d50207017000828a04001402c102d2510803d0b00351342c4290b1a0b41032003482c0310144000d00403e100d2820207403403582441e0303030003c80e6400b02d03e981c1100e450f03200d4405e0f0b8000641d518075034 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 670744703 1250 670743453 670743487
    0x120f08070f091509061b030c060b120d05041a0c0606100311041d07110607032c161403030d020c030d1401030302010509011a010815090a140c130b 64
    0x60f60761400d451a86082d1008144c104284aa54005000068501010300d8000a202c2805c1e505890b40034034080b044c1e41e10307005449080c0205038860b40a0103920f620040a21101d00b800805583c1c3d25078880c02c28008580c41c0300c40030200c0300349a40c02d10002e1420280094030a4006000f2266084507a02d498000c402405900d1600c1501c10800304002841142144807032007801c40c405192821555500800c441c070450242d004085948518007044071240030703610500105906250117405408074100c0700c45681004071040c00749038021400f04010315049500341c0c000c1c021107a1011101d090b00ba0000f0381e00d001d06109410366680c000352240314000100111041c0c5011004184038129085100200340341b400d00c02600507508200c00911202e80c18811b44100403050004100b88403d5103004681c034400091100d101d0f900d2744000f5149a6445401c1e091040e15541c60204074000c2400c12100b51800203807640d050741c141408901c403041c0034140305905440d41c82401507280d0312000040c20200c = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 670745953 1250 670744703 670744709
    0x702030a06020a0507060b120601120c05060a11060f040302030a0f09050306160909050403080a1805061609060e09071107090905030403170903120a0e030106080a120f08070f09 77
    0x107503200007840c098480c0c01c4800b5181d03181c041c0300b0420014010a00340b005039115080614510b40055005101e03241e100c8840514242c055154460755a8407071001c103566920441055022990480d071410002004010745e590042060300089400d0806681c06503403401100703146400c0c405054034080c0c2d03d501c280c030f02000038080141210b4860400c0303103149006610038028800020b11030207000c07a501319103005060050f030b895541d0328000d9540000ca80010825040c5030854461400d0400c80031400410940c0d00841114512001440d2a4400901031a0b80c517800001404928140e000c1141e54096520b41d1008850914150445044002e2804c040aa40015404629150020341408000400360040d82c1c45540d4040c182414581441e00500860b40041c0d0304d81d01a8200201900101c805001080010700f054500343d09920002802e54100380c000f81080d90107501d200c1c0902c001d40250480d118440d05144c120a1a10710000340802401441e40081c442e45400c64100c9074844d80c90700e401 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 670747203 1250 670745953 670745963
    0x30903060c030e0a2907080c090d020414150f130207031803050706030b041b0f09051e030d110d210e0318040606050405040506190b0a1106040f080702030a 68
    0x5140c2451801d60001d80c0111012074a402e0305242460541c281c1c0480305003e1903042d100d1000641c0d40b240503031101c3d80101c42707807078005018540c000d0050b201c0d40902036210003200364003000f5192102c0c4100792502c0a50006100300d050818a01d440e423251102025101c4890501580d50b00080c101614584c205400c60220407403180000400d100700030405005030740c120303642800440150740400082d11400034142c200c5515559441481da4050303400c0d11314000660414510541d6a240040c0781c0b04810008d081d440d05000009811a140a01002810072a103041584000d28000951541c5407000c0b500da5040c803038489140c0464500488081d245400070b18010300a000242040c0d0391030b034200f800301801c0030010302c0b0020200c0c41c007802214180c6507a55209030400e17240408002c050700005d4040c507040303168460748540190301079140102408103180e015594010069005220a0154800c0149500200c00780000140010301c2904e000d030304040c22507210710443c0000307820041071020080c0 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 670748453 1250 670747203 670747213
    0x1f050c0a080325030b0a12030215070c030e0a0308070b090309090412030e07030213150f0f031b08060c030705130602011505040e06010b03100801021210050d030903060c030e 76
    0x340e0300d254525582050000c0503143c02028182007015001e480503003a2050340308008100074800404400641e0014500a01c126550f1940494603040050019508000061f103402c07801405d1640210404403d01c0003943c0c0c65000c540745449805c950300078513100070580c10242c00841c08981040094030394058000b0009003a6041615003407a40c0e071880e00032140403e0800d060f00084410100752801280d8018002d0780c2c0c000002c0f0f00c1880105502c003c1201d10080c41c0d980401c86c0407102c603042024111711045605200c0c1942409000c01c040500800780d00c0c19110800c5c043c0313000c00304a20350000f2080e00f42e02c3d240e0303e4884090702c0c07901a565422030100780019000600660540003407240100e42c080c0042c10b561904240020b6441c0212000303203a506c031400401c00d00741c4c488000c4d6405248080d001a05980721001d46003a6409080e6071403c4501c00c10601005c20080b0001c000100001c0702c02100042c0980e40141c00b4003103e11000c2c00c44d41d601c00024680718040d030483c000b04032403541070740c13 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 670749703 1250 670748453 670748461
    0x203040e0106091805130201050a02010608030f03390d061206050f0106020d0e0d050a02130e010c26040c1809350304050a230c1f050c0a0803 62
    0x8000c0d120074816840c604201404148130005517119050080100303040170000862150010745080c1e12861141085641e00d075000201604144040c14968070300014041d524200f404c210035138032191000c01503600308004000c501e034000c0c801e00381118510204402c0d1704c461343c030301c0000d00801403980311240d401c1d102003603c1c00300200c66211034412008015045450f98817100101d075156034024140000c91290700d01e400c2184ad200d0240901c0c107110310122400d043d040d0b400b10b0601024500328142c01390315180b070030b42100c10a015070b004c001d0780c5140c00964031481c0c2c030450784604089040311b5142003560002c503041c07040e0381a2400c0a45100d424510040c034000c00c5040040c40307035401c265801d12440205807a100c09070f03c1601d451a94920b5030307000691078409500c3c103550001e031040705d141c42884048000200c0021954458440710760b1800c000c90b5103100e175541084140380701c607840340040c40005a503904c900c1c808404450f40928180d40c83d1111301d00f4242c80c050074140c0103807542002000300 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 670750953 1250 670749703 670749707
    0x80106301b050306130b04020c0d0203040f060f0f030506030f030f0a0314060a03080f0d06060804112d060c0a05010605120303061e0619050405101103190203040e0106 73
    0x62100c01c1900c2040c11503146511008540714002510b116a0000d401c01c40c0351040102500202022803009100525020203a1259890000055206009a000414100010110582079400904aa042a490312490300b1001488985001c141c00d040c955502c0101e201e64404004144038104080e00302c90340e5000f4a1890b550079080710b41d660000904107445420402e0110081c540607200c090144a8020f0465441c041950055a400c40640c0ca0074031507000d5003801405920000c01702078450f102d0a003001d080c6008207611403aa52406044c1d6038118484500c80c0401680d0340c01c400344c1d0302400004908001550b10b119648641160303100d1014080184581903206600315201210441c0642d03a145040795101c1c007040b0b840551061201844030003900b40c442403609403002c010143d61400c40203111006c41006403c644000180000c1014801c80c1800f42a451161075941450041a40040100d075502e03c035030001c49000d00e60a00301003c00074000c00c2990b0142c020010b1a80e403544e183c90300 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 670752203 1250 670750953 670750961
    0x1b0a170d0e010b060f03041a0406050105100201140411060d060f09180f03141603020106050301230429090c0f010e030a060e030f0706090b09010c08010630 68
    0x1410304110314000300038101030014401c1402c9488060959424181d01a408160a40004100b942c4545c080081100200106001c0f14415407180710001040c1d410303c420b103c0c5680d000c2d0758040035685825420406204803202103580641d0111000e800402e900c00450741f140907102d8002e8085080150102e03010700510400c03001d40b41902d00c01c104980119002c088100d210090140401010380a040b01213485a060310380380d1820b25401e83d2400500440000b40c8141d0a80190b0042c0d40d030700380a00085c5805c1c05084400300000304c1c85c208100316010b00075800304c40680010301884040b010140714041814104045504403060420030b840c00d10360035034841032101c0f9250300c00c003075101d001b4210b507002d00d65100000001500801d4520b8155661074020105040d6200d081d1009100495400401d280100001440b81102180c505881d1402000043c0040d000da2001c0c4d040a48a014196000300714a045a281d880d000e41c110849859424140144034000480d03c1194010600c0454040e08 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 670753453 1250 670752203 670752217
    0x4b08090d03090504200703050901030213090b010210060828020415030b0c0f090105030a0905060106051c02070b13031b03050a08181002070606090603031115010302061b0a17 76
    0x20707081c404441d100300c5d00010702001c0c5001c0c80b20145e0510911001c40c0c8180301501603036006040c018540041c111210048514642c041040c464070f0320800d4210303590611680d030800c15205424403284d410900380035140c0c082e1455204078025000e5444186450021440d620141c01400c01c0080d92541170100015401900090340d403641d1580c00321340c2500a01003110340c10340e400c20380203042c19140001182e01c0d901c06401445560340b6192a80c001c69824043e0364002c003820348490303588002100030754008450380c0083c1c00c2c500780b050141e030b004100c40188066211382c05ea40d00c59007442d10f42c60140c030f0003100c7c1d8034807403076104140e01000200b680040040004101d980c981140329070350561030345039400011240307080582013032000080b19a0390b5000740542a108c0c40d00840e4658580e518841100d8a5901c03d070005a49501e945a048506000c2101c040800b40680c070300c1c0d981190007190461048645001c3c0c02c5003030100c041c00c442e40a100c0703e034100384d03c4074000d44100380c0c281d42d800b1300c0d405c059 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 670754703 1250 670753453 670753459
    0x63609010504051e0703140a020301050c0406090506090a030206032a1e03070c110409061b090f06080613110a2001060e180c0d4b08090d030905 63
    0x40420004402a80704038002000f94000902c0b285e030031755841d5080040740002d602024842c0c3c1740020016602805554440c03414036121a840ba40760038401400554107910550090108000d84181c5071121120070055a4050360700e04c0d907079165184c403600e2010a6611110350301100008090350340407168002d00401000c0c401084400d4207564840d082c512041d50340741c01241d0a09403210025640400240503090001c200140004094440e42c0076107440d13458581c000d80a0442c2d900800c0d40104400024220b8290a603040b10300700007010b09407203000703445a0302c526043d6000410501141e00040b01510300700c0e4031280c44030f801710f0000e800e034030750010b0205040c42101583c020705201403050f40c1c00c503154035900c43c5080c0c071481002c00300c052a00314420414010b0006111040c5c840c0c04003c10303028802e0b1103103805c07025030010082c181141c4192004e0071910a070311034140e40d040c25944520001101d05445c4032082c2c0d80c900a00c1c41c1c40354540d115000b240030101e1070b080c90740004008040791400c0d = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 670755953 1250 670754703 670754713
    0x22080a1106090303090907020f0d0e0a1212030509070b040308030a050a0e030405131d0708010509010209130b220e0f010605090403050c0a05060c07031706360901050405 74
    0x40c80070440329008106a194041d40b06002031807403032511250b101d03000f4040340182c0d60305902c03504d82641410361400d041e00200752140707018800350408855480003001040094910a0b0742c603920500341707100c0805140e04041e10b4001140c482d03607061242200612190307420030ba580e581ca160010340c6410850f1021251440c007070014048100a0050f00700d4403c903140558906130804007000080d0044030360228506549003070210083e070a0104c0c0103004030100004048052401c0100b81c290340e0000c0c1000031507401800342a00700c3d10380d90f96104a0b03280c1402d004c14280000004203140315250030f4079000d210751080840359071416035072194882031350aa06079081018020101400c1c0d4100b8851160461481800100403d11960140c12035000e150709640c0c2d1920070782c690300c1c40c000094a5811080c0c0c1c0010f1824200b5411641100b4001f9090011150b10315041c400a141c1c3c051490007180e01542242007076400e00b0504244030340c1c5088e4440000c0103410141c003064001c0c03800301c904840502c20 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 670757203 1250 670755953 670755983
    0x801092307080d140d0f140a0c0e060a030e060a021803070e01030204020f070f080310060f020a02060309010b370b190311030702011a0111060c22080a 66
    0x1020400c5010342d0020001802105002c03001254490300c5644d02071050312003070201c1e10070002d550141d10000003103100c000c40c00f140845840c8081c8403000c0c041070a00e514000044224640011596018000440ba202d4594410000c103401505aa64011005002d01002c200c84101c00f83d000d030600e404800130124007d0000024180d40e68020700503034000f507400b0781c010401464550002e007445601098041e060241035501c01d07420b040c1c2180d046900c00f10100030403003d07150344421600104500c1c6049070303c03811346040c081e40750341003114064000c4800000080348080250803080360010090003184010b041030050740e0700e0881054031400500000c0824200d0786001c8401c4009882c0001e07040e92408001d4641452190b0319240c0c610285512641006051038000c8003451082c9010380000c1124102907040c81003050005286c21306000040c1507460f000c100c0011400c1c0e201144101e95a41c441c012a00152051881000310390021414403000c10340c60300c0400d2841c01c403031088019002d1154 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 670758453 1250 670757203 670757273
    0x531050c0a0e0f13120903060b04090b060d030908070b13060203030709090207061b0507050c030d1403060315010f06030b220f20090906030604121404080109 69
    0x2040e100c0c1c103200380c08000100329582c3c0d441603042d4000808104a5240c2c64440d42c80741c2d0503281e071000b1000455803a800030024040365005c0c0b084600011201081040b81e1a0f84264406c2070140c1a02d01500e10898100109409403d0860181811004952580c2d44c0c2d41070704c031010307400034400c40b10f02e5440302c0b0300088050000054a01809440d240c000a150911600d40300a400a2038242ca105864603603a55601002c0c00c4800078101c7e180d038549030354280c83d052030361410343c03035410541c0654012800d00d942e1550100e400b030000d079404a0b4142e600c1d203404000a281c0540521100000405a000040c00740c81098042c42280c4642c0c4040c40040440020811140d00ca4a0005421034050381c0c031244071955680401081e10b000e40c4c0000380004040152070517600080548680002c2c009805071280c41d0101c9816030160080300208080d01d4190307a01406046d106400740180105086a44841ca04400c180c070040d00039400204020b0a950420306403018800d0300c2e07805181c50088000000b58 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 670759703 1250 670758453 670758469
    0x1050c0a0e09040f1b0b0d0c02011401060f1b020a0806100e040305091318111e0a05060714060702060106030612030c0312060b0f090102012d0531050c 66
    0x513030440f4811010074429224030310000a4192501c0d6070650701d81d000b20340c14080320041c1a1800c1c1e0400006854141d03010040d003102d560400725084003002800400c0800c0d8000000f291801007880d005580c5251045a180b11291869000b03512140301080403880b1200051428452004104500429030f40c51008042c01c44c2c00740c40141c00580100803040282c20b141d1000b10f40010003010005e4a9480300b00400c140e0b00e00030108a8401c04944000a00c0c0e182c808a45a101c1c000c0c044c2e6080500e56400000d40c0003010361140302d0107890080f030600d09200d501028450300c1c4000074181e80c0b052400c00740003034560b4002d010714808280b8000d400701e800c0c8850352000c0100c503856220703020322a000352400c0d2603901c4066182c0c001552110000b007403818045024000085606503119183e940001c00a820740d840d0072008100301c518025200310f10440040b9805400c4001c5000207141c1e1501c0240154031800c4542d022001580e1511968407080404032110b12140150103845018000900300203a003 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 670760953 1250 670759703 670759711
    0x1d10060210090c030f050a1202030a080114040605060d1407091202130e030a0c0b13020616020301090b13110603060604091d060c040801050a090812040c030501050c0a0e09 75
    0x50307116800410a01eaa1079000755402801801d49446050352a5210381c02c4010024041b100c54000c0880013003044060110800c1d5002c150003d10f003801d4008000400c1d01105228001c00f0000000500586131104da02c000c014181c0500b45070303039030603002c0b901c0307005070a650706680c0103107980030005082107100d20518425034a2004100742140c10580070010828040c0e034601044a50700c00194070700140820042c00d6000c00780c0ca6140e00140300d0b04145d00311100060040017070403004c11410005980c0d50303040355401902c05180740d40303261203800402c0c010300000c1002003045081c1c1d01030242c981000383d10146e81d103105da0041031030002030358180321a500040d0340280e00300c85c00340000e010070366258000000e8050710f409003030314078400c036280149885230540d140d4074409000074050010710000c0c0030791070b8440c542c10310a011821041d03858403941d210b08184141c1204c100c001180802c9039062410000399000002030090382040c1c00120440d40c050070400d4041004110520014140011640c1c45 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 670762203 1250 670760953 670760957
    0x915150405040c08011b17011203080403112406010228051002030f04020a1a040b1c090803060102010b01080f01050103021e0d051e100506160204061d1006 68
    0x240445006110150070080c00441d140e039200308004ca0f00c200c0034400d0300e0680900f600070300007501400380068181d40e50b0350381180308510840c0040c024001800e031600855a40361170450b10641c0d86040071141c4524540c2d2511306c5000d002c0d04c4001c0c3c412003100354070b18003005443c0e40155440e80e5005a075540e24600041c0705248494004c581c003031030202c0c0a2400c1c5c0e8000c80a4035140c15408141104030b0340112520035a50b680072040c0310560504400120241c20410801404000911060385203030023640308026000c0c0780003d09402e9401c2d0400204201480080c0920100c0240c1c41d265030590001c5448038015031900c014a141076100e50714841c05031031000e017240020790800c001100a9440715025202c50010301e03900034411190f100040c41e211a103510005514180182078036400c0703158045409039217590b14140200484040d1101c02121011a10380355211034142c10008455040b1a01941c082c1c50f2400015003101160401c0c41e1000c5a101001425a5012402000b1410034064240 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 670763453 1250 670762203 670762231
    0xa0207030212010905030412140708120306010c05060702070303030f0b0f04230103050307060b101706010917062a030106030f110a110d110a02150d0509060915 70
    0x1504000964080344602c2c80008034915001e0703124030349998030a61001c0003039060b5840000c14001d01c0041050320030203200140c0700841c40c0065541d83c4041480c00d441070b624000020600030707801200c903040c03882e03441070a590300f40c50442d2010b51101140c2c8030980109091400400c9c02000c00d21499140310740007000440d150f01c1c10401d1100a10b08804640041c0b01c000540701d88400f040b1070307118021445400210340d52b549a103820001c0d282549480d5000d0b4402108200740a80c0003001030758148070a00e50340101d0f80d2940012284c204035a80946c40240e618030f143c421b441008548288030b1410a00f000581403561a04a018620075154554034910700f0700041c44124480c1c0c11a006d035100c2d9180104118108001b0b048540e4444545200810155035403041c2c00d80301030003040340381070440c20000710b5207005d032840a44407285079100030311500145100700845461002560340ca010110010130403481d21419580d40d8207030039115021103108800303116641d0702130400d00c244501c1c0c4241d5100 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 670764703 1250 670763453 670763459
    0x6140d03080903040b041212020303010e01030b130b13060b060702010804260d0207030806010e0f1201020c0708070503330415050906220206090f0105041a030109060b0a0207 76
    0x1a80c001e4080c15010041c001004006881007880000d44081d105008a14a2200d114039201041086542007001503400c1403004104100d000003080703045075040034800507540d44401c0300d1135040280c07807070041460303845000380a0140030300c01c0d0a1100c18410442000444202c40402182e402505070090010f215000080d00050104031245401d00c08409503120100169007000d440c0c0e00156200d400a65010a0300018964041206a003144081c2410030a00c0c8a4501040740c440000724268010b20400c40b24000c004030940c1101c1d204000b5400740e82e007068a42c0c00301a1155420300c074940c0f05e0f04c2500f03100442000b42100150304200c0d0000d0910030301180c0f50829680c81c800600984245014040c0981980b4050046500c12a01240070f00300618000d034004503075018a413401c10310882c65008480040e1102d004071030307600108403a01c80188101100494091140e6013150429860342d2019070001420072018606070381c1165014081c850b10350391030f800741d4000c08040704016806203c0c10 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 670765953 1250 670764703 670764707
    0x209100801090e0f4c050609060312030702070e04050304050a1a0d1d0a0b1006020a030228020d06090b0c070f141002160501151d06030102070b010e04050106140d03 72
    0x1544210754003205c180c100c0015134031041180481c0201c88084c0b000c050f0140f9441c40d1250f03546c0f020040700c0d11135050424101095640b1140b4070800d905910000c0030a040a000b0003481000b03200d40913076502036250502c2c0241d00c0342c005208081c000c1c1c4280002040d0030045c11101a200340075040c0160a0003603010210019080a1380480301c0c400300e620012400b490103201c1c0c104a203004503d080e502c1c1c10580e81701500794515502c0102107400051700036001949c04145000e0081c441a503614844002d80516192410b12400081d4015001d030045020002035410000b0601d0084c91543c14607541d1850b45005031103203090080900325101038180000b4420000481c3c0c2003d010103c0721202c00c04405442241c0c01400700d41c2150010b038000c001000000d020b420308020a858810400c44d10305001c02840065a40800c040324101e400051003d840035410360b4000781c0c1043c0310260659441ea0f00c09101c110a03107080c2c845500b81600420003a5100800f4084d842004d4100c1450041580341 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 670767203 1250 670765953 670765993
    0xe06070b1005040e0c01020d090b0a050915120f06011b0b04060e060a06170102040b040b1e0a0f12090b0703090f060e0c120d020a12030209100801090e0f 67
    0xa0365156141c007003011410740c0355481540d0040751070400412505402c0e10019243c001c40d42000307001c01064032814050240060140c030142046410029140d0390700100081414122040002c4030160110701d0103041d1211542d854060022240b200700c550b10b50b07a0046540030b180007a001705c1800351910590005108030032640d80180280c0000035441d0341c004030941002d038256200b0703c0c00d9448010a1241c081858184000d200101c4000c42c0780500d042d82c00030060085100d468450303003000c600c0030340600c061800c1c0c0054141070312881d5503903080c1c480301600c50104c0c590030000040c1d01060390203401003588210645189c000c040c0312860341c1c80107400c40103450207500403105044440c004400013482401104903c0034410007901c2100229424801c18141c070310361000040e4000300040c0c4000e500412096003264100d84c81e800520713140032050700a84202404a40c00a1900d480101200c0c1d01051590513104044001d0052541744c002d800c0d41c45012030801c2403142c02a0b0109181d0380c0c16020 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 670768453 1250 670767203 670767211
    0x12309130b01080f0f030313060b06190201140a09050a120c1a090c24130b030a1d010603150f110d09030e010c110114040807030501060806070e06070b 66
    0x215030442800d665216000d03500c00781c1c405010b42c0d002c415200d00940d4144400e0307803e42e82110080d07046113800898161240310026015007030ba5a0741002803141e40b00d08003111809031420305950f0410700b44d6000207008005030340701c01d080c2c151043c0104000d49042e000b08500141c22230010b107881d110350748584524110200c680c00600c0011020710700081c180c851410421034401700b10030100d10700085081d051a00b1441302510410040b81481c48082c04400564144540c4c80a4951203000141d207640200342c0e1a00302e010b502d04e01108008890705150000451840d007080d461600036080ba141609907002400700a0008081001c90752000426500103156000560000b0a40701c0091420003095440b0b501d800744102d468100c040181500080f040c44054028078100c04014000d4803500003070111181c0d118104202e062910350f003903043d0029200901400d4054442d050340c0c82c41c0450003420284981c03892400303100300160542e8003c915050341d020003e4419072900f40603680e52101c80300001c0c = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 670769703 1250 670768453 670768471
    0xf020a060b0f030d03050a0f0203010b03010315020f0309010c20030a0305100906080a03030515090c0919121709030c0111150408120a0b060f070302150f0f012309 71
    0x281c44410381c0d5804c01c40740f00c0005494400103000d04181428000b80c40d0006408080d00e80104010844081400c0490741125040b4030404403402e0301c558504043e1142c3c00f4070300d9142c03802000740b0101f150194045c1c1d48400e81619410354030180160152407040c00f040400d03180d0380003807010340071080c0039810042d0310031070004003402c1054031a4602d100b240d07141d420818030380d0b014001002c20150148281500300d13442c146a4038540f01080e00041d003040004180c0740c01c5041c041610195911218010b8400f8404164061036003074940800d0560001c040c141555003010b18900749200c180342030101c800c210070203405402d00e04060340c01902c1074203d003813212180d8400d88540d200c041c6d510180c418022031292048031b40d06c0c150482c010484001c05099004040e10b4080c1d0041c0c0d0750b40b04000c44098070564540c0c25210f004c181001d07030414000689102d141c4884108001000028180a620420001c58440c01d40d98841322182c501b4030b11061254010300607200e5900030303480c0c80200c1942c460074072 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 670770953 1250 670769703 670769719
    0xb030309060408030c0601120213090303021303030e150408060f0405280c0b0306030c090c1204050a061d07050d060e0f0c0f0105071a04052b080105010f020a060b 71
    0x28011034965440b903030025480b6040850013544c0d150060054500401682c1e218030182182e03a000a00a0b4040074600c03d400f503034039505541054003c0c1c050321040b0120101180c00144d8904014021100c40c3c1b0f000340c42040c0c0f000b8009030358020b443c280d8050321580e00081c01c140d0385100a81810020140080d9a54400c80381003040e05000b00602155503586140e459802c03808501c1c01d4200302469811003811017809004100d21610f0001300800d55080484602d04591a0f848464405101e50790114101c0c660b10002c000501c41c0028000103114483d1004001d41c00003510301c0c503c081c02c5000b10328403a8200d11401c1045281001041401d2802039000082c0e003d4504210703850a050040030720183d070803032408201e0601d0203841205901c1400e00341366103018419039904451071032030002b1142103981000844c0038090308111131b6109040c0311810702e00b10340c40c0091800000116010000c0081e04c45400415194402c018645a044842d0001c1442e000f080c0e407510003a14a9035001500b201039 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 670772203 1250 670770953 670770967
    0x5041503151107061410060206190b030a030503010f0902040513020702041d1f27110d14060703064e1b03020f01271401020606030f0706030b0303 64
    0x403030801080f101d807151400281c03014241e894003070850f00081c80504400a4040d00300706854002c100e039540648d0300103054074040f246000078401030210705000c903014452101100b0406802000071410395010000040172240d82e5102c0c101a44128003940707400fd010100c03151708081c01a00034041452000b003020514038151902c203a00302c01d0030340c010060340d03000b1089507010034100c0c9503441c0427010030070b409d02a2001c00b0b901519101903107070143c1102e1030340f00449001d00c802c440152003911401810081c0c03e8035a41840c3d91005078940c2c0b2212240a1280860702241c000d10a09044850460641e4111001e021004c0040330401e52082808882960915038101c4619040128000e1482104a44d00340714248121395911102c010340e801d02801e20144003603641c070b00142c202282d0900e4a03c030503030300b040c0010700e6030040d0200d15507045984e04c101144610400d00e074151404000e1b42102d285941d801c0405d5075884039001e101101d90402c0805110341c1d4402d81040429000c045c04070380c98599 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 670773453 1250 670772203 670772231
    0x61c0f060f110711091b13090c0504080d020319030908120405100b01140301050603090715030c110303060d060203150607060b01020d0f020d0e0f10090f0504150315 72
    0x290b0641d654503900008041040150951419580440070b0340c481c4032924008070152258101c12030408000032000c6001054103070040000f1000d00207040d030602c000700c0b109ea000703001a00f00c2e0048030068000d40d00b010302c902c2d100009030f6420848503106412200302551099000b071982600a942d241c1c02000b841d000003150260007401244114010320b2203e8085036100120b0780e00381c0301e090400c50304011a554031150a820b40741500ea0440b40982c0d0794640f031000a150580b603a00504001411119070907115070550300a0030340d80d02c2071300e8043c1c0900c101c2c2c005940328842200c813643e01a0f540940c0d44049002c55020319401000150318030618000580052030303c0d0018001210102d40750515880d4659050003100c000d6400703400c048102c0d00c4140350180d03c0d42801400002009015101403080d60703918003243e07000c0c1c1409000303410212011900203120000c01d001c0c401f00030014900004070fa08203403007600c9072102c09460400b105030443d5030b808104000c2d040d4040340e02d03855030b0403000220 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 670774703 1250 670773453 670773461
    0x516050604051605040b1503060d12080a0c090b031302131103011509050915030c0a0620031804020304020f0405010b04170309060a180806010602030d05061c0f060f 72
    0x1d0042d0010500702c40c450f540d851249001d0f0300540d00890400c695025251902110003101e4401910b1300781d1641d41c0c4101203140d40801c4000545801c40284644e45102e80201646010781e501d0401441040c40805003036070820810b106280c0604420000609103c1e80c0a401008030340c0b00510582003502c5003100b000c1651039002f65502c420000100400400d00302d05079847c1d43c00214240000c80f1403410b800140552401040c1e1000b40051103540742195070180200084210001c00b18100942c603294014082481d880129040c4e08485042c0002c030b100010541b00a140300140c149030108146041c40081e42028100301d80080140aa15245503201d024070380c081d12601e0141d6840300c4c0b07080b12800922424688401c1d42d03070410000d45416448203002c58420605c036007064080c101d2a20080c4840807160b50042165001d03140022803030130f41c0030008001c0f0040b0701000b48091f132a040c01f00b0803105640c012a900302086440000c1c00504000f1524000324091140014003035004260542a2 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 670775953 1250 670774703 670774711
    0x20703120e0a05040504080906031b0406080402101713060f06090b0117041a0402060702030d0816020609030d151d01061b020a06080c090604030b16180605160506 71
    0x820000c414004142c18000c1100300100b03002c503000d11060401f0b85412030b5510400000070302a400000004114a0440701200d000b07640001e0255580c5950f0f800044c500d65003601c04070f110300c26000251007010711075180d01d40301100076008221076844292030b02c1c07517940c4080745c112046529a18020034055481c03043c6d0b001030500e07281c00315404080c2e0000400302c48940f11720180070740c201c40900021600700380202c29100c081c42d02042c0603403600e0000410a00403030307500075031510404000c1440141d00a0f032850280149030f21024005d2035040081c0c3e240c4108540d8588268014092882040b80503000300240744440080b04c0400c507220f180380300c3c071341d81c00e003952251090b001001001204ea0081200424140c010f004403003040361580000d40050251142c00f0400003d400840d44040c800012110440b4001340b01c00c1d03071641e8904d086d0204c40022207040e280c401e039040300340545a001e94050000c84881466060710f440c180801950035407c07458407210a0381f103802815001500810038180030b = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 670777203 1250 670775953 670775957
    0x405150405040b1e0c0919090216060507030c0e0607020a03140a030e06030705180102030d090605090601093c050123010e01090e061804030c1406042102070312 70
    0x313103803402e9120713118050340644a80d0003920008000e240046a030075207030038140403034500120811034000084000600d41010a4882c40020f80d00b41e03407019080742048107072042d20700703103d1561201002e03421162480303000c2011400f00c1c2b401080c103140070002441700601c001c02568032a912900c4500c10300c451811019460f80c41428100181078001c6a40f20541e2000c540c4207203149003c0c100107146000705005c0c103482110300da8040d0708a80c024000e0310f440800b400420030500d096030805c40007500040d1004013240c0905800802e00c4842030042c007881079400e200b9580c26801105441403903106121005100c0c6032078454070b81204689000c3c0ca070003040d400030150100001c00d010030140411221002c0e040c01491174900d03d443c0d81100705030007101c88102596040740da483c008154000c5075418100140c8034004200000c05402c8042d2148007030250300307082c45a17800e040d540c0340d0f02d20060301c0140803d00440900c1c1070bc540440d954048545203441510209652540c4480e42c3d200c1c21035090340 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 670778453 1250 670777203 670777223
    0x50304030806041509021324081509010317041a04150804150f0905030f0a021b0a03081606060e18030708042904030302030a1418040515040504 63
    0x10038554400e05458000c10201ca08214400700d2030045944003400e880307172604586c0c0104602c191440110b00c0034000300b8031034003402104100150a0385840d0408201440407916120200d03210102a01440d90b400e10007901c0344075a40d0954403162404c2d40c12010540c0280b00401011400c00681d907100c151119058520315100c60030051f810f000886500410410812207804110200d206100d070040c00702025507001482002e42449100070744100c0d5805005440001155218803811600070415200140d0a90b0300000c41b00c414941e600006001d11a07006c080d030071003400072a81c100c0c000c2c00c035800340005001c1c08103000e55074101510019403041240792a03003010800680c11140c200f8811458500240d89080300f141e030b40740118011400f030f01e0301d00d550040007903020701540c20302c2c010b620819a1f100c17a2501c2d92440d000b5601d80c00282074000040894031481d80c00d00700701c0180e1b0180c4c2c4040382084070f07203102001808001d100c014040c801034414401003401c0307501c85100345c500a50060103804 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 670779703 1250 670778453 670778461
    0x6032406031415090a1a0a0e090d080408040e0601030609090f060b060a1715060d05060f0a0b0a180914090105060d05070b09011206080a150b01170919030503 69
    0x30b004200416200c400c1c0d601c2c40c0e82c11a941e503104040ea6224500c5600001d00000d1560380c11041096281c0f0107801400d02a03000c0345424010400d50b201d1301c0044111440340300c406100301d501150548004140000922041c0080c60585503c181c0c8540189400039286944c0c213001401e1751000c02040d03508070080c034288401c0c80018091003c24042c01d0700e010740b03400c13007002c0c00900400e4046ca0540340a0031a501117180018030001584201c40c0c020442c03a1900c0e80c4d1400c0030014034096413001c0c42038100f001c4214082c08c0c0020300501322140112600e00b44144008243e075411240e00c00d00b000e0b141c110202046400d52803040014000d0000c2c0307c106c01e031a003c0c0030a42100d0024158501c2004001c411500148000171290169412440c039140c8031801d42c001600c1d260702c09035004890b141480e2001caa204400202145500c1c060008100c08100204011040b1071008030640e0000342c1001e50340c2800302c247c0b440c05401104100403664081c091400310b0345041403076001113002800c000140 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 670780953 1250 670779703 670779731
    0x1b0311040b010e2b05010e0303180a0b0c0a030603061a0a14060304140109021f02060f0709091a0916110705060a0f02010b09091e01060806010603240603 67
    0xc8200074003e0030000384185040c03000810301422110040501007490701032160108481142c0c000c1a64850001d00004a0007620151130340c0040b11900708103110030001c403032051000202c0030400354014421002c5900d5003403031910b441d401f10607024141522800000002560f5100d0391140321410301c3c820441d4101ca03000c001c1411a943d01103059900750701a210350030707640e1400300da40050b401900201054450303540c031805440280400703544011603660302d864245800d851210a50000d07400d030341c6a5556180c3d4125800c0303040d1003075000101c1040c014801314105a01405804500c83c541440e0050501c0004d0200801103c100142616011114450503040b810b0115090034110140450609000106409019841c805409c002c510032614003c03a00030342c8211600c010103003500406113404140c5170340d5401035551040d08058a64101251a0b05c1031007001c00f40d80381d1801a050030b92030020700b18003530a444601c218510050b070742c60782c03080740e40071030010018445510041070403000c520307070 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 670782203 1250 670780953 670780961
    0x2040b033a0c0503040e1009020423120c04050c0c03030a06150c03050307051e070b0f10062106172109031915060801050f10061202071b031104 63
    0x312205202100080720000303080801918291840040b1b9464107550300250442da5075480da0061043c07910015011640720038103101c0c11428a42e00e00e11000202c041c4041c0482c240d24800a8000c070b80200900312094a80703600039903000514040b04501f0141c42c0541d65055030f1041d00d021100c503a80700c0080060b00b502d40300d0303079103d08400c4c2003501e515051510090401d210003009901000f070300140841205070b540031407840b54100d0090454840d00c0902e404941080300b82c031706d600704410306000100d01c048580303c604140c0d00660b071b42d40114905040140004403041854003e210f482c1d50001c641c2d82c480500380c240c800d08440007406c0500c0c000c2d0800c45030894035401140303944c0d4204182d100540b00062403581d5540e8900b4002c0310400e050070041c200c0c000d84144000058148240040c29800541156001d0403009213180030a440d08000c48200d03e84511403980440c2006904001c1101d456001d011828003c221020302091040c80c19114440d4503082100d0a9488088816442c102449 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 670783453 1250 670782203 670782313
    0xf1a0f06030c0415050714060f010902030c120a090506040b0f100614030601031e0204060806060a0e01110c03011b020f16050d0203011b051c0203010b0702040b03 71
    0x580989141407142d0a41c1e207500c994014103074070800f02218520140d01c80c004465500d134001003001880c40702e4194641d1a0402518028945514813002040e003154900c00c49008800300c0e200b0910f001d03050340d1280b0343c0520081003002d41030764520091000c5041400040c0c840d9101e81444c404502d045103050056640c05442031040d2081010b0900c44150880000740c40c0d8202c400d2032903104d544140c012405008030711717010020107604910503c0442a82c3e006041a5803040e02c50307502540c1c503042030095501070700c500000002d0341425804480e500456000180d042810b01b502c03074071440000400d003960103201000400001400400308103a03818010140a112118040c203590b02d59804003440c0c1c11240d0103918400e20002110800f1580d003540514000380c3d100c00c1e003074181c40341d00402500c150040310080f080e240c2c220440001c4c0c003034144200da041c0d4582c458101e0a040c0960244070081401e170280c02c2d0076105103d082e100c001d1200c1c240d42003880704181200c0c0300e50450301c1c407187c09640000d = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 670784703 1250 670783453 670783459
    0xe03210912010903121a030a0303021305040e0303060121111206040207030f08090a0b160f020609060403030213052d040e06061306052206060c080702090a0f1a0f 71
    0x40d0540003030b911411703082c00380000c0300000c14160210122580d02040d1b000c9002e60620070400002d08150f016005002d008220f1400309044540d54014042902c0c40080709411540040000840700c0d0301502000c80001600003280c844401c040d482c040403035200d545607102004000c145294254010300546a00004c15034056050103c2e035900038103078038501220700042c02404000540d01c034104200e4500c9440c2c11a40342d51141c1003914559080c0c079030a8410100003070400f15000b0605000050307060084c01101c000740015a0780f0b4908600075040000c83c40e01058150b107001480350340f8110308a020390314018041e00d200200100450704070280d4000c050242d8140700300c640c070764070f0003140840e8030010540301000c0c4201d03c800001e000745426001158026060003850680d500205685c0c4194180803504110b9183c07500c5003642c152002c948000c14900302080200c0c01410311100c1c154000314407010124001c110842480f00b545d08840c85d002010b40c5c501101542423030300d001010480c8100b9 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 670785953 1250 670784703 670784711
    0xf1c14030f044211030d0c0305040215032a0d060b0d0b1c081309050702060103031d0a0308090a0302040f02120f040506070c0302070308040b0a080709150e0321091201 73
    0x20078142c00444261100481844003030113000300702c00c40038801c603841502c000d03404114504500c1c43c041d00416003035400342d004910100d90fa16401c1c221a08980c018030b055180d50740d020381401a1030321001c0b04600e4000c010901404a14114a05800b40d400907149108101c0d07181c08010114004642040d06030b1441001c0c1045d1420800340100c22012400e5004103d490303a500d03040d51041059a1640d05c4810050301d1b0004010f03070710380e000c61294140d9109aa40001e81c10842039014141d640440c44168000054442000061940d0005101102c00540700d003480940d61f40001d403c5400900070080019000200c3c091250215400a640300d503001e40041102d04042d240c060f9298030040800c0280980d8110100a1500802c8100015075120762543d5a03107403105000600c0350802c40920010801420114904501500e491016100d10088080000d100304408640800407403143e039030103001c3c9291404248030400110301c01d42d0740d0741900564941c288002d011014074000034049281c0d02d4 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 670787203 1250 670785953 670786049
    0x21009210c0513020408070f1a04061403040203010e07080610170304091119050702040c300e03030a02070201080f37020313020f1c14030f04 62
    0x945608401d07640b054030024002800408900d00a20658014400c2d510880500081e5003803510307801c03004d60340d41d030100c8141068010005102402940604008104440021124510000d0141d41e03c180010000305440303800704034140c10b0880302e40120000b50000410407610f103184000d5040141060000e01d40700440d40000f0075201c0c043c90041c2c94805840340c0f10354040100700c0040d10300301600a1103083d1020122840540f555000500403402035007404000110316000d02029060b08000d81407500c200d030010a40342e0b0704c60b000100240b01c01540da4001141034002000075510440c14103500503501d20007400090505071f401030143c02c40300b81038400c216010303220f442c55502c610300c040082c04401c7d42c403050003119211110705590380e8502c00310400c0004100301a411124500030754440940484100500124000102903c103101031403141000c002160800806200c0d41d00c402076a041c0b0151f0145005580e00980c46000c1c1100c4043d0380d041d080d0081030150a122640c0040e0340c4440728 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 670788453 1250 670787203 670787213
    0x60801050f0411030901020a03051302031507050c01181a09031b070302060315150c0a0f050f030f0301030b0108011a010f0e0613140415120f02100921 66
    0x5009a41c054651805101c60715201d581083c210001c84200c000c2c0c0324540580700d14005c0d0004104c3c4c500180c00c20010600c20f0714080c810100e001e4015020f441401054551001d40e400e01400010800c03034108181a0102002c0c8150f0250720008003901d4a81e5085052100e02d002285071403001100f00d0b082400b01c650000401c60b030140c0040400c01d8480320a00d4601420052076500c065008440001080b0000c1c0b2200204030003440101c1340d5141c502c51000380c481450203140031a02c156070040ba403000c00f282c6400210300460388100c4c116454001c0c5001141c0c107682003144109210702001c801402040302c0c8465142c054001813000b0004004240f444512032016607101e98140700380ca0b060f5404040c4a401c203c000491702801003980e07010341002c4a504801d00e44107202242c41e076180306030a01d280a00840e1552540054640101c1c2d0038812601c04031510f201c0308568202d607501c0140010307220b1150030001c00a20362181e00300c0524044100740c0c1a04810740d4106159000100d41e00052 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 670789703 1250 670788453 670788467
    0x1020310031104022d1c05060102100e0d0507050f01090b091011030403081f080c1504030b040605130b130c0501020d081f0305071e0501050f0306062808070f020706 72
    0x17040d006040d604031403c01c864184602c02ca40740710800d0081040c1c41d80c84101c482c1c02c10b90140d0021b0b422905e4054803460710030100d41c15451901d1054025201001a0510071005032000a0080080d02c4070291000a05421103002c80021108005a030003083700840c000e00811005002c4a0300034803135500c801400326001d100c020700080c24051180c010030250711030b04401442c032080c101c0203425981e40f50a40103542c0c2c400300003036a21641144484458011001050301d04907903104900d50b0043c0c450b5519140580320051103008a1886c0c44a24030200b020503a03c540144100c039520a012401402c0100308030a16420440c155408800041480350307002c50b000d60b0024503008140038240580000e04088a0103500240461184401c0800c41d050180e04c001d0000d01d5040c06902e455a545006450038042c046400801e42c10600004069080100040c51252002c080c1140000d40d05250410070b1441c4542c40340020b1012000c06c05000d07000145d0a000c00d11900052803c1c40c038042e0014002 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 670790953 1250 670789703 670789747
    0xd031104080606010c06090b2e0b071205090907030b030114090a0609140a05071d04020a06050a0c080403080909091204090908212203080a09140102031003110402 71
    0x403615403491401d00c0003941c80b400c03c09601194901c5a4100100304048270000004800d0400620718101000b00038107080301e41c121002000c0c0c4600702021600c9400c080c00c00300f100401031110800001c1904e90310151072511840950302c0000700d404910301450308507442d052568040b452100e0501c02010343c000f500000c002c0e0f0003140421240405c0c40c160400d5401104e5560041c45104400c10030000c3c0843c1c110241d400005990800e00400700e019142c114003500c02a4000c480d015080c00040d105000900d105240350404030303c0c22400d40c0d5000843d51103070380f059030030745c50205070301720075203084e0301541d0704040a800100030b0141d241c28800c031144100d2140c50f62056850801104025130f00007038881002c008202c0340700c0b100d100e00f418241c0c028100c0d20b80803008000d0740d0340092902100c4d080d0015981542c0c440c50143e0717800c1d210400a008186c0152407602030303201240c4481609000440c491100d420621288910718500200e41c541005100c2e403085005120300c01510b0a0310740b0394145 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 670792203 1250 670790953 670790957
    0x1d04050403080402040504170d0f150b07080304031e0e18010e0a0f0912020a030f091d07020a0f110f010c0f11010c050313031205180609060d0e0d03110408060601 71
    0x5503454610b4028232003900922000c072030301d40101e02800d0b80e1001d6401404d0f2401082d100344036000114402e882250003501070b00043c031310240015000b00781d100c0041d5238014031034101103041000807541e030a54000840f01c8080001c00b8188039034050305254042790840080c0c41200e101950400e11001c040e0140100421142c65683d5649075a115030340e0050340d0704503000307070701d40d081c0200c000c000075103440d4034180940c0802c0410500380400c3d403080c54104101c50302c400104004400340076003104a5800038180d802144642000c01e408030f00000700812001e8880c031340c0c1d0240c210244050144206050040505200c2a2442c50000c100c078030355045e0f6010761146481c00d08241c3d11005803441d078000710f40603165100100e0201102025500c0303c0e0140c90044a06020801e483d030011605131088629110fa041020100d0b65442d003042c8005d0815604000c1c00710782000d0b1400c0810044520040d401d0b0550351007403800001680e018070442c041c01c0c0d030148045e0321303203800c000381e0030f50361603010b004141 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 670793453 1250 670792203 670792211
    0x60608032a031e04090501080d0c02041d030c0a031b170304050703150204091109180c0d0903180b040e04080306060d090b0f090c0f0d080c01020a1d0405040308040204 73
    0xc1d0703400c0c05104580e01005a80310300d103030400342841c104803550410301a00321aa440c0800116000070006010017542500fa41c45809822103542840f000c0d02d850403203001d044141d25008100980c0c113001034920034100300300801000c03955090080010300c08826a000890090403184081000380c4c2c014501840c100d07028980e2521140b07801850326280d135102900304c4881c00d25010300c000e5950002d000b1a407a5034011b002083c0841d002d100548502441300d9400020300c0303204030300740507002c41e401e901404000541d8200000c900b00d440c10350b00850001c4002500035400d001302103803114244000b400604100904081c10560700000020014001031b21285000c000101545e03940e200325403010811110034002d159040c90490300031030003a542f00d051a000000040d68644000820885805005000e034aa40740c1d500c080c00034004800c001507403c03030410409008c8081c3c0900041041340314a581d031911000c1121462040703451060b0b040c521450902e0b083c0808250300091032500700e50112030010f = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 670794703 1250 670793453 670793527
    0x180f1005061b030d0e1e12070f020d1203090209101d090a0c030c080606240f130e071b05060c090315040b01090f050c040e0603190b0406060803 63
    0xc0c59130041c803030452607040c1041c0701c0c40d442450100312010300821944e040c507510828800350644480104268840d4414140501e40c04600c005a0140580d40060403a014002c041d844040031901041c51000200c0c0e2074404042c2181003e5400c0d40c0d01029110718040310300d0410050b400c0c00c0785400e01ca50b00300d0000744c01103000a039050204503165075008458280341c1e9035030315200d06e0012151185007828060100001c0060601100306041d0360103040e5030340030941440e10110815040002c10032441c003014015441c10000c001c0c2e540d0090f00404144500d603203400480146040202001406c072004400280b200041c8002651604000b4100b620740d201d00958001c685059603a001c240036444800080c0810b03c20765400c00ea0603100407010511141c0400030102d0180c60090303880c0008c4071004c2104104039042c050300190002c078020255000d041380055054034107c80c03c6415240c000c08507080c40100040c5100d200c008111040c0610300344003a1100704241010500041103070014030300c0e103603 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 670795953 1250 670794703 670794757
    0x405030a030e1213030b13050d050a031e0212091203061c0b0403030c030c0f0516020109181e1a13060b16050f030304120c020a05180f100506 62
    0x82d0440c580304100380d41300e20382c80700400c0d00c02134a444152180001507001c140f4070340050884854140e00200280340004000c50100c0341c039401181d5010404d595800309140c03400c91284405a000a9460b02681360a4003104142d0501c2000e4031000d103544c81007034100c020420680941e6801441140c14228210002c001d140400c0c2e2444001049400c20710b0411042503010b6100c4c48822030303641e40402070807400b2901a070b5418242e00409012074014000b41140e0450821070008035031043c035150380c1d50781ea905004500003090801036907109440d22060700e42c10081090688140000b56414020101180030101c00d08003004201c600071200c03801d00c02003010140d0003000c0140204d15201d80e80b1a00c81d141d59800c0c50301018111514045e80080400d0b11800000380c1e4062a0807444c00b1662181807101a03650844140c001c91700001c0821001495a9801800c1160344078040b2783c5c0070441c030380340038010307000700c001020f80d50341a0201c4000e1000c1d85817882a1205014180038a210380c030340031440 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 670797203 1250 670795953 670795963
    0x50123030a0b100c060507020d090b0f09060403140105064e013306052808061c2004140709050a09020c030304060c03090b070503010512060405030a030e 67
    0x2603002183d07050510101e980c020050000b0f2401018100705c1d984418a0803a11480141101c0001915800060205400c0c4500501c0c8460428150314a00400f85e004655160000c0c0c0c4140c030800d190100d0000c1c0000c003801402d42c42042241e040303501020703248002b2800c00010900c1082500765501d804d04021561407100321410380d6880e585026440da40596010300403c00c070b003007501040800300700c0991801069046a81550310f491900c040d0a02d803044903690800290030640d41520800703071020039001002c00b0f034003000c43d54540b0440d04d000001d0000800041e0500413100010103240c4010881d000e4102d50a080d50340900d40405d041030700001e01070301d0a07224450329441c6000900801a421849080842e00e080e107000040c0c07507807003403540101d00400ca09503405800400c00140000c069500c05401c80340d00f414000b9500c41561140742e190728003203c02101180700003006000d02c0ca800d00c2c021181c0d07642000180214074056584a40701d001312420070043c180c40303003480040c0b2281401 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 670798453 1250 670797203 670797221
    0x62609010b041a2803030c020a0f0e2d04120e03010212070f020703200111010f06030c05040b0307090e07080307060507030b100507200418020307050123030a 69
    0x2000740618041d04030248100c008004607035110b4580020b18142c1c0018404021080c969413084110009140d518140c48100303903100126801003c0000c08a03c102c1d182d40c46030b0141c24103800c15080d52828007220f0000c0c08121901c10180c01a400301a002c0c607a0601d9500c0d07010f90300007a074025400409106a500701001c000156041d4000314070762589104803103e46d0300c40e4a242c0d40d0035030786181e80321060340c64040c1d500014001900184040c081000d1a481c511025403040c500306002100f030803911801c5901954400800302c0c0c803100c0820a00600251500107008116410016040c42c40c00090766011507110b143d11950b1101c0303900850040c1403004a00516020050769611191031415070001e000c11194100400d14158441215051030340056101e501c0c140c03502e80ca030010f192074021609024103404410400e10181165131621540110b01c00602000b105901c02c9a05104150510346243c0005040010380010013020115841803585141c1c20032902554a172280e01418014020003c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 670799703 1250 670798453 670798459
    0x7021b030627031204150b0303030424050f15010306082104030503030f190b060a08060d060c020d1d0604051302040b04030b0103140604021f020c100810062609010b 72
    0x2207451818540404001441780e84200040040d03a40e01c210200d040781e460702411038040d40180006000540f0324000300b05010507007081c0c000340e5200102d8807001d40f1000c030790014003241004240540c003110300c520700702416800d0900f40074103401d203070b8a15a1010b8148100f40ca070f62500d0105128030702000300b01e9025580100030380b541c902c0c0229171080d014200340c0e410b10704607042c6010440ba40025120320118400024000352508180803803c4440300000b41c1000c0c0c1c0091484032a0380081c2681c482c0d00c545103001c1d00585414207921a014004402280403000103071411403d400d1b480d42e0b01c100310f400f034a00c02c03034440b824407422803400c0c0024092034004428000c1c002602105000004003507604803071151403510840d804459040340c0341c8400b07460003500304030031910780300d90801809010042c42000d0310444500544d020300003900040b0645401001c240c0c140d0900000c4400c0ca40820302814543c00c4c00e040082000c20807601e0138864140090301604070030080b0303811490a41108062900c01 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 670800953 1250 670799703 670799707
    0xa0c0809090f070f0c03020714011205070206090c0307120206030403110105090601032f04050615040b07050f0a052d100c030b0a0b040e0c0418020307021b03062703 72
    0x7451040032442c409692060100f09000004101c0718480c1454400190b4140d0190902c50b00d447c4011201c90400d2030540e040c040c0f030003d00e1043c480f240c4641c0d8403c0c00d0a81c0202003505014200d0780c105000c40b81000c2c040c1e044080140b00107061580c0f40080c090341a10603580d42d0381c403801c00312800c001d484100c13441ea5007881c043c444046000030391a410380c0d0060164050280704001281c090408441120710445100314030741400346840d602c40c682c88440545800c00f807840300c00180c0c00f25841504400d14400300030840e001448070411400d204a01948028402011992206039441c540c40d001840e030082e254080819519004c489158409a8241114640280d412200000d0a210700030341c000649810309400386460403c095504645d01000c4003883c0030700b001100d0100303040042030010600e504002c002280180c0c410303e00e55191410302c0060300c0e800d011034003c1c180700c10780c030290740229444403000c1c03a1650040341c200d40011620820301848005070342010780100e854060140e070340c000 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 670802203 1250 670800953 670800961
    0xf09120c0c0a0f06021b03190501050109050a020301051c030e0a150f02010605060703030908190903050c03060408030612010b030607051c0e120a0311161a060102030a0c080909 77
    0x80015520142001182c070641c0c029115007241e118032541c3c3c031414006a10020010140281c6d101c10b9602d40c80c000307001d55182003141882030700303030485002049696030b40d01e81c010013209005100d5680c01049040c0c0651855140100261400b01c980311014181ca0050040e6400c06001e1040f01c00a000044d012420b410303560443c2081c213114002400c0046480e02501c1940b040c4184039070401d0b07d034000c1007241002090340b401c800070007600d60112a00b00c03007001540b2041090000c4689101c81580e02c1c1a081e608610300103051010201d515402903020b00305000008429400741c941c4a0403c0d201e13030381011a5049014058100780080f030350180101c2050190031a8002c00801c01040034000e100d44402010843d04229003110407141d0711500b0081b200c0030721080540007025012960300d4040b5000c0806c04040c1015800000e6030000c00c4684042541041404886911002104a0b440c515441c004002035140e114000001003006150344003041003003a540c040d00e01201c4003504240c51031030 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 670803453 1250 670802203 670802227
    0xc0105030609130c12060b19170a08030a060314070503030a0302030606070b07030e010b0a0f09330e011d060f010c1a040c05060f040b0a0c140c0406051203030f0912 72
    0x1709841d25414030500500e50b04041c0d582c0d04041d200c50040c0c2c030b101d91030300d045d0280e041e00c0410ba4008a005004090700426460805140919004080014010710314a80000303010810080005d0a030895103040207560340100c03c2d501e60b54000d08001d4ad40c2d075179500000c1d00c0c3c1c0c400c91800034a030400c3d000c1032003d9543d061740840308088055008000820401c004c11100c0001ca114801525100044c10b00c01d07030010340c101c54011036480b4074545411200d40b01c880b24554181c035910b841c03041c0c0501b0070032840c0c51105540c1d004060030040e9900303d11000140b05008100100150301035a501203000500382d00c01c180c03001080c1e8010705c60409442c07200300744000808081d60140e0710346103110808146441d024040300c50207000c40039118a001e2600403940129000f0100000c240811145000041890401d10581110044d800307082483c102d00104011507000b81c02039405204508800c1c0d04550001040f20341101207040b5aa10070b94812400c03c0c94030f0410a202008820301240d101c544030 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 670804703 1250 670803453 670803479
    0x6070b130201080a02131202030a0218061306060f031512060b09010e06102a08070c0e011214011508060703061d01140102070807060f08090c0105030609130c 69
    0x241c800d030382e0502181c480c02184016409010100302c64074612800c10040c0e0442c203050780c10200d2000c1c0903124880f10710340000745c500380701100d406407c41c0e2030b204020301440c0019441c8014460b03401b04210315410604020700c03104000341410705059545c1103410b09444051414402001000c1900080314080d1802d100a441c0c10100303607000c0c00010001180010040d5441031160744043c21030310b01104400c1e4110b408001c0880c40c546980001d9411545401c0c00381d4960f000d00d8050514260b03100c0051409855004260340070b280c0c10800c074001809080351051000206680011064840c190a43e0300940140072a804610240c00403080016070b901011030103522891041d2810040943e460b282071015480780383d2054500c070b000000500010301c00584508111034188100c0c5c1d00da90310b421060780b030010190070030000303e00c04480303c2d51803940c84102d450703210f00100003906100901c030001030040d010140803d40701d240301400040303944210a061402039500200c07070080f803070b5807851810055 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 670805953 1250 670804703 670804741
    0x120f050f0d020f060f07050304060e0d0c03110105040213110d050925030f0f1104140907051512070c1b030b180a03050a02030c1b1f020d080606070b 65
    0x1d07025691000d515400041004d610070700312000081566545c454049503980d00090089816079500d2154001404042120440e20310450300d0f034520141c0103007006400d410502c0b00c10080c1d80c0c101010080140c58660b0300d03548500d0b10400126005800e804e100031a801400315108038149403101f0898516000200c2c400c5890b90201c00056041600e1040000380d000c601014101600b103a880c03000281014000d04003c5004008541c440208040080c040c0c030103c001c0503c14070b415a0520001000901003007004004c111210140340c0a010100344080c0145420001c02e04c00000000300300e140030788011a503881c0d200054212568040c02640c0a02c0c8003800700342c0e80001010300107070b0704c0e01415010101001c0488000d000c6c00d50340e564100c496034400d211490441c00301307002039002850200301001d100091090400a4411110700b0b00007200701014540700182003d85905100c1500030034500c100d00c01e1403a0076407107030b41e40e080413400a21900b0b0300242903a80311410407420b642c3e40302d444002 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 670807203 1250 670805953 670805957
    0xe07032d0b1f0609030305090d0b040f11010f200715030203012916020103020904090f1a16030c0c140303090616090b160c06020303070e03010510120f050f0d 69
    0x810040d00a02c9080c1440c020000412010242440440d02a401030005844002c1c9226030a0b8025990514620703c203407000c640380000308000204000c507840010b1568a02031900c020041c00c40c68004280c61100c1d01d004e42039580041510190032001e104800c00350000f0703500c0803282d80c42c6e101c00174000e500134406c101c0102461048460300d101c9200205000061824013581850503c1d01a28541c01c00361404906240c0e0811000c2115281d9000b0317235040b24001c40c520986e0000c10b04012220756400c07107114210800d0401042101046076121110035031041c40c0010341500300303207016140701e110311001a2070101d14039005040041c2c000000c510540003201074440648604944000080d120b400010104a0703005007802441c0d0307610080c062060100c4d0b2126100c5c40c0a840310032a001641d041000141c01c000104040c99400c07407603500b0007100941c020422031070401074456081096008a01c08089032400500034400e11001c581880f64010094400d08001f8050072541c8405031840140 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 670808453 1250 670807203 670807231
    0xf190813032a0e0105010f120b09100609080d0c14030919091503021005131701020405034b060109050108070503070321021f0f0608010e07032d0b 64
    0x203001200306400340d040300c030180c44040d00881440f0042d5250301c8c0800520104030741c6c071118250b143e920005454001da0700c20142100c0f290074100020040e01a54120701c2060b030060f0304014900d544081c1004000382c102080114180070500c0550852146c240e840741d100342000c05d0103059121044400d401c40d2540c0c0001c01200383c7e14140340301409481d00c4007a40c0014108194207510380214010881d013125280022451500c0780610f805080340010301c0c0f0f1080e9030100d824442400c042014a0030303100e888a4522031010340c4041042a00281c00c415131190310f0f83c42e00c200e030b9249007030480410411100b0540d0b600d503843d100302c18018082440345405034450780e40300040504000c6080411750380c0114501107440e90084240c40c190014048050841c4580c5040344a25403100c190511429140076010415040c0b20740d403c002d072840c3d5040342d01c140e45810b80100c80e040b0300054601c01c0769030103850b0402d031104610801200071800b075a480c202c2610080004100b0040c54499481540148940e02c = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 670809703 1250 670808453 670808459
    0x6040e0a051507170a02040f08070f060311040b031602011107080d0903171033030906020d0f02040e1003052515020f0f190813032a 58
    0x95682101000140007500075a4502c45050001e1250b1030380b01c88681083e9070624240303901010100c0003203c510800680c08501030140c44181c02c20440141405001055060304250a00c419a03d081c03003030405040ea150b860145645510701a10700614407034003001e80300e2a0940d425110001300d02d680704019440d02c1c46034030b8085000d1082d02d1007503401071412030510745212a040b0007801c19903000d80a03c004200703c0000880031000041c404c6000311034006003540343ca00060a80c65180768200d00d0000040414408180d200340d540c002c050b42468040f50401c1c1c0750928800a22905189100b024107003240000800c034160000d0040f194841c0c0e8a180c650b8641c074810400301d68502004041c3e42241d007198400c0e0134460031218104612054801f0b04a5881c542892402080c2203840e000d608201e080d120307804030510094000010420151090461b06841c4070031400d05020010440140490040c98001150a941001d980c1c024410f0448998901c900b203403540c10001503251000c6c0258000c = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 670810953 1250 670809703 670809731
    0x310150c0b0c2d04030203060403021b03030403120e19060509010e04110307120e0312041a010311060c10020a020a02090a090c0e06120115050127260102070305030604 73
    0x7a403901c15034803080c583c00c809441590340901428030032101c0e6070b00c003404080b025030b8041c00325038084e501c0b03900100414200d540011250b2000500c032584241c0040c0820804140e507006001c0c8024241d01d02180407154410019001600c05d08110008651400300401c2c0c05402c00018111010240c0fa8010482803c0c010007041c0c0c0c640c001030303010b035140074004101c500340507910341071100b000024049600c040c17140d01e032880c40d000b0394460b4070781010202c1484248050031445211403616001c08901a40c10340c0c652a60361101036104900030000018900e00462042c410300c60b010900301340565403114584c00081da200d2080700c060f481488100003141d0b003202c80b841307400c0700d0f0b65002c0303070a549081c070b03010b00c0000041000f0300c00394000400c0640060011820703c038001c030410603081c2290049007481300049c141c280c44605d01965202421520120070503000404085039508910010000a140c400b05000d205201c42d080c200c0d800419090101600880918819103082e64201318410440c003403 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 670812203 1250 670810953 670810957
    0xd091a04060f0b0f0a14150d09020906010305090616020703020a03051e03160201050706060b12071814100212040608090c1e1513030311060a200310150c0b0c 69
    0x3e090b8010030039a410450400c09400c141b42c030741d40051032510520310340088400940c1c01001084281d90b9902443c03011882d001007140d40143c400c0c42c08200a00c0d00b45003031551601c000d0000c07065035030076070100c10180388200503480c0070f9a03003e41203c6440e65245407695607503400c295500f07502040c0380d802c04140b0304000141e4403105c5010a044801d0549a00103591a41c001c0300306503900358032000041101d0f20400028503992415110340301091810000040905072a000250403080e0107030310802803041c0e250141d601889046030703c030400c4100c80303400f6031510202d048031110103600400c0c0010320035000751650348140d03484010755501c40700d4007080081588450681c40b440c01c2c4080c800c2c0f90725050401d560740c4940200c1100a103800101b0300520500c41c0e0980c0200d002820b0a041103025a0061003126001401880c003801b440340c0d0454652810858840800700004c4040002120403840c1c103502c00003000442c040784c540d41c01243d0010482050250259100b80000001c681c2513089802 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 670813453 1250 670812203 670812229
    0x901080d09151206030302030a03110f040306021c0c180b030f0a15030c0b0a0e0411161a0c0d050f01050f06130e07081e0c0d091a04060f0b 61
    0x14459881c0740c2024201c00080d001e2000c0c0d102000040801046000d4a5100700d00182d03020b40c0080d40c4030b0314580c2c00201687d01e1946103400220090050000920a00e0b003900e059a038000400760f1130b0007038446410161086100c01450701800c0210f1081901d8200350341d10510110140b40394a030545944402d0290b10081c2d0310aa49c44a0890014440f407c0a90008004141e003481100c21340380d403a1107c0c3c1d18140d9541181003031110004840c10529000034807008004410b80e010720001c0d081d0312030001540035421707a030444407038540708010420a0460004400118806034140181090303021a2980d810922201e00c5a03494080422410404508120f040b40c40040c940c40d40925844c090060580002a40c0358003001000360110304044040c00c040d109096607034807110302d45841d9840413024545203103007014120000c018414501041d00803286031807a42e60000c6200c26540c6045003a60090002800b800c00b01d0000340700c100111900032040c002c0c208181030103120744030010040300c410500 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 670814703 1250 670813453 670813457
    0x10e0403050d0507050c1b0102010c23070c09092d02030703080f0403140f010b0a08030708091507060e070503161e0f0b070501050705070f0f050f1005060901080d 71
    0x1010300b031056012900919130041c5985071007820440500401c610303003141000300010b039488411540f00c06507424400c102641d4194541043c101c070040030381c08107d00708481c1d140d920300c000090030300078800d0921010004040d4000c1c10484180b043c285a80100400303c9108203818440c609216480700400340400380580040142c078102d8a0350b030799500591722a40c904186a4130a00c400408100305446071500e20801c48064108252602c0d1240d08591000c4044ca20501e69003106106a903c00825035846552024426523030b0610a00010319100010407400804440041c0700020000c00342c02c001580c8048004a502c0251103130b003010b84444034401c500034520030700300c820042c01c050f0942002104840c0501c1003030503526101c00b80310500031600503111807400019100e0402c403092155a9000d40310349842ca0034912076649040c41c40c501c1c1c4002070404090301181500740581400b502e80541c10000448000d00c0ea4144d441010f00402c03240e107403007a13001c400001000340c80450b18810340c0c0f18039 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 670815953 1250 670814703 670814707
    0x6041109010c031b030e09130519030c02040e15010806070f030f141008070602010212060f012109050f0c03030f18101d01021f0902010c0812040b010e040305 69
    0xc000441e000e0164040c10f80c1046600a0840c11450f0800e030500b494a010765211080581c1c104140f080d14400034180c02d0310100140030302c502040000c204a4421580721b07a407892a452141021500d2100707015010394094078088601030b030301c880043e43e600d81c8071005914890aa03a2510103645a1700102c80b200003088006402c1800148a40d1051003158403012002a4541d8800e850221000c0100e904202001040d0340c103010f010802c000b00001044548004d40c903200e2986c194044032540501014098244042c0703d52060f07004010900391440c10300260602c240e050700d00d40e0301501081009480e94010080503400503440804c25403948031000d0015490b00500c400008420760140c0705659074060329148500e04d59844c1c090404007001c05940b880561311000311190812060300c090345d0b05561042010b92110f108038410f00600c1d801c080c800140c48070a9000581d070001050700010401440059130002c25191298a68010350117400035007016078944801f03410050307007620042c011a04c2 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 670817203 1250 670815953 670815967
    0xc0105150307090b041506080108100c0f0c050a14010c090504022d0d060b07151a06030c0c06011707060507030804020904020a0915050103241a0c12040e060411 70
    0x3540e00560402e11002d0000581d403171100081c40090200342c7c11800008035410010070070500304220183c444801c0d0a400c0155440514000d8424100ea4142c1001d00110702140018000b051140c2d099103600b101d1580385101e1819915402130884000c01004146040350124240c145842a12100c0e0324160111185080101209012003103121304924882001c0010b00950800d90180740d0080880c062082e85500641c541000c020a0000809100b28901a214a0a281498520340c0c2025042d114203540b911103484581c940c0c07254145103901407040c54000658107021545080105050030705960134180c484608232094865048050001440000441e016180a00c3c141e50800e1008081400d80ca80d200040c0003a207510200c101c140b120180000c10281d600742c0030b12119421510702d50f401c022101031421a0807581c07405507103081c903009428000c004440608543c8402d003104105c0d03071703041421b40c03030411541c0c018010002190800c81c00700e40a400c00740208600ca002459840781000c0c6 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 670818453 1250 670817203 670817219
    0xd09090e0c060d06050a0b09010f0c02060c190b0a060605030a0b06040f140306180d050c0705090f042d060c0903140f07120b0402120709050703020c0105150307 70
    0x60340c45462581c0c0221940705200b40d55081c0101890035000501290b80e40c580000c00c4049803450344603002110007001142816a4407900781c0d0b24003961401c1400880c01c0c00d00229465002d8804441e40f90b02c142d00042c03158945000001190900c51034502e461641d0f41c5035030209a0701c85100b58000315000b4004141c1920864001020503c000b42441e82803036541c044d2400c110001e54011102040441903a92080c2024030039a41c0c8445280510f690300003040307080690307030000c41446800b0804080703040d200641d0244a01d00c02010005c201c10a0360601c5410341e2800942a10219082c1c2c0c03140900c498031465445800341c418403100320f5030166602c00c0c1c03034480c041c20312000e10108101c019800440050120f04107044ca03403500b2801807a4a001200f640762400d240c0303030400070250101c1131800002801c0308800617032049e4103a45c40c4030102c0a484920b0310b008180d8120f13101150a010400428a505602174808114508021f101d90744401c07030803108400000210a8041d0810513051003608 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 670819703 1250 670818453 670818461
    0x9051e0711030d0f0207030f0e030309010c020a05040c0509010807110c09041407090e010b0108060d11010c0510090303111612050d021b0606060f04030b04021302070f02030d020d0909 80
    0x4081802ea910380703040d03907503904111103040050382032942d80400d8200906500840d03c2e1f500309008c1c20078032417440714040000d560b8062089010304200c14001040c0c110f40300c02d00264000d200290041c04841402400513005400010341c050001d110303480040c0d2007610804104401c6501c21020302802c4d00e00000740170407008010801e81e1170f000082d0124101d00340070000040100f5144200040c0d102c0307000c00c0b4a007541c61843c0c02d41d0420003900e040c4265135442000c060b070346a51000004003038200b01c600686400c7e00c0c000001d0806c0c054103001104500302d42d000201250b100360f408100d070380048000102c0318018803010100d0060301c0401000015420002159148060309045042068620501050340d111300c01c1d84170030181c0020100f01403481041807a0700003408890b007500709685c00154061030b005500c03000d032001c04500003290a5480d0407003640c6869181803c29940c0305002c0c00d09a4403031080000480c001e1068018800c2c1d01c80c800f1030b80080d000401d584003c01c80349050b40c048060 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 670820953 1250 670819703 670819727
    0xb1204020109051806041b092105061e0a020301030b150103201803030307140f04030228060f0207050909031603090e0a020414010507030c0c0b0409051e07 68
    0x1c06a410300100e125960200c01d039055043d03c404d186501c1c50034400f4002540c0d40c003070b41d5665504000d0b10028115030050855025541d801e106845440e0308140d61031030000c0081005001c070b0203500140000724209103210305821040016012190723341d2a01c00d002c07440700340b00c003900c0641c090000c03540c03450350541d104200c983e0514020480118045180032440d6888041c0808441c000884c920344c3c0b09051900300141104801540c1145000c00c0c4c00390a048590001462a4000003225283c050303007034013614041e540181103080616900401c100200342028849810403103401d078000340c124440d03d18047e00e20b1150f80130b0a2100c1c030345030910124410180490115000c2405070300f0300400e0b042040e0010034040d95074401742915110150480c40800792403150040e00411050103c0d0030684080fa5000c0401c2c80c0c40d950741c041c00d0400700c034215001715004107a500c16150000b01c2c0d030520000781054509030350040010751210355450b1407a40001d564114011b00090001e102e0702e00403c1e5007140707 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 670822203 1250 670820953 670820957
    0x70510050702040e07081f140720100903050d0e06070e060a020f030f041505041a0a120e03031e0402090a0e100204081c020a15020d021b250b12040201 66
    0x81d080d100c004980c2491086103074000480680614222a80f0b8580199021705802396070541881c01c20b00303401031403488040700c0c5083c600381c107544582859000b00300b1500920b6004504011081d1507190040496200c00c0b114030070369091039000810070601040c0c00b0701650160b01c0700142480c1c02018030101c0e804c00114201540503024200d89882814401800404441c480c5d0f01e07916418503000344c14402105241c0800c120040c003040c013811070154408c00c080504a10b0060700c6070074003501107401c200304d00709280103142810308a18102c1c0c000005035009901c031940d1050b84400b204500402c12008880181d0b0103400000400c03000e07c440d6010f4030001743e03590113460992614440b12016039209074440c2d205503000580c0404004a0708146611010310792028100804040d150907880008512002411542c0011001e001944590460300b0b1522021a5440110b0fa0f51b0201034444840010100c25600744205a50340c500c82c141d200e005075144460340c1410807424204075044114005d000300c2c1 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 670823453 1250 670822203 670822213
    0x60412030c200a080706060f0e070c0813170106030c0503030a0c020f03010902091303121b030c020c030d031401080c060f0904061d0402120d0c031809110705070510050702040e 77
    0x4c1200b41004290b802c1c041c2c4400b04070186400c401c2140e4025603805600c540c8a81d038180140e1070f9001d00807030040c9421034807003a00c0344c0349252a0303c01018694040c00d001d0300849900f045140040d013000c001c0301c1c010044100655912410705450b4400c810303100001820341c05039080103140c120380907030742440040c000152100556011030a2000c2c20784240441c6480741051004140d4030441c0c4054109032601c06000c1d120500194800200000f8258001d050f101c1a00c24842c0c0e1080102c2641140c0042c01c6859040403200081c00804850300c10030524280707a80046160840090301003100318014100760700e44200c07848036a283da08250741302980a44c85402c0016804401c0303520152807201c0c50006d0005081620400002c2c40c07100d402d0340001e0b0028002c10500503040440303468a16050b042030400580c0d14481d10521082a1700000d03001498195490b841032021405008000d108000f110071044d103510800850596050315100000c03402c105100040c2010781008843c1803000003151 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 670824703 1250 670823453 670823473
    0x10e06030a1413050d09050105070807050c06210f01030807080f04051314100f050f010e03030c0c0a0b0304050309270a0221040b0a020c1509060412030c20 68
    0xb4025801600c800f01d000c1011450b5206001041c0412070a02440d401c1c28100f1034036000000c0c100d8010950041c00c603080109400c0c00340720b414003415584010040a043d55036811180088400b00c200321070900c0180520002501940c503544440e060301d810030305140c01d2000075a03a44000e50b109100d2400c100400f8070000074a62101c600712074036003440b04400306d000c90070341d150400d1002004048142400c1c9040d41013060b84200c107120400d03948152007840c41900c4100050f40d00300c0c000700e100c94140c400003916240180d404102c1001b0300804030b518150040d40e0381c009540780e010a490144c1141c0040141074030910701403060844080311003d115840c4d5180300d4220020003000ca882c1402241c0020b20540b0b00d1a48143c1d0804c014212240314005040581700c404e2400802081c8407901580050700c1e100c4100304000c107603440c50500d0141c490034944000c02a403108001e45084465a001c1d0510001d442d01070301821404050340e55549145403000304c01505080710300c54010740c8030b01501e4084 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 670825953 1250 670824703 670824731
    0x6040206160f0305030a050a020a0e010806042901030507050a0801060c020f130c020705041103010b09011112090f10170601050d0c0302041e0b1b0705090a09051b010e06030a 76
    0x41924025104c140e00c92808006c6030050352401401c500c4a1031041007180400c0342c0010854203d07510a1034030000c540d0710352001c6001001624a4003c0c0c40b40c400b001c4545282500640b841d0010303081e43c05100e80c3c5c84501056515029040351280800c50741c40040c81a588a03580d040020780c001881401c0314212040411030802c0581100e0700c0040d03c42d207408150030f0301046000b00400003640c041180c1c07040b00c00d2024103030106000c2c0245449000601140b00c0c1c0c0b0429034940c486124006880c03601300c04100048196011207551400703101d034111003a0081c5030030900c10011710442e41301c1401681c1e0f80c85064181d22001800c96040c40700c00e005450f400c5060380700b0015114615140142c0d56030400c8031035084001a882900109000e441d424452405c8640643e5204006d003885448200e11640065081c2030b0300d5000603810030042c000300312a982d003a4000e403013154065410b4846a03690040c0e02046d00345019100b07404104000303e080e0040c1010001158005003212001458400450352 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 670827203 1250 670825953 670825973
    0x309230405041103010b060301060c03050f04211106070b16030905010509010c0e15040e07020c0411180f0609011206092d02040e070507050a0f0b09070b07050604020616 74
    0x4190f40c00070398242e00544506092081840325101207400d24115803500800600031208004004d04100020695100442400b0300307490140c50740350502c1e44d00708945403020310645003403413050b18510740c1c42c464086203043c10f0085a4240750801d10700049960740724a88801c01c030051000b00100341d5501c2c40c29000c50003c0c8a03483c0a1a5424000708800d0000000101034071040c44000d44600100703001401040c86200c22582100d00e210b1181081e5a5034820503400c00c90003181c2250440d003080f1b0700d90714100d50365000340800c40d0701610000d051b485080a00080d103500440b115088001007180740748a602a4254030202100d004002c1443d50f2221240c1c0b06503000b4800580225030713421050034100503c4104a9111880500e023141400d10b8640e030042035200250900c01400000201042402000d000d0556440c0d0015810001c80d022441e21015503802241c4501403400303403c00c040388a684400489076002c3e04a00100310940306c40c0c00f005001e0b4044a02401c400d1060703450a40002d01c541d130 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 670828453 1250 670827203 670827211
    0x1006110312010902030114030c300102070503120a140a0513021305042a06080c07050d021c020a0b151210091a0405060a0507051c02041701090309230405 67
    0x3d01580307952401400e291802c00b0080b034a8881d8115040038091910b516000780903200560118407500001c901c980e04c04c14050411100142d400051440c040c410000000c00c500340007420086402c0e954003a100044442d0020300807001004040841c00c070140e40d80055402683c0114882a80c00300d03580080d50408002c052512141c0d118800c00c41400740b2074a958003031031141c200168030303841d407000060072a081c140520406e2295610120b042000000140e030000b03036220045902140360042c01070343c0e03145901250b9086050600000440343d101091151016034481d00310040c176140c03100314083d5007901191040d0071880081e15210310301c41c1040610042d200e60000003500d03440303d05000d001c921340c09507000a0010341038240300001d500010784503448440d400000520342c0b42c40808481e01e1040d1100311340d00064441e1800072050f0240e004000300c1d0601600c0005038100d0400303040c01c0c3c03071035031102901080c00903004104101000f121106c403e140070b004030562880792000241101d205031 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 670829703 1250 670828453 670828469
    0x20c070609030605010905040c030605092805060c1801030e03090a06091406090d020f181005040501080c0f010c0804032024180109050a03050f0d08100611031201 71
    0x380e0420500c0b0f101d00c180c1d405400701250920007803034191954450000f0030f11000300b030681c0e06c00008108500521102107043e0f0282d245040611030a00c07205100d40b44120141d402d8003810001c00c603250800012100e050310b042d4105040050201c0045d00141410000e802c1140000c00080c0e000d991502e240d103014181d96215119801d04150720140020403803503e4174040d001c01c104241c0540c0d950400442481e50480c1c1e030104124009000c01c6000a520a170840c0e118080801e0002c6188100d46580c00da410981c2c08008980e640c640c22a80d5032211520302e034021090001c002c540c2d5200c1c507a800c04041c01242c1080c0f43c075640b66070341d200b81c001c1030300d1410324448a0020345405141c00d88403101c154074400b00080880c03070040d107142103d2084d40d100149201c4900c03078081180e40620040802003000070080c0c0390a41e500c0c14000e0304d65010059074111401040d203031050b101e01130390000340a601d4038a800341ba80c60800c84152650901e10740e55180f02e2006020b03c1c0701810300070a145000e81f00704 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 670830953 1250 670829703 670829717
    0xc19090b010e1207061803030516061401080d0e03070509390901030c02010c2f01020c150601140d090c0b0a020f010b1c020f06040302130209010f0509012001020c0706 73
    0x710b0000c28041d0141550036200646c0307901040429400000e40c0ca00320800d1500c01c40354041440d1850040c07848044c1c05205c50031000c000614100085802d44103540f132074a800c46866100710070180c075040c1500071a90300041440c042214481c1080d950300803080310414200c030b42c50704e0710341410001c1c04956000c44c010070001501c90055a00d0f0041c2e01140782c82d0f0000344051090784d04090201d000480c520f40400300d04d00001e01c0180200c8000c3c0d681303000c03100001c40d07540702c680c0c05c040d80711030b500d0140102e0441041c010a046500c920818581c490340e0041e41403c043d542030070780c00601400c1806842e8000d5105c2c0110300d10000300d0042150610a0300100042d01230780080c5402e41d00c00296091043c3c0d40f07212182120142208543c0c0d0361541240c02420690f0b1083c0064030f03038040e542001c2e4001b0301134191014091800d6005220322003090301c408003602d000700c0342201d440c0b04810b880b80c00600d0502e02c00c09011f041980d401481c0c0e000c40009030a010f14000d280e80303030401c0c0d6070003070000440c4 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 670832203 1250 670830953 670830959
    0xf030f021c2001050f0a030519020a03020405040e1f150e15010f022808120f040b061c030e0a1a0406170403140a180b03090c19090b010e1207 62
    0x42c1084419030307110282066400c22021800004041c0221313904001810384400c0015000c14441200e51002031080d2800c5460700300090004009401c40e00609004510b41a080429654001020a0305100c0c41104a904407190780160015022102644120854403c3d01203850500500c105100b04a40314003001012a044001400340d4080d0312141c05541100c44000c421415150f0456118400f0416804418510b03140c510014403c1030810890001200140490b0380350003c14640198011800644540c82340000c005440302060804140b00c0c038440140c40c006801000c840302c00c3d40001702011941503803400b65000064001042c0703000183c0c0001c1c04c3c00719680051802c03c07845440030191000340340ca035a003c0c02c003070b030040c071141c00c2d40c1d0f00881c0701d100c49489600d4a40c090b0380a015076504d00d40d80c65030501029017098a0700aa1030081c400955441c0c1042c101925001460081c4040007e1400100c6002010004000c0341041003445207580d40e911210700400742188514001c041040c5 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 670833453 1250 670832203 670832243
    0x1403180105100602060c0c240103051e03161e03030f0e0604050d05030c0c0307060f0c051309050604141503010b03070308040b0f0702040f060e01060302040f030f021c 73
    0x10301071002102042000d20900d940091a5540304811881182d47ca09034462000c1c602084088031507081d00450745440c8020700c0348140c0d10304980c401c034111402c0818405000030100d001c1b01c0c400109a00920264640900f00e00394011001e0103031510241c14000b09200602d030a2403a00254082078070790a10722a40301d19849010082d00c41c10300030b0103207402c1c140e0300c007500c507071801d007242c02081808404500664030741404c03078500140301022a0781c0e0b1000c034078000028000e40c41d003c4521710700e40902c0055042c02607044840c1e100c0c030a03070000402030829480c403009140281c84c1680140d41c59190518100e0841d8995010700c008111003540b541c019400c141c20359800142e0380380280c011300d4040000841d010207513019106401c01c81038403040f00500180f03460007140c07006035205091a0462000300c0c810741c0045e00741c13007892101507141d0380c031000142e003684030768880c00030325404101c01040819a08030702c82d0810f40c4014920012402038081030807140d07101002c04d0b0b84103500c840c1c03d20343c440 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 670834703 1250 670833453 670833461
    0x61306051c14030901020601120201030225060f0203090d0309050c041404060c26070311070b0f18030f0c031b0f06070c0309030b070c06020d140604060b03041214031801 74
    0x1a280c00003c0d881c1101307400000351510010b1044502c001142e101242c11a0f0094040e509a1118052484101070051803144500501d540040d41c0ca9490504100c08440050003140d10903040b02d03008140c1d006c0503070412001007402d10401e407154000c001d584d04884c0d88034018040c1201490b0030544036070410f4103101089032280401c00007070203104011400545100300651200e07c01440c2150070303030354807024250040c001c48076006041e14800600401001002410755006154140e6004074695030010300010340c4001c0488218281d0050108031501c0420300000c2514901003403d42e030a226051203808100400b40d203101e085504110b0604000d0b00c410412103030f00080d80d01c0d000744466095100070708001038601001c3d01c1c0c550040e00107070079540604881007004d51b006404543d035425500d11400101542c94845800c54a03403408100ba918060050000f52001100b003a4030319280e964903660006a5280c0d0101441814020200710981420182d0710502d4407004102c0700d0692620480e08413 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 670835953 1250 670834703 670834733
    0xc031005131b0c230c0108040f05061303020c090603060c070c0e010801021b15150105161b05181611010e061009090f11060c0102040801060602060f0f061306051c 71
    0x816500200c0141314500090711804003003082c02e000e000340c0c0f6a030814480031050441d0107003040c49004240880a443c42c15001034244c042c1c0d00b1f45003130750f00c0401007040034803094a00f6941940302c000401c01610500c1c0c002c05010388034845070306040e40d65512903103138014241d2010505941c085510046002d40000a041d01001c21018204120f5801175940540c1d0001e0710405101c405047c01a82a900070821a28103040f0307141a442c01988034030704101c0040604440d405010b84003840041d40b41410f50400440b1001030b10307045459a0303a0790b02207000141c613800308010840c0701e00103c07500940a02c10310f800441c0c40005030080f4035064030b940c0a02d402a9002d41c003414a400003410128190142c400301195000000c80722a08540c0f00141c168000c25411400315440060001000c3d0415031004c811912a80c00383c45496a855200c81140f4900b00d405840300500326000450520b0180510944a0804200041c03255225030200b240849001c6480e04001e0500b0b5030301041c080108003203018 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 670837203 1250 670835953 670835993
    0x1104120c0e010b130b070218040606080d0203042321060103030905010f23131202090105100f080c190e0a0b04140f0402070204150e0c031005131b0c 65
    0x10700303807204d50003180501540c4912840d900c1c0c0450404110355445c01c03110103148040b0f00b00c155034242420804010808c5110358803241c802c1c1a000ea1003030340013009480898060449102d4a1a14800c161412403402844d0301c0e440032400a01051541e6905000d101c11880c440040100398154034015101c6400e50300041c0c14000349401401401d0b500c41803054101c0c910300000021510302c081e211003a4000d8510b80c40744020515408100662000c1c0000302550017158403009a903621028807603c803065001c03400c0001c101c40e02c03c8603070a015500c1e550304490000215464400300d0050400100300c2400b64000003400310340d0000952600003200b60140c941c034000700340741c2807400a070700700f10060b0394440e203001d6044400d0300760180d81c03640c0c182e072540c0707402400078400100511060301ca2020b607070103122045c0c540900420f0540d03d102d000e0300c0c8900f00041081420500300010406022a03050200713641c0c42e222841c0340d1a005d154145486036180c540c40b01102240e040c0792000d41d078946e01500c0302c2c0f = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 670838453 1250 670837203 670837207
    0x10203190c080f040f0501110307030b0118050904020d0309030b25080601050d0c0203040302060c030c121c050603011e0b0112050c0d09050709050709090518060103061104120c0e010b 80
    0x14610280c3c1c0c0310f5a03000b540c0031103030042014007860b00601608210901c2c01048101204001d151134050300455900602640c40441006824149800380d540d20302a480d0002d0804000a005081401c880307500c0600038101010400c2d6266941040000115869052580310500d1080000d0009486111504907403c0c1003c41d49400c000082c100d0060b10f000f00c04180d00c802020341954000d004940146801a151503500d44071082c502c0e41d07036030119074250214441c041b0203840703200b0f11406442280e20000040c12030483c130400d03508090030740070b8109a071556031441d0018516580649415000c481c0d110301080080300e8000140200840114841c001810141040000031403d0308440384014aa58000384040765030505070300d00141d0b6000700645a2600b402d20480c42e802054090482e03c40110034486640e0380881d01d044c1c02d4071454108a558800380061001861581021411152211215060035601c42c01c41c0114540d8410640c0c2d40842c4440500c02d0212a201d2640940883d203400742c = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 670839703 1250 670838453 670838461
    0x4060801090b06040b210d080f1905060a120b040311151b040302090a0203062407032106030317090106030314030601120f0e07170c060c070503010203190c08 69
    0x200002c6000300840d02c602d60700d0502407030300c3ea01d03403520b000912407010105800028140a0580e500711146402000c02c0c0d100c03000940140700da165540c82281c0d2140510000303500c000340100504800340c4a140d000441c02c40105012180d000c400c4156805400388640354205810003510450000399100d0030340d00000e100c0300100e502040003603000149416450720714036000341011068003403500025884141d220a0052100540d00914065841194030480305940d030703000e88004201140311400c000300f0501441001c2405007050380c46103983c040c0c103004c50b00c08100348401211003d0b04110042060020129030189810740705541c03110802d0020841d180c11070314050306103400030000c2808204000f00242103030b40705140702240000100310500c0b03500c40207c0c3c1000034002941c4c014082d0320490000044c0c0c03245281d03036040703005200b0700074221084544c41845629800461145903501c6901d00c002000d072400d200541c0320b542c906110700a20101c0700c03065419120303003290100c104403a408c184 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 670840953 1250 670839703 670839713
    0x5090d110d090e060402070209040b0702072c06040b12150604020412080304080c0706080106170c09122b08090f030901120b0a1e0815010b1605070902090406080109 72
    0x80043e9203400180d03c949540c1e240010703000c0e02c100000207421121036070511080100c0307010514041d15840d02943ca2079a01c0d0081920014181e1007144080c1603d2190f035001d0f0000c1c0c0044540050340036001040240030703a000325050654508402007654400e11000d4001002e0034100e40d04070b00102c80030741ca03092800e03001c022014200c2c1e1019102090000c041010440c600048440064000c030958802e070307a07070b510003808000d0248142004241c00c1508012013005810803180300c0c5c0100790040c2c0c20425080144a87c10030581000c040620070040340b8120a0401d036550b40460303c001d28110982c00d074808000707004480190204c6201e501071004009100e601106031034001c002032801e901000c618920300c1c0050105000141e410040c042808910201420340101030100f0094071042d80035a98460582d0303400b0500d5030440d220700e5034001070094a1600000340000032910400e054038805a0b111641403001661182d00000d50006000c5440c1c149402840010702480d40200b001501039121 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 670842203 1250 670840953 670840967
    0x304180b0f01031e05090618030306090103230106030503191110110405040c0309060c0f0212030c0f0301080706020c0a0e0406110f07060f0e0c06070609080d05090d110d 74
    0x41c00d8141901d800e84070302019041c00c880c29948454a4050046040000b99241c962006555080603180c5030203481c000500c0000031640250070180c02c03094940e103591140c0b403400300016459460300c8080741100d005040c007409068060340c000c0c8003947d81d079001840101149000c4803005d400340181003680391010b8102040740700360b405d641000070a4000701c3c0090300480d8455500004e070702511301315a00000750f60560004c01001d04c6240104440c489080050b24a910b0560699005a105249500400410300051600718045490035405c1c008006614240c3d0b4000341c0081c0003543c000c940400c8826410814801c000e84d05440d844445030500c001c000c00b8080062026003101c1d2603c41448805800c5012681390020f843d02c01230311030081c0e182c40c6010707014600304018100d061000980c3c9801d03010500400316203008240c1454103100d5a076003000b078012076809441c80e40e0117000c0c00195003414094584602e100c8c138040c0800d02082035020380034196241c1901c050342d00829140f4a42030300410 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 670843453 1250 670842203 670842229
    0xc110c03150a020d020d0908030a062111040e1e0c06030709210b1e0a0b01050703120213030f140f07090216080d09260a0e0f0d050304180b 61
    0x150b0b8940d04c03c0c3c400b6000c0d01c6003e14290956103040140f6082c00a008055401340b4000300c1e00f0310000384d880b00d810560701d089000c02e89440c4c1a454059000803403440d40c003000b80c14080c0001c0350391008040b216040022103802c03c1000e1400385044038a16a06101e180b2200038112841ca0450515010040c820400381c01041800060745031010940c11190341000003031640030100101c0c40c41c000030780d00c255046400308070044010b80c0b0085031508101d03010352544410103a481e1814604030b9101140d2004007000f800074101c0c2e00b0002c2e8404000c0074900b000140d8010300043c0d60b403074400e10740001101c8101c0b00704103046d08046000c1c40040000f04a10080f103012010250702c40c1848120903140320032401700140800c000250344c0036240c00941240041034002c1b9041c14100d90303010040580448102c00e251a440303010000d80343c0b0b0900541c42c1803a00000904607040b0481034101250311001d4080003039075198004079080061307012504450780080035001c01440f00c0c41000001c6280920101 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 670844703 1250 670843453 670843471
    0x31309090201020f060106020d09050307030812041a0c0a1d150f04081b04060e01060507032303090114090a0312020703051e0408060609010506071b05040c110c0315 72
    0x44200001d582c82082411030104024042c0c4801d545d6a68000c1d5940c804100c0f2103000c60f080b481c00050924001c140c45e070032680c001140914000784a4061054a10014000c584d18000003003002d00210340b1004552040c03030041015656240036000140030b00c41e8480c0041c900044540c10000c90352158010b17010004101d000f40b9480e061645140901c600030303038000f00f05d0752054145965211420b455844101001034504001d00740d110181b070ba0901c41709014540c0800d40800810001134820030203c044218220070040328a00c003c076002d03200303038020f0b0340c0030f1921380d101c0685c509110360801c50381c1e0300700c2c05040042c58840620361b0b0180c205d03110b1840145015078041280da0a140c0030300201c9425a034021200e480000ca1030072038114940180c040c180c03885c070800c40028854289810b429058130b000400305400d21181d655000c06060340d1000908c4112502e1500243c1529140900300b00d0620366210407004000c2c203600a881d00c0104030040e40300c0c1d48091400d108012a80c0e0020390060284c03 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 670845953 1250 670844703 670844711
    0x90501080c0f01270f060305040b070c02150703052701090e18191a010608010306200409020c0c0405041718100f0206092a01170f040c0602031309 64
    0x1030b00141d46540708031814103000031440c0c0c407600002d4040710b0110b05503403c3c48204c40b10035071103c400310105c40c000c803001000d06050700003194650f0b000300c00c000b0115200030912600c04017941000180350b000f92200b2400304002042c4050381159454034150001f202c66010b40020302c096000809441440c420154100324010114050009118020b014800000121080c91520307040c8030100c0070b1824070a9491284804e03020001c6060108200c2c1200c07981e03980c2d01c07103c2e4215103c0c0310040c055105440030100c0030340a854a815a2240500010b0004860068840c10f00c905424241101c180149100710b1400e42040009a410069003015401e10310800303840760742901c0b043d012040f200c0030380c59000e002e0102010506901c0b0b1002d54030882654265140c0e41c070303101d5401c0d071b40d404080003d6043c140442c6060800400e4000031001c560814545160b40e4501e090341c1c109031a000f650700c0900e1183c0f100800c01885504031104004200a01c000c5140130442085203160040314050f07134000c3c50b12 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 670847203 1250 670845953 670845979
    0x3050901150618050307290403020144061201021204080309030d0f320a151a0a030b0303160b0a060e0a050103020a17070b0901030216050a0c090501080c 67
    0x3c445040c0028100c0035046946858483c1c2c441d510310780c1074510f04000010451100c4101040790404c3c1c50840380d040c1c5420240342c10f200b8940101000c070785404400f416940e080108114201d144401600760864035a00f07040c1082d90912100e00c50000e421065a801084500c4440c504800819070060b0055446030312070b1200c2e289907040d4400c41c078882440600304400ca0703280015503400421444105100424004040340007440e4038400b000d101c0500c1d007444000641c1000240e0004050301e0b281e03060302e0b8140740d20345407000a646100c601c80340080c000411104810b0317400d841140018042207000310300f00003e019001d0b0b0b400000700401010815044c020a003500ca0580160303011300f00e54010f007842d52501001044c0108024070099200b41850750000030206500d0354903a428642d44400391008a084c50702d450040e034441c8407001c0c1055030030072200462030350109e50464401e100b04003620310300909003010301401185c0d40200c0c000c2d9140c4001000040c070f0003d46a084068190344500351180 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 670848453 1250 670847203 670847237
    0x50118020f0d03120b120312010518070518040e0708031207090807060c0512120f0105060c0c040e12030408130801021303060c020a2109090c020312090c060706060501030509011506 79
    0x80090044003d03207c0441d000040300400d50180d416108155129180d152111100c140c080b00282c46c1540441d81c10081c81d090819003401c1d00e0307044800031340301017040589010040d2610405900035140c0341c1022603164491a8603000d025006075003494007480050038400c031203032500c130303644124070034050a0075006041101c1440446d40c54000122015140d044c0500952a070781c0044034071200c00c00fa01310001c500c0345032540580d160b400300c0314003c10701030040105100c01820121004401449070340c0c41c484032110b9050095114511480456440340c00151b9940e0030078100790080741302039005020464079611000b00d039408881e0030240110b4000c024500a0742031103414080604000d41c00554195001003a180400e194085030780c0700d2103550396401010b0f080310703100d40c010b10040c0c100b0090004400072030300f4010341150900c000d45280603071342c400248403a4081581101d80c0d64030382a0400c15580c03d8403a16500c003080c500284000f05044201d128000703100e0144405001c512482c44003055 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 670849703 1250 670848453 670848469
    0x8160909150303110106182007111f050f0a1106010b0a320703120504050a031d010c0b1f0308300606030c07050118020f0d03120b 57
    0xc010368400308418003441d4061103440c01d4901095010030740812000741c5810051140c1c404a0790401d41d900341c0d85028000a501070f1807260314113041c039a84c9081d104034040240005001d0700748540349102c010b4100000744005c00d0003012100720008807800201003070702d4109080360903041840805654441c0301d0b000a640441035004a00d407075210b0701001140003410100217101080c0592501009451201e41d02007181c180311410195544581d400a04814035850140840c20b2090500280207007054001c1000c59100703c5069542e035100002c3d180605400c01c00c0c2283d07103013018ac0c0c4041140011000070340b80210f0640d004003114450000a4100c8095001c20994100d0380310590f42a59a039080080c0301d50403078501c0c4401c544c101040f91209074407000d0401030340540741c000080c890381d88008004498100404c10b030018401000960001102171040500c4202c00030700c140c00c00c03915070050240500301e5004860003800068481000304e608100d4502010000c1040400c8500c00580803407141 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 670850953 1250 670849703 670849709
    0x102103020a061d1509010f2f0c0a1511211b040b0d0e24070c02040f0905280f1a160219080304260a0908010f02070201081609 55
    0x940101d0000e2482107034180161313400ba000700b4000748403038411061081c080328110000105aa00088a00100244100440f0725510340d032041e900d0501700d0b030320401e80c1801d031240740448114046919904e59013840f07201c1c0304402410024410b0418010005080102406640001d03114903a4000a610180c04001056000d1440074181d41c0701e952f03854402909130001c015055209082c00281005002c00142d40441d000201d10015421001d4070803103a44544081c00003010488110700c02d0025850300e000725001d007814107000050030000c50034101d0400301c0100c800e503a212141050320200b80c4408a0040c1c0190b0480c115109413481c51400310f0000b00c0f07441c400203031580001b04110b0620007143d40749060b8040d507000d40b000c12031400801c54061a40110040000005001040118503400d400066801d80c02c103500310000c250b0844441581c10034451310000566244091100d0b00083c011000043c45484080d42480f40c1035002901c07204004202455045c000240d40c5101e510500301c0c8401 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 670852203 1250 670850953 670851011
    0x43060c060902030106170c032805010e060118200d180b0705190801030203030316020a1709040b090f040803040f060603030c02093912102103020a06 65
    0x843c59071340f251070540c0384210702240c201e40607087c0c1103401c0b401c000c182c2d01120001e0034100e40d01500510081a100d5020340c0e41500c042d962418003800c0c1d403c003000654080e00c8072100c03050755540310200d580280c4126001400120034000380d02420b100b880001c2d50360700c039280b20380414404840129003562410860020f022010004c0601503a540c100c001004424403055407400d00390f030106801c0ea0039800a11009415038000c0000801440f2411101d2032190464410703140c188803da101c083c0c00c40c907651881c036071a04000a4090710b0303281ca0301c642c9902c4881561000690315041000060b90794008201814a200007c0010100210202900e442680c0034508105194680c18000c1c0745091056080b8020041d00c0c0208114401c8002c1d07000300c03094800c51540040040c000c13100d01c0b107040c0800741002400280403411340d0301900803a00b48070321002c0b072100b0089890040d600d2804c1611408484481e400310342c132540820307400b00700850b01c150406004910203842500f1520381440c2e01d015048 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 670853453 1250 670852203 670852211
    0xb01021b0f0d06020d0b220c030e0f0607020d0e0d080a03021e1306170610050d02070614010f0b030c090a05040903020105041a061c1443060c0609020301 67
    0x10400e050740070313203945c0054403810414501c03408240000a200a00e400100040d02a103807030006445411410309008030380b030080b4040794003001c01864030581e00c0074071032181c2104040151280d810042110446898a000548400c0120108400703410b08034024203000300008240040d24003a4045818000c48080107480d07188080c0320008803a04031290110303052400324030000d541807203030300c900709021038070001600c0a455010030030400142141c3c0c4034007840010305c444018580c0501c0504002030056030081410981940c1612407034a050308a540c030600e0340d0b00140700000c0382405036a4007007504a071041c2e9848500001502d04020390703112580c41414000034404055044d0002406144650059100c2e0348602c680d441c841041115016004241e2041d0b0b4511100300b840c0d15103030b090150780598514001e2602c0541010070b010030181e1100da42c44da42d141c44400000d58255685242201c014600083c1e04841d100407585100e11001c00a030340c0f42030790620000e54002180582c2c0100204 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 670854703 1250 670853453 670853479
    0x1e0907170f060f0717070c02100e01030b090702032703010f020705061003150b13020c161d010909020103021c0507090504060e0105010302030907080a0309031202010b01021b0f 77
    0x2592000c1222074403280d0300800001ca810380301d0403800340d40110f550742c45200301e482c4941204068114010880340c2080158402d080150b219180c460070b54031301c0d9940360001e9104130380002d070a440b01c610411740201650b40c00c000f02c1d184d0102c01e488000b0081e950f4140d80111015911f090b169202c049182e1552800d001199008440c1e80140b503d54411400d1310b0555840d120005103904080c0700150681c06142d0101d0100700b100c2c1e00c003603400c5d14002e0444400020f21442300c0c01720307040381000e1103039984090340002000074a002c2c1d900c000c0001c14019147c136802002000d180c0d800607c50112065200d40c0303e001103a0182e01a40d02c10400b180706200512000c403601e002421042d1080004140302c501c000c01c0e6428a0700a20003995005c4036407200356440c0000450095100402e0700010380594400810000014815802e00d0f5000c0e40c1c0340a082c034214104000000c18071640078066a240c400054401d07600420b00f90030a81c00e0150b440700c2041d1040200d0280011480400c0c0d00c85030580c0d0721 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 670855953 1250 670854703 670854749
    0x337020d0906080601020c19120b01030b06030316230f010c030e210d021b0109050c0901030f03110f012c0c0a290a0c1101081e0907 58
    0x11211189095032a61412a80d4000c15070303c070f050a0f50258016004410001913500301074080380303284c0704501401074825944008041d64969455000c0350030344a800c1c010414411f03900380d0355410100c1180514036042c80103000d0070312003039002c20041413070803490700002242c12010000304058681000399480094095140c074028000108030300d0101c2d141c03580c0e120007401c0005980c044004841c3e81c4c001100404041a6429049515090710180d001c0040104031031100035141101680e2200200740c50a841c984581013014080d802d601840308040108046040c66222450954150a00c184062540511241003048103905e1308030960074061605002c2007601e4941e100c03441c200f180420440c41e150303c903d840743c540a20403903102510003001e004500034004440350741c0c595840d48462011030300f11454a50f4100e640440c0210310303024240c5040c4010b007004082404800d282625036441c00801018185400c56007900e071903940b620000307110a00030071480c40503066014504480c1c102a00507 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 670857203 1250 670855953 670855963
    0x51207030e01051b070b0c0f0a082a0702061608031008070815010b0c10090303020702041503080a030f0207050a0c0501090b0a0e010c0515070e0a05060c033702 70
    0x641d00c907601e03000c00600c40200c1d545412000c0b00c2107040701e03458400d043d110301c511010042d100030010380c41040042c102c0c01548004041d03560403501c0c3d004032440c0c00c1d924480895651152050190b45028442564400801c203e40e080f641c101c65441e00c5140200c0480402403142500502000001050181030118090850708a44003c81200c08250321000d003241c44102106101000009000061254002c104e0280c0800340340103040701c179074041640803c0152406c000d81580401d0340041c0a2042d03003030038001c050381540e0307500e20460ba00c1d00d196607080341e82c03003801c0d403007020541d0741c4d05814184006601180c2820741c0280c100c92400c1034600300215000700a04c80c06002c074040c03041c0041c14003c400f042d94544586a15032070212042c0c0d03c01580c4c40d912201c0221801e00600c46030b4032003c0e4850907040c0c00340f0700c00da54010112030010b0034421100d880b0b400041c850001400301d0110502c00104882a888000040300c50400c10344c04041a1608201c1159000c3c1550290740d0180b5680061 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 670858453 1250 670857203 670857221
    0x1b070809221e0c02030906030a1d060a0b0a060f080c0a05070b010e0609092802040e1606020d050403020f0402160c150305010906051003091103100f0b0a0b0d0b0105120703 75
    0x2d010444803081030002d9943c0d00c100711115801040034000a04a44456031142454034116510401400c82e00303000542042d40480b40c40440036601c1191302001e0a2a88440002e0b044504040001d07039101040580091801030078901c5907400020340d0070000340324030281c40000b40e10003006807143d41c480c40b0914030080c046074030500a407104070000d41c0c1c0010004443c0c03003101030480c941100c88100510f06165656045080c2e800070340b9080c148007881410402070b00307281800780d0794010903424100d00034140b0000c01401c0081100c24041400580d8480900c07042e0398004480041c0d40d10581808a0410300243d036002d007503011600c50009221100007100b01c403c0c032082d64200456a21031254000b01c0701c080c000c0c141c02200004550401d00c1c001d070311108005000d81d0300c0048142540000900d04940b07880380655180d00e4804c0c400c032003d8280900c41c00490f00300c462450107410710340784808a01074103115001d17450305c842607040180d004000301d501b4800755001c0030545180100c8080d0182003020 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 670859703 1250 670858453 670858511
    0xb07090513092d060b0f090906060f0103050118050a0b18040c1508061905032d030c120a12060e150406050603070c05120a03051b07080922 61
    0x585000301601520303030000c00350880c0f0101010421801e842e40070042645000854014040e0a000800d82d03030303641d09152041003c01c00524462a090b001d000e07040720151280380c14182044014003907040c0c404600e000c0d500e40c01c0000100b80c0c0d10901c003140680020032900b900499000c2404a0fa01c4075282a50300c1940107082d18401260f80300081e944144102000c03000152078600840c100f0301d44445108205c8150900116040d61a0030009092102410038003010100a0300e1118290300441241e0401c564034101660500b08011403c944a400203001041c190400180500f0103034003030044001141c124400800045031141c4050b0015030301961048850b0710740c1d20740080e040c07030503000309015140090401821a102c00d4410f954122035003a044555000300c03010203078001a0740014021401143c2c0e0040b6407814601801040c807600d01c869000c4844040220700c010440320021030350200815140c1d0741c145070342c0c140310440c0d4160b0082d01c41c16003070a2039190b681503000f00c40b10b80d4018241c0c07 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 670860953 1250 670859703 670859723
    0x30303020910020f0c150d060906090f0b0307050603090304030b16110c0a061b050316110a14061b0118020405130309031106070506040302010c03050c0301120b0709051309 75
    0x10402e0f41d136104002030000306a405012080620300f0b001000b035440602c0340c1e20b101d0034010b8039480303001a0342040c0c22a844c03145d81d941e4204420009070003807250350300540d8403c03c901c0d1460000b007500c400450060a0042c1000004501140000c004503002560845d076100324504203150056100c030340c1c40340307040005070481c1c0c480c640140c404100812250001466610024a00702d020348502c2e00480c5c554030301c58484610900414410b00003003001901d00300c50203858000e640380008001c8907800c0402e0003002110340a001e075948004e80480b41810484009448031100c401500e041201e503145141d440d42040503001075000070040600d03030a80308403403c0c4035664855003d11382d1001444005400180050410030204e0b40c400f1405020710800b8080a1a210954039450300d062015079007100103030340d16451500303442c0d4140f00d40c41d003014491124078915407500800313900300d0089180240c203001c0c5e000c010884550180e07116500a0001608014a40c2c0d040e100c1030004003130a4805407420b03410 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 670862203 1250 670860953 670860979
    0x31009020f150a0f11010608030702040e030310030627030f020f030309070b090a03060c0503041104020301050d030302091f020307030e0607120c1e0c080c090415090201180303030209 80
    0x400245485010000b0314920f04280c01c00908882c1c205030444420280924181ca4800c071181c03e0003040082c2451000440c2d5503206403061001f12032400e441c6200e0703a0018003d00015410760000b041c1107a4014074040307a000c480012519003003803254500040d01c8407204112041503000604c039a92007070f05409565010102d100d1080c0c4a00c400c885803101600007000c00e002c031500c524007030319159001070140b8460320384903941c44007113400354442440411404001c010810140307552455102200380e90039402c5500d850080346003070b007442c0da004040c1600810380c064141c03640551311007607000c07806c142c81611840c48000ba46030740c0000004d82c0000d84214141806040c2402140c220590080300421a491050f0b0201e41402e421304e0202e074807680f80c1c03081d8400402c0c04030410005600a12403080035900d0240241d180c2140f1054036401004030304104004615000c1225011a1b850400800c4203549840121f0b4600ca5003841034896002500d40030051561690183c9200395043c0c80345001061 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 670863309 1106 670862203 670862209
    0x20d1101060e0c190c050c0d11180907061d101e090e0708040b18070e0901020a14040807090f06031e110406050901030f02010c02031009020f 62
    0xd010801c0002d013421090035110001d582d090812031105036036100d5403a003285c0200310703108085060502003841560300c5030710302c210700c01010142c6009100d414170080d0101070354841c0991103400008940203004015006201031510303d0032541800b05000c01c10103000c000105410058400d920f061105440c01c529143c2d040d29071140184d04e410601c0c800c100e03500041111082208000038400865030b292280c80d0000880a440c00345107041c2500c0c035103440300c1984503128903c801810002c4200b01036000d80341c40c0c0c01a994101004084003035020141c00b460107400f0507900031000c10042640d10394000c5503007004025010a105a40b40c40d004a6403000c80403641d20400500100d0741006841350b01c0f0748084108640801906d410480801e450a1b4140002090325100886081c15a0b010345031341200694028200c402c12051220200090b105852040b801083c01104e4451107207 = true := by decide +kernel

theorem cover : BRFrame.Cov 670683453 670863309 := by
  have h0 := BRFrame.cov_init 670683453
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670683453 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670683453 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670683453 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670683453 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670683453 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670683453 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670683453 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670683453 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670683453 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670683453 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670683453 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670683453 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670683453 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670683453 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670683453 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670683453 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670683453 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670683453 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670683453 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670683453 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670683453 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670683453 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670683453 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670683453 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670683453 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670683453 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670683453 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670683453 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670683453 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670683453 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670683453 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670683453 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670683453 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670683453 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670683453 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670683453 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670683453 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670683453 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670683453 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670683453 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670683453 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670683453 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670683453 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670683453 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670683453 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670683453 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670683453 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670683453 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670683453 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670683453 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670683453 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670683453 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670683453 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670683453 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670683453 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670683453 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670683453 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670683453 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670683453 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670683453 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670683453 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670683453 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670683453 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670683453 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670683453 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670683453 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670683453 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670683453 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670683453 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670683453 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670683453 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670683453 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670683453 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670683453 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670683453 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670683453 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670683453 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670683453 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670683453 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670683453 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670683453 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670683453 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670683453 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670683453 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670683453 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670683453 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670683453 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670683453 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670683453 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670683453 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670683453 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670683453 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670683453 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670683453 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670683453 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670683453 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670683453 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670683453 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670683453 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670683453 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670683453 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670683453 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670683453 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670683453 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670683453 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670683453 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670683453 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670683453 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670683453 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670683453 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670683453 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670683453 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670683453 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670683453 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670683453 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670683453 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670683453 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670683453 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670683453 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670683453 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670683453 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670683453 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670683453 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670683453 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670683453 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670683453 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670683453 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670683453 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670683453 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670683453 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670683453 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670683453 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670683453 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670683453 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670683453 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670683453 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670683453 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670683453 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670683453 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670683453 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670683453 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670683453 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670683453 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670683453 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 670683453 ≤ n) (h2 : n < 670863309) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
