-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1524
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T03:24:00.471802+00:00
-- url     : https://prove2.me/submissions/7790176d-90b7-4b7a-8b1e-cbf4f8569b67

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 273920863 ≤ n < 274100719 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 273922113 1250 273920863 273920897
    0x30c090a0b031312020102040609030209060118091b020a08040e0903121e06180c0a050409050a063002010f090305012a020d0905090402030106050306090a060c080402090412050f0406 80
    0x304c202d100c20380c0029814589481005440714200380300c040d005046010000e1801ea100e0071413034502d44a01e414200c0b4458540356044010400d0000c0800007002c40560b007071a080c000141c41017188d500135160ba2906041c49a10000d03c003000c0e1078141244003d00840d42500100000548103015030980521600c161840c510a503100140a9030b000e9115003c1c180440170a01c00c03210392101829007155034480080500702e5a6216503402080c2c0b03d80b8107400d008044440c0e41205089550240c04440c00a00c180100307885c2400000c002d80050b40d001049a0065001d281e603048084120305103040f84550f240c642030f007515072000d40d01e440c2d00b541d0201101f1102d10602034480c1306c1c000c1d1005000f01fa007004d00280074901e0354004c091083c401080040c04540c0e00350040c0d00544405803d403030311070506200641e0390307540801d001c660160a1904207400d40340308030300d4603108903002403203054a03488030b0b10b501242d0655000f0000801804028116006072041d00920003015135a980700e000800c14015 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 273923363 1250 273922113 273922133
    0x1110a0b06040b0d0b04120216080304140406050306070e04090605070216081212090a050a1a0108190201050307020703020a06051c1518060e0109061502070b030c090a0b0313 76
    0x414400d02d1816020300100f00b05d140040d5101d80d100341545041800743c10182d26220003040101c0205c80113081c042800d540c088041c00071528244c5d131481808042c041080300355102400703070507003580c013440c00100c8a0344500f102c540310904c09000002c02d042c441d190380d003d5a104403407031400b40e44000f41582e400259402c400b4014104000030384100c80c50449500d00310320031541104c00d054040c0002c03c800b9003050104000e250b61040489400010910f42410840d031010540d00c0e805124100020b0702080c041345503180c982c002d03c815400410654011344180d040540000f08500c0f9051000c0016103e01800030007a004c2500c0d803a8a402800c0d01e00001c1ca803400c18031860490030844c44140461220014405503071300d604240c001c0c40303101e0034280000c05d0030780d002c81c242d203203040000a015031007540b011040e500b0b080d9000549441c680401d0341e071403ca52007903101881d02000081d4074041140b01a0114540080c10250310589e112001142a0002e440700800e0624a21110040001c4818 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 273924613 1250 273923363 273923381
    0x81c0918020307020c04090b27070f05011805060a0c081b06090c1206041214040e07170403020c01051b030d02090405010602071809060e010e010902040b0f0a050f01110a0b0604 77
    0x260074405d01d2040e565030048c0340f401078400c10406034a2003c41c042034040c01c42030f000d9451190211166195100550072801401c0e12542c0d000c510140d403080c0d50591454001c00c10355030043d03d9249007400380c0038111441410308009030b84005017840185018400d40d09002945600c100040c0858204094901d04000c46401d00620503000e100704c00071300c0c11000c146030742e009401c03103a012140c4001c240156441807009100d020032a01c005008a00c1d09121102203004084550328000740d12250441c081d0544815200603003d41c4c02035482080380d42c842d600400c007000240c500c5000324005a8105440c1d034001071800c004041c0c0100315000c150034680300303086c010002480203001181ca0480d0401c03629007070f003410b00009521510000148621a0807e03a440c1d14201d000300f0240c00703e040c415000b02120207007248a83e09000c03120010f8500515076180c02d01c001072201025600d400700f000004000d800c0a51f060200e51802800095014804480c409015030003440c424a0031004000444070152 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 273925863 1250 273924613 273924619
    0x14011b0c1a06120a03030c140703081b0903030f0301140f010f0c0303061a1903020a1209021521071d040c0201060b03010f0e10081c0918020307020c 65
    0xe0280c401080c4007020740304040c040c18004030306503100c0e031000c0380c00d00b04009020030103445140058010541c1c1a889000d9441d0780355509885da120700160083d041c407420790302800007003e10003c15280e1140d0007d80c06528840031030306181080045c00f01c0e0864101c2c10800d00701040110040200401c40d2500210815044400c440c0d620703c01c00001c2c004c600030010171000c00100066000416010b41e00480107801a00380c000403150030103101d05100e9114081000100c5a07a20840c480c83c0d01138020781f00c071440662030300c03068009608488401401c40d20703020f0f03038031003040c3d01081e030100da13890014101d010b11580c51001070b544002c4c80004600703003c5e05440401c60003400c045280c0c545100c51802c401801c56010801d00c100310001c9000d030050360071a0300c00309400000012042021815a0110b40c000542c2000b81e685802040503c08240d2141d580030750840c083e07026004144d1085010707410341030300300031190b13039240e070380b20028913401c80d082005407a400024008000c0d0100000c1107030840071 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 273927113 1250 273925863 273925877
    0x60127060e01030b0406020f0409020403030e03010c0f11030d0f02041a0f030601050d0b120d03060614030c13090213050a0918021306030803130218092814011b 70
    0x407126a03800100c0500c400782010014001043c20480d9540403129561174801151340c440f030b101d000ca00001d41c0144401ca000c01c1c0d80d00050f100504040c051000d09841d40d403100840030768600016070301c241307a024200303206000030030540c4503d140c40d114100b880300b000d090041c0c4580c1401d03480410608550718840e00050b09001e0425060017040072aa0300203001c0c87d041d9120b00550170184090840d0305801a4002e001e0a40e0408200c0c3c0000c41a40c0c8681e6968180040743c2d0718607080e04e001c00088100e15040c103017000003803009109070004085041c002c045003400700303a40c1c00a01040b83c00c4000880d00304400300c902008a85006098900502105ca40810448100201060004884050081c0204205008101500300c254000790085410550481d92441c0c940d40480624000c03030000c81c424401440c0950358078420f40c000900c140741c104d0062052074403102000c200c45006a5100300b20100341c00a001c0001c4510480c221110311541c008142d9803040181e01f098110030b48422070800c50b80c = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 273928363 1250 273927113 273927119
    0xf100e0c090108060a18060f0c0315030c0b0f090316030b0106080601120b0105090d06090b0c071536060605030c06040b0f04090905030d0e0303040f030e011106012706 73
    0x8a01c02c0d400c0346048500041c1c030a00564500c3c4103101540001d0406850000044080259034111000d49c1c0540d40d0104200f03c610490103442d80554007001d001e0052101e424006640080000c0c480006486e602c2070400c1070100003e454880070681c0c2100030241c2c41c104104004a0f502d4180c007400550401d00524070b408030000748200002680480d5254407007462207011b03400381049980410014101c400d260010f400d01c840940540e2404842100c61000000d580d100071f502030300c01d8168006080c00411036449201d202404404e2509d80c580d80c0c9280780a03440c0d210404911202148216080200720003905168044030f540d42d002500a82018400556907901d40c4200c03400c0e0f034004049030b42c4031a0350b0f00e602d981c1c0303001e00d03040344808510707100c030440610030300001824030400108814840d6035840c0c203503141c03680000e032401402180a1081400064010029405020301c10f1400c061010b040d203c1c4140b13000c100784d1080030318001c0d0141500081c0b814000600d020004605d0500105203 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 273929613 1250 273928363 273928379
    0x507081204060f051b0715090b04082a040914100b09061306052e050406050306090403020f0a0b0603010b0105070b0c0f0f0d0b010e09040c090e0f100e0c0901 69
    0x10f840808000708580041d400d072001d0300081c1c84000c891420340441d0f2420b0340700c0c912201c403104032400303140c0422445a40001c00d07900705030894080e1164540603000c690006c00042d0405c0c0c11840b40c1c01440c00c0c0441482020b41c0b150302c100c030746032401040402884440c00502c242040703600d0544182c0380e420f150142500b40c0715940c0c0c03140c0009054030034014003a0748540700c90040480e03400c4540d0000e6098007018600400b40031128a40d46601c1400c0d600c00800307041a030f1702c2d1041c0c4c03240c200800e0702800001ca103454146c00740d41e44a4040d00590b880c41c11300241345402c040380c103281295021034000a110780c40c14244220448444207013803a610b85440c0e91107040d211040145903035600f00d40010300c2d01d09a1015401d82d030b001c583c60100261030742044040341010b01041c6072451300042000b50304088903c0c00014003409150082d40c3e142500b030500110101a00c0744004251942c0b0800100303071100321040141e070b0070941c0002c50008000c0054400c00d4240b050510310548980300440041c03203070391 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 273930863 1250 273929613 273929627
    0xe0306061014071704051206070c1506050310090c0f031a041a01080f010b0904030f030f15090605040f0c081620010b0f100909050606090d050708120406 67
    0x1d1568103050042016a5203000716521a025000308040384400e00c25056010350380c05401503070f01c2101da40c030700002c55041c180c2d60750b20111b40c4100000e9510b00e50201041e00d490741c481207040d130000d02207059034888012915206050016265540d80d4044103c107220522107c00042d00f17007008550711080c42c6443c1e042c880342c810301108030340284600101d01003102c0d074201c41a0780b181031000d10b0304a682d40c40030103444011207014400d0f194203102c0f6400c0c41d443c04a52862096a1540b10040140c1424100710010542c0f0781281c091141d40c2c1d00803252242400a41070001d010044011a00386d060005020960b424245003842c41800c004885400b15000035182d603000340e103070400500050b80fe903422580b1010107014410402c00f41c1c0070071042c0b05019001101c5042c0c040c1d41980e80c440b4000d05103d0100103072008980051242e140c2400410b00c0307038100c150815002014a41000a18800076032811100001161240d010400030808079400f4131418001d5403139540036a04052600401030094 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 273932113 1250 273930863 273930889
    0xe0105010e060c01020d14070206070e0901030b1018060303110106050f091315020d0c0e0109090e01060810050f0718140102010905012408010504120c050f0615010e030606 75
    0xb2480821140e0b01071400350f044d80c4181c81d404a041c09040305003642100e180100782d5600b0014000e0100089005001329200488000b01501c2104903030700e50f8848940815001e041d98a500c1485000010f40d0615041d001036150514040010305524524000d40f8541c140d1003942c103180d041c208200038554644621040c03008065070038400c20341d5406540901c542c2c0048000b042400d5903d406540104143d01803e0b810242010801008820400a840c203c1c03801030028000364091001f4450b001880c0c00c41d1185068400010440070f484014250034046240066014941d859082089407070050042603001440f40c1440031703c0d1200b41440b134000c00c0203802048000b000900341d022940c1d100b5440040095005402000802006c5034489104010500888003030310702200041022030042c0b00d668000e80d44030354600d00058001d68240c81e25003100100b038406019080c00ea130310100080c85003922446500c04100c01c5002800009000c080180290364000d0f4000c1e41085842e490350f003085510 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 273933363 1250 273932113 273932119
    0x7020f0c0f010c03140a08010f05040e0c011107080a15060e10120c0e09100c030213050910050a0306050601091d060d170a0801050f060702030604030c031202220e0105010e 75
    0x14800e001d04050b24000951401d00100c45000a00b903106e0951100c1d032070303040e84c0c400ea40d2403500b1940d800411054480c40940e49295802054541060f91300554130000c2d11080041510b20391592245040d01b0500c541c0c00c1680c4104031191421100c0c0c103184a594040d208111034003449003442000101000200e006400108040784840c40c00c0c410300f900d030a001014480140003089c1381940388607842d0b8112801d50035400d0704082c030701030980780203000703545001c0443e000c0340180c50b25043c100a100754020741001002c4075800380c00f24443d19240c03103440240d4003d01c008140750910100040c5030211561268076611101c0890b1200c60040c0d0a0b1280c20a108441c200076441040c2400801e000d285180710120b00c10000320955600c2d027202c1d060381200e10407200800c01e180d1a030140a814410a000258160040400900080e028101202c0c00f035009140c255484010101200200c0e8000002d0350a0a92011039800300010f04401100142c1507030108403441c0d501d8000013804242180b180c20348 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 273934613 1250 273933363 273933377
    0xf0b0c0304050a09020901031a0d0f1505090a031d010c03030c09150f0210060b0301060c0f0c090e060702010e030d0209040f1a09100806151801030b07020f0c0f01 71
    0x300180c5002e81002880b60f140e866403070790254000d5105000ca140840d0078940ea241c0041102915000e4554010b8945224180583e41d44004058164011100c1c40000f000b000034a0070288145441107410b1002041c540c50b0505014040d10020700303699100e00301500301c00b480e40c0d910000207440c4981c5410007054550340b460b0103072020301c0d81c0d0700406604e0501069100400e503100070320311904d4070b0b1502502c240c0002980d8a006481c52070061414560301003004004403446207000c0d03e9480d014048240d40c2810b1541d8400555003640d2140300c0c840c0c0ca6240d1503049140c107000040d0440c643e03000800c80c0c683d601811a03100e02441601d111900d6001c1a180300c1d989071900050510040d1280410402c203520314030100005a110019000e125000001b54100c081501c42c0000c1e240e4640c01401540d0f00d00780198012040644203640041840346110688039041541a01a501c2014500803c6c505440024034284041c5860310b04c0c0da014060810040d00c454040070900c18080c07030304207 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 273935863 1250 273934613 273934627
    0x1a0109020c19110315100b070503041505071707110609010801060305090c0d060e01051e040602070309050607030e030c0a1d040501111903060603091e0510060e0a050703060f0b 77
    0x2404241101d0701e0150140214a010400c92940c1c1700300900c44c4100700340302d02d140c0361103c41c06021801903401c020820f03031082109001740409240c140c008010189002d620740364a550382c0b103032400034070f00c0120000c0e640803030240c0030000c0e0400c50007100131003a9161030034400144002086842c0600c075940c24150354202141c0e0102c014082d0b00348102014046440c001d18034076001000700041c02e2510f400b9485e250108a1404901410300d01c0c582c1804100a8103444640301c201c001d512054044081c4203d0440000d4191241406807a205000352100180e030341c030352810705040c405618030651042e41d50100c2406403440110404840301881118101513035100d1a005004240344040c0b0b189545004c28800c0748045100750a1001c90f02c50b075400d00410341d90720802d405452400f607004148000c001c0d82080b00d034590314004a0b81324007580807030f40340411005021044a045400c450714901306101000b41c071103511b001d41d0780c0020140c981000220300d44a008110061240100220600001148 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 273937113 1250 273935863 273935873
    0x110301060b0703050c0d0e0105040e0a0207060c050909100b071113020c074b0905010b070b0609040f1e050105010605040305010f060e1306020d06031a0109020c19 71
    0x580207040c40c841d0195a030403a07800d000d895a0003115171001c0380c0c4907103820300310624400d004485504031f040e10361034185810082407040e00f210042c40111015402e100c9040402d0b10f80c005c510b442c0e00541c441c03a82d520600e009000c3d002c24010f00e203250242e040041049001009800c407402c60340c002c0c103024203070351842c0f002a038810700c90820002c0d541d0001c550310741e5030b0314007050701400c450326a0282c0ca9000031822030352020108141c004100303010314901c40e490705411b035290300307004140346405410503076107880078481100c03400e1704091020b10010405070200804e6142c12504031004039658030084ca0140e650701480c2c1c0442600426902d20500d4000b45000c030400a141d40c981d00400a2040e50b0319120014441e80251000b034901c0c3d820700c1014440809103101d520300f82e84042d4600b03030955031410b400d604401c030469812034010703a00704004801902d191003554041d61180003140400c200c4055881320008040c0c0040c03004034810094155a50000542e00c48a0403a181c0307601040301c0c040c01c00e = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 273938363 1250 273937113 273937121
    0x9190204090b0c04080724080c0904140703150806061c08030901020315060712210f050103050f12070209180d0f0f0e0604031502090a080c03120a0804110301 69
    0x100402d2680715005102190b10030750050000d0707900100485141640c4d44d00300310303c880c601d4004241c2c0031400540220546205000d110751010485543ca454610b01e40040703800c407140101e5004c0351b49d5101003402641e0780e143c0281b803003103c0156209407500341408803441d00d50307078046d008500c200081502070000340703440346252a13100c0d0002100d60303c03880c05c041c200c0c1c040c1d44220b5081c1030301a040d0a6101c001d00c0c101055070b0300c9075045141034100142c0444150707401d0440d0741c0158a0304840c00b0281d1582e10190090403080204440003181951444c03070124500788500744400d1094201d005440002084201170311007807a011036204c015522103542c904001005428821014055a14111207640d008140d4141580345070b669111403040707090040714a0020fa0f960300f68404810042007021400c0744a444c90518a030707281c0149481c0444000950002443d4010300458200107001000c0d480d082c0300d031510080350f0940040c903110300c2013002040f00c540240000d0841070400d08556a5440947c0 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 273939613 1250 273938363 273938381
    0x152103030f18120306030111040308090906030f07030f0c06030603080a1d09011d010b090f01030504060f0c11010e0304050a090c0c02040c050417030909160e090109050a0b01030509190204 82
    0x644051024030f5041002d154012500203000e9803e1030100740507450400211405c4a0b0041c8003542000b40400402070f038040c0242842c1c4d40b5100704044070029400510850700198401d504180340b00b074041c548040300c1c0d21a0383c041c009052400b402007000c101050200c8144623020f01e0806681c0840d40c217894019003904243c2c64100038000d00202d010258088031403103800c000110031501ea0b070f07a440d52000c00c0c860302c488203420418510710360007254000e402594002c0d204840119403100010307a440210342c0740340c5030800005d00e900b080c13a148800070b01c034487c0c1600000c4080d514260074040071800b0f121b070300d100380d07110241e550640c6c50403c0d01c6140000000d0323078010803e000c2c80c1500c0e180200150414083c400003200050000b1110400000844c0d00751080134003c2034040d40d03080c0c5100b4003070308040805018404c0e00d0380044055640c46584034040c0024007000205414a615a0001c8540000140741070519160038030140329000a56a0b041d040c0c2c0380400c21040282d44045406441a21 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 273940863 1250 273939613 273939661
    0x100c050a080315010e2e0507060213051008060108011214010614150c0a0803130501110a03050a0b0a0302101103030a0e0609030f0f0702041103152103030f 68
    0x2005011a62500c8502650507280076a04c00744072058040402c004808040c054000c5058a00d020451aa60703407020000c0d0808241042408d00029854030710a9038401403100002d111500820b0103945042d480c00f000c0c1229a103400c01052402d440081c2110006002e548501c44840850b2810031614030703482c0d00070b0280407009000990b41c03403420403101011354481502c80e4a21042d4101035407508000c1d070740b25240e8180140880304a0352902103450f400541204800c1e0000c408420103e1000d02620b03190741a00e042d480c0d56480c510b04010308840001c2c0002070302608206959007031b03131348020110040c2c2c0e40494110f180004120004d503014082502c040316a40408001c1100c01001580100d0f0850070020643c1c0309982d82d110080e40f42e200d10040031000f818103000410011040c00041d200712440a000080c0890718484241c206400031605103420481c400f48028850134039055400d12181c1080881615020f4102003d0f100c0c000103194510202d00c1000041c4003081192003050f83c4d820713003 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 273942113 1250 273940863 273940867
    0xa08090f120109050d0302070c0b031005031501030b0109020403020d170d090b06033903030f030f09010b0604060c03031505060c070801060b0f0f07032706170402100c050a08 76
    0x105640b400f9100045040d10035020f9040c070340f074445000b0b001700d840b070507403000480c0c80c1181030106164041c0c10151081a060924100108054404011110090300e402d0f0b480c180740e41c9107262000f0f05500580040d107900303005010400040c0c41d2140c441000660240259402d01d03030008086c0c07000c0c0280d0031544051420580100141f006400d007150050005a090710694140c080d6080000d20030003146000d00c03d400101c2c3c00311b1260442000b1690f040080641e40f601e40c4030341103144250400d45201400424040901145041c02d10078112070031b1042d81c00b9030a1514212001e040c075444000040d06040e2601c0c00c1245884070200100f028100081c1820703241c84003092602d60f100c400e802030120f40c2d80b0300729010562441e54801e8801c86a07148801501e4141c16814698240e080301d041141485001c5601c07102c400070445011161040141445401501e0b100b0000c00a0001c950f1680301c07a010300b0180303c0135031944034481a1420607401c0103440300406250003850300302c02c0040038184c240c1c0 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 273943363 1250 273942113 273942139
    0xd0b0301051501020f070303090b071a16020d020a020609060c0703050f010c08100b04150e040c02010f0b0901031e03020a0515040b1807060f02010f0e0706020105010e090a08090f 78
    0x2d0220740108004207908982d4940282c0e1a5a07560303002500014004c6041c1d280e04018031000c2000421039288201d080601550018109404100c0f0a4411000c00d000500c5c4040e07426034100800c103602100ba2004010501942d00416024840e07014040c0c000d6400281c0c1200e03c00003008070200860303014048505145d100c40e01a4001c0040e07106100016042c0d401041c0c0601c42c0415030426a034082030700510745807800e0b001d0714501903420380c0c1c1024400207100c05195940d0b40c0c8654000c84100380c0002c80d03804801c00521040306c83d00030000b4421009600140081440303041101080030341440c0a202c1450542816450045120002000c43c4504808901d4202c1c1c01c00015018500c0364212501945a80003d035603d80d20014584c0300c0c9501c15a0300b0041c40348031b4040342030800c17410b000000c0c4689101b1100010b542240305050740c0d990203100c1c100300e155824440e603070042985144e40d9402e0b00b05050100d440b628069009000b494021807044083d56a0100e912080b02000b0624400221 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 273944613 1250 273943363 273943381
    0x604111203090a09022a100b041803080901110f030a0b0a122d0b04060f15090203040507050904080f22080c01030c14040e04050c031203090c01030908030c0d0b030105 73
    0x31080d003540d01d00c4190303940d40406c95126414221441d00481d00500703801003104644c18018208004e00c15403054548907079072a0240081500720f4400c5c040c0e51031000380c1c5003805519003941d86500301107c0a00040004000e0034910209031783d0490181340b008502291510006401c07240d540c1c01c80c440e50300d540c407000c00c200511b2445007225041580c001003101808200f1070f445003441038002a103524807241c002000200c807940700091491046100052032800e0503504101110650045806030758004123000504c0004c0000300000c044c02c86035440640303084d69031076040e4004c1c001c255240503c0401e8411007204112650081006a119409003083d90b440d2002c0d80c03800c00415040c00b082c9041600c04d01b50b031154010103041240d401405181c18030b441c0d5001e428180007402921540a4414081447e44d0b051045040300e8030960403c41d26410910b441c5810070300e5141445060507c0d103000030700040c0c840002d4941c8030802c030442688070b0107801504070103443c0b00307006a68554a8002000300080d = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 273945863 1250 273944613 273944617
    0x8060903040f0503010b15091813140d02030415111207120206041113021c0203010f0f080d051b0f060114090c0f0a2007060f020604111203090a0902 65
    0x80190855501c0580d80d003060500300c6d69a41071080c3c1000700150900c80101c40a80240800750020b815070f0f02d42d00c1201503494501000390341582460401d50042d0090050035007111080700b207124003a001004200c8800b0b07541e4403441c80707800d4101c44504441c603512800f6110005001400d40282d4079022600543c012080e0311940d011101c03c40000001070203544005070701840b0385d81c4415014440e05000d010000161049100c04408a8003003090803846100401514101a0a1040540c0329410b00c0c0c182c070340d022542d412040c41042034240c10003410100184158101c03c0c9428040e5642d42c0501e0501110302010100c20414802d00e817110000f0007000030801e040740e02408404020070f0100040280c400c40030b40d1048244c950520205000c005010014640602c0074200502c0807040c0859442d140f0346000740d60121900a40001c11010b03070041c64448400d4241c5c405059030740f1740755454404440304181428000c2640e510302c0418410104119038005074000d1403000b0407656081c000f40030f9 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 273947113 1250 273945863 273945869
    0xd0308060307090c0c0b0108031215130603060e01060e0f0703051e0403020a14030906090405090a0c0806070f050f0d090201020c040f1b020a0203060f07050906030c03040327030b040203070806090304 87
    0x2601c0b452000290085000c41512400ac6c40c0c40c3c85001e2940f00d8005144520540c4d982c403c2d0302100766000401c3c3d8903d81e204e0400207600c181800714003000c019030611308481c0c050b40102c031030a20b00d078100400c0100d100c284551010f1a404c00140301c0c2c03108401c40c014988010251401d5502580030702040c10b4000401c9603001344100510000920320b440d00ca0386070b0140b01c05140d0400d20600c6040380d94a0560810366020136000b0440d18030f028580c4508502008540c410f05e0250002c500b440081c42d80103c903482e00b04142e0038950702c1d10200801c8a02580306148500d045180d80c0c11400c001c5a100703000c2c00000e020010002c0c4071207220b80c81d102d40144851909640400162412120498004141411034a40040240c40fa544e10401201c9441e400100000100101007004039040e64443c0091802140d407c1401c588901e414503025102c0e03039003245100141c01d00c120346c860107100c12130b084100703580d4860748262082d2620310100b031600200b07801800c418080c190800100b020000301130011 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 273948363 1250 273947113 273947123
    0xc060911041409011512031d0d03050408011107020109030602210a0b0102010501150206040b130c06091d0103020319030201090204020309060906160206060105072102030a0306090b0d0308060307090c0c 88
    0x20a1000d800605d4041c0741510682c008a44562041e00100c0d0080b07100788240883c0703038600b0b03100a240d03000003a06030040a5003100840d02c08241032101160903c102a0542115001070303180c45550340000e00030344d1545c44000e221a0b0001160402d40035003c03000443c20b213002e804089a4184510004040c00402e0320690041d8605400000c0c20807030341740c0503d8800701d9034005c2d01c1292520f031104010381a000b40305500258014805400017201c5411100007050190740b0341c0c803094144242d407070711582c0000c201000003c46200501c096a40421018100c017503003005030030301d003201d89001d1b40500000c45019510500c00300c104040e440e00400e03403a1040001a054820039920051128540100046c03400010b900c454001440c0d0b5004400911182d405800c00d0042041c1556451607004201200080144c0020a14240b01505409460090320720300700c0030300507124440c01141002c124404054200700d5024049003d07600d09101c010003500d05071000388080a0410f9000d0003c880d0400b00b150 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 273949613 1250 273948363 273948371
    0x60403231005011e030f0206030402030718061d160f090b070f1110020c010e0112020703180b09030a0605101e05091501020a02090a1e06050f0a060c06091104140901 72
    0x11315500074400001501d5200300380302400401602805469040200120b0b0103204000c4081905110942c428a0340038084002140090800c01d20711601d070315980c43d00c400d1103030001c03e202d004444680515488002440c1c4501d00d040c26100460f03e401c0070f80d00104004500007400d40c24023036055000f00d80f41d0300452611196003060010300440b441740c0301d0002c00503008a40040c055604c0b0b008400055441490182410710081d80f040702242c2c480c1c00101e0220300b1104035028032030204e0762103600511a400001c0e007402e00403030100303482e0118607100521041d541c82c00030f00d4408401110070301600011004000300307443c500030b0000c11030650050501c20902400052031207d488804031103106c1d01a400b41c1207180d444d500b88031491001600c3e0420050300c07819603007020340790900f800c008442c0c3c0360400710b507140c03402044c032506c1c1d28000712850140000c140306000f0590030540c1c0c032000d030f54450300c0000c0180141c10801da840d40040c02c6a58418108001840c43c03048460071540900c0d42280200 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 273950863 1250 273949613 273949649
    0xd150207260909011224140108030c07033504060212030103110d050f0d02160f0e06060a0203040e130605060904031e0203040305010507090e0106030b06040323100501 73
    0x110740350141c030399050f41c80b850030300060250011022144410074840c41d0b650300d15280000e407031126072040d151109041d95954060040304d0b5620311086004004d4840034500c0c0200e841d20040e2203200c81d010107011080d0850031480d030215003840c02c4640c208042d40c0900c0740c00d064204502c199209106041c01846600552846401040c04881c100c0f40d004102006145424003441b01d00c200d000808d99031405131443c40c5c1e80080c0b007802407241004041d809810074615070308504000044581001c5031480d00048103000250b035901159400107000c0703820316107400005008030f146210705e8001142c202000800d0144034405134105051503403081d0418405607584c1c0091102032042100d014001402002d590340c8102e8044001d034844018620540b80f405481c0e88605003940c205070754190019080f00c4080104c1c540c07641c0f205000d0034442c5000d00000c0e400b03500262040c0501d00000d865601d48009601111001581c1c48450446120a031401c2c00260158007008100912443e600001180b40d14 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 273952113 1250 273950863 273950933
    0x60a180c1d0903160f060f0f0b01030c050c0303010306090206160605160c020a0308030a090804031101081006080613090b090607120605010801031e020307080a050c1503060d150207 79
    0x245190002c2d80220010002c081e13140c042081001e0413086d1407450b55000980300b0300143d03025140b0760303000f0a280400c0f002c500d00001401c480013104000100b240500400c1c122407404000ca90460b070700300e1004600c1c0003050000030200d21603444149408103c45480004100d02500a103200d0715498051a0a80d865100e040c0d039040f144250003548928504000d1001440c0700300a541c210282c0c030750014002d1810303528146643d0241e00152221444820445203560740240290760202180758140003071460401d0181c01b0310805403e0f1341c03040d440b620701000c10044650042c541c0c80d82240c0090141e0800c4c0c04601e46038881030300c1c0c10001410a21044081c0046400740400302c82e01a5503600ea1a172840c4c0b16000100001114440350340c14910034000583d80800030b4030050030b8014042d080b01400351400c540307003400c26140c55024110b10145101d0010300641669846030b0241c40c0802d60901c00e1800c2d4041e60101502c02c48090310103c0c41c401441000d00c80c10f215201002d02c0100c6a00f04043e45d = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 273953363 1250 273952113 273952117
    0x10e1509030d1a0301090b0a06050f06180f04051501020c01140f1e030103030f0305060409080301090e071511060c0c0a020d0303060b040b031e09060a180c1d0903 71
    0x151556680c41003100507003050b01d0342c0c007582c1e0707440350260001c0700354520034002030035540d5840b42501c2c0f0703410940c21322001c48070301e22a003002000102c8000004189050220ba034902502d00c001084031040c02024109407504d03031a809440b40001c1c0100102d1424800c0c07003002c0303140160762900502c240e000c220541e50090b8402424800d050050a0030045602419182540009408101200c204043c207225400010103580a50700c80d17220741c03200c0040e4103c02401c40e440288620310840c102040389020402041c100c9056412265010034038000b403c0f074052510744641e00032503036400911b85440049a004080700204180202611159104da13142d403e82070141380310a19098100145810041c0b6001d610060560701c41e0801103038050f6502419182500b0075800a80d88507400010003074000e2540b61004810802112072503005d062020342155900c1006042e90310866035807002948580b10001400e40540c0d101085041440e100d4a041e2074022102071800e0041c10034a010400751100881 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 273954613 1250 273953363 273953371
    0xc03052215080c16170315030d020a080315040e12090132030712050f010501030605010201020c060613020c0102040b07020307080d020a080a0e040e0d1209020d060209010203041502010e15 82
    0x5085420140d00701c43d080502030150380110748421040658080708a005c801441c0708801403150602c40c04100414581801c1c00c140d04001150040202100090410001c0c0c0390440107082801c0d44c4241848040760051a14811105952040c04940404035800030020b00c40c008080c1d80e11030f001b01c0d041c04c902d40c07800081c0000e1307c0c106121036104143c404001c0301031680000b01e494000ba000c1440203a180851348141d504034140b14041c00103100070b50701401450010802803000714903241c0c0001c10f051700c4280181ca020300c40e0f03a40d0500c42294542c0c130340682c0c40f48031881d80219030392503440e480018140c2c0300c580200d010340280c0100181c40800130a80c6040b801b0150080c0c0400540c3d9919505140d02c44086c2d0002c2c89400d030b903411481c4d01c0d107104000a10b03400d100101380c10310300090700be08003040c59032810f01001c1c20000220011780b0b410700400c43d170685c42000540c580d4040c1c40140d00718016900402c03040e01d23464040380101c590541000340541000d40540e040e003180c0208208880b1003c60b = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 273955863 1250 273954613 273954631
    0x33061204231009060b0603010303090519030305090d11190e16050a030c0203041205030901020609010213090218180f01050d170903070e0709080609060103120c0305221508 75
    0x10340101c0d070340380c000b07580c1c0c3c40c400c440001300c080f50080066201d400a03007082e03001603001da00600c9903007807400c0d04c3c852185040e000080c00b1441d540e13000303086105810141d0301842d103110101c400c210aa10080c0b5000038000c1200807204000c12988403501454030400300300c80c102402040528052000ca030082d1701d0580d0741c540c500560300d00d05a028240f0b000c2c81108600c410000000e4003039201c480e04103164440e802855464501200080c82c01401404103400c45c1d1040261880c0d02d18480c104404581c6011000b680791a40b00d4210824103c00c01140354100c5480681503800c0c009c03041c4d21b0b5105a41000414019076214002e011a07900700c80310090402c0c030f001c5890000f01500d080948043c03400103088480964540c00100346034a803d48541001c83d080c60001d018482040c0303c8158440c842c0ca008261a61440e1100b840c4202c02032484014071414109000a02d8490002ca03084a10881403040b0b8861780d12406c64100d60482c8074030a820703030850120a0040e44510308040c007441c032030 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 273957113 1250 273955863 273955873
    0x70b180a0b0a0f0e10050d05160f0e180702030703020d0c021e040e12131d0703052517090a15020a0c05010f0507030b03063306120423 59
    0x210161204011050040140300200d10050103956a1710f01060700f40c800303070744c496071500f03101e182c0030056801c003620451480c030040305900b000c0da90180044220035400e20f401032500704010045401560407601140d405000400ac10414036000030040030341905c02e508494118400210840d503204100c0350007584241c3e02c3d00012a0343e0030790070407001e290200400000e1040b4200c000c8910f4a2080404950000e90200d80e0000d480d480410035401858403054620712a0480d204504034607c00a0001052580d038801085045000107801c1c00380014801b00c280c800c54075414003810000320864000b42116480c0c0000310001c201040b02c200099009084541140610001101070b40000002104008840c0d80410105600340a6101f522a00080000742e83c1440c1c0d800505036840001550702070b60041c1e060000400e040d410209442c1a080d01080c000c04103400840344010f600d1109551200021400c003103070020070034586015912400c008241c00b0400301c52045411440c0613000711076004 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 273958363 1250 273957113 273957127
    0x10b040b0702010908010c080a050a0902090a0203040303091b0503060c120601110118030507021003020901020a2a06020d0e010e130e01060e0c03010f060215070309020f03070b180a0b 80
    0x1100301500300d003803050400303c90154899500d6401c4509400c2c0900c0000c1c21517052085041e510b114141c0c211005100138041180e4a8020986c03003a005401c82440c0c60b0300200140c00d151180d41322140040d404031400703a50300f444003403d200ca201540140e6101e8000d14001c00d909542c400704036944000d2074503c910440d030321000150341e18109481c005c0d25079503c466081c88240034144651a4183c881d40b256138445425005211583ca010704140e0f003414070408c81e1040aa0f00000d0b9010880c1d4800046515040400e15010000ca8500c8842000e4503142c040440c0158001c9900c4c0103d200598640e41d214900800445608003640c200b40e800c4ae031200ca0309600c54500e42c200078071401c10500040b5980da07480c821262007000c21030307041c1500c2e0800b1005000840125008030f001f08860304c014040e0303140b038030380d90000c2850251115042c07640d03c050000842d110290b1003400034200074240d90070260341d0303110b54681e540203038241c42c00182c5000100c500340ca0000c0d1040143e0303200f00102820504 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 273959613 1250 273958363 273958379
    0xa090e0a060302060406081807120209180102030a020d060b043006060314160b0901180f060302070506010806040804360b04180c06110a0804030f060b040b090402061b0703060606020d0206010b04 85
    0x1000e89001243c038de0f94132000305d891409000030f40c082c81c2c0d00740c00180c0e2502c00c0d4540808481e00c079000f028400c00100002c1041c101000d4402d26421060201d0381c1c00007180c0b00c107450400e400380f0340040206060010002c01d210006034079140c7e40c030410090b601001401c1c107280c4044070b0035003e1244034140500554010303512481049503e121a001207407aa281c13101040010720800e940031000180e00001c501c0d041103002d014542c0104629001040542025900c480035801640941450581801d1840804000c0650010781090950302c04031900114486101d002d49444800039020f01d0a00040c0300354143c0788001c2c46041e540240d403502081d400d10700225050041141d4640382849441c0c1042c010407407590003840203602c0b6000e03803201c20140b440c02000395101040c04d184140e142c0169046c2070b455007004940c1c807030342c100c40d400da441007401e01400520a60300b200711520b1003803080204c03c010403540490240c3d9461b8003101d0385070900240480c2d5503007007402a00c00c0724509000402400c9 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 273960863 1250 273959613 273959629
    0xa0314030f0a0f15030506060a060801060e15070206220602030a120e120a03020408060112020d141e010207110415060c0201050f07030206060f060a090e0a0603020604060818071202 79
    0x120f200c90001c201d90a84ca00d2103000d449440d001a1600d811040c01c1c80568902144035800810301d6040640d0550301d0a8005418041010144e0703001e14008451841a01708040440c1c40255004203605c1e25104201c840e80581010247c01c1141c5426010001c07912600000c10740b883e00300c20f0b0341c070100d01c1314841e40440d000e0b00d000b61500c4020300c42c54010a224042c0d81024007403040d481e940050300c4502d8030501c54178019069010342c2c00d101503e2001000744e01c0326189241201c3d0400305403090802041c600c11b1038425400080316030411029641401140107400501c030480c0200e08040c0701e01e03400000c0108640c1c40c40c2030289400c588140800110340510220300c03034103005040050502c0341da40101c000a5002c14070450040e0411400c1004070301e0b040c0d0000b0000c20054540c02e00748100100c0103400c805d528000c07011030100c2c140004501900c5030300240d000e16800f904490700c035540c405000c1c090050030398a2245c41c0c80783c4850741300300d100001008412100c078400c08010203461502409298 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 273962113 1250 273960863 273960881
    0xe030a03050c010f060303020d0905090f0f040c080f010e0c090c1b0102040306021218060c0406050c1204060302030403091a0301090b0112090b0108070b0309100c120e0a0314030f0a 79
    0x155481348180d074040012441a0b4000303500a402030610103007504402003100130315401c42489038031000b06029000d0103a804890340840001e0781c420541c0c0b200e0800d60442c0c402588501072134450009124048801034021300c0c00300081400310390800c035001c01040b070302d00c0b8111124115890140500c1d40c0c4140c0380d8011440c0916440700040c40c090302c0f03444a009aa00c030036910b80c00f00c1261428405200015024400c580d0303400c00103842c0d60300701b500140700b840c4100c4c4a950108400400c824940c80d40a003c0c0e55103c040907078141d543c90340d4980e4080c0103500101c4054010551916000034010038480b0300d034007a0251030880d0b500c8c5a0070520000c00a01e45c01b45924100700901d99240c000808901c124081c050184002e410690b00d4012281e151590540098000c4c12042c81400025840021520440040d9800c042a81024030400300c500003900fa00c0e801d141f5042510b0414048070208c0c0c0d02d104d590295070b4075014191180442d602c0342c801070701c00301c10b00200100059091506039200d0165 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 273963363 1250 273962113 273962137
    0xf0f040806070c020a08010515010f090b07050607080903160303022a0f06010b07031b1403131802070812070e0a0806090c12060c030604020403060f0c0306060e030a0305 74
    0x1416180c22425280000407190140402c3c186286031003035242c5110204002c2101d00c009200601c0c0c07042c560038404440c00a41d0741484400b0307000104d224024810080544165401c968650406044c0180d0701c210646111010030318400100e40c2007980801110307614414030803410500d224036542280254011000517404810641e040300b403259000700c1410a0211a400400040000650043c10080b042e44a620001d034108000c00010713400c8600c00c03004440071414440d403404d82c0c1c1049807006824400c0c920031404002034610007440341761184826111150300c01c50040080b01ca010027203204000c801f40101200b0300040a5003011036101a80c003c0c1140b4110304c40c0b071080408070b2800700b02504450050b0b000501003181c000c4042206c06000349048514240300e000080001e46c81e244043c10403109414004005942c0385ca482d0112001181d00c41020022201c914402100518000c0a00e030006800d180703000507014410125090303055001030142c15005440d5805458651000e940c00c10 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 273964613 1250 273963363 273963367
    0xe01091503020d06081b0301020405130905070803070f0b0702071214120c030a0201051521030c03030a050103030e030f03190306030206070515100b0f0d0e07030c15050903030f0f 78
    0x2032500c0c0d413801104010a103600003801c2c0a59049014000c2006130904540282c3c41400304010540e580f110b07105c1407401344030002820b00e121b07040c85402c0050681022003070380710020340d080c20005c0e08208003101c01e008441403c0240c9603490201d8843c6918031078045469080303003500001c03a0040396101c0c8254600c40c21200400f005202152880d000010a10030642002c00c107000c14070740a020b483d42c0b200002c400d4440040440c0001854015100321801c021200030000c1c1101c50b204000700e030800c10101085a85030300d480e00030781024004c2400110000fa503040720b14001c5090010740c1204404444000d5420310500c0905804943c081904841c00c040d150300d000005030701d9075070042030014010b0020b400280c2c00044086040240500b240d00112200c0004106845009045d108840b61901803d951084800030840c06482c21802804290080300800010003004980000c102d944070b08500318800078a10301542c00340074152100d505a0800c220f4061041e880304000c4c103045502100e954 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 273965863 1250 273964613 273964627
    0x4090f03030f060501050903030409020f04030609060501062705220203241503060108061f0807030f02040e01030b0414150403020114041e02120f0309100e0109150302 73
    0x1010006601080d5600b0340b00d40c01042074002d000c0942800e0030094a0000c3c0100802c0e030f81d119500c0382240c050381c08640c841c0301c05c0031401114000c541059003804030424a0070000000d210078403802d00466010f02c0c0d08840490a4204502c0403080c01110703038402c510740750500c40c2d8080e2000b0f04131b031a060b0b02c05456100c143e040c40698020844940c03254401e40e03541043d0619031128548481c07144164010300607081c0ba808003100c1e030245007031800d0161900e078600800e55445106094004210040c01801c040a0740300142e2489003074a0f540501c40c101c900d8502c68128410f42c05040e04200d0302000620105000f14040c5400030b100320103203004081d0303104240d030416041d074200d0b4044002000a00040c550b0900030720400043c082e955000500345642c9448549294050320040722441d40f59032000e6544802e0340200c0341510700c058444103040503e010f900d0703030f12400190b4490b0b0313650300c250251184038802c806140300068662078032403420010186d540c1823218550004064080001e6 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 273967113 1250 273965863 273965873
    0xf04020406120c05030609060903031902130603021801080903090103091502040e0709080d08010608130c0617150f013605010f02011a0d08040905040803090f06041a060409 75
    0x59039643e020b51010092141401d00b0542045005007082c4c03140e611a0301400410100072084907007144207146112050016508040003134007591001100b4039641820006115401d034004107039018194000c0095202940c0040d01c03683c405403a280c98a91061000c1001c5500a901600a550080b160060098420343c4420306031b038040d030071903500752455906101c5150f41006020380509031403000b904c180c0303003a29001001c04405104032010440450081143c030003500e60900401c40d04074450101c0c01c0d4681501900c003403410180e0749640d0141000040e510384c54880c44005051005218181c101d60f0600115a001242034410709060b14030844050050383d4858803001c5405044c0000b07410519200015114a11480d008029a41000d0442e281100841c0c1481e07a610000c83d00c16050f41038038241803030746002e903803c070f040e8180c07800040c0024000010051403080501104607141c911b42c00940c3c0e030701c80400b03550090006241082c514503400c070144290b58810405040010f814141c1c1c0c4403 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 273968363 1250 273967113 273967139
    0x2040902070f03021c080a05071e050a0207120b04060902010908030c0106170607080606210c1317100b040f1806060501090b0306310212010e0601080f04020406 70
    0x41101e601241c02d010740101601804100401600031114880c44241540081e144410040544c4a016550000640c000e4060011740d071806001d10a0580d0303140d4600005050759000c81c40e02d6016114020380001d25803a684458043c10340c1c041036040340398a07245d40700d4000c0e0606c84012818403040e08800315400304208040e00b2000c03201000032030000d00d07119144410060358410515030382c00030b404015050303402c404640d401c07071030644020750b803000010081c0010461020030021070f412000144100303001d904024208011030000d400c1c0780c680d030340c00c6110040030a401c45004d094000106034800f00d60f1581c172180040d5000b034004996011a00074940842e03a6403000b89410443c1d40c1c0540d03042c000c051007600090b10080c2003500300301f4140702000d0f9141c00700070a0507100d0a11568501c0141082014aa2184600c1c0300b6030580d160300c20390402d010390006000444d1540c17003c00000303260100e8203882400350506171900c041c3ea40b618420101021030040081e03070003585501c0002400712014103 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 273969613 1250 273968363 273968377
    0xe0d060b040b0f180c0d020a02012a0f05030903070606080a0c080606010e120a0203060c0d0f05010e2d0711070b030637030b090f1f0b010302040902 65
    0x14002a000c185100708012129207299503801003001e070b90420826191455514030010191002c95070680c0d0b6080c03410094800d50b910b1007075003800800c2c02002c0940541204448200c0950200e40c049030820800301049422002500003900d00440541c08070300803001580c1001c0c004081da0301d4017242e030f21020142c80b03a95019408075403210807480c05200d01c03103090402030400b80c40981414140030000806400b12403810501c10301540709440c01d2040100250f641c40b65014041c0c2d804c600c7d1683d11040c0c0b03a0002e20140d51483c0c10000c00f1128400f09200707150581350b00407a10b40f1143c480064030180e558540e501c203aa2502c1d0700441410481d020390019109000550f2540c2c0181c0e40880250300700380c550b5100410304001030051041603541c10341c00003129a440003811981021054502400c3c40203400380030302303081d0782c8a00070040c0311890580300d1043d14000c0c201c89003904603982050f544d000824a0a44401303910b0b401000204084e00b010008490526000d420217466410440890340004 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 273970863 1250 273969613 273969623
    0x20303030f15150a020d020d0801090b120d20030901020d08040503070b0c04080f0a0503040509060a0b0a080a05010e191a090a0221010303140a030e010906060504060510020a060203070e0d 82
    0x20400900c2154100803507a00d1b0306080c0302800b0540150400a8240c0710b06009030008a92980354010719520b0310034003014030011010482e18a11070040015102008048801400541110f40107140d40f0001046801420341a4000c0c00400e0b0000303000ca1301840007a004444070b0004100c81408220380b44036040c000c01803440b038a82d8443c5088817241c81e000d880212144e641d0444d800d003001240000c01039400b00e880940300164650f4648001401011450b0030891584001184842c100b0781d00060a5116440142e0100441d90300e410340302807202012600d0f03803d0744c4c3d50400010740c0a080da8011950a40b001c480040000403200002603024004a4901c0001580401c2d100b0340d04a0f440382e500220761074011440c400354110b4170014094004105e82e0362280900043c070303900c00340c03081e80180000105030300200540c08240ca03216001c0c1486c1c0c804c091246007030400108062800340d068002c0340320385400030149e04040741c0d20b82b000b03500002d21120511945500d1300c2d07613075150f40c0d9215181610032 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 273972113 1250 273970863 273970867
    0x9120a030206070801080718020912031c0609090b06010c080c0109051609020a0804080c0a020a12020f03010c0f1805090108100509061303031a1201020a020c03010504020303030f1515 80
    0x38a50081604d14143e01c046420361042d28104111018070105080c0c60007030703101c003603998020400840c0c1900000040c000880c440056010300d2a001103600c00f1643d650f0840910038180e0342d07100002075039030200c405400040c40c10301041072580a051484502c0d4486c00c0c10505010a0240c02400c483c0310070f07010389880d0031100a803481005035080d41ca0140204041c11420a071100000030105100104001e20001001803e1410ba6404100d03803400150300601000c407594a40482d14042030328107100321300461854001148501d01801011100c000d6503480048058828400301c3d5200110710b40e00914052014022a007074444071107080c0644804401407040c05600d01e40d007003c0b5800180044c1c0590171038410b101c0b00d9250000301c14010394141c500801c8512040502c10a060150340865500c5815186498058032042d0090140b0b07082c02c0d000c0d6540e5042c030a007814261407044500a6050308208001113821042040c0c0940200d454a29032400014401c04640304504020145c4a51000 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 273973363 1250 273972113 273972121
    0x70c0c060c0314070b06120f010c050405030c011103090d020d060c02010506031c0507032706090807050925020a0f0312060b0a09030b07050d060b130b0408030403030509120a030206 79
    0x20f404030400003181c04205181900d607440716002d528000c2c040b1842601c00c0c2e8041403042c182084880c4040c0e00780c0b03008005840120b50b01070219406407044d41d0003801090303581c075115070203904c03050580684070b009103260001e030170f08000905140300c001303e0f44005d00c3c012038000301d00203120300601041640c00001d0907084c141d042515003880b03a0707003214003c413a901401055581c08425100400c0d132504140c2112012849982011411003000800507201c5030300001c1d8007580840294102c2e07a00105580140b51994180000d42e0021142d01444c49406d180b0030340c40c3d000301c90403001018654416510901c147e50780d40031410320901416400030f0440b03d40c122080003248030b540020701d800520580ba05001782d00142483c4018440a08400403000c0002c0029018004840846090030800c00c512926a20720b020706030010b140c1400104c1c0c40300008103048031070300121019901c81000a50409182d581d00301c41d20b030710031151541c009601c182c045500b40010080b01c015503109402411031460 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 273974613 1250 273973363 273973367
    0xa091a071b080405010f0c02030615010906020c0d1103030f0307090503060a090308040b04050c06071b050402070c0b070501060f0803122203140c0304150206060a0605040b03070c0c060c03 82
    0x90550840d9103280035941c07800005855841100d00322602030a1502c11241c15000544001d644000043e40600032681000072442540620140340d034403d80b258041d07191210012a502d05214421035008903554541d40d002c84c000c450400c2d40c2000040c2104d29040c5004540da48503001622548081440b92606100340c1c582402843d03880340b5414010410507500340c500408496020748082c00d401180804101030002c18000d03d0501d17640030b02801e95a202034078180035900100e10f4520400708401401151900c0d05000300d610701ca030001e0580c18a50306060031954158441c9004842c00c0d941d6400000c2c0c60440c80a50b07100528080029603160001c01d40c6e0b0745000c59004080e00314002c8185290008942924000e60600381c161400c680c009201d296660140d20450040c001c0510000c02e0004102d0129250507441c0200781d400d031911a1902c80a200c00502c55005110104100f0302081c80964142006981d0100c2c161404810755546074440b0040d02c00c2175004000011013541d88001415 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 273975863 1250 273974613 273974627
    0x4080607023310030507060c02041506090302150408010501030c380706020408010e0307032616020a061406150c070302010302210702240708010504050a091a07 70
    0x1801c1c2c900040381d10a1449900d40401401909404041494030120308200f00b01e400590155510208071440207888041c0504a50101081203205908000c1540c0b5690700d01071580b8112142c84d00d41288090541e402c0208040a5500c22203400c58240400070300064240101742c0218021214507520504102118a459541d0302c0c0600b20490060039186800000400305559a002600344588845142c03400381e001e03100c1c992025109600300070709111091008402800f10751b2007a02e0314040c03c4850203141c80e031107110511001c0200021000102a0406286640c901200030f10640f10380748030507a140c40880d400303214804981881b00c000c200250410031180e81c0d00c40813850b103a81c2000c0c649180e01c2d640720a02d000003810190007043c61481c1c0b4010414030346c403441c0081311400541c940410005d588072548150391002400c1e002d1320f420700c0c2010084044c000d8113940d031a201203a082c47d081c4000303000042c19610056980341341d041c000c511b04c195544545543c59020076a58206408010020 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 273977113 1250 273975863 273975883
    0x30807020423010303030e010f02210106140906160f0c0305060c0711060711060706050a050112020f0906011b060204080f0c03030403031d09090a170a022d01020408060702 75
    0x1542d2200d074400c58403400540d205045991615021032070f100c02c40d035098054859403010490290010440741800c10700c0b0440007103502c1e00c1c0448101e25a0343ca0707500300c41005080702100c0724030b94100510302481c01c1c040300030310781c0d00241c04000812002d02d9884815140040384103a42035002e00f0720030700400c1400e000b00c1c1d802804c0c2107074250404a26450f51403034007aa588419215503c00160340c020000d081185200040c40200200d44400310740c180040500310880e8500c0b94545418000b0070803029410769104046c0d005810054401c42940a01031755801c041d21103810f002c20081d0304c0032200c1f8601403414240f4030500c005611103280084452034000240b00400d0240c0001070400c402e83ca000041e50100d0f905071418403650103100380c800c00103640581800360028805020402c00d20400a014081144038204203003141c02801242000d50140c80782580042c1c0020703821803001400f294403001e11844140d02d03200d614901040c040c1c02c99203e90700c850403940110003003180d10342c0c06115074055 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 273978363 1250 273977113 273977141
    0x602070f0c061d041505010815040c11071a03150102070314010c18060203030f0c07020d060615140d1d0a0605040b070503010605160816030203130b040f0b0a02160308070204 76
    0x1036001c04034202400c17040140141d504022445000a140758400300c1c04182034103001d04104030320201c003100141403c2c0941e01484191050240001c0d01d517004854030724003007041c8040c4500315207421001d00d40179144183c07001d0443c1b140c00b80c040301049080765a889070b0030040c070000030714000d608406001810303550100f000e0708001c42c4040090741d80200480364840700a00042041c1d90718030810542c18020b018001e500055109070640c1082201d601100c00e840c10300050f01c144201c02102103400c00541d1071813815601080c4001c1681d01d141c0c1e00481103034403442103508600ca003080c829910f00607100c00245e50880d2184e003804103120a510680790040010320f07000b840d44d03040000140c928420211520350034810039200005112494040d034060300c8640c9900706420402d4180213540350040b0100500c0110031080001b05402281c044408172281c200e201140c80e40303424042e11003500082101d01c00c1d401040c5004040c80c3d0400e680030040c62040301c3c0240c6a2040d0300520044605140544603 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 273979613 1250 273978363 273978371
    0x9060b0301080a06020705160803030f09031e0a03180f03030507020a1109071214180a030909051312020a051527011d07150306120602070f0c061d04 65
    0x800b0034000720f080460140c00050145c1d0320100d924200c0c2c9070074401f03200310601101040d030218450a0100055003e042005020f0703000c3d45075a9a269100d1180c034118640110054600401d115080800b4001d51541c40c140040c1c03080d2000c00c01c05541d08000c1c3c048604040920341e1100f01505407180680007540b5100401050350786949000c801440c0108043c0300d05440e00000c2d5110f071003280d40b219882c42c003000a0080204004081200e458151003401505030342000c1c0c0c0c07441c80030000700c4904240d01038fe103405460340303400c2d58100100300151098010001e0003180b03c000c100e403103042c90b84500040c0d0003800c0710b28103070414600304411241c0300c01c5501d83d20400c5c0b00c00001e400c1400c1c00400c3c1c003a00e0002002c100ba00025005054014114194283e400f0100e8685080441c1400807514040344100484e0700a04080342182c640380510100f10030444070300070110f1720360760280ca0000c0c41041c01860080160701d41005c07407100c690040c40091190000d10300410680407130041486000d94040c4 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 273980863 1250 273979613 273979619
    0x209010f030b010b1c020a020a03030b10050403110f0a08071814070813060f0902010e060309060f0c04050d08030117011e0e1501080c100813060c050910080109060b0301 74
    0x1000c40c42d8184500d4207240408504480b81c00006004d11034485000c07142103583d00d00c03020010b903c80ca1510420380c00f0902d014400603007820104a800358900440c0d0340c03280391074103503500c903581d03600071640c480d400c59050310b030030f21443d103902c1c8200c805802202c0082c42c2c02454100301c0781c1c036665604182e5541c28104607000d10390305001d07180c1c80d80040ba07600702000e05958003500d0074003c03155803402402243c18400c1031798a2404170303417101030440d000b0780e580d000c0c0e030000c0001c2c040c881c40255440b0b10305502880000f10041140005180c00112400010349019544ca00280420071840c0c0203645056002004000070740c00707070310340c9660a21072030005d01c9181903c58030b149a00f603107031700b901c000e00380c40f00620344000d2410701004000e00d102007500707405544c50f45e4409030f0f220182c16946010307003181940c5003070f00c4c0d010700f040a209682c0311103049510f521a41d00c41000e4012800100c05101050080c4850b0340c2d90300c041c41c0d10f2190035640f1105190314108452060f604139500181c15000108014 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 273982113 1250 273980863 273980873
    0x120f050912030d061511060f0f04020a03120e040c1e0503130203030403051005070822060908160501110702060f160206030f04020f0406151805040e0a0209010f03 71
    0x140344041822110444040301220314207042d4865203601c002402d2030810045a45e654a24940d076040e141d9540d142648100c1d4405c040d81d5010942d455403c6010610001d08001480e880459020348040d1410654642c1c0b0f50f120310300c103103e4117958800300c0c1c998111450716040c6807041401188503898546107003401c0713121042d1a16144040801000030000014046d45c0703490140716000e907406030449560b1981d90500301d8681011480c0c0410480c01c000110345820301c248203e900400700f50801003c010b40b42c480c045d054151043e02100e0868032020b00c031012441480181c00c0a9010031032800c0c1070f02013803805508450205101c4507400c0c0084c8030150260710340c08180d03420607000702d46640c1e0300c690180084044880c1e038100203600c684000100006030604070070303041c0540d1017034603080c8030008880e08010a4452a008088914004401c0e100a9610805848501d045008480e0b602aa01c5e00c010805984992151108961021680b40c0860030300b078009500415440e03210f94141c41c215550307 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 273983363 1250 273982113 273982117
    0x10509130b070f1b0b0405010b040902090a090303090f060c091a0a0507020409050604032c010e041e0c0c020a0f0602060118022a010c032a022404120f05 67
    0x1c07040c100120003004000b00f90261001e4501d10140c0701c0014032000851030325003d02d24040f1000c55455080960300c1c14507040c07030300400d0f00b010743c010881013130341d03544821500c001c10a46105030200f648550303062002c1004803107034102403401081c0108030744202060180c0741059a503c5604401c40700380081090001c01c0c1c064a26221192410703680e00e500a000190243c40c200002a0181c002c1c04107120825400a00d1901115400b0b080035202000c24015640051000203030140812462101619a85010f500c03202203003048c24007400e2030143d9034031400d045800c4015000d0119080c03001c0c550652800c1c800d09402044000c03d400e640c0c60502c035009450380c1c418480c01074018214550300c200c0b9416501503036950300003107052112141844c0314803c2d468605a4000c9059464445603035070103880b80c0180100c44121002103d5480f03598456028880b00f401050400c501855001500030021000c03101000c10607842540300c542820b041c01c0f41e04664228011080c884545c04030700b68070381c001d02 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 273984613 1250 273983363 273983371
    0xf04240804022d180601020f03130302091306091101021203100308070f061407030605061801200616031b080106050310050904030c030801092a031d0105010509130b 72
    0x1042c0c0705211200c0990f120302c243c41c0b05501da120710030328440d07040e072489061038910500c02603088884030080c0701010b6440e40304100340e403480e0403a409428009410300e243c03040e8100c04c4458441c40310300003d440701c1e400c80b11030a20482e410a0002c0400401d5039040040b0171000c034101f40468514104440e02d01a083d441e0f102c002e007002c9000c507943c018403404440844c01160030103c184859010341076004601e07030007180e000010910340700700030805080000a44da4110b18603105203007003e5800006444040c00c41c41c0b412404284030860354102081405620300500c7d000704031f44202303c6144c00150a66000003004041455040c04039135000ba4014041c0e41190524103000c3c3d965165280d064144a01ca5048207400c46036a1041c00209a400f078102d546490080c0c0c3d4510560740c0300c05401c0f00340c89400200c2d10820382450346c1c0c10305040c003200750540781324014200000c40050611302004860800011000185d40d908010021412308010f090352217901c01146c2c20807001c0c2550b81030313901036000d0 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 273985863 1250 273984613 273984649
    0x3060b070b061801080604120f02030d0e0708030a0c0b0c0309030409050a0f09031e0206010803180a0f0f1e0e0a0902030c030f0d030f050601020c01050706020f0424080402 75
    0x80460b4080d21070407504104072a800b03401c1c42440d07071100c60890b9a040c1c240c4085600325600c0c0f199005962007000c0020322084698099860011141140405000040001602030041030300c0090003200400c000c04090a958031020868442814090b03a1718034010081d045016081040100705c4d6008011202580e1500c000001d59444080e4500002c0c82440b0500a100740b80400050601d40c11051440003458891203010f80216035550498031024280720f0b5a4039603005000c203d80090500d189100031500140107100c001c0d40d1800b044500107540d0b40480d140c082002414030035100703045000c004050003c10214075540c6040003400100c04c0041460010316034800001d001c43d5001d01802c842d402005003100c003000d11081d5099241d12480390560042403074074500c108803460500845d03106d044160050300705a41044015200d0f40e001400c100e402035800c1055030340c08101540507101901e2040200030441d118040a6822510750f41c841c002807085283c100300046c0d40340c2c0043da102000c48 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 273987113 1250 273985863 273985883
    0x50109031524030209130c0b0702041103071115070206070809010207021503061908030703180e0702030d14040b162604020315010312181205070905010603060b07 71
    0x14520100201882d1a200540c0103070480c5081090070341941c01801d89008448081e01a01d9000e0022040c0040c400700420700c04101d5020884544098054200b241c000307403010902001144820700e940e402220184003180280040c0c0d180c01104025030300100d111040c1940342420000702c080e540d070314010650400c00003038100081484100390181e40d900b50307016001400c1c4c280264001482074008a0f881402654214000022404001034080444042c50041c1d8a044814cc030111a800881e2100220031b45021800007942c01a54448510400c3d256028503140d03601c03010301c00709a4a2000c04207050010001c1804040345810090075001840c494880090b0a20a882522035280814452129107e401c81c40c040c2c400c2041602440b032442201039aa0000308200103030b074200300c00e000241010a0094900c66058003c0c4a1403000202d04116203444640da00c403403216041c0354890031119604012030170080081c150291034054021030a040c01454185508039a0078000d03480c002d8001261 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 273988363 1250 273987113 273987143
    0x12060a0203100506070605010302120a150510080a0302101401050f040b01020f0a240504120503060d02060a02030703020607020105010602030a03020313060504050d08071706040b131a010806040605010903 89
    0x505044a0020f00300a000151a1078003828000b00800e000d21040e0b02400c0c90305034a405031003021130a200780b00c3d44081000082030702c900340c1c04000e080013066080c03d0740c541d503070124001c0410000d0300c8182d4442d60040c070320054110040cc0503542c01b00110030074800d0000c0144540c4e9908007844100903025240007031031040481c0102d2404a0071054040c0500403050040d09000d003403100d81c00112110f01c86020045820445882290070403600548150220640b00170004d00c11401550000c6004044444241d41900000c0e11648a0055074001d41c0c0001583e074201a014041e540e4401c3c8180001c105030762510718080d4480c40381209100c10117900100044803180741032915414903800101c1080a032815181403540d505c0d5140280c0080341078600003944552140c001215424110549500103446007424000a8207140c000c03590711003105810100038003c240315240c20240000381400c01030020800244c40f0407030143c4094000c03410503130140910398008805c401203e5003d241c034011010 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 273989613 1250 273988363 273988381
    0xf171e0c010906020a090302030118020d0212010609050a0c030c0908030901260a020a0207080d0914030a050f07060914030706050f0705240f061311070c0314070512060a0203 76
    0x703682d9400519a900c0440d600c1c6400b83d0080c10141928400e4000300b01e100d1180c06410745034010048025401840c014480c4010300305100d02e82d48000c158000402d5464961b2019400c0e110100d41080290341e031115003401250307040c0101180b02d4840d0404003402d60400e001503441c1d10491001a062192140204c0b0000b010300030320707044405c1e0100314000316041000c040000395018401d0400144600c02010886c0300002c90785030320359811900d803600c045280032582040003040340d96284d8907004981c000e00208400b800b9002c4548043c401500324141405009451500369801041641c2c80c100321003e025200080d0b0134080c0c07000e030f04000d515841c00b09074810301c2d403059203001052400751a400341a6411000352030f130320407811010020126903400e214052050000c131200303640403c020030412407070701c0305a000314034044640619501e804040e45130700700c00c02426803040750b80c40d0307200d40d020411030002c0c010940a8081116a154440d09501025275605000b501d01c803045580000880e075503075 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 273990863 1250 273989613 273989621
    0x12020f040c09210b010b090405090d020d0f120f0501030c12020303070807060e0304120b0a0902100c020a050a0b04050907020a03020d080919110a0510091806030501090f171e0c01 78
    0x1513801504070603150303160201c10740e558001c042c40c14000c609040114850030808200c24460498582c0281800321a88408452088290309041d051041c060355040d010b1000307010309030f1300c80f600e6a00400d07a94550f00d413102181e00b0306e41c41080c0c6041e01200d0000140d0340802211111074210040581301c80c8a414880001e144900030b0f008644000540000c001501004004919003c5c002018071079980d03084890030348200030710003980466402c9a18800600860040c45454000b80012400c41e80b6103001c900f06000381d41007401e02400c0030504003e01d2a0009425a1281c0544003404442180c0e0790003a656540d802d036501705003e4004009902c2040c02c000d01900e080e503074030b2038040e804107030b0a000245608000d03080b4040c18031140081214101b060007402040c1c1d52f40d4544480920300f0800c01003024609c030b420f41500b6100c20000000c650300340102c50080e80a401c0e0f80c003020fa210325051400505402c1c03402034841d0300b4420903140180485c0314185500d02d88101980c1c1c0c10407141c882d8010 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 273992113 1250 273990863 273990929
    0xd0e070503070806040b090a0c050d141207060e1b060307030b0d0b07020609070614090409051b0a1208030a0b030109020406090515060301180c02100612020f040c09 72
    0x1d807140c48000a180c01001a00a001d58003501c804003642e00d4030583c13580c4031401404007030103d9a0300c0004204a0509580c01c0ca40c4034000c105690104e48081d81c56401d080c0c1100c2c070700000352000b0411406000c0a8441c00004070305039402000c400100c4811404c4803400540303694840d03400440016034690203504040281140245503060340c0d40c540c600006000010740c0d01d503005100d41030005060040004d915403d491440d11020300c1c00041605010b03040e400300e804150040d80310444000025410001000110034001c18141c2c0040b8141c1070040b0081c40b540810003800c1d56080d03000105003154100d0f50001d400f41c0000c07503010200740220f40900301c4400c0081d003061605a0005041d8200d40c4254080c151441601885071040020010140420b01030805000003444000510502c60fa0104a00071214010f07110024403c08406040750195403100350800c0800c86403d085241c510b0002c0c1100e0401c4500f000320310301c5444000c219907140c0c0102d0401d0740400c02040c03a01441d00100c28a0 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 273993363 1250 273992113 273992119
    0x1508030301060504090605060903060f0702070b04030f030e0105180d020a2409120201020309040b030a0503120702120408150c0c03070302010f0b0d120f050d0615020706020105010b0d0e0705 83
    0x14a50b52810300074603590041c801d5442c941c1c42e00d00302003420300e0702c00200e80020400400625803502c80e461001030b289000360984056101d040c10015285a0200103040250700403810002000700c14203000e8456103150105604200003002140043d140c01080c1e5490361806035200b211811091000c5040c080d103076001140c101d00f02c10356040d001d205100f0171082c441e901d41c0d580254641d8035220003003000700e40c4200a015030000e0049000a040650118492002c0201124034000254407030b03900f1540040290450304d114082000f03003c1d60100501e106c00c01c81e441e03072640740c20728001900351204150340a0310040034520021580440000c1c041d1000029003d00350307913641c001c0d464080d00a00c43d00140a1481d4280349540700585450040c00d8640c9420004c120300803003560b002146e610306080000e0050241c01d0184820000d150b20880c03000e440c200704001d80c52281484060f00e091801d60114013160304000060001729200e0050740e1030841c00000110740000c0c511100c9003001d03055041690 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 273994613 1250 273993363 273993367
    0x5281b0906172206021c1e0905010207020904050d080c0702060703030f090611270d020d0501091a060f190b070606030f050601051203090a230306010303020f0d08100504150803 77
    0x414066142e0082890f5120400030410b801100081d54098a51408402c5c0d03410031100a01d0045961f40c1e045182d045219400042c540501640000c443e0034003500d040d6540d81c01010b8045409811500305508207c0e80501ca600300700b00703640014514411510000c0130103849000f004502c200c0c5130096095136a008000740960b00c5000d580c070b492508a411141005214900d030024200f802010106000002410011090405400b03000540e104080d04803500d41d6600c4134100803518034002c6001c2c1d001645503414503070a100301007200b9034075400300e11885240509564080c180c0405c11507800ca0f00c0303411405071035042034100f00d0004c0c82158005003010841c01000001c2180c0400c00c24165075040343c1c10707401c014812510641d43c0c0694030145801401600080c04202004000c4900c40d10a08442511045070040841d080640a03401100036a101c1d0701c0700310039480d0034014902e01e90084e10707260803079281606071035210340e1003031045034000e40e42c80c0c0c20b508070b0501405281001c0d0001000302c0b9 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 273995863 1250 273994613 273994681
    0x12030e0703060e01060b190c020105250308070e030d08090a051203061009150309060204120311060903090f24031003110a03030f0305281b090617 64
    0x2c0150903045000d101e554604039001c1404c228260903030f0303600b510819843c0e1403c140000c054a0381e0316080e4041c0d0500ca8148407051110881c0d1000074500008641c1556010b083c3d131601801c40b0300d018049000f401441003100441e030b01c001030a10008401460518200d0712290241030070004044006492801a512900e20607030111005601410003503582c101080c000702012541c00780f050003400f02c0d450b1062000c2c00c80d1440791700000c558500900005241a50380e80d1400c0008144050440109520030b01403080444184509544110300301e0107185040412400140c1001d94001b403d807050701c2031030150580085041d1041942403007401d0b140e03904d003403481100d036850700c81e0b110469111203024282c082c11300f0825510b05c11a0303899113030b110759481d1000302030b005040300905e205044603003110030161455440200c410904400f0303c000502421f851244c10342800041d29070030601c2403880c01040b400f07610107111500d40e484650801c3c01d42c0c403103400511640a09004d8003410302d1040f4115 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 273997113 1250 273995863 273995873
    0x60723040e190b03011118030d020709050604180f05070603020c0d0302030901180b10120305030606030a0e030f12010f08060112060209180106080901110d0b0604030501112208030712030e0703 84
    0x600c07249114841241d80c00a461f0100355541e4a1404003e0050700302c10401c00200525800c80c03034100d040144042200003d40c1850344221140d0314041d58180800358085090100a200f680e020b003400f80ba080d45041c080800a40c0d40302c07404d8625138201036000001400e0340b2000e40c8030700d109540c6204115500729550a285442c00000e40d1460840f0300d4034400003805002251100d1140c9907d61512801e503540c680400090f03402c01410800b2054403a0151400c1c8030b8103100600c3c58021b104015500d0f042c199401601c2002d05802c01041913401c42014061440001180c13030440e03e1074240d00201c0f81a07480e0a0020b03014140c42c180d0044203203050245580301c0d9941c1a41079548542c2da100c00707603442c1441e507402c1c1c1e140b840c1000c0c107520040280005010b100d03045071b88001c2c8041c204500e0b0555940e20a401c41c0c6800d806519406000305a000d1100c10044030503038401100b07014000e5050074540702540344d210703100300103103010403842c032480c0583d001e504400000c0d1444426034010540d01d04103 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 273998363 1250 273997113 273997117
    0x170408070510080f060103110706050a05190e0a2d0c0512010903080705130b0c060610090b04090f06030602070f02092208030406020903060723040e190b030111 70
    0x9a6072088400e11a0300c2d055510403c500c1d40702e1410795a8040081e03d40a0041d4001c11018500c2440d03007400700408400326485000d0035025460000d80040c7c41e20342440500d0616095145000c0744500f80015810000310002d10a464560448010500443c91280391040803600c2280300602c1004041085c090003e4982e41000711001500d540c00041420501e90f030032504500001000f1a003c40089180c2c2407041d4042e0001c1a5440c42c0d03101296101e04948600c1d81042d810034125a000d1010081e0700d087c58030507003802c4003860900c10485414480004064026170003482c041641e1402d6140b46400ca039080100103540040c2c085503110b9850a0086008000c10740590040400c2c1d004120300d0400c60394110950010350014802c1641140d50301d903400d6101074010b4903a15004c1c4941c05641d5030500c0906c1c01000d560322018104100480c00b8010360311201342034502c103c000d1004015405c03440c0c1c449544083c4580b09094450311101c102c5004001c9034070f6054240d0310305103029030044d1301400 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 273999613 1250 273998363 273998369
    0x41805030904050a090f0f0302100207110a09020c07140d0c120c15090e04141510091109210d0504170c01211806050403110a020a1217040807 62
    0x18040c40b03d9070300c11a440080c1e030280600103100c002e0b45413240010880009080c0b109500ca40706544814150b20700311340c280c1c0c01000080c0c61170301c0c0c0181030401c2c0d850b2036000078004000c560401c3d13041034038035000c550303e800c65480b9007000f11078126525111541c50b2004a200d05900c400602202d5845620700015148104411900842d0302000461220b410510484812180e070307a400f00882d090011907550404090310454220001c600030040c030400a129050010410913800b24a51921000d8000c3c0e00006030b000102c1079103081c074480c00e042c00c4034044070218401601c00301c030100380b0510700f4030401e5550340b41a400350003429401000254800010000c943d0400d5544c0c40a81050a006072210303443c5104038041039140c2881c10b000c61240d00d2088020078008000a0b002041e51a44011254413841c00c454241d914810081099003042150741313601200300c000d0000809940c04101058440d000d801d4103001501c0640d010441c4087c800082281c1410410303031144c2d52001c0365561412180 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 274000863 1250 273999613 273999619
    0x70c0504180209061003060308040e070f0f1e1e030c030e0708071a070f120f020d022d070f05180f010909150c02060a0b010c0309140418050309 63
    0x461001400107003061070208003500140300755802d441d5402008603201c4034240550030706450f0200000400c003044042e000410302d00203601e02c02e151614000f01140600042c00d030070302051403003480002c0d034040c9100c8040010040b4040602e40462025070b004541e188079aa50701020141c41244c8036803541000d010a261500c0c2030000000384426140c444079036020703801c0650301c0500d0400c2130420158101e290700c0303c4a4480d0307181030380b1516646080c10400c070056880a121a00c11141954000f0f01185400030320b1001c0c101d40820307088000c0d12901c8840424810b00d2510510400c800c1081d01d920000140d15411100503c0d03542c041074055040500c912413040c0c1a500c40085004442c40d07409100e9101d0000d5404940e082c40558001050b554200340c41c0b9038000e440146021542e0b108050403e0001e0b00101030b60302e04204400140c130f44002c2090f04008000ca010000241c0151140702502c000740007410801020101084c0144048140740c4203c00b48520f50b902400404002066119415 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 274002113 1250 274000863 274000871
    0x10e040516020c04110d020702010e0a12020f0603130b07120c1101050903041a0c070905010303030f0e19022704031116140603090109080301080c0a05040b0a030f0507030206070c0504 80
    0x400c000417a130300c4080020740308604109030b0002c0308a070750040402910504007850302060301c802094408200e90170007109800244102c000350300c2c00c040303007018614045866900d5460041800402282074080c01456102008081480f440c024140b010510942103c10899070000c1c0000800c01700003203250b50f12551a00011841c04a8044105c900b6600c42105819000c0309051207000c6950254810403440d00647c080401c803032513503000d118004c41c0240d50100b180d41c620031808084890700c141c08401c952084080c98550030900b01608030b401d80403245500009809000d1400d000c82901e6a00800c0c0100010401010b800651080c5040050021540d8400c1000f0340c02c3c85e2000742c0e01031141c080c00945501d01403464001c008591000f401c5d000480e810203a40d580c40070030741081e0411030b0310317030010508511142000b080d8100200307000c803800d011005880c0086000011a8007000d40151403c60750103051290800225004641c007401c2c2540da50924203001031441c0c11401114411410 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 274003363 1250 274002113 274002133
    0x603061503120c050708060703021917070c021f0c120827190c06031103060901030b130b0705070b011e0e22060609050c180f010e04051602 61
    0x1a4500340025264041903008001c0346452080d240d10300300110844032480390706400300e41e106091206c0741c021040ca44000d81c5811402d40c030009000300829090040000c5020028115180c0b04035940d0040c0b40f9090286c101070103400480c2c102e000b20000242c10b80804a4603e011691090b1641e904a0040b83c00700c1007000c0003401151560400d82e504c00060034200a1000c3d0032014080f03020190100c3c8080300c030204001c0902605045400c442030303170242c01d0101c04000c0141c0602607481c07008040d00c038007855440c1900002d00d560406000143c1002c02c2d0300005045e50701010084507106800c004030207c5440c00110090840e40015021210341c02d0300400064000d5800700d01401200344042d0040c91142400f0158445510060040d0340308900b03100d000307081207403909800740114041c0303c0c0490322a0401d085a000d84070701400100c80d50070100300000c400c4444400b20101e400c4101d40004001840e5001200c8802c0b092003030650051911050040380c500001c20340300c98104940a072108900 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 274004613 1250 274003363 274003391
    0x216030c09061a0301140a051801170706140703140d050406110307020624060d0f11040f0b07060b041406010e0603090a0308040f05060f0a050112020d080a1103030901060306 76
    0x450468082845006000500000c0100b03801c403541106e0161001c1640c99072030001448240c0415651004c500724040107004150b82c05050070174040c070316001406000d1a06800404522001d462400502004600c40003058450310381c682c000e88014034072585800c50454000010802500d003100c0d070f1840c0140c0b00c001c196052066900c10b0145c0d40107843c59a03690304200d02c00c2c0c014240c0d8800c0f00c1d03003d001004002c0c0c4c2d03140090030180e810b0080000d411110904040304540b464902071440d50b1007803104110903112003007000251101801601d481d440d0600e0058068611031801641c05400c0c044402400300140505e40c7c0b0403802680c42155420800c028049980320a44000820b504130580007000b2a000707010494010341306080c4407623400070705d40780c49080c110306036000010401d0407007e1044021b45400303000d0140400140c0e4030b05050940c1e00141c200b00d00050000c05404000c00d00c8044140a080c040302c52090b088241e9680b0b192184080f40200b200f8041192050301d001c0740c81c152071b1 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 274005863 1250 274004613 274004639
    0x30c040b27010f08150301150b091e0609150c010204031a072307020112090b01031a0705030411060d1113060509031209030a080a0207030c06030504031403070216030c0906 75
    0x1540c540703841c0d400d6100d1030385c401d580050030604aa010740d00c0b03500c000c0c0c01c41c0d081a0590001c010100300e09440314000d400300b0540f504031024503207803503407e0043d51406561b40e10440388204000c5030182c200395840c0340810704901481c20b003035021b9440401d0000621800310714000035290014483c0e500740e56940700546166201408520914603110a13815009030f21000800043d0b00505295000b448604a07000a0b1411120119080c4040b00010010005e2461100d400004101003070702c207515010500808901001304003800388120000b08080b6034540c103084400b1003d0b211401e00410580400d811010340c000742003411103006002c40020346500c50015034202001c010040c0c1244213210001008a4001c02e180b540d141c00b96130401340000302403000815140c0b029401030000c6a14500b084540740807c0d502c034800303150903c41084002a07110740c01d011242191040e140d01d03600d6242d801c900d00843c440b03110440ea1403003040070041c842001040300c116110325009000c0f554072529105c50708 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 274007113 1250 274005863 274005887
    0x3080f07090306020a021524060703120b0406030b0703090c050105160b0408120108070501030b01030c121a03030a0305060406090e0304060f030b060d0504140c1005030c040b2701 78
    0xc00e00310707081c40000e102c1c3e001001011400e01c1191800001002c8170316090701e055400c1800c0c0d0428001c1402c40c0c40b200300b41000e0400086505500b061150b0301d0140c5010384002640412950703400c2d08000582d0346070302441c043d540008100b00d2914003200003030014800100e0079504110b6085001481e58410030403a207100108103120f1100c11070303507510720400c00005002214032200c01e020002010102c10407039402404580c0c024114640380c4000502210f0005ca212410141400500041183c02c0500140c408021100c0060414202440061401000740b50103516000003c2e41c0310445525401007030082008840400445984407107184c115806038642c0f80940c0c0052104000d003500410341024203200307900300492440c0084000440c0e9500180e0301030b400d540d68506102c107205d1103c2000303076007819100080900c40000c500003051160030f021712030b04220001000844a440420540f40140040c2c81415194041900c0504641015190000000d0303400240ea144944c4580e4041240c = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 274008363 1250 274007113 274007117
    0x20c0f0f1e01021603050d0f0621030e060d0b0102070f05090c0a0e060703120b090c16111009051306060f1416081305060f09090712050103080703080f07 67
    0x1075000303054401480401d04240600c0c855500348010042e030b010040c203015000c1e10076550301d9510603000c1115812207403003445007080c0c06c0c904001070281c5c440742041d51042d07034101c281c4500c84d284289421628003030b05154030b80c3c1000f07001c00d200c15800c4907500030488003a0240c00341c41519441d001c1804110180303101c0d442d0b1290041c0041410002080000e0140031800d28106448d82442e00104100c0da100d8403040b0009070040245081488041c4a01d11903545d0450f00007040d400c005820494032300800d11040c000381071500c80c00082211059480c0c010b1080600803058414500c1800f4010102500c01c040c000c005082c61498650307414407480007550b1240d01c8111660b40000e42c00c841d011222407040d9002c4804100641500d0044610340403041d22403515941d0300c140c4a020824020380c2075110364020b00007848585140b0f00203030240c0303100306000c1e0381000040c4d8602c0000c50b0200c0e09100910003851903e0004014010b41d01c0c01031012600a440e5402c041d01c03510b81e0248141800c80d03c2c000 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 274009613 1250 274008363 274008373
    0xe1902010e150c15160e040218040e0a0605061906031a04150510020d05040b030402010c140708010c050306030a111306080a02041802010212090a0b0d020c0f0f 70
    0x540c0605503034070a600d00506071510b1090a20759a0402e503000300c005403a25403015520003078841d58010303056400f6a41c244d810591761300750040606441d1000309034178844e41e000b00f400c1c2405440e081c10300c0f44103000100180004450711a2060320b07910511426a10181404000f40c2d81d420f16402c145092011010001e80e402c1c07a0050031801080d06184d0194544006554410240e0b2503024055543c03002d086260803003482c01007045552041c0d101a0340c00d54002c0c1d42c034014404d4006d4190340440b0040304581c0d55079529880100c55203521280000c0c240400901c0c009106d10303002440c902592907980c000c01540c0080041a54a400100d440c2541079001c040d14070001011010b0141d007100026140c4800340b01840c0c503c00030348803540c025811980c8030003a0078003980707428065080e0844500007030000a841940000352200506d001a01d1100000150b01c4055100c0c0c51502c2c004081d48419a81c8a1a100c14090082e601510000c003035446107003040000704101240d95035081c0c0d01900140 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 274010863 1250 274009613 274009663
    0x303030f0c0f0403060e0d0906021606120902060412121403010302011d031c0909050f06010804031101020310170114070c06180b010302090c0c0a02010e0d061d010e 72
    0x30345a40280b001a5401c00144000800640c080c0a051401c2c0b00c1300014000f0000c820a00a0041019520200c01c6501c140040254084011600d4003507900e14030f0f00701c0d140d840959030320307002e0160458029000500060000b03080b4481d018002030041c0300e080c0c50388042142c10030031982c1071500c510590100600b000108019802141d481004180528214080103a0300002070308182d4036a00c8100c41103030b4a80c0c41c0340126400341c0c1301c0c1e0290280e4030042019060600700c10704208001080c4034140603207080480c0c00c0c140685100c004101d01640290340d00e14090810703541c210714a1007a142483c48140c803004071030206006100d02c40210701085881a80c512004542c044651a825606a50303101d10314210044034030396004441e8003681c017480c403e514520501c240444014109869443c042c4000c901504000c1140c0d400c07240c092a10010400210000903c03003004140300030051480c120703500c0040410a40c50010021030b6400801c20004c140c100c058880401e0900c00c0d030007a011a18070 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 274012113 1250 274010863 274010881
    0x207170702060f0c1f02040503101e09080c06010f150519030f061802040e1014090a1d0a03020706030b010801051306050d150f0c0e09070315140f0303030f 68
    0x138151005095040750702c00f40c407191405084d944690014815560002400e018030f09003080041c10001030103e0412110300f24458a82130009890104403040d81c41d0090b2070107001c00709040c2d607809140301e400e0300d0565a6800400910401c94400e0400b601c00c1015605001805481a50328020025100c80403607030700803508800400c03800c0d40048580380d80f1200400c090000d4020018488800000180e0310ba00346040703140d481e90028105100c1c81e1502906105580360002d421481c108282c1c1d00c000c0b203490700c000c441d029003a40b5221040c0311481c041403c001410000b60700d000c0500940039240b40c6900d07248101d040e551110300f0300c2e000c98004001040103052404140112900c00b0000044071521080014490200c0031029102058081da80d030b840c642003446404803d24856504218140c0e4482000e01400110f901c010711504590b03000440c0340f8042c0c0c0144a03480c401041300d11040d616006081d03915002d040c480303401240c1100e03041d51107041c0001140d001e50f100020a6003141e60342441 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 274013363 1250 274012113 274012117
    0x2010b0d051c05220311060304170304032c0a06020d090b03130803042006090d022112040602060a06080304150903050a1a091b0d020d0b0a0207170702060f 68
    0x90b020400004204018803400c505100007003121300140103076603451031410901120302c0420310042c8180820010b0000040752800985682004842c3c969101c0e40d5904055078102d4200d01641030303501c4074a50085c01c0c03030404003d644c102d100c211045040140c5070a41242c2d562140135940f0041791600c0010b204190444010b50382c0804c41c003041a282c3d4040755580502c6420aa8048400000e100348840780384030300348c00328450030300b007502c91034201940c01740054950b504d0114040d010b810303031075518203902c48580c40c0c0c0010f08040900b140d004103600c0d0310300026a40310784903400044c000c80f0046224800907010300c104440e000801541080d060403441e800e94802c1e4066207003881094100040000e10030700c01614071601a030708940ea510b84d10010001000380080c10500a90844500089061444044640d184d10191195031206106101080a01ea8a1000603050b081c82c0e008102e80e01c0c1440e001010110b01c500450407051001c1003048a00e8011090001d50281c0c05014042e944003d100c0 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 274014613 1250 274013363 274013413
    0x41511070804080606090108151603090f0507060f020703052d010c1d010206090a14150c031e090c061c05040f0b01140a0e060f0913020102010b0d05 65
    0x104a5160400c550340350581c50784254030003049500200100862807411140c15401881c844000d40480300120a40244074080101482540c40f2506025140070707200e0752040c07510990001c0c40d081c002c8141c1c10140d0b968803440c402c920004845150000115201141000803254040020b00100b102244204002143c001354000e451640024103a140d84003401010f0000142c1d48500e9010103141d46038039085540f485280781998401414001c102c18002456030080350040c201c1c070712a5009503015810140418142000744a805c01400f105102c024015402580c105007205100201c0c226a1107180c242120040c400303800c00c0c0205015820044000c04504015140b8610044080402042101c0341070760156124a0300c21800010490424403d0740906520b0000e070f08a03c5800c400160f11000318000d0f4414141400042649a2a092207140c01d9503001050310540c2e1601050114a1404074542070b40150b007440440c11260602622070b010654100000c0d0000c5c0600c82c05414100c40112 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 274015863 1250 274014613 274014641
    0x50a06030b012c0a15170d030f020408030a05040e16020a1209050406170601090b06040506090301020d050711010c0f05181f0201091406060109030f080403020901090c02150415 77
    0x100c00074081400792040c0b61090b652050700241031451080c000d500382540303420003500c03200001b002c01808030000903000c6204045150125001c00c1141030440a030003554845152032201103070400e80d0329004800341c015901020301c12842680c41e43c5001e07c4443c0c1d5032042c2405a04444406000300301c1c060030f2744000040c10300b0031159441d520b401040c21141540e1000807241c4c07071814603070341071802440854018000c4003003c2c00903840744800102e0600c20352107680d105000004440419482c00e4042d40d1960041140c104034034030b0481130241503c0001c100003180c0d5480d00518812032401003021060008032559028145400309101003806070342c000c02590b216a040018002d0829220310919034040c0035400890f07100b400c0d1914210070790b104ca402540b2a0000310400ca5030766441081181241d8000c1c0c84503130b048210382001c0d81c83c1c0c840c64001941080280300040b400070f180350040d2066800641c2244c2c4a814100c40c104540030094a0003005403a100e0241d15080c00107800100d0116405 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 274017113 1250 274015863 274015919
    0x609030b0703020c070303030518010b031902011101021b15070507150f1118030a0f020603072102040608090105070806090907051c230a06021803150109050a06030b01 73
    0x14513116280c18460351003100040d480c2c00c00c00918180400e00c8401303210944009208015103240000d496440240d03850360950241c124010a580c0300b25001143e0401c090000c41d070711031011410780c14038651a951300c00b0070310078500a0042c03030404080b00707446018a6070b105402c1100981d0b800c044e085aa5495000c010384070541c021600095214007031070000b610900316520b0b1020082e128149030107070070042c802c1c0c02c40a402d401003120700d0401310341c16504980e000d5499641000c2528007a00300b510b510700300d446020b014030807010182d0007001640c900b1f8450f2003c9680d442c65642c00e07581c0441d9490005400b0b10081031181c100880140e401124040c1520711807515603000ca480240001030b03c1042c0910030a2500a00281e141d126070101c414800c1d09042c04088280c103a6a05100503008040650028440803210702c030217072a184c1d1400003001d0701d220a461170f40e1465025805c1c0110768a15141070040b407580780e0103210700012682d04c00b11060322a0710b800d820b80c00c0e5a01c0700c4d2108000d1410 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 274018363 1250 274017113 274017127
    0x180303031311060f04120c1d070306090623010311070602030f070201020307050304122001020712020c010c1b0b07050607030c08041a060d12020d030e070609030b070302 74
    0x1062000d50720440ea0034191040d40706603418920300c50305804141e01d008000411141c64480802c104480c1900c0101444612a03911403030411107418066010206403004c0105a804028109031481c1c0120780d503a4090100c0c94440b02040f00300c4100d0300c0343c00043c0b41c041c1041d41d1007403821220b00c8041c1505050000745034194019504655001d000c0c00c4803115030000401020329800070a080d004a642e1008500314a000300014281c0c1c40301610143c1003030045840d8042c500e2080d00450740f010400340d00710015616240c5454081d40000384103d504401800c2e1054a02c4d1000a0a8104490503550519011066110920b40c0d4009010b510142d940345400424030920758001424824800c400400061804220044c21980400210410421840140f0010924015006410000c1c01500d0f20640d12800000ba1204610900c0108a150003d542202c2e1a0300840c00c1c5150304210348040c403096405030702c41c0d511110385000754804607a0b600d00600c04100200c0344e81d54001403a060040c07030801 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 274019613 1250 274018363 274018369
    0x1e1905010b07031e050406050715020f0a0e010c0b0106050c030d090f0b010e0114060a0201021603110c0f030a140a050a06060501200d1b0b040609140a05070b18 70
    0x4800d82111a440e480060348000301a8890700c42150200a104c8060214421a80c020040d114500c240c004000f40807c00c4c2c030501c0612000071803d201404401c40da1a5005100c0210f50381044072034002081c9840b42140965018070f0b1101c0310942d0240d454031490b0300b8080b09450036000325411074800c0c07100703111201d10380e0410312508038540c1c06411070f510031103501c2c6030030200d500050308500b0300e5410000040200d0440d00720300400340f12048600c1d036100ca50700c2e102240240288441c241e040e40e401145c08007807580041403001c1035401c00050316142001001441a4020100c401c2d41e011350003a200c441c0492281c00084c8400c3d010002a2107202e85075032500b83c50008407010550b07101e03950391000c01c803c1d07800c00034141114040b4040b0b040360b0402c0c4402c1640b030305460821241800b00a500303000f80c001c081d000c0600369650014201c00b1908007030511100034007050300200c1d051800070200e10125440005c0c454041b0b0b512800400c041c42c1031459511003904030a00c1620b80031040c05600c0c5040d9 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 274020863 1250 274019613 274019621
    0x90c01031a0d1b32010507050d110f03090d060903020c030a03110115031a06040213030f050f03070b130213060b0a0206150a061409210111031e19 64
    0x6009002410302c0f004494050308141525520070100220f100302406603c40c280e00c49100c2c1200900761000e15900c0000050714144201c3c040104640501c1c2d0728159203542004205034103002103821200002040341141e55684176000a103540030490071213840010340e40b600b20700d004512034070560756610407800c003280c81d001c0380b21b1040340803070903030b08013410070090920440c0d00300f207401c4c1d0501c06142d18540380c05910084c2c0003602e00d058805000052a40c1d10b89404840a00c01801c0780b1f102040d50303a050040c5040d00308071003103825020701003d8047d4600c000040d80d03c601e03002200d0401c280c403901c00d4801046036452040b078201880781c0a40803040042d02c10f5100038000590440d0b0b0720807c890b002400c0c10340c0200303260010084503140e1081601c1d41c071550300c181c40c024282250031004003140080d440c041c48074000d1f802a06441c2e170b00f00c03c0da000005041011140c1009000003019240d5115940c00111402042500135042c41c9030324448400160350848282098007200c444100d82007000c1c1e07 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 274022113 1250 274020863 274020889
    0x1a0d02040e072309060607020628020c041503030512130204020f07020f090c0d1104180902090c09031903030f0c020d02070509010b09090601050415020a0614090c01031a 74
    0x2005020544856203c3d1010707081c0e00640c41211005000e14102e00010036034001e050003e40644000700d640d400701c400710000c40c1d1040084200e40c1403006e07030013040203607240104a81a40a01d040074504640c000444680c41c082d41c0d81a2078490a0000e042641d26207010000d181003c40301041c448240561214030003000401d08100c000740c1d41d1125401400320301c0b801c0002090040c070312a0200801c0000c0e007400d840349048250b10104081d40c092075807240c24052034001d4480e40306030304485441046035500c6110030501c2175900310700c1d80d903d01c24013480d1401444441a0140c0150a00d980e032118988440400075200e420300280710081f2030020000c480d00b401061000d64803e848003480560104403075001400100c030701c6101981400354102c028000c240209002d040f1036808500140e0055003511b001c1c00e0000001c072024031312090002d6032101401801e456551402507413141010416101d244100580c03002020800b203248011801000c0c0c43c4000c00038404200010300e45590f88802c84960 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 274023363 1250 274022113 274022129
    0x3060603150e0d12050907030506130b070203160b0a02120f010e06030102090a360b09060a03020d0b0402061b0a15020306011e05130603020d06091a0d02040e07 70
    0x1024a00c1d00072842200c10140321046580e1102800748a004e41c00301415065013404480818213491701e0300030301c0c03924403140c00007031144c01038008202c41c8400c0c10912100c054040c3c828040350361143c050598803803203101d50015000700e986c0300480c023107008c10350420740001c001240185000361800030707c20504802c0e00e00c40c14090101004000307040c4504130064005408038001c6103004901d00001e41c2c41c4c003aa01c20960545c280310700007200d40102d208588100070500c0c3d005d002811000c8082001003428440e441c0c4101a1200410480e04001c00514141c0f80c0c040d001030301e600a00d403a05204088006d200300d0740444204111403024607405c00c51401c036a5140c0040c80302c5400c9243c034104004001d1100701210b032040c41008010f07070303000003001d4281c5007100c8440710fa4081190210380611403114039011013134604c4000942c2542c50350007403443e12011001003006903258a010025545203080242450060b0f0411203041c2c034020100c4000304e0b01c000c0c400190881000d071740314100180b951040007 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 274024613 1250 274023363 274023383
    0xf2d020c04060614040504051308070309090c0503100b0c0111040f030c120503160302030d050f2502070504020a03020405090106091d070212030408090a031104150b0315030703060603 80
    0x660a00b0702682d0082c0c040ca0800512802400b134464001e0b01031072054512036510340c0081900310b0304254950301243c1e000814151380d00e40605026011180c140b1640100303e240640041c40d2a21031002c6d203010b0100d046e0b041d0b2001d0319041682c3c0703850300482c216500740c5d582e0301c0c2a00101020381d0014001003c0c003145c0315010310f00c0c1d4102000c440845600488c100400d02c507410002520100c00c40d5100383d118100e10b00d42c4d440e542400c80c41c50140c806404940b6107083c09000e00907843c01d102500c2640e03807982005400c4a48201048000b410f0842c0e0350150b4030290b410700c124901500078009101040c5001400d0507561000210881800c5e032104021408030358051101c04240040444a054170b0140d0040c6420080c200035a40c01a6904840a228002c00810104091a412200c01d254020151200c00c5e0b1039060a909003031502911030f200d10700e0195800c0c200080b91489000b12601c01071054203503501c5440680d400040d850350035034540180c4001000080e5544104000385001e011026 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 274025863 1250 274024613 274024633
    0x204090204452c1006030503070b090a0b010e251e050c03190e010f08070503040c030f0b0a0c020c010c111504080102030a140910090606081e010f0c0f2d02 68
    0x505182c4095004030413181410010f01c0450800012140102c3d400340780105581c0c1e0300c0b42c10701e080a03045030307006003441c1801c0000a89210040e41150080d408020050302a095a850504140c0e24020210380402d60049140c014180c4010000c0c1c0c1e01821820214138169828503140d0456003d00989010b01c140c0c941444c010315849108449015001c2c00c1405460110110162008400800060412000000241c10811301d115020300640e80482084a81d683c3c80c0b0340040709150854241c0c8030a803900c1840c1c03825038400510080e0740303541078654003025a140d4841c03a503a03401401503103400000320080c0302c0b5044c00341d43c0180000c0540a000589074140b45040b10f007074a0100f4010080341e40c0c21014850110780208003c40d210401e558001608681480d10300044c162540c0414043d000b446450b0340c8900c0c44070701202076100c5050080210b40210350142d030072200b11840c2d500006403240741c41408907010f00e042d0b0000a40405a000703907004085417221034484003001030710060300110891 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 274027113 1250 274025863 274025951
    0x7060504350d02060f0c0f0403060f0f0c0c0506101217090a060f0206090607080601080a090b0703020d06081203041514040f031106010806070c1104020409020445 71
    0x30b410818155500703140005400103040d65000b00c0c04040c0c26159072f0318601002c01980cbe8441800c0c840411403d011b00b80900a0140000441076400d8a035401000700249140c218010800240d4041c102c49030052440e0351a84406a07000c01e8489034005005c0040504964503240410000c2ca000d075680d441842280c20000c0c00c110010303002c2c08d46a07100e030f018400616046094294440000e18100c81e165403690b40b036001400b8004805003d0410882c140402598103800810a4018140040c4140c6a4500034540c0c0ea00c1c4215800c400c418061022400141104510310706280c07101c1c03400b090b02200e180d00340f440c445054804590524840c08004c0c00c0541202071100301e144400d0207801703a50700d000c07074440e15984000d0038501040b4420404400b00084502240c109803006001191601c0d00c03089540000d500030301509904000300380104a880741c442000e031100d0035110b164102188890568601d01c140002e0401e008151a41034444c85c0c0c0070301804041040c1d02c1d500b101c1e20131403619210 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 274028363 1250 274027113 274027141
    0x309120304080d03050405060402100c06110c0f030702030a03051b030c03120903091005090a17010504020a0b0a090303050306152b06050a03140f16060207060504350d0206 75
    0x20383c052504010410000c00c40101c0c0e025401501070340c040428007e4000d08590010903942c000f032106140046d141042c0c61500098800e01c2c08110498140d41f030224880e46c2c0d04e00811a00039490340c044020000082e114070060801d280003180001c3d48101488111402c2d50000f1282d1051684042000a80c82501e11105500410038074040c5150032400030110301e0302c16180d440c482c00d102c00000c42010545032030040200903d0844001000302c00d00070302850180038141c4007a07110340902000410070540032000c803a18600c1035201c507003070189180c0c0c098a0f15040204802da21038094905090245100c0008141d19010203548001d0304007000d1032981d010010755486003800380340010031700041d2920f8036604150303a08031100d401100ca45035800b51410520380003a10650051141d0900d804508a407030b10103540b01502a900c1340e0351075000032100b5025500c1186900c0011600841e0400c10f240c403000d441c0c140325030207807203e481c0c0782c040750380381c40f11051501c0c0c01030303000608002c409504038003 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 274029613 1250 274028363 274028383
    0x12040203010c050702061b190c1805100608130803010e07080919020f0a08010c08090f1204120c0302091e0c041512060f1d1605160302030912030408 65
    0xc0c043c4c10f002c0290007044280c011203a00d008151005150803224402c1080100140201801042548209407070311250500c003510903a42e0319102c450f80710700b494070306009e507c3c843c00681010300055440c01ca42159514006070215a4150720b03000c2880200340e100000350702822441c412078019090480c80201400070082460703140e82c108201da07055030003400040400380c0c2e4049988071008041d0b01e002403d40c240961002d122580b0b0402101c03496038010700d10070310400e800340981c2c0e40020070380c00719501e030030506801400d02c50f8100b20501013140d41d1040c0c41d403e2806241c6220182d5225404240c400c001030707030000b200b0205600b0403078822001446280c0d1200c8280f8440d41010701d441c1c0011140600c0300710b108280aa8000740b1000d80b006070f40b0120042000d80b03d840a81c036035641e91036503501c030000c0d034200621800c0d000083c0d20016001c11034180d24581e80e600340c40c00452141540d6100c41400c0c048045000401c00c0c2803403903640401c100407168541010f103030380324500143c482c5072180c100 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 274030863 1250 274029613 274029617
    0x21017010b0c162702090307090902031603020d0f140f06061306030f0602070f0c061d03010e10110405120f0d0f0e040b04060905040308010807050102150c0a0504030812040203010c 79
    0x69020300002c04c2100b001c0700101403c1e00b0b04840583d050080728007038012090b42035090711404800168040701900003403002c43c02039050703441e00b00c190600171502c81350a001c0030750083c5e445d084000c00107403182d800c2600c441c044c0f19166804840791380340508102c40c1e000d070704405074004028001d0a2030840c09188564052510400c10640385a845400700040610054000c0b6408941101400890100c101115910010f00c0f4500744c0c8541c3d004d0810884d0442299404aa00c41051240c0c01c051080c0e4500000c040f000f4140441e04444c10005801502c2140b880d140c3c0600001561340c40e029004080f5441380405008000380044801e03203011480c151a0040013040f0003250701d8030740c10036081181c01005542c01b049856041f030100f80600320907404009032a10f00401c0005250744000014141c40b001020f80b402c10340e4400049035100720340081c01400d075194401188441e45003100410900e01741e410f0440c2016a02d403910350031600020f005000c0da0070390720100001c528082c803d00840510074 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 274032113 1250 274030863 274030903
    0x20919140301020715021602090a0f060506030f04020409061d0f0d180909030302040b04062001061a090d1e050d0212090906012f0f0303060607021017010b0c 69
    0xe44070003140d80c99070740c41c07070349111b81c0000c02c46090f02d00001c80108203034002d0b28a64050a15041d079000070003d00c08907550b440d2800c0c0c400701d02442c010301200d0054501d22a04405510340740c003040300401c10150b0440b1426501e640343d03100349107848814043d0320460030161500c040ca0b11034450400e01d60341030020801002c42100071006480c00d0740a825038244040010704c002051600b50000d01c02c503003101180c440040f9000950a41c807003002d8100803061501c2c03139804600000d03100d00f6185540605080c000d4030406401104190b68090510035100603d1521007078042e44030030b11440c01019981c1d0001886c8440c50051107805c0103e10f00c450080d10080a000039818002034150080041003417141c0128800700c2c100b68842ca0f144c1c02c04c8640001e01c0d00c000000d000c0b1340305e00c402440300d41415500411404e410301c5c901c0802528400c4102812051034001c442d03003001007450b8036180c110140300c02a010060030151408003640038010105030b240e6202d01c1034107400d20f80400c40c50140f00842c00e0b = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 274033363 1250 274032113 274032127
    0x1104090c170c0316030b1e0a090516050310091502070302010c1107080d0507031e030b0a050a05150a120207030e1206040c0b0c01061d0105090601090e040f030302091914030102 77
    0x50041504100d0360080b480c20b02c1900c900c61614900d00c0c40301f080340c16207042c43c4280302d4915603951024541754424000c8465021444038a08481c0790207205559250708110380c9030107101308070713040545140d200e010b0990400c413580719004100d0300014000d42c0140e649443c50030310700da000340c2030090300c0000e0710007480b0162404035100c1d5904088900300c800c0060200d1a40d00b0580280483d01c0d0305040d00c00c08007054907a80c02c001b0001e2002001c0c0364458080c0c1c090006150401c070b8907007002e5500c007600e00441d404004d1001801076016205060410950010104d00b090061000d01031940c0300b60f4940d064021020100035820b024914081620340101050000040030124943d0031624808603080c1c444084c900f0080c010425070380031000c03031303c0c4003840c005016403640c810034140c41d412a8412010785440340119600c444501540d412102c0000c0410040b48003100c2c00101c1754803074900035203880b8000d40400c1416580d07072400001c15813519800e0105000c01143d50000e40401d034021820594 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 274034613 1250 274033363 274033393
    0xf030c050409060e1903080c0a1b1407030305040302030105061e0f22020403120f0c030e03160b0309010e28050319050301090609060506071104090c170c03 68
    0x180c81090722a07541c0d14182c1c010441c4541051110850060035121003030103010110003078900549003200050003800000b100f101107001529070782040c0d0340d0b4100c116904090146606854900305650481c294003c00140001c00c124002c042d501c2540c03070321740f59131035841032509440c009080c1358820720040c29004074101000000c06d8900400b142c40004003010000454038a601e4600101200c05207020001186400c0390010400c80303128511058034444100c200712120401e10b10305200140200d403000b40424443c400303284101c4401019116141c90100a0059a2402d44e00c101d0f02002d000c810842116000c2c40b90000403035041c00500380c407091652004020088000c891242c0001c031214001c14403504009640110754031000000207032250800103041500248281d458050070b103038001c90300c404180039840c125400078041c14140b0740e055131541d00020302da200300c0e41c01c41d99840340c0f0030201e100400a2001407001100c4c44040b200200481418103200b03001720b0f8000d61002c40d071000c287c0c07 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 274035863 1250 274034613 274034633
    0xb070636171303172b0608011b080112050613170d09030f08060901051003060b160b0c071211010f0c05130b120106030e0f0a05010c090914011e050a1409010f03 70
    0x1c1c1600d00001c0205e0f20005d2402c0101354603006988150b180c40e0f0103059201c070040d00d50180165680720141140c1e038400d02152503000010004107540c12031004500d07030074440a01c141000f44511034281d01d20030640c0100f2955045602c15a14940c0c5500050081c10341111880c000300580d850880e189103800d1005c20300d03954040c46510f0040a034803402542e9a403103a4002c102030a102440c9660b030307926060024103040e240f0f01095864a030488041500c5481d018122001d80d42d005441801411241d50107580040c291490340200b5526110390304070000b0540b0a131080001152545902d440c000c1010380c081e501d0540180345000c02c03c009020541d070544004a044400303e1401003406540d030701e034840c100810500c840074584110441003003045411741200c02211415614000f103150303101162815a150b207014405810344050050080b020a03c0c0440501c03843c4007000c0444075035803000b14140100544c00031030b403c40b0028101540e498510143c60040c06e8505c9595070050841d11000044 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 274037113 1250 274035863 274035907
    0xe07020312150a08010f05161d100e03060a0f050a06080703060506010c08040b0406030515210f0a060e060c070302120706060506040b07063617130317 66
    0xb000c96858440d40c20381c2c2da03452100c081c1100030300a110030007540101d440604004d0f140324265425808601d9115445000300141c464441da4215000040d00c0c424401c045152140b42020020550020402914100300450250786003d0000807981a810190401c40301c01611040c580340c10640208410b41d40002ca00054a400a9002031144c84000040e01d41c0c114141c4000e201650101d000200b1032585070250088650544050019076a2003000e120b03100040c00990754000321003104500c0c02c500d010001014480040100d03000d154400740c80c00c0c0b411032400070450f140d64807500e600481c00002d10010740c101e40313080a491300308071441c1d401a40302ca540c09291420118041052000d20540d900a0001002d01908203030b07856840d030301c4281d1254080340040e60783c142403402c075002e04440c0c1e0b00b03076070319405007892031098007601e450392201d049003040700c16660320310021042007004040000400e03c8202d07111403490102d00c0c62920300e0a402030200401490901440384050b6429034100b15020 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 274038363 1250 274037113 274037131
    0x30b01020c012a140d05090d06020c0708100b030c0306070c03140702060a05070308100e01061d060a020a02030601060c0c05090618040b2703090f06070b0906010e07020312 75
    0x16030103903031150f8a4030310030702290441c0c4044882c2a020700c8540c01404070300074103000c01d483c2c0003180501d0607501886500400b640160755a081d840c040740d4103a002d4100c2050315400c0d28031044c0c5c2e401c0b41c2ca190000d980800007440ea90f5650011442c542040403441c01801035010f81118544600041e03c14600e414003d02800b40390010001034220003c226011107034000e0015841d5502c940c8014a00c1d0040c0c1402c0b00814201c1d4003041e00e1a510968038002c454010810345d100740c0c01c10004503001009491540d00350940700c600880320f81d0359140500403801095008111010b160b00401d0301e861010303400b480c1840f4807407045a010070070484110058032000c1d00d980035030b915084040b94080f4420048019210461400e000401c2445400d85015032035403a1b10304030500100402060b0300c06141940042070b0b2080101071140c1c1040c1850003c20303080200030703508040c0c180d01c8403044000c007141c504815812107001800b6008800006a030840c10b1480214106022a42c080001b8030011344200c2c2c07 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 274039613 1250 274038363 274038377
    0x50402030606100c05030a091d15060903070302130203070801170303071817060f0108010606120b060403170915030112020909030f0a090306060902030f0114041103040f02010807030b01020c01 84
    0x10f800760198030114070107075108080b0380d40c80c400c2d44001010000140507a8095040340c4591440409144a00c5405000c440c1d950200504414003044060362000b00d260ba05030060000001c0035999442c01c5980c20b001000000d692840c1040009101007016044883d00789610807024010060001c2a254006030b40d0a0050100e00041d81c4080e41c200300c2d6021041c1061f19564400500c080458000e020711050f0384500d0590340c03030380d007080d003030355800d0140b180000d00720b81440a0b40300d00c0303420600e04202d000d445146416200d80701c1200c00140c0d1038501c5004407002442180343d0408414010924800d0040ca5055504242004180780200c00b0041e104045400c08160f41000920481f0f16135200b02140d80e5451105c15006010303146580300550300f1515159000030a40c5250003124464a004640c0041503030070102c00c807440000da40c2115802c50750f941e07180c0f2085821400110b00880c0035084030b000f42c400d284001400383d1002802001050300b0010348841a9800144141c0072000c04d00f0030325 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 274040863 1250 274039613 274039639
    0x31103010c0518041e02070201030c09050d0b0612011506020c040504110409140708010b0a12051e01110403111e0303040605160605010b130e3309010e01050a060201050402030606 78
    0x40d015201000c1741c0c9016084c0241258004010340c1d004141e01e501c00e07281401803c400c1c40080e140d1031690305ca03094204070b40c0d41d80b840c00902c500c0d060b03d911007401003400c00c442140c1441e55086402c184886051182924403d01000e601005401c0150754100c50134841881c10b40c0e902c2030014060501c0600954540e4400380c10041c0c0e1000c81c81790803040d60304039446140c0d2243c2c0240a440c00180080c00b07454129030128040d0a45036000c8103c41c0c21000814100c1c0308241c03d020b04000300d0340e448000795640c08a0380100f11075074000348003c0d802503200b45075503803504003040b40c099840c80c0c1900f41040c0c1031000100644000c001e039800c80b0564100951110718104920001a120881c0103001c40c2c42c0600200d20000280041d14240c41d05288101c03e268841290050900041d602070082940c0061858101c034282c403426100c01e05c15900e040c02d00c4501d41b0104080a00c281c0140c41400c6101d001071000e1300f00229942c00a1440d44020b00550500750080380d182d21001d8607160107449055902 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 274042113 1250 274040863 274040869
    0x2a100905010207150b040b030c030c09060a030b04030915030e0705011d03030708040e2a0f072015040605030f06040b0a03030215130302060a0507020c0a0807031103010c0518 76
    0x81c940c001c3d00400e461000e9804e4141010040c400c0b0302015104a14004541880e03040c0090701c0300d209507014000b00490802801008020080144950740c4000e16000210014482c1d550700d03802144261200400b1500344aa20380303201c0340620410041619002045c0403d020004240049a000b82840008035011401451a9101d040306007601032200017684401c0000c42d80040c01240c0c85a0b86a001036100c1011b400000014807404c1c1c0010700303d40200103008002a4010b000302e1a14120241c54808a551016000e03201ca44405c03508021036000c2c99070905043d94816588100001000d1825041130f20103800c0303001c080c1c9105506884203001484a89440c0c2c40764000a80092043c42110356a180003580d4056804075158035880e03c0001c07659a0f4060910030407015407580240100785d0b10080c0790801030030000d020708218031440707201e20390070303210441201c01610407d4081c021090842c24850b81d500c0d40802018000c3e80340c0427084024a82c40000d54a0032606d940144040c5c0200c0300c00 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 274043363 1250 274042113 274042117
    0xc1c060803040e10140303040608070507020a031a0c040b0d0207020f090f070905040b1315030c0b0d0608030c030301180209220c0314070302072301022a1009050102 72
    0x4000c648000207010480010031800c3c140b084014141810903e911080940d0071240301c0c1940c00d4266005010a11585006958a030340c07000080c640306d03042c00d6980c0c0000da5103064131303270003581c4840406503000c41c5c0b5082026107a078003020400ca120324003890700c40400424810342c0c510b280317800e40c040b4440c030855640303108500700c110b401050741d00f0301c1c1009a03120ba811002554078001184014600050b04e0406000c2c0602e000002080103d885940c3d1480002034101e00c80410218500b00f403010002800b06141400078103447c1c12520b440e030011500240c22607005401c1000c1d00d0f442071040084034880001202c0c1901c40050341907500d4480390b182c1c00040c0c0120f001d02980030020380c11920a0301c4a03400010000c00458030103019103105e1000c01d0f4221b80c00c0866001c0f1018109000620840c001d400800c0c80a118045001b00780e1441e108504010a0b00381c10500d09940010350740000c14019400101c2c5070311884501030081404248207503580c4030104505880b0307a2220b400805115081d41 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 274044613 1250 274043363 274043369
    0x507120201020319020606090a06081f18030f0201113c22090c143f100810110d090c060323061c02030a060912080c1c06 53
    0x50b501c43c100c900c90f80301039150141254001c8c010070a503000900700300c065000c0c2c00f04076502d8901600450641c0e200f0300c0300080d100b103100c4d021280c846000201e11640180d000c400d082c001e40d00c3c600c0114803440b0080c03d68010b10f144c068803d034180700d80307403610500301404a4151801e071000305600b020780140c1050082502d5002c0200032000c01c503105018000204400008040720402d9003442d1120b85041c2220f08100d5090002142240486542c0c2004c200030001c3d003a600f441c1c419100c00c44648c42050221180010070744208115024041e10000c01c440c54109040c00e10900040c1d040110441d80c95101800080c42e6944038410051354120280440d4030000e011141407082020b40d0130084581032091003500000b034a800003d460005440f801050310945052002c04035440301010441c0e9a40900ca500c41e51282c983c1c018401030b42c0400041c98100d125940210705058941414603010b500e4614100c00d01490750208512034207103908480c520301103000180808016040044001c0c03103950 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 274045863 1250 274044613 274044637
    0x6121b011e030b0306010504020307020d0c080c0709140a020307210605040606080603120405010f0c021203041d06030613120e0907120b06090d020111010908160203010b04050405071202010203 84
    0x31a0304001d10707502d500079081601066040f00d4035039a030340b0144400c074071045500d0001070700704008206415228500707c10b000c50080f0380841c03c0101400b201c60400301d082e805114103903a03940070300354000300524189510010a1308118213601e410180580b030721300184843d80d010010798180e0121010282c0c004806040301030310170004152184400b6000d18015640d44d84a03106401d20628800b110310100c40540b20180d43c0c20b002c00f0140d181c19101072100010480e40100050008500c0580800240c801000100700f034062008081d80c2030100441d016100501a801c008104540311860395440100d10364000550300b8400c884150441d504d00c0100481c9502c10071070010b0064499014400c3d00040c1040a0100302542c00d200c10446184103031604250001b0040341880d01540c02010305403210200480040340c20910b541d20454254040f18855140c0074000640e541941001d2003000e800030810381e0104900d0605d0780311749607502a00c0c811041ea88044174514421a40f090041e642543c8c00e035 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 274047113 1250 274045863 274045907
    0xf130501050403030509060907031e020109090e0303010303090e0708070528050c010c110a03030507051c020d06080303040b0109021602151e03101412030c0c0906121b01 74
    0xb82c50000c0c0500426111910548507007c003182a5002c082041001c803030f80522032400c1400c2002510b002c801071800c050707060108d0000c00281c0701d0b000b4000e54400844403000307550350b0744c11458090801e17010754001100b1044000200080140c21403504c0c3c1d0402004e041441d110301c904200c3c40032441521034513241407000c209a160a10b50008040c00900e0f2840c0c0090007032001046c0d0881c0c40e450740300001d4609920a08000d400702c0d00030f5024640003400307442c01e1440c0199410072612201c240036041c00c444c650001d0001d800e447d15128a00143c07001501541c91818240c5803103000b03820600540610176400500d0025050000d03aa25a017a0742c05040c041180001000c10005a0002039560f02c0310700c48242c41c0664031000804580c420140d101100c00340d04c0c1001c200f511004a1b0010381340c2c203c00b000302e00b104406020005400c200c24104d0040c141c40030b48500340300f400400941413030b0007070060502c186886400030a0558000d1040800260f07001a402d00480714180e00d402030506000e00 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 274048363 1250 274047113 274047121
    0x1b0304020d21110312010306021305090c04030204050f06100e03030d1806150605070305090103110301080607020708060c0a030b2704120e09040b060a170f010e01090201080f13050105 80
    0x140d4601d030410b60b007454850b44464a0041000383d1a44281600d01d01c610407070400510010b2815400f4005101461010b080c0c0c058481002c989203e03400d681003404d41c20302107000c108600c1d05001740c3d40d1201c402c0482182c2828a0401725201391102200705080c048005c8080c10182c4041050f20315111130703660309201140000d0020003086240301001c1d60001c1c03d140450a41c0c101003a0134070119030136a038400d45060215142204e0540190728128105900c0f0302c0555600d501c1e1001030b501032301204001d492582080301c0003900e0103403d0303444011150000004c00800701402c10a43d6000b41040c1004114501e03a680052840c0c04000260082108540003607a2402c0d440190076100d107101d034284100022142d9001e90700c2e500d40380314855101010100080000d18080100d90b00054050039403a490f0341c903550100280c036481e0601c2001c41d84011143c0c581014240150a8191000c4d0001c005503015900000c0c041c1e0001003405d40070440c01400b1400c05030300c8511541030544c220000f0001e90030 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 274049613 1250 274048363 274048403
    0x20d0201021c0c0510020301050f1908030423040e0607030c020312010306060e0714040308070609020d061a09191508030a0e011416020f0402120f0403171b0304020d 72
    0x8001c0c1c0f0030340c1c051040d4400d10002d034140c0c1c82140d068400040c000041c00e13030402e04019040100d4a0303030442c2565400d500040400c020000f50001d800309400d07190540141141003c0c2640c125112203229600749405941c04a4002c1841a04880b0514021849480004040c3c0c80d5105141d10700750b00000180c000414040d1690008041c2d076601019a9419102c212040703595a00b0200b07040d1303515004100810019194030010100984501000725808640e600002d0300301180f0354042c0c0b1810b0326009901030b1141005110074078050105c070701400c01d090580c16544107030840e50303543d5a15a512500da04154144030206030051031540d088a0752041c0d030040040c888901050130a02144950f59020451010300b02a6140303500c0b441c070107003115881030f020058041c05c5a2440b5400070707401c205020704030941004030b034460481100e070760f0039a040c0340c58024403a0300c10414034511005d900c41030101c4e03080d03150f500080030b04e500003520b9201c2d04c407400024000540010000c0980d800302c40c881130044 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 274050863 1250 274049613 274049627
    0x3060108270604050f120c030405011d100e030c0105040b1606090f06060f050105030103080d05101e050907020c240904060806061207050d06020d02070b01060c060c1803020d0201021c 80
    0x1003104011b5400b0b650701c0d0440c0984500034600805007640042c0402c0c0001c0d48140024182c01c000401d001c034101220394081804001c83e0100c480c0010420740001c400e03820100080901c00c042840d0603498140380c03031008000e074041c2c4000c2d5200c054001c0582420311101e41c010b2500030780c201d40a035680b90b01031714100380140810721940e500340b0a18840041c00f07601400a0fa8101c0750010481880c0a24172080f9000400000700520300c001150701d8041842c04081c1d800c0b05c01d0b158045c0d0b114100c94240b10800490140050400086601c03525198109807034080008040d0118084003908024107840781a2a034080c040b98942c10526007000014004400640d080c01a20103032a05d0380144500801291a203090340651038121807415084000a02d0a50040105264002d8010704040b180c6c1e48640d0500000e03409240020702458079035043c00b006200d01004050b05007403c104100d89002e090f844900f00b48806440303160b0301c800e2403095900910680c11680c80035400c0c94103185e4504000f034201 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 274052113 1250 274050863 274050883
    0x150402030c07210801030807140d050a080c070305041a090d0f020108060306060303030c0f0d060603090302061513020a050c0105090f0c0312120702030409050106030f050c0306010827060405 83
    0x41441d80c0102c22030030421043d018a4040558501506070300316102d116507984511411035414034580d8600305001c0c1d0031312122100b0880c0d50344450761410f180c1c000070b00340c0c44040c1012010150402a4800294002c4112000c80300c01d00550f500b07280728140d500c00700d4000c0e4407005411100741012030382040501d0104205840c400d0301e03181e50545410050660354403040341e50030b81645c402c00101d070034038510300050141c1102c002e054625280c20400501c065609507400980442d4a5100300c0e401c15805000095101400040900e107079858600003d040b4030010121031121640000c0a004061165040707070030300341d0414000d00403030820080786035403032000b074a402311107001c0d8121b00c2d03c661402094011400360040d039080d0411300860002180c13000c0c050680c00a40c4000c1000184c80419809114001d00c081d44000990402c3c07070f8945400d80f40010f00c0d01c0c540040400411a1581e08000c510341c025200400c034aa02e4003200d254507c0c00080d1050005141c815001008100000004c82d0611 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 274053363 1250 274052113 274052123
    0x30705011e0c0206041505090c15030f0f13170f1605071403060406230708060307050402090603040312200403060b0109061d011e0201050727030209150402030c07 71
    0x811141d84803c80c1c840c0b0058400a1100350140c243c01c4a680302c0e03401064110b08040e042e20703444a04440041c52803c01e0306e40209071a40084100580000c09480701680080b82c4404015103281002d01a10390a00c0c1000040c200d40c411440d41001c81c01c0a41074a0546025805031a540c1c0130307081c05030100800061080341c0901c20345001103a81d000351582a0862000540240490f0310350760380d80c134081c2c14290b0720295006d43d14540005034000301c1c80518002c601c242c4a0315801e003002014581003060a4001c280203034010842503081c0e49600f02102d03440368140c5410410807000c000c10300701030429808043c202602180d0026004490344006104a030700c03c10040012040d01c0300150342000b60341c0300300d0b00850003408a500d8540448400fa210085052500388681c40c0210324104440c1d51000707a0b40d0060f0b40d01e03800c000384260460304104075000105030b4012901c01c00910070304401072a010003030189040d00d0202e21050504100e00d10843c40080082d5200e2804030a07070581d82d003010105079a = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 274054613 1250 274053363 274053371
    0x2040506160b1501050414030319050a030501211e0c06050c0712021f1107062f100c02070510050304290c0f0702041401150e21030705011e 61
    0x50f24414610100c01001c0042c0c60300c508180c98007040c0343d40c0e5110104d6003034140c0010000c00342035410003441c82c0080c0f6026252076172250080d5030010111003050300100001c411180f4100070201c1d11120707210b01280c0c02501f601480098000b44c4080410200d4000e01c0310b80c2d540300100d520303500040940700c1006040201d41c3c41c2542c2d52403252a1802c0d01c44042d400c1800b50590b4101c01034240050408901c80e428145040403090300c4051400e0000e40c8008000b8419401114468801509065190354520b00c26141c000c0c031000b8079070f1507540c08044c0145203a030320440e8806040c0240b040e5801072000a10000034020360000c040d10b00e500840f07007107842069090800c2e060132101c2040da003155050143c00062540ea107104a40f00303a1040003c01180e403010300541c00140d855018043c5a018012850220395241c40806411202105859018000d90312603c10403521b4000c504500342040c040c00184048641e41428210f214003100a4540e500b0f03d810011410344802c8020420003003144200 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 274055863 1250 274054613 274054621
    0x21e030a02010b03031801270906050127090c09120602040503010e1f1107020904230d020c09060a030c080303090d0c02091503011b08040b0109060f061202040506160b 73
    0x55120304c181d905501c0d52200ca44500074065200f26400101d15540c07091230304c50f040c1d1040300c08101d54a41d0f03005042d070b01d07291003084c4650b582c800071141c0321150485410008240395005211050901e00407240d140c0c2d43c84006c807001174401c1402c58001c00403c0300d191800300d12400c100000e5803041c000c032070096080c54040c15250500042d103402c290411114110490010740511001c1d084a01450300919000d02c01c113800b6030344a1440601492050700301c002800c00c15150020101c1000c800281950407114545101e641c000c549010f001104407031800c1203585060024490401d1070300b000c0e00380603e041000c80ca41c6000401035008540c0c2c0f200722010040c001004407005007092800070740003c000004540e88400c1155102083c1300010004982c441820841d81405000d52070075000040b940018007003442034135021580548000c41c0d05001c01402c216440142c0901c0740b00d10410130524095150414000f0360568000d04801407113203940318050031140a1036003210400351600e8001c40c000c5 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 274057113 1250 274055863 274055869
    0x115020c0102030d1109100201020c07091806050901090605040c061205040809060c011b090f050402040f0b030403020102072102010c17060f0f040f27050a0b07021e030a02010b 77
    0x821035900059004500d00041d06042c036015112119042d083c1c141c0070301c0f813901e05650303881600f0110001540011303115183d16814610b0f18416600c00b12840d4540300c61103207034070306405481c07211907080207021030035446201d11070b40180151100900b40c06d140c0003d0104000c2011890400c4655030b58a880501640200e80d03c100e4506640040c001e0408000c80011824030700058401c2202800c000a41d81180c45190581e10460343d5581d0001460b5410174408600401c80000c094401034608500385814940703400c0c1d0a014502607004001c00c007000103010140300750102c502c100d0f81300864058205070407054102941e072000020001d54246044513811364440c8220041081081c020700c04103440b00414400b2590003040915004404580011615100c07801011001a800c0c40c000480c5043c00c280d2031013070725600c2095182080042c50708800300d4000a05180c0e81d82d00449140c03030325210160140d01d0072010000c0d0100b450040d0800030025500030000d440c66a5442e00240143c055138020 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 274058363 1250 274057113 274057123
    0x2d03060510140a03021c0b01290403150207170a02010c0323040206091503130c0509041109060d1a04050d0908030d0507091e0821030a09020f0402070605011502 70
    0x50f00034100010801c0076103000e000320031503660400c04076512480e003034565841e8074600340c0081480c00f14442892481440214110181032200d00086080500b980d8807a030b07680301c0300c01244030344603000320b08141841003a01c2403036a080081d04000b030795031600c02000380c042c10b4090381c41c1010901d03084601c010500002e01c011181e81c0c41c1c40074408150b841d81e00704030715608a144103980041c8404c1116602580c81d0740103500940b621000a01c00622074075140040000d00d40103140200000000d0200060444113407040c071140c1112030044603500c8501003901d00c405c011002e800081c1482100003450380c07410720340d4000c1e80260183d038106e80c07102c0c0c030650790100c0300e103c1c0c1c05107680304001012080320950b03c010b4000816107010240c43e5a07591201d0852004e1440c4030358a405c0001c17081020030710402c800c40746032001c0743c00074001c44645032456060303000c01065842d01c01e4590001c0401c669130030885802000000b4021501c0303000c9810110002c000c00d010350310980598440c194002030000035 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 274059613 1250 274058363 274058399
    0x30c08070b0f0a080406150f030209092b0c06060e04030e0301020a051b0a05070e0a0606090b0301091a040c0c021903080a0c0528030f0c030203042d03060510 69
    0x1034000d14141c42041d0131138001c80f000f081035540d15aa64900d10003120480d1051008040c101844100d241c210700400a40d4480500302c548d4550240f8076006001c601c1400240100ea440c9210780440e1740030400683c0c4030140c034240103060368641400400c0314000d200a0701d0240b80282d40e80c3d6500c81007a0103142c203c0c815170480c200411003d01001c0300c0e072281c1e00f21002c400d560200c15100b4058580c0e840700e113854420782001c4a0841c041d010081940014800c460003841d03545803015480d4503206a02c21941f2040c0120b1740150b80343d00306183c2400b0b440380e400d400950040d004114101c000c1500824410000100320311941d2100c0501c0081c5410501400503a90042986840c1c5465444280c1704414881c404031101c0c05001402503885401d01c4045941d2940c900301c06004c50441d2800908942200b04003100340549400500e0200c0d60010030341f4103507241e81107440c800c40c401041145018405500b1941b01c202c089401000300b02c125049103024481801d1441461501c50042a0342c2c610054 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 274060863 1250 274059613 274059637
    0xd0e07061407020406080a08030402011701030201080c0f0c06100f0503030705030d0b22020d0b0414010e100905150901051c060c050705060a051b090d060f020f04030c08070b 76
    0x300c1e985011500010042404601c01880022400c3d80c4200060402c0050402a030741100003108000075542c211552105041cbd0302d000020742e40d811640041d00310b030b101800c1e005140c0d00102e03041007c400700f00304079103201c2148000c8130702616000001401c00240c6014100085080c41000549801d0000039104030680c001d004d5410404100201c000401c190300301c245d031243d0b20004000c4901e0074041e43c840c003441c00c00703030242c0e6131241410100191220792080d41d02451030302401c0d0701e00b50640100c580c103641c40c82e450140300e5101c2c1b50410358550072a0308040b45075894101030000b0603030030f03041c5060a20300c103580d602034680c0e9401c100312007650200d02c06140c407c4c10400c0000081c080358855170300d40581d400c0140c02e00c10303c0d03281d20b840d008040364414401d82d650422301402c040b007019203202441c040d6080b140340080d0800031400c0d04000120040200f6185c1c04215882c0b00681c06507400544c81403880d903201e640d02d04100c40e0903803036031041040c280200100030454450b030f507003150585a419 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 274062113 1250 274060863 274060877
    0x803030610020a29011d0604110910080105040501090c0504140105040902040914090c10080603010605090421020105012d05060f0705010b030607020d08090c10050d0e0706 75
    0x103401072201c41d0307000d0100001140240464640002e403c04a6480942c241e101e84401044405403000d041d6001a04068101d8a40007424440c11703820700c554541c000340980e40854000c0001e6101c0419000340000c10b580850700718400400160300c100194100c920845050101e640e84400027000c40b050b00041e1000590100000e02c054142c0f079903040e01300320041c90000d28296645071400101e82003a0440d040310781c2c4880411750310100c5c44100316002036652010f89450400480050f4103484103e00600a00c404500010002d64080d480300000b0076014180303844034500f0b8038000780b84441d8a40e1241400d03120101d0756440300d2052140c03034140c5618101641543d164200c1a0305030312141003046440b007030004008210703900c0702c0c0701401c1d1920134585025110701c07c030b203017144c00d40d00d04121036406644001d00f044485640000c4520008416041034000394441e036482d582807100307024001340c0000001503080c1085501000070310000300b05a01c10021850130440580e10b071005445480c00050742 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 274063363 1250 274062113 274062121
    0x3090d2a032007090209120c03030d1a0d060912020706080604050408090415060905041104030209040804090e0307230607081504060b0301060f0903080301030b1e0405160f080303 78
    0xc00b8041a000740c44161100016180c9003200d1401c689a0061140207402060106090924007201c6220030f1100c00a40780d80c107d044086940c1e8058111000312051320741c10b448a07681284241003160070400340c01018000407030304000001e00417a080440c2e52805811070307a20924400b003540c1007517406a980382e40c0203450b0b040401c00603040c042c2040c0c540c51420080c0c803c09a445100f80900c9000607900c11a2042c82d14401030080d00780c5900440c0510f0070700080400014200c0200e50581c0e0781203441c464151207508201e0b01d50300071601b0011140c0d14040d50780306030b02e000001074240c0a2042003840e1100f02c840c04003200403c110805500c5079070105d8007103801c4a001c2c0740d220394041c003041490150050701500240540c0c1e201e07488141d200c0320000040c030000d640000b48104045140c10842565441e640e41d140c403034441440007600c64000c0601050158002d0341c550140494030f0541110b40f403c0509010380c682c1f401410746450180150f20028504070140190380464100d0b20283d811551 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 274064613 1250 274063363 274063367
    0xb040b0904150e1603061401021905070308040f050901050d110f010324080607031104060815060711040515060a031112100e150a1401030b0603090d2a03 67
    0x640040b2280588019800205869483c2510244994042041d82c0d07042808808017500b100d10580002104040510984080d81d800054850006c149a000861045054140942801c0064100a01001001a00203100c0650ba029603059400c00c035004142643e0750740c1088901c001c0300c0002800d01e124401c1103020f5103898500100518418107001c100c42112400c51400e880540303e01c0018411010824854107508114807548031195042c200090f20a080154589000324451002005090000149402011107400b83c80c018040d1000d52a03c00d03e1400d40d0074001e900d40c0c2c960103a0702d00800128030448482000c808820050001c51504d28007007400c41c041c20540b81c0f00441c40700204080070031411001c26441c0308494103203040b001c031130a00f0300c040751184d00644040c02202c42c200d0b810341940d0f94204034100b202c2c1112200b103083e400b10700069014000c2d05890307039480080881008207a11022070003072602d030300c640d844014030040300442c0402c0c0400202e01300150201e8030242c00000e8 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 274065863 1250 274064613 274064621
    0x705090a03020402030a151203270801180506060307030819050c06040f05060c0712030f1e0c1403090d0e031009050d0f110606060a0c02060c01060303090b040b0904 72
    0x80240035400301035200d8010409a90040d82c42c01d207000d07075900220303c1c100d18105d0305001070440c0c2e184248100c552510001d11000c0200c40e0808030240d40610368a090003800740c10401001c041780203100149151081d4403403810f000c2c1060b20301340207001c002012850082990400d40b607102d0340d00c1d4284000ca43d034035194143c035031191806100040025184003401040090320461161494030042f0135507191003428240c024005000c042c1c81440071500082120366108286041c5240010304018144041070140845c8100395071117004203501c0c009020781c16040242c030005641c40f9141a0540e00c40c8505140c0f10031602c640c80c030380002812480d018031030361402c0c0c0030403001070841d500046c60340c0c407a000b03e901c0403104850720f50258404010b2180c01000e24401030340c0d6420001ca00c50302d2011314940300c1a004000c00d204500028083c04c41c82d004507010340e201034018008136120354080c9000b40c0204140c2c002540492660b846c000342038981d241c102c0c0c0989805147c3d4509008a0f4002d01000d4 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 274067113 1250 274065863 274065877
    0xb0907050a030204050a18060605030f04110d150c09050109051e03030405091005011b030206060f0111010f05010f09020403150c0302070807050c01180807030807050a120504090b03150705 82
    0x180c00f08400180790b80d800502d40b01600d12115135924081c050303603040b8101d030501c9d8884000e02200740f00300102c85907101c26080d803054014404031994481000007400100d891a0000c0c56081c06071400906610f02d544003c010800e02c0d01c84d41701060301c0e0801900e05d04003502c83c06034042e0703803182e04c001804a6480e80c0500582c0160469040681b2500041d0103c3c400b240d2241c0d009041e00d608200d190b9006e20f4240407526a00c00e410181a030b9a20001d495400c010300c400d00503e4800c4c802c2c60140d21400242d004d80794990002c10090070000940405050203104240301c800c030010001c1550104c0c1e1080b9000c0700e5125a6858088003021000800741811401120a0540c01c0c8112408035902000901d80c2620a40280c8080102d04001510b01082703458480740c0c4281c1c1d0340c0d0030702c245500012600c1c25681c00440e141d85483c400e00c2c20310314012008400a0034540c0c46034508081540040c00341040d104401010700044103548103155481c400314503024180c181c3d00b0301090740786000c0c02c000c05030 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 274068363 1250 274067113 274067117
    0x60305092a03010c1206050406060806060a110102180102011a01051e1c091e0b01090f020c03041e170606040b0414102105100203090313120b0a0b0907050a 68
    0x482060880080d0131035400e440700b000451010313840000c3e926a1885128042c0004840411620b801c0c45401806400f0040c400c82c0105400554100100d0040d12102d0030a51070030b0096640301c4098680c05004181c00d12014050360808280c00c0300300303100c07444100320844180e40c1c2908024a0103046074071300c400c101d444030303c4a00401505d144240c20500c0240204003600d80032403155140d190400c940407200c240c0c00c0c01031152000704400200b0b060003842c112202c2640104a10f0310141c20740e4001c2c414644d030303402284000500061002000e41c44103841242100b0b0b80c4e00d505650704101c0280b03a0724024036910704e400c00c0740001d96030302d4a5401701114140c0a800000e42031426048018102030554144c0716104028000b007020043c442c600050401c24141c15a0205409545827035582c412030344042c0d012900800011040c138420010355400c80a000707451202d4960390014120402c43ca03040590b02509040001654521039000b1203600e1100507025002d1603032081000c45054004640c4042 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 274069613 1250 274068363 274068433
    0x30e0a090908121e010605040e0901050603150a0b0402030907080105060d03170c04030f0b090c030c010c11040209030304060e1813020108101a030109140f0c03040c03120f02060106030509 82
    0x3420312004100303174040e220f80d441d0740c2e542e2810070010038144040100782085d1a810541041440c0d2404100102c1400d94540980000d441e140c280300c01412401e4481074019102108200c070381c030400a2540c0c2140e01d444002c00950700e900081c050f035180140d5001c1d021440d003801c0e000b07107080c120507003552160908500750704041d100c0ea194040c4c08ae058005999030703400d0405200e89040300340100700d80c404089000b00208032403040040c0a41203007080c09064910780d684001d2550300c5580448201c01030003800c0e60369582e01c0d41e20280001c0341c0c0d031851781c2c021011140428800b0b604e660103d4000d00c5c0b54000c50011607281c1e801125010b84c0100319070022150030000260405420840c42812412045040d40325810301c89030b0300c03c540c1c3c0d412003152180a80c00030302c00e002c82040060f1750021111300c48103960b83d98034140f200b440702c1c86034401007849884030809086a46d04c0802c24007182900d07801c2d034100da6a160000c4058030303c10786000e14240c0294249110013008400c24826204840e940c2034 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 274070863 1250 274069613 274069651
    0x70c0504020a0507030e0603011203051e0c0a110603150d020f0306010617090109031b1b091410030c090c0e03010606050406080a050c270409030e0a09090812 69
    0xc0507600080018004224080741c0d000c101500a1041c26a05605607655800c43d850000c025002910411002d001c0c00300010b0000c2203c44150000c003042c0c103201070881d83da180039001096440c85c4608044c0d0700046c4401c01d0201a140150469000d50003840260107a0b43c859801c02c00c60448a4130100c0c2d102c42006007504580e101840618020421a25200303041c1e04c00c001a90951000140080266403610325254000390300002c0e0a010a055108030b803012450514040c0c18803840280341c5104d58074040c0380000d01d200907401c11401140a604a12026101c9a02146915080313000003042500c2503481408141e425a001d40d0048016113410003034040344ea030209003190101d41103040050f40004041c0500368002910175004009407008104038640000c040d40ca5004a85200a07000329030120841c12102c4c40ba84c2801503070300248100148003c51501521640b030705050140105100c02000802c0e222502c04d0118580e00448180e141c0302d1146480c02c4032050042071040d0512604402d1 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 274072113 1250 274070863 274070869
    0x31c031401030b100909080301091e1505120d0e10030b0a0b03010509160f080c04090525050f0f07060624030501141003090809030f0102250c0308070c05 67
    0x240d8000c50081c52405038900f0441e800411941315600a10141070400342e89400280da44011a03044600c06040024000d103120b524a0450700300d00245405c00707041c00c1e031600c074221803490240c1c00c80d00200d40d010b07800d0140082c96034443c01c8660010000c03d4504030f0541c11401e0407070b84503d11403040d1400054080782c0740d0001d0394040c06500190709440d004001400682041106c00d0381000e401c992281403102c01c284020034084020b0303030344420003914101140044804905039405042401002e0003540380c0350b41071324114131420b0308503480d1110000c0c1203510140a501256002c120713040c0458a06040003010380541e030f11080003154440c0d03807242c00003034400d1000c0348088041a402c1e83e041c001120401e00034280ca0040e005480c0c00301171b01119510fa42c2d5500e0420004694908000c2550045030138000142e000700c1d17080710b81500828452800d141300c103500501142401982c241174403c60403c00601070b04280500401803009442d090021400386805030890622840c0403c0001e6111008 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 274073363 1250 274072113 274072151
    0xa0b092512020403060501080105060409080a0c031701092c1b0d0b070807140a1d01030f110705060a0c020a022e090e060f1c03020a0c031407060e031c03 67
    0x207171411940c40380140000c94080c0505500600b00721414440105191561601c40c071407a1400c0040c8050800300f0340402d40070306004c41d80c0c1034608000507200d40c2e5540184024006025140700d5445180003d0b51501080500c07524031703004200300505052000d03440a03d02002804034565102c00d1038050b1310006071290190368070414080c0c0d00c88506080c90480078000291402e0200a400810701098180c9544030560800b030345c403645860701d038510361200140c0003010241d001000c0c0c0d41c01c0c441280c1e9040c125000800c5064410f5048510341c0e60340038110403c5828030250030005802043c40c543c058030f020440c1032100000b440108040c0c5541110010740c0745614469100866402c81c1c007001581c000706029944190140c5050210644007400248040e101c0c4821095003440e10888405140c4200b0462807002c0d409488030701c165480e0f0420840106910440444500c68000041012445086121401040680141901c00310301c1100c82c400c00e410344565042640c0d50040c68040707404621 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 274074613 1250 274073363 274073369
    0xe0a050d030b01020601080307050d0305040201050903010c0f18050319031806030f060b0903060a020c07080712060c1d04020f0f070303090210020304060c020609030a0206030702060a0b0925120204 86
    0x207001440a8615001a051040c16071000315560030511802c80405d03004580195804c445240002e0103030b0b960710050380d030b6014500300240c1540c40c00340c80c2010180c0000303100b1851400703515030b003040d01c8218000110004082c001e00390140c11800b140b8808130000180020028403a00346120301c040c034000c402e80750150561003d00000d85990440360b21000300e1260340080d0289080d04d91800e02e056010966500016142c2200140d0008090354910f2041c405180170b4021503054400380303030703881da8004081840804140c4035585000b0f611a6520f00580d55040d00a490b401c606501d40080c00410009401c0403841c00d142220400c80340c0340c0940c00b00024240b16101b80c40014040301030303005200c4003a603500d1480d01036500170001440030070b400c5110500c4040d81110059520055400800c0c100302d41090000e41240c40070007807020350380d004103030a40305030994441000ba002a41c4100700444100b554054a1030100481000615140c495641e40182e403a09148420000d0501010201d81c0594 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 274075863 1250 274074613 274074617
    0xa0f05070509010b030705090f21060402090604020c07030605150d0b100602030903120c010b0316090f140601030b010c05250801050103120c030e0402030c03010e071e030e0a050d 78
    0x25009000740e00d088070b5040c0c007401110100030b0451518080140c554800d615803035106200713031328050405a88141d8020000021800050854008520003651314403080e98224419114000010880e080600c255200780075918002d10910b40307142c480c00001d120103000081c4245a2030003061180c2c4400610079110791040301603607060728050f900d0502554050f0070010854108200c551901c4c1d0300043d10020828065401c21350720741c01e1402c40341c010510b8240ca180c2600078120900c40301100314008100b2915000c00502142201d46000d00c11907103184424480c02c5680e80100e0803a51195021504409e07042c10101040f08903070321040e14000c00317400030f040c0e8030b04140e00c40e000c107503c0a40d55000606034040280a903506560f03d0140f0911040721520402441480407400d05204031405248400003620865603420030580e00720040c1c1c402d003d000321140c04600803435000d42c4105620403600950000d02c064650201408a0141c00e84000d040094400c0081d03800c0070810902403048000425 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 274077113 1250 274075863 274075873
    0x2071a06030a0b150103020712051c1e09050a060e100b0f03030a0521131106070f0213020403290f040b041203110703030b0a270207050a0f05 62
    0x50900404100000342800c0c02500100c00c40d0000440d21111503800110288a0003201445440120005e009000c0d000d4468640303204c04040701d43d0040b004061402a201c0c3d041c4405000d8501c420a45000f0181920351804411107800c3d038080562084862a2107502503c9143c1e105032a00b41c2030b605280d00740769964010b034001003080701c914030032a803c0d0141550b441085076680e0001036280e009090030070080c80b10001301d2940d0f40a4a40348801012b85030000c103400c03410322580c0340070402402001210820020800b080c65803905c002078540d140d500106a1412034080e0b800d200055511340d08a030001502171001000080304005c00034007110110020713840c10003010811001c800e03406400d102c640100501030002194180141a50140d0031002c074221560700204201c000740413040128940b004082450010558140c00440e804841196010001a2948041c4140b03080e0700b901181c038040d2100110000c102c40b500a4400c00e0f010718180c5454040caa140c401d10321641c4801143c85d9004 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 274078363 1250 274077113 274077143
    0xf0d0b0708150d110427050604060f0e0a1520190e01050304030f0903020a030b09010b010f0e090603030702061b071e060324080d03050c070c12080d0207 67
    0x10030302d19881040c0100e50310b001c42d07605a00c4249866a02e070344014001c80d11418510004004079560301040069a4000e00000681d402d086454030000da40c212078060400c000070000a02601440e07010100070b83c01b070298100f00d03903034082c2642c405031200c0c003503da20b0340e14414005403c49003130f070194040d11405681d035201075640c1c14140c060b03407900d0f50180044c1032407c0309241d038442c0641c0d501640c0f600f002040003100440c03d55101c00160700c0207500a000341404002c000c42c0c0115140904c0030900240726480c080801500c00d1070305039642e000003411600017100d2514001040341d0300200e026041d2844c0030403c1d0003203103107640102c000c2c2c1004020885035410001d07040100d00d00600c550014800c100c50340c48440b25072a0304d41d114080405444c1d03c3c42c9150403c900a990380c0050388040410b41e11662100041d454104c0c2d0410725022900d05000617081c03200d154110380300140c0c004041d4080e5410002c2204503401500c4069034004428001040c48072020700c018201035004100100325005 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 274079613 1250 274078363 274078381
    0x10090e070908011d0a15020903012d1406190b0c0c090702010c090e25180e0c1e04030602040609050901060c050a0602160204050a06050907021b0f0d0b0708 68
    0x418242905160440f4440446040d801060319002c2ca51b01c0f03030f04007074281d44680d01c2401a000d0a003c069045d4a40b6120740040031450b60101502a40010102d1b44210701d04044012100340c00040104400302c2c000040302480e111102c040e03041c4c45071415030b00803501c171103e4101c17540015035101d0071603000800072140762500a04080c1c1c03140c91031000380428010500020080c8409125080006600310003055000d1411440c40207210000d40c5e521200b49843c5400030714030342809080300c0b4009102c0038040b4039541910641c510440f0250000c510f13000524580035407110b5810700414a8900501000c0002201400200018041d642d184d001560503c4100182c20300e042c4c0c84001803154031002c08c2c0024001003000404650816030045c3c032548610602040551401c90096119140508100e41c40ca542d41c0400b00382d62064075810b03700e65941e00c05aa888010225a0550405080703039010286400d500d03a01341050054200f140400700c50b518031000203c240d40d0200070035914400c0003440700c = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 274080863 1250 274079613 274079621
    0x14090a030212180103020a030b030a1511040e06060a090f080a23190c0f08011a040507120e0c090a0c020c04020f0f1312030203040617070e10090e07090801 68
    0x101002c240c030b00a83c0c881c080c00780c8142000c80038145500854021540c501913441050000740140607100058042d24054281000903003408103114600b480000000342c01c0401d980c01c2c0c03820360b9804002521030000b0050103070040000e20040100141022032000d0f6a0f545510080c4044070092800080c2883c1603180d4000001030a514100b04060035901c541000500f51a104192a6006030007009414680700c3c61034107400c91000c2100f100c40000f5400d0055022840410040200640c0322490380e04100c00d0310002d551042c00107404858001c0d400305c069000c408200064001c45040c5050400850031050301225425003141c0d8556850340c0e40303501400302d8954a8004c9808501d0310551a48400c001d02502c103245190b01c2000c11808011180c002144018012000c510320300907003a031400a41c0c9601034011503002444da000364104503c0c014401c0d82c0183c03e00e8a80196084446040c011f1000010501800b00900101d001822403910b1381414080c51f10b079a03c06210320b00300a221808e44d = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 274082113 1250 274080863 274080883
    0x703080601081012060e1c020c0d02010e1005070b0a02030a0e0a05072d0308041d0115031a0d0b090c010c050c041d190606050f0f01050d14090a0302 65
    0x200404004100d62031803e00011400d4440601c0050b05520b110b0604400410f00c0d03000804461017035660801289606100c4a03080d0f0b83c0301c0e070890f8a0804400e040c8080d01121900080c0410070b2000040003501e01000d060100c9030481c03800303500b002c0380b94079460300c00b0070150380c181389199000080c0b00941205005003814500d5203c01018401040e5441780d6031032045104419900301c0c41d881c2101303000110562010faa45034102c80345041d0f13803a404c0044150b40580b00d80400140c019900c4a0034021f4071880c079040b81d809000201000c1403460081d4040d00030901c1e01c10b02120201180f007581c0c0e81c4c01da8041c04660150ba4100ba0314a803291b2450310b00041c50b5409418040c004104c880020300001d08400c0221040d02c1c0851402c88400d000c0201c840080048000c43c055a0013410061740d42c02a0380a0450040302c2c02e00200d581c1e1810f00146480500103ea04488018501c0c203aa5001e80000c18503050040b000107141042d149486001401c141c620441903001100c50109040d03041100c0e4840e = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 274083363 1250 274082113 274082117
    0x6010b09100215040b0709080a0b1f06020c040203062e020d0302270f0a09021e0702130b0a050a0603062607060f020109060204350c0603040f08040b0703080601 70
    0x34403c04030f01840c0c1c010400410007000f07201d42c1c800240002d48240e2801004014101c11218000c0c60f91401da100b070001205c41815038211012840000c214207402d9900700c40054002c3c00c0240b40d034009100c0650300c00ad04a640118000341d80a40b1010b606c880c00c3c801700803d90896011201a5800a0915803842d00e90001c15006208140c1100b24020100c08000c90302c0003030b12050a425408155002c011002c910381c048821000080c00b010980c00900180480039040014002c0c1030300d1300d200038043d90401a4108850114403166030300d2551090b58051402000100b420b592500041d0519074550013110000c1d0b142c1d5801c0054403a0807000000c1000d2100641c4600f251203032446694490b240b05180810419004585105000390b22890a868000a0540d030347e54030b5550626920090000c0c400c000844030b504c80054810000000086401d600042e1403400328040c100440c81d007001d4000d42c0c800c410420003078005015503004200500440000c1c588612035820040c05481000700303c141 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 274084613 1250 274083363 274083373
    0x30e06030c181e090a1103070903050705090103230a06020a180b0301051813060c030b1309031b1406010602060117010516030e0321090d020309090604180506010b091002 74
    0x2d8141440c0840f4144003419512440e0a60fa144007090140460454411440c540001403006032684952070400752406541159401e540d40e000740300070711070b00748000380070404100d03500ca80324200700000e950655502c2d001c41e03420282036104c170310480c0c3c0540701010100305e41c440b41c02d80c603840b1480c03424001c08105016608643c5071001069400100300f40007403011000d07000140d0420090700c10844640d4000d0800c10050b86102c40140c001c01d2a000b4451007a01c0c1c0d503070107808680c41c1e030242540d00c0c0c0c1d166560024801124146481c41201036100f110a0000e00741e0002c80d440c020484a402458182d0081000c0d51424003c200c840c0c00c100d0f505005641440308000c603001c901d244202c0c0300461840e0010300309004031071140c11406650703403040c0b2098040c46e00c114812040b0103082d009605507002d50360f840080034016682c0e40305a841164000380c5090001b81d09280c95440310b00704261820026580c04040e9440c1400c102d1300f43c00001800c1d50201c2d170300d141818560b59072200c035005030004117 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 274085863 1250 274084613 274084639
    0x2d0915012102060409020301030b01032307051009090f02030a0b030d0203120c160507030308060315151503070c0615061b170d0b10020d050313030e06030c18 69
    0xd0300d401e0700701081074444050303141c20215100c0c00221030052008400031916542c4038545101114800c0c802a125203003850416071441841205100c2d14400c010001c151030b61600091024100b03200d00c03003200b4088105000180f1369414043c040c416100396100694038600000c4010449a500f4000c50007030344440281c204075034001040b00c0c1e4001c0c1c00c03045603403603990382804007004c1d1042c5d074810040311040486203000c20000117001400d4a00c00d85444800d580d42c5000d00d641c500341042c01c20404a0030001084103100c40302801414010086c1a000d001812a07400e05d01e254019102c0c040019000107141c2d0034400b480c4901001c41101c440c000c1c003043d160150082c07030615901100c41c440300c002ca69500c1000410001080805010412151101c50040c085001001d0398281d40b80904c0031402038604407071000c600754080440c2616518115100c1d1010300c110103901490440c2888220881c2040c2641d50320b0156200301901400310342e480ba00c40c080520581040000503000703d80284000d = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 274087113 1250 274085863 274085879
    0x5010b0702241603020105101a0403030809120c061b0a20010905010e0c040501080c1f0309020312280e060f070b0c03040c170c04052d091501 62
    0x21403214285110ba00740c00d0308144000406442005040c0c41c0366004080c601e010141c040d00003d1007054010354244065541c0d091009109005010300c11100c00200700500009006142c3d65821200ca1011520403206441c2c0040081d800140e100600e41d106404001a4840f18251307140c0390804c000320340d414000d8841000d8001c40003020302c0110a807030160401c5141c4000d41c01001d038103070020000c1c0102d0102e45049a21004813890030790240341000004200351000184800001c10090070500e14500e10003da00051003034428040c003019210341200025940c01c1140c0040300d9030091409903103100c0903030088007030000d05506440d0300c0300012805101c00c2e00852400e51189043d00c81d60764a01c0f420140300c01038404c0441c01041170601405001d40403006601461159204200070305c1000d403202421800402c1d0001c3c90300035030740401942992418180c0001d5089848401c081c80c101c41b91048949184034254814501003442ca020050143e904002202d003049100c03804141650401c444 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 274088363 1250 274087113 274087129
    0x62a04050411070501061e06020a050709050c0c15160e01080c1e040e060301060503151f1203080f0a1103060402130509070c03120605090402040902060405130e0105010b0702 76
    0xc481c419503854282c00030415000d0111625140d0000081014545604440700f9401d401c4c6c407404981d280c004408624240000354900305550404001c0c02e0340e0b840c007d5403601400000700040d006a8062086921130b407c104583c4850001180002c415442d2002a200310160100310880030400722052003038060741c010307082a03008071105101d2640c8450451500c04030320b1000075060880c0d1000280000d00c218911840f43c0500d004078001e0140c3d0766104105503403048034001c800c50070840300d0b0102d15000d02000304813807141000f0711202d1207036030b4400140300d190303403285419404944803a04104041c17140010f05940f080d00058200081656006040c076940401400280210341c00119210b142040d041c00c1c0000700750042c6581d40e2440c103118000c04c10390000b40300f14042003480c072802100340348a0084400b500d00280006903580d40350703004c1002910f01e1500a07a08071201300800705081e1607480750310022955140b4049280050b40940a08444050f070005520000074082030006a5403c0e070 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 274089613 1250 274088363 274088369
    0x3011a03161202090a030b01030209070212120a060e09100e030f071b09180b0705030601080a0902040b090a0e0705060306030a0f0519060f05070f02100e01021b062a04 73
    0xc2d04040c040440180c0030000c1c0300d402c2c8004d50040140c5400800c111414401c641624801d90b01c41e0101d441e41003090ba80d88020465010140d0000c0c070010310a2280d400c07d890380003071508030100f2090750350f144000000f1029201005550000103e00c141c210003030180c00072900c081c000a51400b41a502460210b018a0138000e00110485020301205602c07400d000c000781840303100c05c104900d40310440030901100707020100d50000301080000c51980c02101030303070711408068403113001c2a5240d60084004298442d0700302c2e4401d550300c02c00c841d6071b02e50054180c4a8011b200c030000f4129400180b66103446d44540c001d0703114040070010007655407070100b070701a0081e501421480c01180240303072460601d0500c00148510111f106c0d0994280b00075600402c8080f0741c5050100b01a84034030303400b1501100c04510740c1c800359212250300048610a5803202d417060f45900001030800b151000340c10200c82918614a003280e0100e03050000060300e0048022440d1b00042c1d000140482051000d10140a144 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 274090863 1250 274089613 274089617
    0x6010c02090118060306020313050d03181103031b070602071202030d0804050a060216121106011815031b0806010e060918030c0a0c05010f05030411060702060d0203011a0316 76
    0x14252440c5030f0604c0c1c0180d00590b40c0410103649a240034007940c6003030290140c0c280c0d114896413141e40c1000717010340b01d07858250209001072000c4003015169054001110010b0f80c1d0135100801c5141d07940c2c0d40750324907849002d4149000c4c20700c01d03140c180000d2418926800010354107184809950042c0d90004281c4034402542c280481c0b02d1f940c90800c2c80c213000e24540302505080c00007540740381c5040b005603c441ca0501c1280804115a0003030001c540518034034407044195408200140b1225903403448100074281040c0011468140c4000340d1481f2804035802120034041c044044103d45100d1445400a04903d80040141e5890301c0000e43e1210006040c2c0d500424912022501086206030000004141c400031265500603a00c00c2c03655688440c041030b589134807a0350b030201c1c4541c0b0943e040303100c880541c1e0f01e0324259200c1e070b112240301d00b0420014540c415010010b60340181c9840028160308104590b0040c1c4a600d00001d1005058031283d507441340000c10020852002d45c024800c0301005400c1c = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 274092113 1250 274090863 274090889
    0x602060108161707080601060c150b0303030f04020f040c0818030a0903030e04060e040b09010b030c100e21030301030314070c0e0a1e0605012309010c0809040507030f0506010c020901 80
    0x41d050f02c0e0030b0190a0300400380034041d02c000030a403240c000442c115100c0c411003005499503540ca0240c411144460b180329030640040000c11520741c0154100d40c2c119000a00340451506a00000b80440e1030002e6020013180d403201c00c0010b0300e80d00c0700420340440751100143d46443d810450003007001c109400001c2c01d00036040c0b50090543c942d5441034025054100c410400e50400b030500c0d0220003c212445915982090f40300b5038076007000325650b001c550b805050884007400015040d01d559000c420116048881811100701d8425046141c4114203140d001650b925415428020b04032201d54224070f0940000300a80b4000418400701d40c012601c000d2a01301035038444138001c501404515010b650020760b0f848030000751400ba90f010604036102602c5568102c581d00e602c58034001190504218050004d01020415501450004142c0c074882e130585498449107000150454a0a4445900096a6880e40e6100501c280300c3c4980000c0242464500b5007001e50010b00445014045c0752820111 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 274093363 1250 274092113 274092149
    0x2150307050403051b03010e0c0604050d0812010e16210f0b0d200102010b0d02040c09031e0c120c151101091b06050f030411060d15060206010816 64
    0x100c0c60645010315030000031741d5140e0482240c43c92601c505c9003c424429480c041800415580026007410042005851542041c0c509010812010b905410980301040104502e0100401d46c0d0040307070181c091008202c000d410a6072003214a00702207400e04d01885042c0b002c400040d81000c6403542822011440802c0c2503160f200d044010b4000a02031642000b08014460b04002030f0280354125805e0549202c034040380c1d14001242070318902c055594015806200c00005814140c014024034906401c10044c0b5650369510070700751401442d03199094001c0c401c0c1c03100400065200b250001d007000d11000c40140e5594030381a02a00c1d043c89440568800f20028210341030007009042e9525104100800c418050360801c001000c94005c0d02e0042042140004500c441c042d00c207480356800030010180c00c542d41c9946080f100c0300c00342e03002984008288071414030300850f070040c0700ca207820200711140414541180a85080301c10b030416031f02c941009240c24425802200c440c0c08540c030f522074811180300 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 274094613 1250 274093363 274093367
    0x6010915030506150111030a0806150f0a050909012420070905040c0608011505031314011e0e030717040509070801080607050708030705211305100902150307 69
    0x400d640c070040181c02004104054a0401000c0c22010354080c0c03641440304480c0641c0d141c0724440c0c180180c0100e02c60b103004c00c11900303012101e1180140404032840c81d001b450002020160425a950b40000c3c000082102c15070038210141401070500512505079042038240080c0441d80c8c90306404e04000c2100c40180c5d50000d5405d801c04000e40c0c2d4001d4504003a20303004004c0c0900400c441c192086030412400040d0144200f80003812900e190a21503104100d041044815070b0001d4001020025250100808a00c0c40341035032042c03052000c000550925284007030f18804a07960211000d061500550303104500b404001c80700903030360005015103038a0041c0b800040c94012a000705401900040420a4440d00650100e051b544c0c41011201a940d941000701c070790b407081c0071005008180600c089a8210300031070281040c241d5188002c01c09000350740e02080e2800046070071101140110103018217011302488616042c840c0c43e13030f003400400c280c6c0d00404c1d400c81d100d10410b1050f50001001549080c = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 274095863 1250 274094613 274094651
    0xc04030605090a080a05090a0f05220b03031317010b010e13061806050117090a060506030102092e0e100507031101090b07140a091701021b0321010305060109 69
    0x760788091005c0e00d07800310800c01000c035004603c4890103911071000200326240e0b110b44840407601c0052001310000ca0174101c41000e1030200c101200c2d403a0700c034000301c0c01d240d4052000c0c0c903a1325002000026410302d021044140031b544c64452604507494609016a00e1742c0c0700781664a4408141e030405402000c4401040c0100700c0c0e0781c00070880c81c10324500c440406005410040c202e600c240c0c2c41d180501c50b031b401c0d04550601d0a0381c0780c00d40d65000f1105480000c0990f004198060002000103050281301000b16124414100b0f0701d542c5071712124010b03003c2d0980d11146640109084c64061000c0491202058100c0500103084080c0007010464800f0180304d0110414060080002881004490320f03044800983c25039644000c00c10700c00041122491a0040c0c659180705aa540d4401c0c0e4035041003140100300184000c2080d5408008051000030a59081905400050003d56442d0078214581500c070341503210860307a2030034803001003000c12000548241500c40003c0005600d8144180030f605c01 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 274097113 1250 274095863 274095883
    0x3070506030a02070b07050f16110913030f020c010210020d060b160c1409070f09080708060a0e030406081b09120d080601050306030a032006160306050105030c0403060509 75
    0x2000c000030410080c0007080c0c01500c62540b064201c009941c50344001640e07540a00e01480100f50410310004001c80000e200301e28885020f20310011400c1081030101d601041c045034003296030720b00e1380486003c0603808901c0480405551015001120f01c201c0001c0d101c3c28a80310b241091500414071480e11104d40d80b2140040c1610324070745a83d272782900141445d420031181e00f039a000008000000d6455440103000341482c1004089003140d81e074603813003070b03c2d0194030410003000c0201810000c40c511104000100c0a801c440d4000c0c022880c040c003010080c0c0b4405001e030841d45e00180010000185c01c1020240c002b21130550081d24030722036a45038110f0707006440f0721070703841203424208560440d400b199403000000c0aa40c0c20003142d0302d140c01900c02c3d00c0141d0300709030554000c410202c04248240c0094603901c031075480d80303141d0600b0b0f441840d00c1c1c118284c0702c50b141c00d9107407221103107031a405101e544001c240038203045041d0300e041c0c19403e07410b004912000e80316903101e1000400c210b000b8007840e564 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 274098363 1250 274097113 274097119
    0x101703161208010e040f0f0f1407030501110408030f0c0c04020f040303030506041a0f0414090f061308030601080405031201060509040f0510061b0b1509070e03060114030705 76
    0x1038101103007000085914681220008142d103800041804c00000d803882d4400c1e0f401c08443c54101001d551441c0c0724048840c8203031840d0040e2040c072000160030b14040030801e600f41c1d00821880b810360400c5802c40308440081040004104020040c0c41c10120030b9803a110f901844e25510303000340c8000c16003030014042e00198020701c000380c3c50f140003540c0d2024009503806558108550741d190300501040761896010380d82c075050345880224040c500f480006400c8480075002180001c0c0800c40f4042c06a8280e4560041e6003211007000b442a40402109500801790032005101c01569118801c01380300140c411030400c40e0510019040c4402001220100c1c41201c070601c0c00f0b583d45400040071600006400e900c03840c1840c8581d07988903424081e450240022064000301c091900740c0070344001404410710382e40c2003900804900440c5422007010701c520140070100c4624030540040240303506005080e00f007480024940308101d51800101d0701c0c10b41d54610b030000c00342d900700c50000303240641591211741c0c = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 274099613 1250 274098363 274098397
    0xc070e16030b01090e0f0703060801051b0a050906070c0302090f10210b04051b010234050901060503250e010806040f020c030702100e10080a09060204060c0309080105101703 76
    0x460340000d8000d0b0340b00d81c1f082d42d01000340980303d4075950700b031b114296102c000704a000d50140403a6800c520040407a801ca03801c1862800400340301044840e002520262601d1000074800c0040d4103250074070b0703640108039620f00c03005482c02c0c003403e000d900c100e40203003600d03c00c08410340548402080c03024000183c1000440406280c20700c0c0c115660501c81500025000c0541e181480950000403818100c0854421101c510380c01d001c12050681140f03040002868400c850000702a141c0f80307213460182211f940d41540d04e00d44807080c54943c031303840900d1100310000c4c084c024400a600451130b164050007442d041e03415448007800940680715079594a800c85100148511a00000200a203c5148251944222405400d8058071f40306c1101802a4005501100e8103500750b100c0c00d111a40089010800038010b500d503140e0308226005500030170b0102c0e4200064034107054010170074000501d00c0034020b003c40e00c1c018000c1001c1ea4068400c1204841e0030140d1141402002e00c1030310090000300c09414 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 274100719 1106 274099613 274099621
    0x131d031603050903010912050c0c0607170a1404080703170c191407030b060906030f1009151a190e0c090f0a0b0c070e16030b01090e 58
    0x42c0c0c99507070303800e600e00000c2e0f491f85285246800c581c0c2c1c0750f80300c00c0001d5070310f0b01c0c0c070241c0181c0720f10070b240500c9054002a8a440c21803104180d0565140d11690302081c01c0d80c0780c140300040038030024000b10b000300f40824002888421603020340444c0c040d24680c05c2c281d14080c4160030f421003451b081120403e0306820b4071002e207103241e442003003c0340c2d070000b01d47c10b81c45c2044c0c51030300210b4070700705408140051481c00d0142c094001100302d01804cad070005500807240d0703074114105144000039182c20028081c003512140764001540c1d1b2800500c4211a03c24071490704800b042c0c403051041c08003003034a00254403484100405e45600342c038142c802d6112012241610780015400c1a446091840c10001395290000407500410750b180c002a119202401d629041031420b03003180c9000c0030404200800002d5514061002190078100000d4215840780100c4031403140750482c5120751181c2040c0 = true := by decide +kernel

theorem cover : BRFrame.Cov 273920863 274100719 := by
  have h0 := BRFrame.cov_init 273920863
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273920863 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273920863 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273920863 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273920863 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273920863 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273920863 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273920863 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273920863 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273920863 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273920863 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273920863 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273920863 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273920863 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273920863 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273920863 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273920863 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273920863 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273920863 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273920863 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273920863 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273920863 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273920863 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273920863 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273920863 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273920863 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273920863 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273920863 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273920863 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273920863 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273920863 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273920863 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273920863 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273920863 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273920863 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273920863 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273920863 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273920863 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273920863 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273920863 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273920863 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273920863 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273920863 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273920863 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273920863 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273920863 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273920863 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273920863 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273920863 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273920863 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273920863 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273920863 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273920863 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273920863 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273920863 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273920863 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273920863 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273920863 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273920863 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273920863 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273920863 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273920863 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273920863 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273920863 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273920863 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273920863 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273920863 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273920863 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273920863 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273920863 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273920863 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273920863 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273920863 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273920863 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273920863 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273920863 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273920863 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273920863 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273920863 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273920863 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273920863 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273920863 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273920863 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273920863 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273920863 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273920863 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273920863 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273920863 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273920863 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273920863 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273920863 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273920863 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273920863 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273920863 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273920863 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273920863 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273920863 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273920863 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273920863 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273920863 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273920863 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273920863 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273920863 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273920863 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273920863 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273920863 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273920863 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273920863 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273920863 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273920863 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273920863 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273920863 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273920863 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273920863 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273920863 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273920863 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273920863 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273920863 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273920863 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273920863 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273920863 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273920863 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273920863 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273920863 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273920863 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273920863 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273920863 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273920863 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273920863 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273920863 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273920863 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273920863 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273920863 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273920863 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273920863 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273920863 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273920863 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273920863 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273920863 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273920863 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273920863 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273920863 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273920863 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273920863 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273920863 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 273920863 ≤ n) (h2 : n < 274100719) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
