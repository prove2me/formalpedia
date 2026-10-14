-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3609
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:09:59.207249+00:00
-- url     : https://prove2.me/submissions/639b9df1-9801-4aff-b8d4-3afc58372ee9

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 648920863 ≤ n < 649100719 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 648922113 1250 648920863 648920879
    0x1621090e040b011e0e0f0916031106030a0b0a12111503061005090d030c1112060a0f0f0608060601030c050418020d1103090f060105100f030c030f11120c03010803030c070c 75
    0x614050042c001c100c00c02c40c40d043d0341f614180404650341e1450012005420404903035601d28801042c40704a8015030341c0c4e02c0d100d6000c4001c2500c24805c0d41c1000b409030000620809020300141c0c200c0c0114210580c220380c0a040084d0760481c2541c0c01840e0700203201140a0b8101040c0c40d994941341424090316080d0400000356291600060403000229200000410888410004a02c06a007524101c03050003010b441540c4a640060212043d80d58500c0b0501c2840781581000c161640440300801c222500c40301c0c19a00d809044034500e02003401d017000720000c24441e400b15421079151106444c4542c0490903143c1c0070f540700a0030703440742d04c1d122380816000c00b5980004602490300400104100e2114024260030070005a0155118101a41e04080f4045d004001c070480340a15150000c0c00c1c07104100d00380c004140c100c1c4609042407900100050485140c4000c081d85405114a41c000350f03101c0c811064140b01c240a0090290401d00201d1103010303008019000c1644201c80d600c51885c1ca4110f0307 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 648923363 1250 648922113 648922139
    0x1e030424021f06030507080102030702030304030c1b092301050a060309080706180b0901090f12050c070b03061c0203030a030518011104030209061e061621090e040b011e 74
    0x20b92040c60342c1c03a0800c20802030100010801021841c00a42c05c8d8500701d0000b07522400000c1001c2d0034403070112000010094201514107090480003103042d03006403581c0115004004141c0fa1100f401c14900942c0400320803640341e14100c50000381205180d50800c1800ca010700040d900c201c0d00c21340140801400605540a56520110341405c035200c14011820a00c850001c00f405100c1503074504008038001c07410b15082c8108443e000038941d0201c0b003110004550500c120241408a40900300b40802c4041040d40214040c150490703074030881102c0a4aa0949100c2c0408000c1d40b541c81088103000039030007500031a44c4070414108016901c403c00f00c00e02d0135229120000050120005024411441c5c07402c840e680111084c3d44209080030400009035502d1615901e040c800c1c2004503084000841030182c40d86142d503c125100c0c0c0040c10381d414030801c0100300c070358100410184003000c6880c4606015207840340c0d400c1151343c40c2603441c2030305100200c00090b540031004400440007107805040c0b003035 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 648924613 1250 648923363 648923413
    0x3150909120e09040b010902130314010e01051803030a0c050421020319020f13020f0703111005040336080d080105120d111c021e03042402 61
    0x2100300606088400c000340b9203100b00203014441c03541003041c0408600464030b05419500d10000041c0d50b54400305502c0869090795000070031380710030000c00e03403001c0c2c4064226505201c0e142d0024070564442c000000400c0d240b20a100300b06074014000115003d48a0700640c0c00000070382440351510791541903100341d10343e072140380140340c2034500c1d082000c504007042900c103c0144644180000282d560000e0180950006103900c600000c2c1c0d0201d40c0805168100ca0302c110000c0f040350b80d281014a005000c800703200212100d03501400c0543c8142d00344d01c1c004c20307100d6541565170a044aa1324826000d00500038580740101d548030544270804100d44880c0840603120490040054a0380d0380c4000382068030580015003d8403c0e0180700000500008403e4080c0d400c600b000720b20303104582c500e41d02c1c184804615840000f8880700c04a40140c01080ea41020b00c505e00c803429895840d200d519030740b4405c5201c3c0340c010705003030101c0c1c4100c1405100480745030501da206032074981640103030804550b40c0c20781c = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 648925863 1250 648924613 648924623
    0x30406020601150807050412110901260604082508030103060f0e07060509130e1902150a020a1203020c060c09010e190326040e0a0e0f0a020103150909 66
    0x1840201218101c3d091640c0b03a5103460780c10740c07034260001026030040d441400d0100880520000800803881c2d10ba110342034000c1d01d410030960b035811840c0d1100a242c0040800f21101c90714000c648c1002141c0d030b0384102e0b00300b031180e4503140c2d403542112400c0a40300b03110031050302c1c244d006c000044c0c00c0c24002d50003140203840c00324840100181e501d0840300306030711713200065204181c02c1103080d40160507142c6280c822210444507102c64410000605048401d000c00c0340158658aa1410702285617950070b5030003503c840e071520690107892a014407613410b9039400342e0301281511000070041c14841240240310302e405070425000d580715a25241082e45e00407030445005c2040c04065070311842c03520440700110f900c206161489071084010f40d03002e000c00f40440480d034910300d10744402240c1c06030001164141c41b81eaa41e41e1381580c0b14400d1420b4400c0f2040b42d007412110306a0507800103040154490b80e80c0a0600040356600541c02020301ca601403801680302200080c078802107100356450310707011b0 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 648927113 1250 648925863 648925873
    0x304030207050f100903060e01020c0a080307030c080103050601120822140102011a060c1203010b0a2309040f1d07050306090601060507030c0203030f07060e0616020c060310030503040602 82
    0x82c0810211061140b400707030080c41106101101181d00641c2c1c1411a0740041000884003450200113004e84500b0200c403070700e4440c0002080401082e070000b98412003066804000790200c0d0041203c501800388009400c643c00240103103c240c1c0425601382c103c1c2d108100b1140740c1480001501d1600b0340c400f19542c0c0c5400792070001c1141e070300c0680510200d500240b0080182103c000040346015145004181c0102c40105029125442c200842c0d2018018605a10344035a0744416010f0300798410049000001c0c1c1000082c0408419048041885c01075200c003c3d00b4090000d060100030300081d001e4203509030322521728100d5844058641070340b850100c00544002030514003454980100076081200b154131110040100360752200c02d986c0308507454a40241e141c045c03800000e1450085094030141610001381400070410b10343d100c0941c3c00d031003405491403940c2d2410000c04052240fa10036026070010090a000d6280c030130700031503111804042c08000700d9200e84a0510351742054212002580c04 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 648928363 1250 648927113 648927119
    0x307120e09090303100b0a050703030b150c1606020318040218060c03040515090108070c0f2111010e0309011808010f090201080906010b0702100318030216050a36020304030207 77
    0x400d174020086e25064031064504040d61400034a288030300103021782056610410100150f4075001440003d0f0345584a60f5200d0310080c428580310741c03030b0781d83e05095020071010004103140003006a07500d6022050800800358001d40501000e90300c1460744140c40040244604044d0b5640c4020340801c40c5140019504c403400c002c103004403a403c000344030803200707014801004940ea20103240e585c440d8a074980301d50403690031718000d508052044c1c4000c1c2400c442c00100c1e2030100c4090450241d400b0580d490108044000c60300354202d50780c040f680d41007904100008801c2c0c0d4064210203100c12442c42c840d141299450380058211030602080440a5455034544d03419580d00c030050f9030b04200c0400140400b945040e0343e50700907104d4400000e0140c0c030150922000d8601951180c6816261040c0103800161a03140003501d601d9000c6000c10595001c0c803000c24581072080075030080c2c0e0060490a030302c852108840d0006911001c02c444100c292641104041c2000c41c000765002c0c0d0f2003a0001d00080341 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 648929613 1250 648928363 648928381
    0x80904152309040b040303180503040303021606030c02060f061302030c03060a0b120103110406081f110a210b03030a0801050a060507020d0219050a0b070b0a0209030307120e09090303 80
    0xa1025400b4440c84821060201007a00815640e4010358107040024400d5182c1c224800fa401007100090400d020110b400024140c000c00d0324108403a101010105458441e90281c085030b0302d1f44602c1006074080c0c0d0008048440c9107240c150040c03001040d84149031098851501a0307401140c01240301da8002c400d012040c00c0190109000d0001c0f50215824161304404144014030148005003803210a201d070341c0c0c4070b41c0b9985d12110150840b101170741c120381d4802498101c194a045880b4400c00d1915004600300100903043e00c883c0402075480031406214507041e001d09480c1c2c621604001c0380e17200410155651f040008101004980e210403101d9890401048081a2264003200512608000000040e6551544200c0c0700303504036280041154500c4840e444200321f038110f550007000b443c0c0d0200d0000422009041c440d407140d503200190b0350b640d040c0d2a003a07009017059550503a00604c8174500103800303441000c84218261070000c07032402081001030240101070750060019003000090040310b071 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 648930863 1250 648929613 648929669
    0x2107030c150e0310020d14070302120907050f0d05070803040f0303030e0d0e120a020a06050702190806070c051513050c0a0b040b0d0609020c1c17010308090415 70
    0x100641020003841c1034201c0800d8552040c050304440b0313103138001591011035800382d00c4040382141c481d02d40c884610f45000050002d500c00ca10303051071411080e00194100d000000c00906490001d00140d6115101c8801e100401040b0300c803ca038140516540854040c1081003e000204108592418058910300300501129200341c0d91943d140c000c0040c03031000c02d4001e01c0d4040311600c2550000741c8181c1030941641070002d0319000a50040e40358100064440c2d1000140165500071600b10441420f100190ba0070812076100c0c48000f5009800040c566501644a20304000d000c0c20540d100e142d0500c040060028040301c0a01400d1440c1541c40d080c44410045610316440c1540c00c2800d135400c141d100c44c080d008900c183c4083d0513000640070811001031b0000340c000e00104800795141d502e0b00c0c4525464007040d9000004150032003003800640c92040075000c2018400601d8500141d00750f0b111901c0980c40342e00802c0d000b6440c0c08034500d05030741c66040c807002021103907241d04e02d60b40c07107403c21a180 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 648932113 1250 648930863 648930899
    0x50a0b0106030c050901050f09090f1f12020f06040e0f0103150b150a091a0d1b1b0c030f03080f06031b1e1306060921022107030c 57
    0x1850308110041d4a03821400f00c407170441c02420456290565010603100910032008110f03007060407a011301a010040c3e007500d82c042e50000d000307400c440480885140000440340701e4008141c99420b149805420001441d10603000b020302901d16058480d0750111074158240c0e00c1100710044c20004100348074115080603442180500144604150040001c0c640340008464210f80880081c881c0d110341e004044042c01404034500340d003010040002480718940124040100351800c1c02c200d82800b2110b0508080215545c0d15024040898040c0e8000c2d445010350044521005100c00480416040300120b80f14030b210703980d0b0500c1454014424032031080080c1c07842e0301940c0315000c64915a91222650101a40c1c10350302c07408400194500c00e811341c5004051141c002d080141702d2100c030640c40e0420000d9030042d480c0c0c1e142441c1c0e503800342c40c02403213929410010b07401e90b01418030040c94200c80240c0700070094044000c20074004014a420002c0541c000c4640300ca00c100100400341c3c11212103550 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 648933363 1250 648932113 648932117
    0x305030301140324150325090f02070503160501090f0b07030c0809120315120f0f0a021c02010c02040c0c020a0812030115020f01020f040302040b04050103080a140d09050a0b0106 78
    0x60074500000e07411580000e043c0c0d0fa440d01090300c017a040303510704011380f5440103204448504c044400380050081c0707004034028078a4030750078442d2444213500d0768000c5035412a44600213514000324001d0390100409102070032103042d52238900c13000100e07413001144404203006203180003160038140405130032500180000420f0000100800c140c403a00443c0d48030b0003034681004660b59a82e05041505540322404000c3d50005080540103c5000c3c000340304440310760140211030b6110304524845960700c00c0180025803040340c4400c50b220f5410b4498840008030310606041141003000d500140c160361007a00950f000443c07d41c820000c0d4500503140d08020003440c1c0240800d148228507030542031205008050b080c003080c684c201503480c420010700c0c0300152000002c64841860580c0c40c07105901c40d10041c1c1c491070401005010602d0301d8468681220f0340122140d280006420781910203562604441001e04003c6c012481500070307a000c0c91520f244140054540c402d10340c640007140e42010303041981 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 648934613 1250 648933363 648933403
    0x220501110c0a0501030b0109080f03030123090c0a2303090c090c0909102c0f090a0201080903070c09060302040516170c09100801060206240f060403050303011403 71
    0x41036807202d103032840560318280b0340032440c210030b0f8005aa410526502c150031511402c000d410000c98040003560580e01480308030060300e0003c0c44c4600d00d024645441c0c80d8441000000300307050540c8180140810121030170140d00c14250801c2e04910000c425414021080001040100384003003841101030031201200c42080505000b9044060340c010169202d0241c2d0700040030a291502c000398200003000e100c0c036280e054407070314002d144484100884d140020b032000e402044c0c00c80013141105109061420051105c2e503903a030011101050040c00c004041e020810510001c20804000030014144418000c1040c1e4038600c1484121035004200b045560f1b4444011228241d1116207103030440c4130910b0390020ba844800051145102d4500b405610100790b5252241154001030001e0485040d602528144e6a68129400621051151711a14200392401481c1940381401e15180d05000142485091984966a50b86540d00a800410403804107600c9004145410400b0307940404811000078 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 648935863 1250 648934613 648934633
    0x1b010c030e06040204020f040807080c0a050111100903030f0f1d1f0b01050f120906060609101101090512130b040b120a110a0c030801090e0d080c22050111 68
    0x260b269580600020b20854000407102a0f038029a0240e0b4040e0034920b01b42c84120f80e80e5040e540e40c4140c03035564540100355140d030020f0198040d401c010401e43c65103015114100200c09000c0042c814024102c040c036556000c1e14001156500c503130b809116140000092001c0808070180760007100c50f4200b03c01d64000c0703010040954424007000b1480401c0032001c82e84144080041e1703440e00030710003401c000c5080824910141404400c280e40680041c00c19101c0644400b1309001c0a44901c0e0001500102c840c0d824420f03080c419580308080c90b000b10000180c81c901d5594041c03c2803418160320020704d4001c108041014625183c1c8802800c5100000d80307002e1428014101c98060f400b100c05901300e2580000e00303881d201d50000781010070815000e980e43e45c00000c002d01175260020b425000204080004950710200d8440c1c5164250041c009000603050800c08a40e43d11006294507032050003840070170705034151540941c0c0380f110601c111035a054140302c00141019424180380010b42c1c010b840d51 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 648937113 1250 648935863 648935891
    0x20c1e0a0b01440d0503010513140c090415030501020c0d0806010e0d0206120a02040807060203121f09050406020d2306041a0307030503090f0d050d050a090306021b010c03 75
    0x42030a40f0600e05008108090383c0640b01402e14800c403a1600d680a03420b1010780c4642e2100c029410b80f28211009100100d40104540c203c4400c0e000c540600c00c0b014010803000071081d8040d01a4640089c40811030f10f01d80106207a10181c81d6004894580d000310300c49840500500c24200c903d149031414424514100700020000703000c000740c81d030141890304110300c15926071030100c407448602c20050660508011200000940c070500c80e02c1c9950040d103c000c9846440030080701c0780a01d0000741d04005803601765000310705441803800c51001c01c1c041d103070008500d00d1b5070280307a10580c003d88005885042600481040d86c0e8141c4c80502912072001180010170151102130b50028010f8a00144445c404822035800741c1c400b0740065410b100b184800810004000000d14040c0029030b00141c01c1034581e403d0064600c0f1400d40105190405c2000c03448083c03003400549092170f0036241c4554061f40d01d8541ea800c03a4000302c0d01c0d251300720345142003411800b0240141c1400701e400e0714003040404990380d00 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 648938363 1250 648937113 648937169
    0x1805070c030c0f11060304030c0c050109061e020c1512060109080d08150402042706050a030605060102160905040b07020d020709051807151701120303020c1e0a0b01 72
    0x1000c00d5036507400d01c1c3c01d03c4441359084490010107098156203050a05000d001c91080c1101100c00e0714042c40003090319440394400004444043d100e400e0031808902114910510f608191000c40c450450b4600103a0354240042c40903100c012041c5555845240c002c60111800034042418070074a08010030001400051031f00e14040c0629083c4059200d86408800c0300b06c03c264440e0b480742c00440c1c0803600002441c403950003000030300550980200010844010385020340f2615510014400d0204085440b58201c2c1780c4c00b00052040e00c0003600003c440c02900d001b1504085021651001040200b020900700e03540c000d000c0d4001070a207201000c40c000d40d942140e0162031010307a00d84020541c3c42014007d25810361807010195581e45440e45840e800001409410340c0010310481d1a0544506582c00d403941a20b000501c091b0114503940c500b9006035001000121081c031455410404c0e02d00c44e2007805004c6d40c4400003070120400181000b001209044c0c10124103a0f401b4a0151141892284 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 648939613 1250 648938363 648938387
    0x103060b04140a020714060117011a01050f0d1404060203012606010611030408030a111c080601030504080d1a2701060c170a05042d030b090f071805070c03 68
    0xd070240c1c2da40003071b241003c50b90200c1740c888059482440000300e44190341c01c1ca80414901c81e4030003000700c0085507100700b01d21100c01c203005002c0380e003c2080305100035a25004040030b86003200042541d800c0380c82e20401903101140c065450903404801484170f00c281485048100c0c001500d120041141040c0c02c0d61500b2061185d007007032007615000074206a0041c0169001032442d0801d8a03104c5070b101401900406128100b041d040c000c00c00d0812081d0b0000410340480c4039181d941c0c40c0195039200042d8000e0801400a03a44003106110222581c0150700640e501540c10340c060004020300c00e410700482810005810083e40c0703040380f000c4591880300d521241100c45a04d040c00001e0018204140403105506600d180c0080010300039203002c1d000700040c000c64110805c041981800b4250003e04a002c03a0002c1e540b6101070071080020076030780520543c1020361716064600c88880c00807001d151070515807040800300514000f0304075501d40c0d481081e6204e00719040440c40581d0035640208800740d801 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 648940863 1250 648939613 648939631
    0x30105060f04021c0e0c01030608030a0906051606020d06030b01050a05030a0605042316050402071104200a08220209070516020a0602030d0c020c0310091a0408030103060b0414 77
    0x462942000040b13425030940400e220a41040840f03010185135403100b50b03034080f940c0800d04001002401da4000030490301c20b6002503507052840b07403c00d1743c100d034a40c2c813813001c05142451700c1c0401400318003d0310080101209481c0001215850f40c540f0310120b40381640100d11520784080100007a0710080b902102c1941c2c049400030b0f00303565034a00031490031840c0da8180c0c3c896400c0c2c0f06481069000040d0100c2202e05400f902d42004d0f0b5a1040006921480750001c0c81041840414090307810107400c95651a00b031581101070a0382e20101c0b64071580c0001e60300e41c000844032410300460608a100c03084118003c2e054080003102c0903004a0264a0083c101000700400010f03510f0781c0480b21025083e0490b802042c200c14107a50340310003941c81c1c0110582d5480503141c503901c000140e0002030381c1ca12101c000b034040c040f41e280f20101d0000400181100380c6800081c00c2501c01000f03100d551ba03e10451141c4082e03616541107050190031640703000c09681c0980d1902002c904407080e1005030b1584103000b0 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 648942113 1250 648940863 648940867
    0x30b0a1211060f1b0f0105250e1f030e0d170709050a060302030703141015050d11130902030601090b03180a050c100c1101200a120806030105060f0402 66
    0x7060200d40544a43d48503000003800c0443d03010120500c4811069011940c1d0b0b0481e108002517100c124200d600540c0c400c041401c40c010180e10b02084041d012990710a42c0c180b802e0805140c81c00704080d540b070902111038440202d01d00d60301194151040303484c01c6112500510310801001c2003d01481040e5034a10002115500020004c0c0d1062072180b01900c009040325450582e2880c01401035041034890354040b074100b001108000042420261042ca40c203035001c8000391402003212191200748200b0010041c042002001512a0340100b2042094142c1701c1d0390340e80180c4101100c4000e590b0803220310540100140211607901078220300584400c81d140c15520f880301104c0b40204006030f0309500c0f090140c0d59215003400008101d01030003034015903001007150141002107034503500c5118010025480b0140c4190654496881c01801001f800c80014129540c1c58000e807410342e608408641d01039a4034031404001d9400311526400140c2540248190309110300000c1400003031030000d0340a030741c3c0 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 648943363 1250 648942113 648942143
    0x30f0706110706090503071a041a0a090804120c1a0a08130203101509020708040902180a08060702010c030203060d0609021f05040302040b0916050703030914030a030b0a12 75
    0x70060440780c0782640708000f00b2907410207282c0f158503600040015940312000c100c1114180c1c1501d885180300300d50000740551405c040c0342d01410400360141040710803541c1c960b40000004c07a5080104043d0003841c9001c034151074546442c14074041c0a8100c08450071803040701004040311482601d82c2c0000a041414039541c54020728410725001e45001380d4144225259207880c00044c0e03200507071501000c1c0d20301412540b00d00380d80040e0b100320f800090950904001c00c00c0100c0490340030344800181001c2c20001c440f640c1d00040c01c01e10036a00070402681000d01071200ca583c0920601a40071b1460030701f9030a518002000820700c0c181404060000c03030b100c070034484c115590740d40c10054044030051900351030300880e0170043c1a038006000403402940b50078103000440c03a0200707070980311b04100c4401c07001c045044a0b04851b07039000004118289619030111100241d000102014842c10300c000454540c1c2c80380c6001030986000741c0300c0b1070091165083c240305130b101e04582c925280d03421203213040d91804 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 648944613 1250 648943363 648943391
    0x1303020a0b07120b0102030f121e09060702010b0315011413020d0606090e0405070605180301060605030603010c0c020a090c0912060b0a080d1718012c030f0706 70
    0x140500c402000c0c1984003080144103600301c080701d0700c0103101d40c8080103000102070044e41d0321312030819214040402440110000c40c1c11064490b80948002c04109621900303880307100c6290416680c2240b0354008108009011b81d09106540c0409400c0300200403816501c1900c8a40901c18051031048441c22498118180c461302404412403c1001086558003801000b48006240c0d5010b00c0d8009141441c000138000150824140260f400c00044e04a4074940481a10380d0381c003d294848805100c0500c1d0040ca40e4203204a00043c0b11546a042d503a00c0d042040608403403c100c020010f0040c2c044000700581c5440c00c502c41514084200001e0452000c1c0d000c0d16a10250752001c00100865022103040142680044448a0b001d840d034a80c00340e1161802910740140d00392480000302c400c01d2400e2501c900501c11074003c6e11007440366580c580b00050a41c2036504440340c2050700400d024190180844d4551a8810b14144201075800e200e000c4401c41010320800401411207502e40001c084900f0b = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 648945863 1250 648944613 648944623
    0x18030f0a270f06030506030a20030c060c06130f050a0b100509040c090209040905120c07170d03021c1d07050105043f050d0318111201060504110d0b0402070b130302 72
    0x1603004407202c01c090004421003041c1c0715032701e51524001c0c01040703110900c2c2e06000041c0c61080a846014101e030307558004a19618142124040d641052010503907000b01e60140110411070b801103a601e100c52415000c1ca80c80481ca40d408580100d40c040104804070360b00070350040503a03012000c050b944200c24400500a4451088054107078003a10140352405a0000004c0111000b00801d1390750803562280c5c1c4002400e410400741025810026640c04414444e600400740c0c54061504186400140c1c40b0b0307002100c0c020030f01c500300b013000c049140c0d10380a0200b01c440700505c001d10701140f0309418040510419003544112940148400f0000199440b0303048003406104103000340000002410b0821350f0369881d0300402c0801081c94024800090b040c00c030071000c68207400c1440301101724078440030300c03040b241322071403210065680b60781c00b01e501e0361140aa280700e003207004510340c0c40b00f007148090707400c5603000903009e0f1069104200b00800643e10281941d80b2030460180100e50400c2824103038100 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 648947113 1250 648945863 648945883
    0xc0b040b040c210501050703050106020601030b06150c061f050a0909170a0c030921080a03061e14180c070602070b10080606010207030b18030f0a270f0603050603 71
    0x5512800c0e8600f005854a20010302c00a00840081c40540c84005013a0200c030300030b001d0007005800c00f4005001041d010f0503039a800c03a01c0500703c0c00c9804d06000c2c50078000d4200c41251405600400c090200c48249825004805601801f0b901032a920b813400180344218a4451680c4064035520a00140b04002503215030981c0c0c030304200c40e03583d502410f00410180d030000c0203c0200b100b6074408110b804070309501112103203500c041105ca1600549410743d00fa00018000c104040c1ca4200101f00e14482c800180784504a0040d00003045040c990150740300c20714030002d6402118074024480582d03c4213140540c00039140710a61f540c0b01604e041140203481009806071280c00403000b0301c0900e502d43d1070b048003110050000e4a1791521408012a1221540d200c0a402000340c4000f241440213140c80c0c1c0064036040004407441c0840907408210b0580205200034003040191088066841e0340c880c007420b06000805d010318100303040c070a1746410072509020b45410195036000088264a08110040c01 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 648948363 1250 648947113 648947129
    0xa05010606020a0b0c040308030402013e1e030f090604030f08030109061502100c2a0308071812020f0409210e01090515041a03010e01060c0b040b040c 66
    0xe029100e000207941c80c0321429084410a4595000902c50320707045040d00c094a510482c0c1c02d2441e15160011901c8900481c11541c03640c91002101401d1003440701241c101c00c41440100c010b1010340201c4c0c5051881c4121007500017103458100c1c10084034040120b030141940d003840075440d07540142c0801c50074012900000c1a011038030089105020203980514121461614113005891b11000c243c49440b50b00744455015901401249071900d80c0368001005689940c600441d05444102090340d2255881c0010035803140503a03054800d240c7c6c0302404560000c000c1c105050401041656a03290100a100c0e505034011308611400840d0f40b00c0c0c9400c41640e1008005000c499100d09041c0341d0000c12014070488148264610a00140a10303c240b0b00c00805840c0d4000700d901c1c00003404903079a20b1000213901c1c01001c02c00840c000c1c00300003070603045400d075004c9241c8075810003000308140c1038181c01003018080d05101d0100083c00751010b070f5900507880101c3c8081501c1c1c03072424114481a176040094 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 648949613 1250 648948363 648948371
    0x9031709030705131d101d0a02040b03010e030a0302090f030d0903031d060d0c030f15090203040c1203120507090f142e030b09060a051005070807030305061f1e020a0501 74
    0x709071748001240815602c1e0103108100022552100007140001040d2002c1aa001001981c01502e041c2c4d003e6884445d0140010aa849403e000035080d0390051740e6200120303a01088006190401d441415554071040c2d0040401d01c02d03501c800745c6a800d951100a00f00807002140c0700c905021004840000030004d4a0280c4503240c03175880300c02802c5403298240000c1d281c00215554070308203000350704c003ca1b0690442070107241803d100748040c2d80300500940300d09860031030001d0521000308414200d00d004e5510136a2081c21800c810041c1c1d20080c01c01810030a000c9010f01540d103000c1c0c0104100d4580c1210896012138100100d0600f41b00580c10004d500c070a085800c1019490200c0521002d1071568100101d102030401c10444803800c3d03580e19005900c008042c4070f030742030802c1a260b039603805090079400c0c83c88a0340d801c1c0a55002c00300c102d000a440b50103005007410402c05c0400d49240644004610315054070000b801c920200410745140403408002c50340190080c410714403c2500500240 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 648950863 1250 648949613 648949661
    0x6281b0305030a0510140d0f0c0603020903070602031e031305070603050a0e07180903050d0e0d030c05180f011704060222180f110a0903170903070513 66
    0xd0007075001115280c03d05410000000c941d03043c9848070700103070b40c66109101c242111030014042c6100002c0e004460342400320000a0100d41580003880080031241e6001d40d0311100e030010700d0300700041984003106552052019103004080540e00c1280b9440e11251305032a9618014018111281c6c03081c05411402610b4020803055410307041140306108074001032200c064001151540c461543c0306c0e141118611b40c0020704102d400d504041c90260080c0341050130300c9114400d00040760303005c070740b002c4142d0303c820084c6d03442c40e405018404040a150611a062000804006034080c2d50f0b450202c0c0b00e41c00c3d8a900407403da0154a12080c20910171030031000d545402c0c68581c2c0254010038403291a524014101410851044602c80540d445029008001054006520081d0100035550102983c41c0c40310010141840806840000c0080c0d868440003851801c041c2e400c2c5468045c0403d80480800089050b6180003038410100d9070b00b0303543d4255105400a01030300800c0d00c3e83c0381c4035190315446514 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 648952113 1250 648950863 648950867
    0x715020f281b030c080d1e140c0307231e040e10060f030b0f131a0f0d290906010611010c12050a1d150606281b03 50
    0x4001044140d48441890500c0001c0076586070040d440000d00254401c86050300040214015065520301c6c0040401d02c01c1000c10204951084540026182d036900d43c511021000300d8010207820014284040c1e01c0d6003403019008110401c400504031012101815008001901408072948603d407001e03414085481c880d5185040d511034402c800841d039001c0086a038141082e4001021240b141d00c64411040c40c15400b030f40540030950381d01d80c3c411a002000759030340d113401990803001001c03140000303603031a05840f500f4401035038411110b0090800c80e05031a00358844061128940d900105000300d00c020020440c40c0c08000a0444512845a4014041804800a00241600c0c15500c4e8032514860f402946400c07505070144240c001a400d600d20040c0000070b5104a0700309111000110f64154003012540c05600007101070710503a0f002d40e9120681c00368080034150096412543c040c83c02000304018101c84002c203503021500a011402e2028603402407048440122150b400312601600d03078100 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 648953363 1250 648952113 648952177
    0x504060f0c08031801060f0e040201180522290402090406030c0807030203070605031909020d02300a0c0b030601350f07090b03090708060f060102010b03030715020f 72
    0x807001c0690b007000000b01d03000e245247e0304d0068a09551090340c443e640c07a00110ac20b01c5001402110b0070125850100d49070304c50076800e60100c2c0c2c1005a44008903001c04079042121b0121000d490614801403040000102c00072031103a00844c11140581c0710701c110350001c2c008190300d500040c440e40001c580000d003000080f0710081100e0003103064610040d81c4940984480c41300301c0741d8441340a501005145410296440b0484c3c160028200c03a85101c040d5020510110003040388200b04241e07110780540001c6c0c00c1c042c185244100380c02030501952103079140342040031640110100c40102000040c4144d00c1820b48040d1503903401d0303000900102110138400b100b4640f201700c0c00c05881f0980018030351291450321a0103620075a540c43d0007140b41511441c403903000541b41d103800d40150080003803810010016507000c0c00d04401805a2818400006821108010a000e0098205000c0074002c80c02070469108015a524809a99a04550041c02c910703c99850300320346e00b000e0103440c07603600001c50749 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 648954613 1250 648953363 648953401
    0x10612050c04060b031302130905010228140316020a0816030810081b010e030a2d080a03051b12060103050603030903031e09090408070b0f06010504060f0c0803 70
    0xd0100103044c0c40340a45005407208403801100741d00d10074007035001402c0410300c0002d91000041c0014002c00255625030aa038091110190003103518890050300346911920810300c8825828481d000c202d00d64140307241400020424007142c41c030800700c4903505000703022881c58954410486a42c81c400c0300580d8041c4240d041007600051244000255a80c039040401016501090000c0c10741c1c10506103c0600c0304ca00505d0503041102c1d404c00388605d034400704548540c407446114505a046142c4100c1c116804c0711020000000b586941010007040180b000c60303011a01524020521b50344200410705460314404114545080c000f0b900500a506460b00c0707402008243e03018022a100c1804166490003140203080c2e054100300b14152100c0040e40021400600500780942460003100000b08802021101aa007440001a1140c2048891840380b5480241c40d860f000080c20000002081402180207107018401d81c030400e0103030f40d802008482400f0341c0c0b16144594a20300090310390304031a1004 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 648955863 1250 648954613 648954619
    0x31902180c13080c010c020d0302010f02370509010f0c0f0602090f03120306040222030f02090901052404021308030406030b030c06120c1c0507080a050403020c040e010612050c 77
    0x1c04081819200403a02c4c644580051b51a072420046a030200306180380300300f0046003959611400d0000c290000c0c0042c000d1014200c104680308030000440e9080842500c90901f9800840e2030b1180d031082d0410251411320300c0a01e0b080c0480d001c00030007503e002d4070300500174020a2110710101d0800415400030401d08030190b640d5200f440c280700038141e40d00510340c4a440716150620029010381025806070601301d0802642107529421382e012160301c40e4041e00207035500710b0300100c05015801c092402c01d401006400080105140c148011400da042e1024996050f80d98074865446c1c1d41c0d140d406a880381083c81d13214504c20795031010041c0e40c030f40c01445028080307424803020340701da4070340840c05100e40080030700803d141c0f018642c0c0c0302061520042075040714403814094403001e1104800c40a400101d10040040e0030305003150302908a490040c0b103801214109070411000a80c08200c100a034032041c0c0c3c0118410405038101405400f094000c0c080c0843c4201001c0700748040001c00038541d003025 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 648957113 1250 648955863 648955897
    0x5090d120524183103020a080c0a06110a0201050c070507030f0f020613060801091e0903020f06130213020f070f141501030204060e10060507110607080c01050105040209031902180c 79
    0x31410052941c004d5000103400741c3c00c080806404515004028400c0b5501042914800c60156888004444009101e104550004a2040032440e024803caa4001462030b006c40d00300f82c0c161b51a255982424003004000010350b43c241e400308400c805104121a40c01000310380c1740c0c8050282101d641d0313600d10a8800040a0b44c000041421280c8220744000320148110405030b48120728820240c000e00400701c1c2180308180d0317901031a040610003e401100002c010314001100c60040111071050810b0128011f4810030428916840d810102e810855000500704034a0f41b80b8140b001d04a0540c000402050150907030115181421107101d5060301d00c01c0720108070054480100b032074104c0d01201c260255400701641402418054009401078911403030205409000d4200800d6854101e407000b1176805c0c0e4007080c5191045400e0045c01d0142209407000c50812801c90006a40c40c46580c40d80884c01c00756807100029511a0402c851f02100d00c14100f21013400d080c0d8440000780c0c8809114080d5504d8 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 648958363 1250 648957113 648957181
    0xb13020901060e030a200d050f1002280903020a08011e06050a030b25200a0302060c0702040b030609062d06120c0405090d12052418 58
    0x95a08040383d00303000d0001c2031400c40c16582e40f40d8030320303150344040302c0307850818240c051642c0ca0342e100c20407042c03041000c1c00b000c02d040902c640c50507600541c00d940070ba00600580308146018080e0085450500201880c40100c420094560200540001e07404c02c41500c400300e01d01005401c22412451140419002c441e016135020b011a00c5500034141c0c48880f0303000c1000403818416103039400c11032001d410a100721a050240440e028980355020100796803008418462258450500c150312990f4042d0548810030380d4000d4a403000201007590034a00441c0840640d140c079440040180300245c1203402c5800c1042c00a60340d50001c96021081c3c010380c083c907180c0d40d060b980506a003229004c0d2806941e4407039004000740040748082111030f40c411100c1c0d400c51b40e5581d001d00e074000d184040142400300c84152000301124080c0d81d07410b076102c3c103240900c40e206441801003e4480c4140d0040c1b14601d05801c005580d4074818452503402c1041c1c5014400c0740e51ba850001c465a2101400324440d03042 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 648959613 1250 648958363 648958367
    0x706090b010f0603110f03042306220b010b0a0e0303030a05151c03031e0c09080d020f0a120c020904060218010801030506040201030504060b0a030303020c01050c0c100209010201090b1302090106 85
    0x601e005c80700903c82000d2102d40c040640f600d01640d001480740d031a52120100807040101c0b50410821051210340c44102800782480c40b00c41103045004518140300e808007440e44520092940611451510900c005200003030644111845001014010f0649032b40e07041c5010000d000e402c056804655002007240003102900d013000c0c58034517107280342e41240800341541d1800e40050000c05510194141c0000700d06810403070a20a61036080c1e0b0b55290b41105505240f0660b1410f10200382c91419503008183c030b0080d03802c0001d43c90841a0340205241c00001c145003040b1801d0b1781501009410030880d0041c041003000f103401410412030010400110303a081c13000111a840000c0c40080d100d0b4114401142c003551103500035a501a004100214207403180d103012415003010707940140e0020b94085a80b00c4c01e800c0038014550400121006241022500c928603901c038524191002050359000800e040c141e4000c0d080075400507040380d5000480d01c0c00c501c0c1180c2da6014110200c1c0700d907408100102e2040c0c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 648960863 1250 648959613 648959621
    0x5030109110a081504020f070b0703150f0b0f04081f23040311071701020a090e040203060705220b0a030f050f0a0b0d0209130b090a050d03110706090b010f0603 70
    0x10b18140ea40010301e03124900d00b07244945102c0e41d4680c00640070400820ba984104000f03001c22482040395003842c0c50b011200404940c09440320908166005030108044040082c604095400e00000d6030703684e20840d407000b03015200d1640020520300400250038600c002905100c02a440403100601c1028207440607900d4000700017201082140500c030100b40030034407a00f0f140507548031080803285040c0e140d141801038200f08a400c41c1c5681c0d0001104800303503a102e582d407002864002424030007410903034002922028010700c0d6204000010802c10b40780d40c1000c06c08130004c0c80655002015940780c0031803540541c4100110404281050112007850a142c4102032080d00c94080584440d01c0304440c900c041c0041442155000410074081000360f03860074500d50080031403400d171600c41302040c0741c820070340340780100703484015005019200e021030004100e07400f0210007840c000a54002c1030940d0041401129405401649025a4002040101000345040c1c03180d40c2d91491020381c0d1071408138152 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 648962113 1250 648960863 648960877
    0x6080f1303090e06010203070c0f051e0d0204020906070b0906042a030213090602120915091b010c0803090109150b0612060a0b07060f060905040320070b07030503010911 74
    0x70b150a0740820900b582420400e40000c1c0520580b0314141c0c098030f8034108d0003000e4200d82c441048001e420082c03860010003d010407540365400c040503400241c0040d11004250320040e018a4000034ac18546544013012a80c1da1644a90441458107050015a41d01d00088800301c8064121a40d800ca6664984000ca082e1841c0000c00d884140d0655081c0009003440760241c1d8226a11003001c44002412400a07207460442c03072a40150515012a0b441d15041a100001070003080030000d01c00e640f5000b050352003820400d45802920342c40d0110040700c26108a040141c01c3c03690100500c002030806401400c401e9009000328541c401d010640307c01282c0a10040039401700040145000224a03541813a074480c0e002051034200b150349006144140d1b000440c03c54081d5a00d980e4050f4030282d91041c040601000c0384204500d141c150342c0640503550b9107004000307030000c000b610180d140c8100104005400c015116549403c424a0042d00d01d07082170040580301ca00307007003030204c0c0301c000b8006803540 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 648963363 1250 648962113 648962117
    0x9080d0c150b0f10091809020f01030207080a0809030409020706091103060108070603051902030103051614090f090703230c06070503041a091f1b02060307031a0a06080f1303 76
    0x140081d02c004102c20001100c03044c8003031001541e8002904000d0800d50009010302e0b58001c80c0791081c510412000c1c5009003003c0d81450701c18008540070a6a541c2907405801d414101164140c40d0245110f195000740d030b10501c80a400001c08004000d0281c100c2100d462003414070000d0400d00384105a180d45090240714215801a8420004544250001c50308512060089043c2c2101414140181e80c426002a511035100d000910801095544071800800207582c98009140414000440500c0c0c05006140f203078080070080b59401406100240046510034051020000e401c2900c0000c410f00c0440744000340580b0f10002c1d030300d082510803038240c558488040c6107171904140d402c80100741d02108550142005114180302511000900200c6a0341c0c41c40f1122030031240e0800510005a4000183d00f200c2031058000041c1c440300c0076281c201c151400c01080036215015100701c0405180745956026141d900d0009229070085542c50040c038201543c0304032035841e00520000d400f61400c0c0100 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 648964613 1250 648963363 648963379
    0xb0301060e0c0f071205030103030906140304110f030106031b080c0f040e070e09071511071a160f0c0803120103060504033605030c011b0309080d0c150b 67
    0x1079041420b600a141842c02814401e06080103500c03800524203405a241010420000c01441030541042c007500040a15240204035207001500940003400054001468600315841d858210307660909040700703841f0044e000700301c629641e040c9540c0f1807920100001e40c0790381207003001c0352155010808030a0741501601404010400c4014030004003403086809946018500c004141e64a540d80040c0c0074808142c01400d40c82d080c03001d000c007e0180018140240009075503400013510700801c08000301c0f0040072507401440c02c1c000820002d80306101d0b00010000c0105810301c100040c000c400c00c80c20340106616201c6c3d0b511802402d50781e100381a01000005031000042000400036040240d00a00c2840d2070020540000e00321000034201c848400450006c240c20f030f981c010401c2550f5401807d04500514154400400180594498000011a218007044100e0a0600813000c4800900000c0100e52640c103009000815401c0d140c4001c581c40801c00c02d441031849181e010700c89020300000c022076 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 648965863 1250 648964613 648964621
    0x70501170a1404140d0306050d03030c03060902210f1e04020f040507030f1104060507080c071a1207030203062b21020c1503010e220606090b0301060e 66
    0x5140c0000c0103001d03040464031605807559071007021010b680954843c0d020940307104888002141011041c502c101d0405103040c1d005c0025617108200030078816058240015481d0b05918118051b04054010b41c20040c00094030f11550001c510f00d40c40d050755003400b0509252610348911448030790030740307a61140c04466544103c50700c100110700c581051000b080c2410840b0002d0208050740c204550001c0441e590f24201740c203d03811401000354824200c0381240c501414010054410f0140b01805081030348041660f802050003080440c02510900d03d005101030449540903d87e6840001c4081c1c1c1442c2240124031070ba4064000d60b405180001d00304403580d024100320300106812000d810004d540b40144010110700d81000c0c4000c40c074504041040021411400a89083d140e03d40441c000c00810301154030b0f003840c510603641500d4004540c50742d00d864426071580d0074013060051410311a40e110781401001265031091040700c000d140e040c00008080b004140c00c80d035003072013a00e0800780c100c8001 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 648967113 1250 648965863 648965897
    0x306070f0207080105073603031d0909060a0b181018060f051005210105030c010e0315181005010e01120b061018030c030204180512031008011a0f0102070501 69
    0x40c01d04103031607081401d1f04c1c0d140c80d42048101102d43c1c4250045848a02c040c80c0141807072400410f00e1206446180040c244648125602e86c8000d22003805d060360b400058000760f0f00c0b0907840000500410701001c0c982868004030b400b040562040444000c0e01d170850058801d05c0340284400c50346400c083d00c020a00c3c003014814002007542d50311042210400444650b120115581c05e860110000300b0401507041505140ca400314450f0b440381480210b00e83c8120b503a9000503d64004413070741400c02180d8950008a6002c004840a005a50302a80c000604c01c1e40c03013680f096048030040c007003003005c5998400d5a032642115100010380407c12401c0041c1d06424814243e010354500e40c50503112040100031110f102c0c070800c2d00101c50071884a2070800035840e0500803014413003440c41642580d13050541d81d0f580d030b400b0000000c5c407561801000182003185000a80402855050000d000340d2103410048102000c0f42031201d0b104e04c011036030700c501d59407001a462055400685600d40c4040581c002 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 648968363 1250 648967113 648967157
    0x9010e060c0306190807260d0f0e06090a090f0204081f0606210b0114040803040302090a05090304031e060f0504152738011a07030302030a0b0306070f020708010507 72
    0x4140c4400b1702d40314983c0c7c0e8801003111440c0c481c4c0b5035668000b1070310610f400620310b01219200c640f04110034022500603a40b803e400c1c000725030304050002106100581d401c000b03402581c0c803809480c01426048524103504201c1110205000c0c0010407040d42c941c0c80c10780d20360a20070800ca10116085e006134440405c96030024030042c5050516809200d903400d0f034142d580e0700c6608101019000880c1c02c1045040001880e5000840000240300030726106441c0c580d82d001e940300c0a0718810240507814000d62030030382c0c00580d8503005002030140300c288a0966020748020b03035046030b000c0d040007010b0722074807018402c080c46080b407104150244113441109256281c81064280c1e1224000148201c000507402c0f00310444040d4001e96002105010b521f042c1c034200305034030682001e0581000001c214407003508035075400c0d500d03050040e00d0b5154210050024490030031142d030188204002d00c90b4090304100c0c4029030b0b9100354200d5024640b1202980c1c2611001d50320b1070003042c0f074101407030f15901c040c02d0 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 648969613 1250 648968363 648968399
    0xa031d0315070507031e0507060e030f0f030c041e06020c15030106210f0b01180b09060d021603110d0c0507170a122015070809010e060c0306190807 65
    0x14000c81742c0d416840e040c186d0460b0160b940008600005448020884e05001d2901e03070a00510185043c181e40c0b10a001152242070304007000c0100020000d489040341c94280d074003500c0c141c000c8600d0071410900c44c0c0d4a510840c040e00e000f40c45080c00c20009450000111801160799112142c1580d00e0070341c0950710401c2050000e58408102c20800f0b00940d070b00d11480032000c0b44a040420401216000034180c02010344072540c0442c0d01c00c030140100000d4108070b810070320050722401d954030001d17a594070082c0144031031300800030380c01c1c080081419801480c0103211440c2c5010f0352030400d40b00341d05075854018203400034625080208108030b5080b84884210fa0b6502c5c1c2c5040d41c0b5000c0d2150b844182548110004ac00800ca500340745800000d07030442d509802d022150028200142400003c1c80d1740c4200500ca41d041006035400105c10901c20b40211440005c504210394107800c150100d104142c0040310401e00a01181e0800410f01c800c0301e83c0d0004444000001d041420301700340c00d1500c6449102 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 648970863 1250 648969613 648969617
    0x1020304110a0e2a1209031809070804031206170a05060601050c0703080a020a0b01121110050d091e0f02090c040e010b03040f0b01140307080d050a0e03010605030a031d031507050703 80
    0x3c8080c0e0551017805c0b003144d00ca1b048440140da914840c88d01203c00384203101f4200c5000340100d030308102100381c00046c0c2e13580260301403c2100d20445403901640c00b030407858008201c400e0b18212441c51890f0005041c644503841740091300c10a41c0c604004650f00d00070780042d000365900c07412003040422035141c010b00b00f00203d0f106480c880744c12515040041e400c2a0721002c819081084030750180301081e1440d003600c50b81180d0034450604002c500400b03270b010341c1d0603210580f81ea403500802040b1000030300c010f9040780c0340303180651380074507041055180c05402c000741d00807044000025550401042140c040e140741a21558641e42408590490f50704000c104583c010b10303030b0703001c031020424107183e4034000c2928400081480d0028824035041c08032607031201c1c402d94424080d01c00c00307540210079541e6040c4a4606261494500c0000901400e00e0b42e00040c0c25002e018440f505040d81b2403040100c59202c1d400303130207841c1c1400741499500c03952201e4426440d0031035004501524814801485a1343c001c2c = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 648972113 1250 648970863 648970867
    0x7050f06150f1215130302010b010507020105070b06010e031c09140a0e07050903010203040b070f0e010206070f0306090501080607090f030b010909080c010c020303070f03051006081801020304110a0e2a 88
    0x32641c00d0a135802d003580c0342c0440407408400c0804040e82400b846128100078039044e42410240d0b400078209004801c0c0090018403a0000621141d22814407100c0d280030003411160543d50f02e11001c00380703080a51136880000c0c104040460400020030924000e81000307055113000c0c81c41e100301030321049006000c1c01c08000081145d58140d80d000d0004d14059401a5410f480d20f0500040182ca1a0020041102802441c4200203007603070300450001d40c4002181803580d652040d811040b0000c107011741204250314a0500049144030002070400c1c403902c40c685590141c0c0b0713214405c03500c8501140c84002d08400e08030005010000807034011032480c030300c0343c1c1a043c2010203c0b11080c1c00d4596400002c001130344007204000d00181d012501001c1444141010040d6090407051517a25044c94028075040c05042e0303000c50b221003152512071103042150402103440e03003800d1400848046640c038000b840ba00ca410310224161401c542401d00031614000c240c020300c2200e25010300c00e203400100b102190481 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 648973363 1250 648972113 648972133
    0x602160c060e010e1e01050c0a060509060103030f05070506010909080f0a080402041d1b0a15181401020d030f020c030417010c05190305150607050f06150f12 69
    0x40d4000320050300e2140c07521056481480c000501d903211111100344501d1034451080b829888440200c1d182d40805c0c40c2469403552141642c914000555000900c1d02c0d18007400c00a9554000c81d01d14140ca120f076a40c40d50008801c0811a0240259140503280b80c01c800c0040040d40c4190344401c6d060340c420030080d801c000c1300d034900e0426604848086408540098104011454288580ca802c030045c00545205542172007a40c55949102000080d0350900c2c04500d4071342a81c40c40501c0e401800120746041030a84440001054095124001c1d0680d2070800c10210355000000d04641c50000b045e4024000311807078000480c080e0083c103e941184071f900b000000d201d90f0701800100050011180780c0107902d80248115800c40d0040803c0c1800c100041c0f000042207004810741c07021200305407078046050340320b01c15151600da0040d01c4040d40701200181c0d2404204021803a00000c007000b105403505541c50b660591454083c04200550002d50300d091041140382100307042503051809006c40301c440c0701c = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 648974613 1250 648973363 648973373
    0x59010201090b180705101701170a020103051306020a0906030c020606012a14010b03100e0a0f11271006020d18090e0703021f1b061b230304020d060216 66
    0x1d851b901000a40540c03070700340d5440c1d00c41a1043c014100c0c042c00946001c10b084584d52941888007001b810075480c1c50114840c4068103200480c41074009501f15911864807034007900e9100b062064038003080c10441c11582040c00480c000d032145c0b0741a125498030402002d0008507140301407801c00605520300307040e81c0204445130001d000711281c00000041d405604803c140c50800040000440507081108c01004003001080741e2400d16030060301040302060525000d4549803d02c6040d5030402516910748043e15410640101400c0281403c04807688513842895401c0070240a1400540d111020640300d2510034401d5001e00d4441041e00c036002501c1d0180030f002d850341050140c105d58000c08050096203803030100c486005401c4050304150b040440b1015090340915802e0000e00d0325160140350900105d60040d10003400ad54525407102c600401000d011041d070513005002c2003400b44401454102200222406690000c00301091007106a962801940c01440c0b41001041c2e09040540021 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 648975863 1250 648974613 648974629
    0xb010e042102061905011a0a1b050105180f0c060a05091c0210021519090602030f1f0e04020d06060e0a0f0f0501050159010201090b180705 61
    0x8500755019120b5820140700c015844046103c412424600d4800100494441e0145a603829006c1e42d00c5540c0300c032001d4409690300300e044d00c84146d15003040c2511343c08002d010f62041788030b114150040d12851001200d02aa168005403201d04540d002604200003854240064207000d90145070440c0707051900c10214a46000d159100c001442c1c080c8402c0b0704501c2d000c030101c1801c1c101e030710050140036404401c410780f2540140c01030310284041502c85071303050f10940000380000e0f0031220640d5242044082c02d4055581110703e220003035900b1010540c0305902000c42d504444210304a404a6116602046681c03003621200700d40303083ea035220010380e00708000c1c1018850381c0103940009215a104600e542035038502045034900503d001d005004980c0c000c00c52103c10703295a4100d120000c0601040b51000242c0b1114000386d0211410417480c015141020703c036001044d4140988480070900164203031548101d00520740d0205100003070b0008444248140c800c80280e081782c01070b40c0d032100032800390 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 648977113 1250 648975863 648975923
    0x211d0109030503060f0603240316060509030708060112080306061b0d08061804060e2d070b0909010314100507050a021501030804060e0f030d030506090109090b010e04 73
    0x210b007011040021910b403500082071103c0c2c0581c3c0c880d01c2d602e400d8000c1c1c01c1408034001140540f00380c03107264a20300d86007084560b10802c0d0902982e80c400d80c640c0b901904d0f54200ca070049100788128100450030032808541c150480300a020034003d21030203039842e03010719000104030070703001503080c081010080d640c03c40364141e04414030040c28680c0395107103004010350402000b050040380440d01e10b079410303050a10560b40c0940c020350001485104140b50f02d050415541c0e0f010415181c24622a0280c58070400341104109003104580005664210a013228000c0c5910030780d00c601444010404528541190b0424000841c1603a03555018030a108040728030030346170390300000e1010602d10300460701048442d80c012040039150721190b156540e03411a91165004d064104550798074a0b81d069101d50380385826080c401801d8501c00074140c00028001c19044465501c00c5461000004000394a885011503c6420095000540c1c1c24890300303100d4804050000c0399103001e50642044d001150a25070040 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 648978363 1250 648977113 648977117
    0xa120f12060b040314010b0105030403030504060f0507080604060911090d02060c0102130e01060206160302130308040e07030c0503071407020a051f02010614030703060903021606020105090d211d010903 88
    0x81d1421405c00d5400703248402904101a0f241118229550783c00c2802c0d2035000e98186408035941d40c4902c0d2103800f41218081d4900480c1c10403003401241600110399601c90f020a80301006072640e1410140c0684403038a0200c0140c4204200d10080c1e41896081c1d2103449001030700311460072138000881401c81e0f00000c1820b0b03210200d02d500740101c0c94025181c900524030b0344021302690418448102c40d4483c80740076130051540c0054107104064042007200025030b0018015500c5558440b002d1101842c101c070802e002030719118541c81c2c06809001542d0003400199146900d0300c94a040c20000c5510514050b80d00101c49900001c00c2e1b40d60500181d01c0340441104000c10040158010f401d43c0c1c52a0072010900903004c1480115460004003201181d40050011501d03110074101682070030310103200c05900b81c203413140105013190150441c6009841000c101e50085139640f604480400300e0313243d00301a07264141039000080b129034008042916145c000907040307807800300c03101d400c480c0c441d031040300 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 648979613 1250 648978363 648978367
    0x70c0803010902071e0803070c021c06050f01081501060f2015070e0d020d0c0902030405070303020c010206010f0905070e040c0f080f01150c0f0c0e01170a120f12060b 73
    0x10058070300c0e2030904c1000c208117282445d520550f2401c2d15408020142d204204403140400155900c07050400702e807113485400c1c0011041c80d03040520113010200c4400c5220f0450400015011000050010b01c100b00103a2848030f41c0d003848821615400c030105c2100400c040a0000407406001e0886010308408090003444542d0310f146542d011000e000744200b080c4840c0d544d002c80507403513800b048068a58115940e0490303680510b02040c031444107400c800c1039940701104210800c8030028000080c0c4e4040d40032241e980000000480e0f643c4402d01581c1a04030b076481041100800c240c0116402107407034181200c0f0401c5480204085402941e42d10000440e8000d07c45003140d040080e440d004483c923810014658107060702002010104520401048400091f80e0140100070052404469000b130b051803d050380da015120107000c00b80640d90145c0e2003800c1ea0303c40c00e80c00040b0001001e90001000c01504807100054030400b0f507802807c0d007031024800340060740c12154440d490144c400d4411446d = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 648980863 1250 648979613 648979627
    0x3030f06121b14040f020c0d091a0a120209030c030a12090608040c150504120609172703100609051803130308030601140307090512190b070c0803010902 67
    0x3071481480c0702d41d54000d8104268140a5800c8500034038140010959020030000204d443c5c01c00240300d210401d0007240603000310303a0440c036030220380c0d40100d85400c4414110450300100c80b042900c01c08464101007a06071940c91100c4540f41c02800c0320380b100030107444081304420003103410181c04a80c11512200b180a002c480950081044406440d4900d02032a25150035524001805080d009406811003801c5c900681c0510070022600644070384504100c8000da603152600c050000908101c0d46000040c81840007820480c080d01c8150085240e8080440142d200740b0907191942c0340440d0301800740322180c110004075802500020401c90b90001840e1410f5540fa044201e48031480400c9904100f1140e01e5840102c105002038940003054141d41c0d864280041e075100030205501c400d50840032080103074854010080c0d50480c0d80540e03e032035483c1c01050342e06865440040f080180d604a501c0101d0200d010807440d20350003036860a116243d001c2c0c1c0d40b54061a40c009174800a4502d800007854 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 648982113 1250 648980863 648980873
    0x20904060507030e0d050319020c120c0c091311042309120403200619110705120d050708070803011e0503150105011803080a0c0c0e06010c030c03030f0612 68
    0x1320101d01c1d40350280c043d04121200080c41440040c0107501820140d41c01c070b400809041d4105c40f442050034044030340c0c0651100340c02031150845078554101e40110a040380150400581541c03064544021406a5144070740e1510720950a41e242e081d0440e80c0c520120741807060080c8000340811aa4502544619244800300d140c1101003503468030a20301400200001800540c113005025480100c004a5181e01d0011034a54024044003440c0a0f40c0b1143e2140441d80200c03000402c481944143c0d00010303240c3c030912445105142024207154081c07e02100114402c101500200d071040645901c1c0101c41d0b00e030003010750000e8024040601d100ca20411125004502c000c0c000c240a174041d01c0228289150645500790502c5441d0502800344000c088081d40d03481e40401941d0300014940c0c4130072070703800020324000020130211080c2c8100d503c042032909010000d2445604169103166101c140d95600720303620070459008500b03160310340c800703586c81e5203480c0280790240c076070082c4041c0481c0300c0c1d01344 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 648983363 1250 648982113 648982121
    0x615030212011a030c0304030201200c0d0e01021e0c0405090c031c050403030c030e09070806010e03030c060c0a110d05090112021801181e080c010815010c060902090406050703 77
    0xf000340720b141054509450681c60192a4010741c0007840c4d0340c0b603a455041c141e016220b181c810b11710901d13516002d1403050000c24040c1c103038540b241048802ca841e109600303450380a403c040460159014040b48024a103122400982d00840f205c159000f125840000c10142c075000e5036140c81c5a0064140d01c80141402c0000c200c2c290301164003002e442c0140c84000c0d10749e01c29408003a0400210388442c0c4140750040d07112803900140541200031900c0c005034010500b0f2001d0703031903500048800798160510314000080d100c1000f02c03040a000c05440c0d5080c00107280c0d00145101040c040d500e030078010010300920a02c8440d881030f032501e5a907004640c0004052005609a04108910502201c07910141201080008200a00740f1102040101c1c4109116084641c001982c0c4e0b00400c15025520b03840307012030002c80e44100105c0d2804c40e217007001914884011103028008640c0f428110380150b120f09a2054014051800003d4001c03098001c54661102100c055400386d440d03806102c44203515120f = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 648984613 1250 648983363 648983369
    0x604150201050c04031a0a0e03120403020601060e01080a0507020a0c080601051302041202010c021201020406030e0609011b030209010923130b0f0108062704030201050a060b0f0d061503021201 84
    0xf4075142c10708542d41c00440c00b08011030625084060000508100010b5000a0480a001e41103a8494048441e0780a001108030313011001801020000640ca034041e5950140c0c801e81619011815a0f41c0d800b51402480c00600c51130861103052030034400319007500c0046010b4020030001d000315605180030b00110080706042c00e94180c0c41000b00704a81c84103201d5190741c00b0b0342482d203528054070a000051021101000302a5654400100001c400d60150320104501c2075003001c2c2d865036914452164200c8012501d840e841d002100340c682000780c0302e54010406d2031014109046840d842d440b403402075000b00201c01a000050700c1101075945030002c4142400c0c0310002051000b6191071000c00c0308221700e0a07510f418480c1c03070f1003c9103d40da241c520800b04501d003900300c2d1661160000c0441901e503026542500594030f400d01160004d03117540900f034145c7d64036550781c0389000c5409800030180e62000c504420042c0cad640c04040340c070796100c000c8200c2040c0d85960158440c4100407207000703805c0040e4 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 648985863 1250 648984613 648984631
    0x5090307080d02160f060c092706171e0c01124115010c17040b030c1215061c020f281d130e010c051e12040b06120d0807030f0c09170c060415020105 65
    0x181564490360380c0584841c05143d40f4101c045100440d40426200120048618410351140c010068109104043203080c06580000c0e0b805d4450b50304c40705c1001c030303103800c00409060000d19040d4058001c948500903080e55454140d540c50301c0c1540e40c524000140c0c10565124420000001c0c1030400114285407054001c00701e240e11490000d00140040d01034896141e44100354400c18400c01c00940d8650b040ea0b103582402d5480941e200c072400703521004250a000150b00390500e44292111852181d400010348040400c940510205000200401000c004948400031a2201030360084c4000a002e010304000da103441d03c070b81380c40b5280020030006450317040c03115000030140455a8520350200c19075802c40d030868000e000b1030721404049030300308882049040003440342188c490700c0c01e540a05a20310502d010b982c04c101462200d11000706481105e04840001907131194280103503905013504128a035828411259000e00350303008620983c1182d400461404041078204484680a0013181c0e0300c000c0130 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 648987113 1250 648985863 648985873
    0x80c0a080f100b16121715130e060114150313030c12051213024509060a05090307080d02160f060c092706171e 49
    0x20800144400c0004015840005461000c950589074890307400c805402107640481c1e640c00e8806505840840c440d8003201c02c1d45c3c0d0645112070140c400d401c00018559041d1030040e143e103559441b49802807401e1000307640280713404c01268109503207228110740e07581004060241989020400007103440d131152000d00503c6c0709040c1d103424030400030480758010707080f8555111200c160308084600c0001c812006160400c0c8203989035450345c00c4406014030b11903500c1c40d405182c0e25211003080e25200440001e41281042c620885130412101c40c040105412001d80810140c0b48842981e00903019104202940400001c1c01034021003800000c0d40640350320303000d01090030001a02a0b581c8107502e00031b080010701150501061080c0d0301110745114442c1e0716581300ca0800d0070440c429408049045488500d000d440b04142c601070509181224407414001010032401842065066201c81d1a400b2280c0c0d225000b085168500d000c0c4806d800b0743d40001d12034404c1030b424090301c0c50202180b003206907104e = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 648988363 1250 648987113 648987127
    0x90b03060102030403031b0f08040f050f0607080d150b040e1303020616050f0315030f1f090203010e030408010c08010609030c060c0503091002250b04090e070e0a02030601080c 77
    0xc850817207501d0b06d00104940b042d80d4910899494080000b8119802c208150007440796020182c01035a85244807110241c0d61201004190000311204940160040c014034000c02c6c000c0c0d015242184e00c0800100d91003583c41031112a01500f5000440381000100d814880c9945821906901c131401161070f034031024541d2001796854000038110ba203d0181d040e00310071480e2186080d40e444407402c071b21180d240d080030052200c1140040030b40b11301906c00c1804034203c00d10001840f502c4041c102480c032544104259000307000c0d1a000da01a6095034807603800d04440c40c0100020300003045900000128010610740081a215040c0d00640c10080059803d10114800001880403100c00e0b04002c86180f2107450079070304501502c0d0301940d01012005001c00300540200c0d45211152000c00f41c090a081045498074903540e545c05071b881c040390148403d00140f0201d622100614040c1021900201c1d034810042c48040004c0b100420340e190084144a82d558025030105d0308128640710840c00c00030 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 648989613 1250 648988363 648988367
    0x160b090c041e0c480b0601050a0201090203100609150b0301151707020703060606031815020f1c0b01050403110906011b05011b09210303140a090201090b030601 70
    0x10062070300c00c5810765101085403110780a900a410030364030006291211109140100244d0000140c041000040d00040601c025182e11550021140c0c850b540303000c2600da2030011100b40c0c22175440003080d90350b6251018003581e010003c00b10361000c079100201ea1203091080b01000d80d41f0f030194150b9041c0360030400b13010803041482034030705440340365000d00c11359a401c003422504c02e080d441503c2c0c20007000e5400c0c031004d40c0d0f0116541096a01541c82132006507900c40c003c0b0700304d50644580850244920f061540000c5203181011201180c00b800941081e00103514200fa1b07900525005403e4180c0e641403404082090262280481c0f090030102d08007882d64175040309000c8918480c078843da0442d0001407991303004e424400c105001c011804041080c0d81d1510070300a21000ca0f8281c0801c112103884d080303003441804280300b61500482c1e03074415422403006d032609080c0380940c11000d1549815003d601c0203000f015051083e00d0070a400318200103680005440a40d0641000755582d40030801c000301a6 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 648990863 1250 648989613 648989651
    0xf0b01090306110702090a1a031903140714031801020a1a060a08010509031804060501020a0213020405131b03110f0c01090803130b0903091f05160b090c04 68
    0xe600020701040d0b003500d101e0480024030410a000354050403003c280447c08005500502220340c41d10400300d82401428101580d5034403850a060307038203103401040300001c0d20900d0750385460800c180380c1508050003075a4820308140800c428441a03400031800c080c000365600e07408568002d083c005040314103002d845814803a4103042184068440980204805071105c0d0b54040040501600030002800c0201003203071280d1003024030f40c240b44902400040f25103040c0c03158500700da0058008001100c8180d00f0301c421590410060030303146500307020004e480c1c0c030744503e02d444440c09810006a080d55400c002220b4048000141081500d4940024102030b1000203c0d204041e401101d961209010880e1038090039040f0001099503002206004444106510703401205206684004643c0c0d19041140d5917030048156841d44000400c00f02003848252240e1984591024500103213050200003c07336080180d484c40484e41c0d20710150030070442013800d100c08451070f4000ca40922030030f0500098003401d1 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 648992113 1250 648990863 648990869
    0x608030f070201180905011418010e0c04120b0a0e0f0d0e040b040f0204090e0307032c10020f07120c140a2301020c01051207110f01110c010f0b0109 65
    0x8814005500800d684c01501200320740511540380c0c07000d56848401c02c6016050a01c82c2c090106054a00c005a5103400d00302200b28010054080955078a445071824076840c02508480701c0640802000ca840250282814113241c02401c0300c2c10141420f02c56901120354422500301c490300a52181600e4940104031908188043d01e0440c100103140b00004000b000d01428680e48140346c611107040d17000e9260050003c86105000c10407503002c0251b1407039207900c150f460040008007000c0200b20106950300d20251105140001c100340344484c500810700103002c540c165000f50340310540740c5101c041d080001c88082c1c08a090310410b141002d5031240700d031300894001c48448003200140052641c6800b40b1300401071180b2486072140d251203503031080e40c4100001e49039005000706001c400d80c42d4010001c0b01c44241005030301c0507581d651104100c0b40b4521048035251707240103115080f00806024040d0742840350f0000925a40c688a1801d042e084800d80b401d0703003a5160900100e0307901030381c000c5110811 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 648993363 1250 648992113 648992137
    0x50109031d1c080408070e011a0a120504050a06090f020301050a0b030a020402070501140c0a03180b06060c0f010f021305090f18072103120608060114030a0f060e060a060803 76
    0x9040c00b40d2803e400f550080d50000b9049100381480040c103441542d500c141214490002d0075050100450624103c1c824000e4000c0802d000710300c0e481d0f09850590106034000e0240050711808001c950303540d019201c1c0c0c1c0f24282e50348407517810804c0541c42c084c40340d2034206000180400c068108400882c1d210616604082c2c07280d5408180c50040c0402074001110722905544040c0d0a0325010b16030065031781054480c007002920740300d80340b00007141c0c0d036144440c1070b60402e0300e010081ea280010081c01342d1001e8010091070044007100c28030b2035000d014400c0103175164800944c858000704281d041442d45507000b98401c40c080402c2c040b082030401c218030b800c5504102c0e800c510b0030803003c01600c0c002095101c840d040702040d0391481010151a507118a04d88656141a1007c64403500917082d24640c5c000e0100c80c1d000741004020601300b440003080d490030050291104806c2e9510307101c220200158080da1850745540c5c060001440511245d6840006000b00b004218203040d07030295a40100696018 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 648994613 1250 648993363 648993409
    0xa0e0606010507080c0f060415060e0604240e09160302060a0809120a08010f0510090b03060103230103060606050a0504031211060405070e0702030403030c0b061c050109031d 76
    0x414001c2c03210417204903075418000c45800f14440960b0707582ea1242110251002c0e4244800014010210b004403001c803080551007483c0e075100d910411008000445142154249160350f5400d94507598051400810b03414106008034504615074505050700c00c1600e80c81d10740450004d00040c1c0d0341c1819101c42001c1c5240c074004070364a8642141c038051040004010ba900041070900c545903100d840541030350030000400000b26592014001c0f013098455040e00801c008030000d11022490001840d800141494042605000340e00c0c40c140160101c0c03000c0381001a4000140f0a01c21f09000d210020100c0d845d00d980760060b220300050060140e4000107010001141c106203000707229034691050000800c041c1c0e42e031402c09240050341d0315180d1288507100d1501d02c000402107400402950100c94260311041201702c465558030b000d20b40001c142a601200d92070610310700c0b0f0300807110914501e1058000007441d0708542070181044034840c4503015a076072003d80c9032680707484441400c8410b0310301e00c4c0e08107 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 648995863 1250 648994613 648994627
    0x2418092d03030103082104050a020102010f05010602030d11040f120b010626060d17030601030b1906050d0f02040320060415110109080a0207051305070801050d0503090316030b0a0e06060105 83
    0x700320806c10301280030525585050000303012000c1544030b8043c1c406d800820944208640e00e1041d90424400e40d00075805c280808450080b0641244228501480d8124907040e1984034060382e40425402c020300960895040004004041d04076a02404490808601d100d00480e80348420411681c6000d42d030100850200d42607888048030000040d0340170001125840c0d8100015902d500202c0780300b80040e0034407100001e6400c0c065001c0301581c0045940410b03007810302206a845902c01c030369120585a44002106000081d4406400503500c030740440d80140f0b10341c4221000445d016800c0510820040004104d50328188114000000030b50619507440511002d99a004010b02c0c80c014007500c0b030001c1c0345a611640803c001c01955012105055684855040501207810449481020801703100040c00f0758904030380a005058070400440b8940343c90140442e0404007520713000c080040c40030409004008580031090343c4002560010041041d03514005582d6034805800c0605009001440c1c0e = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 648997113 1250 648995863 648995887
    0x10f0e1e28111c120314061011030403030503071107240c0c0305060601110105090a032703061505060a080a0c14031602152418092d0303010308 63
    0x20b212081d002040b03030382d959010009800c0060007490382160140d9100031031001480c02032149600d01c0886851104050b612081840104d4019581000a005000d201414a42c90400040000d503100313685082c1c50b420010f00182c0b00c800c5484d041606900f10160900c00041078250f8104d5600601080101d9022002820b440751100c0d0000030304001200f10011040c01030000c1d0303060240400780e07078034140085ca020b40c15080352015951086650407804590f004a0310656200c40004038018620800c001c50010079024100c142e03004407006a111007180803c420b050409000030041560030034980036941000402042000f8004134219580e4030825800300d02c19040c600d08501c0300303034103141c3d81d0404501116148010205d428018071800d1a80c0c0302c1c5070058280700c0d006100428144000c00c1d03a104515043c207203030007a45c035080354103030b64050102c0c2500b01d0800d000f0400700c4060078254503000340751010b1000292100f0071604103214154040300000040324116070300440702c152106289541 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 648998363 1250 648997113 648997133
    0x14011d0a09080424020607020703150c1b12020c09040320011509051605040b0d020d0f06090911040e03040b0702062101090b092205010f0e1e28 63
    0xb0070111000d013240715084903c8440385451111305103400b10f60041c0c3da4148220b80e628002c1c0001405115291031400d1858107680200955070410b003070140d85040300601c1c4621481841c00e00b6100d441d1214014200981c051204190400054440c8070031803a00c1d44010b4800d941c0441c034440e240800c15480544488290301c68075945100c2030100000d83d0381e0300d034182c014200030f4400c450001800e028409615010700101e404442506a059040c41001c0c440e40c1c00035006500115400c07034484958005002c201d11a1501801040e14001803840c42070406400c24150b40d00c1c0355010720700d03040001403c00d0002094030110380c01281d03003903039a09461000c5421801403c0b181102907080b2841c15003c0000200300c01d0595528400401280000d9000c018505a0a9480b030101550070298000d042c0c07449005c180e0200c0c01040007013880d20348260780301d040300c43d402680c41d9030b42c100c21030b104a81e03072044282c01881e0810700002c100f40325030140600300d400b070b0780f400d1240c524030041c881c041000000d100d = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 648999613 1250 648998363 648998369
    0x603070e0a03080d090b06030304031208090c090a020a08070f091a09090103050c01080c12010509040f020a240302070210080702120a03050a0e1603080f0c0f0114011d0a090804 77
    0x240c0c4a4644c5038080290015000c1c03420200c80e2010240d001600d90306000007643c0450b5040428180c072107002c84015980301e280940400c0b1a40165003120007607403218180180103488465006a60382c480490050106201070000403c100c0761502d242545580007020a040d034a50b45204030003120080080c440620500320101c0c1c0050b00d103c000018011b02080b52074520341c0a0b250300318166603c03c2c0d4030b292886181d08103503444503100018001c6040200086078070074880c0803070100c40e02140d00003d885604030f510030000b80c0e00d1620f40d4100c01d82880c0300d80408840d2401c041d4103203081580010065040b021183c0e04103c1c00c00c0008007118820800d040804028840f09942c41c007070b8102c000d02a04c0101d400c070398001e00380100700c0c0d102c1c0c000007400c11044102c086440141400e5070345005581d0f0003528440402d50041c4500d41080c441480240000c0303028800000d091405000183d030101416401000f5145829101d55000b00c81d1041c0315a1010145900181001d06440e0440032402690 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 649000863 1250 648999613 648999623
    0x10c0b150d230105012c130203010e060a06092003040f021c0c05270903090a0605040f080703031b08040e161e021b04020415090e07020a020603070e0a03 67
    0x40042c1c16912400c400c1c000203004181c00074801aa02c03131520f00085455082c02c0008400d0310003011101d480c0300c0b588141c01c43d185075851000714145800003030946829403424211500304005004510603948100c0b001082402e0040c07004a0050a0b224034410080740ca6180410000000800304000001f2600055074018140d00030140908811200350300e2149048503a808688000308052a001c0030700a5050b020143d40d6021610205031401d4100010b07060744c07040d100500154202d56588200000503100075981c0c2350310f480c40d200c01c01199803c66030080c1075640001c4000c1c00400e034810400c4c0380d00c01403a0104082c005042c9481c2ca4107100d650710900002c0c03404418042c40502600c00381c0715007112a924034800c1450000c0d0103040d1080e807581c902c0981e0004045450301b82a881c410002000010401414507076210100852241e0340d450380c00010b0365101080c0414524a00fa00341c00c044c03103100802a003a42c96022030003a00c405000e20007440000600850150b45004000c0080d40d440 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 649002113 1250 649000863 649000883
    0x10806060f0708031902030f04030c110a140307090908040303080705041d04030e04290307030b0a1521060e100c180501020f03031f0b0a09050906010c0b150d 69
    0x64107000071150805e45000c5420004000c1702040b8490328002c0c0da02840821400c540e040d21155401d981074201200103c0e01e83e0081000841e0316691107176580020580010700e00e4089810204060521520790014000613103400902e00100f00884103440c252a454248801984c41e5008252028080e40e40150140d610030000c00707059240d900002400355129071030f40f88100a01d40c08000a90f680c002842000350001c040003100c0343e540003403c3c1d05040c0c2c0682074dd100f00e0780f070361640f079140c0c501100c20b084e0254440c1e0074280b2000c01981600c00410a1981c60701d440c1000a2009941d41c10002c00905481c2d01c400c0c2d58203400405026540c4500c3d0003044c00c100014210001400043c074031082500303250000f240008095001249208251104201461855550207102c441e2000e201000d40840404503001080114506c0000d004e185010f88444000f907242104000702200018a15030411440d5050100003500c41080607400041c11000c60700443c0110000c511014400310016051440b8 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 649003363 1250 649002113 649002127
    0x180121020c0f071e0b19030f020d020c0705100503010b0904050406021204030306060e0402090102061602010b0a0e0126100e0c030304060302071b2106060b0a020f060709060c02010806060f 82
    0x51131410145489800446031035142c0c2c5030036a8030580201001e20002c0003130800c0b0042c01e580b00c0da10003110401b001c4801410f14100344065000c0343c2054840f20002d910200081c40103140202c1c00389110701030303458424907540c1010480d1690340208200170380103c2c0c542022408200c00790701a07481c00c0d044550095801c0c5014140203018025501c42c0001082c3c3d015195005810315000300c0b600c81da410b0f00100001e8944914011240f041c4002c8181155038441c41c5607419a51840341800803c20880003040e60350402c1d50001840070081a041821190342c80c115444000210300c11402d1449100b000485940044c5441c0c10840681c0e162a4540400100030402a030158040d050090180594080003183c0781c051071400d141900031460301609a060f00407030030b0100e01e00300282e503105503400b00c1da140d82c40140000f035030846882c0c0c901503005144100711002007004440c0d440b1001e4a030204020b40b030880c000e8003008021001030b04100710349000808030348415085560001010b080d203555412 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 649004613 1250 649003363 649003379
    0x60c0203210a05070f0e01050f0405090115080705091806030a08030106030e010614061c0b1c030f0c120c08190f1b03080f060d0b0903180121020c0f07 66
    0x3a00b1a014000c40307203418041101c492082d0600568800162112440c11100784015103040d000b00c4c5403040c10203002c200c0414151203c1815500a0200d100701d145245244817000c1c01080000340658100305091048010958a00b00340c000049001d20084100c0d848070300209090010106002e410004000300014056601d43c1c030614000361007100800441e6207a43c2c040c11040501307124194886414490100000c0c014120f0f41c010b907694102c0092200c03c60700226940c1c160360007020540750f040b060908181600015001403180e02450030f0103800041d607444000316045090316100304090382c1d16500400c4078601c21030b240d640c1c50041100c110f038006403000b00b00300ea076451030100148640203c4a90071289016508005905440f0300f8403ea507000214001020024841c6520080683d0000302058400000c0d81c0034a10700d1001d9681e84d580b1050031140e0420385c03001c4070304000c071545110880c0501c9504002482c0c1c041d401c0503030b8a1011541d840d03d02041a6494051750081c2040015580 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 649005863 1250 649004613 649004677
    0xa08060f0414180604050d1b0c03050601061b17130f03050607031b080703020711100804020f2202031005120703050c0d020f0f031006031b091503060c0203 68
    0x410010104074110390080308850320f413241030728014000e90000c442c411020f4006c6000c00030303900f044800410004144e8031800200b0403550b00c15501030b00108018002240e001c1880d4005004200d152141c8100f990f0f100f192003203020011001c0c81e5804101d410b070402400070100c0041200d912517440b01c40c1c03682807054551505a0722200030a107000c810030450100c2010081484000b42c03120700141c3d4440b84240c000c2d500c0035500300c9108010b510030501c1a134940e00700f04010a11641e5050862500340306011080c4050030440388030381c4c40386807030030700e0121100e41032844040e02d0003015850361134110021040181d1074006542c00f9840c0b401134004801d0015040c0c04490142040300c01d000068030600402008994002c0c1d0480802d50345000581805042080e0294029086034100507d0000742070485038190000c44040000340e00b940144540e03101102c014101d801d604000c0c40d040351304000945801031100070607681d100e40120320590300a04c1030b5104650302d601310030740340315034820382d41d00304 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 649007113 1250 649005863 649005871
    0x2f010212060f0d0201020a1719020d0314100614070b040b1009060302090f071106090d0e090c16030212030a0c031b0f052b05190504080a08060f0414 65
    0x1c441d003802000c001c1c03418400e20380e44944c041e006070800d9941c0b034403200713101140b40c031401e50f012504001d11501c1100d00014800900c0700760b4090010544a140300806558402000510450b4114140900142c4041c0c401040725010b04001c06e0141448024400c0d034001c0304c8014010305420b01c10841408040c4e050a441414201c051540c00c6403107240c15421560b55000c0039410140c03000004440d0b1498102c400d40003050750600d005003500300c5103000c1c03409100700d07110141d9030080c0ca0344480706d0750440e10b030300202001110220201d1901d03081c00c600728000c03541c0d459011204420300e042851300038484500c00340c5d460f050881e501d2501e9030454001d0311080c050000000e01d81ba400c07034418800303d000064aa1641d603241d040350305840004a03110b8002c10b0a614460407616040325a89222001d03500c0303d500401c00100d65443d1070050180340011003203000380c0190801c1c00300000600080c0c1181d10200300c07070070030f0743c0c80351201d9000c03c09032040c110025820520b040660035005202c81e903071a00c2 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 649008363 1250 649007113 649007119
    0x30b0a03210810030b0106051c1a1801080c0103020906130b041d040308070503071b121e0210181509020a140a0e0c09220f0c2f01021206 60
    0x7558503100050f5240070060b21020301503240110040c031010303110304024071441d141c10b20008101c00c0c0319002101106c143c581c074040c00340c5100b0703001031503401e081241159120000700210f030150f140c102c10b10346400c03030403c9142c1096400940c003030b000c2d038440c0d003a03a02e4040e0320042981341d00e8944440c21002d80c454000c0c039950040078002d01c221400803081440c0300c0d56043ea00c040c6c0d0707503c1c2c003d829580c41d000507001000717122a10340c04469001c1211a20711410703006100301d022101e08100050f00c042a40c21002071005240342800306113540004400040d01c0560700d00041103d80170441d04540c140403980103210801c81c00c442c0460008a030030440429000321494401c0325900e240c00890311000e1900180c02c4004810704100310401c1c24045940000d007029800e00c2c0441c0d5000040d48113401690070f0b1840444825146002041403050b180c004140c00000c00c04040b460101030000c049400041c8072400d03104140986280444150306002d05101000390b40340e001c0364200c50724041c000c85240340 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 649009613 1250 649008363 649008377
    0xc0609140402090102030a0c05030d020a030203100f030c06080921090a050402031e060f030a0510050609010f0902090d1b1a030402060f071704090c020f0f0d030b0a0321 74
    0x8481d01e814422100951816001946829618441a207500c0310841341545e10b0b01042c4001a01c1a95500081c044081946e80051313072850b00042640d0b120300280c2000d044101200342c02c2c000106618080401c2d10000e041900d42c2e5524079441d02e03d00600d40702d680b4820036420003180c0042c0f4140000c5c0c02980000c0720701d030603016260030511040307000480b80d50041103152015248014451140ca070340006020340b2500f42602d1600110b450304400300030480d0300d0741c4000c0b000e44220156210303036078221100b180c1000c595403400801250054030340c000e06001c1c990015200d030ba150f845001751811542d203c0c500d030115103e20a070800495516124035410301c074900381c0d00c01540c0d8001044034030580d0300600050074140905460b982a81041d0303811910302e80707441c24103000d000300c4401810080c070122a0120b0804100c000c001e007061201131000c5260b6210107000940c0c050302007800c100b4201c503454005280d41c00200054000500c42c1d001a00304000c011001c002c6101c042d107020b400c1545522189 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 649010863 1250 649009613 649009649
    0x9050117070e0d02130203010b070b010b0a0c140c13020301060311040b0d050c07080d0b04061202091609030c140f03070b27030d020c10021b090903070c0609 69
    0x10000200403101e000000b070140c042c6030780500d0070b0340d6403050550010742514040c2c441c00000320b04036802a00480310503c0c0215800040291b001002030141204510090405501d44000740c4501c030481001028010003403081c1c2c410760030800c076041e82e01170001c01d081417986d011501d80000398400c0c012000042d040c5a05140101560f4040701e04441446003034a00c3d0a401040a4004000240c10050784401c100421004903007141b001d006107402070900000c840321540304100c11248198851050180c81509000150f601c100b962039201d10a400d05071580d81c0400320448000c40c0135003000b0440340900401003158003174000c100d2030980e0141c0c2d141c0312011203041019515051031041d2010350008101040310b508010207040b03600c0114584408000c507040c1e00107410101c4a058000043c4e020b02c0301a0707000d2510080303110201c005070003d04500c96159080d040302c01001e02c803043c0588a200003003980700c1010401c60b007003203401c64911801c26849040084c803030001481140011440050740e2 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 649012113 1250 649010863 649010897
    0x9091e1506170c040213120516211b050d06090c061b06020a0c02040f0f0510080304141801030f0b010501260711010f021312080405060304050a0c06090501 68
    0xb99610703080c034000511101c0c20f42c200b080043c0d40110000700c030b24282d4400002d480303600a072600051174172030320191a41041d80c00185241098030b901c803c41000d41c3e0b42a21000b011000c0e6501801c5400c40000c12000a01441d1800355591a40c00541c02013040b0583e4130620907290b020403601403080d1341c1045125500d0f07908541c0c0c07080070748800d8a0003101c2d11140d000549164010902c074081404c10204074144c940004007114507928202d0135140d02d13003200841e15081d034800d543e441140140007a002504040340705542e80640d00501914550000d42d40c0340355030300c072505c1c0c3c000450b414600d02802d6840707185c10204081d012034102c0718007211000128082d03024610b901c88050325140354501040c0b404007080c0754144064014420310442d00011a007030303c004c1c01b840e908140b0240025a58021003540032201c942c043c0d02050200c0048010100042d07416000c07a0101d54089503040e4a81d00d4504101d0b0600c460071800504419240038000b840c990001350711000c03503a098032000c003180c1e514542 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 649013363 1250 649012113 649012139
    0xe0c03070f050d060b1603120618020702040f020c01020918070e090403201e031c05060a0b1201060e03010509120309030c011406040b030a050709091e1506 68
    0xd40c1010910505180c1c6a052041e000341100b40b4500c400801c1e0185d480b8441c0015521400c0e01c04600030081c2c100500303058018945014081100004000e09032038886012010413400e81d82d043c686800181d02c0c4159541c1c1d401c226000d494800d001c650345c0c2e0303d040301c1c24001c2d40300803440d07030207444c3d04440f220b030301c02501d074625104200b00c2c1c0311510300055400c00c0001880c0010012800c0c17040445408616101c881540030070031003c2001010400071110b0319110340c0048602c2c501007588100001302e10081c950000c090103512840f404142a102da030300003032140b81d40780c00000c10704002140f14159040c003000c12504a5100d502c41240e060011014903003070398421511000301d548518524a100030600c0000d65001e50054181d90401c003c601c042030958032503100c40040b203504001444941d1900d403150f02d01404084000b010180255642c01da181c0b04507228a191095440703450a0034041310702d065401811221070010503034100c914003041071010b01522140c03a5031900d00080380782080250 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 649014613 1250 649013363 649013371
    0x81605091f0e03030711040f0212070c02030c06070807150e0f0a02090a060e060d030302211e012103050403060e0a1502040803040e06030c030708100c1e030c030e0d03060e0c03 77
    0x981111b03554002e100303010180504008aa41c040d508004002c14160300c03840c40b90141c140c9a0754888021b40d2401054501145000105d00c1880100030840004202c103003290040c503440180310030610f2000c40300380c005040c1c04100300114051200e0b2000702160200e401c82c0c100e48200c40d07507103007a00d0303001c0d1000c110b58541c0109142000c842011814030320784a20389821423413003850f0261502c41c2c1e81000c61126034480300c030f01041060a0091000d1150100300d03000201121600b808070320b6141003a642c3c071181d50710022040d045c0c3c21103000820b2500ca01c080360050742c1c010b042440b41c0310442c403410740e9900074510241c500c85c1c41d82d1fa0902100704680219011150080000c600301070800f11560040300024103102d5161003140d41020264405021410081040b240907000c0000d42502040039500503541a10801040719081d080d80d0059601d01c50320030b980362500154003070320304078103500511a112001040d0b108a000c2d04000c0c5505422500c00d44004002d2a601511003901400c09800251 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 649015863 1250 649014613 649014623
    0x15011d060a09020702151803061803071e06050c0414040e100c090e0c0702130b010c170c0609070f120b0612071203050a03140403081605091f0e030307 66
    0x540030010002d464001e8050940000c002032502c401605500b0542d901180601d5030801900018001a2400b800300583c0139400c0030b0b541a00280c0180960341b05d10440c4402801401e1103805c0010384c0e420500001c82050f88030004008030b081c82c1915100e9600035120f441e2541d0401140750358241068052501003801c01c40003015131032200c20f620300203031000d0480842000707000b43c0001381007101c12038183c0c054140301e9500344d59100d02e80140000005100c0182503a0360901e00020796699000038911032040d0403000c80c2e07000c9080c2110101c1a4411840c0410862203030740140701510f0710100303101d0208c0e070070b2861200c891580c50440e201c126003180009020311020000103030490900c255044080030090b030541d10304c551034409083d08140b000d907055001030008914509019014428400c2c481c0391a030f0f54912600c0d042d0780c000c2c5101001410480035610302c0f411301061a01030416101c00f500001c00014888008450f61108002181c232000c0020304d6003070b030700c0031103003001700440d15003075001 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 649017113 1250 649015863 649015879
    0x14011e1d06160e03150f0f1b0d020c030315031606140307020f0a0308270a12020c0307060e03010f1b03020a05040b0409021201170d2015011d06 63
    0x14004001203250900e180105104080070705038060b0394148066801d40c17a190303c410380d0a06008904460044004099200d0010b0700001e01c91604411a003400120014130324080e503c82c2c1200c4004068020071010003094880030052244102d070b40c0d010080ca9041c2070f8100d900c1500c6261810785490094400c04c00071501600b214182180d5640007580c0c0701c1c00c240111a102c0c00c44240491901c0f841e00030640c0040e00d19020b000f920560701c080440d08c51120701c81c180e1070307826110000d5125032008400501c84440d004851101c81c3c02401210030340103005041e50201ca50350355015000d100307994686072081d4a0101c0d00248980548942c1c060100c4030715074070054008c2840150020741c0040305240a11000b8040000c04000b840003c00c082c0c41d41c0c45015840c0d507c41794041181800c10b80107071191641440890603200000200d0050048891a25002c0ca03084000d00b0030161001035154403080c0140402070209400b9041c0d498102c525203001240b280038941d004101d811800e681e010703841201 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 649018363 1250 649017113 649017121
    0x30114100824060c1c02070501030902060a180e160e0604080d080a06030605011211030a02030c04021c052706010303020606040c050c0607030e01200708030414011e1d06 74
    0x300024400e100d00020303012138a4510103581d03d52401c4c04000e2009181185c000d029070340c95a0501069004117400c3c00d0501c440070f0294001040f40c004c000c01035042000000c404a0480981c420710402003203c1c101c222010708000d00340380c0d0110784d8803080c140811009504195242000340845d403c035584000a0650000321030012036035450080e103898070b134030344541e404004207250b40308440c02071009000803500e0070181e1400b0900380840c600f80c24030a4210242d1100035890100381c1c2602c0c0001220010b075101014404502c40f45d8550004982082ca05001c00401d0803c2d110084a190486d0b805000c0034002c40b040b10b079642e6003d0000030010307082440810254140364005103100030582c01c2541c10304041030900361610508039415000241c1315107210282007003c0c03140c151646600000b00f03000f04c0e007400603401248a0081c0041460030000300283c28440000d05100c4545450002070010b654200d69034418801c0442d1900d041c1c0d89441401e0911649014030242c01500d50406080300b507403 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 649019613 1250 649018363 649018411
    0x17010e060402160501151701150b03060d0b090d1b0f020f130e0c090a1a0f032d01060603050f04020907030b18190b031c03060302060301141008 63
    0x201d00342c14541c40a80c0c243c03990000302c003801240c040c5900021020b088900d45101d120b66555400000c03115640341c4500c903003c3c84a50030701581550b994039007850303480d20791030040741001189100c050140c500074800e0104181d40450352141c1c00c00319540d01000b405c000c000310801804000c2000341004000c2281c00c0040c10102c040100f0150000c2802c440701000c070140601b42d0300044440380742c030741204030308402510f4414800d9401001c107040030041c0d007100301b17000c08820590b0032865101c2c4107a052103440650b000c0000b8440480c03204c0b041d141f5403513075404140c0c903004000c0d10504035500b44100420820b22030300c5010721481a103075528907a612103409014034100e02506e00c00406460707000382200d94a4520400440c501e4452429400d481c3c1484104403140030000904491410441c1c600c44542d07002070a01c64107040c8061450008019a500390014a41540000d4009502000014a20040720082c802420003600e582e05125443c541c2103400c10720840da1143d2540b50041c95011141d = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 649020863 1250 649019613 649019617
    0x1030e15040204020409020403030c0b100815040f12180915140d0c120203011a060717040806010303030903030e0a0c1202060f0c160e071e0c1401020a17010e060402 72
    0x1e800588018a0591281d005105a0307205d5003066001c100000c900074100440d50000540c040d0a440010424604143c41c59844003000000c42c500c10442001003401c2c481c030942e102210b1544849140f000c10b0201c1e0b409008206160684040042281400280c0000c02d0107842070060b01d62100500c003070f0402c9001c4182c010a140000d07084100d500d07281300054100702c3c040001c1c01c51001c0030300d01c030f05072031040600f900d00105190840d00c444128444940d01c40324181c6000c00e50000b140c22811285000044046c042d40e80022064459540008103060300365010700c984c0d40c081e80d414020004440c000e50b0f540c164105008010b640381400802c00c00f00c0454150034401d1008060501d407070020f1100080381d4112a4681d4056048a20008510314a0b52810310081988100d9494180f034100d0740036010036840c0c40456010f4441c05198440c191040c4024104d80c0d9000d04c200d4100b84803507520500035000301030000046101c40c480a01403000c0021028102c84122511600035547d103802d200185d = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 649022113 1250 649020863 649020871
    0xb060909150708060f0607050c210118062a110114011d090607080402041d1f06050105090f0607170c0a050d0503090303060906010e1002150601030e15 66
    0x18010348041d42280e00c00105141d0160b0081e0f950210765007000d1040001c40d032200d0001504c02c420410400e40065000704980b0085201100d165480d4200020300c1d0b010500405520030780d5500c2d10880d00444014600d01e250505d00070041004a08080070f41c0032100000003c1c02c1800707040e4000703e040b00620036105805207001910011541812440810000303410a070400c00b89030349400c41708000041ca150341640e12403446001041a803c005101605001d406040640141c2d03c5032100d06040003540f03112030b4030b645241c2c102c1e90701c00e03107800c4014115110b1500342c0c202d2500b44440004c80c0e61040e4262840711200500d00c1e807040004030100039281c0d21255080f244500f840d000c11801070882405810868000809003041c1500c62400750b0504070005502c80074000705000740640301c0c5c0000152503020303506889880b00c80e1141001030f62841072118025a0042c5940900c10b1a29030216a54407084140042c10b4540d869040041d816200d58082031042680034000c5015200295075400b500 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 649023363 1250 649022113 649022131
    0x2102010302042111010804030c0b0405070e010e0414010c17101a071101050a08040b060d060507090e1812130510320906090102010b0a14010810030b0609 67
    0x82d0030307681c21040740410407410058a1003610b8030048000e102041d8840e585126091800d10120b1800303a801405451815601400c8099000002410090100804800340c9000b05c06503d003076a5440e00c00403841400c0390b0448190701100300e8a0b01c0f000d4140030311003005480ea200c07403106030381c004459414000e00512138528032044041c002050000b81110300d60703118150301c4550750355219083c003810551b5a0a00d141c10420100048c2c1c7d1807580c008001034009a01c408040c8568030348100050400308105405418071f440c18040c0020241c210400070102c1d00040550347e01c0e5950452030b458240e90118100e0b0701a0403411401000c40300040040c40d0302410050314821aa03190008651031518086041000c200c444450641d2204412400c0d0004100c16203c2c9003d11030702d121040f194021182903900522000c1200b0469030b00070341064245c0d41001e01140503082d80c5003d10005042407500b0140810110404518840594001e003004d580d00700d4034022280d1520b40902203004402000d8000e = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 649024613 1250 649023363 649023367
    0x3020102040302040911030d05030f0c07020f19080d0509100503090a0f030906080c070c03020f0604050405040f11090c07020d03050c010f0f110a1d060f1605010f062102010302 77
    0x10040ea0fa40c0f0411807542d00406403a004130a0b1b132002e0502e4540ea002c0140c090040500810111520024041d54001e15820201da240e18092001c03c407000000951507910040c40c0c00e411170100b54604824003290006c00c21104208000c1600b07030750300c1c41040b144c2c90304a004041c004240034082c500039074020b040c42003110b035030903481e4840d00340c4d03d00554421000100514010840e0b168417160301a0030840ca01310440c80c0a8007903450382090801444002d0107200d09883e002d000740d860741d0a803401860043e00902107440c16113401680f100700002d044845000c00b01c140c60190400003062071050322690046440d006658081201000800c00200c08001d000c010345004160f080c001e40389880301100700800c410103854180025282001d00d44010304806021800b141c1798000060b00660581c04441e00704881c3d020082065803013040482c907000e54001981c60a80c00c4c000d60a4540f4a0042c0001c02100c4a03440000d81078a0542c4034000c41000680d43c048003d8bd1506084c004a0f0300c1410018 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 649025863 1250 649024613 649024619
    0x20304290417011d030702090709080f0c12010501180f020d1d010c020303071403220807060b0105090f0f18100e01090606140a03020c2d0c03190302010204 68
    0x980581c000c0d04601681040401120b80409090040180021010a104800f19004032080760780e40075151010380f150840c0e4000c03c46150007450104c0107814640241d0307004500e6400203d5171050400202c60081780c14a6003c00c4405062080ba4183c07040b01400d92451500801e02e80d01401400c40c150800c543d08001094070394206119400c04040c8216036100b100d0b014200c0b0301e00b1a12110400c00964004004101116a000c21860004c803084000c130754803a141e0030118006c07900c4101c0903c1c87c0310100c00401081c0103682001e00034951240000344a00c018490046602d40101e8141c29080003800d0204580d07458841d585a010000240260941c441d450082501a0405031141c403001c487c1d40300c05012041c1d4000782a409403143d00818040d2601d040001864210400245c841e610000b14007101d2062298044592a0084400311103608040e1354184c00d1030000a02500070407001804103040c81e560100b2a000f0030280203001c1d01030104211191140c6403503189007201195801c12005c = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 649027113 1250 649025863 649025939
    0x92b0804080c01020c07030609202d192d060e24041802070c06080c0f0f03010e01091b08100e0a060302011803050a11011202280f020304 60
    0x448015402340c3c002143e026580d06003002800150031524040c000003249500d100e4407808009915458034041c0c204403a070361145900d442450b00d400b0182e21020401505401c610384c64080015600205104881d04803101006c41c2148410820001e110310041030800025014080d11440f152000c0d10760314285568203565280c4a845204c03007030b03241602040c180b04940e200c045400a04a14030011854030180d5100c49000502903c01c000c00c00c00000001541c01e104002a03940f1f0381a007180c219101d4200755010105a00240512104003441000000d4402030030f001e0000700c40030210b14080c441d03503018811111040010030241d00c40741c001c00001880307184084034034801d910b80c8000045150951000600001c8280030380c40c0480c1e40c0c8002400464070200d0302080c410f90104183c07640608400042e903458240d2031203001000d20200d00241c800920240842e2030380e0b00300403440304903041b251040e1202141901d8210060b44188802c0c00800c144100349407200d1074010200c070102620040d4 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 649028363 1250 649027113 649027123
    0x10e07050d0605033703080a05151e01080f160e06160302010915110313031b0b061807020d110102092812020f04021c05092b0804080c01020c 62
    0x295070000d40017641120101e0310311020802d2050340d24504401407141a10001c00000e0041e1031102e1185c1c1e20804145a980d170b041400d2030b90070740900010315034a00c103030030343c1c62409803010101d012844c0840002c1e42c03010120101d52054080e1403a002100118000c100c603142080100c15400030002c01c801600628041000e4026600c00c1e400403500c0412071404136204500030041501350750400c101a48009414000d50b94003030707030406003d0b00f91002414100e4070511054016154100512115414442000e010504c03c0d1000c0c0c4008000c005040e41201507010200c4000c40182c200800f142d210300c3c8106055000c0d1540070740054104499000000c4000440744400c0503004131088a40c0e25058035104148014600c00782c10502c80c1445402044d8801c12059035107200d241d000030b074614608061171559000c4d1001d84000c00013494144140c075918403e44041d040c1040f019418010321414914440c0c00701305203590f0f0038409072075a40d14071009030000c580011055400b031020021070a81040 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 649029613 1250 649028363 649028383
    0x1803030c0a21050a0c0606030804150f080903090d050f03040603020306010f0203090604030f210f02100605240712050414010302092101110c0303100e010e07050d060503 74
    0x2016040308a002c0c07502040706001254441c00c0310582001c10107100350882d041c0d5140c4a0326081000c4100003525040700103103510382005083c0741c2d01140103d103882e0001c0b10708144030303a00e44807100c00340b48107103003603448800880e03a91616a008021039138160410151714070200748602c04039030070201200e58844c215002600010002a804001c200c143d40c1d10031100c0c1d6a401d0940080c500d802d50036004660248240c1c003001c1d08034400201c3c0314082204150809140400d80b400408045031268002001d1020140068006101c1c030b8280910b1a03406100746011190020140881d1281c000701c5040c1c006450304508d00411401d016042c007081c074589049290510304d55540c0c3d922070408540180042c2155200f604140c814080700e0780036141d85402805c02d0035060415040203140c58047c60151a144030000b03803801020605648540c0c0000180d8003401c1c000e0104c40c0001c0e168030f4403a61240c024801c070380c8d020781d0ba00b0224000324020030041c04003034007040e00032400c2d076180c00c0460f107031160402c = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 649030863 1250 649029613 649029637
    0x60c0102030a0e01050c070b0106031d03180f06160209040809030a0c050a0b0324060d0c0804060b0306070c15150e040209221e0f030801030c0503070b0a0302180303 72
    0x34140343c94801d0284030b01d039072001641c100d25003000da00361903201c0700010500640c2c050503030303c0340717811260f0010b800003c1100d60100100c2e5070710031004803d81c3c0d030103401e06034580c002d15a500d001070040c80c2040c155440710440d140070300c0680802c0d13000c000c02310724090000d54a40404000f041e050307071014000e0403010f50082141801c458508024450f81760003d80c801d14441000b4000d1280d0740f2640b650216242041600010325180b5060004006100348040d02159520b8412600d0503150424446842980a540e04002440c11101810340314041216030748002030b8522503440c00030380c04099044100c584107030300080c107500120250b0f910141d180c1042210b00c410900b00b00452400d0342401e9404028030802c5113500c0800d10320b4198000c44000020405c170070301000d48aa6408640d000a80a5002000c0c0307c0031036224100a4040b03202030106903a118100030000c201070400140c000b0441e0400c082e01440e00801c034908a00070f4004603400e541c8400b41ca214180107980800c050241c1d00241 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 649032113 1250 649030863 649030871
    0x140d0b1c0803041118131505100807050d0209040f030504181b02010e0d0c0f150c0908012f0c0601180c140307050304050718091e021509060c0102030a 66
    0x160814014455440301510320640e408140d0300c4c0400d40e00796115401566150729928180306078031f01400c80c81000010440200c0c030f03000400981c0d01c8980041c10803603074983c081c1d13000551514207000d90321144000c00384d00141b00703101140000e201e0381341000784940a440c109041a446a20060507005030380f2038800340c59154901d92103883c00c0c85101c600402d00c41e000130403031400e0b038610442e19490040700c56818040d131401d078001404100c0c2c41c4183d07600d034401c525002103020309150000400074003c0341800107000c500c0c0030a03c01c07014815903030101802004041c050342070044070548000c80d04c0340b11004003400d210f0240714110401180380079040304109072040303c9e48078020b0320480d0780c014005010000300914200704884000c0c1147d0300410b41d403802d0344d80d0343d5503801d02c40c0c41c14505500036000110400702c01ca040340400d900c41c3c41014450106446607075012030503018030001412010798004000c203035041d0482ca445d0001e00740c1e000c0c041c3c03105003840415080c0600f26001259240ca81c42d4903 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 649033363 1250 649032113 649032121
    0x507060207260c24071b170c0907031103040308010e1003031e0912050f100209011b1506270c0f050c0106050604120302010606140d0b1c0803 62
    0x2102041d00602c41444103903004074500840500c1c0da628566810902962004e05020380c4101c80100141c000600300d400d4680e9550149004410a8400301c2d515200e0f2000503c046101903042c1a07c1d0505c4e111600145044909a01007203854074014116005241c1d60301400350101d0021780103180310303d002e80c4495030715600d4000c1c1c40c0c2d808500100342c1203194020410030300000c1e400094030700002000b29400341c982030501c001683c1440709504039041c0e404003280d180003042000524581c210303485c202618400c0c000061008107a00a000d03d00d804204034900340700c0c0c40700380d02500c04002801002049005501e0140a908480e9035070008280b0405080b420501c00d28410740414514501120070448000d4500c0001d1413040100340754801c0010004222a02030000d410441c0030f000000d0131981c1c0c0310758a0070888a01e840c911812400755082c81000910309016040341d00008104200140c5408424508540100745507420281d101d0001404418441c00016513100201c0c8104c040710f42e0703414 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 649034613 1250 649033363 649033379
    0x30506011806020304030303050c090303030903040317070b04080904090c0902070309080c010509221a03210a0c150903090302030f06040c052709071a090306040305160507060207 78
    0x11241c40c0c0c400c039401c588504104803540007044508883c4c2624001559880c2c405803414988034500387c40d0391500c008001d105c054040840244200c034411a440144003081a4245400c0c1c0995103015004501c07082c00200480c110314024901c0140040000815401a0b0b03110310b80580150060402d01e940440c482d0708043d0040c200c00c001c0c090100007090b8000001000a00034410030b040c2500500317003400030400e084812255218400c41c0ca91041c4a403005080c1c0904007800c0c0d48515512a110320032119544d8600c1040d00d40e074602c070f141c00c071030f00c0c1511b0158151925001180c1c1101d1121850403d035041c4401403280741080f078842c1e41d0782d1410381e04d580101480e1600c4540b12201c01c0d0004014400040d144591075800c41713900b9694920350071300c804184420f24070b401c10200025004801001078604001c101042526203003450781c0310f22140344d8100401400364160355030301030340102c0109021038051170213803004e02141030603160040102c1da241e50038041c0b580d00c1507025070b0005c202440b00301 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 649035863 1250 649034613 649034627
    0x60312090812030c09060408010e03030403031d0606040b010207050909100509030f09100905040f050415020f0f0c0a14150109050c0a110309120c030d0c020310050702030909010603050601 82
    0x710815004000401800c0d09281c101c0c403024001064281c0c0000b4100c081d621224151001004003600800130300008c00891902d990045504500203451b01d401c1c49040d00c442c0d4140c450038002100105410394808090000400250940c44c0c10352050140000d459507030302200900c40c1e201c0d82c010300855140300b1440420748402810750959500240014241c1d044100140d4079440011940100e041d4280c0006036054480e6811240d00681001c418860b142045c0e040315014921a03004120417100c108a068100c0c065640c1524042030304006401e5103140482c0030f80000b5008200355500700c3c400e40d50380700481844039803540594008209800000010503009401400c51101c140298030f003450a01c0c0c014030482d0702600070300549402980304294200280c1d00d14010280014880700a80c0b140c4644e11b02c80c1581e00c0340b0a00c24034081c505243d11440044002d50360140c02400c0700038490401030041c0c20b009211100310b1100340410b400940d20708443c41d000b00501d880008880c180040014921 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 649037113 1250 649035863 649035869
    0xa0902180117040b06040912020102030702070e0601020a060e190506190902010503161e02071715010e09011806050708100b0414010e13020903071211010c0305090406031209 76
    0x2c8000340400d030200d485442149a0301c40c0d804112640721396200d100040c01492011400b07025103078002801c090291301580254042e10380f68003120002e503070310401001081011140b03640140c101c06200c1e030004800e50000034500c60100b0a44a43e165081403048000c07545910540d900e60225040c040c04183d44c0303205916013440160b0501c41c01a40740c00182c0f1901c00a0000d450700b1002c40d030020700891041080d004442a1440180341045010390001c0d9100b10500640161000550440c010b440001809041c290354035000024160701e410070554080307000401402c025500c401c161450304805511950344148142800216810b208500600c05040205070030341420b5035010501c0103411003415038049803907002d481c0031484001d60041724000f4000000c55084048040c0c01280c0c001d4503006480210300035070450f00c107640d440c0541c0508450f41c03040900001101000342265502c205d030003c10550203401e01618100320900480c0480781641d00650f2101c200c803440c0d00c41958480030301001 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 649038363 1250 649037113 649037117
    0x60b0304051e0f1c0201090501060f06030f05091902150d020d0c020a051203180303040507080115030305090f0a03150b040c0507150c020a020904060c20060601030f0b0a09021801 78
    0x1000f8489521940d868070701d20306010341c1d072488020908250340300750410380c0c0700740d0701c40000d008881c5e030351900d440c689a0381d01500011908140d004941c042c1c5071304c1510312500c2c40300020030f015074262011211800d000c40c8141e030080030000708071000c04038a8004010260103528010303030751640b003a0a001120300b071003c0780c406c540090f44560049a4001469010401344554440d83d03511100b4090711202c1c000481415940004070420042c00b0780440c41108542d038400c000c3c03100f0411348075440100403107804028041542446402860308010310070840a07400900300c42d80150b00c0b03496a40300c001c0d83c07207050740385203032101603095040c2401d0044c50010b1009080c01418540141d50f094440c520401c0d050004035030381d04a501710a407003040001c1c04642c001d002513881d4181800c0c41e201070004018180301198400c02d540c084485151054103103c52814043e0602d601e40000441c00780020081100e0503a0311950515102d40d2050307001c2000344800d01005035900424684c21152580c000c101d181 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 649039613 1250 649038363 649038373
    0x170d0315050609040509011d160f0b1207051c0902010306090605060d0e101b090f0b18031e1501090b0a27021303032007090f060b0304051e 61
    0x1c09a114401a214030741000c941c042001c0c0d666034a05401040c1c201c00d25041c0c80380c40000291044c41c0412041800c171041c42e039540c261034807402c49119644840c41266041e050402c00901c090707080c1000030b90081103d02c0d0407441c00a00c0554000c503841940115600c040c0d8514105c4119a094480c000c010101243c0601c04180342000050090145ca41036033480e41d2140a900c4000ea024010360405116040041000e10441c1c81104110070a5202000100703100f9030011803916011881d4070104c0e11000d410902d44840d250f0700020071482e85901e0368140c4120f08070540582e002d002c2c5207607218503000c01400d43d06a040c201c15007401040e030104000782e20700300042d203494440740001c0d0150b03a0000100810040c4607060101c0080712106000c80e00c51002c90f50b415501c1010700c5000440b8000d40d41c8800100440c6480d440003134240c11541180ea03c5001c0030404146140c0280c0c0c14144098400940d0640d0f5000d10560b55104450845464001a0124450203001a1008c249601c0c03e80100 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 649040863 1250 649039613 649039619
    0x21509030a1404090501060c050d03090203030304063909090504020a0302091f03080301030b060105090a1a0f03090705090c0a050306210307150b010c0506041b170d0315 74
    0x16200d101d008041010000b003825481c04194400382220010716007400c082146682d6000c00525481886c3d6003118503000d94410850018030a019040c0310316001009145161529a1034500038080502d01c4c001103001a440100580404072039101c0305443c1840c24003000c984c6071001000030307000e03400c505000ca01e00000d000260301d5814219003560780c1552040d040d91181600624000081b206400f904004101c0c0803082000036800f8604070380c880c03000341c1f10700c0e01c481d070056460780601031130150094903040c0204100e0403103c1c0c10032031716124002031629000c10000015010b5200302d070b01e00942d52200714204103030b050401c2e4440d401403a1380031050611f41325120040880c400134019500c1003001c0702803103903044d050701851900500a0000c80ea40d88c001c500c1c0c807500702c10900100e05107540c5000c4035a95254010b40d1150302070765000001d802c041e43c455803a00303e0b42800320b1442c4401101c205002c2141c1074140703000d0099130000002800078415043c4010259001130710145403188034050700f0 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 649042113 1250 649040863 649040881
    0x1201090204050919060906021b0c04110f07020d1514040b01050307050d060f061d060102061f091802060313050705030a20040f020f18030d0f08190c0f0215 68
    0x4c50350b0300c92404141c101840c10014040c0c0500c07102000111040c00304101c1c41e201c001004803824009581c18851040c010280803400d0040c105260600b56080118100600c0c007801d101485c50710608070b000d1880e490709040c0e070807556985041388003107000900f480b00780003400c1040b0380104011030040034080d041c940805c0100b20700000007003250fa140e004800303125000d0f030002070140500400d0b06481304003040c929404600140e507200e015004101c0480d004504940040c0c40c0d0039125044d03110081c0c645010b0360010510004591100c4520140a000503515900198003d10b054121070540b4a07490a000303040445e5540b1251107640004810000611011041410407130514800d0150100c6003012034082d10050320141031083c40015091013640300e00000d01040040003d00c40412009607003030680e03510484003c0c0020803540081701c0c1740103200360040780d0300040e081c2c41342c090b15004a05d001d041e40c95032f0030318801180c80c41500e1300c0070981c100107010341a5209400c80d03456081c06184 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 649043363 1250 649042113 649042153
    0xd0501080c0102030f0d06030506070819050103021026090303010305070b161e050106030804171501050f0d120305042108061228030f0203041406071112010902040509 73
    0x219440c20300115031b40302d0407a010b034415001160420161101071a100700001c0c1014400ca0303045c5884980320200d100c144120340700b140d050340d0f405090b0f0300c020420a00142c41420324900083d820b203410642d00883d541c801060180200c00c210011610b075419850007034201600740d00142161607061140b00c44640400d61000485500a4040040d10030740e002c016050304040c0001034107030340c01d089000041101d01001402140e00303e00305a80c0c519100e4510b0307030701d814652200f2034804510400602492820984040c03da18000b4003148007a600c581d40c03403501031000e4400301d0100f95604100402d01c008076000e88108001e4001c0c14000401100002e08021400f0704244d00421502c040000f0380c0c64104620b84640c2c007142c801a8001d200b16280071040450354404074001550a00503440044c00002510f09440f04020912940a190400c1c40b503250400341c02074800030440d00784001d4648035842005200140c600000c15421118010f0006550307011341822031035844651141740340034124074 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 649044613 1250 649043363 649043377
    0x1b032109060f010e0402061b0c01140408060a0e0106120605040516030f2a0e100f0312050a03020909040b0a0b061303060b18011d0c0406090302010c0f15020d0501080c010203 76
    0x800507580f5101c0d400840c1e008d0040d00c0031190001810003ea80e01000001003d07001c2d000b01340d846c000000c0a05140005500561140254503408200032030707170b0b60b0003942208071101008000002c0345c66440d11321b8030031481c00d0b40050391210b54800c184018040103209c5030001c0601c03514034001c005e1441d59802c040b208550406801240410288810f8041c2d585001410100c5030740744102140d1100088d0302150300944000d0002c2640c56000507100c0300008981c8200c03908202c6000500108800603242a03000300c117081d040507401c02c10040075665075024540140e000f15002c4c4818500441040112084042000d100b00000c0c4441c1040003075640200701075a9100001150722004180402c095503ca400c81e60040131410300003003144d8039041c60302040e44c4c100041000090b00c40d1080c0c00200d01c00c50054500060b402c640500255000300c00408071a48101316040c00f020380c41d00c9180c01c83e500c00e2541070748103400207120b064100142c000e09024103001e4028000a18140c40003035600d100e442 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 649045863 1250 649044613 649044629
    0x9111908121602190e010b091e0105041e0803030a050109051e0a0c0c020301020304060507081003050c0607030513081b010206011409091903051213020f061b032109060f01 75
    0x81540700514040504e0010038240807103000d60358417400b118410341c00440e4a180141001c201e0110700e8903110034400340c041c4042c1c4034507240a0805141e6980d0549807440c0e903000c0541311100040b60001080110f1050200a0300006c065042420f02019600098039108116a5043d002213112482410389030300103000c21800a86881110000d885448100d1030296042d4404000c10061015540015124001950350303040c07659142e40d15070244905900010f001ca074004515000c240c1800740c000d1100d2802814428140007000d468103000c0f902e660800d89458100158880b108140c03407007000c10541007400a0b01d15981813501e04404d803040020ba242c8216800c0c40860b0683c1350511010035010031021881402e41c1c810b04001d0300e558004078a154034044443c0000c0d00e00410b58094802c143da005003640d409918840c20070009401c9000c1000003114610300c0d40700d51080401c010280703c01845c1040811010108010000a400800902c0103422010402440d6840002d007541550210 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 649047113 1250 649045863 649045879
    0x6080607080f0a0908040b19180e0402040207050d020c01180303080f0c07050f0322030201080f0c090d0c050a06050c0304060c050a060c08090c03011109010309111908121602 76
    0x10550744041d0084e2800644032080014000c01c0444901c4024080b5103404031b10030b051001d0081d0200c0703120041c00d0b042444080700b00707020b05c0344071a14109250094001040541400501c1e21171900700212004001d000d43c0c050400c6e003640e941c011040a4040d045800d50f41c02c12813543d20060800c0c0c40042c1342c0796844042d0303c0010104030004d025034146a4020080314a03895150141e40c1d42e030b9101e40d2140c08031503006010442c007041c01140460683e80d040e5588229503c400300701d414034800c098454004200e042c0040d01440e16042c003402d9003980a4030070041e80078039007402d100340340019800c05010010200305403178141d0400003c6504496951500d8401c0c2c5032103061090410b4100c6070010101e0741004124448181d0103080f50303000303408050070782ea40d040b003030410507088420740c15070b844c0c490138240542c0c2d21a601a078002c02205008010200c180340d03032a0000b078005150a90b440e045510f0540c01441111401c020803c0090b0790010349070b10700101a251403240c0b48001400074460184 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 649048363 1250 649047113 649047121
    0x3091c0c031a09190804030803100e0c070201030f060303021908041505030726010603110f0325030e060103060e03120c0408010b0406030b06120f060a050a06080607080f 74
    0x25040a0000a5400071204521110110b0309442140010348200c80c080c03184903450320f2800c15165042824662001603030b482c0518580c0c4400ca1500020403501d0076038030306100054000e40b074000c1503202d886c2c540441c070754501c03480c80007501f1a04409034032000711b890250300f400000d070000f0f00c1010765214080152441c400a01c0c19500510403a00100d914802c1050307443c103c25048800765008921a40b40c0044514020f409006000441c40000303030b10103030b203d00400000340250300811141d8170080b2030a1a0001c07100c260105540b003540c030056030908000007240e0000c043e420700d1a10101500e01482800c80e48490079a5174081030202415042d92060314102005e4100203c03800fa54000000f03400600d01039542c804203400038480c3c40c0d519420507044660603d01842810207880d8810360360409a142c250038001051101002118076100303034481e00300d500c0c00402001e440f43d504001c001c5000d1600c0300020090369920303070060b11581c1c810703000e006480da00410181d40c0711070a000f10a0f51681c07 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 649049613 1250 649048363 649048373
    0x7080f19020724240303080c0712090e06011110020a1701030c06090f0e04060507050c0613020307080115120c120b010807060804030c060b041107030c050c01020309031f110d0b03070803091c 83
    0x303e501d0000b08030ac1c0800501030305c059004418442100c0200b2001c00103513641100664084202c90030820240c2c10000d240d03000e5038072640c05840b110289140502c801001c070314038540b030501c01380c01c1510001d80c4920304001c1158030070042c0025012a8034084403044c030f043c91203203001c24050801002ca585450000c2c5d0082d200358155905260040e0850b0f10b18100024041c0c0700b00c040c00c3d0260701901408034003080b00d49e0140240441071b00d02d0428070003640c0c03424581e101c0e200c615400440380106503c400003010650485800400741c0903a140113025458540d0007840d02c0002d6000c8000d00c5060820000801c2e004200d940c000398102c10042805801280001c000301341c05c1990811b81030003c07501034181030340025842c54892041007105c03260480030005a90f00d0041d9461030390305522029810030b0341c0d09903600140320010710807000b05542c8401c004011003904080081c8052582d14000c0c1c061500d0100410b2008000c03601c0550321f40800140420b0308600325920700300d040400d088031202040 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 649050863 1250 649049613 649049617
    0x2a090a021c022b0e010c03020406020a111906020d090f0303090b03040c0305190c12051f0b06180102012f070302030d090c03020907080f19020724240303080c 69
    0x1800d40500c1c00c0071940f9180b0520002e280c0025644160341ca091100e40255000e4801c5900b510030540060081c4d061030317035901294410101040e42c00030000320031096110207000c01007000d01156006080410000d490041020600c1c0d40010100211004100f0102307400913504c00036961141d480c10f50f243c0c0c0742e051000f151700183e03100900622541421009501140106201141c407486005c0040c07a1394240c218a40c110084024102d504568022070204041070402000c2140402010400040078030006a064014540d8242041a1032003140c08545c2c0c28400c1d45088400c40384a040e001000c00f100c41c0c02050700d041922907440c0c000950000303040c002c00a607500290f001800f40045101490124014102c600c000c80c021f43d032400210715654010a440f91040c03060124072003942d6503240034140401c0c40c04042e1801141e0820903940420f152803103c0b902e000c41d055403c0080c41d85007100d641100c03004410301762505900d824116201c9840b078208800c0325054a0a00465143d200300740f07907d8 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 649052113 1250 649050863 649050907
    0x103210228110909010c030b0a0311040c09080d3b010302091201150305011b1d0f180906090f030f0f040f0305010504020102070510050306010f022a090a021c02 70
    0x40360107401044007001e015000700124006c01c0c2d5003802510319400900180069a01000b4246040c4c0c901d488a142050740c0215012010b40c540280715550f42c030f00345805c004330b00c003c500019a14800704110fa180c4e003000f9130700402400d00c2068548142000c1d2248109400340300a040540005025110340d030f81c41c0da0845190901c10007005403040100003983c6450340c80c403086596500342105000e4551440350230300303054901900c84c2c911000c0440351482180c605082d01643c40880034458a91544035038100c074001c84101c2c03513140f109040c508140742c90107000800001043d4000c2420407680f80c404025500e4070b10018032210b8444240030200c14090045030402000421189400810321a0540155010700d000b0380070b4486480e143c1050140080000c4c10001c040f4204101081140d4032800b041504080c0601c140d401c41036940c4980fa1895645d88900f5103040301542c400209e520f4080c4049030443d5516604502e412003210344844402042507452480c03640c04035505050096960340b000b60 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 649053363 1250 649052113 649052119
    0x60a0813140d020303090f0c0a03030e040908030a050a0e060603030409021e03040c06030b0109051c23070509090a05070308030a0f0204030305121005031b0f09010321022811 76
    0x10010b00100000e41c1c98200300d40000e0f186c1700d84041d40565840c0410300b6244d510018090703d50781c90450f18182c0703454034070608040c1c105585c4c0c1210740200c0c1d0054060350140e03814100202d101d050883d0b8403000c1c0c401000c16900380350480e00600c49207540c0001142c0c00ca450b668405a01d407600741440100e0341b1000c0c01001e405c004000108030404c0200034210f4141d48080d102004a105403400441d100d440710702810343c0017000800c003850440d0044801801180c4248020030640c0038242c8000c0321500b2007080078040e40d10000e002c0c403161910b0080550b008882d40014540c200003034442c113036216080c0c4005407910034000049808030100b60084512441140e000350f607200d549140090156011501c0d00801c1400e80020459841c040a941011208010000d141d00150010018503038410f991420303034000540c0440c0f1506c0e0710344920482c006d5005810080300e000e01500003182c3d06c51180304e208119000300000043d01e20443d203240e0000c0c0d20b1040400d0a460389031605030b54002071b10340740d154 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 649054613 1250 649053363 649053373
    0x5010e010309050c0306040b19050105060703110a0213060503150c03072d170a1a090c0405040f1b11190305090603040506160201020c120a05130306060311060a081314 73
    0x24401b48d01d03100c03030140c1c4114031145411100044070780b084030001e00441d41e000501300201408644034203901214148484151284503800d50300141481c041c0340c1030000001e44032103040041d490140f002e190400c0c40c02c90203550754504042c0c240030912000f064002400b40040c0303c0c0d00205056036000021107207204c02c5002004860320080d10b0180317400712814a125045c00068107401c094000d20500e1034480c081088604410700803c030004400901c2c03a505c7e44401d1100080d10780d500d00508801c0d42c0c4852000500000401d800032000107918100000e202c2659858003000000180e50034080900c1e07070281d080703010300d480c04842138030880324016841800402030000780980407618a025500003940d6035100000520281d0030f0740101042caa00701d4000c40180c20903110040010f00c0408201e00d4501c1c40c5c803006854405912000760016580695220814020004680d0f11400001012500681002810f0400400444000f4250700203081e030036003140100294020581c80c43c3d50702405580c = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 649055863 1250 649054613 649054621
    0x507060e03041a030a050114010c0f1506030c290f03090304050d060b240f1b070314100209130e01140a0e06010b0c0c060309030706020a0c150605010e010309050c0306 73
    0x15006400907179885035000e1420300000f402c800001a100e00c0030304180c41e0103007010104e46504940c0300c1a180e0645900740555910503200c61103200e69001b552281e810740504c282000000000c1c01506041e12503c9002108001c842c051444182c42c003c0c540442c0842e641e80e540c0e10401d0031130203590300a6800401c208031405c02c101041d0400000d80e98160fa41c2c0c80b10440040c184844a450580d103c1322103403007000740407407110b0a54000e01048500b110980034030b0094030411031529580c0e5105407800b0008810765003003241c00b44002059420004820350501c1410703c0001e41c10688981c01030303030266031068079210140082d003110f05904600c1030281901c3c54400415809404110a40c841600a0340d0004c1001d201c1101030703401c46c1c200c1d04000e08044046500780910780e440603000142902c01031160b200080c5140c001466a040179903508a01a41c851514030f08440582642c81050f505002c401e1160381d90103045143c07280803d10700460941c1c0306051440c03c040442d5201038050090100304 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 649057113 1250 649055863 649055909
    0x402040b0414010206060108060d0f14060103120c110405071704080a020c030a0c0e0705040f030516051f030518061e13050a0807210e0a050301020403030507060e0304 73
    0xd80101c91041001207800c1c20b0040c01203803035120031180140491402000f16055081c996107a946c40e910900410901d85001d44440640101114800f000b95000800500030170918221010003002c00e820304d000d0200c1caa40d111007820041d100780d14001e6680300006401c1c148220190010034070410450304003400c16091105665001072120000341c4144a643d034400d0074000340f050301c00c942100c0320020342400c0246050b01c011000c3c0c0104200324003803002007082da40400c41e41d0000c6110391300518000c140070003184e0107500141e1000e0b10800c500c01c0c110086165042d0780300c03c207000c0c03840c001805541c0e0b030a0004255607008001d40c02c1e4070400c4100004032a40b140a0a1003c0440a40a000359504101ea0744080350420004005411256445001488070005482d401e4420707031654181c0048801e030003101141504a4900054440c0110380107400c240c0071000103080d05130000d524040c103545010301103210385c5800500040da074411001d180d240500c160385c040c04e003084407401c4a521300e80d41 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 649058363 1250 649057113 649057117
    0x4030306080609150604090f12030501090510030506041202070902072a12031b080c060f101a031302060307020d12270501272607120309020402040b 65
    0x1064680d118450128001010001e80e500d00c48288404041d0250740d8402840003030881721f401280d0105400000c80000fa405405403900c018055500040640c9499000400d444018084016041000d2814808201c020900580c06504210580b0040c0c02c164002c0b49070000031b1b8001d283c82c5201141310410482141c00121a0b07400301d0f10444031a44646c2d03491440b841e090700c603500050710303048080c4000901964800240c9500c401041c8050b035441c0d1120b8120390b210010b00c2d20b60703421003000c02041c00c07945044d481e04044180105464035042003a42401d03132007103007148110104040001181101140d58045940d076014100580b01d0511072400796407043c498903003101203480c00306668850074880c0701d48034100066140300070700041c865000d05e61041c6c0c0d80109807155500c4190100a50740c0000440d803408407034050307030321180405040801c8061907e4202440143c8074010411101c82c01b00156000c00740c01c110020382d081e0416000b0740007400e00680080d003041c000b2400040c00000000 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 649059613 1250 649058363 649058369
    0xd02031f06170c04270f060b0c06070e2b060606020606011101111225110f1603080f1b030d0e030327100501090902040c0c0312020a03020f0304030306 66
    0x4810500d9142c50f280380d10b0a0050303014824903900546282c107460060240304107054404121300050344003030102c074502981c1d4950844450b10800041024481030f00704140742d80480c180c0b0303060350b14034296800a035450300178040c544200d200e19088440100101d220f4246030307660113481084143d07603400020752101d5040341d065011076120244440501c0e0180511480040030b02401450a02d0a910b01084000c010304a030116030900d4201c00b140c181c034568031140c144800d84610116070180c140321864480134003031204058012400b41c2410030314194580c02500d50250245494444041141a00340030361400103000001c021100010701901000403c0008013150080c40002c8103041c0040e540d10040d169130a800a40d80004143c01030700d060441d4460b4014001d07a40e03840c942c10f03d1641a904280c00031030000d40d40f0a0010308619080c86548000c00b4141090300c3d00b00e006071006000480106152808981c002130f008162903c6035048074480c568905940780c403800c05060040041003540 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 649060863 1250 649059613 649059647
    0x10b01090527100f051f20010e0604020913170c0a0218090c0a240e0d0305030f0603160909050c090408090a0b16060905070e0f0a11030c0d02031f06 65
    0x144045403078200f940308428241c3e0340030390311101c0060780c01d01251f5800054001090444490b04561106002030207840d2150104900608003801c080c0100f081843e80948410000840901e00800182001d1500500c1e42100030150f91030300c1d610140c95040c20f4602d08020341c0030b1801540140c00b45541c0f4172290140d0703c0b0f01d04607060408444144880d03203211b03018500c0c841c00f584403c02d00d001c0000e07200e80f0808480d4501041204000e00101d41039040d10401140421004420041005000500d0540c4010201c0082c00c20b95003032890b49903110858040d03805546d0300c3e1910300301840401c0042d2040010043c100301e000d8030b403505140c842a0080c00807180300742d40401c80005c1c030614002c29101c0707604500014084800165840100511445a00719040d003d2210002036001501080c40d20a410180c1d00240b1444d00c01924012034035400945040e801c800d10030b00c010341a1384015260403404001d0010f90342e484a01d24a0380351703030341040d18400d4a0345044000c1805540301c0342d9522850560 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 649062113 1250 649060863 649060889
    0x3170f0417100903080a0e120d020901180e06130b0d03030e0105101a0d0e150106021e0703031d13020a2a0b1e010906050111010b0109052710 62
    0x2c0001c0c81c1038070a50300015002800b1240420700b44009503109007015200c081c01c0b1009a82100e00c200e0f11030704804240485240c2c0032800b40e4055030004140351200710303200c0c981d807201810a0903154409501034030044c043c0400e4042400301802540c0011030b0420018035091380000c0c49c1c81c0040c0a8001070210002e1b5508280105881d0195042c032581500d80c118a10108850304c2e2112042540202c2441c5c000303680c907030244d50034901c0c0c240100c1140084000480b0360035810a0400380c50400e02568600d820241c034095004580404100c80f0292a03051500210305101003541500417a06035408541c000d0780b4150485e03428003641c0c02080c0090143c0c90708965008010000800301840b8409038042c0c52503e26600001524030481951102034813000140c0c40190802c0030340c684001f60401d0003580da0b070744418400e40da04041a4a21144024003e01079602000002000b40009214040c05900144210030601c1d0703101103800002d4000e40d4040e60382d0300d03000820003140590b030310603110074a840b = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 649063363 1250 649062113 649062133
    0xe030c0f0610140f04050a0b090f040308130804050126090a02151c0209030118080c100c1b0302010b03030a0c06050a020a050a08041e03030504030e0102061003170f0417 74
    0x8000c0c02488040802440c41204d60380402c24000a00710051040400541e00c9000079410f640d043c19980c004e071208403203c0c0003850b0528002c4e0a020026109400b03008010b8054000188001c0c2242d0980b0400c1ca042c002540d04c40e4207522009000c040200701d0055a08108a2071400009003004c6d0355000315002c0c050410307521603c203c0e034407403020400d00c181104010b030054929160020143c000300274000040450900e0003c80700c0040c40d41c2c0484d0011800103200c4001a41008a403c5202960307008011003001036402801ea1078004619414490101945006150003940f0074100c0c04009002c3e40d5407a881c951000300000b0540f8012901645000c000c07800300c20551003920f0918a4a85480d46885ca00d8881a02c1c202c42c0104101c4803041e824800700c1c1d1b054218141000913074840c0c3c0300450076003840e1501600000d160940107045601400c2003100702910503001c41d00302e9821032200c920a40d40ca42074a81640b1030392319540030034000040e0000b51810818542d642001540d42aa43c1000c1 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 649064613 1250 649063363 649063379
    0xa0b0f0c0d050c071a07020303070302030414093601050a0b130c0f0c0c0312052107021015210c0602010b090a050a0209030f070503160510030e030c0f0610 68
    0x101045283d01e94413901c8244500c10200034514100c1c00ea4040c0c2c141042c8850740000e00d035901021040740160400f0034100680002030405220240040715416142e190a0051100030041400398a10748100c2640f2081100304e02c071a04500f10910100a00031450410080000703802074900707040c01821010f00032125000c05104060141c0c05e07690305c00d8481600e40d08116420180913005861101c02400008001911284103030f102c1c40058072000d403102e40b4a50190242400510721300051081d460810510544c00700d000d205103000008000741140c4808041c901c20441500b01c0c10070004034040040480001654810f030503449500c0f07002c4482d880310800c9090303880e00c81da259048505400410040b1001d03400251340141001c2c00181403600d0000040d240c0740b00000e40d040039070030588081c0082e060500c030071a98100c9041c0803154031803510010a20480107070310683d082650751181c0e000014000e10440d0001c41101e0308868143c41c06601c1c65803125015107200e040084046400603c1d44 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 649065863 1250 649064613 649064617
    0xd020904200d0b072102040905060913030c0204050910050411030d140913110325090602030702040203060d02190f060318030c0302010b0627040905030d0b0a0b0f0c0d05 74
    0x95105150b60f203540c4072940243c0d40c45141008926103050a1010084892098030141c4005c1c92003020121ba1410128280100030318043c04a9640f0b291200764040071a070802030001a450f4107407000031300c035a29100046d0414690b8808001c000d03050005100500501c01070b60f15415400f2010b0f5107240d41c3c80d11040e12140e40308070600031502c030144050f04c03140ca4942e401d004600300a22000c90548a4654104419401160900403c1804c0da14032500500030000402c81012a41480c400003800d10034060f5030390282180c0248507a80010000301d494440e0ba1010740c47c1e0b58080c010303445c448510006880d0400050284000c00f40e81c2030400250248640a4a00074069030402184d1680c1981c400f01c0380100024030540a640d205d040c100382d69100c0100030804420103400100c0150001c1d0a034446c500140b800141c4150b0a00421074003150010088820315080d1680c000341d500d12601c0865501203c3c1e03800520203880109a4801c0420408018020800c80700241d03190020fa001080c0c80c41c0c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 649067113 1250 649065863 649065889
    0x30d0203031b0309010231050f0315040501060b0406110114100e0406110a02100b0303120f0702010b1c0303201e1b010b190b07060b0d02090420 63
    0x2056000aa814480c01e41400640d0440706138000545041e4001da916601c1c03050070b007051103c4510a004008400c0344000201001d03100c1181d40c215000d1742c5034000b0396204180c40090310040080000700b002c00c5002d6001d20020b0150720311050b201ea036100c5028054019654080c50039509089400d8040703030003510014883c0301c0c20040640f00608020b502411240300800844400741c0c0c58105281c84c0d1002030181c9800760340f0354010080307071544480c4a41900d108029680c002ea00030f120700400701491043c4158001c0c003595800d1055038500b8400c038050b00118190380d0700541c54456810a803140107a500200314000d480c140145030a06101201c100182d4111040c2502c040c4660401c00d90f040300880520024880b2840c18402c910311403200f2151007200e420784a1b0340d200c491422038102100c18560045e852008110040e180100c4000e0030300c1a03010040556aa407040618695605401c55003070a4015100310550b20305858511101d2644009100c000c13511800c5001c3d80d4500440e280ca030b0 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 649068363 1250 649067113 649067131
    0x14030108060c07031206180e010e120c3c03030603061501030b13090c0503121c1d01061712161410020409060b0405030d08181209030d020303 62
    0x65a102501091160003e190490030400c021a018803210740d00d016140150521714101034501e201c100b892402c4840b4900001500c0e410051083e54110011410702500c0c0005000c3c1a550410381c1d4140c0d05100326002c052454002e15941c00100c0c1c844180c00c0381030344000d1000604032a40341409143c0d42d00085584c00c0d4107500920008020791800b510215030420107060201c0e0710180070002502076001d114858410a81c0d2360550b01c140315601071103000500041d40a0b100d0f00507000f165905511903100300e0480000c82c808110030b0400564009600c40ca0105450740c4074200c070b080d440b4041d01d0644210549140f501d0300c0202c0c210000300c0e0f03410780d0040f000b002034948072003603101e403214500c001d03429240700300c1028400c0001d001c10f00c01c0b10b412501c140340c01640c6a0a004102c01101e46030b07041001d240500b440140403e80740002d181c0c0001d403150800d0b10007980c4050364410f08002138060308410303004500c00103844020320400f4202c4894200d064405100c0e4950741266640012100d0442c = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 649069613 1250 649068363 649068373
    0xf0609051507150b12010c0201050a050717010314030f070305070b01061803020906040e0312090d08010f0b0c0120040518040b07050a02030f0711011707080117070f03060c14030108 79
    0x19020003584070f14029003000e030407261703c01d48032503101d0308540b1001a41c20240c0d4541003085a81d000c00d12426501194508000c4141303254408401484401400001d0044001c20058000c01e84100142c40c040700014114903a00c00c0790b450300504a8002d12401c032040c0c1c80242c0041800f90141c5501d0407503452641c521a4031910715020400280009090a60450354885148007291003c2c4001e2100c5407100741d4281c210301b0000191481d00b8041e250a5080081c0c0700014080c1c4840e8401040842da00302d1255030321401c0000c0c410780100000450501200d405003640403202119a02620848104031342401000410b00304507011003404880c01890040c00000050445002e01c1c0500000b0071580304403410b002c10203c3c0e000301580442c03130598501e01c00e454442002c4d0780c07040213803c201202083c810020704000c00c000d0031480040c094640000c0400d4000f9010300002c212000040081c2c0c1044010b640d52414030342c00a0900c6c00e00c0c840060920b0380c0703010711000514110390490384100b00030b00c = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 649070863 1250 649069613 649069643
    0x27043e0105070c080106090b0a0f230117010e0709060e0f01050c190803040b070203191d0a0e01050405010501090e060906010311070c08010b24090103060f0609051507 73
    0x440c640c0c0102402c5840f04004180401c88102c240f0944c0003901881c0720001d40c8004441c02c000a00501d0f6025041880511070140320300001c2c58800000c01008072500f02c0c2e07165499005070340d03980250081c100312105000001405601c440380803030080c0c00c651034980b2040e4940504903a41800140401e0304282d150420300d20350b500c210000c00d245840c0d10706035240068042031218450140350000d4039080b10200500c0300340207400d00ca00c0d400c00c100f40000e41c81d280c00d14011301000f803100741030342d01808203800b0b4a04440100141c20380d4221740c001c0c04e2145081c0c0b64401e08074180b0081c0129402030f4076000010480354094042d0205a801c15425102c6680d6030328200102c004c4000d00840c1050f0303c07030301881801d940620260042910500c10b401d8050b0420220a0840d003d149181c2d21900030310021100104d117152801c00450f8401031081d50314422100180c000d01116413100c540506100c100107503090780101114240c49045640da001c0300083d456800342405a20030251504424610700 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 649072113 1250 649070863 649070867
    0x608010b03120a2c090f011202150d1401090c050721050f04030b0402040c05040b090402090f0a080601030308090a031b02240d150605030627043e01 65
    0xa40180f0034907107440d41009035403106481803003071103028400c60803107480020151882c00015a941c40404210001855171400710742d001d082c140783ca0702174042c129414150502c283c9860445001003000b40e001c0c071201100b800310003035400d4248030301240d06140a41060703002d4400e804881105422042501c40e6104a02c140f5640902070000641446010803801e06550b40c81000b90008501420014810389840d005100940e0381081105040060421042c44503e055209a44c0945001d840041c0c03502d141c0e00c0030a00c6070114070701e500d6100c2c0d21400300041d8030a00280d0030307040e40c2c03199585180e6034840414240e903c0f81010750080116410900880c480c85038000081c101d240000c10b003003168000074610303942480110b50212441c406c0000c40910288403405403250b0800481103504580b480e1650041850202400843c4142d1010b213480d0085954a035160b03020002c600302c101218140351030002d100a0454840b10491402100c540d84201420021003220100c01a0a048460700c44001 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 649073363 1250 649072113 649072117
    0x21062a0a110a03030518060712110d0f0c2c0108090c09040c140a03051c05190915020604020d02090c0f040e060301180f061a060703120608010b0312 65
    0x14140420070081c2554a8000c01000701c100c841e80603480010b101c6c10041010724100c00e0107250781199602c000300340071003661701011708281d0740c09020001500750280b0002440c9032113a5101030b504241068820904400b1561102c030201c00b0b9601c41241c5440b0240e080b030042d104041c0d0116100901048042040d4040d0f0680c580c08400c8000740d03500703036486100041d41260140e40170782d440340d0700c0001405091914108800c0c0100c0480e5039000310f0307180d0358402e035680005c51442650040e801451003043d40c0124191a0f685441689440700d103407645000608400d13051141c1e020301d42042d54801900340c0041500b40c01140c02801d144e26029050b02880002c00e4007900e4520f6441041121420b88000c500280004c0c0ca00003841c011176042c068101070a49000740b0100e40b1f65070085d4030f040d00080100c15010b40c2c0c9a4840380110b6510501c80080c1c8100100081c0160000d800281441c01c05a03c40300300c150350980010b082003690b46a80c0001e081f20225000660940d02c00c40001052143c4600 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 649074613 1250 649073363 649073377
    0x6221a0d0b0f030a0506060a050604030b01090f0615030911120a121808010902030f01050f0a231303031d070308090f04061d160903060f090221062a 65
    0x110408002e085010070300d4486140800d59054101c213051000da45401e0309210018041101c005050038110341740c0c0c001c0d007001032284100a582d0340c8a00303005400c06820040061450400381c160301c1c2400f0130040c000d450034400071070750140315a030301000d80c0c0f0b13019068244030b0354518024685030115036103941d040b03201075008000348451035000b01681c001110080014150400c00843c280d0322600c18945800502e100700e00706a41000d003044220802200070592114540d0000318023542100300d028078400201c15008c090140103810021001c106205500d07102d80f01c0e5408000c2d002403074001c203240d18504c2c0ca0445654209070000c01c00b1480300300c054000004001c00c2d00681c1c11404000808440030b561150300c115000c030030507908440d044042180d0002c13500c0c40b03884000243c3d2000400d0b50016000c01004103569120440360a03c8951102c042e2a90241c40749800030300790807520a42404840c8a0344440c0701e10030000e03055800329003900c04030050b0040b80d8036004070034a03144841034001c46 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 649075863 1250 649074613 649074619
    0x609012405060a1709011e090b0412090b030a141503030d0b040b061305010f0201020703090e09030c150a0f18142103061201090201020a061a06221a0d0b 67
    0x204c2c03109000050020701610714040000340160344501c004020403210f40000d07610505c1c0c9001500410241d00d00704d41d010307a204807200490908603a0545407a800b03038000d01d01e5071a010007000489400355020000035079140081010b6035a80300c03184c07000000c0d1024143d41580045c00b007183d131168617030040417540800400124680341a90046282600601402134400c0e03410341d010421960855680d0400c10586d2000b50f260484d2604d02500c18540c502c40c0c009007295100c0061402074040c400d442c21080c0d040e09889140001039207005c074540c402d462880071580b80800520341c201d414440c0280d00340c2056107100c076851480d1a90915449c2050514645011310740c02c030246c50f1200e400074803001b180c503140e5944030705001c81130080601e113100b21003645038981282d460141c1e80000b070803a840c03644100040740c044c0015920440301d81d050540c0340d400c401c003c51854181180c1100c1d9104003608101c0806e03034240e980c9141010501c048850700e6000d442003000071502e000980003004105000307 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 649077113 1250 649075863 649075877
    0x90102031b03040303171012150c030b09180c040203070c0c0609090b060f16060b150301090f0b1f020a0f1b0f0501050a110c030604050609012405060a 66
    0x410105094419107509064140c100050038810142c00620b000d0070002c03403180180f0103281246603100c06c00300700d0041c2103007049013803030980410054400c0d8512040c44100e0031301050209541c00f40c0034108102e10310b4031400e4420006900c500d03403003a8a0140c030100310020880015a041400000e50000e0244010007404122a002003103900d070459004100513034440c1810f03440c22184a04a130f100040c1903114120800c00c08070441212010b0700c3c40d10405503084464140940792040c0209070035900e0b9a00b2038210100b1003921816003014604030f4101101c184425852503848001303c0b6140d20500d940502c006010040140481d00e040343c200007180121406101c198440c00e0002c0c0c24140d040721f10400340040e000424101050880050141480403203455042c140040c01c2030003004509010003a0204255800d081d08000781c40c02c194010703041d2101c9003050300703200d074030b40c1f1045030005181c2d801d0044140034040340c901050502003400c00c2a0310824200010014950710088900e0100408 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 649078363 1250 649077113 649077127
    0xd1b05150a050702010915050712111206030106030b0c1e0d091202010c090b0702041b2c01090504050a021207120f0941030406030e0610090209010203 66
    0x100440d10020360100c0e8440440d2400c0d5014000741da10003490b02c011a410010141c0019946190718002c070701c2460000300b00c0390b664140444003404ea5a1000003101c4c2050f8901c9131040c601001013074007030302201c5140c800d596100285401d0304d90b603210003841c242110700050720020329540a005080c4025880700310301d994004110185421026010ad2140c0c1e95081481c1009441100b2081c1d441d41d80c0000e100704e0311790101c040c1c8a00d205104510010400043d140210360b1958010a020301001e450140e6102141400034005540b01056028007141400c20451512407228400344805d0b0580d02c0000e4a41400c0c1444050300014050440c110303000e0003645403101c0e1442000380b0a00460359000c44101e29010b240c025905481003c1d401203180245080c04210328040c20700c031803404819203040840c0e940f0040040805550601e51000c1030802170310740c110304007000400480311a0fa40900044849004454441409907110701d03800303030307900400c020101042d005400455414015a1b0520032 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 649079613 1250 649078363 649078373
    0xd021302040f0e010e0709090b0607172511061c0c08040204150f050f011e0e100914240f120c0f07140a080403080901030c110d1b 57
    0x41e4000b030903140360050007440070b03c2c448860540100b035040324481040c1000b1001034150b2804d4014081d10355100d018190503130300e551040320758140d40f1005059800c000c41500744415040800220460300207070319004c2a4030010811422069000030b031540c0491007660420205078844042c60300f5948217444030850940e40f42c030038642d440c0a5038450a00510741441003104903143e83c550050000251401070200c5074145004c1403d80b603003a40d80001d54103032003005a40e0912041023030600002005940c070740095100d604d28890000c00e5500d80d610307042c06282a1072a0b4001e00400c0407419036014041c1750307860900c070b0600340080711007080c0500700c0040300c06a21580c030a1004461040001500b00d500045000c2c3c11940f02160605440c20115800c841103078602c54803c000c4c1012112402142131410181305101e0356541c04810142d03166924035003c1c485411441d280c03800f084c0b6001d002c02500e400f48a40d004076480c1030003d061a030900c86410307240c10341b00c94244406882d442004000141c = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 649080863 1250 649079613 649079617
    0x6090e0c01090b0a20030309060c03011a090d050d0207031b03171c0e01021206090112020108070504091508010c0305010b0f1833090d080a120912020c0103050c0301050d021302 77
    0x401485c014596a00c0c0080e0071525003c0f01811604810008000400030312251b4040c0c041e00000d01e1146950310710242c000500420107a00024140c3e0082c003044070791258002074543c0c101c82c420b1100d0f003d0151981604c0c080b00001d444064440c072001403c003400074040c9401088400725000c0d542e02e00c841c0c003414510807103496042c646441e80d07000503148a100782c242038070703544954221010b40096052158143c08613540d2074000341070107002c07004a12180d004500b920007070034038030104010b80c6660711008610083e080c496816603500e04110130003c184280a068142c8144804070345c54070340c5185c070036901503119805644a980c2c01c0c000f20b05c001e55483c1c0b501200d403c0500e40611001100500500070100141a020340d00c800800c8580488e8a920b100c0308000ba412212250f10f5003520203050700c14501e44490004146e10340201002000210381c28a80040a650300301c50110440c0c40054085402c15200d5050754401072004120924040b00000085407003d0240c40d98036013040c1c985405c1e0703 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 649082113 1250 649080863 649080917
    0x70311070807060e12031803030403060e07060306090c0828050a050402040c0c1218031506031202071a0a09050d0609060c0e0d0b0408090307030606090e0c01090b0a 72
    0x1640044004000059004e0f00c203212a82045440305401c4038202240c2d5600c4c415906143c840d041201d254010f955410300907940116003190741030040e401d5480c001070b2591018056440445c1c544907000c104058144501c0155000d5034864000507102c480303880e190748244106020402c240641c85100d14a040d00070b850080094410200d02c5050a204100907290200d103840c0c20441c0e001c6d81c190205203600071504501c4103a0070910044940d42c024446100b001d0b0f0000f500013811082c409041003d25805001180e010301035020070075046036402c0361600c03024401e0200d07001d881c2001d01d51414080000b00b4000c9402d061200510b5903410201d10503950f0301d1410307182d40e1b51791414001449900d004030501e01c0940d10f00140342c2d44410000519000340c00d0006041c0541050000e82000005000ca43ea0348200600f101c80c00d540d20300c2c0c400c01500160003190f6242c0d0030003284000da10400147c01007080016162480e000e4145610b0501503003182d18207608000c2c940f4230000805400611007018 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 649083363 1250 649082113 649082129
    0x102040e040c06140d02030402061201061d010305010b0a140d0e0304061407021503090f011a01021504030503281e0c0e030c01110a02090115081308030c07031107 71
    0x507103000d04120008048030360228003030002000c11440707028250401c43c4c004ca01e040c800140c9944903800882c1e000d01550034842c1030400c00500104030b864004803501c5842c020f120290760820304c2d0000460075200280f15081110b142848450030103401751802d0301110425805045c18040300b000d548080d144128500c10481d080068148403156000d5180d004041c2000071003441c0c42c4042d8003180d10740d140c8911540c10400c0200100315003a80c103111a10b004801c1c0c03002400645560070400010512a26109004d48560320544004400c19160a07102d181c04bc0c841e1425035803001c2e0308000021050000c5550020000c2140c00003100d184266a603c0d090310451000070441c094020301201c80c030380303014010300c0b00800020769540e500290072000c2242c28a4a103180e0010707001203500d482c15818000307621603070120001c00c00c0b18400a00007a500d0413644c4850311074071034882d10410740e044000090903000007000022000c11200c0d008040e00d604c01d2420005100c1143c0e601c1c1d00704001074100d044 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 649084613 1250 649083363 649083389
    0x15060807090b04050f040903020309131a0f090402040b0d0f0606090f15140f1e040b0910091d0a060506030111090303041e03020603180610050d03080901020c010204 72
    0x11640c0c1d48181010701500b402800545000e06000000f052180e5038480f03d40b03c0c507241d40f00c440400d8400c0c015124040c0300079003150080008100d18130701501c0c0820800f65500c1440d40000c600b407a100140b10910300c1d0280000311251a5a0244030240c024100480c4d0001d0701900d203c00092150701c03d080f94980200300c0011500c2c2071180210a48544442c001c29060500d800120001c000c240650308450341c0a21a0388000d2000300843c0600383c1813129250711a0803001e684180401200780691510403c5404001e00b0200c002000b1300c01805807904180714562400c1440f00811130351010b0300c120801e000c5c0c2d100d0300d840b0410080c60801c1009080300c140e5103c8042c4a00d5050134003698003070351040041c450600c00100c1c04242e403805548103180708501c2aa100917202e0508545540c00780d900501b07001c0ea039103040104024101000622820b03540700c3d4100040c0e41c2810688140d043c2c0d14000d02c00f0302240616103007260781c020082e1089899560130041940107030802d200510042901c006069 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 649085863 1250 649084613 649084621
    0x320150f090907081f15081f091406030303040309031709060a1e050408032a0115061407020607030309050c030316050c060426070e04030309200a09020706150608 71
    0x52a0009214080302c030303244440184a85403400d51b0700c0c3e610b4155403400580c540d80701c0702c103198040d0000c0c0350701d80c0301d107042c00000c00e02a0090304041d01c10300c00001c2c1d12116843e01070a06507a44400c0700c0c0a030002c0c80c45141400050801100d801c0b44016501e40181000252000562258008101080441d2900c2d404d01c41c41c0205240000080c409401d02c03e05151070400721a4991184200444e4040e82802d40150705c1d8030300389010340c402811000204401507518040a038407180c940500c40c0030440d1b10b0300c10000048080219841c16502424290a18959613400d80223004400c10485403401108000102910201b014107190607180700d000e111403006051140c140740f1003106075409030700204002e207c100010985084141c1e00c08840c225070200c607181d00e50403c030311038001a522400d0f8030103000038194150448940c03540141c1e00d0803e60310f50ba004002c080420113001c907402c02181714042210704110303030280502c05d025a4000c83c5034264032104000721201c80c1c11020224000e40184 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 649087113 1250 649085863 649085881
    0x60e19050603010614010f0219060204030302060f0402060403080319090501150506120103020d0f06020a0302030f01060c030f0f09050303040803180904050a0f02060c0d03060320150f09090708 84
    0x203400110a50003040b6050404445c0200f81031351080c91818400081201091b240c42040110340307800703070340283c2002802c2a1134940043d510a110540c014850031700811222007403c004107000720b81c01031140785414078680d229900ca0b00700030503c85901d0000c0260f0307041c82c1c00f640102d4103124415000041d80c2120110032002c41461600814050300003071101d80e81485986e15001c0c1940d4049810b5021600700c1e10f401100c000141d07034020b01150010502603c6541c041d0065401201c85800c107004c16a20360b0004c03298051443c2c07015002806042c0c407c49054003902d1841010314641ca0464042c1c1c1e12100404c0c6964403a0b486070800ea4000120780c100c070004c84414105079103085a80312076506054980d56a14404030b1300191440180248410855892a007114070320700901c0e080d07441d442940140078004004a12007074400075240c0c1c04007407280c081c60320140702d80d40c07000b404400c144081c0c4000503125088058510440340c0d04020160301503403042443c9201d0401540c1e1f0a0301842d03d0000 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 649088363 1250 649087113 649087121
    0x110d0207090629090d02030a08180913060507050c030c210306031209010201180b1902190804080409060b03040c090203040308060f03070512070e0c040b041701060e19 73
    0x300e0400000142494414007038201242c0f5a62001c06184a032030396028000500005c0c10b0303281c020751511417070042c0d104205c0c0c7c050142801602500e0100d410b0b44c5084140242d50000701c42d11030340c00d06008842d800040950f40416000a01441d01e68240070703940700c03020301d10b62200c080040f09910055201c0c841075416100501004e10700100182142844000b09950b5100003040316001e81c0c0105000c40c259100f544030310709a01034100c0b40d0024149905101840b91029103528404a003484c0c0c05080c1550503000301c03024682c40c04800d0006101070380003280c084001500c03c4401d023078100b10002e0411898001d140c007a0680d91101d607903e0a0900d1700440301e041a5010890881c018401c10001c20b40145596134054010740d1006e4074003848500184c28040035401c035a078003215a5503802522407000488405454042e2006034094682c040700700d509000314070542124000c01c00050041181c2041c41d034800602d100000f2600c29240c0c41108000c2c8811510081c4103000801c1860011460f802 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 649089613 1250 649088363 649088369
    0x50d0b03010209030309092d010303030c2a02060c0303010b042c0601030b0402130b0c010b0406080d0c03111b012a240204181b021c110d02070906 64
    0x4002c42c40c2907040d802294417801035494540c0300da04a5000200c0720700168104c00504000ca040c00c6524550030035018040742d07801c0c002500040e250000702a9000d0140c400320703070164943c11a1155510003550041512601c3e0442244c02440901000100f1207042000d503010740542c403005a02c403070500d05a0090364400e880c00f0100ea00407040303044074003644000c4564000c502807a0208050700c0001c0401c000e44282c00c2040c0f00458030907000190404828050498008894002d01411111008010954100b070069405981183d00b803a40600d0040b030101002c144a400d0181031b4420100752541000039111154000c0310030880031108a43c1d020380e06142e00e681c00300c0c84041c800d8816000107100c0c0742c8018003c0403400c180001781034441c82c481c16404514060181595155103c40300240e802e20040c00080c40c0d98244142000102c48403840c45640e44410782c01041445040079100103844445518070082c41003150780e0345680c20341802031516641c201c0d002004034a182a80010449440758 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 649090863 1250 649089613 649089619
    0x507020d05030f0103081821101a100c080a030c0915080a0507181e17030a27060f020f0c211009150507091a2206050d0b 53
    0x1040100c51a050f003015819130b5041805161107030b08040f2502c001c0311034150071550021907031104554014400142c040381c420703000e0944403000490540f1000ba19802240ba18048401c412284d40d01c4c00c046160b07404c115035601d40032520558680303c500d900d51002490000081c0c9682c81d03034040b503401c05000c1c4004d0100202c03071203881080c42c0e0700414020002d400a4140b83e00d034004038084a224a180401e02e520040091901e1f65995a5500c901c607808c1240840b84440100000740d00003654081110400302c01d0042c503d4802402001c495010141004591807680c030000010106d1392842c007100a0995602c95812541106002901e0700c124160a500d66900541c1d100fa45500c40c4503249020071241c0d210103170101e0321604007908100842c0c0145210034a0304402d501402403440d1030090f041d00300d1310f04001a440701c1d08200d903c01c055011b414040e140950300c6d1b00d2070401d2100103100c1980075440c40140c04400f40b10217030300c4880c00d80c803140c000b030b4020031a01440e00240c0f02c0d40075410022 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 649092113 1250 649090863 649090867
    0x10f0e150603010303030525090501081302090106140409020f0a0201050a0510060528020610080a05060f1302030a12091428090c0c1202031201030b090304050909010507020d05 77
    0x40c200040040c481400014101505c407070104041900317004843c0442c0100288880384844100030041186100c3e00c6202e00140510000c0b846041d00b641c0700511283d0054540c0305c01e60b0801d07400780c8260b42074400745035007040100400107c4242c0c07480505000b007074030741c0d06503642d01040e9402820760750040d04140000785010107001a901c02c0d07014920481d01103017000d0307480780e8191102400c1003044006006090001120710030030641d02281492091143e0500d101c4100e0329509000c1c1d036460391610040485c1c0c004004111421180891558080c0840c4c9041514a03929408241400341b41002294011303180b03400b5811094110039014081c00a409851701d5001d000000201442691044050a40d00f0b100804c0144051141d808000d0604001c0c14092452196802450944000d03019200509141000c088003803010007120040110001591682e0f421a110144101000340100699100c100000502034035145901441819000f000042c0d91038003c402904182c3e4040d0070380100081 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 649093363 1250 649092113 649092151
    0x3241f0903150531021311030906071407030207180902040c020709061406161e0f020109060f270906062001050405060a0903031d0115060207050319050a0b010f0e 71
    0x8100d0f44c40031425011500608805007030b01c0c91100070500030384101a4440e0000400124800c00603100b4020b085503030719820780500502e100483d0b03024140340200113812920701040129140004900ea000401400151004032070703001608880c0340c030614201681000604100050203446260000d0210b6030703d0440d141541c00000e0358610030340007503402008080e04040203101400c2510707001c4210010022910440c14100b03100001841d50040b8001412a507001c507805110b0b030849100c6a03c0f80d01e4024449020084c081c0c8110080d20040d40003400c20000000c8550250042034010b000b540c6403640040400e400c5004600080803891071a84e050a00380b10000d140080c26640c05407082d5400590031100b803404a0241c40040005420701205200c0c441c80b4040641c426071444a5241c0301400710f03552a0000d90712102d8074030607d82c0c90f400c10644000c0001107603011581d594481e6055400603c2680c0d13a0b03203542e0000b0b0300038502c010fa407121306011510702c000766250005c109640690150399 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 649094613 1250 649093363 649093441
    0xd1b030501150e1e040603150b06070b0711151f17030f0c15240315070309030509091810062111040e0303241f09031505 53
    0x60f081010500a16003001101c00781001407820080e40340b0001d106000d801c0d0381341042034280306980030100708503150000e150100d15205088a0b18503500041031840d0343c0c3c07503403010342d4203444904012940f401541908030b801d0301c603038182501c13030145a030741c400364410042044041009103401282c4240411010200c8081001080d80c0c680c01c05a084d059441c00c0054480e0304000740000d0044401c907d80e81400203082c240700540300c0b08050400d0711044004080c0815a07030300044881d41c410041410007003602213210f42c00c07031040f090107401c0080c644803c81001c540103020444451181c2d00c180302c01c500480b0000e20014042000e180f109004850400d804040395200600460500c2c00101c01e501c010881000c451a940d8900108204400301c07840c12010f440758400c031010070908005200351a0f592204403403201c1039880217860904000c031074080c1528903501c0031170400c0a2001e50280040040c1c0c070500d850301c482021400c045054141400410040300b444610005203440150910020340 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 649095863 1250 649094613 649094627
    0x2150c030109090c2102092208031003050a050604031e020c040f092406090c050f090307050306090a11090412080613140108070b0f041a0d1b03050115 66
    0x20507604001a0b0b40a651600135048183d0b54060801c01d2142154240042c5c242c1e40c101e18201c1c0251070f15a50341d982d0400d00418600360400000b40003004c602c210000c01c800070082c42d4044003032026011155101d85a041c5094111036046419500c4001000100b50b441881d510550324244003482c0426802e0300301a48400c0c00fa14514000e9a441c1240307208100b13150044841d90390041a03006003000b07074440f041100704080d40c0b580c40c0386082c10400220300071140b240800500040d9212420a01e400346240c0583d4400b0707600700e5142c45003402c081065a024040c0f14040e00380740c0001c0404800e0343c40c2c2103580000c0040720714800d802c00130800c408201c4120300101c803107000785480e0080c0da80b1040015a5400c402945201c980c0c9421007240100384032921a505a558541c02c0350f10959845104184a20407051139401c44101840104210a070b10250700280014200b0348506102425100808413441000f6076447c480507000407001468240c031466000d071405158451400c0390005002d401d013 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 649097113 1250 649095863 649095869
    0x9050115050705121606050903030a0e0705131a0432060a05060a1715030106090c0c080a02010902130b121606050f0c01110307090603022a0a050a05010c02150c0301 72
    0x4c2c072000525401e07070740d18581c0c0b480d0710340764440000c1003242820002903940e9002100c0c5a50b800e031612303600c0815060300184440c100c80e0020300203207058030f120300203001404468403034081c440030100302540c65a9a9005448144098181c089146a400220041c0c40352040d20104400d070342c03680a12a407034842e03162500984206403015640d07107904940c21540c11905090048025010409000703074518a84408952020114007c0c003950fa03c0d40b0180d0101c4010001400c0030a481160b82000154440050703c210803507800001940c15040c1c0206080b0032112115a450b540c3e11050780c03031141341450b0105044508000100f41c0761003143d01032000c07089103004a9007808404595030411030510b03400c480212071410000e108000006c0c4d104803d40d0801d403045004900200d101040b0310380b1070320a68408818070b858dc0d80d0b0f01070b141c22042640b400003204001d8180680b15810000c900e081000c1c20902e4480c074000100d05026202c020304241400c0522440c0200c1c1344184648080020181c03415 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 649098363 1250 649097113 649097143
    0x210501030b0a181704060201110c03191701092901020a02060d0605061201172b0504030b090601050916020a021c201e0102030d0c050c0709050115050705 67
    0xc48030382d22810441094900070041c50500c40054040b9004c0c0000041d1003240c085800a00943d04d00301281680c500034405807000991003405180f5440c0404440c2c401c0c11101801c01003c95004403280703040c0741c1c0c0700340c00000b030b225181e0b89424491110103406075032112030810b100d8244002600002e44030600c9000c040c2c8100030110f500900c1c03201950200c00104001000a51b8406080c0494500b1000920030341499212060341c800c99103e000c11032015508031400400e28800d0a0310603840da10000f845200b0802c80f05200c04000207a101c40b5590042020000904c0b5a62402c401c0241e0584010f0445416600001144011030b80005d003400100c1e41c101d440c44041c100417101d0001007030300404041c0202000c0301846c4c0228515603000003450400781c07072000c00c0b8207a0000b13500c2030090341e0f82410f0069108000c8119092000d5000342140c0b012450040c1c5841c0b4101e609526140d025044509003e942d03200407c13411003c0411308010400704e08201d0305264151b220187c6078200340e02e440b40 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 649099613 1250 649098363 649098371
    0x305041e0c0801020c0a0b0714041203090e01080309040e1609020903011815060501050331080d02041d06151c0203180d1716030906020a210501030b0a 66
    0x10007551024520280c1000780085441c0c4860100551b039800075074100340c03405050000850000ca1040c0f00038117110b01d120480e02d10382032034002c0b03010540c400c1050a40c00c0018500022034030440100c403880c001c2c625400290b03150003010041000f107a85c24900300343c441d80514031119080010a1400007101c0c2442d50050b201c22506010a000d4442d00740e04205100b4807150388030421a00d407089042002c00d50004112198840300103442522090340c60446803000351519982d85500c0d003820446000da601c8074601680b8072503955420b41e0f008484115000b030f40115044c4060380001c0046001130400003402880ca0070300c400072800c007410710540300c0140c000019580442c10700240303090300c070514030302011541c0b0b2906107000314085205000348440d034069001000c080b907100c0c0403038468440815905907010717291542800d030300016075206207040c9603c554040d4041059807002e098a980c1c0e54980c030030032014140c0f01807d04002e45903124001d0386414010301c0810380c1003480c15030120301508001 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 649100719 1106 649099613 649099673
    0xf010b0a0c0f0f1a0735064b0102070e18010227060408060c090a0e040606140609010e13020f0f0a0f030504 48
    0x540803503032100c0810003020310003401038480c4280f20b03144030351aa18400707803020b50750014000c860503d041159503070700315205140350240c08482003404906d65204040c1d8882001c2c1000d040e800910003c0d8058a83d8440d0b80560300400083d4809481e4007008401e058080d84003181d002c0c04180aa281d1003205400082c00d20078050300608100c90400c5084540c0c0c480c014070190b24186e08141601b0001c40030302c01448c425011040c0301d07035603016072403600c81113401d0b4006460003020b00700400c000265000c104c55400c0503001060035500e43d40e00002621450301c41d00006200c010748824002001a036502c0842101e810315062070800c03040c0d10800c8500e000d03071034510b4082150007000f4001e6243c035600d0200c0018440c0001810943c0c0408400340b550866840050726100000c0c504151640054003076206007140d180c14440341c6025a030b801c1201c0c0d0400d84903c00320b02410110 = true := by decide +kernel

theorem cover : BRFrame.Cov 648920863 649100719 := by
  have h0 := BRFrame.cov_init 648920863
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648920863 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648920863 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648920863 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648920863 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648920863 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648920863 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648920863 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648920863 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648920863 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648920863 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648920863 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648920863 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648920863 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648920863 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648920863 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648920863 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648920863 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648920863 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648920863 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648920863 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648920863 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648920863 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648920863 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648920863 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648920863 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648920863 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648920863 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648920863 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648920863 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648920863 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648920863 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648920863 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648920863 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648920863 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648920863 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648920863 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648920863 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648920863 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648920863 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648920863 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648920863 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648920863 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648920863 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648920863 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648920863 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648920863 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648920863 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648920863 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648920863 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648920863 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648920863 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648920863 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648920863 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648920863 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648920863 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648920863 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648920863 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648920863 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648920863 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648920863 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648920863 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648920863 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648920863 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648920863 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648920863 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648920863 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648920863 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648920863 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648920863 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648920863 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648920863 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648920863 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648920863 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648920863 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648920863 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648920863 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648920863 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648920863 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648920863 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648920863 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648920863 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648920863 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648920863 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648920863 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648920863 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648920863 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648920863 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648920863 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648920863 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648920863 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648920863 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648920863 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648920863 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648920863 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648920863 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648920863 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648920863 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648920863 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648920863 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648920863 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648920863 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648920863 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648920863 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648920863 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648920863 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648920863 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648920863 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648920863 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648920863 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648920863 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648920863 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648920863 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648920863 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648920863 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648920863 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648920863 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648920863 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648920863 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648920863 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648920863 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648920863 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648920863 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648920863 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648920863 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648920863 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648920863 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648920863 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648920863 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648920863 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648920863 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648920863 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648920863 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648920863 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648920863 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648920863 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648920863 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648920863 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648920863 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648920863 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648920863 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648920863 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648920863 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648920863 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648920863 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 648920863 ≤ n) (h2 : n < 649100719) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
