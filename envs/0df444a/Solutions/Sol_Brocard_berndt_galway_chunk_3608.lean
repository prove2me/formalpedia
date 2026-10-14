-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3608
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:09:58.330822+00:00
-- url     : https://prove2.me/submissions/532585e2-d672-4e00-825a-768e11351109

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 648741007 ≤ n < 648920863 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 648742257 1250 648741007 648741053
    0x4030914120a261303060b1903020103020f040801020318010b010315150e030a14013b011b0206101d041104090807150c0813110f1c 58
    0xc4010704008201001c10b158415080003404142510b40310420400344555000c109010502d03e800f00d40742c500000071280280c0041081200460920a140c0c0d101e0425940c10008107000b080194401da00400e0202c94a01069043c1038440394928260ba02c00d40709507168400340c5c8207500310140e0a00c01c0c69a441700900703080182a0245170200700761910342c464040c1500c940044127003454090001010000c500600ba1040d103c420301c0c0401180e10442c003004820341c60b02100604050000820f543e54841400d0005c10080140c01185c0c4550780307180c014112035403200d0a03800729190400a010250240d40c02400b0700c0d1500704c013400c0b030f0800035500442a85140800e8914415034010713800e500a50070a88003147c06611501040260951400c0244021070014428050100c01040c0d207107000c0c070401061200340c40c1c0100c1124a1081a108107001003050701c1d1200004001916144000602030b0080c100b1241d00400030b216584101007003800341c0c480504200400110b510000d00000300d072001 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 648743507 1250 648742257 648742279
    0x603020706270609020f0409030816020c0f0d0f0803100302180f16090806010e041112100917370503011202221d0304081209011704030914 61
    0x804031141050381c80900f203036035503881c00c406644a0403405154508060402d0010800d240340c01803501c00100e4032850010344410381c0010b680d1000c10b40701010b4030002c0043e80541c040341300308030b90f00c603075070000300c03491910f418050740005c0300400590f215003820030305000342130318600511140c002040101001c0505c1d250030421f0300254000015008507c4626071002481c50040503a0131482d25001070075544201400000c8980c3c1907010315200310300c40c441140c00c610300d190500100410303107610381c1d0442d003010502e410148130990052100b1400341d07a000964818000810409500264501c903400c01000b071031410031801c41c15400d142050011150088010f100700c000c06d03500040c00390814a084506840d400c0d03540d00c3d0140c0c80c4919030020345802451003004040000c180030f11107007000e1308039904030803d00840401520101e80314040500351030150f4100c1780c2180e07031156000c1c82c144505403000300e0728400d04544540c4110300c03039290b06103820f06140c0410145c500c0e42c03100c0c62003644000b070 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 648744757 1250 648743507 648743561
    0x310080316170c011820010f030f0b270702190206090406030618140a050312090106080a0303091104110a1d10180803040b0f030915010603020706 64
    0x1074202035642045010312460000100002c0d58032510b0b41c0c1c0c0c2e00a42c24641185071002e8094041e40c482c1d4071560b40b4521a00e4005070804040d00d01d10491030100c2c0802d80b0128501c0e021303400c1130b10016210840080d2001021001810300d04050308801c021000740160002584880000503401c144980000c25004166030191a01b0110000009000324000f1628400d030303840700e4001c40c0103150300000a02528685030700301d113541894800c042d10401015002800010004964140d0558009000d14038080044041040c0030001428402c09990784420000c0c031001c0c1400b210354070714440da40c0401e2a0865052680400020342c01d01c51090749040c01041c00c100081d0101ca0441c2d120b42090680004007400385038101404502d12904810010180b002c000d50062402800b60150383c004854180c4070b0314415034a000390b008100c0104000c01444510300c440602946d0301000e6102140c0602008003180c0240f11000c1c0d0000011036004500e000400c00b1501450345140c804811400303443c00410 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 648746007 1250 648744757 648744787
    0x120705040b07030e0406091802100509030307030c11030312150108060109090b010909060f050a0e0411090c04081501090e0a02100e06070b0412140306091b071703100803 74
    0xb9001000d00a24030a60901500c41d500810010203400008010a480a5150b81041c4505400891243e1040c10300340e004a40903005582c101400a0000c0d418000c040c1c2c0c0a4070300b008860800d0702ca00c84c0f50400f0401e0781c0d40405c01800404042c2805c030f0540e00b810003a8806c0c602e00c20b44903c2c140882c3c001082240d0342d210303100c0812654500c8000c1580b10407000140c85081058205000240c180080410b98980e0200024102e41c0306a0701240340c1aa21501d030342640b401134070005d1284403141b01c100b001d440c1840d82d1a0300040b40b070030388624103a41c0c0e040c46444c1031882d884500c00000303c0d20040000801c0d6200c0c00f6090190000542901c0d1225400135141088054582c8184582d0501d00001500c80c441525000c9030700c007191031101d05140c10540400c021289001c000508210b00d050281000f00040c0c0e03010300e0020740358180503214030380f10a0b110560070b0312003643c0040510541e00410415041030105044032071000307980b0309128004002c45015500404550742c8104a4012501c1c005 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 648747257 1250 648746007 648746017
    0x4030804150e07081f140c1c0c080106030e150f0a0207021215011a0a140d14010f05060f0d0b04020403080c100f0614040b0402041a120705040b 63
    0x1100741c003080e60a401c000010141c016400d0901d101c3d9440200c3c0c64a0006185c916401540c0144000450b0001c050341c162401c02c15030260741119140410321070100b5901905046a801d59503030a6030002815800844100c1c8146000082042004206054041c840c001000d00050040d014210403104408a01031000d03095011050300c0c40b0000c2c140c038185074156000c082d4024039007026200f030f414602d55112000344a140b0004019400006c00e40d407010b00d02202d44070150000d40c2820b003c101c040da0300301000d5000c1c1032510010000e101980100c1d20410002d240f000350070403021f504152a50746130a40380d03006035000c0c000030072540e00240c4802098030f01c04038000d600410340c21000000309000c0c4c01582d00c010040d15010a051b4054040803c81003600141c003202004443c1524800c01d040e02d14a10400c041041d5400c07140205080c19005040c90a1001e40701624061350717002d94620031340d00001005200203001c1100c0c0d120440d941100f82d000366161504905107810038092119900c15 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 648748507 1250 648747257 648747263
    0x4050705091e0d05060906180d0c1a090109030f030e0705040e0c180a1505060a0f0306030b3d050d0c0e010603230f070309080c03030c0a0801090504030804 68
    0x2810007402c80903910040c039402544042e000c5000d43e040ca01e4610760300c21084e80c46206601450740052000303000300c44241000c052501c001e00704840e4611050301c4200d40f1040a860903101450f0003080c15070381480090040d08107000005a0407a2030800420105108980004060030120030120400300060700c202501e008807000908003c45658940c5090302c140281d580187c40c4802e01080d002c9256001c03032180c104c4020a121588000101c1c42000780d082c05101d07071200c400d00c0041940c0c2c0c82a503000c045e111050600040300c548944901624402c210360085007402d00584c9900d0130300c20180241d0210030203581021802080f00ca214000055038020180203807106840c40c401e202503804014002d180c550a50b074041d58441c0d000030050060702d040c000c07108031708002282c06404121500742c80f400290007408819291034800705c020b45817504042d03903020700c1070015010440041c8002c5005145203104983d0303c002c16940035205850581c48140000e15020402c00402d130480c00705035020f98 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 648749757 1250 648748507 648748519
    0xf011a040b19030f1e1e0f050906010f12060f1d0c040b040e030d0c02030f0a031401061d0f010203040302090a06090509160909020a090e0a02031612081b060403030501050f0405070509 80
    0x505040a01d90207071800724052202c508240711072100309000d078488d41c05050103200303a0f54540c0e200c5003c40b0f4295454811a0b525135201000540400e480b81c0c440750401001e60713004241c034031740c01c881c01d80c094400b87c45074001500954070b14280303841d05100b0060210b0090750305001c804c802d040c106440340500015a10031545464020510620a0048038a52200340382500c1d15820b0182000b4001c100820301144442d07203150021a04038080d85445100c00d624400090382a82c00006201c100c40c00405d00505502c4140800b0006070b59000202d0312810511b90300080080c504030829003541d0015024030201e8000808410584c104101305a080d2805480c01181210152001c60b02029a42d8414540680307828802c000d420300109035810018022802c558090700d0b0300f21121903a600c14801c200c060704992984030009a0410060160086945031111195620341440c50404404640c00c0b000aa035030341c0184018501008092464141a1400c10851504e40e401424030702c170740b503142c5200e28 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 648751007 1250 648749757 648749771
    0x4110405061813021c092f0d060e061f03120513180b01031517031b0d14030105010e091902160b010e0f011a040b19030f1e 54
    0x34148685800040e82c0504099818003e440114000b074003c041d400d00045803002d148039081406004601c1c0650f041788010301100c4c0b441d47c0005040c503101d0b0502d40e00317000b507610030710255030755408100f1a207008140203e42c40d007410001c41c3c1020b1004024001d0510007032404c03480301c0440d500100a4a6114084080494450f48155028000d0b0750042001000034517010a0080354110503014000176002e0922603041c01f80c006500791400d42041c0780305042c108e074007044100c030f505104241d0010707000140d03450010507255110700e4065600c0080407513800100c00c03089807584160155185900045210300310f5041c800024280340c1e07003c0c901d511440c50040070440001103140184030990f001c00b0b08564510181c036111004140781c41082d03428010f80300000a441541030180d0703100e1202c050044031301d0fa0030000307481c54080e0781070390081812005200110750565008010450725249080140501032441c0005040d00e5006030400b03030030303424015500c0d1121008820342c0c04200940c1c902165003 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 648752257 1250 648751007 648751027
    0x20310090e0a0b0424091101230f160c03140f030703090e07020c09010f140303070c060c1b3506070f030905150f1e0c07140f0708010b0411040506 64
    0x1700c0458103118056919164401d0204421707407501c4a6000002c5c0c8031282c40801c4101c00104c584040d14625518600c02c0001001ca012094003c0c14407103207188581c600c0710125200c0f008040c242c0d4000b11401d1101000f1401d00d0720081114450017103021004520f48440baa400900b43c0b88030b841031142c1d0f224904042640f80d8024851400c10400161442c411503035201c042510ba5800c038482c1c4541115510b00d1301c1141e00b4084221a10180c1040c8060a021301d8442d0455801c0d40e410001d03030f10b10000b10f40782d01c1d1a07001d00c1c01d50002018060b10144040e5142d074203800101c030150504440d00004280515441132020a4040d849205420030300340c102c3c070000094001c0c00400c1401081c034050001d9024003a0700300a0050302070350386400d002c1c0395942c0300a0b40440c802c40a041c9907104100b03520018480145110080091a02c2800030034041c46014552514003000d1100d884140d400c40030b0700b030180300824410003020140c119070510225660030f034440c001b0711840c00b4540c041d040000e606411 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 648753507 1250 648752257 648752303
    0x3a29040c091d010c0f080705040308090f0a08030c0105090d03020313030806030f0709090c051203270d060b090a05190905010b06030408070c05030307020f0402130801020310090e0a0b04 81
    0x40e1142c1d010003449030080801006002d10050340e00c600c0841c004034003081120b0f1040701620292a40010842c2c502100341c0100003840f02c141c040e241c0e000111410125164a061002d000e00c0d03401280081194203000c1307451405d2014080600b010140305200704840d0032240d4800845e85900350401c0c403a6a10f4100119050000c00c3d07581c0c200380e1182500005451025034030031000c0901946510b451207444004126456410005400450b1320501c03a070584698100d126040d000d40080d100140d410151020038400c4004500c180d9060790764070300904c1a0f0074400c0041d0782c00030311b15000f007003c2d00d40044034150381c1c200d400070034030010340c1c0d540444200700c800d50060359803c100070502522803601789824080707544038100441b0748070a030000000b1740341000003e80303850707a6004000140d20705450b814040250426040e07031503010301e008400940308600f8070045000740c181c140d4440c2c0003410250540300340c0b40301c403211000c5540a04030030b0021541e501d0b0416002a03008040c0285004c2c0c924000c0b41e = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 648754757 1250 648753507 648753551
    0x1062604030e30060606030106050f030c0c010501030326042a05120c01110309030712060f06030303020c0f03030606030f040c1e0f06020105063a29040c09 68
    0x21140c0604003030342903601d0141401c8083d10190b0080b1105540c4210903c031160100784111400302c2c0b014440c09030080380200255501c100ca030000789003848102d894050030340d90f003a4025408200e5090b860550000c0340340e2505140840000c2039900740c1055a19001e0021001c40c0260490b44454030b520713029510760414000800d0001c0c500c16815103c40516603c51205c11460741c081600d0200c0c03444d0556011080d981d00900040c09810504d00c1c14501a000d10030f0340904481c500d5440b116801402000e20540020b18040c2e034005884241c00d00c082c074603140c112904010180d00900411240303031394030790850307620582c00d8003414540e0f1910b140054006210390010011158003110008408507894440710071540a10f500d002519540c20300ac0e403c95409841660f00b04404d49800354199220400c1c10001022080d2003071450003560004504074081c11800300d50f05100907654246555440c850092888107851400205040c1681c1d041c0015601344903604402d52610b8132042c1011410460708 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 648756007 1250 648754757 648754789
    0x904060504050114012d080a1409010c090f0e150d05070611010f0603080306091f06020a140111030f090a0f0b090f0c0604180e1501062604030e 63
    0x88203c1d41c55401c209604100561024001040c2552050545010062507520000000e4000f480c084003a0303801c45d4042c10090000c451795442e200d941c0d0306080b901041510400c0040300000307c09515080040c1502000d0303010b9082501504400e008264111941c00d4101e01008921010b101e5204049403c000c014040985280203c81e0002035154020701340300000310f0000000c2203888440f0f0305000c12136000b8003024080c00300600024046044c40c0740140c0d0000641943c005000000c0561094001d269400420068220b02640e000700049044400204030044009100c1141411000c07107003404010a4241114030b0040131418002c4d0510445141c580c10411040c10351000b0b00b00241402c03016607000001d8442c1c107940c40908031001c42d13040c18a803401007002d4501480c00f401914107144c402c8603000c0c0140d54110111800d0020003410a2095002e4440d1601c0d42c50910098504001c00c007180b0401300882110340d9098400d640042d60060b414103101846258510100d2070b113000507940c0e2 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 648757257 1250 648756007 648756011
    0x1008100e0a060219090803183a140c06070f03090306090b091509060a15080319020f0309010f050f1204050c100212041502030708180a090c0f050904060504 68
    0x1c0795040c15212050b404901302074a5030915180c0e649000f0ba500e04c5481c4400410f0803080b10241450720b0200c941c0300e04400d051031500b80d0354a01154402e4250f0302030402c2d0703c00d010340d0b01c101010000f10280080040700c03180d01800c41c2c2c10709072000c5941fa100399a002021285000180b80c101400390400303030003030751300090108a03041c01440c085a00000c25500c1c54007070310a00790b03010f0751100c160345d04610609005c0d01908094035611a40c0c1c02a1031000400001c6200001d8041281030040002d08041c21007220800d9011007040300103414448050780c80c100700d800802245000c0d07600640c140d0400c0c120791810700d6982c0454466195140140c1c91301c0740c49104280140000c0c40b0001410781c040c62011100d800c44984212010313a0f42d0049480c40d0000000e080c403041240c020118010030404942c0d0069034035200c02d950707a09080d03500890111001c1d0900d0340c4808543e003454140310014041202c0b040020222401d4050300680451165a082001c0066801d4080d191900036200801c0c2c05041 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 648758507 1250 648757257 648757267
    0x5010f02031e032203020a14030409090b040204140c070206072310060b1806030601020a02030607030504030905060a050711040b1809240a18081605061008100e0a0602 73
    0x6014883d4410b0340c0140f0419400024400c3d00c00700700ca410070312203906130028101424203540306040014150f03800a65400140f00000760101103005030035486200d01c04110052400e8070400040311032488101e20300315090713401c0110655110301110010f980480c1e1058442030035251064800f80c2c2428044243c4c90310301600600c800c00001da03080c810413210424000c041d11011000414000d400c08a1070104074500d9002e06810400001c541201041c070540d0560304058000c2031420030140c0300c039400a0f07510010401030684c0100c0c0300014140450722246440d00c842c50040540c0144d0fa00603140b83c1c0c0501c03070411682c1c6c2d03540c040f80d0402d1001d8945408400f494400c2e100c0b008007140c18a04500612202001101d42d10006e60b0780c281510107002999202c0000310b000030015202040b06c44503c040c0b180c0040350103603014003103c0341c3d402d00c02650280a45805814000c014250025003588510240440c0c1c00209042c1c44040701140c0006102000120a078946905d604010b0481840011 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 648759757 1250 648758507 648758557
    0x61003112704140c010c03210603030504090b010e090601030b01021c02010207030801090c0504031b030f06020406030c111c05040906090506011d030309010c02041b0302030105030d0c0c05010f0203 86
    0x1041e2885180100c0c201c2040440105015071101d508420042c001103006080b0b00001e8043c0240302003104080807803000f1421150803d0044500701e81099020590106080040c0f04843c012a101d0f0002803801d220703145864800300740c90031000360200e0b042c5900d8420b20b41d0365904c2001050030503045003002c1030001c0d1680f0380290003503004100c00c1e400a200980041801c201c01d01403002d4220391990341c1803501e81f46840380ca0106000c82071a032600d803006180017000c50b803d801540c503554004d0b40010380d00c6282c0003020f401c8991a0303907181d0603c905182e90325503030000460180c00505036940030450414000b02c0440305442140c20500b4020b1505001090b40e03483c0d9801244500c0080c1c0740e00c04c1e05401c1e183c0e910340031060308680a900d0341c002c0144032900d5102d82c002801d603902c040d00128800441c0080d880c0e8484e49071115100181d80800100400d241c02c0049010006103402c0101000f007044d19003224203501d80c0141d0f030502400c00c415015103031081040300d1f103c50780d11100001c6aa0001 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 648761007 1250 648759757 648759829
    0x50a06061e0609050603130c09020408030904050f040f06020a020c030105190c020a050601211a0604050709030c05121f0603020a06050c060a11090a031a0906100311 72
    0x2041c101481e0484030007140b110b000310784042c19500300400d00c0d41569601c80c00c1180425403078204840d220300c0d41d00009050741d07060001e0400781502d20040c41d2240c0060007480300b150402051010400c0180d010700000c1041c0c0312240300c00d030381c0060b40541d48034126803040c1c0c0340180c210790140e0190f291104100c11800d100c07903040a00d1501c1d80f0b00340100407007440226552408818003410581000e401007180802c1d12828000d8000038108100440d800d82d00e41034906940740c0b45c003400895034a02040050b01e058416564000c4090030483c80c0c441c110f45900c0040c1861303004c0e440c000c1021020303203158100c081145058450380483c03100c86e465610b08006000d8909807008074090305888034045100c0e40902c0130f42c1c0003503180c48010301c56540c465019030040d20180c607542c06481c0c010041d00c0b07200c0e00c56241080146001d80c40494250150303142600b00101c00608056140d000001408a0184154001c0003201e4201000d94407035042c540000d0900c0c2d07022078440031060f2400c0ca2180d0130442d00 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 648762257 1250 648761007 648761039
    0x151101020f130503160b0a050a03111207080f190f06030602030103050a051005070804020d11060f091906080103080703030e01090b150405061f1214090f071809050a0606 74
    0x680517a0021104034003848035803802070285031000701082c44000c1e0340798881c0f03000e08058101c3d440d0200f014030341940ca0400a502401400d1161650301d410032003003540101c0e959802944604e2492201e00c0e01c49074602c00c007100c4c000090752940c0c5031603001103000c82b02d4100b000990381100f8219900e503508d1515583d03c03041c10b40d00300c0c0d0743e0064428a03048088680f10303491003a5440d0f100c0076403a9071190308101400100346030440b45244d001c20003102513140c4102070310000c0201d4511954403401001003107140c421841c1441c0c0c0341c151000c4107200c5294007808490440b944040b0312615544a841e06502808010396003960317541c60184642e00344500c040c681402090620141d2000725075000510061b034070304071000c2d500308418503801d54580c15030309602e80148000d0b00c1c5c45c00e2180d0440100c3c00070703202e5454812004000403010310a003480140691985c00c08a00c004000c19894040e02e10040031281e4031404d842c640e91a10741c004e0100900010303140c65400348003081040d8841e640104003030f400e = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 648763507 1250 648762257 648762259
    0x1020408070602070513020f1206040f09200d0c03081315081b03060901030b070c0804170f0d0807050f040312080114040e070302060c0a02030a111504151101020f1305 73
    0x81901c641c6c00c00515200700c0e15035503070300000b251038104401c020501012001d0400d0f60807aa0b901d04034100103c03180f044182031403240f42c8001d90910f10845885d10304191070a000c0c4205405107145000890031090001260f0340441d40300e4030b40d1842c1c110000305408a03440100b00940340304102c0350881e0300c84041e07881000c440b098009600509010340603d030004803103031600b04403d4001440824890100039a2084c241d1601030000700095454602c103801039400340840405400c040a442041403040d2101181010010400032844d000c000f814a4400352440061020008010074410b8001003250041c5422004190890607840310083c03080109119a01c6031004405004a4501d80b0340245109119204014501d0324113640810149070f000f010a851039100b1400240010388061224814090103018124006940032050100383c0b414243c490762600c2c0200801d02240d1790715000140300c001d8924010702c1ca0345085901900a05c1500c41200f048080400c010a003003918207204419100 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 648764757 1250 648763507 648763519
    0x605070912150e0c1207080f0c010206040b060f0a0305030d1119030b040e01060b0711030a032007031e052517010b0d030309050606030f031b010204080706020705 71
    0x19444032420008901468001c141d48850b4004000701152508556481c003581d4083e102014548030000d595a2a0f4080341c02c0c8136000030700104512401880340c00c00c032001d103801400d074000080b40001d4980c103008200821064408010030a20348031849103018005000d044005010303102e0410a6a030381040600d41c40344c604105400c8413846041f0181d03507034505240d9155101c43c054100540c050407003240c0e13090b0015501d400d1200300300424051400101591f808107581d60103281445002c10740c020540300c1c0641e22071440400041c0c0d1192100c42d0041d4901e00c0f08880a50a00c0c4490500c40f49034806021354074281400c0605e500342034502c0c00c0740e91150048a040020091035000c05003003a5000d40c42ca0450301d601002030365585105404070414903000010780c41c42c0070700021900240d0060540001e80e42c1e415070020003408100080e0012800c40080203064411000e840e82c034400d5002c2c512981c0414040c0e860b030340c0c1c0c007501990040c26030340007920203450312810029079a102911074203201f03035 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 648766007 1250 648764757 648764759
    0x1603030911030d05031b0708040603021306230c1504031e14030115110102072607151a04140a0c050a0c1b03020301090b090c0105090105070b0711060406050709 70
    0x202d000500e00c1002001da480b02400c5648040c0030260014003001c80d9400d61608024090006c1c101000410103000140c400680b0303104000d200c40220503c9422207010703c0103034049840545022003084140541b42f8151aa891401a01c96414030380303000660101c0b01b5070340041c4410035402c0381c840c4204000d060441d51541d0a460021200c00d908503094104202c4200b00510042c0d902c1072840104d03603160f080643d01d40240483c170034220b0340040019105c1c01d00000a41585407105440c000c2030707000341c070603a41c10301d03d003900c40c0100c00714000d0149440c1030740c4140100c0c031003070001000300c0325001c014810400303264003086400300c04030112a1400650310341202d010b03005000301c05407401c2c41700c42d5854000d119900c1e51382c1402c42d82d5403200b6499200d8261000401a5000d000780603d50703204072000800d6040090000b03107851010034803039040c0142800070220b10303603026045c0c07132810781c01c4500300c00680c449040c140d4404d4442d942200f0340b80140404c02c41407140d240c00103800f45046aa40810712 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 648767257 1250 648766007 648766009
    0x130203040c090c03110409090305040f080705030c01050c03180109270b10021902060d0c05090a06020f0c061803061e01090c0e131b02070e090d0912081603030911 71
    0x101c21704c0c0ba01d0441c110040c8000c1c01140440d0340181c010724032a00f0400d10b8103440380c0c86000c506240d640045c906620114080c00a81810f10101f8400307802820110b0030711340c02e8183c2944a00038468801c030314241007441e8840c5a845450103500801c0d41c2c5210300040c3c0e80c80c1d6a0440300c01802900122500d060443c090101c0c10054400001c001e41c030b50146c003080d001c008a0034104901e20760f0980e0300110900c00e0411060452044503890226900e07240e50743c103260001d1148002c0780ea48102d066400c151190344842e000424811a036a404070380701070313031241180c070550b6400080341c1e94140c061049070104441c00c018070781501910009820b003c80641e80c0e9501c14010b5800b070200700350001c1c10070740301e155041c200340700d40c0200e00403d080c01103040a00c51055807046913a00030f06200581c008201000350104a016840e00704804601401102101250281400d0654070428162035840d594030814050814140d51515240c0c6005407401d10305403c0090241041803c1650080c0004040c007540b = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 648768507 1250 648767257 648767261
    0x30617010e07050d1e210f020d09030b130302070b0403050c12030c030f0f07020d0b060a0e060a050d031205011e09020715150302060c030a0201110f09090402130203040c090c03 77
    0x4c480c1d03020b00100b9500c20382c0460115660758141c81283d02010805180400e6000703010940c12101c0544e83d100440c856a110007480c0c41d05181d40c44040c03044010080c804a890325402e81d5001042080d11710584a007407038200e140204503408072803060300126002c8100040480e68008001c001c07117654100c2c1c014195100e480344949880d00720103074810002580ca025069000c2c1480d112000c510310306200c0300d03801042c11118109012101514640204030300e620f0141e6007413001d4010080013030307000d10389078002c04d0764642d8038007403184641500104041018802c4081c607a1415a00304248000e5039a65084000d50100d0207008910b90015030700400e00304014820f44e202280c1107505d803030b40050b000c410b1b240207001140c0c50108e203900400000c400340e1680b00003041101ca9450041d60394440e02c07a0000d086442c1510380060302d08080022004800100c8142c0d08050300844490040381c6891001910b4900c0758000c002c6030030300100800048c401004595012191250000c0c4544413040e4000c6007 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 648769757 1250 648768507 648768529
    0xf060c03181207060e0a031203060305010c030e060f1308160201090b0918060a12141e0616030204050a060507110406060c26030c0d14010506030c0a030617010e0705 72
    0x60f031041d0700812015215403d150000c51001d04031800031038a03078072404801c0c1030b040646030201e40c840030100b00b08a000d129058032000c40d85001c110986908030f65035144c8a000c0c1201d060121510003252103002e07488040c2021941c444a510b946d1481c102021603d500e0500040c0c2c04a07100400000701420410202c802e9040001c01c5402d4144817106101058180646030300d030000b0610402140d005105214685414004c003200d560300043c0c030310001d141c182c01c0585482010305100d141110088000b038195000208000c0e02c841912036000708800034041d5505c115408000070b900003a2454101006001040c0103050141150400f601884161401d5102d0040014a01034001d00450100d461181440341040c041c070704804085000a4240e03001a00c1d90101650001251001d411075480382c0c01c0e40c0e8014000405082d17151200092840c00014507941010100251150429200c1e40c032507030191001602c034800c584a1113001c14020303d12201700d903007144203011001c030b518500720070040 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 648771007 1250 648769757 648769789
    0x1404090c151e020307021e091303020a020d0c0503060901052404020c01020d020418090503070b06011107060809010b0102160501050903161503060b0702130b0f060c0318 74
    0x14550a1900300030340c2800c5a406070100400007100b00c030000000c10100200300e01e4400741d00958580f0554010000942100301040c0403008902a80840e40c2e100c041c0050742c06405003100c0300558000c0c0c103080c2d05110010301c0082d804004102600100b000000d12482507882c00c3c2c048420540d24507100d030b400c0b40d0040d00c00ca00310f001101000a04507061840c050705041c0007030005400e102e680d40f5840d003642c003c01401c0701c040e03402081c140625810b101d0800000c820285081c0850180c5840f0961288204103026003030310704500006c0c2c49a40588103820041d806c20044440d0342d581c407000180003007401d440040155080c002c030508a984009001c600c0031201c010740d01d550b14542001911964444001b031600b501406540c0200b03101071650200c0100031300c4880714101c000288004084a8603a080000503050034055007001d62603144103204044104980001c2155a950014545840559000381e0003840011007061080740403003e4403103006409075041212041b1000c00403013080d004411 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 648772257 1250 648771007 648771023
    0x40201020705090601021e061b0f0313060605090a05100906051c11030706090312050f03151203210705030105030d0f031d150606040b070212190507140409 68
    0x148118038003c01c00c540c03c40d005004640014031803d00d54542001c1026003420146c103c030040048049002030801200312036008614641000310030204414000030f410201c481c0c41000030442004103507032140c809040000d280d2189c5107060b4010f08050032040f20700350303540080ca400004a40300c49000d0001038500007030904003030701890b400f84075030402c0f180d2056411817114100702d01c3e243c4003400b1941c007500881e070305c500c003040c00e45c1440c0c81d85500301d02d02c00c000c00030100400020100c814082c0c81e004400310080303100e003620340340016407102411040819540400100386027512140c1c14404042d49503204500c000f030359000e000b620f0a000074070800382c16805c00c28041102601c03070280170411044900b80000e030008450891485064044080005039102d44101c12102d108004030383d40c00035086a0300b500d09410046440140d00a40300000d00808405100c29110441400400c2250401c0c4445640940b0182803155603000240b00f00d5540811003044120b4a06050013164080342d000041 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 648773507 1250 648772257 648772259
    0x1091511071403041203270b030a0b3127030c21050c0609010615110703140d08010e070e12030c1204050a12020306040b100b040801020d050a050402010207 68
    0x9402400142c804038082d90700041002255013a400766400000902079a03076040c001092900003061140b00e101c1e401c40c180b82d003003001c001c58039401045076444280d0010218134181c0200128180710300c1c10086d9000c0d00b07400c1d1400e0f034505800c0c00000d0300500621009000140341c2c4440280c1040c000c280b03031160500f44880c0c82c00132074006c221800d2514415105070050441013458010300103900c040c0b2a0010703100080015840404000403a00b101c41c4000811000b45044000350b12001d480c2c4900c424850070b408420203114090090364005c1d40c0119104034509a6010300c291a80204a040c4010401d807100104e0407000796076010b882041a0307203500c5c0101080104000b1401c9444c00b88480034881004004004401845540450f61383c0f6a41141c4490034081080042030319504406898801f5551500c050f03900010b441d0342242d0010108030341c1d511159501f10600307485400c040b0590400090020740c5500550040c010924903100410951320303901004001d4070000d0b50040d00681c84060 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 648774757 1250 648773507 648773513
    0x6090b07022704030c0c051e10030216060b100f050f03151305070813080304060e190f03030605010504050d02090702011b0c1110080c0c1504050109151107 68
    0x59034242c40d41030720b400403400c0404100c0c00103808034211811000191460020420446070840300d4015200440e06001d9202c82100c10f803a1455507025003503c203807092000952002c0c02a811240e00d60421524080c18800300c0c20701002030074602c05038a002d1514100c90401551040409512601281d0756a07450704400509525980e003018100c2984203c91b80305004541d030b55109034400c0e805a080c008030301850000005020f180c4010038040640f50360309071450014081c5421240c1c40f44d071005001032142d804100180c6041c0fa54401c0c251001c200020500500c0301d55440400141d11940d010702c2250f44403c0110360301d0055126a5801c0150314008c2030041c6004060668458101d1000080252602c1c08910050194001c1007000c10180319100c0c1c240800c201070002c0400c0141c5480d0700046079100000d203130f81001003401d0010b1901040c9062000c0d814050900032001c02d50344031100d42003600b0420300030030f81e41500700c2e400f03045c0c440b240000145501031420895189007165007000c0082d1 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 648776007 1250 648774757 648774769
    0x80c0a0b120c09060405041a18220c081212130309050f1810050a080c030c0108090a0501090b0f0702010615050a05040506040b04031b0510051c05010b1306090b0702 72
    0x10a41d61340000180404605900ca0b0b2082e0b407424001c40103240c80c1403040a0034061040460038000c1c960407000010011107105260960a8041c1d00c8030301e0969084203810b215142010541112180b40645140d0065965000c4007800c0a0300194640d2421610b03400c0c20728010130310424009010945141003041107150504007041aa0381c040c00c00700000d41d06019200051408403000800d811141c0c03410302c060b040411a40c4041c040f800000c00c00860750700c00013545c62954405290412555400140b5281d0303040c0701544107030ba4000001d0000c0101890700007100c01044485410754a40f60700001c0c000e0741705000b8041207503241d07a401c001248040c07504891651000c00707410207205003080b00086c152030380401080142201450252124198600084450592220014044207020b0306010503a10141c0d03c0030303105420705000750f5071601803500c10980d40420000c07140642c40c207000016403c0c6003200801103448a0202c1a8130161202402c0c0c41510950041c1d040001082c401b08005080603 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 648777257 1250 648776007 648776017
    0x307061119060b040e0d0e030703020901210602131505070f08090616110114070b1311040911030606011110020f0c0307060c0801120302030d0510050307080c0a0b120c 73
    0x50600415002c0f90030003c9001e0b20b80d070014143c00d9611503205240e82d01d60180800400d044114050308800e4034540000e8503000301030090140b01d43e07160440c007000080c10700d030844c1a00c0d44024259210103511050344000c812034407030060180071107401c00701a18414000c4405440d44440400b224082d2078559060340d4011b95206504001c0400000c451013a510b0744a0074901c0c45003080b001000c0709034000500c4030618007010705810701d0900401780007801c1c640865a01c440c0d202801442880306080c10610070a031030075480d8000b444d01e4014424071807000c801d542d161209034219000ca4482e00011139201c4003c07525004140c0080c0d100d50090019900100341800040c0d205a050100d04c44c030440c1150f01c034000c115450307a901c090084000382c10071151401480d010000d02c80301c0c5020746000c0d460384030310104c0e000020b5895002506010240a41c00040c1c07001030308a60000382c0380c03001280d40301407580b09607100f400c010400180150308001240c0c0090800340c80400151517040c0ca00c03001c3c3d005 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 648778507 1250 648777257 648777263
    0x7151515051c0608030d0609060602071d06150c0d02010c080c0d0e07091104080d05122a03181203091f0608030a0914010e010f0e03030c0d0503060307061119 69
    0x743d0700b0000e03c0c0003080000d091210410080003d4241c50030405030100c8a041d4851025904a15010407150b42c20b0001d90034441d0844508010550794000003503001503612900807400040490354201140c0002080d154060302a00200002d60588006881ca03c00488001d140e03420204041c0d0768170602c0c4c5d009841425140006c4030400e54448092605030340c1414403050701c48401180800404c030b01088103642154103418a546403802c03000c188001c80c900200300c1d800401580b484540000041c000004103088030903001601d03030401d0203c00410760b21181d81d520041c4100c0284000080160040783c3c028008000144081001e4402461ba41c03090740000468160307452600051101c0c09100070400d0b04116943c1200050604041f800440303540c00721503040120507030422040b070740c2006541c400c8840324101000310600300000070346981f00740300c80402c0e10300903810381c51182c40e00075000e54054401103045d508110388032141115411079030b42401c0d15541c08155244102113202c8120f05103640 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 648779757 1250 648778507 648778511
    0x4020705030d110309150105030a03140c0a0c0510081521010204080d110105100905220b010303170405030a080a06080f0c030106060e010c11030307151515051c 70
    0x1182c41120011154a200e03c9007001c10000108190354409000c048030540c0d55a8804c0155410704000ca90b580409441c001c06000115003501d000d4880b04041d90b9200021004442c0302d03118501e08000c0030000e6102d4903020300202a05059101d000700b640c2031050042c8071190180101101c00c0043e04c07281102c50786122450b170400f84c0008482030008001902c04c040c000c21040711030120040107101c0001c1c540403980d05d090305000d800450f4a0605017140e0a50601140030703141e546c0d0f541c84803402e1459215034440144400d0302007250099160703040f03e000381c4514010303101c000d4950103d2401250020030700c0d001003280242c064020800c05400c502d6650002400540f1044208e14081644080b2601c43e03001120b10041481c00340140006058185480c4c4610610100080c05a03e5900001890715140c0106012103031810800d40e008144c00401070310702140124180002811278114100c00540c1150001c110a450020710913100c40f81d65580624002051341302a079168500e145660881b9 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 648781007 1250 648779757 648779767
    0xc110a030c110f180f0117150403110d020c040f140408180a08010b13150302010c0f0b010e090f01020304080a0c17041409090f0715022d1009110402070503 68
    0x244032074014070590b698048034071085081011441920b124168010842c040040905045410008c07a090584c00c14401a0303020700d4407107246c2a12080400900a1110702c148032400c041550300060120f150403055a00b0060300344654002d20540b5480c1e10000d101c1600302c000300340014140e40081009164030b120741502940d100e400105550001d5020030f080c0d80d110b4005403401e16002c020303440044041c1e1410480002c0411040703049000602c006810711550403665803e2002035015401501e030701c040408495a1105c030140e002c1da0003078034014014402e40b007034801e149205100306d070b004e0b0b03400501680c201803a0410840e03066500c00d00440301c041c405d800035090f804012014001920a00d16814442c12001c000d00c0440f1000070007514482d030044100351400034001c00c603441030b120f0040c0e1031281803640c1d65080c4cac90400c03841904607029030380c0001c504c0e410904100c2ea4524400389000e44101c0f9900419074400ea6030384480182c040ca207009141ea4084c9420f82c001d24500e881102624241 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 648782257 1250 648781007 648781009
    0x131202100216200901090906020913091a0c0d1a090a06090e010605090105040902180705040306060e0601081f031a09070b0a14130b0a030c110a030c110f 67
    0x680c220010900c420007068082004010112606090016000f5002000301c12080002500391106104034440c0541e10700170802445801c0d0100c541d01c1c18068140d00d0743c4e02c100b606640003031403038440030b8990b0300b04641e02c1c1c0b50303c41942000328000c4404004490621420000000040c10a8001807842080105103048117450b40050035109000007500001c2081c504426142555030506061500ea450480284541d5840c03c036006c3c10b4074000c1d0390010b0240c05610200700c1c40c1d56000245c2c0c000c43c2c506800c01142c0780c0d1000040c010303684690340501205681e050340301342001095507180c1c0892550400180f170111610080d1140e844200d0304445c906540c0d80b10f102013032004084904010b060b0604002e0f85400070001303440200407a0042c5841c1c1f41e90200e00415140e58400522007846001480c024800f09550304000505580c00d02650ba416441001400030400700383c00e000418518200c40c44901c07404100301e079585030540c07103519046116030f41c1d00d040e0001d130455043d486140f00740900d0207 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 648783507 1250 648782257 648782261
    0x612010e10031514060d0503070f020d020604090207200f010f180e1e04230a02041119080108030d050a1401121106040303051621050d1413120210 64
    0x7244000000560f42d01140b413041500e00d00501a90040d00d001c4c00b6000004c000104a0310341a80120040113030466502c0010814102100d010703601510116010801544503401000181e115050f43c1030030446000704102051000b40c480344e070101b1840030b081ca141d401445091003c00451038080e11020741682414040501900461040c41810303040100c401c004418014200d6046142d4603000d20303081d59200b50340c007240001114a6032442c030008100103004c01416451031b50050080c0f020141300c40244040340c0115071444041c0d010080d10310040c1d4010060701d416103a400020350710301b9510301203080c0545000f0740700c600f900e541d80c44003c50100407291010701030701c0fa241c007010040c6524141503941070429031030b292180c1010041040001e070070808980c40c5a905040613003900b000c90500282c030b0407402003e030202020b41e1070240f00d503583c01001003240701c0152204100c03001da0560b0810040504441c514031515801c0800b9010484d100e0840c80c1040c40d910490b20700f0041403480d041 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 648784757 1250 648783507 648783533
    0x1050a0b0d030c140313030201180b0f0d0609020d0f0b0d2d17040513021201032a0f0801060602071a1b150a0c030c0e01030b04020f04080a030801050612010e1003 71
    0x10306d940c08120203004540e8009803807036640070528820002c00e4201120602c1900c140d11002c01204000a21440d20344425000300d0010480341c1c10854407200104101c1c0c0103401c26884c8490300c0d524115181410b49086040c08000c150420900d42d800d00e402012101c050391000342c0c01205241c0c00400000155000f1041d4500712008140b882e11a8a400103110074000110b1318144554014020382040081204900c0d0440e40c11076405400c110360b28002c03141d01c48400303922940103800c8113400700f095818a040d1008a4250781c000304030305603803280120380711071080c05050810701201b0f4015030344480c00382c051b001c0d107000044031000080015410798503160300d03180031100300460441007003818480fa200e032052595072810103005a0703024a40041c5a10b401c486183d0505980d03280c819201e4565906441c220480400b080d03a942d0f40310b208460f83c0b600442c000701c1c0014408400801c0a0401e0401c1e40c5a20010305c41c1e003815079003001402d10315401c00808030741c511400240000081500b80140032 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 648786007 1250 648784757 648784777
    0xc0a0e030a050d0f0203070b060f0121060501110106141e030d0804050c0108090a14070909080d05100b03010b0306033316021e0a020612070201050a0b0d030c1403 71
    0x80f800a0050002526444600c074001040d0340090144a0124008010700b0764801c100303d607105c1e581440100160b40200c40300b00025003800304000034030780c51055a8400400e41d0303000d8807420780801507200c02034265025801241c0094a454003d43c00508014040300700d0102c0b0144c464002c81440404130b440c141721800c006000076400307800e00c41444000c3c401400140700a19002008d40b504e4600700750359174100070000384007141c440c03040809000d0138400c100141c003001409000d81141c0342071043c5107030401c01541750f4052802012a45d9450444603040449000e0411682180e28141c00b030262900000c015070740501a01104480302c09115000340c02e4503404040d03140246e501841203030040e0030010103000c0719a24440002e5034454000039006900d103214218640d8688000b040c20741404414080250002404540390000d6542c09201c41d20684103640200720790b030340700740c01d842c20745102c07031f0316650490b050108a4002c00d1080381031408a5000c2c403100000c1b848510555803039a40500c1c02070b = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 648787257 1250 648786007 648786013
    0x40b100504060b03010e0a0603050d0e0a090b0306010b0a0c0503030a05160c02031c0c150606021005040f0b070318150c02011a04180605040605012c0c0a0e030a05 71
    0x540090814011015210558007002001c0c2880540a03442c80107000b0319040004c3c42002801c000c009030001d40145a00406941807405008000340c45000e0070b0312080d05c9425a0a0041400d07101031280c01000c0900070300600f0580d20700840c03404650300000c419000c10180d9088840032035400c000860180c0c5405c04000740601e00442800b03c641c10906856042051441c004000b43e600040c100142c4c00c0b803c02e100303204100a004c1507503d80070b6510001c00c3c0311a56020310b07013188e03040d0b80710100321503684d0203842040a03011212011504100d40003000401d45418110101d05807000145e8400402c1c28000350080f09140e240380340030b06c0360104490034040d44d90040f030031f02e98a004003c0795240b603000032f11250650400b4200c02800d0420380a02841e500c40c08084001074488002a8054112204000c00c1c01e05061070b20143c0030900034401c001c60101c000c0381c0000284180aa92404219201030054403600c1d500c101c55070080e94100104009040c008e43d181d901030085210440c0f0071801 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 648788507 1250 648787257 648787261
    0x10b3109060504020315010e0f03011d0124090510080f070807151202030603031b060601140304031e030f020a0908100608060117031c0b030c0909030a03050408090405040b 75
    0x1800c01070380d01c03079007095000c0c2d80180140305003210b28140324007a0382c40c2401d02c59500c0d0501c8000ca18040b10094091382e0640c00d014864520401000001420542c880000d21005508030382030720502071005444852100008802c0160b40c04a510054126486110b00c007100c80e52549180c0c03901031011240700d001d40041404100040301048010002c0c030b150820580e45005501c2e014000c81804484d0109040d00000091180d5400b4000c841d0049120150022048003a1540c5a030700c407003c548842c0070444d413242c8030b0800c41c60181070380c6c400d41d0f05607100c2180000c0b40580100248019400307500303140c0c65000c0b02c828042640040c0108400b80c0c0c0da080c1d5607602c4c1003407491400340b08079032002c0c0140c079041c41030110003070208405d0305541e9120311000c181294101428554450300c85000e151903d209180c1c4aa0304a43e00100241c0c07038200c045880180700e0004002d1000310603120503009038404c01c82c92140c3e84c0203800c5154041c0c0107950b95410146400080341c00d0b2581120202c41071174400d01 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 648789757 1250 648788507 648788519
    0x5100519050421080c2506050c030405070605091e0111061f05060c0319022b020c04052e09050a050f0114090c07230c01020c18010b31 59
    0x201c0f4480c00c280f490900500d04010740018060b1243c44000d050440043e0445003281740035904070b1520341d40c00b45041000e460030501210722500261400c17102d81c000c40b540055100d100e0810740710501802032040e0803200b03036000d118503195400c6032054103010035041200d21030002032102030303c0f03040d9001501d0078440520025a184124980200e8031800090000070704004000017a1b4000740800a0b9400c880d4061070000e038500407100e040c2c201e070b04e044140c00c0d40d0280400c0580501c1e0030501d400b16010b80380140100802c0c0c4400722000b00310040189108000c4030354540f81c108121200032600074020792900f1000c0140e40e0100c030000011911402403250f00d07032100321514018003540c09020401500040002c1d401040075005a04001020542000740b000600015400b039a030007508000243c0e04030640f0307460b01a509140c07405801492415485400c01484c0c104000f024001650b610b6070030182ca0101c107800400c4588a09001c4141a07090401d06520209021040c0300625240e589486 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 648791007 1250 648789757 648789803
    0x712020304240e10140402190f080a0303060617040618080c010501080d181a09040c11060a3b1006051c05420a060f03051005190504 58
    0x141c403440f0961401761040c5290344400e807042c0c0c205504a80040548401070049104224103400c03180301850310300400116844001850710a581c46a1003d12459513900c10075582510380100283c54681e4400000e0001a21a404484038511418921401820545a101c0c003900941b12001d01a0340d03601c018041c401c002c10075020400181e1070544241c0d481e2a0590741d031998144942ca844e59410034886405040314002c0e26200003024100304841605003c000345a0b43c0c00100751a403a008610111719545454003e280c403546211b24003101d10312040c9003600000c49038a082c00b00c516410380b84858410401d001850114902c1440800e26a00302003c02102c1405604d103481031402180014001902c00302c1c10740765518400f40701c1401714060000b451030024680d20310180c02500806500301c41a074a01500d80655403c240401200d511000d000c269261540400380c050313801050aa407440d99103401031a40300b03200618000800c61340460b8002510000d68044030b01e00410400801d61503005 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 648792257 1250 648791007 648791023
    0x6191206090f1a0616032001090b0105030c010203040501081e0414010c0206191a0405010b120114010c1707120309030e031c0c061e061d0712020304240e 67
    0x103c45080c004404600050410301c41c501404400c1210322401ea010f05000d400ca41c02d12071070803240424040d012600007402030003542404c40780d00380c00c0000400c80d41030001d00000f1440f0103800071031034141020011341c0c0f00381006114942500307507203c04080203000a0001402a03100d00c0380010384441401e541420341d0128032509045502103001c114030240440b60608450f004003000140b0507481c0d02800314019003200c0c1c0d883e00507042c40700002d50900c2c02d000a240c940030150490500b070741c0350714411840e0083c0780c22031070021b0b04400442c0d0111701101c1425030003000c0036040341c2c500f007081e5070f40a81c2502d02074080700c0808d42d0b6112010601d03400031041200c1e820220003403c99005210042c038000082608460200300c20000744808001e050341c0102810125804034800c0f0250262540018001d1402646003588542c0128007110b900c042e10b0500403010f40c0c40d82c94181c08070220000094000610540d84481000c00c05c040038000740c036401c403880b825060040750b0000081e09031840c260740 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 648793507 1250 648792257 648792281
    0x31020030c0f16060e0708070506032a0c010606050901080a0509060a020901051c05010501090f0605162a03110612062e05131406191206090f 62
    0x820000c110300e240d003180484600380084a515034881c2d804190780e250715290040020012031520840c09243c10001840d0021a4100c1c800ca4842d6074807001445121300080da0303104005040824424602030208200e40c00e2000c403400038900346013140c6006425203548c0c0c1d2020010a5000500c0841940d001030000d601280d03418082c0154103150001c0b81c1e45175801001c18245941c080b4034241e0980c4070b1f800715510002c440c030002407040c50020343d040c000d100c284900c034003040c55948002002460020703120101d0382d060b03c440c1c6c14452008642940c1c00310b840000ca8040180a0601810f8001a8103071000001d1000c0310441131825450540703440c250010030b882c8070350010f00450f0742002c6603107506a400b40007a190510100014030030f4181d000410601c441e00464007001505c0c01ca54401c0243c8010b032005090701098035a1010307000710710702c21200c0503500300c80d04200348042500810150321800a4502d4030458064002c0315807411144d0030742000d00030988424025840a1140c001c0006d160340c = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 648794757 1250 648793507 648793571
    0x1302030f19050c090c0a0c030e0d0503030a0b0306040f140a06050708090d05090d1514090a1e0b01140d080c010603060b195910060513050310 62
    0x41c03902c00745d07444d030051108110411170010910020184a090107a04051003e8640340005001d4507115840740c004660414942d8a01318440b1243e00e13000035503074010340e00888400d00701c41c095101c034507a040401d001140b944c403601e2aa036000811500c20075110b018156200303100d07030a04640442c10005110009001c1050034003540c4d400350f490401204000d50701c4116480d80d40412104c5001402c84460000f4040c0400d4007080481940402d01e400d0141c41200e00404082c1c0700315024101040d2510050000c10481c0700600140e4082c0c442402ca4180c02400e62401c0301d5241d80c0c4592680c0704500305015651246000c00801a0394020036142c80811500b541c19000d41140082191f001071041f044003480000700340300010302032100c60221078081030b4174142e1340541c03c00400480c002058090660001e1b40180550326015100071800f0b1440d038910072000c9460041c0840d000d401884203030150f450711400009483d07604000e0b8404240c0c18160204000c500d80e600300171080b45081c800b0120131 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 648796007 1250 648794757 648794761
    0x40f0c23090612120a110d0f08010f26151501020f01020316031e021911030304110108070e120703020a0617130f0b2a121302030f19050c09 61
    0x20304081201c444888030080c44d20b480e400305c200201c5100070b403124518124050706002041c0f80340d010380764201e00300c0d990b00c41803070590b600c0a110030891058821040011108020550a07000d4141c081e411210000201c510002c21141d048201820549801c21103040d44180e0040b51b507010300c21228003145180c0214214900007407a004440c80101c603400805984401c0c0c0703c00080d18020845c51680321010440d102c5220810102c1e00b118010308103000b0921000e0307480c032110030020841e8400e551209a1041c8100e80d2801950568005003207002070041f00345c020105030311042c07101002140000700030318116155005100c03818140c0d8100c1d408024101b141c502152121117040c03034010141644545c080700031750074071319030b500030801009044060707080610550603008420101d6000c0d401c0242e000705c3c0502801607490344103907102034480340501c5000841204081c030550f0b6a650028080d00c2405031000001410f240b0004492031030b40f141e2660460030301204100381103603a081170f14082004c0c = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 648797257 1250 648796007 648796039
    0x908030f06030f0d021e0708030a020309040f06061704020609060d020405100207050102070e10150e01120606020d0c0204020c06040b07030c020c06040b0d0b191e0e040f0c230906 78
    0x44008006c101c690140d100c0320845081401c100c95030003020100252911450310003002502c039031014000c03601c141d0270700c03064001c8604a8441c0c64212044c94403030502d242044040302241c861b0080c010303a032001c800e200c000a5900c03080010200703030700d03a03a6005a50300d0601040080181498019004540c80b5040038441640c0010f4414103691180505a01b1035450350741441e01d0401d07a400c081c40080e664001000619008501524070b070900b40c1b00c1903003450102c02d42c80c01b150a40e01c204c00040e800060078121035805900c40e20315035030020740007514004016600f545492020b9404440c909165001c0003034855143c0b02e45280202140b003c0c00300d2900220000380f09000718042c600007050300089408101d5101d40c4142428440580036030f140c41e0628186500e0074140303100e60f1f1717804800c00154940421100044030309a40020b454108030392550f88806a1401c41e58204980300441008082503403c4011882c0c00602e071012030202410700340d141804801c1001501050040311504200004 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 648798507 1250 648797257 648797263
    0xf0e01050a090c03080f070507060908060f090c060c240f0c0702060405011b020a150201231b0403080f0414040c02060402190e04050102030a060b030c090d060908030f06030f0d02 78
    0x80f00e810a0301745803030f0913459803500300e00e21910100410340d101b41c000003d0002c4d00804a0022a0680402d03a0b0300d0355076010700c81c10080d40454034040d043e00107071340303030f041514009015100068100c000c65900d10036011240c40d4111138140c4d032030701c5135030a4420802074201c0c0d62245640010a0b0b190203042880d2035001c21504e02a50041c0d605009a04098183d6141b0303490000509030b800030719488420b5580d502140015206c04607040049d420225101204130741c0150702c55280340b040b132280716a540c901702940701c00d0822038440ca8800c2e10400000000c0340800020784200c2102c40388a43e5030710b140a9644080030444840d540c01181854600700d00103030007142c425400340d015100c2c190150110000f0304a6406181c20a0302120800c1082c0402e011f8150b01941c4036040c100d604104082d141e039030f281d61030b0204440411800c10204500c07030b030398140301c000c440c0c41d03074452100403410544603a9410200d42044901d2081261603900b0440d00749401c002c0d00000c0034140028100020541d00c0c0292 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 648799757 1250 648798507 648798509
    0x501090b040329040303091e0c050613030b090d021507020a030c021504080114090c090a0f02040e07110c04020f090405042316063f0f0e01050a090c 65
    0x28043d85115200c0300d1600340c041000507440f100c0506510300d05440c0140052507810015035256402c0140c4200f04032030413217015a1290480c03402c4a041c1e14240402820303500540d400501000350050020005014110503400740e01540007520903807040c01d00c003d20300780810048080c004070740018414000e4012500700142c079018036000340142c54a00124500c03040c080f030341061400d8005130001c2c492006512544081c00a8002c410749502c82030500d5a544100aa0b55603000268102160b03a10700c159200140500000a01609156a481d4810100402228160081500002c44c83e84000d002d101c42240c812003241e0460821664020f42000d5010307110102c1d018664590206080c0b14403128098400c058810303005a0403001200070030b48400c0c3e14130280c00320104800010410300d01481032000ca101000380005103500c01c4214102449001c081c1440b20852031881200c5a100f8602807400c00418161000c145c070b011501c4200c0c211100104140b0801c0d1401c12800e001641c20300d041d01c = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 648801007 1250 648799757 648799763
    0x810120503130f08161a031b0f040e090309011b0309030f03120509010e0601140f0301020f0403022412041b0f0f0b030426120109050f0c070506010501110a0212160501090b0403 77
    0x2d0388130340c1d41c10036061040d2241e8804a2088c1408912104000342d07030030040043c0c40d04103180510780e4840180ca07036564020b1502140c0855a032180c0c80c42690481c81204d00002d0291920416803030b07403a10b510040c0214808160b0028004116465100120b80240e54001e030110000700845038088884a40710a010701410522204c0404810300964032415021048040100215070700c014404405120f0760252204030b02034a42c80585c541252944e02d10722081c0b00050320220714241820084482880d002481110b1b506130b41d165000c02011a4819000030f0402c50002c0b104050500449036052a206c3d40101d03460380c020010080040d402052110050181c034600e9428004034a0294a031070150244040d1121500d500001d4409269000503001d030030403100c89181038036200060040c0c4e00c41c144024095038040d00c01008503520500c80f078040030600307070300391200da03183d65000801c0319140080c03c050581c8100c900e183d2802d010940e00b801031800b401d00903203903881c010002409006920001e = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 648802257 1250 648801007 648801059
    0x91008070e0108060d0501060e0618010b0d15080a0302060709150917190309151b020f0a12030503040c060f170c040f030f0507060810120503130f0816 66
    0x1041031174451800040c1103540c800000c1c04650f44404900d0645081220140d00c503c410042c00b141652070320b6006070681d804034007410720380010003500e03002410180c1820100302e08815030010b80a101807203101c00f2180f096018200e1800c01000040c1880120341020700444000c0894002c41508021008200c42c82405d0040c00104024000303130400540351a00c83d800543d017081c940030560f200840c202619585000b190b61400c145404440b003c00010540f00303044914007844015142130080c454140300010480914a030f290040c04403003002550b0300310007041c0c010050000b000040b00c04180a0403070f520705101028031a0500810041c01042007404a08070240411045440e8000703c0340501050b5032030300786d0755a81c4c0c94181c11b4501c0c12401a991360203a90004106940b05020260041601203405480c82d401d185a001e420030340c06000b03e42c0e40c4010045024102078a0803403100070101c038122007500740d00d480405800d2407811042c500101d441c9040030b002483c0c5101c001405020748070b8031 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 648803507 1250 648802257 648802261
    0x1142a0115090b18090307030206070509061c090204020d140a140c1b030708071203050c0a180e0115110d0f03050402030a060f05060f030f0307080715020a05091008070e0108 76
    0x41134010781900000702103942240108039200074000010031255100e5403c80c0c005950b00903040f1114044c2d002070301d03030100082080e40c6640650b504552a001326018001820540c02e5000070126844603003086c0701c45461320f4038480408107450000340c1c07201840c0c00601c804c070480c2440010710b82b0f00506000030840003144021500c001e04e000d00e400d8900303450071280d681849082210044d08030309403c5844c0c9504903509100d05101e0300895010b8554810302901305464180c01b0740c0c050700320550440da0941d0007000080c0608100960a0007000c0b8001e8941580080700d40c004c5c08012850340c9130b1816403101c0501d0000f00d520000d2034500c1c159a00d00058907448510000341080700b000f101402090418001c140304c000aa0310a078040d0400f2510741402c10900024507444460a156004950300148414404103101a000301030451180b0789016203103019030400412a0440001d100002d000031440c074003e800d214404454641181c10040d05a2600c800300a00400c480b0341058108110b03d80 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 648804757 1250 648803507 648803509
    0x1031403070b010303020c0901050f0a030620071b0b030708010315060b2a0703020102060a051b0408100b0111100c022d150103150b01142a0115090b 65
    0xc191440d440d80820780d024196561705009542e40c1100480c40d118a01c00c90001805140050031280201c00152400c20b42e28555142c0783e008001d503c100b080c182c0f03039030500d207008481487c0041c500070303210b0011441e49500072034600000c9a11a0050030b070000d01003061048054120b6034450449500a200d6049004012401000383c8450341c00079102c01c0d0089030000010740105641c0407641c0101c4212b20030416200c080755a140c0785840080d01513000301c0b0200d00c0308401500160760100090385054400c50030700040121552081d441111250400d24180d00f26407264001c034115100300b468040400300c822000c05403075062200103806095610008008564000d0082d5607401000c2c000c0c0680300c3c0d0b03280c41540425035492849000c41d006514095500b40361440d41c15050b203411024a540b290740b04070101c001040101102418001d1000c004901c0f10481ca000f00081e00c04401040030000030205403041102030407018100310b0341000f09406600da59250308904451840d0000700c0c55a070712030 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 648806007 1250 648804757 648804763
    0x11515020d05180103110a111204060e0105090d0c0303020f10020901050a0503040c0504020f040302090a09050d080907032405130503090d0602071a011502031603050309010e0d080105030d09030209010314 89
    0xc92400d81046c0e0105180b8a09504030180200745503080b4140c40c4a11100c3e9070303907002c2e8072542c02614040780603485031f05a80d5100e1409800a0344024180e0440e0240903102c442081e400d40d130040f40141c0c8261428082c02c0001c0c0080e06c0905c0c0105401e40c10900440700182650081030004410044003000007028000703a030204130024040078208550310078200b0003d41b20359109003c164040c54103a00070600350500c40c07103580701c1c241e0004060301d0340c00100b2204941044018000403030600c0b03110b002002044440d4401c0c00300543d021084041007900c01145000c2d10002444900d6881054061402041b0007000f100c01b80c01c8203d603229610f00d900d1030041c0c001e00800d90007412240f00c500380419600030420740d144c1681e6000d12900604219004201d9481c40340441f0340841000c2152000c00181c0100d01442c2c0000d4000c0010417861500d98009140041d81c1d540394000802120040020317050a0121200e0440035142458200782103030045580f003481848014049030041e641101c03501814 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 648807257 1250 648806007 648806021
    0x50304201302041a040e0103021011250501110a030806031216052b120b0d03020d0f1103030c07140708160e0921040503011515020d05180103 62
    0x1c0c4500121074011480000030740160048510304181e4148101075054400155001c0750130003003000300740340c0c01e40e4244030f00c49240e100c2180c280300000103000d061181c2071042801d040d40c4421003074406499860f07001044944c9511a9042c800182044c10303c04034003080034490943c0505000d05180c85010109240c01c05a203c3c1e24507aa0000c03406102d00082c41c844a11582c1c00340040720b050090072072540300e000040300c0030f4250b0101035803071809016000d030740d011496001c07644000840c0307421301001c03c01171942c07072008174010780100504101680c2c0052160141c00564a01803032262080d40d423081d0b4030700c000752048040f100c0200d600400c101c41c81c0c11a060341041c1c0c1c006e840130380355505450b627691900310514076403440760500d0101d54801e00602b4213204400510050658075000c61414541c031100c42c2c120104140d041001080648007400f4409500d1150034003940014980f8a0380200040041c84000440d08040380c400045039001080d140c05c10210b01d50850780f4808500103030020000703 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 648808507 1250 648807257 648807259
    0x30b0a180608060609070c0303091a0108030c071707060311040503030c100f090210080a06030b090d0806040c1e031b080103050f07030206220b0c0a0218010605030420 73
    0x410003181495940c102508a4040400729101e0780c440078200000c1384000c40d810b000249220000354082403094000003940750041c942d100c41300b410300794801c80c0c0507800d820031120342e0300018030b411111104200d4540103040c40302c000c6d01c01d8040340e61000d0326803245205140c00c2584a602e08102c0840e450201d500a110040c00c0301d98800c000042c3e01c1c0c031004481c6400c0b00c0030786001302040c0e0001280c0156402140d000300f0418800c600d40c0c83c152510103001d07094401150381c0d007802000254020341801d01580c103240040c00201031400000700910001080e403401181080100c110f803e40205c99109550340c543c4190301fa024114804800401cad01c0c4402c90500000c68200c66100317070300098000d05903401401590441124030222503900d01c42840000d40190007000b0b20640011500d030701000f806654140101015074401d0a208103810038204000c898126401d24011450a50070191994980413044a125890410080d203d4040248090401c1078070300f80d54900790b122008000d000c400 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 648809757 1250 648808507 648808529
    0x12020714030d0518030a02070611100c02071e1401050a0c060213140d11042403060b0423060d080702030d0c02011805030322030c0605070b0a090210030b0a 68
    0x5070b26072108040e10040d03e142c04e44414042c00390341002d001100b1075540d42850b800804415141078411101d03200e000c1c0c0c6160380d40c040c90040b407034000401d01070003000e024503500a2002d0303818407034045845415100300c5101105801f10030408002040e16030102001c0908060b80c44000e0b010040c0e0b017800c4c1c013400003404039200007008080884120360311420785400942d4080500800707010303c000106515405421064a0344a41100d45000e4001c00d0041342c13009290900514880088510b5401c150000c6031920b4441c640240b0768203052158038110908070007001241c13480360200400300e140c00f614442c06100440e520000703200100048031240c1d50b002d800c5811444104000030041400010200d0018002c4044e5031900c500a45054058410040c003541c030b0801d040c2c583e0202011400c2e40b41d0340340285131000101049400340340000401a41d01d41d6503940546241ca034040312002071501110ba1f10384030030b00c1d0141c0c0b1008002000e0920b203060000341000e20354001080b1851551081011302 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 648811007 1250 648809757 648809767
    0x30f0c06090c0f0603180c121c0c170f040f06020105150a060f1b0b09030c07080109080729071d030d02120f090907200a02011202071403 60
    0x11000080451041c100c12040d20048941030041181c01078001c00c41e21390181d0b043c401318864900341d80907040300800c51000c507485480d41d0b601080131000d00c1c007043d41403504036480316114420362201d000c0f0301e50110702c5c02807504c056607036030070b6081c201c640410002c841d1302280000c550b01050f001c55000d0320b01210305280c440e607181c030300901030b2004450b041074080040c401d904040c18180380c0c003410340c3d026451341001382750744050490300103840740c0c521283c142e0010600740c081071001c2425070060400070059aaa0300c6452107181c41e0540031707803104a40c1e038500040e55011441600c00d035000a42c1c032042d0300c003164001c5d08001c907805040408000340390b904031042c041d07415000421f100c9800e03440c0110b1080a0748120030140c40d95169041c08015803c01600c400d98580f07450010329100403180241d03130518410304081582c0d41021101000420000c840c00703000d00fa00c040d0303000e0404860000410503101a075000030688460032401080d59600440d140040041004184a074940e110003207a8480d = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 648812257 1250 648811007 648811027
    0x2061b0706110c011a030d050a170405070501080106090b0a030f0b03010c02011a0402130308031314070611010b031b030a02060d1b020601060512130f030309030e03010605130e030f 79
    0x766100c20284145917180c103924107021140818030f83d06203074004002d000c4004200600b9130f0140c2c4980101000c100007407403800b0409150101841c00340340036400a0082a040200240480c24181c1203107013400403500040100c1b1800804807070140603989808a1034070340e4550800080c0c80c0c072800c21035141d42014580410709505501690070650000c07149001d609948042c0401c80c440d2040c898080c200f030071000d00c0440d8402c4001c0d07800403501d81109001801544406102001401c191003490b004008200710321640103480da500304484070020080401e040c00000e59a1803510109981e184081c41c2d4000f00741c0e011300c00c01c0c6a650700a0300da1a07503410200c102c0c5000b00280c4160b8000070203955050441c00d071000502c03d045e1041a21280e1a02045180c3c0404042c00240480e80300320000c1c0501e000a075414a142445a00c640ca0119a2921034540136003442680c0c070038070740030b80c0c5090703c1089960740b001c540510307840240d1000145d080483e09080c1c15840707140c8001c0c004030740010b6070780c80d4 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 648813507 1250 648812257 648812291
    0x30c070f110303071a071803060b06040b040b03070305070323040213020409020309011127030102090d1209080c010f0815030a08040f0803031005042d0f140702061b0706 74
    0x5003000034105d511041d41d840500b60b448200c5c1ca4038a0421525035102030000a000f94803084e0b183d0380042107581025603507019446264820303000a00401408024405d8007078040c0112a00811203060504c80f6000003004240e03100103041100e240c092400001c04c06540304c80031201d402406c000c1040d541c0703179119416a006175105403110b134615844c02f0802585190b1540948241420f080340d60f11089144900c003000d070307028070082c09a15550070030510711a81d071000030014920b0f2140c0c030100001c1c1d00510000d40524040d5224000b1500240c10003600c5a81c03000011600c00b007103092500d4141c030b8103100481c11141c402c44003501071144d500c240050189440150048941c4542c030408101c1d1101500c54481c0029141201c4515211000340010300c0d09810000f0740ea0101850030860160b1140b400410504031200c54480c2a40d52010391820541c2c1e00a01c0e841c00f440b084040303021300705810003e60340e00004140441d0f102c4090003a80e01007c0450488050f51703040002031020311100001d00318 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 648814757 1250 648813507 648813533
    0x21602010912030516061b0e011101090b07050c01021e04051005041202040e03090a060306090b0a03050a030e0307172a1807020109020a0810060506030c070f11030307 73
    0x1000c5624403030002aa54018840a0702c035540c141e03038030303820810103191003010098464400c81e039494407880310615011041184c0b006000c510b036180b20011030040000340c004940030003221001d03410998164042101794580d213400422501d052079644152244031030080c0202e1f1400011207950040318880c0d49011340c05003003550011120410303051511032090360144500c0c414403501c03030321003805180585010f91150402d00c80460a40345407181a4001800c91030140e00510b005c00e6030390318148010041845034082080c003c0c0c541e802500e045440b4a40d6404403410004d0400c40120700a00c2c4648041c06072400815198827415407601d401101c254690740161a008480c1512004411600d02482c4100f658003034080c003080c5c01180070b14a8813130142d10080204081d592030f04801d030010f0300c1e8046105c0c01420700402a044441440c0c030b120307041d503040340e106510500e002e105020a410380201222001940210481c805851514080b04860441c2140b5641804082004c03000e000c01d0710340040b = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 648816007 1250 648814757 648814759
    0x60a02030103032019020a26010e03040f0306050a0624170408070609050c1002010e0106090b06161719140c03040605161212061a030a09030c06021602 66
    0x40700c401c04040d001c40710031044c5001e0b103060f81e00c02c83d82011903842018540005900160200c00c00d00d0300d6000324824400c0350340d407040d6550406044081c88000030310039030007214a031401962805141000b5803c0142c1180130291500d0390700c00110f80e00a40c0f55105038024107202000301c00850f1600035000d20000c50800c0c2c000402c0e26100100b8203071291012080c403072079100d40103601700603a81d01d80d0401070041030390403500c1340328068100d0310f07503698002d848816052039400070540002e8549100d0954500d603205840c00390501505642d60750b641403d03540c041d41d00003c07581d00d1003400d007845030b104008090f4800e00c0c09000611465500c0c200c03115514443e1261b00c40c00c0b11000089010066446038201d00d510300c0d00140820f106071481040144641d10780c914007002c00074050349600b02454032079003e20020669028282000400e01d009000040541074280c4500c0c08115000e1102484020300b41c45e01140e89403c94410076000d810b0030741415030400c20864403030083c840030401080c0100416 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 648817257 1250 648816007 648816017
    0xe0a03060c12230a0c0903200a14010801051002070906090501090c0e100c110603010906061d0f1012240b0f04030b07050c10051803070507051011060a0203010303 71
    0x1121501ca5601c0b9284406100b0fa414000780d980c03040c420300300900440030f80d001001405035000011981560790f41c103a802c807001c50001a070ba014410003000851f95404000c05607001c540c130404680c0c2145200741111010386000d913450000000c00c900701b0900e500b000480e0740c9400d5010030090080e0b400700d4161503110307200308960b24030410b00317460a180c1e424131940c0c000c0c0048109410b00780f1900e202c400041c4a00e407003083c51550f00000070b03240d40098014095456441d4800c002d4030382d01211220002c607a400c0e0300200940c04c800840c042204200105002d0f881c1d0700c0e0013030101840342c1c80c54400c032a500d490400c800a4501180150b5000480c40d1445986424002041003101e0204803220180303a086410f142504e5a6199808140c004110105000e001d200520a210091002800340c6e1410103001a83c1d1400c882c2514556644181e010800d0b03109200010004e000000c8070419141300300c80d0141c049800ca20708035240302101103800020b01481003408042c481540296060300d1103a151 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 648818507 1250 648817257 648817271
    0x30a02010e0112050112061404050a0213020706060905040c051e01051e031003020103050a06140f121603060c0801122a0923060604090f090812090d09150e0a03060c12 73
    0x8488e5a01c0c0040d10003820310b40000c03d1220040c54520380314410b44000341009420100d840d100d080403104654402c0800315144c03c01c200400004401e064042e21041390010703802c0a000321401c0440f5540d1000074140a40003c01149a000104550544511403058642d4a18104450421030081c5100407804031782010007044003106d16000e002c0c181e13034044103907d4070094800104900e44030f03017680550304000c3c44442007540c1c2a007809588907000e1034080d400c88031895842c0010854080c1c00071441000300d00c60050046070f204402616103a5006060140d601e116a500d2002502c0c409a280c0d19101c0c2c0ea000008900140307800c106a08a9810041c2e400c401d43c250026018840803540130768071010402062100a0f42d641c06006001c905003c005140d00c1c8a90318480d0640c040b1038071012003040c600030440060010040b0010114061a01092180c075084041080031030716031500041c0b00300014118815240d041c1e010005680040d42880100440034000d003241c40d520440d520002d083c051 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 648819757 1250 648818507 648818531
    0x6051c030f440a0501062f15010e0f0601080601180b03011d0108071d1f1211030a05030d0905120409050f1b0f03040f060e0c120c030a02010e011205011206 68
    0x410135040b82c165441c2d07020b01c40d44011184914a13008000c542841c1d01c544448020804104148442c80284418044c56941401d0740c2c4040e030f0000a00c170001a802e40390411100c2c0c0da00440a540203042030a040c107018a45407520700391a4100d400c80c500c0020044000140c814a9824041500d0100c03941c1c43c0f21a41ca445105031521000d0198030031001000002408031120b80900c01d5220100391041c1d410403881c504000300c030800301d500c0392010100c070b81d03049014803d03180c141c40384100c401c8008011506299568903224040e90150910131507556440e42d090007130600c4145401d0701154041d942d210780342c04089000300015200c402c50a404500041d0b5184c40c9500c003000200c244001850402003820104106a030000300100e42e6018002c1a10000a0440c080c600c4105403840c050000c400c1d4020510201e20724890740640c031303039100903a55052920f0120715640340640a180c03010004201e040144c1e000010445504142460040001071004420540745a014800c1c0f03810f0000356102d130 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 648821007 1250 648819757 648819761
    0x14040240150507080f0d02090f220b01051b0a05070803130315061509150302071a060103141e0c0307020c10110a0606051c030f440a 58
    0xc0120555120a0001c40e40800d010304041c0060f02d200760f13000c520303084503c10008040d411040c001c00d403268021400075a01d00d04026241760101040c0c880090748400441448803451441211904030342d0307a01324044050348602d003114000450003030b501008a0350811015690040050140c80070301441d0004140001c01204032500d91940003800d0707605c1da0941d2a0f001d4203000001c0000115a0b98200005016404468540c0c094940392210b140c0750703103407225003050848040313010000c0602c10006d10b00020510148101e0f4050f500341d110000381d54410041c0c00510f03d01c50001e080c40d040f40c1c02c120106c9503080240d110380d02078083c0c003500c6484407a200c4107140030540f6140c1c0560004000d903505403c1c0048140c240120b2490000b03c02c191001041d401c0952074070055038200e8841c03800b846982004041012805002d0300700c84401840e070b8800400c80202c5e828450104000b100c01c5218610700b1142000503428590254009000d00e6124407800301050b80c0341c9006d029081001800220240c = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 648822257 1250 648821007 648821009
    0x130504050c1e0a180611061005130504080706020304050609010c02030f1b070302040e0c030f0c011707031413030f0305041214040b0307050406091a0414040240 70
    0xc240c0c1800d0340d45108602c0034090b0400076a40080103c1c0c200740e0403919501820b0040140219165520f03840010404282446002820384d28007212400c010081c0da2100c0c0c0c401030760025440d07000100340d1141d01d40812503101d0300d1005003c3c1400030060105100000c5031450040c0002c070000c00050140041c16a20307405050b202c04103a1000703100641145409130044040c0001c1d210542e080c1d82d8403940000c04503012585020242d0380104c0500c0c0b0a400c0c04c00c2006a0024000300400c600c8034144002041122005000e20aa58650003c9000240030340c0145140282c04007200e8031914240a544038004030964040d000145626a46450300e8002c1c840d1500440c0c02c0355581700303c2e50203c074054901003a041070306605035204210015002080401850040c2a00c2e1b68003540d4502d460030083c610034140d00054141990414800300403484201118120780910980c1048a111000014000d014003060484c2d00306020001d6041e90849003030740022041140c81d13155954410000304100740d205 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 648823507 1250 648822257 648822277
    0x1204080408060a1404080f0d2f03160f1803030c060c05030405072913060206010503070803032205010515091605180409020a030b042d1202070803130504050c 69
    0x113a0380224010805420040c115190392000f454640510a0198400c030b0788c04611005800c824500401c40502c160800b2242400c240ea0841d82142002e6400d545050850a81d910070310181d00808840a8010386004400c9250701c202420566541d05002c1c0058584190440342c00d8900151803003450f0186090740d0180da08000241107444c14664000d21100f005a40d81500c920100720746102e0f01c80b444000c040c4856070b1000b41c000a840d00380040d280040603001644242c0144500380503201c80001560703801408030b0544034240381c800b004007180d84801c8602030015420702040058811210400009200c070545030703a285503031034000c0b0140440c080b0f1821000198104020031030402070000c981c125203030081c400034142c09181d000074a09221580115011540344c020041071240b141090700c929108003003060340c5152000c8865031148610440100509411210008103520801010000d40103203000c81e5a03a444040000380c80c00302c1d504c80c0501c501d052000103061140f00030141c0d808080 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 648824757 1250 648823507 648823541
    0x305010b0d03020a200d06060302040f05040f060b18180714060d02090f03032b05040b0106050c010603050105180c030c0f150c1203040231111204080408060a 69
    0x5101d5a1741405a49603001d4030888200c100d0a5000c1076484c141c01904083c0700d8880000c48910358410701058480c05a00c00c031482d03207400100408140c6100144107400c0c3c0c080400074144d62040300084220000202d240800320303580f0100440141c3c040340080c1241032200c12503848941c0c0e0100d100380d0000c641ca0181d0030110a03c8694590300c1c081d0082c04004500814400c0300c03070080400f1038034542041c1a41e161240001c034408000e102c41c0407000c4056080b10006020600c0c0a403600903100e10b0600c651002c1100020301042c10600a6015a0185522070024825804c081e10306600309031224900d0b40d000d01654515940ba40f070b0010b002e0005038809003101140024010400030b040d41c20401410101c0810000d81141c5e400c02d10450807036005200e46191a410035005018100c000c10211f0311040c021484c9250715032554000c1d5030b40b4000c103001c1c04100800f4841e0080c515004004141302078a000200303020400c988040035100f034400440440782c4a964040b0480701382d40e00300c4205c0d19098 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 648826007 1250 648824757 648824773
    0x22115090601021c09051002030a08180303010501212c01051509071b060507090b0c151f08070302040e0312061003020c24010f0e150d1b0305010b0d0302 67
    0xd04520002c0300051007130402440f41c03130351b42020031400080c0c1c0c40185c0050b0030005142103d00d1b000103a080d0403a60f4007509035601c9400003040e1b503403480103003e12410301c0407503c980c1c0c0c8007580d09840314082e802c0a0703201780314a0f2400450345000110035541d8034003e52650f4083c00001e5814412a442004610204100046128144601d103000130740f4176810054081c00d24101700080c850080089489400f0004103494410001407080030300740c02842c001e0754108140e81c9031a2002034000d0031611403140c1d9030500e0319420140149030304101c0d00000300c5a81c84000060044010a005003224003e49003400b481c40718060003a100e10800e840700e41031241090101c1e446080ca95054070700c1605d1401c00514141184e0026481e014042c0358107442080180800701340300d08a4481e00b07005042c4c0d0340250407060300b084605142440e008080c2c4802e07802c00d00304181d80340d65083c50b1074110750b00030012221042a0b000c1506100e10203000960301582410b014020710304001d0709207044280c060703020341204 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 648827257 1250 648826007 648826033
    0x1005090901030f290a1107080d0c21050402180405070b0702010c0605010806090f0d120e030405060a1d0a120b1009020c0102120f012702211509060102 66
    0x1003180c3d40c0070344290300319043c84803220440d8024101c901c03040318580082e40c0f8088000e103042d44d446c58004c003c45403040c004035001402030000d807401c2d080074a00c08241c140040104540f011800c14070815124030700640c41d4072007011507100d507000c2c500070703107100c900b444501003428000007003030b80c00070100d0303001290401140034040c1c003070031150748145041008036000c1d4650b082618804e0304810000e40029051026541e010050170862400070300180403a40b5002ca030180c9680e4520b50343d040d003140c8039544500c1100043c011680a403000400c0191920307000080100b643c0c103105c050300c41e1071085a003d244146040401882240e0f1001d15540d49480503070382c3d400c1a8407006d071190040c170035480404100014140060300540c0811000143c588041c5080b8010007100079008080f5032520000512170600e140050252013091020300d0704000e03103401c082100a05c10252000490101282160890340f66003149501540300c0c410100c4500c0750340d104000c20a84140c4425004d40d016082d00246 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 648828507 1250 648827257 648827273
    0x30b0a030b011203021501060305070f03090b060d02011106070c0219050604031101170c0a030f111603020a050a0b3102040c0306050a0312091a0a0507080417070302100509090103 78
    0x1194131901c15038400a02082402c2e002c0c21083c0c0014003c69180e50403c448503520810100400203149014803a1001c3c0e030312402c00b840c50140c1294000d0400002540569000b0723001404c050100ca0103c070414545210020181d210142c8100d100c0ca64030b00005910200740d80c5a5000e41e00c00401440c075242c0b455a600f00c1110700074081d0380c180040c411510300c002501c01070300392051990303030000f65076000c082c00010102e4280008005040c1c1c94108600045151907050300c0341611246561804046036040691404d180a0b50040603445581c03010341c1000050b82106001c1c003545404901c0380800b81c101d95465208210b018081520214605805860f00341c1007203644900c507050009000740c940c404107101c2c40c15900156000e400500c82c60088551080d650f000030807103402c070441d101e509510303000102d118418a0004100020510009000c91320702240c00500307200d01c800d12505200d111498861065102c141c1c826102c1d03d04212809015804403a001180102a00b91076804c551390028 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 648829757 1250 648828507 648828539
    0x180a050612030a02010e0c060c06040206032815090204030b061306090c080402090a050106140d0b040606022521080408010903090806090a0201142b0b01030b0a030b01 73
    0x607114160038501c040340c0a050004000030308066001080030216074111601d0301450172621402480d0800c4248804400820881d0300f195040710255a0780c2c5450001004401408141c0500c0d0200890741084c00f5006a0042010b080d0100650034107664408a8104030300861101901ea00d40d40700000d0102d15050a907404070441c0c0d0500051980d8480d02c0c1e040071140d0201c04900031494610038001075241c400103882d80448905400d0140e90b040440c02000101a10300051842c40041103202d0022050f4000103e8003030094010442d19558640003507039079030441085650b00c0d1020384018100c1d8007202c0c5002c107031060000901a214004104118148191441a54041410301002c90200e80a020303410790240299584001a13007001c5005003045c02c050304541043d40000600030060741c02a0a5002e0741241518003611458040040b440c0c0c1200c080c5c1c1c0d41140d010345081034000d10031a5020070807031502a0b80c01c0103001ca2820501c590a0000c0c0400391401ca102d134010001c0401c1640150 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 648831007 1250 648829757 648829759
    0x606090b03250507061a0a15021515040e07230a090c0305040c080303090c0906030f0f011b08040f2406150f050901080106081b0d0218180a0506 63
    0x800071040018502c1c00384900e020110004800003110400d0000a014801840c0003207160514464502e00010720f0014540c852205521202281100d40c18000d002d0741c6546590100b0300c412501d07102c40301100c2c10901d40b200512480c0b402c17681a1202d01d001a2a81c01e41d00302401462a03034003210f1500b904001c00d910a154003c41901003c0f9080301c00d40180115841e090b28042003504081c83e0503201e0f042e441c0c000c1c0340340d07510900810001007400500d150144406681410303042c0c07210300c0403d003007040302e01001140348900c0c14030b01d020247c154040348580e11115044205420803000403241070b14142d801405030000c98580c000803400e0042080c10042c0f210217038540302c44000001505030768403640107075400042c501000303001a1f000b01c0100c3c0c882000345415442c150003000040e0185006004040c1002007480008140e24a4075a103a42c2200d5018020717521350880240c18000f03540226002c03072003a030716070400d807a1a00b001800b040380c1708100300c20b0650b40d41d14800350728000d0400400701 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 648832257 1250 648831007 648831031
    0x2030703140906071407060908280c0e0f1504090c0e07110a051f02030121060b0301240806090303040b06030102040b0414180c1206060910170702010606090b03 70
    0xe4001003011601942d880d400c60050b00b06c1c00d14081340a441c02c542c59201000c2a085484c074080030341060303016440303201c4106040e1818002d15041050346c48040780c2120021000e242c1c140400107460408842c855030034031803100324030042c040c2404182c40444d20000c0400d070700c844c0203000344038003031120035480032051a0030000512580c00035890400210410340d02c6800503a4544846001540f5034108500010400d5140d545021020f10f1100410702409840c1000111070b42d00708986038114140400c4018001d01040d541c400910f03101d50207e0210740d6140010603030008031701c600400c9881c0310f0a2244003940c150b9449441b51200f0000c000d04007039041d5400c02c000304c2d01800b400050000b41c0030004144c5828840c0509025401d1042e0702030b20042c0186400708a6494012030482c0c0c22242d011419a081d5211040850114094031001c2079000c501840031411503540100c0010f07280030040c880d106161522403041c3d0880c0c0442c025840000e407400414490380490b44002e68100440c4214 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 648833507 1250 648832257 648832267
    0xd1103190c0303120b010f05070c1e180b3d050409051f06050d0f06151b0507031e0f08031017190c170d030c02030703140906 55
    0x12401251000031007211102000035042c4107141d0300844003c403640c030380c520402c610940200041c2500d18078129400400000080ca103007005400340d5144000c1041d5406000f008110082d0500f16a4541c018464981e040012031619030480b40a00c4000e0400504610386c1245180468894000c400851010101842c5e0801c3c0f004076030079568039000504c0d03036510fa80340ca0424400350103444015041032241a0711640318502c45801c40c4044088a100b03040060355808100500c0c00a4080c07295800b0240e40f42800002d00b0304912038a460f0305546560b185101c4e4403203152006032481c89a90003404542c0700791000d0000900300d20703031414a000c0302003080d0400c50007a80d40c1c1c4180784100d501122143d201000b13019840d00c4003030000015003c00e140c080d00311250744034590340c1d44a0600d20089003000d0145d8120a00a01e40020009041e005182060f400310a080265840c1100f00d40320000904d04940301c0009840030095a949650540d91074191030f401036583c0580c1d4005038152075000c101080 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 648834757 1250 648833507 648833533
    0x80f03130b0105030d02120309070b0c0714180c18030d09170705010c12032910030204150305070509040e1b09010621020f0304080315030c0d1103 64
    0x514854410200d08400c000a98039000d844403006a100900a900c0038002100b181e0b0040748280354041800104d03500e941d030350040c0700e18200d49640910320548000840c0c1c1d0340003d0111784c000541d07030070001d549075402e40c0d0300511152581c10719603200c501c10901c0200301114210402001c200e641c4042032401761041500190404040e40702200111390242002c01c2403608440051107821107070390181806502d84800a0030398100720b0001019155006c81d034040c03450003644080d01211348151010b008000e00a8805101000c0210580c46a03050002e1404424400d000301d6040d139240303040c42c05024032034071390070740251030b000d031a03c018000709000102c660785a5114205001c8400001040c1c51554501814510040b072008903024a40d4140180003542d013117052400e0ba05005031803581210303641e1305050005c1c080c248a0005880000003844184218076001d107000f400300e4038108072480006400c00d03039180c00e50203500390003c60440701c204c0414802d00c00c40c491b13610060151440840b00302 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 648836007 1250 648834757 648834787
    0x901120812011805090f030f070606030f0b0a05010f0312030b030a0605130c08161e180c2601210f08120702030909040b04060e0601090506180c030402090408 69
    0x181040b4841601c2d82c24525001240e4041c1c642c21180400140c02c900c01042245d5449208d0901e07540c83c02e040004649003000001e40c03040c0d00030b60300000d8140031880c4600d4004043c0b0000e07101441041c0c00d14002242d0034049440c9881200e500c000100d1042e140c4d071a040e805002c3e002c12090349070060041800c0030a815004003032144204d003012403041003107460300c540030740c50940028440d940030003c40100108698881c2e07040d0743c28540c890007680c2001054404c4083d1540002455007902104648284000c0e0088800100545c4070740c0b030090340380301801c200380841095000551100c54010094006c20404548504500c0c1d050020602000d85422088802104085841071170000c2c01175229204a48140c2c3c2000c000d00c09940f50031a4000095600040030b0006813034448241c011408118a5521600600322004203441096039115050001010b049030420301840c05a1103400da0025a41280d43c401c05603843c03418115107440d02400010780300204202c9400008000301a0504912 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 648837257 1250 648836007 648836009
    0x50108060417130b090114070209180703120f08070c03020618030903150109051b04030b0c07060c020c150c03042d0b09040f0e0a0b041b08030903010c0806090112081201 74
    0x207404c0b80e603a20a40140010100ca00b02d084075600316905100f000c0042c1e603005003640c0c2003810a1901c0840d40c0d0460743c401e040800315800200150040c0c01000140d0342c200b0600256035001d505d862074982c0d2039100c04c1e1420200032100500603003240340010b12081c180402044002075400c116030402e00d032203007c40e1800d2001111458066103040040011049034040e5640c040107180001b54044080302c00766816002d1800014004c4001c0742c0002c0400842100750b49005070001c100b0310040701c080b01d0282d00c90002c1030016004420004009103018178a004503001d03030908800442c034140c5405403940400c10340f6000d01d40119214411000f9510003440768002414600e1005030b600e88210041004451a0b40c541128407810030f055009814404142c0220b0160480001e25507035856103031076501200f42c400760741c1c0100c865040c0442d03c088000003415a000c07080e40204400448000d00381d0700d040007120b01c40c4e4049403210040c0080180604a103200622440400e8104208481503841052007 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 648838507 1250 648837257 648837269
    0x30507091805010e01120503041701090605010311040606140901030b0613080609010c02070e19090501060909050c090411060c0f010f020a031d030a0e030708060903030403080a05010806041713 84
    0xb40d02c010301680054598090040c01004500c841100b03942d42c6094603400b5500c07448885880c0c441501d0308104082d0052002c01c1c0c0e1100e0104825a128a080407021900055480c0900d2412201181c241e0044c0c212440d44c85141800f282400300420046000e01404c0380c110b40c000c2c1040c440d60b1001410062928003803c041000f820092070020310003070071190300131010700c1154050703d401c008106101c91450340041706c0d00701040712400c092a003040a440ca40000901c250310740302c000504050507522180405115105071010710108000304404c480d0240c1d405001d8600240d903000042c9000d90040450b0f0312b104044d84c8040795400e04803800c4070420400d80107460340000312007410070b6252080349000108550703034103601c003803000ea400e80d03e00541e2048810300041d241e100c0b0f011303501000340d0002890400c00b2242a443d00d0300c0380540701d8106a800314003040c43c00740880d5030344180303008281c1a01d00c500001c0c415560f560b12900d18901180d0603020382c0c80400c201240840c500300071242e000e010 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 648839757 1250 648838507 648838511
    0x62a12020a0210020625020a1406190203060f0918031801110307121115010815010b0f0a180503060403020a0201081005031f02190e030616020d0305070918 68
    0x24010300c00d02000d00d000100841d0096001c025a4a440c0c0c2e01030090208444086d104840c4400800c2c1c5c0741c10494030001c0c00d01e0401d090303800880c100c0050907038800d98800d41403282981c8403040c400240c0c001076480702ea07c80c00c07020642500d030400101e155449009650f070b09128498607030300942554040d00040c240c0e51160888401c05580042d60159940c540200071480d082c90354461350b881e028203003a1001044030b08402c901022004000c00700c110500b20106071200d50b52a84102da403500e420142d00e0311901307814000074803809248142c0728004d5400d045680713003200340c100407107a00400001130340309255062800f00b403d8170f080241070300c610303c660001c0203004068000900f15030001404010400300ba031138140200e80300130400749001084000d14003016422841444040d000d41c41c50040c00c03080741914007501a911907400840c1c440e00307a0540741162105405203544d03160340c0c20f0400142e40400000c580291280e88107541c019541d18024174090b0b164500c1c5404181000d0850300c4030b80d = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 648841007 1250 648839757 648839773
    0x170f34080609010b010f0e04051504060611010c020a050607030b1504080303090c04180318090c08010306060914060f0a0810020a0201060f05011b1703010b0a020c0109062a1202 77
    0x400e0912404d07580e58400d09108142c91001c403002400030121f41005806039481d000410841034001e014100034000c010014403442d522084d00905a601c40480340e5055070900002c4840d1070f0002ca01e00381c1458025000d07180a07a141901540541307014140355400c1240144042e070314a5480d00070703101030030607000a16541e0409655440c0f0301400c6401003445503151206090480d0250081c1c005040d40c1410442c01090030038411482c522415130210010904040d101d45229620107480360589100c1d00d0100034141c0c4800344081160408146c0e001c1c8100000045051480d020718031101000000300b000c0c0103d501c0311001814507101036006104103401040f4000415028007900f4003500b8906002d142c0945407a0000f00329580c03540300543d00d02d40c4091880c1c140300445404103d0312010204a983d40d5a41d182e10302407035840b540003240140906400205590702c980300840031502155a411440d24140200c011040c4201c2244052808040c07504000510307030b4621000c1c6181c154010302824 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 648842257 1250 648841007 648841021
    0x7150e030c12071401030905030d09050f12030a021605070b0d1d12130e040b0601030606110a061d0105130204180b04030810031b170f340806 62
    0x100d0512035100b8440d60128415142c034100c0000c0210442e1020301e50b00c52040803980069000340b01ca540050200c0c08001004802500181c0207121514400c2045400c08031141d001103469a041c20603507074800d08100041401000250060f00348868030098410840300190345d00d600d05a55503021622202000c10340d5030141c0d090344102c0c80c5d80d8a1010303113004038000340d041e00b03a00c8840402d803289040030003094180b10301103680202e4003d00542c104403035a0b42800c0c24000202c800483c2c80702d001900340140440c01511503510403840416030802005840300d0303681c502d070103000c00240f910540e04091016810300182405214041d08084141100700340542c01070001382d0b1480c40725a00204248000e55002842c0c0443e802c0e401074061605825946032103800c00080d0a45030320142810f001c3e031007142c0341041d103120460200c0f0540001c128400282030030258580c0c07500300081e000c0b0340212030704940c400405008010a070390101c1410b1011107208000812a0762203401c48042d6a009100700091 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 648843507 1250 648842257 648842263
    0x1215030a03080907050604060203040306020318031611102012280503060d0f08040b0d050609091605130605060309030c01060807030b1302040f1b180b0a08070207150e03 74
    0x1e1702064585a20780390500740e002c4d50301e00c510b200061103c0d6000001444600581c08640d102d42c4026040d03d07910070050700303030703122411000406071034044090394104c05c64580803160350f00d4880a41c4903119000304280c003602881b003200500c607840f80038480c480c040e0400701c0c0b0010b00d004101c035101c80b5a106900d61140542c011710032800418403400b041800106e64034000b0240400343d2242a11401502503e001c0d5071030b0096070f105151504001c61450302c151010742095110b45e030140d0b40c2c00250380d6000122603aa03a00540700845407e01000180311b1410b0410136080c440c03003800c401041030740d07454003c16220790040390b480348550000305158140d00c8007801050010892480140400c0c0d0a54882100038000603020141d108c003004103260440d255600003080110b80c800c0204804850307410411015012100c0d41000034424019059280d580500300b401502c2d41d05014078107110500d901a2703210303640601600158806c1c4800043c1d5a03914544003038000500303648001c5150720f204107040c5 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 648844757 1250 648843507 648843509
    0x2010c05032b0e030f03220f0b10180e0106120c0509070f0509130e1e0708010603050c040b010908100933050c12040803180604081215030a03080907 65
    0x114560401407464100b6800005079a0604d00001017150f498855160051402034400c1c48012480c95003101d40303092140301010110154041c551404003540c031103076001300d4074071140180d41200c0456009400c0b180100c0c0e1003081d00f604441c2c000900c45888a07070707004031180900004c4841141300c1e6002d1101d411700010964100106041c001c050144d0401c0290050050980084c040d0184074104072450003140c1050f007004943e2801d0f40c1000103081421504000405541038040c404c0740000170352001c0500c81c8104494000d000b42403070178000000c020280c5030f408051f80c100b104c140404101c614081c810041c142c1d00f910800134203c130b1246000083c50400407410b241c00590001807950f0880c01c035400d40c0700b50070101c0001503540d8a1608400c00d030700929500b5004001200c041004200c1418011800340c0000341c0c581140b20151210569605400c07100180411401d01503021800040d41d01150080006074450441d18102c0002c83d10b032a40400c010f4002a40030313414800d42c0501408210 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 648846007 1250 648844757 648844837
    0x903030b010503011d072703120216090f0603050615010905040506010f08090f0a0f02040609091e021819110a02070311040b0a0312020111040f0504050402010c0503 72
    0x43c21503150410418106072141c0041c045840d28400141d05244540030010075103904c800401e208050b180d501d115081014041194450a0251304184c0f49000050b84117100c1410108003c1c2d040c00c0143c580c015140407044e00e05000c0d244e11000c000a981404107038840c800da08002c1e10b603042c0801c00100f94650761391000d40213600e041c09004031640d00c00d07550040b0020303e05060b038203a11880c140c2454604002c0791150320b800750303044d5541041400c0350510700860088070306100c481e8940d44640200c4410803c014a01801d030400d9505041d01c00e000d10300b0140c0024038010030703210101c508d040c0c0c6410490310300c0b985101036802440c2021080c400c61062907109100d09082218262010350359100602000c0c190008928000e109076455800003079601c1700150410160654030314000d4200e85220140c8030140d4200441000d003a95404180e4040300e00c104c0060001d140780100340401004080c0c8181d040020712900c20011030400c01c001c22070b180c070728482e81200d050590907a82850305045c00c04 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 648847257 1250 648846007 648846017
    0x70302090403050a091a09010c050a02030d0c1b0b0316030204030f03081f27090c0b120a09050a03030911300102070f12091701050a0501050f0a06030c210903030b01 72
    0x40702e0002c20000607031f11403802c01e0074410348030605418494a8415000c8000754144140e01e80002081d5102e2031203401e03075101e00e42c81a0036030b140100c00c2106801d00d0003082d08040c014400200c0d0910441d203c12059a102c1c200149000c1d16601c1c0c0c45048c801d6800240d000c03600c54820b20079105a4210380d070a0650b005500601c0441c00e002c54010100c0910100301c6400d4007054580d05a15484e500c60000c169001010100d16036540d40740c0b46650b00f005020144035642c010010700c18106500459000302e038010050446041c2d5907a080c1c000307122041069131120611450030318551a03140c0da0707410300d0000e00026603130810881d070042083c4150800da0021640140a2040001d03600b0030301d49001507101102482640c41d204048502e41c0705903009981c041d07440700c0f502c40800c1042d40321602541c2080030910950782c864084c01082609200b80d544c00c000d03200da0030000d1522030b80c00800103070018038207602d0022401034001840700300410b007606000d0340c6000070005c058261259643c00788083c241 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 648848507 1250 648847257 648847289
    0x50a0915021e0c0f0a12020f120301090c09050d050c040f0606171b0d1a0d081903020d0c020102092821080705010b030705151605070302090403050a09 66
    0x9800c038540505a03400d442014049440a044941440715104c021205012941c4407880383c106195001043d40c0f07028054010b8591b5000001004549940c0503513121465901d181d01c0c10b40e0b050014006104140d0800880090202e02da9603460701c0c821049010304000d05540d5038640421040b0380302403040031102d40c60140c007004440e401450304001c8a00c83d1000c2c20f0070b551010401004041e180304101c96184002426158600f00c80d88030350140e44080c3c10b83c003d000c0751f090510040000d0741c640134100513804c0c403a20b02c204154006181012880b46400360601403080030036400d4803d443c4130350015035004501d81a01d810844136106002e5003000140035a035501640c030008181060040140c241400304814581c045200213150000354814a602d69810711424500c1c02021180d2815201c0d0051800004e000e02c1c01c2000c0d03503421403038207402d28a0b1007016402611081c030a040101c840d4040c02c0c20000150b510040c01900c114001e84456589055514005004010030f8000506107515940d03 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 648849757 1250 648848507 648848527
    0xa02060c1602010e060d140a06080318060313140120090604030b040627050d080f010909020111030403080301150903030e0108040602130f06261513050a091502 70
    0x404030540e0740e0203013420b01e10300d0301c0580450080d106a2445802c1d16050504540d0104036813140c1e80d215504003601080b141c0e0b1030348000c40d1a0b106400202c440100300d008110b040d07203003000040d82c100c484040d055507a100070b40e59154121644014044503a51f480701c09070010042003000003100d03001d001003146402d1020000a009004901001d0607618000000408000040c1d2040c11094200c0700c0c4c1000594412800d41d07031096a42200311510b00800c030f25070425034025030b0054000c180c2444585501d80c282841c0f02c00400c2c0b85001641080b01008581d10508018070003030000e14041c3ea0b03100c1e40c942c100041c035101c030100f1044a00c05c03c000010304001080c1d000b44c550301e494000b407070144070585503402e000703010380181241070440b42c980c01d42c00202c0582500c4518200d8a0a48610540d20341c6000c2030703415204d03204010003403911080c0010340c051a8000c401818107200a00c00840b00303204d105400110f0340111004511035035262000410b02c20340743c9440381e4032002d04c0029450004130300c0d = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 648851007 1250 648849757 648849787
    0x90f16030905210f030103111305060a030b2805070912050a0b060103060320030d0504030b0c0703030e07030b04231c020c190512010203040201050403080c01020d110a02060c 76
    0x3e410910072040c4501c2080420352048101c88001c1c199800c11a1a541c5138202203048003a1042020b21420784803000600707250442c01018492100104210b5003103265807212034034420010843c3c0105683c10a049400b002181c0d9003440003010710701c0c006a90b1400800c0900300500e943c00940440300061441c1000441c001140313000c0680c0140151510746402c0b0059014040300c3d00002c000c8528264040032201a401c0d100409082c22000c580b0a0102080b00fa200b511032782c0805000700d514800024a103031031510082120a100789400075032200b4400415080c04844d82088400011540a000502c10a410214121401c04002424600c0e3344c0b603442d81d03a2500090380c10004405800380300801c90090240080b1843d0150010100d42c2e100e043c1da910100300d50103107504c0b817081b0b088070740540041407081c0da200750780c1030311000d15040c02d6458514150300103a58499a0b59004c12103190450014080d0351001c2d182071102075140c480c42000030b814240c0003062154219818049155486800 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 648852257 1250 648851007 648851023
    0x18024606110a110f13020304062a1407140d020f0115090b030703140c0108090309010e06250c03050c0102010c020606011808030301080a02030d080402010c20090f16030905 75
    0x3c0b4000030040c648030004542078010520416910116081d140700c0b44600c1078004602c41d40c03003104208030070728083c1d100d98185890700071b809280401c00f80288129900945509800d9400c00c540c5a0401c202503075419030103001110b917038003160401a0841d02c80f580400a008050090348028850800c00c10708000344400d03a4420400900c0c1c6403521040291070034004040603507001190081d183d04c6607942e50b80d03501300380364510b070002e241c03a8005000c0c000f000c001d07500545c405075038840b1800c40d014104003041d0440c25100c403141c00c01c40c049054409225018100c00342c4030300180082c3d1461410020704049130511000e06690622521807a11903011680e560b010100f42040442c02c5105205d000700f6000384e03080b00c0007078400000086004d0a0024402d0f10f030510840c201e03030790b03cbc000d046e0444208100b9107009001c1580211880c000440e0100a0360582100801c80e81802d0100d01c0054900308080d2181c030500c4010380144071b000c041e00700741c901e41500903060500c140d9290783e54850b81c801c2c070 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 648853507 1250 648852257 648852263
    0x50a081209100c02090a200903070e071209150b060c0601091a0a26030a080a020d110315040f0c1b08071703010603060918024606110a 59
    0x61001c2842d031850154401800640d0098102c21161030035081807802410300e4007024001c0c00c20029074103088101c52040f2080114081d01030400a8600400d2220950000e807002c010301c8101c1c1030800344040c051080707401c4103005010a220107103504280d001154446901da40c083c2000b08041e1950000000364641190110000000c8206500000a8180300b80c0d0305040e900544c5d20b400042c0003116042140606508000003003044260003401a55a20840914102160185000520b0b0002a501601011007407201c0420f40784080541c40c4201c2d032085035074215980440b1995480b50905125620020f0a18070f0100b004509840307003d0320700f0b0741d020059130300103006055071020000d800043d10916580302540c103007014111140043c003074009000d5200001c0c070704103000841c48000c4c025041c034150700814181171440d07142c0a0081d0f41c81125528130400c4000c20000700c0701c51250030b010140c002046d00042101d281c12240070384800040d80300700c0c1042044812b00540d020003140820703440394 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 648854757 1250 648853507 648853519
    0x33102060a0f05090411040906061106041209030204060815071d09040c0504050c0d05090703020109152001061403010501050a0b0c3a080114120f0303090106050a081209 74
    0x782e41400c40b40c920804007015003150410003800000351402000d0400d0b684111414808561101012103810100e000082480d51003880414003180e4607540b107800c4901d441c5001c0e00c800b616500803400f600d00c158003a00265000b0599420801b0a101c0c1f103e410036201d181c000407990303240086290f141d07a10300c8803902c074140700400f2408202c0007544982c001d000250040c0a9860710800c41c1c141a044809241c20180c204400600304820103d840030959034141c5072a4140383c01c241203104c0241e42c0c043c00ea000e211400d0720071198030361b11100c518101c03a415400481c0e10340c01d00030058a68400d04070780c140030380e042400502240e5115580c4600751000c2001468440c02e1040c20b007840c0100d9092407202e00309085281d103600c0300443c020400c22012510350869003c100d03030300c1115619801d114082c50b078408548034102d18504010800035400303084040320300101511100700d007140c0c000d031183c559580d9503801c10041410a802c08000811070304d00501210541c4001114091140e628118890700c = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 648856007 1250 648854757 648854777
    0x80d0906210e0a0506010303020706092301050c060103060510050306040b01120201020a0807080306090c07032c041109120f2808030403030603060501270c0306030503033102060a 78
    0x140c4903910400203140c410b070840712102000e0030640c0d20b815003800260f0040c09054004902603004110340c40c105c840000308a076040d4030fa04206c1c0c400c1d80004504604100d4200310b00b0f140f0341e00030040c0e507010314061400015141441000d4900041080d48060300a41040d4100008aa030b243e4040d4112800d0300221880e069640c40106d0616107041001070030100089442c10500842401940c402c44044d00d030f40d0b0700c03030301c0704418007116000380000140003900c040039038400c00002d0b0720750101c15040480511b0020b503040c0d001405413400f030b0045124040020602c8074952902e8101c8549000c1044090500d41503090502a243c1401c50703000440341d280c0280281c01020320f03c80d0340d0415034102d41c5080e180d00349841e00601419a9120a03520142030400102c0d2001d16030701c5c1d40040c484a0342c0c03800040a074140e498406003030f6100000d010300d0b0365980000302003201030005601c907880503c055031407001c0015007000c03200d0040c0e40d4821854079859080e00142c0303e0b44101c440070352480c00d01010711 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 648857257 1250 648856007 648856067
    0x105090d0f0506090c01030c030b030a1104150e1b160f0201120507030504060c1b060b0a03080a0c1a060603180f031308010f020f032a070c080d0906 65
    0x80880030000b4600d1245600b0040104000f10740c0280e07491003640e0170b10901c8000002203041e42c444020b5682c3c5034000743c11010008991500f12500090058404950003004d091010140603859011920305400c0408100c2466500200580d00300b800c04034140c102405454001d114040d0071132300a0490070380c5404103081d680103000940306000ca050041c003030351415850007130242009030b40c11248103081200c02506035025407070302c501e04d003207004c0d4250010443e80c4170403001d0311801c0140c0382c008c0c801000201c041003c401c000c1614800c5521070300305030308881c6062051960b004502c0c01291040005000d0b140e52500308598010605660442e0204c003110803450901c8114140b4440a01c800200c0010710054406102d081724640c134000c20000f0b6018a00b0000e0744141124260892000c00004011261074100c0000f050050701d0400079017504020541202c2c7e0003940b098401c030000c40c1041220040c10440300034101058a070010700b0740d24146010f001140c42411510b43d2034259102e15401d = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 648858507 1250 648857257 648857273
    0x608060f070c0c091a09070e06090a05030a030e090c0304050c040e0f0a050718062d0b030403080a05090316020f0d080f0a03060e1e070e0d1208070e0105090d 69
    0x41c45401c07030f241e520800c0c0d03580070030f0006040811900155515100c6940400e260001c03059103d6125a102d804e9103402d080d080111940c0410b000d5640800058400b00d4681c50400070b0780490b078826101c00c00c0d846465000c02c40080d20040914604080810402c0000f8502194510b1002420790700442c035100441c001600380200440c0b8100d00d032003804000028004002142d20440d0b031140303200d413049100001610141c1d16940980c003002c0b01c3c0f0855080c03111802041d045421031807003101060140e22a0b08180c40c07941305a03420b80000e48114140b0605d0000c502c550b41e0010302a50003986484002e40c8203d00b0703c0c0c12000084d110309460200d2402d50b4035402e500b00340055200e2065030350361003d0000741c07031150810001600001e190083c081000b200d49094035000b00b4080310030604c8511804498192410018124020001d407071146902030f4440d43c41c51f41c50244500a5110f0030000f82400a240e004020101010060801a55259a60800221160304100391030709510150b0303178202000d07 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 648859757 1250 648858507 648858527
    0xc020402121317160803100f0602010207021e090f0411030106030f060e01060f150320070b07050a0c020d08120f2a040902090f0a0902070b0a0608060f07 67
    0x70300105a0001c118400e207982d048100814840e81064140c50310000d000c04041c0640f0b1000103d4200003c401c50100c1d43c00005540c5c8440601074020350b15444234030304112005517a005034007507034010589408501c2d040190303c1900f981e500e01000112051400a2402e10000e081068461076101c00300301072107a4440010515a00580207211442e82d0740303401003070a0380c91001a80c10602d40000c0c95881001805450300316654030060480040c2080b00d0a40c030506280c56820500d42e5500003290092a0b0121009a07150ba141c610b6441d5006802c1c06424150010a00d104014040000e00340090304510024000360301038481000540b440e281180480c4182440c501c03841c0381000412404810440c0c10358842c0d000c4075540440403900003001d08010314080607840f4060001e20060005c010107501806000340010103279501e000c0010702150000c1c8094118003d0213400040c442c083c48100031920350000040c010400c941c904d805030f00c944403980a4291400c40001401154100d442001c03041 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 648861007 1250 648859757 648859777
    0x50405280612050901020304120f05090411121503031b03070501060b2101320d05070f05270402060409020409060f06050910142a0c1509010c020402 65
    0xc0880d0700c54201515291415640c0c6091a0412000504e4070006000f0340c0d000b41d034440308413071086541c070360b0580e912402145c561040210500040000ea0b03943c0c000d1000d440d6445140c0385c0e88200c000f0040c046007400600c40040c10a000140002c2c070b86000044407402448003844a040c034206407441411031103000c801900035801d1203404030707010700700324000c0c6031141c0c00d04104811003100300007007049c0e00000d101d401300011840c0700003d0301c0c101c8420540403900e20940400800c01c120360015070000010f010a80f02507012210134041c051810302e4650181a003200c0301c00c41c02020301e640a5504903414074600c01d42102001040445d2165415a000340050310703825521561911500001464a441003111b42d510340100050310b240240c08685005401810305814bc069102d400d036014070140300398048503442000920f503498010051440d82c081e111404e40403100010040300e01c1c0045e24800ca51088100e03440140b402240c030f00480368641400c2c00d007000d0365003c0f400010004d0040380202 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 648862257 1250 648861007 648861079
    0x13110a0e01090b0f19060e04060e0a14180309060c1c12060609061b030908010908031602060f181f0903030c1b060b040207121e020d050405 61
    0x11500140540000b0f0ba01c0405980060340104a0401c000d914407050003208440c2084400900c03100b07100d0007104801c040040c00104803142d4805680280b140200c8407407018654500001152070324041c0102d4000f84035034900d5020825043d0381c191248a107101d03241c451400000c02440b410414841218a0703420300450b2086d03d258010094030003144001d200401038a040c0004c5880b0340900c0303840081d14815612400b10f107006191803400c0401400054092200017500013076103050034003070b08108910412007561203041820001c40c0034642e0900b444195001001000340781030052114a5104104c4621035007420a075151003030808036180030541080400c2a4400203541c09a002035840510a64040150b9071690008452120080b040700c440d020100142c040441d441d81c00c000d1310b000008100500d07108556a80407404000c00c001c0790041005820068110904010321000c448030030b00241002c00340c1040003c10a11550080a2040110444240400b400c1403564201c1c2400d038400c0b = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 648863507 1250 648862257 648862259
    0xb01030f0302120f0306060c120f041701050103020d031d0306040b1e060102100e0102250b0a02070b06040507020c030f01020315120d0302070813030b070e03030313110a0e01 76
    0x1503000c0d040c0540054025200d04069000c200425204941012800090240c01c640342c02c0c041103030756030004030784407600e03c1f4181d0446090a204c9005100070b060b0540c1c2c0741d50325403604c0c1c0e103800c10120b0550003035400d914000041002d40c0701c00e031400810070703490314000500b00f2480507001e084222103c6000c2e0980308001c2080100124145c0040c000e000d64403000300c0081021842c800c803200d080b41e04e40c0c0142c01920000061540c03a4000081c00c08900f00054200340d441080d190031301d03d900c4900044400c0c0c6000700004d00c00d116003c240c01a5400100391320300005a00d900d0128000940054001e0740d442c4000740f022032003803001120343d01e4001d0560340c4003681e0302c44050103174205842020b1890702c210a81c1c2001d00d04150b01981d20f02104025004a0303210050540094210704010b4076280420010310391102c50b50160500554030401d40000c1c6801c04c050b0007004d0711000071205000394010400d106048982d150541c2c510385c3e120200d48107070201e03200841d640030190780c8001d0402c003081c80 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 648864757 1250 648863507 648863513
    0x3608040b0301090b0f19090507090806090a020a1d04081b061311032a04090203070b13140f0d0215070b0f070306031505060d210905030c0604140d0b0103 67
    0x40001e00011030340c3c804d03034030175034400c00c00038488055500049103040b880c1040020990740005610500908003921016a60111a4100032080701d480d11290820710720b030000c510f4600041c40140c40107800251302c2144819000507001006000500b410030046010000807014013100122140d40e0300c04d071030307060801c0700004400071011a01100e03114501248a07900703080015280704010265034501c2c8229680d103010170f51002580c0301307168110b6101c00c8101c0268804004800003000100d9589944d2074001c811316626042e140c01c00b082c4e80b50b43c0c0c2c8008995586030500c030a4084c60031181c0c01c2100e42280b0004240030a00a280018054045a42401d0004800c29284500b4140d0084c0e151650f512400700d080328050300004101c00741c44542c80200b0441c03075000d01e600007405001e2180360b6819883d4440b44039102854030012400060420030300a500503e85401441b09500a0003621811400140540910700130b15440000c0a10302c19466035405e4001281c075a080b1031000e00300d58482c2 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 648866007 1250 648864757 648864761
    0x60510320d180f03031d030c0a0816020907090807080309010e06090a0e090d120b060a0c0c050312090f1e0d0f080c0c150403051b011806080a3608040b030109 69
    0x1101b6034218299803288403009007c000c4456001411000c1d14040902ea6102446134100e00c1d40b801844204060580058899210030744c01543c4a8851880c8149450700d06486c100964104400d00e13082405003034056600500d100342d56943c221500d544403007452010495000503130f03104d608210070b007000340180c00102080302404000181d444070b4030000d094901500381c50303803019a55000b6500f081001c803210301c14000e4000030351054012103091a51800028502501c00c8001e40d508007001601c00c130f65151298494034882c00a41e01c40c1c054901030020031843e43d648e112a98090540c0315030500070040502da000a04580c0308101b55144c410302c040241d5120181004030740265001d80b81c1d0030810302c0010503602100d03070040c01410240c2c0200c032038500c0745000e940d000e414031000300e81d085088001c02e44160041c04140e0340d0001e0a10b03104c0e2000041c1c3e801006020b540e5070447d1010070280b0480d00106421603852000741c86c0703d40a529221046104a900101900701c002c80045402020b603 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 648867257 1250 648866007 648866021
    0x90b040c06170f151504090608011514030f03130905060102060708180307020616050c12030415051b0a02011b0b060f06120a02120606030f0f0a060510320d180f0303 72
    0x11f40020001c00b074943e140142212103000e0340610082c0d07006001c028034114804200804100a030075604003811101c45070f450740d0040c3d8603074040f030b1101c09020311126040e4030039030303600610920044c2082c0c01d1400b8080c040a00c00782c21540e561030b13682c2096200e000e040044510a642c00780c40d90343c0d02d84510340aa01c02c2412542d04907000e0056458100062500300140790f4120740300c8010b5481c06103842c1c40020349202a50501c0103121061201e030031142d0013600c400980c00d0910001d02007071800e80c4001005018428003081100e05141c1e000780c0882c4941000d95403082090321418091017180000502600404c014500c030040c0302401c000080781e5035005006050b10140304240981c48000c00c2240f90701007104c100f001d402c8071030700040b00d401041c1202c64006403204400191961244049108100d80c011007201044a281d8a0b0301042000b0609034042443d058440d1100030040105c0c126502c10340d0440c06105860b144c0c1091104a0035040500c030f298080b4001608080d28900540078140c0 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 648868507 1250 648867257 648867269
    0x120c020a0b2208010207200f12010203070207150f080c0408030327030712120608010203011d10050f06070c180f0c0309021c0c030204090b040c06170f151504 69
    0x70b1400003070110710500a6801c1d2a5006040030a1002c403480006001381c8405140e9500080d0300307a1040d840d490741d480110f2078580c0e44001590b24940500080d01c2c147c103d0b4083d8071400c10b00c1d903404a5441d07200d0240d91100e415071030061800c0d1988d00715030324580210b0304010114040003051003041c0203004130a24412101c0000840d4600f80c1e5400b040c1c40e402006405008600e0740c0a8000710f4502c01c44100104c1c0000580006d01d40391640702c80c030300326082604841403002c0c0d00b0034041d41e81544076544030f51001070241e1000049003800302044610104010460162030082051001c00c001904400064502c110402150fa00d03256414405010000e941c41040713480d240329291014428085d1702079054000c0c28583c03500031030200e001d00c1c141810070195403e83c40e10101100603503a034002c5484850080f41d00c0026810942408081600e455111030240050266101e00c02901d0284403a03111244400b01d02c5079540d01c0e85101c0003075240c1e020b07003648080445000a010310703c0d00701501c02e0f40c030 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 648869757 1250 648868507 648868567
    0x5030f0a0c06050c03030c09060c01063c03061e15050f01050a170702070e01080312160c020607030c062409020909011503060b04060909050703020304120c020a0b 71
    0x20703450070243d51500c80c40c1405003050300304100180f00034140c807005080c1c0010182105107025a14280542140c1b00b42c0c00c0700b54040b0340c031103040c080c51540c8042101007011010400d000d0070720b00c03010b444c614070300c0d0311005001d20340300c0040541c4800d00b11181d03c500c070940030b010301c080301303801d201800c0441e100c0c000d40f40b254501c00d079655003a512403415202c0f4450300b9254035052846411120309074800041c0208211f00c0303425008035460f427140038564004c210300b80045855400700c8011200000001f042100c0c480382c44a8842d418903404000318103c2d42d015500c19031b0325265410203ca0030344020f900580103d007406500c01c002210203202009000104488030129515440050207034840c02c401d032580701c000d40c0c0c0180f009404c14440d00010700101d0070700245040c0e440c1034404403900140e2181000c41e817040804c201180f100e01800760310103401c0c502185989050340d11000d01000d5040c4010403c5481c090b24400c540344c10301d42001404a0602c03498640d41c00d049004107003140b03581117017030200d = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 648871007 1250 648869757 648869759
    0x903050f1809010905060d061116030e030601050f090c030606040b0301080c01030e0613030e03070905070f021903091206290f030c01140307051201060f110604020f04090204020405030f0a0c 83
    0x10300c0c01c5c0300d02c1380036100083c1440c400407415124007000d0071060902018941042200e071a071550450300c1c1d805410311035150141d0714200f00d42094101070059100754040e8a4154808800340d452100040e400200c00000b60340341d443c0e9002264550140d0340100c0102c0c900040041042000007540d19038100c03090368240541d21003803401f07a0b1900000e56143e5005a0005480d4002a000b03d20141602c40c0103011200440e0b5a03200a4050341c2d0142c0b1a200424812043c29100e90340c140708541c04241c0c419040c0c0d0701c88902c0d5030014582209485140305000350001240104807480d084081141000c401e110594802e040154001c41040301850f40304030200002100c0d0350401042140580405840b1032820b8038010641d083d442c3d1005092008000b0200001c6001015640031180a05640c2d85c4628402c605000080c100404000c07203103031030354842c0e001c20006035103004207070401e40410342e8081a039007214070105019020300e0b00702c036603d8014582d800f40048400140341c02070902130302c42c0c007000b6 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 648872257 1250 648871007 648871019
    0xb0d0b03010606090e1e0705071e0b040c0b0c1c11010515040608011505060f070c18060e132301050a0504020f0a080303071b080307320403060903050f180901 69
    0x800f01d8210b07100c6c440c40030080050542401503028180a07400745030841803080017041c0340c0e02c00c8024028115040501ca206010074400500310400203803101048151821841d000c0c415521502041c16207800380740c00d00e8601c0e10a22a510f00700c980d0540200074051401d00a5909040c902c0d400740701030045291000005401205000c0d000b1180e035030580c41002941050103001c10741e80b26001c0b007103c2070010000c0a000800044422000740804620014501c1040c40c042040d90503660041000700581c2e018800c3e00c0c1d0790b00140c000310341e0744180b10030000c040e83c110b13480014546402d04a00e5502e031004110380c410068000701e1185100312216000007800c03208001d40c4c04a071340581c008070b5001f4400650300c40d0041d406e4400219140f600303548404040c1c1d88038481e9900881d40d040000d2503803540b6055452406903004010500281c008000c00a1460365074a117000f40d200240840b13032681d40c08014103004500f10f07444103810aa420342d4920352420b880354107100001019003d000c0c008000151 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 648873507 1250 648872257 648872281
    0x4050609160b0306191505031e1e07230403051905100b150c031b010605030c0402130806040c032018040c05040203090a020a0b070c0b0d0b03010606090e 67
    0x150b441e400c6400e425600d99009105031010619505580015081808641052804080c80500055075242543c030302e0180c0c61145e100b4030050303c8109051002d010301440740003294202144480002100c20540e5810208444040c541614a00d801c4a0b680d41b411542408200030001d89000301c0803070f0400f1401504485080113402409807041c0c105d513440700003130840b580020b403815100901c0200d2680e80c58880c0c100542c000800c00380258000140b0411400d4411583d408002483d4000c100345032909010a4860000018007481698002654203078220841c118002500c104030071a4401d01d081d2070020314000c0075000507118107840318409020034498a06403000254041c051400c1c000c4086107169120070047d00403249000004004111074540d032001e18402c1d100c01d030041c00789603214010310558400c540c000003a07000c420002c070004148021102d00c11100e1651182c2d5640d4000480c2130000c00d100c40714254154200f6070002403183d4008420010340b480701040700420b486559498003 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 648874757 1250 648873507 648873509
    0x9050603090303061003061806140909100b0301060e100602060c030c0406110a05060a06091808090603070215041208060105031504020d0b06040f0e090d1718060405060916 75
    0x51682c1c0200000340403810010030084206265050215156403200312101c10200d0110524920303656640003003081454170105909400e0051b299240c2d2410800b100c180c0b1040c159080c80285074503100b105006403001d520440051084111601c050709011208505111161041000500c148000300b89260080700441c0d001b440ea4160083c686440c004054518600742e04842d0214010040802d001c10001c2c0482c0c0e11680a07100c0001e119800d026880e0101c03411701a0848051000790a90b100086581c0d040380c2c00c2c110221000c1c0c2c0c0700d5407200402c0307181c185103180c0c03505920f43c1b1009210400510790413044c030161954907480c5040c0d1b00c80780119424082142d041961002c508a50041410b041c0d00800d2115141000419003140360000701d1010f6100740c7c0300c9000046210010014101c1c00800d26402a510b0000303401000e40a802c018511400c116100c80340303102100104101203d0030480c20102d0a014040e0342140c0350606000e070311390300102c450300d10900038143c0000d910170712030020340 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 648876007 1250 648874757 648874771
    0xa030e1c0c1a13140402041e0503100209060319090c0806060f040c051611062802150f0a02070209090a05011104230609040213030c09021306050d270309050603 70
    0xb041561504800da00784c00041c8000d150044e508003c041948800000304c20070309030345030807050b010a00e00414140b9000c0c151050a00e100e1050012950540c0c558003201e800440302c0d64905203400c0c411083c0c2c00100030100006001c104002400110307000040760700740c46243e080300d146c208006468207100580310300f1011500003507810042985007141782c416200345240605400005159400040395aa52200c0c0713441004207401c1541d00f00c43c425081001c4135a07441380c406440403080d0201c46201c80710028040540360041e1740005240300651ba030680c0c00300c1c3c1e001420007034107092042d070080d10b601a070807043d034055081040007403842e8038207411582190b000d0b00705906d0a200c201d030000360345070003141456030084080060003541e54581c00501440483e800800c64620314600d02400c8104455212080050040c082070b4405880381e040542280e080e0305187c3eaa54002c1010350004002d080594002d95110070030441e07900081034940c0b9080d40c480d4403500e92079600d401c2001040d000c01c031404 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 648877257 1250 648876007 648876037
    0x14130b060d020a0e1f08030403060f3803030403080d0b030714042a210c0f050306030309040e030a1202091e060c0616081303020a030e1c0c1a 62
    0x100402d03020f04c00801d40c0b0a402098100910300b01140944080f030456100d84242d034000719041c014000e240c131407201e00c1002d034041040715514030980c9084000050b52580361414400780444d240c100c081a0181d035405005041d01ea03141c0d12403a01256a402200e4076902c00c40c0341c4100c169003400d0010702d810944041102c00f9480d004c1401c1044050040703c1d20b86a51311600100391003100301107103003410783c42046450f100400700443c503003501401e0001070b5105001d030521545040030742d0040c0c0c5220034a0b07001d10f8a9580c0790b0720040404d00c1d511500d02c9031034106141c03a040b00c24a40020003c0c048606442d501c038031280001100090aa020706c8907800d922070001e4000c0390328204084a00d06c3c0340301e005030204d030500e028500c44038207142d001c0700c0102c0c0550429428003952a4000c80c8182e201d204100c4004c80551b09031030007560347c00c02910040c18031102005c03142e030300e40c4c032251100380025200c210b801c000011071400350114440f074400d205131240141862078070384400c28140c8815004007204 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 648878507 1250 648877257 648877259
    0xe0703060f0903143f060102070609060c060e03030709140a0b09060903010b1c0308060111030304030815061c1a090403080403140706050907050103060605040b0c0114130b060d020a 79
    0x7140d544d9803040030440104800c40251075502d40c0f41c1200d50038126440754480d2000c00c2011030700000011300174182411508400e00a000594108121300d00b80d48103483c18203044151440c110b8000e100c244005802e9200c04400c01a50035407003c50b01d0705490550200c690444208020b103e00b00d00c0c0c038040c490072003605214501c2d150034090080d000300340e0010f00101e00307010b0300030100f040103140c172580c040403c1c2e20b607016030281600400d0040c3c0104087c1781c07031510140720300d02c0d8a13183c1c000948001d041001c2d81010502c03441c8801740301b200705100200035954a908000342c1d500181c1031942094202420300900100100c400710289050b0440a000e00040356280d44d0112030902d0002c104030180308299030726058080002001d4010f0510481000440d03082030302e0a18a800307a142c0c0110b040500341507040c07100c1b03907009082e81e00b101d1500328840d444001e184282c0b4050043d04410b00c1d1581c0c4944200300482000d0801d0100b40390084c2c031900f04035180d00c028000b5511000d10040e4005003107200c = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 648879757 1250 648878507 648878537
    0x905010e06090a090c1e0813080306040e03030106030e060906090309060c01110315030c090402060409090314190909090c0e1807060e01020f01020732010e0703060f0903 74
    0xc001c040b150b01c000c20010351140c581032400201c0340c1c1d00c4404000074125000a4103400b50150030440007100d01e040c044503602d00a070b406103142c0d2504000800908001c0040f4030a500d0740d0b000004100500019a03443c0e41c3c40711002002040042d449180c1441075001050238610081105401020482d010b1071a2191040c18407006600003000c0c07c802d0740d41d6911805148451101660044850702000050300724003201b01460400558034051140e4107800074400143d680008860840e1000000401d01c2403050505407000610242581c0c1c180f27100144240311025440002c3c80034220a0703c03a1a1442c1d16180340d4001c603802e6540080910000710b0082c48810040c4c0c070748503400407030880c068400003484040075080a0381c40c0e00280100342110301d200e06075a0103003c01404031030868021070401c0c21980b141c0061300140001e5185001413040250440300b0300300445100400000c0c001d226170403203050381c41e58503820741c441520054500101d90204110f0380c01400c2c800e030b40507a100300620000003 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 648881007 1250 648879757 648879769
    0x31409060d0e19030f1215092f0d05090d080402040e0a0615050a0b131a07060c02010c090b0f032403150603121215041503030305010e01090219050a2606010f0905010e 73
    0x420307410884141c801d00c041c9c51440259200031901e1201400c02e0b2110701c9016170310b068a4000e454a000343d00b0002100292581c0124125401a01142c02003290504040501d0400c2c6110001402c3c15040480700c0080d03000ca5a112000c5610030385014240c240c0e1500701d40070f240124440c1c028614003000d03040140b500940d0106403240300140d51079150079044d84d142e43c00c072a0310514a80250f5103413038a0210b040d4201201e00000c0c0090101c90346851a02100b0b00e0399444010030292141641c10320503008160102d440081c2d1b0103016003140c0c01d44069140301d0203a25000ca0304075109204101203a040411920305070303988008100354840c40b5403502c1c0041c5c07444442c0144d030700ea006540c2c2c000401d0703990300680c2080021400794500040c1035040202d40800c02405030003e40086004004448480c020410b6840c0945054900036807110f104a0045504a480444200035950704860707549101010490303d9001c4d070720980b1443d8a00061030029500f0021620840b4046070a020401055007462 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 648882257 1250 648881007 648881021
    0x20307140705060d0f0617030901050c0106090e0601031104020702010905121f0f0b030a02030c010f0c061104060e01020c03070611011116031409060d0e19030f121509 73
    0xc081591211a1950b000c5403140d000099418480e40d180d580511401941e882034601030448000801744005104103081e98030300c20b40180d24108039000030700e030030aa070f020360040014040c42c900603c4601e440824040e0703164000e000641d06008994a41091442c051086486990b41a1647c03128545801e042005190000c4c06070344460003850641c244030614a1008556440900b00020751f0400700c45401d0304a4440000c0e0758000c0d4010b4210b1000341c0d40c00640c408a048091034075418051200754115011f40108030b000740142d05024460002002481c064821b80e0450703968080c2e11004403004903a5159800c0c03a0750b4160b04490070500160784610300740140603400f0f00010034140740c485009081e40d44012802d0100c0b46d404600c44007016032101d407208000450710070490074100f42d040024807030320801d008007141e1556600160310804052181c1c04600514107401e48a080030303400c2c090144140b4820400003d40d010410b000404138903c51010b29003000040c42000c9030a200329075006100b5 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 648883507 1250 648882257 648882293
    0x130e06010c0501050a0e0d2606060c0a050a110d020a140607050a06140705040b040513090b0a0507090b0c101104151116061e091505040e06090403020307 67
    0x9881c000710104400b400384034024068088002000189080d000742082d0780351444108002036204684070f110002c941c200007004140c0181189502c4206c00610030744107248284140d4060005c04000b44032010400f00d81c9980640849a001c0035110300700000342c1c00c00103000f540031210074001d1100520140071a180c070701001d45081d2608206880351032a010300d80c0750460701c0b82e4840d403c210201e050074019680001d11805c0072400d00c1d0030044045028003030780c02a940191046001c541000c040358200660603500201e9403001c5041080810010380750840d480c0d8003182006500007418291031040b6813080030044040c10560b40542c032080068400c0d48004841c40c0018000881c00b0811300c20111841d04090303c0380724603400250807680c04d0458070729144000440441041204d150420408040c1d407001069540340c072881c8400503180070400b42c101d0303007105000040c2000c1440d085801030003600d002681610465440c801001b50040d41150001c0040e0001e10212001139008a104158111 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 648884757 1250 648883507 648883517
    0xe040203070c03080a0f1d0c0603060102030403120203131511030a02070306020702120102030907090b04150501050912010c0c05070b040b0403020108041e110f0d05070501180e01060e090a02130e0601 87
    0x41c90f0082c6c041a0741d89101402e070646c3c4418407a0031501e408111105c0401400e650460840c549000040d4980c0241c0c400503015404a2001e02841c0e4800e1007113440140c00344c4d82d00c41a2549034480054404822a0a040441d030038020a00c0381c40000429a405c5800c0c1c0d84c010b200143c110b546000c040d4200c00412600200c0b00d415030000c202e02070003d584217458890041580600d4441c00c3c400f81c0d81030707c40d00c074025460400080d07803030214207041c2001d6907800c0c20260b546011a0000c900610504d00314100e03254640840303100004d5110a0344841c207405041111442900c07441c0042c5184681e104607540020200f00400040d405140f0741903010340038210065443c41c84100b060f55044080404451000d060500145d05241c9451417500310242640c2c03030854600b4aa40b4159200d200f07009180c107010b0b0305a038444d002c02c140d1941d030300901000d2680c1001c82d41c1d0703400e0140c140443d0820f4544500f040e8800606540254420394041c490b8042c034400c13040d0b00e81541c1c40300c1c0c04005014141000 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 648886007 1250 648884757 648884771
    0x50c0d12110c04020c150c04080a030302071401090506101a0a031e05010b0325020a11280e011d150402070807030e030c010509010c0b10050a0806070e040203070c03080a 74
    0x10f940c500c0500384460015028060b1071214035842c501c913034001841c42d252020140b0040c00304c0a40020010704290785420010303510748150600400c1800d50803c6607105601300103151742000f802160590246407003604000d0b040d619001017503506032921380318211030f080c14825110303548d2280e04102854540303118542c00d0342d81c0c203032040025284240c0000c4d556240010078085580d150380b0001c5008116488051170320814628000d4075407021640192248072841d0482019607103482025100b00d42d07060104e4001e07038041c4183c1c40c0c030341503500c070300055944040c0002580344511220802d41003260030b284d00150751101503520170317504410452070308150309001c20400541502c000307210260103a1604000b4080d600101485c01104595050420405002410250742c225040d440400d40c401203590081c0e542000c0420345e00a154800344d40240746400c00a1242c1c1c0104080740654030703640d20220102c0b075200c203200503480b054404400054450342c4110110744625130668101158413000300da45 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 648887257 1250 648886007 648886009
    0xd0c0305390708060a090b0708070302130e160905030a330506040606030b060406080c0c1203090d230a021608030c100501030b01330c050c0d12110c 65
    0x107280d60403024542d000326402c0c00314880800c5aa9480f0314402c07801c2c44403414035552280701410103000f00040c8101c00001c00c0005000c2e07015165900110091505e40a07030300d521498420600351500303041d1030324903850406098442c09494060791400380042c900e109159681106074070600a400d4001900300e61001503010000c00014602c851094010030103081000801c070440b0b15584c4040281890641c0110b020f0702e41c00107441c101c4159003810340c0d413a0b03608541030081d44980f004c41c40007802a1100030141d412000c01a41c0a00c217110111240e441c80d40301d0603100307203150180205d1400200c151035050080c0840080aa05a103803040d00c090791000303903456440e0443d1750410803080c1c0011410003501d20003045154040c0c040c0300000c5c8025403454440c076083da072040c05025030030780c4044100f004a5000400c189810401e0745109110780050440042c4020444102154207020780d4000113542d14148131f03e80181381c1c1204805409010a01c001c0e2404290751344100740ca07000740000a891 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 648888507 1250 648887257 648887347
    0xe0c09030a110111060f01140102010605090708100e07120504020f0409050d02010e0c150f070c030606050901090902090601050a0201180602031e1b030403050405090411030d0c0305 79
    0x1e41d6128014076818200740e10005004101840e41c0c550040d0f00600030003441e001070048803411a4a040c0c49002d00307a2410740103d014203810780059030000c08600910130415805030070f1520822801d0040304a4640303403a00d03004114416144440040c03500740c011003640100750700c001e030030510040c00c440304080c48101203411f40b500442d05031034a41143c0881a40c1680a00880364108503c002500c5592419070000d0000c02c50015102151000400c0107030002c0e081c1d0707040340c3c105070300a10320030f1b19a035030380c87d080c00542030a0107071030b000301342d41c0c0c00016800480d07010b60b2000719070085c40001c0f255140c80044a10f038100010403011507480380c000103542a500e00c444100c02d4010300015036286007519080c842d840d41c0102840c0c401c010901049480481e09004194440145c902d903540e0740ca079404e0031103483c01650080fa078004045000d1004202e0401c1c0800c41000080c0d09907a100c51010b00c040e90b240a1200001d8041030040040076185120b070916540d0441c80700141e409036603244010300071 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 648889757 1250 648888507 648888523
    0x504080a1203140f090c01020304030302150702070317070303150803180f04090510050112021003020a02030d0c17010b13031509120503010608060a0522090203010c030204060311030903040e0c0903 86
    0x40404d85a0382442010181408020450b000a000540ca828039655000f5540e040c2800000c52170a800070100d540e2920921540008540143d038008521803c0c2043c66010740c0301c2181140403074039007207440280000514100d001c132005100138504100c95124700170f10400115000070ba20200e180c03103444080c2d480d4803400c02c00700d0045c0300400c0504042c400f4901101c1040e0040860325000085400c010f90f90f0200f0f00c2180c1d02d40d0704d03015840304001c000683c958020401c4001201c0c1c10555403804842d401654040010350110a06600f82d07a0381c441ca81961003140ca40c01d41c891201d074004c2c0049420b581e1041406180031300f001480006c2c0c0e4848808841d0428541c4000031000030040003455484180250800400c5900c000900d20b0500040c048545010800c5094106440c03080100f1540e50f002c110b1a54020b0003d002084da4a41c00070b00a62282c010b020110b480c01d00442402101c04d415244914400d800541c42d0909202941c181e540340200740684054040111203600d03102071202403 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 648891007 1250 648889757 648889771
    0xd050a02190303030f0905030919051f030f141803070c0902040e09010605090f0403021507110114010803070206030c040308130f0806060d02010f300c0504080a120314 73
    0x1801e202d007503260040170f8611400c2149841d40c1802140b00c01302d03802100f01c0d070400208503140c040101301c00c0580d8203e0314842d4040399001e1440c210000702c6428102c104001c20029950030005516001030017404c0b18450200c00482d407181200103401803103c00e085509104100c42200d0030540180c0d12051a003d540c0c000e03902042d00840c0811200f2004001c4a400100000c001c4c400282010041450b01c03000409000425550801107414580240020342c103140700013200944a15181c0000781150000c54540300715507291040c0148a40707212115641601c0302c2c134018500e0b00c07100350204036040c0c0016044e030f8244242008008002040700005094500d10700c0a0303111241c1ca42480ca0104a44036030000f44c0c540c00203000c0010b19662040b0f0008000d030309090201104a1014048640742d400050f00c403007155040140b041e04c2800d2500e61416150444000d100040c4d400500702c486014a1140d810503500c0483c0040000c2d01c800b0341c074907601c90035140000d0340305186008210b0b4508151146 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 648892257 1250 648891007 648891049
    0x31e0f0c0f0d1a010201060806070c150902060c0a0c06020a02060318010e0313060315050105090d11030a150b0d1203050903250203061f03020d080d15080c0a0b04050d050a02 76
    0x1207040f6503028001d0000034250900505100c0c5800c0030b0282410000c040018030812404201c400d4007402d42d4821b003402038003d004d16450748080703400c16583c4d25910382c0654240080030320002d0a5440000d40d0550746074007506a50464441408214094841035944842c3e5500c4040c0c040c5195400c101a02c40c114024644034201440c1402c003030200c0b4910301c440d0148881203181409583d03002811254480000d981e0000f840203e814060030800031915030941c180512403e01c01801810300602100c0000c441d070030404200e411041101c02c0300304943c0200380e8204c000c11082414040c1d40241d0f80401e4910580381742400d00034001e152117200405180214103589034150a5003020440300794010981c18003070380001c031620390300c504901603488020310840900380c11108212442e000d4900b01c460111041c02a098840016100300707800d4044c0e023480384642c0c4083c0c421460b1818802d011070701520340c4c00d40307031504113028480349904404080c0d895214807103600300140c55115001c3d50b603120050403 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 648893507 1250 648892257 648892301
    0xe0d060608063315181302130e0115180f121407060e0d03051b030301050108090604020108160c0b24011707030b0a031403031e0f0c0f0d 60
    0x180725001c16240007407408121180c8211241910780700c1448240d0300c2d0300d05800b44c4929590080041c01031100c101190410b43d14851114102c0151f00545080785071300e01c01102c91600c558080c110341c43d0911a8102c801604010302403403501032900c0100044000a0b28641e05840d010458842111903200520851406020b0010300c030702c60300080700865101010306030552038098014014900000214071502c0b02007119420140540122950810301042251401801007455522030700300748520f901240304980020b506000c0802d009208a41c161140c0103640c5444c55244011740d1030716041c2c0300380040c448010012945030354655100f01c0e4100b681c41c1e8060400c01140c4c0440c0c0d101d07841207044c49400d0001440f036041d1080c50540c045110f150004840c1419400150b611b00c241d0b1000e80300806034019400c8540e000300c0110b00c24031144822100501d404100c140084c1c400b150031020700c2c03580130049001d070281d040080142d0401011342c94200041c80807143c08460075550901003028103100303 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 648894757 1250 648893507 648893551
    0xc0602060a050a0515040203190e0a06150303211d070302040605030a0c170a0c0b03040516150e01030b030114011d09030d0b130c0512010e01060e0d06060806 69
    0x2402d6442283e050003400b060400307800b240400140d0032006803190b6000700014084404041e1034500b100f109580500c0802c20a82d220f41c1c55a100c1501620344a0410f803810b81c50141c0c200250742265415520311400c020200c41403407031750140c1200c0c0d140481d2101e500328400c2400c83e580350002058403024140c801c0c40c501c104421201c044d80103a0194102d50380b01d03001b15400c0c1c4070030801c98103001a0100e03002c6072010910308182d0300b0440180744203000300c404180002420051440790b48204100d0300030b510701500c0c04c0314102c60740c411040c850850303c0031401c00d83c0c03052848260359131040c1000315410b04440000390a40b41030602040d00d401c04140104540c00b0300a2039120360003002c0554480c281040101940c4a1144a200500700e50700d441c1801407984601c0f251901c840030ba54401c010900c49800300602c0c030351004d05500360441d0010700214407400d514a030141225803d8a400012082040500c59940c0f00b101042d101d1a5407030710009808142403103000e119205d5051007402e518000e0b1 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 648896007 1250 648894757 648894761
    0x10822061a090f091e150c071101021c0c060b0a091a0f06070b07050705160512070819080f0703030b030f0705010206040b13060f0c030f0b09010b160c0602060a 70
    0x1000f0349050740c2c020341400a40c080101d804c0c00310110360f800c01d40801501d500040d10b44094001c030340c40092902c40c100701d001c0020704041d000f0309114262001005042100481c1d482401408a10055020b45041c111990140711036041c154858100810710b00107600028259095550051004030b0b11100340c2088981c54500415411004803124000580000080b403040d0148003c000d00c1034030002c020810660140c025520400d512004a40c2c0c104407005c1c3c510b003008014400d041c010001ca0404001858012440500303030744920005008204610360818034541e2800340035140000204603a4520100180040030601d000780c41c0030030b00d40084403c1c07502d01580c2c2c52159920b90004482030020380e90110303a0b541c11a80101143c1d1064903406400340040d5014940200300b00d142c0350040120303019030b1300700013051040b58038108034400d501e071002d0303043d03504485c0c00343e41c000d2a0340010300c0007510382e8020b0040074944140c0302c401d4002e190f4900841003110341002002d80c0c058020000070b06001c1c = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 648897257 1250 648896007 648896011
    0x60608010603022818060503220c2c151e0109030c080303010f05120d0c1703040c08061003080d180503131e03022110140412030b010822061a09 63
    0x74a4041c0c034500c1c25030310900348120103030411010809d00b01007401c02d01a00205c4a0b001d02184240d0744900d268202d200c035415541520a00c0c003903004c19001803030840588042541a15001d41024061100c1c07000c003000401348000c106042c401440d1012012404d0800124042c0c608040110303a00c0d410040c2e800090900d86d07010b01c0c410160584a026003c8020030b0306030200c2440c0c2801c80301440306152901c0f60880070010340390217941c040100411301458030300c8207044942c0d174800c3c1d6280d9101c00c1004c0700784c12a00d01001d406144100b01144196021b540700d0822905002e400e4254000d0365902c0c281554054038030f02007010030ba20024044584452410103104402030454a4054990343c0401c00c100d00308078003c4051162003401c1d400c4210240303d6800d5220480c042040444040000c0203040242501c095480034001c2d4a0900da66002c0e10602c031450005865160301989c40c05510f00c2440201c1c1050305924400d0a4990002000c900a680d90500e4a24024550500300021300c407040c400 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 648898507 1250 648897257 648897269
    0xf081005070c0312200306040509010c0903030c1e05030c0d0e2d061603030e0312061c1703150a150c111c0510060608010603022818 58
    0x6444207001c50035400185070001c203649810f18400c40c0022409050040035040e00e08214004070b4a25084030a2440740203501c91072080301c00300955115450007500722240c0c0f0200c0070104544c1710007070011a0280410313586042c460800c00380301c00b189204001e40d2024240c2c003100c081e400401c2664282000340884c2101041d18075001d079040c00903400042483c1d050661103401c03049420010703001000c42002c61040003201074507141d9124a004c20420340e19038005001e0b0006031420f0111904040f0100032101051020018040c1640b10f0008000404100001d0b003100700640401e4940021a0585010044407001c103d29850b443c20540b140107030816054007034450100c01d10103101e80805440e4000c034070310007031408990480d21131424600588000ba1038590042100700d0341640c2111031520b005105100e6001e942c0c0114100044500791500d80c080c5401242c081001071007900c1c030990282c40004203141c00a04c14001503007514036010740d03a42c0200c0000d001c003030420300700080d0101c4010080c4a = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 648899757 1250 648898507 648898511
    0x30813060801081614010e0409120f08040804030b0613050a0c11060f0a050c09030703060b040e0303040503070b0613150f0b13031205040e0705071e1a0405160f0810 72
    0x100500c940c40f0035400e580070b400c20141c1d41720f81e118100c0e48038100c013000b083d2020700108161102030520901029032144031000260319000800c2419100b40b0605009651003c81030381006c0c1180d551180e20b4900604071500481166007201102401d4001e00d40134859110300001c49070080c100c02040e01c5a151801030340c9600000a109204009120341c950220b41604c0020341605c0c0c03141007080e5803280d1504582e140c41681408020303c0340c29884410a003804440c1080074410450a0702d4881c04203d6000d4255001440190301003247c0f00c83c11984600020841040385944050300012a14054a80d8a80d811401c034248800540301b1503840280800b50200350034212400c90380c0e41409070a00005041080303009001003c140214252405420480c6c0080441e10b064030b001001d9400904094844081030b10507810450010110f00c0d00386904003110030503081028001c41c0c11030402800c1110940300d406180915003001403c003901a203034004851501600d071020f818913041643e4402401d0314 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 648901007 1250 648899757 648899773
    0x1e0d050c16060506031c110f0d02070621020d051501020601050a1406070c12030e06040302060a110c040501061106010e070819020909190f110301140a03081306080108 73
    0x25050382400c68001e98052408036a556440b00803a0503c80c0604000c2403107034044842c0d01d401170300283c00004d4440c148003196180d00f0100390b020f90740e1105d0020203002d80c1000c0028004984a10101c03450890f00681205501021851440c1280c0c004c9804c503005603900c2c0c00340500903510001481d01c95009100900c619414000010780c0c41a2038414880002007000d005801c3e40c44074001c0d40d2843d030b00006500d1110360f403642e02805600c902c10301200002d25200084210340f422105850030b0369005006181025080303041524043c1c292400c1c5051880307092003d10a42d030310380c05802d000e04420b43d00e0082400c00c0c00a46442d000f4182c011a034000c0b03e4108000240b41e0000040da4400c4948181c00d401c1c0d1902000c14000b84035a42e4059008144041000300b040c0c2000080ca440c081041c40030012440100322160445d00c900c9007040d6030001c108010030146c41d00720300c44260188010214603055540395103483e26680040d00e00046002c1d0701104008040c2c04c140440e00400508005d02200c0d = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 648902257 1250 648901007 648901027
    0x70c060f0c1122090605090f1f050901021c061a161b030c061e170a0e0c040216061b020c0405100e1003050706111f021e0d050c 56
    0x5140680081c82c0070f50300d41c01d00c0d0b41100091400c2c041440021120410081049040020280008851a13902480740c8000c651902c40001018142c081c000c00d800c2c1c1c008114048814050103001c0d1840d48290f4081c0980360300007514000050303110310002c0e40000d020389095801c4aa0424070015030103900400d0040d4954000301c0c0750b64500b211344c8018450416a0300c000c11003032003511600050b10f08100e01d1004600103401484902c103030020705090070700c9011411400c0700e000444801102071820720301d000c0b5450410316007204500d4902d01d415510100c1804002ca4100d8102c44d0038600c2e02010a101a018800d043c400c074101100500c0c00c80c14800b1031004080e64400884513038074040c5d0341d02c90006003507518500c018070140415100301c484c0340c00e21044200e500f2007180020303220b40c05090b40010f00c250041400c0000c030034104014000341c241e010b03141a110703010640d80105e1190208201010340741340f01901004114840d00141c2c40303d80101010302107400040400700f00600030420b5003c1 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 648903507 1250 648902257 648902273
    0x50601020309011b0305070c060914100f0c141605120307020612040602090409080d060801201b0a05150703051005041d060a0c110601031a100b070c060f0c 68
    0x444044c000b04441c2504186401c889611030000302905000400d0b602040813a440441c2e00101da152030084101c0013241030401036803001d0300e1a1400802d100305540584540075440034001507004145402010500680341401c101451011210800800c0b00134000c030f14010295480000c01c1100460805003a0741c0845c1c844e02c40d031070b1001441106800020200030701c1d501110b1541c40050000d100414080c80c0c40300c001e40011211500e034508191004c10b03130ba54140b013400c042078503035036404090716040031480c0c48650040503070b120210145004048088010450080385c0e521a400420404034a80c1024444850260444041505080503c11032200c06c0180000743c440884000401012541085081e85016003c0b08030b42e00a074010800709200e0351f072007070343c09005684500250300000350030789071210030902004001c165500304079800440140d41d10382c0d000b081e0f1002061004e44800f1881010b03044098229500c44400c20280213442d800061128640300e6400e145000da803069503040c02d = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 648904757 1250 648903507 648903527
    0x51006061107150c0f06090b040213050402150f19080702060a0501080a03111609021c090206070f03110708070f0611070608070903021e030d02030c0d21050a05070305060102030901 79
    0x42080768030282413042c410208550000f240d407000c4d04020243d468900f41d440304e0030441d07080c2c0c414210007100d0300843c111805002d01c2103500500011101e0f803032001c00209500602590302d003040050201242480c91003c882070b070348100e038454401c45c3c40c1140009103840300c024804031600d4200001042100d00c000360310740c000d951500300780302e680ca4a1804940760001110a20300c45001007000024540c22a0307005003040508640075200350135948040605503152407900a4101508000e400c0c0414098403007075141030310a00d0182106809020312514149483c1c21104403600161000c003d10359441c14000018481313803c01c035106425804045449001c07504c20346040c40301450009049500c14000c0201940c2d005080e1a80000794441345031841c18000c034030a00034411580b0300b83c04540000241da4101c0d10706170042100300c540510840e01007c06240d5054500505d0802450449250198a10540e4100c0002480c0c1c500000010181c640140c0080e065420801c141299640c3c0903441030 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 648906007 1250 648904757 648904799
    0x60203011412031e091206100510020c01120506030a0b07080a1a010c120207080a140f06010b0706020c07030204050a0b030111090d080c030d09050d0810051f0c051006061107 76
    0x140c88442140128006da91020706421b600d0140404009030070303103c2281607056450640300c1b81102030003c4401d076941c0c04403010761408100b00308501c072440705958202950000018041d203803400c0c01076954070b030950f20a65034a00481d05903001c00002011500c1027003c0114010385007030f680342c00600044c022500c103100180a00580900000d10a40200078420045c404003040300c0ca0b168550400c0e00304160400e8005000f4000c1102c100004c03040001c55606a41c07589507034601e0403e15940c0c84009501c644038580c0d0a010381d002c0040546e450384070b854841c1d2440200480d41d801d6020405003115250840401d0058050040c00120b072280c3c40210400e0307134003c0109640b41e0001c2d6516283d03000703c03001d141805040c0b004860802502040f018001ca8003501c5a01c0b054a4400c0c060040c24081d00403d9000f8012070405203152007a0038401450300130380d0600d0300040c030701501d809003013080c0d08103040d880944540c820006154040402910314032250042e0400c5401d1000030300742000c00c00109 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 648907257 1250 648906007 648906067
    0x40b01080a0e16120303110c3d09060b0d030f200d020d0f080c070204020d2013090e1b03160f45060306020301141203 52
    0x500168001002020b9003d01d022004072001550b401da0300b07029400b8204200c0000b800e10303824034605810401510f60440c0c515008d40003080212120141d410420031051210ba55150300e034a01184080c52400d10003810b644d8081051411400d0000913201e000c541c0c0e40c01207120f80350380f41c00329a104403a07131008149840c110f5440c540402c1d1104042506202a115501a801a0303288094000800311085110303a110100c650003050002d8030744d00c00032a843c05002504002d00001494140c0c0103003d1070b20303690000a500d0365801101040c259400003181c40d18100020090035403580741070700c400104034280b018003450801d02c804540f284150100e0710060741c045200300c0620395081c01301d541e80d1144400103141d000d951b4508402902c2071403045603a49090301c61040400b40441030320f206071816610b1003505112148145940840c0310302201680a80e0f2a400071000132207038001107000780141c8140306000f10324031081042040038000744030881e50040194080104420003110044007001200c = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 648908507 1250 648907257 648907271
    0xe0309210307060608010b0f0d0c0b0703091203090504050a09020a0e0403050403080d05011508090a030806030c0a0b13090917030703020904050a0e0c04020f04052b0b0114040b01080a 80
    0x203003a1460188200040145042500100302004154460031b07120360226180c005410070072051200b01d011080c0081c5c620708031031000740035100f0700200800165100e4500801415643c07841c42d45143d20001c021000605005c908010916050081c140c0140c40d0301810080840310f07038000b95908010f84203a0b4014400b08001805141c01f030b0050341c00440c4c011583c6130360b03501d00d803100600070301007400768890000403403138001015403189904904c503500080003011101c540e070b00e003a113107070000402c0707580d15100c2c0c410181c01d240c94220701c850091816403921a00c1d20304a140c5040700c191943c1180c1c100300c6c5001405c1c408214001200e00e071403191099125030740d48544500710064400c911384103800c94100170601040c421158410942c8904101c19100c10042e002c041200703074403800711a070028190502003404146403440400400030500c1440c0c1c861060b5001c440f001d0702c4c0c28420142c80c40c000c50401045001e040c141c400c104950219420043d44100e8400600307048005045409aa42e075078071 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 648909757 1250 648908507 648908569
    0x50702130e300f0a080402041506020102040807052e022508010f050408031b070f0305090109080102040803030c07020616061e02031501050c07270e0309 67
    0x40031020504007101501c015242c1c205650329802c8025201090251003100c80c0e8030200b500c101910107016502e400c0c20b1030184601310403a081d032009041079078042d58969000c215104030100a60041030290005038445103401d0350141016020f500050040c01d16103642118001708a131441c0310b034032001c00700240403c8240012032500c9040920b8450030043c800c1a190440c0c00d02421000311028103000340300112680050f82d040d54000c0c3c0d17004100c000e062012801c12006c00b800d1494a4134070f20002410005079403500001440781103026004940000342c0c2030982e5a0080283c40030340640d40003545414035095080303030b032488020003c1c5682e00003c910f4604568440046802c01103440071030500009180c1001c03401401c614005440140303485131a486080c80600a482c811041d100262400024a200640b11640144d40c0c01e0514014481c01240300544010009165000607640110346a03460004104903000e50513103801551061242030259a14040300c1444112010804a03001a90311 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 648911007 1250 648909757 648909761
    0x140f04080c0105100f060201021c05150d061517030a121b0305160908060a0b0d210909020c03031f0902040b0702090c09011d01200c03010c080705070213 67
    0xc0c140548035400c0405001d2084046450002544d07003a07580325403170340e80c2c1d81c0c000d038200d100305d01c0900c0040e400b030f4402c80303a1680302ea80407580c01080303580f51408000800c00021000e0411441c1203901d2a5100d11801c21051004401005000c0c0e03182c041041041d02c3d60b125030749010300c0258008000d61001d44410502c02034000e001c000c84a0041014400d0700c001001e0b0280004540d0362001c0e210010840303140511441c80c2c0812914034102604954862101681c00740415030000c5400405200c11000021004c0c1c0c041c0201c402c4410300c5100f42543c0c06001040c000459100b410f90b80e0050000000c02040031080b282c21002090080302070320900340c88400d0300032095001440a501c08200002c4a0741a00002c0c041544215007000703e07a40ca10310625110f00400c44000d00203410312400e07001a148105ca408401c00050500940000c14020017908419540d140300c039040e0032211400c00241801d008030000190a4140490a4689500014401c3c007405c0300182c0302d10b00901c0346105081c0c0075 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 648912257 1250 648911007 648911017
    0x14060621011b051e190e04150806011706070e010c020a03060e0f16080705130f2a0201050123180c0a0f0302071104091406040302160801140f0408 64
    0x141c415400c80804060b01410703c0c0c20105011204030703840461080c1d0301006404031401c01c01e0180740c0d80c00c02c441e00001180d00300e07009400241c10a50329800e54040c0e003280b0400a00070f084801c010b000f0380d070503d81c88a001c07203084050284241e00c81020b108000f900441a001d282d0001c0c81e042c414030500340009032a200d4140c4c0040c006c3c2c0c0c0b5001000c0301c400c00c0881c0c1883c0220401c030403a02250581c40f081c0c030401c8030302d2041302a507030403c42040c802e03403401f513910b040071039050300b004100c030f840020741c00c3c0480740e40da0b03c0d6080d080c1c20203515160002d0aa090000086054002000a5890b000074000c0e00700440450005100711811013070b003a942e410403980b5051f41d808104400e1807501000da251198050014100420047d103441554503200e4022206501ea000403001500002c0c8024440580410003084402c0c1d4442c0c14680089d420421046209500a5000701100e007149801d1410b0008103402001d001d9060500c4c042003041c1e00f00600d90400345250900b90a603440d418201c0c114060 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 648913507 1250 648912257 648912281
    0x908031629070f0306050f03070306020307021c030c0f0815060d023f01270905030c010c031b1b210e0405102d090c0c1406062101 57
    0xd04814810040e9100450345440080f0351030030403400d5105c2e800c10264540c0c05c000c280d41030303021080600000c0c0054000d1504296140111100c1c0d03c4160814408024010810310000380e80341900b4200c00e9100b450101081701d2810980d246041218800d01100400c51845008010000c2e1034031011081da03040701ca113241c080990040c017001309207030550303002d04a038078001b920b401c20a2843c00c0c0e0600c0d040c00c141250b0729891201c40c961000306010b415092650120510a542c9a03403500c0400c0040c00144840015040001141d6807803d1020b0101d03000c92201d48410b520f0001e02c40307209074105403402009820840340032070301401403a0040003081d40614104000d00204841e144a5400c08041810820222003e020329a1f40800c0015000c4403407054508010080d1910003250800010342e2821400d001c007100f1303800d40c64405039010b64031300568190014513000c080b039003449010b40b04512822a20b4001c0e16540c14000d0004240301060520002154035445108504102c03d41c404002000317 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 648914757 1250 648913507 648913583
    0x51e04051201020d0c02010b0a12150203010e070801090612151112010303030506010201090f02010c0515071d0a060215090f15040209100f060c0501020c16030309080316 74
    0x100307288264040d4008000050f10507050101401c0d81c03500600482094580c0504031071045840c4c880c0c042021403030507a080e03807803080f9112441824681c3d800118040c0c002c0035000507590600510080100c0c105920209410389008011300000c0e45c6038581d0000329801240b5064100101c10380d81c8000c105e0a00d10940d100c00000e4402c003002c001c500c4042c101c0b0b0003520108000c0d80e4100041e401e03554079400040c0b0030048291440c00660082080000b510700441c100c4d800c91424000320200c104081d6180c0000c10104e48400c5020000c0441c0e80700b00402c15500c0070000e9203008006591880e040c004100e00c2540030b8002640ba40b030401900c50040c0c06201160101d18141640120001c0107460981c0103c400c000003908210401c692142110381041c019034601e0f141000884250524550849480d5001c00401d07001c651704100c211480d4004a010500b41417442ca03014040f0b8141e51700c2039a458006100c5500082140300040b6141d41e0010003001c2c2204101001001a81c901d031000e0074021 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 648916007 1250 648914757 648914779
    0xb0f0a03050124030f1712180c0d12080606130902070308130c03080d020405090108160f08030a0302250c090509280f0507030b160f051e0405 62
    0x10a05401c822009084841a5044656035044448510025010144c0000b20b01006040001d5076218155481a034040c100c43c1406003d4808003481101524a16040c400c1c40450304040d008c284003803442030310102d902003408003155aa400b01082c2c00c400c1c500603c40d00100281032516240e04071540d01c201220f070180101d0f1218010320003500714001c03d4001801c4000003c01000e040c680c030150940d0840007151b40e15145641d0032079180e03c50114400401d40a000000d400d803644214540a030070740c000a0400c1811610380341c5018030140d84000342041c4c85110070064140e01004440c54468249000740c1d0740c40342d070b000150b9a000005803001d000361006a41b20180300020307905405490141d401030007261106442c0c2c65403120790401404030300c0e00041144903a0041030624080311442a00c42c40c0000c1c8550725868103200c016401902c03102c4d4400304103c40ca401000d005903d51140d0b040ca48448010382c4002840c901030358007549144a10080d0058002980006541c000c100080c003181c800 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 648917257 1250 648916007 648916013
    0x11062a030a0608070f05031b04390c030c15021317010f0203070f030b040e0a230d1e180603090b01090b0916030f02070305030402100804030807030b0f0a03 68
    0x2c0c0858840c0d11a40d00500743c0100d0141500c1241400700c45009000b0884a0800c03000c03a02d04404182c0c0281d4001e0b03582a0780e5402c1700d02d01204102801c0d00c00042000c80100d0440822811403001610080285130000100000e400c840008209604081d442400d014442ca410000b4851344401e40090303601c0300c40010781600318000744126103a04400a000031810107254205a000980300c41c40841c5503c3c1003c10707850300c20340c0900c8030050002c2c0089042140982c0d818100b1041d1310b03060300c0e00f00c013113401c1105076603011030303900c20030213a5100400c00324141100041007030911001000ca2003030240104d91960303103d46030301c03411a6591020348082a50b110009002442c1000007180e00c00c0300c080000071a00c04c43e03c9074800008001c0c1104c81c150341c0f00100e030407610036070f510b082060643d81c04003902d0541e480d00c094650640301c0d4544076a81d050a0040002da102011003210030400024200700c006079101285542049140c100880d904000000042c01000c4404400d07822026001c000418 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 648918507 1250 648917257 648917261
    0x31302041a030f2b0504050d290702060c0c010213081608030c0a080c0a0b041109062d0f120312090601031a1b030a05040201030b0111062a030a 63
    0x42900c04404507282e480d49043d41545500f0b280c03080c411404020303082e550710740d0f80814110f5a81440c0e07140181c0351680710170000701c0e403c007051001d4440407030340501100c11702c070340d0b03051241f1620070710401c40c41a1a154400035900c0d540203007000040400480d03030000c4440c3c00d4040d1240410b090000140c007685940000c6d50f201c10820400310001c00d8144002101d10021044031408162100640f007515110b44420318030707a00c100c809450a10407401e01c0c20214001e0380d41140150b00c10f1280b00718840d21501000911030000e4010b502c60f540424182811079215044408000d9000102030f40300c84141e400900c03002c0b00070400c190044080c10303600255020100082072483c03a1011507603d2902da9030744540d610402400b00800710b0540e030340050484040105000d0f482803440101ca40c40440d0500480210303041602c4001005031100c00348800c540e01401024030340b400a10700b052410b0202c40040b80d48000181c852043c1da4803c003142c5c0c6c0c401c0100c014480c2150804107400b40d0340d00300040d0041c0 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 648919757 1250 648918507 648918551
    0xf060909050f3901020312070806040c0521040204021b0a0c090b03030d110d0c0507050f120d0b060906070305040306060501091815030c181103061503130204 69
    0xd454003401960401d1607a1842180520010400c0303c5200701d00844806015000300c0140c5a065201c01d003c025000004000a0f6200702d200c2e0780c030805a42409800c0c0003c0d00c0201e0000d1083c04010300c000010a00030b00b0012040441c56002001c0984450010500a100d0b0b05c0040d091750f03c22404c0003421580025460903445e110f800d13103004066450307031030100721104508820b074150010000316103040f0f1190009644126004942860302c07046241c84011580c2a85007000401d0380415004203000080c0134015824030000c0182c054029081140c000c01c0c485d121521078070a80d90f8010a80715200c45050302d4900030040c1c411981c440c40c504bc007070300e03c1d0001e120444070542020000308155100b81c40600841d02d0361403108050049511118024003005031410300031403000300300000819842e0f241c1c140105103080c2d595014425404646056446040541d01e14500800138440e05880c0c012400644c03501004035681c50352034806134051a000d17140c402035402420060388070594450305503041 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 648920863 1106 648919757 648919783
    0x3030c070c24170609161b21020c030d1b0b01031b2411100204091a0111071505090409080a02060c070c06030f06090905 53
    0x30105088486948100318405500810a9600040701c070520742410000f40310b070391600c140072400c1c0d100080d01c1c4074500404200031914042c410855038042103444240110148807600f0104900440321291952250000c2c002c281d0142c00010310124600d4003802070880301d030a0715401d41b11030482045104418005900541c0011070381d46401d80654032901180407c0d40c00351010801d0311417150401811002c2c0c06c0010286d46400784800f510445d0700e85031601e10000104146801c001c1412180c001d243e002080100d24426946c102c3d041d00300c1400a0030b405001d44600441780c03a8603295500145400a01050044d090100c0141410840300e0518518021450000c90107c1e405500107a40181c0081200111117606203c0c2e290089020503000382050042d072110380c440c0c3c4541c8520424036aa40302c624200c40041e401c0341d80140b4481c2d404200b14600703402c040341c4a04042e1400 = true := by decide +kernel

theorem cover : BRFrame.Cov 648741007 648920863 := by
  have h0 := BRFrame.cov_init 648741007
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648741007 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648741007 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648741007 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648741007 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648741007 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648741007 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648741007 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648741007 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648741007 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648741007 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648741007 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648741007 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648741007 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648741007 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648741007 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648741007 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648741007 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648741007 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648741007 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648741007 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648741007 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648741007 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648741007 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648741007 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648741007 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648741007 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648741007 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648741007 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648741007 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648741007 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648741007 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648741007 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648741007 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648741007 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648741007 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648741007 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648741007 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648741007 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648741007 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648741007 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648741007 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648741007 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648741007 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648741007 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648741007 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648741007 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648741007 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648741007 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648741007 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648741007 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648741007 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648741007 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648741007 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648741007 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648741007 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648741007 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648741007 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648741007 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648741007 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648741007 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648741007 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648741007 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648741007 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648741007 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648741007 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648741007 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648741007 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648741007 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648741007 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648741007 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648741007 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648741007 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648741007 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648741007 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648741007 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648741007 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648741007 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648741007 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648741007 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648741007 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648741007 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648741007 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648741007 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648741007 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648741007 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648741007 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648741007 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648741007 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648741007 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648741007 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648741007 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648741007 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648741007 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648741007 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648741007 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648741007 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648741007 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648741007 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648741007 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648741007 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648741007 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648741007 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648741007 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648741007 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648741007 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648741007 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648741007 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648741007 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648741007 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648741007 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648741007 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648741007 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648741007 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648741007 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648741007 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648741007 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648741007 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648741007 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648741007 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648741007 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648741007 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648741007 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648741007 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648741007 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648741007 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648741007 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648741007 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648741007 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648741007 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648741007 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648741007 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648741007 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648741007 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648741007 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648741007 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648741007 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648741007 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648741007 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648741007 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648741007 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648741007 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648741007 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648741007 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648741007 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 648741007 ≤ n) (h2 : n < 648920863) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
