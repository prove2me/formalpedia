-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4035
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:23:15.120244+00:00
-- url     : https://prove2.me/submissions/b415df14-850f-445e-8350-23483df580b3

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 725539568 ≤ n < 725719424 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 725540818 1250 725539568 725539571
    0xa0509040f0b150301150f0215010e15010c030c030e1c050312060303030906160504050301020307020d0816080c0d09020d030c031209020102191415010305010e01020408210409 77
    0x30a0510781198031905904100b01c5400c1d20207901d29000da81140401d005455010042d461400021130040512010326410f91040790f96909003400221548002039111800180e0407105000041d038501c07604103c000307020310386000c140340b0644008100c030b01c1000d0013405003c02c99141c2003482c0c8070640d88481b00345203078002e4034030b40c03483d460326a580342d11964900c6542c01c002070103e400740c903000c01101d015000b003000500898680e68550b41ca030f00341444c0d8071010310408110000340d0b0b860a0000e98812040c40c0c024028031000e80da805084807000401400302544606943e4040340d0300300c081030f508412000802d5445080f458114001010050b0020350300c00141c68480c800c050784040710584480c030075030b682e00100d0809001c0900fa0f41c1c0400c00280980c1080502001850324040c070061a540660b540d04116400d40f0141e5042500c404160000c11a400d4014000e0013024007608018510b180e0086180c031340340a02283d21040341c5c110150502e20f1004d410704981c40a4400d990181000410 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 725542068 1250 725540818 725540831
    0x806010f03020f13030c05010f20010902090f0f251407050a0b090106060815010806130204140117010e16030608060c0a2c13060e1515040b09060a050904 67
    0x31480d11340303802c4d1204070b445040d26000460070b03520030403600340d400031b4a44404800400c465500100300d00150b940e003501c1e650750204580076a0b900450310f8040c0420041c1c0c0c01440c02d16a0421251b403400611210191549a4120042402082059504210600d0308010345850a08504018841d07668007801a2094070340d10002c3c000070411301e40c000c040c07440080011540d160000c2da00b0709021543c0d27201c01e01440c40da014495014100003980641c0042000e0030100309a401c09089070815000851201c11503004c5854950b040040c1c1c0000b082d0101580d0385030340c035006240c2070084000300003c85ea401d00962201c003680c026002980580746103401e5650078582884c4546071508003640700c20006070700840141c10103020441000c07111807414001c80c2082107400074030080140c111000111155900c4001400016403444070303004030200340301d41034a612240100440c10300d061401c0d80c01180100030800120f42c2000c100c806210003510300c00e440c2c210080c019074081c0503004045400909200 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 725543318 1250 725542068 725542087
    0x30b030a150501080706020109050a032f07060905011806030b030312070f030b062110050d0c1703180f0d0b100302130e06060913080406080412030c0806010f03020f 72
    0x400443c1601c030460216209641d84407001ca003030350b0041074094515000281036201181c4240c10381c441c09450280541e4144800030b02c8000d425081c41f410020704c1d0070468040c4403450344101d910005180900c0c3c089101002d1841c41c0f11420b90603c120400d140d6140306080140c3c0302071040d50f402608244200c1010f1a202001900c1c1034140c0131010700003071a0641c4007059103440015a900414400700d5a60165145403140b100c42030041c004195201f810320000526a58051504187c580314004100d10720b440c140c200c011244074110904265001400b00c105001d896072504029032004070342140e0302c14185004100e041e494844040c180b0703074140c01003060f014442402c000032039100b56203140e0440c8001c44a503007140c9003801c0c44620b075003002012401d9441c000300103641003c2d40c90701c0c000000fa450795841081d50301591013100410707511020842401980210071110350980d04043c000012241c0300248411001440c040c1444440c1c07100c000003501c2641551340e185002d02030700d507a884c0f940 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 725544568 1250 725543318 725543321
    0xe1b03070c02011709210405120c040b12060411011806022103090d0e13090c0603060e010b2506061202030f01110f0a170703050402090601080610030b030a15 69
    0x44070103078089010103118001ca02e1035114410322480700f0034003030411890003058201500141011603c0c560a0500010415580303a2940100b180112002014050500b074140020703078203009000b9104134440500c41d1005078012a00030744c0140c3c00014101104810001078442c84405404a2040b0051381c00100b100b0740c0000300c030300441141808040300c010300c0314401002ca00c8201c803851015000b6421104049014048039020124010000050403d2282c1c0d41300466190400c140c413030204c014010004142c061154002034440d64411425540c104207410b40b10b4803504014025004002c0000408401c0c2500c13482107c650000301442025a1410030b082c0807001b00d03000b43e02c2400740502da030340e608405224407514031410185640c00d0007012140c020b0150888036280081c0050442460150300100d101075100b4112510001403a0801d401440742040c030003405207042c00361140910202c1d40c1d400c1b011798490480c81c42c0114802c4a40808a030400f01c1581e40105214400c0441c1995000c45 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 725545818 1250 725544568 725544587
    0x10213030c0509090d300f1d0c060f09060d09080301050301110313020d0c090c180909030207140d0b190b2e09051306060212070c0e1b0307 61
    0x440e4002502e46400c02095145c84030519040003054020445980c640f0280d1040045031038102e40b40c00c121044550383c8005d5441c4d62001c9119190f5985541c070001e81550a2503020303403072207001807840c283c540000c10b00030b1041074031610042030085604c0318103030385d1030044072100012140c0070700c008040c03450b01083c7c0350028010144a0350800d07001ba03040c00e008500380c0b481a2000c20444224074229001d2112800c0f061009039182544030b10080b0320000240185805015103544030086e400c84018503940c4443c06400c600912418840903401181c0e000544005548811610b21a425040b00024058010100c002007e010b10002005000050f601d183c105000304a481400710103011020003035410240030300c900c0d4040664501050100042070401c29007862030928190142e1104000b030004c880d800c01080120b62181c006000881e814040011640c40c0f290400b800d00070fa07a502c281c50903545001c0c500070b0040a000290844110441d5100c9041d40d1110941da2418039900c000e141904c0c = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 725547068 1250 725545818 725545829
    0xc0103050105011812060b180415020309032a0f0307060509030c10020c032a01060f1406183d050703081314101a060a11010213030c 58
    0x40c003000090254001c15540424011009042d00c0d018100b45046403c2c21948506036000b070350b6028142d805450312280f03c40c0119101c00700003e140b4152070540722103540764258901071070052043c03040a20000007a240c1c40c1c0000c070583e604c000031805e0f140702400341d49062110b80f48640d10080410b14008002003160358040d01080c0820703501c80800555a00c1501314a0030150700082098900da000e40c0c2c090200400020b00b0790f403a10800391485282140b509020069144040d20300080d588024401c0000511212115090241c90300c807880120002070900180294000116040111681460071510500082c040096400d009104c015041c0503080c011581ca6407248060f5080244a0701c0c0402050295888a02d4842c0c1a6003c44107880040c0c8981d03101d0350401000d400003001030b0002c0c00c0d00704100008040208230070384000d060b83c0c9102c0c400e81600000031106c5180303880f80c40132103000e61014242011a029a400a80d0080c03003103e06c0182407880111010042101207443c0008440 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 725548318 1250 725547068 725547071
    0x31704142a0a030201050906180d120f0f02061504020d020301090219050403050a0303020d0914030c0c0109051c0302030d0908071103032b14150108010b030705030103030305061f020c0103 82
    0x3004200380030440c540d43c00003a003c07400c140304c1100c0c245080710060880c1850f6a41d01d948180b40c1c08080381c01e18948101c1110181442403056902c1307075010084440c0c00389540350100c2075100310030340039440c1e40700500b404040402e036420902407031322640c0407144180c40d590011992503039218041402034010340004103156820313000f4284a148904103079420f40b03400101500014481da40d00368025407050303d00240701601c0701d4400c00032544401e01000b058901c0c2006c2d6a84503d02400035082c6951107401d1414880008002e10858507140741005000b81c03000c01c107107503100c217908041e031441c01480b00301c2031024181001c900c208040f0b103025054041c8901044002c01c010802015181d0007074a044482c501e2000015400a1592650b0000c43e03401c200d0002500c0c241c2c038200c80d00d511034100c84829910600b8642d0300c2e05540c0c0102028010522440000d0840c248500c00a055100620025040644900100d00b01d03903104051740300c170344410710081c203040061141e000e501c070054172111a002c41e = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 725549568 1250 725548318 725548393
    0x201206070e09010303020d030b0a090c0815030f0a08280507031d0907320403020906010504030302030f18060706050f0106030209100507060603080313050d0c03170414 73
    0x41c1002c201c1c81d030580307505030050042000300140c01c0700249404040b0300d0b070100d42104000345210b4284030b4581d000c2003d681d0380340340e03243c6042a402e0f0250602c42c4d880c042d92024804111180001c01c203d00d00e41c0d44451001ea450f01c91207950798034014104450781611a0901d15444400d800c20014840d4612984440c55000425119011841d00714110140c100100d40c000035000d52250088a000841c11005010140c01c1c01c10442c001551200c214825100c000031300b4415454503801d80c03544a0300920740a4505408d560f0002d48134003c106880007100b001084541d40081800d0b80301d01940000740206440d0702d940d0070703e0005004156503014480112500105201d840380c000c46108001c0507001800d020100a4119081c2e400028140c80709981c0e600007000107800e03803004601580505040300c149440504010342070054000100c414448080340140c002504100329400c0c4907501111200180c1c0c950800c4074039002c0490841c40d05021300900a41c030a8881c444400e4840c03402540100c01c3c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 725550818 1250 725549568 725549597
    0x8041a01061d010e090c0304051e07061b0f030804051c200c01230f03040602040e100e0c0705030702030a030305010801060506030105210a14011406011b20120607 71
    0x184e00d480059140c01c034410500003040c40305c03c01c006603040340c40303001100d103000441055441e1611311560304880b190000f4008114103940400da0b00c6283e510401a2505000c0b5642c0d41c80380d41c0007001006080c40b45040000d01804400c3c8801c0c0719039262442c6240030340c3c080e040c0061a070810600e2540c41c54090081c0b02d2505e01000945507c19201a1960603400c03810341811840042d66a0002052030800c00c40100c140c42518091402140308480c09a100d9042550711844208010401d41400f0081308041020446626007190018110485e003607503100075040c07460940c4141507029405200b40250f010401d980755003e94122800c0e00d00801240d5103500401c40144070038412142e001050700703014443c428100000e00960300310754041314a01c2d02166507200c095100000d00c401565954082201d01420141545600250920308a50140708103400c0c0006801804006011101d4101c5e10001b16140300010100c2000010800701c0c007120807d460701d40da4501110f4a07000118106055900e = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 725552068 1250 725550818 725550827
    0x16060e030306150318011515080c30100e090c2101141905060406050d060b060f0c010207140303060a12050304090504121103091008041a01061d01 64
    0x122002010355600c3c41903d20750181540000e840341c04807441c0c0c000305e0486a4401d210300000d01400003004e0458a140150703c0d414851401c40900c10b00c41d540d02045102182002121080c451581c1103004c103040703889289250658006072076045614400030301000c004c001480400701c1e1442c008605c01952040358958541c45a400c030141c000740300022070300c0241501005c682d5580342c03180002409090384000341c0e082c0107003900c400f0354200c000e071960401c4002c68061a035000c6429142402240d01d08808a005000c60a00c00f42000e69a0844024240d43d00c00444000c0c42d840020b40c1c2c0c0f030340a900d81d014002d6006100803244c9080030031048407110b90204c2524416580140340848452400c030400310070603400401140e00340401c210101c3d0382145407141500907406507040d007450090101c005020402d0000c01158554024001111039903034440c05905000c58600e0034001e1b076100c81c500400784010501d40110f05070301040010a0a80d071005804051294010a00d010505400f0043d503 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 725553318 1250 725552068 725552071
    0x1605010f06060e0103051504090b0906070305010f06050d0609020f040603060909030c1b2606060306160f020f01020d0e060a05220f050d0f09081501060c1716060e0303 73
    0x3c142ca0020244456000c0e80c4083c0e40404031584881d40c03d6202800a012105080c40480b4038032000e005004c15100200125a404001420b0410143d41865030f51a84002d0510425080010008904240442a4222000902c04003000b551106401d40c0c12103c0c0d9040340c0908000a4680800065001c829008407800e60b40c050321100c14000300c6072500c101c0d24050110030900088180300c00035000030b8080070000c2402c1d00da070314500c5521141212900b0b18a0140003c0d200b03071704c503200b40701585c0c12102c1403801c44103e605060640300c07002e440507402c028030350305211015403000c1480884031311543c00000d0241c4218060b40c5550703a6108580302110015124182d9904081040491078a84c00040f600040d00640020500351565903509103008240044440090354602c05030420541001d8400091300748000907145001d151444404900c00c14444e250400c000025800c06010149141d520000c1c103a042941d81c40c02c507903147c41c2e15040c2801048441ca85010031f01903c1c0440882034a = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 725554568 1250 725553318 725553329
    0x9030604120f09050f15074e080a1404050604030f0f050f090d060213030204060b07020612071407030905032a010e0f060408010515030705090c0a0c081605010f06 71
    0x10030b1a80f40400604c81c540598640d4203511103801c22042000c234162600303089100d00b41500041a582c0c142034442d480504403141030764981820340c01800080303000250a102e050305450007002558962034035001401d04140f198070510710810912040c0300c0d011558031320480c001d450b407905c6000040c0d011201c086c1c50180c604001a41400711103046000d1f0002001711880c0149114510070042d26004101d901809040001d0704400d2002c00441c1803600645000b04032410ba091704252160700410140c0c41a4020001c1c03008040d400070b040e03140203410840806000d0950b0030780351841c5280203000086140a038502c40d1046c1800202180c0c015410010580100e0000004461685006494910b20446540c0c2e00c110051802c86582c0c0b2000d0140c0020040800003280fa8100182c4040d00550f0302c02c940c80c0a5008010f09000a4480012190700b01030743c6c141032641c2e500560802c0f51400400840105841700000e240c0d00c11403214120041d5041c0160020080391120302441c408541c42440340 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 725555818 1250 725554568 725554579
    0x501060e06040611120313020f010203091c0c0e07120b030601030210052a0c0108060a080a020d150501090902010e0901030b1306090c0801090c150e100509030604120f0905 75
    0x140100c0d441000c03600440c04d45907044500e100d100d0301100700c403504120350310341c00084000450381c158580850302600da1a021300240d450100d0b00004644600715803c0d40b0300391469102e1130030302004186581d900040049100000d41410443d000a1803048611070000c1c140c1d04003100c1401526011400324101c0340d000300340c000c010004500548041e0030240f80c440800e012140310003089504105c030041542600300240c000c80e40c824001610100028100d41c1c01090010b20500070001c0c00a010040ca42d01110100e00a100c107180401d000e0004070f410f802041e090000000d207a0000c2d4011000e568401d072114005040d07101c062000c812003d00c405041d60450f9400324044a02e9280b000c602640114000318410341e06072540030003c03040780d001d0720b560303990b4803024418403101c400120080c10810300440700440304450300803c43c003010442148640324003004150110b01130405c40d1521403024003518010702d49800d0030554219107142000210780b422038070f826820702c50603100342503a500800 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 725557068 1250 725555818 725555827
    0x71a0c0306221b0f09080106120f241b020a030903170f18030f150114060c100c0806040608073c0302030705010c030e190f060201020c010501060e06 65
    0x68524014507400400c0e00d01e030b03030b940041c00e20f140b04000701558182000e071211210b292100d00c00800424003640580501e0340b404009001080c04000d104200c03d400c06001c00070520a828026000210300030020002082928010b403e98801d07041052940d82036030f81940b13684880761043e40c803100c101d54014001001680c00b4000529040114507110081441d500c0c1010f520b031100c840076038001c024072604841d071400030b03041504c1c08100c00f40401a044c07014250f1340c0e81c84d17088451011410f00410010400310354801d2420b4550b03809481c0042c10301070803205541e11040010009025407086800084c036100001651800c1c80d0058108540c141e10081010a140441100540500713008914031100700980117003c6040321030340e59411844101c001d0b040285103104062600383c079640028180320001161030042034008a40d114500c100f600d4002e5086c00900380504070f5002c64000380032a80c1d2140b40440c1c1c0c10303815809003030090960720080016076201c403c140d0341c1c0003400b101075620034401c01 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 725558318 1250 725557068 725557099
    0x220e0f190e010b04020703020109060612120509042d0f0204080a030e0f03030c0601061e080f0910150906080304080d0c0501270221120711030102071a0c0306 69
    0x140601070741030340d070780c0009071400e440c2d00007505980c030005042c1d0042c6e446a40400500856105501c010584021056094491550382000c1400340b0160102030210104c1d815503140c03aa0340000c0c0039617850007000914080380c6124480b040707007081e0090004910b032080e01e803510310f80c9200300d809443c401d000401e07120809035022580720041c0100160440300c2d01042c4c0c00d5603102000a0b00303a0514450181c00d2542c107103178009080c010b0380804000c81001c009046441c03240c109140a8202e0b104a41946082d0f6403840240c0c90901c20017510010300d460001803403500c840d08242c0c14180d88402805200440d901c0c0c1c170345a9640202c1c0600f4642d5003240008100680c0184244071030903200e040003185e03128100380209001f586545031318005601e0000d44204500d041612102074134007508a00d04040b42d0301754016520380c4d40499544811500040b0141072000107911101c11010045c001d561b0b8031024171f401c0981d0884210500c960070b0340400031408a40039501664450100585020f040303510b482c = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 725559568 1250 725558318 725558321
    0x62e0e2a041206181a150105070b0915040809120102090f0607020d05030c030d0c05131809081303020f010f020c0427052d060a0c05220e0f19 62
    0x1002d0441d4510303a5541d092102d03100c44640c04a2284c0201c0e0380f0b000300707501c4260640c00c05c800204007100518904808110907a00102aa1001a0002e00c0f950300359950040c034138584141c00d032200450f07180031801c01c0104003581005110091098590415070415411020300341d0003681d5205030700451264001405003443c00c0131784440c50000b81559948115525260704560152885500ca5040020811903041c1e03c0d0140c40581d45e007a10b40319143c1110790b01c400340c1c0b0341e03264003c0c0a14215101c18030521941903420040d402d03904941d102c0c0c2d035071480d00c6104040d09824030040b07008040000d002c480540c011074140010011980141c0380140d41e000030030008049081e001d8403402c0c0400c4001c40c0c0b40403880c08004c1c02d00d201e070300244142104182c000303a5207404464200309110802c002d20200e403a02003034072600311010220220b07100707603501d0f019104c90051400c194418200082c0300426000e44001240444455000c4003940d6210b0710158000310a007128204c941041404906105052a = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 725560818 1250 725559568 725559599
    0x1c021914160807050406210f03051909030b01050409080d0c0203040e01091a1c080c15040804091b0c15140a090203071205062e0e2a04 59
    0x580e025038001000c0460039110078922504035000b030398440c2c10280940e080c24803580014181041d6051100ca011040d540c2504c501181c00405000c0200110004c044c0a034064070f0903a860f042c03604a091024143c0184400350078803040c0e602081200c00000e1600742846810005600145014034000055191034090101d8440140031440308020000e5800c0d0104210750103080606004180c030001c81e03104806419003911014031900c1a030402c002d18448035050007480a60128840792150340d40c84030142071008440e0a1101c1c43c25140c1000200010080140280e6400090401c4001c0c1119500c20420b0194503d11000c00d24240c1c0c2007002c00d0020340c0004000d00c594a000c070300d0141741c21400c04070310400d645104085072a8030400086207401d001c440043d003160b00c1401c0401c0c641d5141c1b543d4600c006040c80b1a24980c1070810507940c0d6030100c417034840801310384c0c041c41103aa5400c8080300504d8100d81c40340405031043c00503c48044800d004400140a5090641c10141024444002d092070f = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 725562068 1250 725560818 725560853
    0x30506060315121005251103180f10020a020310091205030402030f100e07060806030604060b0607050304060f030608010b0a170f10020c0c0d03170703110c1c0219 71
    0xb852002504c2040e00380603852003040381440c0007640c24150015181d02c911021030300c9050096408a04014203800011b448014000c410761114642094020903160b0b40c00d92005500180b40c5aa90b41c20300380c0001d141201cad184207030119060900960207101c00c690300050700801c0a1003040542e2078031072268024642050008080c1c59420728040700c00780c5845003030160054102d0b15000035140480003404030380003c000a00b002c1a080c60301c0c000107512140000d000800a0341d80310321601a50f1218401d45828031b40c41021a9034458660b040a81134240c4000c030240003d09010000c2540c40c418020401214009456074008034117101d600003034101c40b00140d0985214001221018032400c0200b803903036101066005a840700c203040407504060196042c58015075401c140e45001070350110000c0411002c1701d03090319080d1504041100506418130000d44a000c0c00310b50544c00d80d9002c100c11b40010a80d40302100c000c0c0d00400181cac0c0352584454071806920300c0901c0900805c0725001284035142 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 725563318 1250 725562068 725562073
    0x7030314040506041707080f0d02070804060905041503020d0308071206060c060e03090d08070f12211a120a0b010803120601031803030b0a050402040b070303050606031512 75
    0x3840c024901501034100c80039102d80c1d000d1401d001c03d100f0351510742c04600e8445002d00d882c3c000c960b00c1d658a1072003a42c440641500c00010300105280c41c95040c0d441f030950004030300d60b0700c603507507a401030444601d4003c9500c1146403540d21103e10354422000f03000c42e64050035587e440422a02c090345c40420041105080c0030000c1084441800740c1c1c8107040c06000d90b034580301054009820110704032940d502c082ca15690040112660503034509d0a0045056030003c03000b5602c20082c40c103003820300c508540060005040e00e22040c8501d400c10aa00d81d0311144403170103511884141d0482003600d440f5408004141e007404824603082c2448604200901956802c0b280020805d43d142076907071809030f00007c09500041102c09840301001d2405400003400d20b02030050500d880ca480da0345826081005090641e903e40241281d110003004800030f10000b48110b40f41e6aa8401d902c2c1990300c400012400030b4648070014103185005d1081d68062062089480ca401d80c0810911080c005041c031290407a1 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 725564568 1250 725563318 725563331
    0x402030402010e10031a0d0506011a07061517010c05090402090a17060610080702030d02072a05030f120706020705071a0901140c0607140403050f06070f090308070602070303 76
    0xd1301ca050086040c3c2c5525039000036845800301d071848a841011070424416a41d9031580000705a0000300c15040d90030403440401e001d80aa5154106813285280c000c16450070600c048003107100a18840049654138241e4403956010429040d080b1000f040344c1401041c42400100007600b00b503400351040e1034024282e440c40d01c2d1658a42c403094007080341449200d41c0610204881814101103850100c0e01c54241000345042c03c04001e51240070b24694540c00f03550200d92078050141c182c40d0602e0354107002c14420408400e0b0103102d6034031a80d90007403034024400c2c009001210800012100d015001c09440c05007880c41c1c540e00c10000c1e600021050380c96105034040440c03c00005d0b0820900000350004c980d40c0c85020030000f402c0d00c40741032101076030a2014000c4404a071004103110758400a549070190a4600080145400740940d4001510900c140b0034658059500050301c0d0f40561520340f9090f1801590140c100c600144601008110b86028040e140000d800764001d0401c080c03181c10085800c = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 725565818 1250 725564568 725564597
    0x6030c031239061817120601051602041d0d0f0203070f0201020102120a09060b0a0b030a050a061205010f060e090a060902010932120c09100b040f0e0601030c0905040203040201 77
    0x180c5004061450b80c8802e07114215003080881685800c0007241070251794201960003d070f280d05950010301c00c905000000801c0f809681082580c1e89a143d4003c0c801c0100b000b8100250b410003039805400c468a205940441240502a100840d05011164010340c070740241d5a56001401007044000c9055640900002d0300c0305015260b039502c0381c0d80f100030008401c0c1e44c5091980a0301d18000e403d07401054410428802e4105210032030f079102d0444040415642c80d021300340f10050455503c00c99154029203604c0b0108907064000a20079a5240b00500c0f84a03142e0003141c0041030203541410b01c0e5884203038004002407440e000501c601e40141008400b182e900c0207446051864100410b0003008040303006100c201c4480e440112202055418410340c00c4074034103031651031110f510068450000c907030000d9240602056420060140c4100c815122941c9001c02030514890340a8414840f400800040b019446846520700541c07455403400006480c20301800000e6001900990412a40340e01c100705 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 725567068 1250 725565818 725565821
    0x10902030c120c1207031e031706010c020d1b08150f10060f27180b090c2d0a020708060c07110402160803070e0103110f0313050106030c03123906 64
    0x300078180c0b00c000c811345903480c03230002d1901200700d052007180c244071800d201d09039034040038000204c0d6054800c00e0f020400c03401d0884200c076007107002c0c00c00c008010b0000701344440f000c64180da030b0410006042d02d09480c2c5651001030b88108461040e40017040103020001d46116601c105003030720180c10040b241600e54046801d1020511594004440c500f4108101e00c4807030490011840e106842c0410800c0c0002e1f0005046d402c0c0548005540b0f50302044000503030240000601c5403001d031070440d40d100304180740302e81502c0d00701644002c00f50243c0800050201d001160261040d080f0a1200f46003007810b1707442da204103042401258115501740054003680410710200b0030715501854075180c4a13340088014401c3e110400d480d81010304105501c881140e40200b518040d08854580315226510042c03c00004200e000c00641250b00b405400014014550580c80550f809045460800c840c40078065810b032002000c80317814010140f100c040542e9100d00031006203550388141c10a00c0d42952076050 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 725568318 1250 725567068 725567093
    0x160c0b0408030609011502070504150f0e0a05010501211a06070506091b0a0509040809061209071502060a09021c030305061201060b2b0c02010902030c120c120703 71
    0x4811031030002c1072014a00e801200c0c0c1703004107404211613140c0c0b161003400a446006074440c481c0a19204c0c81c0d0400011240c0b00f211000e44003004080c03903900d64441480040c0c080070b0320312b00c81e0a8900400481c19510404003001030440c0d0f0500080050070840342c500c01085c3c000c51603501d03041803080c40c200c180c0d074030401030100a004000804d014203003405101d003401308001000800d10a099038509007a01c270441140100c1d81c00b220175003d04e41d03a600340f45076540305000015500610011f0b02c803203425002500580101044811a054141c494801c0b59080544007020800f6910840004049c0b40080d0040d03100544050700c400985000300c0c40c05065140141070450220b5110400c00001d03060012030700001c0000c03c402806170602c1c3c0f8103000030303070b104401c210400031300042121080f0071143c042c00395101a0b199410000e05201140080c0203045907007040340b00c0d01920440601d54600703c1c18900c20320b084140030704442c0134100d081010700c0480704c02c5116075004040000001c5806e005542 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 725569568 1250 725568318 725568323
    0x90408070606060e0f061e0301032a12080a02010b1011012318030403081207020105060f0a05040e0a02030d032c0706030f0b031f060e090303160c0b04 66
    0xa6240d404524116058402641160040101000480080d0f03070310301d509941400001e441480da160b16520848080141440c0070011202000000100704240107180e405480c0140b6000f1280701d04c8041c880da4916024810500e008140740a44000b1442c940010402100a4000000d4500c101008074040c8074080701140003040240e910943c0401c0c00707008101c100e100c90013a25181d08510141440450005462241d080781c6c3d24076100d554060400171500074540018010741c070307401030003030307010000c001200e424006500f40008604c2c0d0b407e1400000240240042202038080c0c148030610006100c80c40e00703100e651040254175005601c0a0103070080544050b41c0104640d407080d905621001c07020070001e407958002001d56034101070040f40c1c00058400601d40810100d150100c00c4002e00740c41490103901d07000700b0086c008006401d190340b09581581100a2000d01d580d2400107410020450303030181d03d0b404c00c200003010a880c1e508540503104031400c003220209119111b6018651003190304 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 725570818 1250 725569568 725569583
    0x91005030a0f06080a0605090f0f06071b050c01030e030d0204080a050c09090c010c03121505040e0f061303140406020c090c1612050d0f0614090903040e0a09020904 72
    0x340441c04540e80140510380e10541010700070940390491040d0340d1000d100015001c103580303c2c0800c48210052190aa501d9040812501c028840341903054036164151a4000170509886154003101c070b0606026400c10b8204000d000041d100741c005401501c6000e00d40503c038042041003034006030541c400342c03014050001c020140c80002d0300c2d04c0362800410203c0c1a20800e000020020388402c001002544a0420704e04042030150074603040e036400d4081404517100701e0418090041c3c0c040081c0c14281180c2c002c480c14001400d420001549840c0f2408035103180717400540000b04800c42e40010091454407034034261401300d00040340c189154005400c41e00041e009201000601d00e08000025000b111074440d0518000441c080c0c101004541c00f402040c1080c513924400101e80102c003518104e00641c0c00c14410080c410b13604c000100814000c00d900c0b115144901d1803e402c1c035660f2107109035181c0000350324150600442c07594400008010103100c3e500c911200b0300603200c203a00710b0301451140c2e20 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 725572068 1250 725570818 725570821
    0xc010b040513020a12020402071a0708010e070f0809250317090a05100e030601150207090606050412060e01060906030308161d0d0b01030c050925030e0309100503 71
    0x40000703580024016140d008000312202000d030f618001a48221080d01c43d110890f2000c500c00b00e0007a004008001c1d0110a1103030a002c194501100d1161040b43d140d42e40342c0e02ca80e2590344100d80e585043c2c0303090000610801c8480c00c80e030b02800d2515000392140301180e04600c0390041500300c004845041740e00d5603c003010104100b02800c50040c03010014074101a0900300d421022a4803d1004c1c404c180c400c5603403120382c0b000c050140600c0240d0b924082c080d600250307145e01000704000459802000140b1483c0030000d44070707081d0301c01d04055603084c0d641c2c01d1405240070700c80c82140b00c141c8011f0758060f68a01064510b281d091007030b480100080c0d8070208019146040c0602281c10040803040c3c0700f9400803400400b15840100f50700c840c030240c1113a402801c02c2d400494080e0f84191001084442c1c184008014000300d0005002101d60444141c125540e892010051004441c20381c003048a07402c18030002807a00a40080a0583c0110116810800100b000950103106000600d021450010 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 725573318 1250 725572068 725572091
    0x605060304080c121e071a04050304050114090607020d050f031920070510030b03010617160e0f18010219020106050a260c030609160e06130c0e060c01 66
    0x80004040007031a400142810301041440c01c0c150321407071700f4a1382070200040c102c0c00c106800d00003040c0400031161095072461305244c829541e80c00b901686012840350781c108041c42c006441141c000c00d002515050070705040340c2c00d00ca4083d01804c3c046405002d040c0d050084c00e5020009002d031605c1d1800080c0c050401c1c0c000c05041c01c50783d80d0620714100e000e4a40c00179066000500c580441c0c01c140d0b104666210520400c40080100c101c1c1c0652650070900300080800c42108815402004001580c0b0380303941850854a82c1001031142820700c00e00321b000642a15104400c0e1036202507981206220303031080c0d20505003280d10009040010b203e00c0e8880840040e4248100405400705862a4002ca420207050b8140e22207140c04000080c02e442d030b014100d2a030180035144803035201504032000d0b420110700e95902d4200301c0c0403070b901d0326000c03550028140c020031340c110303001d40000ba2207080880e01c810320b00d80c041d001016007041845900c0394601fa8544614004014880307000c40009142d602d0326 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 725574568 1250 725573318 725573323
    0x12080121020603040b0c0f0a050c1009021f180611062a030a06120f0614010510030209010903050715021605010806120705030607030906050f0114130605060304080c 72
    0x4001951031403040140c0c8100684651080300c0d04150440010400c0c6da540e01002d0706107108030805580c10b494080313200002e05400c540505051480b2000b0b81e800c130341e100001803048446680c4060b600c40a510504801c840e9210a9105002242c0c41e081da40c402200ca403400350003003940e100ba03002a00d412141c41e40031b0401d01045800175140c01d014088000d0300006150f40e407290b4240c01e5a2240000f000c40c0f503060043e840000101020617800c00c0c0c07461a03080c03014240d02c508070f003521513506212406140e07801120550741038620090142d00d42d0401504100d000750000c15160341070044801010012031000c004a00007080f8814054a007113007148002400c20000e80018201364441200c103100d035130b0b0007540c001e502407020384441d4224102c00b42513a140c000302c0d42c0800c0c0c041c0641010301a49580c19000303000002e00409080c0a2034032240c4203c0c070840405d2150105040b40300d401006203241c5400403580e4424000400b1030f05645a0000410f0341d401a04e084500220001d106401680d05 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 725575818 1250 725574568 725574599
    0x1b02010c020c01022a0306040b01080d020f061303122c03030115050c10020d0b2b06020d0e0f030702010306080a0f0b0711250503010c09030602070f120801 68
    0x3144081c0141002c0480042d58451004083da10401004208051440890740a003020018004c00315000c5003040d0070a40c080d04001c3c021a000c0780140a0035060050001448400310001c480c018403590380c03407240780c0c0c1800d0f400410403010885d01078400131000c0d40501903280348004006a03919822255095440200410903808a05030424001001050b20800e80040e4481d00da06010390b0390305040020905041d100200400c00610200d08483d2040340d590045440ca9020341e012003401c0b003210071080c0003648001044d1144545648050b0010b82d060700a0004900d815034081a41c241d1b44c816603041443c2c0c0d0b03900c20300320340c0701103058815036a0601502000703140c45000740010280c141c560109003580844003410207801e01003c00e0b089031140e010000c4004801c0d003614004502c80d100d0800d004241054401c0310a0a007402044510701880b443c88107800c1500c1c3d481c47c1070302d15620407019401c40f60003903454801e00225031000c2034800034003038034191060381c88080a40c10000a40a058030 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 725577068 1250 725575818 725575841
    0x501090308060f01230a0302130e0907050a0b19020304152105040b04030305060d171b062703070506100905090102040b0715110f071a040203150c04091b0201 69
    0x440c1e0140d420364094070803030008550b80c114141692146c500c48264040e106e014007810180380b004500141e03d00c011400140138091400075102c400395200d040001040c280c0c0030740029007204010b241810803c0c540f2190038000035005881c02d080d650b01104107a441100f0004006c00c1c8407018081001d0300850b0428a0000000704c20030950415880d541f140000040008061540d10340c003003050350b41c4405021816550084000043d800c0c99058011150402008101d450124031104031a118020510701d100702c1020303030b422403600f4085150000030401c4407060205400104064004501d0600805200c1c010743d003001c8204e1031800e10b01908032070004140024591040c4004d01902c01650225111580c00c8207800303032441c0c03460700500e005008000032010500703c001440061200300300e021300030550040f6103082c404502d2080004c02001d04450081d4142c01c5400e16803180c00b041610780381c0000950794882e041c075403281c92a400b15a0b0341d200001103000d02a07840c8002607424083d0284812 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 725578318 1250 725577068 725577077
    0x12010b0415030506060105030c0d051503060601030c08060d0c0308030f16030b10081e25020705030a020409080f0d06091a010c020928050604060b030c03220501090308060f01 76
    0xb455900c4a82d02c498010f000350741040740000101c1c001c4640f10080d6210079510131400c000340d041c034940101c038011010402c5402405900000b03411580244103c0706c0c407400d50b440720615035803174104001c69128080b00440e24254030782000700c04a41510043c51141c0001001c0c1d107440d05081c00040000c01c1004c03804400c01d0b040202c09051034484010060185155083c001344039211082e0ba00000803110520900080d146c000300680308803400502e18251043d4410854454182036040303031194038a0188070303056400300900c90014100ba9020044d0b01d8080e43d02c40d42891008078007108180e2048071804902078903541d080c42038002e240704980701070082d150320500e10a21500060141c010711440a842684281e00299030543d02c0161107240207825400075660941040302c0704020300065590601a52403d0004641007184000f01d83c0140301960340c0d00d044d5030380c03410610f80203184e14070249007407000d9440d00306c0000c009001c0c2c0364401c0d1180d215480c042c0303031180500c000076030048141c90400 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 725579568 1250 725578318 725578361
    0xf0a0308090d3320190e090103050601050a0608091908040515120708090a29010605120708060109030204200f0403050c15190e12010b04 60
    0x14001011036a201009640784014442c5609140100080140e0401d1180050f070a0064400c038041074601088241c1c400c08000461864034010303101e203400058441407040030011501300c810801d40c105500340f9070346019401c2141c9200401e410020071303402100c2070b5204c800148880e2400d04404001b91601d4649440d141c5840750b0100d41d07a0a2000d806020005490104420701504d070040b1009054040c00d8818221920704e640e402c503a01104001503d00d503c030300403c5030940315801d82405018464003c24411580e80c8544030101c408105140d80c1815540b462210600013102d891700070101034403110346a5012019010003910300400307020410003800204580b41e0f82201c40c41f8180da03015600000c0160f40c0c0014100041801f00400c00300210200d480ca0214509100074425244030b0010341c0e202424a505200045c003500ca001205140180a19141c104035001401515545403410560074086c010114104495690b41c0e4540c0c0c1e5102d11706005241007900403651101042c01124914 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 725580818 1250 725579568 725579573
    0x5090309090112051e030a030f0509060c1305030109080702040c09030b1819050d021b0121021e04060e090c07030e0d060c022406030601031101210b0f0a03 68
    0x2a51414050441c3d241205851007083c4401005081c3c910000c0ca2414059002c01004442c1d0b40c0e0807441340100002e043c8010b92040c0003140c01664000c0208c0002022162100600919250042400c201d28441d9045001826540c2402080000703801490000d58640241c018403080e1807101c007010090048000007080000c8101c150f083d40200000b41d510340c5607002141c154100b084079625400d55080c0c101c4090103016000c102c070f00042c1d10035000c175640500d1025414014072000e0030310358046800084442c1d46a01c038910392042c0400b0826005240c411803d2070f000b07c0708061a403004900750040340900196800040c012001e000403100f0248500d0300c5981048c81d44079031040201040a4900002da464641e880d8036180154852810300c1802403500000703540d03460f10000d9070018400a1701801454040c1e44005000301c1000c0c01a040d26820b50b1500f80e41e44003059071860400103801e419000010b840c9800703151040c00c440000c40c00c01d00030301c10820954070300c3d0200c0c1c5c414003103034004000 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 725582068 1250 725580818 725580829
    0x311070b0c0310050a0305160618050103021b01052502070305030304110f0901030609031e0f0809100207060203041a101203140a0503090d0f02070915080106080d0305090309 76
    0x41c804641004240d9983d6540040c400a4403240e20140d00014001000b004200e404200c0d1403281e0502c0b0314030352003140c0da00011503650080032004103864a900100703105a51103034000301004138620003407500311040341010390700b12907040700c2034508010b0b02540341e150340f105000c0010504555100410082d811511100d40324030000d88001c000c40d41902c5540500d0300c44501d000790818005162041070340e0741c0c1c03c21a01400602004400146500d14076200b01c101c40d0105461344021a61400c82ca200745036001e684810010b030501403e44030300c0d02041002c480780d00041100ca0300c600c1c1e002d41c40e401c140c941000ca9034014103082c00c111104008001e100c0c0723009060082140c8400f04941c02e2030030b01d42000c0c2e07031304020201c1440c00240005a80c0c00d00c1a00f240040d4003c2080c0011034810450569040707610011820515005070080c0030200130b0b070049a000090060303c5100c034403248507950030703203682181d00c16401202550003d11f81070107030640520996902070202c001440c41c10fa141800903c = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 725583318 1250 725582068 725582071
    0x10225210f0305060d0f05061501140406030207060b03010c03020d06080102040b030f04080f13061b170d0209130c09060801080c061c05011e120b0a02090622060311070b 74
    0x81554440014055581d041280203419400200446d420507035801d01e207403561000c0b5000c1304558609208104654032500b1000140900703010294200380c00c2c03a60031406540040381c15260a52510f00320181954203118801c200d025585005a542c0c3c140c0c400d4006452055002c41400d0348180001c10040054200b100e0340b00d1003d00d040724043c0d40b54034140415005482815007118008581200001903031901d82d410303207050780c07190804c80300101c02d0400c01d01380200004269000d03600e81c20b000d4145a401030280d441180703038054100700885002c1401c40c0c4108040300d40d02903d8100071a4102d8104480c00082d100c82e1904540541c10060350702d65501c104400680690f44c00200000303003032405801000c80356a03c1ca000c0c020b950b0f44001c00c0ca0407a548100c03c0000808400c00003d0001050300e4500f2000d03480002c4002d15581d14004030b0080d0000202650031040800c46030601c040b80c0c0300b0040c03451003448032803142c075410580010200d07204500031400841c030800002d00801c50141d03809 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 725584568 1250 725583318 725583347
    0x6090605100f11010603032a02010c1e08030901150803040b0412111201050403020c040c1e0e060304050d18030206090d030306080f01090212010917070501022521 71
    0x2820b81d104141030441d15815120741c145041d510780760b000b104044c1c3c410b0300742c4048007a0442c2e800c01e05400711102c0c1c620710040f100080c0030a1205d003941000400c2d0000503142e5411082c880c0b0030864160701d41c2c281c0b030b178400c5601c07100c50395541c4804900740c1860201c3c3e0000e06401c03c0290b092a082c26410b484078801da0007031161400101900d802008044c2ca01240c02d0341014015102850700300c882503001e00b4094404a02600034032440b110f441c20705120351406400c19541d0f0701d001c0c182d142e400c0801a8030403924141040705409520400c1d4650200950140d07100b0801425900f5a00030700802c512009404021448030124042015903035440c10b0703810084089640f43c01c0312849140690040820f90b04c681404d000d24401c1c01c1e448041075002110142c0243c608003d03440d0512029422100307c480020040f800c03014901c1c0c140c1140c10081d040407840743c2d00042c42c0c143d0035000192281d885d81e440740608a000303550b503410042c4002d80451110402c80c980e9074605403201010f441d820511680 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 725585818 1250 725584568 725584577
    0x90b0402040e0d0f08091207050a170a0c0f05030403080f070b010501050403080f1b0d0c0524010b0c010f0513150e28061a01081b091c050d120609060510 67
    0x1242e0381106c1803016125030a4261200d582e218014034290f6191100c407e010f80351403104d9401003078841c01c1c034001c031340007480140d845e0440d03507100366150440e003ca01300d4181c03213521080c040403000400da980105141c03049405c40c940c80c0c1d13a844c80c0005803240c058110070f040120034002003002460305015140c0c82d0351400c4a00c0c0d21851408203404101504048a40a41c81648001c030780781500302d10f042c0040d6006405a502030310071003c2200c860900050203c0340000500010092011010094900c125100740085014111018004141c981c1a1041c08952644461240800070140c200d4842c81c1c0034001305100c3c410340c0300316103030707c0701c010400700a5490002e043e0340c40ca00e0030b1900f2180d00b05500030750410424a4000d03d400c0115000420b40c2c0c0441c05180121b50b00b0702c140c08001c1c0d8002c14060740c5071300e00f0f04080300b1b02c1034001041c0188107402b81c1210380c1c880003a03000d2211840420080e03580328078804117884200240c0c1c031560b00150b000c6240010a102e40d4070f40c81565200100c05052 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 725587068 1250 725585818 725585821
    0x5013f0f05060c0a090b1809040302030d0f02090a1409070311040b0f0a03150f0b090607080d14151c2402030a0c030203090a020d060b04090b0402040e0d0f08 69
    0x14803000082034603000404a009490402204284440c00740c02140c0480d82c0c1d10b480180c0701c03030510031540310750041d44a800c603111030303d0340e00d134980350b40c4041d802486403055074102001403111400355520640c510a1282d00441d80c04a2414054002c2008104010800c01d0002c81000400d80160000d0006800c0640718510f02918080c1c040844d002000200c141c240e541c600b1001e0a40613030491001000002d09180d182a0810200307881300013918007911421000a00d440c88102403a07100d416038542001d01401031401007181c50340030b0300c0c2c6443d416401046010510240031078408005013002442c8800b0b01c070400154070b415503802545001c541194850402c00d080c840a03442c030301400c90010410310f061019072189981c02071402107c5504003805504080c0c081a002da000c00c40d417055850703112072500c0025150446510360142d000d0b032030029010f070f4450040b80c16219046001d0340c600c5c8022003403201710b08151159195080016003c0e141131100943c000780340603032000314441041503090 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 725588318 1250 725587068 725587073
    0x3050d0305040f2d0b1f06080123150c0706030e0a0b18030a110d1d04020a03060302032a03160b0706060e150301050a060b030a020708090306010905013f 67
    0x101c500c02000c10402c16003144c9841e1501c03400c2ca82080301c450380301103030aa100c2003007200112115401d4603541d860b0340080d83c6c204403101d050803030111202c80c0460101c071803d0b04d1680f14100d1680c180d190b10104282e483d0985101c1c5460250203621160030545860074002080c1e0b4081801c3c5c1e0410352201d82403900781c5442c6040b016400400003c03407000e020020b0200319190b0000c51245515031624165200c0c101d00990580d5601c40301680c103421400300000e03130300310ba1801e41e00a00e441c4d1410700b40058281d89035004a458604d441c4000034a04038030b20b1810451100d10b004840b0710320341c114018040b4101900078604c0c54000d503c15031700c0d10003000c5480703002c00140d80c00c800c0c0901840070000800b0302c0c000c5041000890700c540081c0c000d51038000407410503200d82c01042c0540d818204001e1851316a0040f0300c00943c0b0a09054072602001e02500d0f11079a0b05124103402000c0807030b00400c50b0750502c0c4c200400a00f21030440403224000b0304001041d50003440c85030444021121300c1900d60801c50 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 725589568 1250 725588318 725588363
    0x10302060f07060f02040e160c12110f060109050603070b0906090d021c061b0314041424011a0406090302040b06072a090b01021509190c03050d0305040f 67
    0x450000030640c0040380211f030342c0203490140c0d849002c41ea1064030407044400000c0c1c42c149085c4002800d00d814001d41d451402d80504104040c800002c811210010b000c0c8680e241070800a8220f01071a54030361090011a19007080404090064081d0540c507110509000440f035120f4011a54000c101c402c160b00295550500d40d00c05c4500c4651803121103901c10b191000062207018094080e078941e080d07118102174400d03c41e9021034621010618259101c5454092200a050b04900701520420385000202d201e441401c171011100a10000300359418040c4c4408402c05070795007203504402c21b10040100b968032880200490b60155400505d04950102092462080c204054504940743c12445400340301c41d94170120700401c80b4100d154460f1600d2082098031020358800380140d02c407804d0080c00d100d69898403500102c1a408440314211504034142c1864000310040d1036a80e4100020401d029090010b012080d80d13615040100f450107a803003000c040503000019001c1840d0040303c1c036400100 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 725590818 1250 725589568 725589581
    0xa060e030f040902070c0902040510030e010e2d062401020a06050c0304060f1806111201030c0e070810031101020a0b0a09170304031e180f060215010302060f0706 71
    0x1807050745a903030741c41d00c400e80003039842418111031403456039600140b030040714804e80302070320b90061464007045000d0300100c000d02002d441c0f50b0601c0d56102d81481d040c03482082241c05402031140d81c0d03844c00d003078590340381201205040e272102c1981288041003080c06000e00011224100c68411046004440004134600b4601940040c40c903403402007803101d084400d0006d1445107114010a0200c81d10f100300403070603075403404041c0c000319a031001c01d5030009850b60000329002c09010314243c00c0440360b501c3c0d010101001e80c020b840340700d060f0109010136000070000941c81112414003034005d0400405441c100d000c24030000d00802040c41d44c000c6641e20a0107110920747c1c1002e4a00c1903414105080c10041180580072600d040440301c081d00d01250381800c2c1c034812030f0183c44146803110300c00380042000740c911307203500100805115034016481803070031503601420241810303128660412001a1401c11b8000c0780280754034407407004000503aa2002100d110300c03074500800741c07111130629040001c1c004 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 725592068 1250 725590818 725590837
    0x72a120302010b4002070b0114010e03031603030b03030d0506090a060305060f060310050108010c0912020a1e0f41101812020f103005070c110a06020a060e03 69
    0x943d06c090008099260f4103845005103172080e044400001503850030140c21583e90142c10a10103088003080c3c0e05840345006000e400c01281030011100000d08650150001504c01c568440c144001e034100000e281780c0c4884000b0341040b00034110740307860b66117180040c8501c91510a01000440a803002d102d044181245640240500c0d40c403500c0c1507019000052a002c006050f1200c001410700c0301e110a07960b25a00130344440981c034140b0307040383c0c04800c07400807101c0400c91000002485954104441000300107003c1c900202c5500440400c00c2d480750804020060009225405142c14070b0307104078000503608443c0040c6199250714140c901228602e10040c003c0003000700082d0b0001e0145e5000d5180d81300703d803003101004286080000c0030a10701c0503600040ca03007c0d1b42c814010f103080078060154030805c3c141040342e40f400402d2825158110380380b00c0010490107440c020892111403190306003204442e2142c0490820000075a58210440054040e9445005000700300d0382c03e00c110b40d840711 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 725593318 1250 725592068 725592071
    0x150306070903020f1005090405061c080306041503020108062209080301050306010918110310020d0f0f0c1202130305150f060312072a120302010b40 65
    0x94408009081040c41c1e201c02c0c3d00a40455904103e640703040c003401903084000313864036070600111105100c01050018244d030340050b42e8203500d001c86d4489281c1e454100388a41c50056580c90401d051109440a0070580040c11008000620041c1c2c0c1180746550301407019120341003000c0f181c86c0d041260b805c03120300e9061418504001c5006000e040c0000314140c40e0107404607062070741d07a190030343c0441e443c1400c02c14020450f80c00c0310001403502c401196503200c00600b115108080c9408403c03c0340c4c002c61110940c1607441c2d03002d040c0300c400ca018409404100000401581c400c0c034101070046018000c510b414503900180950043e0394208000010b103401038200e562010f41d003400c002c0d195000345d440d03009030b4062200060040c640011608003020480f5661070412020b0360b00c80002c0881001e5042180c0341b00300007102c000807681d08803001011018210440110700d0304010f0308403010890410701aa4000b5000481404101e018400d90803c20b6400f9000b081900b41c4e42c200d0003807401c52030744043d = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 725594568 1250 725593318 725593321
    0x2070606260c0f0907050708071718040504030206070e0a0f0603020a02101803120b040507090906091503021012020a030603021e01081602010b120706141809150306 72
    0x2000481031080c0010500703801c640107040400b041288544035580000c0c0c0c0301038290000703070b40d03148540c01800c807081c4102c071460704210041d519041055a0166510383e10315020441003682c07032005d02404d6505009850421150515480094071070500401e03000a000f541128207a075510340071031a4000f0701251004000c00380d02c83ca07000700a0340c890180d020052151300c460382c890316841c1c030038a42200c0e212000740c407103000c003903400381c2e10780c08002e001503d05541c40d04d102e813140d1500d01500d48200b90a40d40d161006083c04a00400c480840d0001c08a4604e40403560721a83c0c8881109000e40b901241e04c2c1c000a003a5102c1201c000f80c1203102c2800003400480c103030000f00c5d01034205000392031003194411810013002c62a8a806080b40402038001f5150b030000c0b4a80340380e04407810303000000900c00481d800380d554003c141c042445000210240c0c0c0250700410003980d10601681d0098000b905040c54002c52044c0e088482c24803d455501c1240b6407400311384503c00f6107501001440000d070585516 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 725595818 1250 725594568 725594609
    0x815130302101a042c0f030315010521040201180501020c0f031c120606050f03040f0c050a030b1009060b04270f0c110c0a09051306110a030605010e0f0402070606 71
    0x300f507078100d056014117103000e040c0b80c0d1100d1302089400c1080ca0140040d800c65641c3d0030000e081d995460134071810302000300300c0c101510611121001040c40c07801c10140c0d40b410702d44001488080000120f90500000050910541e81d01060601e44440204c442c2c20048185c2400207040690401558480c0560a1800760015800c20408940d41c111100100301d0560354003170a46041c46260b20107800726004000180004076000c580a140310300515850513103075140c501161100c110b641041d90642000e05c00c004a5100c1c80550301c4c00380ca400c031400e1164502e003185c03c20741400360b0b00803005a1082460401c180081001100101140d640340c1806160400c41c0f140d0001c1580f1035001d40024401c68844ca400100011042412500540803107901440c18503540c00800c0d001d051030755044414000c060108032f25006407200c00d00821105a83c40a03c000e001d01110815444241801980d040300c030350b039590b184070a22070f0400079940566101080e2030302d1402440b0716006140c5107a92650700c00c10 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 725597068 1250 725595818 725595851
    0x306030f1c02011a0109091d030a050d0f09022d030a08120709030b061002010b030607030b1c0b0114030a02040903030c02151909080c06010815130302101a04 69
    0x900540ca4008010001203941d41076605014104c0c8240458805842085001c2c100e501a00341418006481c1482007642440c4506640c010b01040c0002500440c80c2106020240300c1c0d49054040b00c501003100b240c41c2d42c0401c0d0f0f410311030f10182440c580c0310b406503081080e403083d00b400411390003401d032650b5455501e010492030b082201d42481d0700c0344c100e00195030140074511481c00c1e01d070003105070085656150208664501d480410008554803600070880b0b5480030820540903c0080e10003291000d0820203100241c00d45000000034007810981280124000d1343c00c1a055419540709140142140000700c0e1810300402c0d03000703412030700e070100c0107080c16410b030b205d200d502c107440d03090f2030000c070803410343c844842d00685540c0390f9103e01550340021034800d54805a2410710500c0340c0c0c0e081c9502d020100f400c2c03e80036403060b10290016100b007144d1400c07031046554010752400080403c40281e4400039a2440c2d00114109665035907000744952103141813140414400c010000c2c003040304000346030390 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 725598318 1250 725597068 725597113
    0x40b2403180706091706060102120c030d05100819031b0309030803040b01030c14030304051315090f0b04091119080f0318010c08070303091a01090c0e010906140306030f 74
    0x41c218041108848000c1170114440340180d205031b00620f80300d0700108620000d94060103801805201c10031170b03070107001014080c0500c5020341d002c1c04e244182c6445006401c00c56490414003c602602c08a54006600145105a9084641c81610810070249802c0c0e4805085400141000e08084100300400024400c2e95050302d2040f009980025640c460880c1000320032410782d0f905800030b1000348694100750b41c15100c041403100c80828240818540c4030700c81080d80e0440c10b009500c80d00a620350703c080b0701500303444034402c6c4d8080002c03454640790045907010340c3c09460f220720001480a005a84048030031005400c0d02c8094480030741d41c3e4440940c0d40c2e4024281c555901c2a9080e40c1030741503002d0b11040c0001c13600400e84618002c1180d9040740209200001101c100383d000e410600c5d05010707aa0114042e11030f030f58001401070784054010b040d40302c10017070b02c0307040207402c0e0350910080b6440303240b950b002c032502003201c2c0d100d896100020742000c00d400080159072050003400c544d02000c220105 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 725599568 1250 725598318 725598329
    0x302090405010b030f240a0605090403180b07030507150603060c02030c07211e060207080405030c1f030b1f0e100309080306091312020606040b240318070609 69
    0xa4824032800c02d00c2685901d0f02505d182040070311b2580d59901c1c0110603000e164015096007001a0607601c44001808104c000d94041c2c000840d00800c07490304855102e040c4001d4100705400c0b0b07082003032a03038000f405807040b81390080030412420100750b19280150440000345900c00d00a1040c0c45424000950b242c00804404510344901c0b140050250f07807180c2c000580e40c070440720900741d0700d49640310f551250885012207000003103100082008141244050031907148a409425511460882058a0002040d03000752103002d01c0301d010303081d00180d1400011070342c02c517040c08166002d20341e0001d40d04000744400c1180c0426403280c61412a41e10408039800314000300ea00150300c002c0500228201c81c503280303000b811514100081011440c06040485d880200c0c0d152102040055655004119030b00035500d8001d6400170303045c0959840c003401060980039090700d541c01c81c08c400114525181d0b49803a80d801c12417000001085a044400240300e0111070382100300d50a00c0d0380c40c5802400d02c2514400c4 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 725600818 1250 725599568 725599573
    0x16140a050105040b030a0203040201091e18020901090e0a09020904060212250311091e0325090b151801020111090d150e011406030709020301060203070803100302090405010b03 77
    0x49000e60007042910b007514884000d850841c1c0e06c5203902e5000798006001a410310044a02c0012600c88100e81d0801d847c1260b41d0800c91036240c4468146508020141141110b00610051032076980c07081c5d5410440b004d004d03803401151200c50300d00b4001d215091000c1c1d00480d144007000244110340d0024402c14004024078410390783d0711240c49509464014140c0e0302c1160569036186564400d41202d080310302440d4100b442d1503101c000041c0e009103101ca9120090320b10707582c00d482c107240501040b0350030308a255005940380441c03d059142030140780543c8440d6035a4038007102c2d264232044082881442c0b8800456503e01c4042c1500c008844421480d034015820881d844461281c2201610b4014401910403c2d41c019180c0c0e4180031290342c1950145007d0303607844030701d004043c02d0151140a4800070003013141c03400e1407014142013400d2070b0013441185004000400c004c83c2d00008496a441e0495803050f12500c6019003055566102e50011354810064010300040c00419400900030a000305e08 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 725602068 1250 725600818 725600839
    0x318141207030b0c0a03020d0c020c15090a06030e0102070812040618020603073c0806060c03090d051c120b0a060f210c08040312110306121614 63
    0x14419a10107841c04000e003c84035040116140c5001c4ca000340ca00351409042c0541003684904c12001152510b040100050f4400c1103000310509003c0800c1c46071070f00c13442d4914580315540003c10480304551013094200340da1041914098003003903040c1ca0300540e202030402d540c0c410301100e00d4034007001558141c0700c280c50701e01c11416a00312042662100f03640605158195603d0103401d564138008038001c051400c0342caa12840504d0504290340341080c00040d00f07201c80c0202d501004050000007000700e40107044c2088901001003000003030303520465044420103209519450100c0c00c02c4600200c644030210035041c0d4200301e0303400c0035a0610f070003800e400400200c0481f074208140202c441c0318010100b040781110316141445003001e9494034944210b00d4807002008100c40d412030315440e40440000c0c6900f400d010030180e10184400702811a501d003403100907030080014102d4407020703003c10302c90b40e9070590140c43c040040c0020030a043c40442c40010ba140d641d0450000080f040107078a1140d1640070 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 725603318 1250 725602068 725602099
    0x813060504030c0e04020f04050f0714070519020a0f03060c0e01030209010801030303270606060809060106141b03120613020408150a09050f0d020601090b0d02010804031814 76
    0xa0714202d070341101c22802442e2803d8a42000c910b0041d00aa0300001d000f0324241c2c0c01e480320b028603800360401c11030701405884c008400400e090100303d07909200c04800c01251b0b0120704005812039418100030407146038108a0710020b141d82c10a41c0c400c10625500420001c00d10000764070049003075903071380c40341d8510741503c0004404a01c101c04d0700c0c6010070140001440440e12136401114507050320482c59401890400c03103021404400c0d40c00303d545540b150700034017015500c51051604202100020046541410341c054140a035007101a420514046040043c1051005610228500f030b031050b41d030f4907a4912822440150200c0303100d03014100620051615000300e1003190121941e2101920708040f9900d1485268a00948601d003910f403a240890302041c810300284030300d6100c1000500e510b541d1a040641040c01c141d014042803071030901c10940030b855980c4e90001c500c1d42440c1c0703000940da5074036040d02c0912440300764121a81950f40c0204022400ca58000a0580200c8100700e80c07403580d8 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 725604568 1250 725603318 725603327
    0x20a030501060809060412030e0709021c0b150708070b0403171b090d080c06012907030912021801120212030301140d0312020d0605120c01050f09040b030703081306 72
    0x142d0701079007160310210000c0c010074000307c01d00540ca42d061401140170300c0340c4d08865151206942101c422035900291600c50305268840c0e080e00c00e0702d115070921071b1401010001d100e807401024100c0903503000040900400c00c00c00107d40200354403107503881081c249130500070204c0700a0300d2280341d003405180118180c0d10602100d003030407196071120b07641760504203014001448891001100d0044041c458045038000c02e10404e8041d08080d250b050f6544141100d2458070210a03800d051040c02c204022408242d210700d03608256080812550070202c0075201281980c0300400003401c400005000204e403414096400d050300b28000c039002280440101d400d40c1e142e100070b11031050104400c4482c060b46003051010342201e68081d0400520503005000800241c0e40401c45090031981c0d10101400107240c55500c10241001400007414001202c5d00068110301c82d0504c040c00d00350010503841c003195140d0f003003e110000040d041d00d42813952031500360b410742c003c507140000402c5503810101c6c0d181e201c0c = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 725605818 1250 725604568 725604571
    0x708090304141302070b07020d0c0803220b0c190e031e1c0c0311030c100f0b0303070501020a080f090703122d080903040f05120109050d03020a0305010608 68
    0x9400910715280c584650100c940d80380151064100540142c0025440c8162001d030000c82d01a00b031301d024030b1400c00c1c0d0007030521900014100620205810740000700b9004400d407644203000030031141c1c4003054103038400c0656503102c40c02880010140100705805901364003070148045205190900f8461030701f0305440c070b2507060001c650176602c568800b4404144800000140070064000e03910b162607400c2803c90100304050b10b04000c20075081500041680c01980110303084003d05c0070754103101105c090f1a4465034050780907008903454200d10007400d070b02513000301142000241180d039100942c1c5040c601075000364614a0100c3e03445000191b55844004106104401c514041d140040c11540c0ea80007140008145204010704402600500c0c0c803102c020710b080d06400c0e8141524030601c0c5000030b00c00c2400614120b0b83c0c0d0010300040120240c250840c005640f41200c182e0600103039524458018001144040c1c1540b00e05220a030007660143d008000d82943c669080c000c0f80e880c1e02068640840 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 725607068 1250 725605818 725605831
    0x15020f0d0504060914070f1212030902030c180a0e01050105030d080a06150503040c172d07060503091b010f0e030a2f040603030905090a02070b100503060708 69
    0x300000034514000e58480307a03001c0e20600000840c8040c4d40c50320141c401d400c82c006001d550010500740500c03819000781c2d0005246000c17840030346d0b406a80d5101c6c0c01e0500c08400c101450380fa1000001117550500c400b00e110040642114101c13541d40303030741d00322135001942c40465044c0391000001c42c1d01030600929050b03e001a00820008080f00800c0f50200c03001800800d199071307583e4001c500300303100031000074140802e43e84d600d840303003094148030b8000c00c00b5074401e848014081017410900d0b20301040403510402c600f440555824248514035040028039044892140184c0c0400308045822401441c003801d50b400488442200003400c104080030b180c0940c5000c150762340c0c81d042c501440f89041d91500c01c006002d4960140066031500c070482458400802d544000850310fa0141c0c4410000c4401c80004507020310807286182c4028202c0c0301c0c07034020240101c40c41000101e554146804481c8010b03448030701030100745810904002c007076180b80140e500c42c1c022003010515192048950a00504 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 725608318 1250 725607068 725607097
    0x213080102041d0c090301090606030b0a0504200103060b03090708070806060303072d140f06042111061905090a17030703060503010e03030a060803030f04060b0f04020a020a1502 78
    0x100f118440f1110090080140401a030100441280c0e502c081c007840c0010785c482d041c04a5032905600d00f025040000401045e01c05141004100c040b8002020014800721060f082184000c1030300300403405401e40c2e4015104800e03000042c4480c420f0002500001c581c0300b0001e0329600d03a1a5402103460b2039007038400d1a070661060003660041844005046aa070410984640c4100c84c10302c01d00c2c6840030700f00350a458400b145241c00300055002e00141400c810780308050b2496142c075585030b9000102e00941c1e820280031040d0815202400340c4a614100b000c5036084032410b10306040e0b00d0141d2140c0342e8840620302c1c140000310b4005440000c2400800d5400000100c3c0650070152114040e0002000e40b010161100b0340081c15450030300c120921560300a01031962450000803001c1940c05640c040d05881e40100704010000e00201c1a8541183d40308201060035281c020010314601001090036a10510018030640701c00d40006514800c28407031101ca51140844a850350103c0c0141e000d80c100c0c41 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 725609568 1250 725608318 725608349
    0xb0120071a031b1c0e0105011703042403091a0403140c0a060b0103181b06080c0a030203091204120b0109050903090f0402040b0c160509040f1103070810021308010204 73
    0x40c00680c1c060b00b00d0071005000701081e82140b04444083c1e4401102045d001d035940c00041c003407400298403d110742c0000c113005500d083c0c80c001d480d02078200001c100314051800c00030312402240c440c0c0c100403c0c05400030390b5540c06501c40401e0110071001501d003140811104880185020041c0043c0c03900020200040c0064848984400001d0b2044900031810550348442e0080250280b10f00890785c140a800c0002400000800e00074807005660051401e0280200c1048200804402203032042c4145141c0580c0f01e840d02c800e094a0041c14100403003507003401050101d07500c2c07010a82c070942c45004643e40b8009903a68002ea0046600c2a82c400801e86c20420008500c1c0c103028202ca00c0e5508042c1005140507038030100168142c214414001031034101880321591469001d8094000e840202c5903050103040c5552001201202e4201c0108a40c20704c2084c4040c40d642400b2080c002d0005000303403648040030261080003580303c001045903010b030b107610208401c0307014400d0b101941c600102c14a5507 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 725610818 1250 725609568 725609611
    0x201151202100216140f0402090d080f040b07030521010b040510120e03190207050609041a0d0302210423031c0503190b130b0120071a03 60
    0x2d298400d844415403207080c10303902e850b10301014520020700c2290a42c114134011503040000c074070120420544540e0041c880300817183d5480c02ca2003c603da2008595681d0401e080d2081c0c0c0341e005982c490706510318003142182c10b03d0b402034010460340303c0201500809007a6049030050b080b00a0050401e440c1c800d0106000038144109144581541810514005050448410140ca210040200c000e800210b000120810b6510002080b0111400a01800b03410080410024002d01580600c2030342c0303503440014049030f89076000402e0080070704070f4846070940d402e000c1d590b1000c080c00b00ba440d00e423a2142144900c0440181c45c2510b50016803000010580c885a0b54034070346c1d04107841e505006400120504180720b03150701402e440c1070340704c0380c2d141e00d001c003024460124840303540c2c1d00090404081c02076a03960b060700c002d40c460107030a00041c02d070321003001204d060319899094400f0f04045103500030880e078002101d108450410112200030030a01e100500c19001c140d40a9820546d0a14003100 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 725612068 1250 725610818 725610829
    0x1b021b03010e1c020601082a04020409020d050907080a0b0a020d0b2805011e11011e05060a0801020909010e150603071829091c030f0201151202 63
    0x182100000c002180812840d0511810a00d2009000002d24500781c4101003090301486000e00614200c030140841d404c030300800707040e40112031140100c0b0300484410318140e5030b115415a4081e0907014411911110155078010040c502034440520502c10407900184a280c000b501005507603200c2015586501c8284040019400006421030850b4903004080e0340c07a1180f0ba11441002c564005415082045101c0d8014400003604464100844481416020312186401c600d40c0385681c9019504240c41c59502c50041c0f01d0340040c2d4141c41c01c5801e00c81003403021504001e0280c2c600310341110071a69500c003403500300c0c4036051410750080300d10301c01001030703501503c0c580740d00803102170002c071003d5085400110f0551003110311001140c08805860f410301d217030741045d901400c0c0742401981c43c144500c404081c0040796034010409135070000788000d0380307480305217032040000b42c2000201038125080c58094010303001e60034203c0042d0b1900400e010100c42070101c0310100c8098103407610000000d50248003 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 725613318 1250 725612068 725612113
    0x6041b120219090507081005040c050324030d0201020a1404030b06100207080111030702060708010b040b0f040803070506010501140909010e0c1201030c050a0501020109050d180e04060c031b02 84
    0x202003616500e002801c60b0580c02118455500386c0e1342d01c10945010070510400d03081c19003025014174600002d54442031b8001c41204c2c0c210640300300d044009181c2e0b000c880700d914015840113403d80640c00c00c11010319015000b900d5101125200d4004041914401480a0050344405403801d400e48000c034400341050202454450201d105441045480f101002c1c25219600c0414810f12000002c0080c0e85030305105041c1c000005191107042c0c0c0d490080c0d9101c02d0302440c0166044034000184000c181c15541c0200c0c0c1c014815001626140d08142c148151103550901c6650b010855661b9103021800c1c7c0c002c22148000070003414040c2ea6424100000450701004003450b030b540d0310811048142d1261504028000c42c031424446242c0b80c14601840700c2c80c0d113943c0c00b03141568104009440052400f00340049203411328a0034001c03044000e1004004180d6070383c0321200030003441e800c0c0028040c00360440c80e10351034640c4040c40055010f41752458051004c21f480d6006030014188851800312201000 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 725614568 1250 725613318 725613349
    0x60a090c05120c03240904020907170a09060e061b07080412110a0b070302070302092a180109060c0201031a0406060201050103051e0a0305030915070206041b1202 71
    0x3075051a2003660140c4000300291600426050040104041e220032004403428900052104440c07098019001c5800048040c2c00244a400910009946248120301d46058250342d181002058240050740d900106081c007403c0c0c03015411b04401e0842030b0380003d0321600511409404443d24041c9501c500081e4001d061704403200c150400000800e1056034140307050190003140881c4002c0d0080c800c01060144560200182c000140515000709402041d014216601a1503160141d900d040410412442d449040220310021448510720b0386802006051450061001400c9100d4514015070744085240320b070400003088105c101c3c005511a03000b400c0c0c07614808050210404000000405036500380d001117005079511001081031000805c61156068080116480782c1143c0421301c0303844034075064028040c001c0020104400d0b00c1d08014034031401d0900318010290303003080400291148000d0368251f43c64441c030048c94100524031403003401154840070442089144603402c0c056084540e2105 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 725615818 1250 725614568 725614577
    0x307030f06170d030c21020903030d150905060d0b0703180618060f0605150c03070203060a0615020d080714040b0c0c1201020a050315042306130203060a090c 69
    0x4648040c0c403404810b50b02000c0190403440d4611038010226000710030f48504110702501c460150b80f800178110b5a26030b1424802695800003079020a2035803042240b0070800520b0001c0c01802603c900c2000c0c020b540d4031444c180401e03154442004413403d4400c801030044e00f46880400d0307074640280d0000c11180604006245920f00c141c82c0c120803070b40c2c101c1514021028060b020400c101082c0314801000c0580b18040203c01d0900740400c40d80340401c2a04002074a0001d6130000342c2c0f0b030800c02c0d00c1c60181c0c010111840c9281c08840b01c0e014104074420040c9202c001c0614501d05400403610280f60b042d0307039403203468950743c40c0c01c101e403840c94100c050700031504100300101c1c45046c280028880b40801e10000d160340046081800030f40c030046403404005034070501030119015800802c4940024101041c0403040c14840300150062116441c0e88140c41502e40000c0d000c420b900c20414820360044462140e0346840844420a03071004556240c0d01015070503052003006c1c0d4941c8054204003a9142 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 725617068 1250 725615818 725615831
    0xb2106011b140705011103041a0f0c070e0121020f010e0406080304051203191d040c080a0f060f03120c050304060203071b060206070311090402180f12030307030f 71
    0x9501110340074980c002d44404642100904603001c080101800030700080c038150315050080352a040e22030145000340c1020203600c1070001d004211000558050502c1d0020051746d07242d200032000d40d5a18248108555142ea00000080c400755194102415041c0e442111a80c1d002a40c20000181c0750645840c1c1444900111140652664840d2102074061400215521404c1100f0820304588801c40322209078000c110b120100d0410302d41c1444001e91500702000b0000c00040c01c070320130701c3d148440707180c101380b901490f10b1043e9071041c00c0c2130180d200d00b00d0801c442e201c11342c0e280c0159242e0340074610401165041c20000500000c01d1001c118102d86800071141e0101d43d0b42e542164496408003005a10114400c03041c418a00c840b2101407400b5804c80303002d14a000d00180d219180145000c060540e41c070030b0800b40c0b01049088980a402c010811940e44e600041c11504502905182c00d01440042c1601241403c0503001151000e00100086017140d80c0c6180441c041c0058103442843d103500c401 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 725618318 1250 725617068 725617097
    0x4080d050a1e05010816082533050301080c0f03100501120b01091e0203070903021f20030412030504051809061005090601261f0b210601 60
    0x55000ca51012442c0000c6025403502c410f4520b40740b111420000d00c024021010010f89a00040301c240140010365014400c141140007041c22a446900c14043c05d1004090741090b1074841c426491101000000100440c190384070403581070100f4060103070b0707541c00003480310000d29083d02d141203181c80080072200380c0704862a0541c1540c000b03a0104d90f2003640804030380200505005554050a0405020040b2150468010b0b445982400d07801d101198000007207034071188101c1c4c541000d1500039111149408080943c1105509d4400b50040042e03030207080c140c480c0c0483e072403003200c1140e0a0000d43c2071030305200b030903e4050f03041d000480c24000100800900d644400800d24140751040002c3e0815141c00c0c02203904010004103880503403603402200b4041541d844c1b407001c0e003204003031034942d1440940312031084e11211642c0100a407080c0300307020010007846404034051020a20101340c030010341d842c82080c03024054030308000701c1c0281440301b06015125075404240d02c07020503d0041340844214 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 725619568 1250 725618318 725618351
    0x50705031b030712020109080a0e060705011407030b010504050a2c0c180d050d14070b0a0912050403052a10030b0108090c06030a020f2b06050904080d050a 68
    0x100001c0701d41001c03803044184401d04210380b8580220b40000d014017529540c0c0c2503010b10407813041e481409540704842e10162964010703150303c00c0c1d02400801260301c030403103800c0c12010100c6060700000c0c1405d02461070f43d403041c0e007a1011a100500468030f070b6410442c2c0c155861700d031188641a40c1c5200344080c0080c1d00301c210410b00881d1140740341541d0340c8070400e6902e04001410b81c41801340c100b0420090010b000041c030304811800a142599401d000d80c0952030051284400140100783c0101c20f01c9101d040302e911244a0710300c20050042e10415800090b0781c1c601030781c48054080c0e0860144400c0c032404107616482c0c1440541351941e020b0a40348009001c0c5070600340394400180c0d60707296009480d40c000410b03981127804100240452083d10002481510008040418a613000f2a0202500e00c01c08280c4150b4240c840d91034141250250341682026206018030500b0341c14034800046a081c030321031303d80c0144d0f0446101ca00c0d000305042590f000d04800381c0481040c0b80d88044440191071036 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 725620818 1250 725619568 725619607
    0x6060f07030e0a0515030402040f0e0708070e060a0f09090203030409050c0304150501051c0c0f06020d1d01051813110c12090603040b130215040602160302010f05070503 74
    0x2d40780c0103140c154a00601680c0001500b00601590b41e003005204015145c1c420350340d200e0360403100440c1c03054a04614001030810207031007440c1c3e8030841d207000ca071801000c00c0e140155440b40c0c100d441181e50320010001411268440c00d50a604021001d00203c4000c0d0444441c260001d81101d14141c0e980701c50b20200e40040302c429801745000320911040018290004003100c02040c02030203c4d50406000030f0380e1458988494880c00542900b00b010000140c2c900c1c5c0042000304c0701818042e0351031001070740b560044004200024081c44506150381c078030424001105c40b060317580c81d0401180300c001091043c07141240039400519008107000312241e0b40a000c010344180042c40780c4441d50030340d07403501c1c00d03a074001c50004442041c44503120545030070050341e03881508074026541a86400702e04841c1300f520703002d010f5000b50400e40c40016864424004104031607460342180c40762400315003d500f06d0f0343c40d400000d0014805a0000e0a000e1042019101090050041c0c038a0482d0749480c03100601007 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 725622068 1250 725620818 725620823
    0x17130206030420031b130603020a0f031406150f1206010807060e0105030417160f050d0e0f0d0803101215140106080a021c0c0305010306051b0f0306060f07 68
    0x103e2061584070781c52500e15040c6915416002440824045000c4070303c1010108030369805001e46060001c800085c54200b00c2c021a00136240d0413810b91910618418014103000c00d0700d05607088011024003040000700103200301240d040c0040f41064000c20000300341c0390900340a50200703689014208220092010b94000c2204100030003640340750110180075141001201410b0107410300810000c14034140b0061194140c0340d28080d5a02400365151a085d01c808602821840201032403a0801200062950050002d41c541c2d0740c844840380104510804003000b0182c12a01a0000c040021030081c040d50300402c90007003500000f511800c65402c002140e10050301d030307030742800d01d01804950688240040c055070510f41c582e841d03042c0340018240754005842090455070020b80303040300320900c5c4078903984021107203070900511560b9240100600307000e010a07901d644c94540800c00900b0180d644072141041084650309003250001c54038100d410040034140c01c21010400105100d00c4031005101e03592 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 725623318 1250 725622068 725622083
    0x607051005070f0903031713050a0305030105130209031f020d150f0807080601120510290306070c02010c05070b1306080a06030f0206030406060f0b09090a0c171302060304 75
    0x182000004055030110543e5100307100c2c602d00e01380b0210360b0040b042104c0c201104000e6241740c03148001056a08601c0f000a8428002c4d08031180c10590b12400540c120340044900710800d02210000000324400c0c06565039269010f4903085807182c40a0b000c005205c18a07000041c00c00086000c003109581d42c44411341d20032121740c202441840342008081d000b41c5030380c07030041507e28101030505540304410f01070003141840e94071028080142c108280030450720b401e0024401408070ba4101e0b205141335041041c81d001e6644a000d01c00e040020f801449505e00d42c0c0c401c51411240e07001501c2c150060201941c05020702c00e4003058070350b5420028101d030100d00021880709031030110010120751002d094412100d04000c000c10100da520350300301e00300e980c0484041e0351742e480f5480c2500041c0f003258803402000c03c0020000581b80703410405030030909002d5440c00500d5032542d80510440301c44001050100d10f2144000b4445844070088580c0b00c2c100304960043d411058000520940003241c0460b140b2 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 725624568 1250 725623318 725623321
    0x30f01060602060a0504050a240f020901111225050d0c26031b191e0c081e0f0f040f0618063203040b061504090b0607051005 55
    0x41d904103c81580710041510030090340c01d041c0e4400e9112083c80801600301c45000e00c06644100c000309240821103140d01041020341c2550f0007e05c00f0307410041416001c00c41910305880301c41070201707441c619080810003c502d80088003000c400e10703e400c0004c04000c501a4202c5c4e03030014a04101030040c0c5d241544801c90700350f0240c0342815551723040602c2e20014840403510001010701403019a41c005088410b111244962012131500390301903208030100711020090048034951f000000185480c0e003494002115007072008003034035004400322000340401000c0104030081011074500e0040c905400c00c1640c80e01819080d00103145c0c110001855070014001802c00514030518400030050941e414081c0780c0012070001300b081101540704903014040407401140c01c0b072070305503800310b40740302c60b142c00c00d10305600d00500641a82080701c0848005108402084040ca440c0741c0d030004540340ea000b628034103424070064201801c41120b074150031400910410000600c18000c0aa015203a2035000a95 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 725625818 1250 725624568 725624579
    0x10801020d0b06043506040c05031c0c110102071e1e03081b16060201020711060c07150e0904050606090619030f0c0803040e0703060923060d02030f0106 67
    0x803a0b0108000a1040004020030410303950b0300d004a4603044040405c1941005036058001940c0480104540d07040c041d0340100000c00c4440103a020985805030f08403522481880301c0d0703441440a0040d0300000c40d041d026401c0016250341c22281c14084184140c444d41c1e039490141c43c1d1486003101350544041c114001c1444400b402c0104d0fa40c000e410804081121407568130741140500c81c4604424036400380804070f0804480802441069060503000c1c481002d40c2c50b04021700075001003001311002d09111400c3c440c945010402d80c4c0e014032a4102900030070b49003071010300650056041d910180502c0b000030f008556a202c82c0140b195000740c014002c18030b413000030000856801011188103500098400c2c440c91141c58158007520391210040240300400e0801400d4055542c0c80740d00f03144000100420440c2c5a441c00501607440c1e43c4090100545400000302501c02800b45150b004096410151100700320304480e6401c15406011042508030540100e401c00c00036180400301031f03445182c00c001 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 725627068 1250 725625818 725625821
    0xd052a130f26070e040b04020a081905160b03070f0311041202010f020d12020a1709010c1b15020a0513080f0c010c15200a020604140f06060126010801020d 68
    0x2440b880610141440c10f040203a04140f2140280c4050512080c81c5c00080440d00c51105502c040c02c07880d01160108541007416402400d4a0b13501115940941c511a08510720030440b000d00b541d10034801d0307038119900e4820403200d42c0740f180e0030101010b48070b00501c076a02c030b03201c4000c0016042c00e40f07118829415a00016102d0814401100c0455210901c0c50b54019030144c014180070215030400340c2d03a83c0003800101c0da040c0350581290001b906500c1400802e40341544034403024441901d13808600d03000c01402d07400c84803500402030004104846490641180c0d98001d003a80312240c1406420001e10f03810f04903481c15540c001c010103502c0000054010402006600000c0c842468210324038080d99984540404050001050558480d00314190350105000b0703100d00c44182d03502c3c0c0c035200d02240400a584950941c0c0c00d8581944070315600b03421b403c000c03071032191448800000b070085403281e400466103454548002c03504da0300034401200001c004290750030700820b03c0000260302c810580040c1c00 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 725628318 1250 725627068 725627129
    0x91e09050708070207090b030a0b010f0305060609071d04111c0f110906090402040b0708042102030d230403050615220504060906050109020d052a130f 66
    0x10500c00b00d18200800180c0c000380e01001c0d00c00100001c0b40c00d62581c0e020038542424200d006010181203000400c4452980440008880c09241124040c1d20b8460070f00c10f50308c00076a0503400140c40210f0009221499403104500381c0d0010300f00103282140380c05070f10f408e40c10481c00c101c1c00c440001c1c03c0c8043c2440c0c5000714800311600d00010040c0c001800c00c0052030340b01e034525850180c1e5004c100c2500c0d60b5203a85c15074000b0502c0b41040e13650780a90345820703442903109008004011a22891010140e82d16280c1c610000754060300802a1601030039007640d429100740c0203200c11102c20b007103c102103441107000e80000d62107400148400c1c00d00010205501c0d0302c400e030850283c07011034015003c840d14241ca0100070110000c2c000703015103441c01c01c100502038070316014010a0520000241680c00c40c0c4c010078004505044c10031254851400002030340c0c1c400414449400800188081d00302207090003025200121000b080c0a207980c1c2000ca04000d080740c0c04115202070000a0320b0155000b1051503 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 725629568 1250 725628318 725628331
    0x31002120f061f031d0604051c17221220120715060803070308150f06040b0912160602060c130e09010207050a061e1b0f091e0905 57
    0xd1208001c01d8003d0000c03000d41002e00801c1648840101e110404100001000c0e09402011748110340703841e04145581d21440d20182941c0c03108080d40c070741740c02e01c5401e0782c12014400140e00203183d00c4401100c1c00030381501e0614002c0401d543d180e10000743c007820750b80c00c4a03802c2d0384400a0800c00c030a01900c407810305048044850300b201c0c5003a042c1f0380701e60040b03a00c02580700d01203c0118068241c00c000501181e0482800362100207a030b503040c035410060351807241d542c10641d031800c2001e52040c402004261011070303410a400303001c18070000c00d610000d000c44040181c0400240e1010b03d680740d203442000042c000d00c0c4140e0100500c0300a80c184220b0b6406a034040b0064a00200380d01c220070405840d00c111240d100124002c07a0f0550300030b4040360b8103240c110b82194201403e90134030740001d285511240d2130380c4103810990000003130f8902801e044401040c002d94a0340441d094281e40c000c0b200402401041001c0e0800b255440420750102c03401882181445115030403d0303075090444074083d010 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 725630818 1250 725629568 725629579
    0x110627041103040f290126010e280b0a0209150c03030a3b0105130b1f0b030103050d0e0d111504080f010e150103020d060b031002120f06 60
    0x3c103c08212500b418a000740e601030220000384200a602480343c50030600c3d28400d150340c0d500001000d81d10902c0c1d60744203240140c501c81c1d40d54041d90007107081740c00000000b042500301c0b06000c40110702e21501321108c1c1d0703841d003001c1c0f8840c0300c1035a40c102021021200e001d043e03540425144101c0c101007035440700500410740341500e054086a04507130383c0c1c040101901c00480c0c8504100c484003000358000001200300d0074403201008000400b9408a50305a000c0c0c00266180200040450f0060080009101e4000f204407013187c4030b88403d80d094000800a80a40b01b0b07240d40300050050701035000354000c50064000d44001848041d0052249005401c0750348104021a440c501055900180701c102600884a50a41070b2030390b480d01e002070141d68042141800b890800840107081900008203624403501501c15240d000d95000c4034030b030390a0001a402c021a00541c3c800544694482d10361484028100e401045410301ca0301c0903a40702c00b51031803070f078158170052042c0d401a60030780c2a0011021a00e = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 725632068 1250 725630818 725630821
    0x20c15041a03010e1801180605151903110a0503070b030f1e01061d0613030b090a0c0b0f120703140901050403050a03110705060106050301150f0c110627041103 70
    0x700b40540313450140c20032500901d481c01c00082c20f00c0940c03015900b250009102c160b698094181030f00103220807a8030f1541402e03092101c00c039502e01500c003d20b13407041c1c1c0c20745980c02038196200e2070520243c1b0b44610350445c2c04648040740c40e5a00700004c03001400c10300d031103031707543d04d80380200705603201014102c045002180035105080241603040301c2c0c1510014030b028550030f100e4141c0100840701c1c0c001042d03001a40080c41c41c41c68215004035405880c06159058555107980c00c02c1940d880a00b08040c00d0144404810f10600540a00030849001c4c003412241c14455504a40080b1751002e0b03401d5004a50703034600321480e41c1e000c9401c1581c0040303000f0003005a8905501c2c0a4441d00c0348114210803d680c6170780300060507080c5400e0790312003500f02e4100c03042580c45820203880d984c400e0080300f0311000f5a641400c1c51a10134000105c0700c0c4080d5507007200c5e080c2c0c1c0c0d6031005c01ea0a101c00c23056602c9001802042070141c210801c10a6400c0b052401d030403803404200900041303400b403030480700f039001e000c10 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 725633318 1250 725632068 725632079
    0x1d030a02031803010b1801090c050c0307030806030703050d030b0f060a090e1003050321090a0c05090414030d0b330903070b1209010516020a12020c15041a0301 70
    0x400e82d640d031003000032642203919920000038014240c21985e103602400c0144280010b4425550740c4c2c1c1600d40340c280410a540d02c540f8255101e0081d8645554250300412807000081d101e01c0c0d1381500281c025040b40c10441e1039a99050610f00b0b0720000d000029515108217080d0301d000d0302003444c03400089da4030031b10301190448003c0002810f40140301060b8580004101e00c400da0803c0140195088400d99441d0b601481d40303241d100140300703551004491030300003180da2071101094410015038050426281c2e10715040601c07c0d9000010320590b031000c0c040b81c00f000030040c240300802c0e030340c4034100000520203915400c00a42203110411011601c101c100c1a100c0c00182c007006a45050070025a507442c0d03816400041d2a10009800003002224045160b0b0001da200a00c014000c0c50004000d20940e91041400f100c02c420400318030300103a000ca00008040b888500342c0d1200d10100d441940c22240c10070000c215024240006011060300c0090100030100c0c4504180f0f900181281d2040e15552602 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 725634568 1250 725633318 725633323
    0x9010f0e0f1807090f0f0209060a0e030a060c0206070908010c3204080d0e030312070513050319060e0303161b0209040c0e071106160903151d030a02 65
    0x6201c807100091400208480d0415011800b85580c0e100e4100c584454030b03210350902a18011000711206424943d581c0b58007082e81c000d60b900b440010300903604100280108480c030342d42810055030940203003107212000c180306000300480302400d50020122424907000080c80e4402c55401000f081c0d00d02a0441c00550784200300c20601000580c80c46204400202001449144080350001040c800500018804000300e014981d02c2e055840d12001c4000920605450f44078400655400b21642c0b40041c480c01d025402500c1d2200030b241c480c0c3e00300340d00c1d0800302c1e2030908640040d80c403149103880840d08102040c020f03000e44d100500061400d60410384005100381c0028140c2c131061104001d03c0044e05500060b0868043d81c0040c00220030342840d09020008580600075005c0a1039800006405d150068a41c002c0e01000c0e031004140c030750ba445a226240d0745044503100c04001e030051001000c2800044034509a458900e4009070341400030343c01c0740c12414580d1400700560000c0c007000c1040c0d40c01 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 725635818 1250 725634568 725634571
    0x7020a020102072304020a0806150a050a050703051309050a0b0402040e060628050702130c0c0b090703080c010e0606100504030204020d020d020c0c10030b0d0f081905070209010f0e 79
    0x1000c4c4a44014528003280c06140058502d0583c00610100d4007081c40c0b03601860031402440b09450300d5000c4105490300300d00a1054581c03403000300d40c00300100c1c2c191a01c034100600815002c3e00d4154108203440d40d00c10744021160f4000714031941c9510500144606604c41e00c1250081190704600c5d0a10b04146000c1000000b1f103018407410340450b41c030030444003d03100303885100b625401c1c80410990840c0054581d421409081e0302035403400c0d10680d42d48080740310310084421a41c9600135400d9580d514000580401844c0040b81d015400d40040060f08040140080000050001c81c0c40168000c0452810b10000e0030785105001121885801c6904081210192034055801503a5191a90b0742407003c0c0c400e05c40d8000e1224400120056140b0300402d000460b20b008840412081030b00e406c2c07c4040d1201000c0243e40105c0c1c01c511800000c2c2e4480317450091a10600056040c940c210403452a044a45403d04000c100c00190312030840c0b8010283c9405031000c0c00c0350411032400d0052039200043d0 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 725637068 1250 725635818 725635829
    0x10f0606050c1b0d05100504050618060a0b041d0601090b0f06030c090604032109090209030709090c0806040f05060a110a05070f0210110111030c07120315030b0103050607020a02010207 81
    0x119107142c55134440d11340324004190170404444250026078002c500405049806480b14014000030502191801e442d25000406100040c800e0342c44080419005003482c900e50351344655181021004c0c0c001d000c0382c13000504d039050041c0905600d0240c40106469808035418031420242c02d0f58801f0340d8405060343d42040c801c560f5191580081d01c0850700c82c3c881c40e00050000001301802c07083c1c004001507c0c03021316207a561410411583c0350440e000b6405200b068980c0750b0002441840200003c0c1e004410300d50040c441003608070703505c1420034140ba50540741914000040913100c0184802040700c1500311175812820017461803040750b40c450310b001d1802c00c5c0c41000000a00c0c2414045940207584156030014991040d004e41c40901a2450401b008208015401e20061601c1c0c2d40324002540d03c10300d011100c4a01e0001c0c41d43e102c0a5400b0b01d10914000e26940e000201c0c1d06091003c11440650301c04e00b4000b8981d41503060840c946a0010040021580242d860b500181d0340450780f071040700c8 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 725638318 1250 725637068 725637103
    0x103030c030306080304140f010305010303020c101202130602160e0127060b090f19030b0c0c0f0c040f09020117090102091c0b010b03090a0b10080f010f0606050c 71
    0x8006141c100e002d0071856100c20300034030020801080407400001c560740d082d0700c101c806200c00c180d00d40055040d5007003444007801681100c050100d01e41800900e20b415017000d441c0070002c0000222819040ba000030a829070350070813486050001d04d4041202040c1c8114000c00300c1001890901c444e6600403050113454506840700b42c01401912890561b00b0300c60568940605c0400c3e02c0350130414468000881942c8503507003c201c425000d040403125140c809100c0080b080b0350030700316202e203c8505400791030010b00d54400c11858240500c2884011040c1190307030050300c41110000702b048245c070340c5010a40080303481d02c4a101d005030380041c82c9003090000194404015542c0c8103a1600a003da114015008001040c0000d50320080c81ca0034003040c0d2140c02d0220190342c0b204400d103054001105c050309030340d00104c400000300d42d00082c465400b083c401d016000e59034450446504042c00e4056403601a91696035075080b408050141a016000c1440c1942c109074500c1040c2c2c0d5070b890310f561581c0411 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 725639568 1250 725638318 725638337
    0x7060908030412030e22060b0901080a0b010c0c030302032205010c02010e04020405040906060f06020d0f0c0507050d08070b09160504090f060501080604030908010209010c021002150a32010303 84
    0x50b010b9003c00182660003000c0707000b50006c0e1708003990101440110f80903410328161001c60380100b5041901c1c3c0d01030307041c2e640122560b0313043c110400902901c0714142c140401d44420000080100b6580c80140d48240e006d981c849444012001060008200100701d901c0b44102c11710959074000c1507004410340918044100c6542c280119000f44107540107290014141036a42e014041c0941248084442d00f03d0401c0c01681d888034200c0c0c0790f800910744000040d6000c40008080c92048450b91440b50180060706c4a503503803800080e60031045004100c49a900c0400c001080c050528649a407000702e031400b500d81d08104401b40070070401c05000d80c601c1a9910007d403018020000081028a5030004c42040107503180c02c0c0150751514200c40444c000703445900040340409060090316440101070f103e4821b120780c0c60f801c011700e20b1022021402180b241f080c0d0400c05060380112349010b423030b400e000000c11210281d00352040b1891203411504040c1e0001d80c00703980950221801781140d8140c5002541c1 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 725640818 1250 725639568 725639573
    0x4051e01090801020414010e09040201051b01060f15080603011509111603090503060916151101050703020903010e030f191107060806040b1206040809060f03011707060908030412 78
    0x1c00d5103075003016499600c04a000328034200c40c4a080ca00065090300e03448001c0c0300800c2080078202044030002d0001d0018410382032005035180202203222014400410030688030141d41010001c298403031200134420a990700e00140d042145ca50700100281e0083c04018500a041c11107030b9880d100e213410b0a9030380e440c0f04040e410711800740c41d1a1030900f602001f441c0707418180140080d2650165034401c0c0154404581d0405000440359805844100d1901d14649001d000c0700320003580c10301840c103000081540845001d000e1107450b1091695890051305e40d0b00d00e10500d402c4949214608856500400100030000c0c6070105459054040034401c00b40d98601e004221038051204a00408038442e9030030224065400c010388911034001a00e0400c20301403141c04016520700c00b24004060343d00503001040108841c1001494004405824946032090102045009a0003680650381d60038517004884c84404003440741c04002c0195103001c50034142810a15a141d00c990b00c9004090040c4040c102c04 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 725642068 1250 725640818 725640827
    0x8011416050d050f06030f1c050a050702330711061602030303040c18062103181e05010c05100b0d1401050601110319080a060506210a0204051e01 64
    0x4440c014031400340443d00301300b844600c0d1890203581840c070171b006202503001109000a030308407903007928a940d2910b20480000903030700c0394030007441c600c00c10004106582c0541c0700c0010341c503020546e000e890781c404001c0c6040b40745000c44000f0030200d105800c004040128003905014510210112101e580c0c030100b03494500c0809028150013074042c00b011080005005281019004603118030b0903011822290707802d804112102d07405445036100c421007010100e01c0325100304155051190406c480740001c03110207a038090b00940d1145405007032200e062041c600403000b1010082900f8200700f83c010345035955580c4c40b00949801204100d64504a030140c03996002c21903034095030061043d0524985c075051190280030100d8245020803213403c9000c80915000048400200851544600054440300c007201e00b010081c00d142c0416465078000700d1a41d5404005285550746d50f01c8402c010345585035200015030009103082c0c3d40501c140000c110355100c11440250304052602201401501c20f001a0cc = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 725643318 1250 725642068 725642077
    0x40c0906050d0f1d0601091e09150e0a021c03080f091504030e010e031c0f020f0d02010615030501080d0311120103050105061201050c040e060a0308031504060801141605 74
    0x310100d060024040e1030400788422a8000c4d0701e2001615031a070789a000007000e861528001090100505420f00e0b80203031254482c8001c0c901c42c100c1a08945d0100e20b003c81640e101c0ca513503080d1500152014801c61600310881411507007010841c2a0380f90720381c0c0340a04040c2c4c004141d101e8a120f1000050502e0303005020104488885044200340c1d814682001420fa983c4002003e000c6940c00200d00032914001820006401d513403071081d41d00c400010801c651140b500f80d01c82e0207600c130380301103030b218142e003441002c0400c03010340d00000380149009040300742008101d000c0014986400014047c944001ca202d2905165504000c5000004e81301ca4000c68428006000969450f001c000310800a040d004103006200803901c8068171000315051900b2910103840200354245c0c104410050f000c441c0f201c15a000c0c100030402d009a81da69110a1083c0e030040b074015035181d65070f00c4014181e242c20300c01c410140032100d00800015403117540c030481c401d401802130100a85810180e00311248144100d4 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 725644568 1250 725643318 725643341
    0x2070302190803220f020105131809120807020703030c11090a141803220506070303020309280b0615130315140711010225030e040c0906050d 62
    0x20704240050382080e02c03103608203883c0c41038841d001d50141800308210803500000c03542c0141080d480b4501581c01999142e1003030700d101906c00c0107141d000035182021550f182c80b030391045d00c01054030041d40ca0f10341d400e058244540000e1110070001d001c00c0aa0006001d415281c0c1030a042074022418101010b00200d01c608140c0d114600c9801c118105681e50800e01c400c5000080761100d945805803007003034181c0c1a811520036517005001e103d80e01400b00c3c0c0b954114250440c0d81e030905a440e8000300c0c5045d800003c2c15404a0b0300001408005003003080070301c140b200c1c40f8681c030100e0100c006420744952801a800340c11401b101c40400c0e007030b07907407a0b070710030191001c12035855542c5030350b0107260502c07165602c0203894106883c08002c00032059405400781981c8500c40c52021642c402d1801c8c3e0310900c410f00105807541d0f007402100c401d0300c2003140000311424841d101481020741c615004001d0007a03840b10502481c01c105603898244e4101c0f4448007a900d40341840c0e81c0360708030817140c04000e08204610 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 725645818 1250 725644568 725644603
    0x90e100b040605121506071b09050f070e090c030408031803040801202109010f0f2a05090d02010311070b19090309090c030f0e07050102011a03070902070302 69
    0x10340b0070f81020041440c0040020030680d16500d001484080d001201080340d0040010000407001540d04001810680c00c158a51110503440d101003a04071a01100c012641d0080700040c401c0f01c580100010541d035600312040c41c07051070040034103183d41c0005880204841c10200104200c0c22008544031015101c50b401c4a40b02c0780d40b040740d6070181070340c0365082e10070100c1d1080d007040d403822480855075000b020345801d4154100e000032110403600010036801c815507941020607010685409500324010f004d290210301402ca52407610400a80b502e2040b6501107000d130600038441d00171066401c010000c88146821341801e0006901406ea1075119010071140056890204058040c4103030050041c6480e02810035049407044040b65880c0e000580440c3c03408000b00807490f800d411015404c80300e441d0103c4c0100c0c138008002c003604c0c114401c40707280d03820441c01407010b0350f030902c210b070040300440c4601d5610707000d03d00110742c541c1228090081140e40014492042c18020404410500002d454 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 725647068 1250 725645818 725645827
    0x1204060f1d030625030911150f21220210051605010c0e0a1202060304060b130b040b0f0a050d02060c070f06030b181f0f0303050309011b090e100b 64
    0x70080303810881c0d0504690a90000000040b2491003407159000107580300c04101c51950800e000c00111061402607400035550800601400d038800c5405001101901c80c4286044e800300c140000c000d00e001003554039138001d20004d0403d443c040b05400e02140b6011b370313010803048908800032111031089800790b00c0202c144864020070060b055020303c80c107600329130300d8001c40e01290040000000d840c0c402c100030788001c40792001c05807070300d072008540092081d203002907203611502c0410900070140f07443c0c9000300e039075640b140e072941040c1c004e000d010002111000d41130104500010551ba4550040078040c0024041d00ca0854881904488481429404940e8600d07914128494a40c4081c020500020b0504d6840c21140c1403440c038040350040859900303503036030744c461000030f0b001c0d50f142c0441110401d5040b400035954201c21181c201950095803140d0b41c2c0d10708802c11170b094030208842c4910b91200300d03481c03c24407a80b0602034030668110000118060312561020502c001103500240080c107000103 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 725648318 1250 725647068 725647081
    0xb0307051e0d02060d021303050d0c0803010b13050429060408030f07080904091b050303130524040f030c080a0f140c090f0601030f110306040902120a060207051204060f1d0306 77
    0x140b4010448e4811400c603494000054000c071000b4107031000003095001c1c02c0c00144001c042e9130001e01620f40d918500900c1c4a5640c90000b400c4c1c4022203084680e001100c00140b401c4616404240c14080054a0083ca0503191140a6541e8441d602e80b400141a000c581c80341041100401c803540041d004009120190407800c10083c08015905031095125800000280d281008020707686002c0f10b00f660304102920340801c1c41041d01d5500750b109085508919103860b00b09030000a08041d0091030319140c000381c294504005040c1d881d4010200d941e104001100000d450000320b12051503218140400f18020840407500d001e4040a09560007030100c8200284e044045c5401480b82e10240e0302404420712484070300d403c8500f00384501180711310400c009031071414140c11480d41d0320300c040d00d05036845000c0300155050605400d0100e40e0f0310380019118040c01010003540c021401d400c550075140c03e107072040107440d20303002203040c3d814010b42c400705910780e80d220000103415880c09401e81d1058501403 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 725649568 1250 725648318 725648347
    0x10807090b0a0e1e100804020603060d0f02040c02250b0406050a1209060203070e1c030809070b0309030915042702040e040b06010f02010e030702060706060807090b0307051e0d02060d02 81
    0x2c42d040d4040c0140c404c1e085201c500c146d8910b4040e0350087c141e40c3c03541d10f0700ca003070240d9180c020a06031a1a200103e2440068032148100a441390b06a80902a402d40045d0791041700c041c0004c0754520140441c40034803409100c5001c50382190500c1c20025038501008000b540d48401a21801c2e40c114540020181030103c41c2c0c00940c41805103580d5201c0c000d034140100809044044004008030100b100f0050000e8080c40700150032910680c2103e55181d42c0b0210303200d480c0d00880f00d100454002180150707003070510301304c80d1030309080c1010700600707050600c0040f44148c0c18074540641c0e800d4481d602c0303440510580e412030b0082d0503260080d6405191a0404400b030388000d654180c002404841010b000c03a1041c82405e56138000f0740e000c1c510740103803502003058a40081d0b405590040e540c600000d08070300200112002840f15100201c0d1f241d40b40410141005107170b80c0820f0080c01481d007a00401ca080700307280903805804540701c0c11554001e0022400a001e51820308002c83d100145400441801 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 725650818 1250 725649568 725649619
    0x3040b09010306170607030b0418030e09061002030a0c06090c090213050f0f040b040e0613050607021506120a12200304030807080c0a0512030411010807090b0a0e 71
    0xc1c0c905006583c1e4403400c0302080300c0034000302135040e0080000b00745124440d800003100300030003c1004c5a03102e410b540009018009103401c401192095440c031465041c040e5609a00440032110103080d04124034003c1d440c0c0c81141900e07000c00070300c07000240c00c01ca02c0c0d500c40aa04d0b50030041d803c034044d071a98444002035220220343c0c0072102c0c0e03c0c400000c542c40d0000304e0300890390010f40032030342c2d80284000b0702019081c0f0804a56010351100c41e1080e80c40f9080041034400c2c408041c1c04948a102403c0079401c0100180448003150000500801c20142d000d0b10300c0d070041c0f0305590240040d6070380103d241c14100001002801400000d4410107140e6002d840340c01c1c5060100c40014068a130f01c00d269507a4400d6210040490700240600d4010840f0310300030300b41200710b10040e11080452036860a040642100040d2074060001c024001801084810f004105d0403e090400f82c900306164081c158050502ca0424082000140180c84034401c100c0d02901150103403404200300c17606103544102062 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 725652068 1250 725650818 725650837
    0x308131e12110a0302100903030b060a0f1706033a05030a06121713030b04120908010905060a020c0f060c0a0215150d0f0807050703050606063903040b 66
    0x41e4000e04002d9000400c00d4071800303516030002d04c16511015500405804200015020b0594585c1045503540b2540700402184c0f010380e481d80e800d01d10b02395000d0410b001d1801d0031060000100100051501c0000e0800201c80c07080c00c0c0fa10400700300004801c07400f000314240a0903c0d400054290301c10750020051405031210390024007105460340700d600c0d410800503002410341d0340752030f60000100c2102401494528200000031001c19200d454000484038107035021034850210418583d540c580c481410f0b80506400c1c8000c2c840290b60381c89a0395610b01c068045440c0f59800140f0005686003045240e22407021ba205488462a02d1500300380d0b1074018405802c05030142c611000039911020811600c02e0242801c130800505c0c0301810701860118a10080717a028640ca11201c0c0820410b02c0a46105403042c00280b07100350440c500523007400005000c1c40e0082d1401d0000c015000c0e140048040b031100840c00031100c0d40ca1405c140c14482c1030818450b01280400600850058074a0004010514 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 725653318 1250 725652068 725652077
    0x209041b110d02030a0503061905120d0e10020a02011d04090b06040c0f050f0d090803010e04021002011e05041e031e09061409030a06060b09040e0a0308131e12 70
    0x80250b841a0307200d1040050840008400b00300180251030804003008048180032014000720340c60300d000c104071420350380c01c40f01140e00c803070301070721203580e011540d080c1c00c600a4030f60009004005001039035510000100034180001c20085244142189540641884004005001070328041c00d1c4a1404030041d28918003d60800070003640c1e141c015039138005020381382e5030303064502422507130892500e42002a20410458641c81d04101040310000a503029201d40700b08000541028030420101d60407407600103055906040307114004031710030f1401c141c180800d1080851540c3d036600c6c1207400e944855100b500840b5148182200389a403080040400d400071100c8e915080414031020381c0d05001a1140e00001010100040314811690b009022000c2c401b4084a000442c15603400c020303104203401201c40c01e20b0106180703100f0700c0c15002e118100c001c440b01800e4a082651001403640c0e00084c000c09640b46900e4508041003003010100f030314881c4000308013850b4207407890700c8020800c200440c0000035 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 725654568 1250 725653318 725653333
    0xf0b0301020403050706050304030c082b1b140f03011203121a04020708161202010c05040f03170f12010e0105030d020d030b0d15092d02040209041b11 66
    0x1824144220782c1526004030003481d444d860040120760759480140101c0070442c200c00b89000050f07070312000d070041590601100460100046000321001c0300802c81c0500c040c00c01c9681c21502c219141070b10340014040c07034a25100320510501081520406503092014800000005482045076604042491003507580209807540d0f00c0b01c071402d07030302500040010110608214049882c0a900800c281c0d4840c403a040d00f0048509a1844030b2942c0310760690303c11b4042032052072038035820b10641044501b1401c0046c1000c1c00c11000004203110340c080140f00300640c000b102100141f10302510f0301c4d03400c0980300c9603654140407802d1008680038426020b102d0b0080001003002d150204024020003059401440c2c0044926811000742c0000383d190b075005100c403100b00c03011a8500704403007800c3e004030002041c148254504503800d860140380e400221070a00902c403002940340026101e03007540480d4050b8566400700009801805412484a64000a00c05a000703040c2c010315032000c208444802d54041 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 725655818 1250 725654568 725654591
    0x606040e0f03120a1d0a02030f01060803040302191e030615050906090a0b120610082103070e0a091407051602011d062a0c09010e1503010f0f 62
    0x19100c0700e100c2507840c2d03001480040030102904001d1544520b641c0c0e00031402001814504281c41800440c14109802000e0404198242000442100a1628000c001c560f181036141922805a400001c0c4612103551107607906189159008020300304030140d0107030f007002400d0b20001d00f02291004541d02410180d00400070b80201d1000030440d1000340061032151744000c200201c02c01d00174200400e45541d50780606298903a442142c00140c4d101008180e1070920b01c40054500e0f103594480910350b444840ca1207840d0000d1042c0c07640880e040708117940ca0b030301c40203401d440c0e075428000c000307800a1415200181030741c403d8101c0650210036400309102901c40f03080442c1e1902c40e0681d0703a003071400c008144800551040c5500da6591b034224030040e0b115203d48000030440d6000310343c110440c0702d40014039603c0d40080c12003548114884401089005698400b0401c40401481f82d030180c2440440001e0340b08181c21022111018010300800c42030b821510307030304c008280c40405107230210300d4a80d21484 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 725657068 1250 725655818 725655823
    0x50a06080112020307080f10140108030f03190c170f070503060609060d1b0f051303030302030916062a15110c070602071d0f0a0b0301110c0606040e 65
    0x199105039403000166800e04902e08540e61840000b00e8261040d0f0f000050462010700c40080307c1c800fa500944040c402415450003915003211070341480d050303076100400c24a4400002c90341083e8607104100d45070340e1001c2c01905181071200450b42c8181c00c01c0d1031200a140d11842d0aa50346404078030403071254803003122002c1615400c45010001c02d0f02040800d8661034400040d1959050091006152410300c00050065421071503811503c2620b00403406441d68001d000080e64a1182c6420343c2840004001e02d04411410b1002030b040c03680c004041025640e042c8031303403500d0402c2c2855203040703207955074001040b41000c0c8054100707c3c1015882020b845843c624a4165560000d5400c8048060110710200802e015250500c2448041010000d9a001800a40010b00454000e00300c0c840c90103002040d074104000e811001105104100600510a40c0b10340313401610f00240052002200000300e4010080504050800000861841c500840010b20b8070b00c40c90342130380c0511402600300e0241c1c0d03 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 725658318 1250 725657068 725657089
    0x7060c15020c0714060c2517100c1b050a0506010b13140a030c081f021c0e0f100e010b040e0307030302130504051306110c19080c01020307050403050705 67
    0x940c0303401405003085240712100c03801c04c0b400c400034103040c6008031801050340b502034021440d000c0c003424404000404500346111400a100208007072508130702214078103440c1c040c0b1000011440b41c1d541050181c41c0c1c80f5400440f20008803a8203540f0441b520300341a0b64510104c10700b21003920070440089810118601502d0b802d26001080c902024180681c1450080009030b01a4009030845c00020205071260012001003030f1b00000340c007500a540a40540c0381120809500980340104101615120600034906103044c0ea0341c0d00103405480b118501e4104102c28607a170340c8902c01c840b03e42003d80742682c04145c40b8000317a002000145940000c0c8800e6580c40107090005800500100c0301090103900200480d40c070101ca109059503d82002030110703502500c03124aa005002d00d980100855486071507031491480300302c142003014240000756580c0c0000c000c0c20403011000e46d46401c101004042d40c0b540c860600081d9124034090100420702e8125102c01d071150b110f10700c4005000d081c82035001 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 725659568 1250 725658318 725658337
    0x9110c0d030e07030204091407031b06170c0304020301091403220501050f0f040305030f030613110406051608210a2702061e09040f0614040e0a0507060c1502 69
    0x40642d680745801b000001d00741e46c00141d4100107000c121911b540414400c3c9000380d03200384540d9951808040407031070908410b810030b006201c5c0290850b030164111079189944148441a4540d69984d42d20100c2c0c054107100700010f00300450001d4052103000040090408001000340d0f068241d4215100d1100e08801c0d4425a40407e404111124001091200510b515912965130600e45a500d07075a032403441d0311140d031010f807400010040c0309035031504080f080b041102d02c200c14004183c1010241c2418407840c4944000d2241c0051043c0d008001901e11424060700138503d0398845508591503543c40d1007800c10904d031101007100140c0019090300c02c00355040b0000303041002d8144000c440c41a001c0c440361003a1f03030180e402d201034840460100903000b2002e00c01b02c8500d0302c07100c0010038081038805560f1200300040c148007081c440c000820204001001040b503011079000c8201c03900038202440f00308080c007030b8060100c000ca03100ba00910280e0400d0300c520480c9105c010701c803d044003280202d0310380c0d = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 725660818 1250 725659568 725659573
    0x6230a0b060412140f0303070216141e0d0807081305011e030c0903051006050f180a0b0a0e090114130209062107060306050a06080c0a050f0409110c0d030e 68
    0x105011840580d05280e41c80d1004c2c0c101c5079082c0c10080341915540044038003900582c850615107100c50048035542c0010550300c007004075180e920000040c0d21900009281e4040101d51440d0605556081103001031150043e038080c0c0d48000c61b003080e000039404110100300c0010101400102944910656a4002d0707110544014100d040d0b60114081c00c142d001103810000405000f0001c14020700c0540c0d060343c20f841001030315510300424084002d4040110500ca110308001007004481c035500c14940c401d80d0000c000500c101c404c4009072030000c1d150810880c1041c80403c128450700c055008207503112414004014594a121422041d000280c8000b9041201c10010841d00d040055200480c0340445901c040d18a0381c04281c54645202c650228000035182d030001c004508012541401901043c030b420949850007c01c400c100e4492030000c1000c003d00000c0b01e00c0c05030081ca0685016206640081c070034098084c01c204195005034201ea0402d0240050318550140248102000703880120702 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 725662068 1250 725660818 725660849
    0x20c030414101e020a06020d090c080d05041a161b0b16032105090a030806060f032e060903060516200102120106050c1b01020c0d06230a0b0604 63
    0x200410a401203540f01c1d8198070900558400161860000d80140408410b00181e41e00c0207003050044103510740c3c010310254000c48906d10701503501404617819508800100e680d80c0f402c090515041d0300c80c1045080c0100459a2010108000555036110005184d80d081e41001d4a92031014041d2040d0b0000b09240782c5c4c274001c074900007400f0380031561002401d441c0902c205003079040c03c0e0094407011280740103140c0252001c00c0825800000c1660404002d5032814205858101c40000302d21015001e0050303075060607211a00d010344080721084542c01a1405040299145c1010307162262500080799240d09180000f0020030040c00c076009511030540d111910085c134034040c881ca40c082403005c0b142954003008808400720320700422900a08140ea10540d81e0b0085074405410100c649510004921080b200e01203583c1c0d0010b649540028101c0302060030701e00c5032401c07000400c0004049900d0b44148030040ca03d540920004511405145506000d140b0b07603041000b010348034600901c00560b01d80107 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 725663318 1250 725662068 725662097
    0x30904050403021e01150909021008060604090609050105120a03090e06040e071202120303040317270706030e0c2b020a140a050f06091002030904020c03041410 70
    0xc1085800500034016104512581c4800f500c2103900340700d1490042c0c4d190082110318215100d0090001e2010480410040a40d580010044100b00500004004114011441569031a011100140718002c01004100c0d17079894034074081d1009214151040303440000d4503c0c020408101c5842c100e6069075414807090502d1034001b03c8100c040c04090300139a454040c048010000c002403c040c000c8040001300307801c5270388108120406a0004400160000e00034000083c0d0420804c041d0320868410303406d400e50780c3c079240500f050849211900c0406641c1425040c0303090208008040c0c40c880e580600404a00e038218999548510442130341000079003440b8202e00000c03005405c0c0a03089140000d1075540c0e16000030703002d034010360490322021040d15901c036158034000c0402801040103690140c14103803000001009805070030412401036030300c6030720071034100d00c2272040312a801e000603c02c549442c50381c812940d0340c0d0064081c00107044440d000c480c00c0c40c9000d01d02e41840049076a1407106810102 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 725664568 1250 725663318 725663321
    0x60c0405061b010204051315051f12110301090515040c0f11030405180a20030601050c0c100c03030e12030103021302040e040b060306161e211d0c03030904 68
    0xb0004040310707560a002c082056544c0542140105189400204580ea405000c0c0419182c07968000c0f4410f08008070456204050048500a0290035040a8418546621002001e008450b280c000908800000840c03110403075400356003e0300341a42d808000842a40500080740e070340800c5000460070042c0030902c210b20400c00840c400704084162420b00e0380e204e0108280d41c980155200f44c03400340100b0001180c03218810221604072141d40103442d6241501c0312042c1f484003410f61030401c40c000400d89403a4500b000202e40c400d07009440c0c000c0a0403510801441002048403c034002804c0c0300f02504641800238920403400300502c4198607591955003000319580b1120012100c4540034030000411442e0036108512650003000c240c01c10b880e04c1003c06040c40e00c010314440d000c5908941440d900e660144195180041c008849200380790042001d499054640c100d2096613041c200740000000e0413900b10310601124900800940b03504d00c1256500c0f1105070704c0302170f01750744203121200b5503103000e = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 725665818 1250 725664568 725664607
    0xf0901380109081b09090102040302011d27011403060105090f040c03080307030c030b120a031101020408120d0b220504030921020f040c0806130e03030414060c040506 73
    0x1414420001d030b0f50f540314030f42441c40404c5112980c0040c2e41c8800c195080103040315900612000003140b0f00307800c550018007051607070301081400404c0d460406800740c40748001540440c3c84240c2c904c0c1c16813640500100c10034003d0041c0d4240034958900c4140608000441c941a5040145070221542e5526098003104d40000c2040c4c6e10051000c40000100785060011400f900c003070ba5012030707481800c00001d819190120800e50060740c00c18503c1007588404940306020036450300c2c000705106251003009019000c4c82d003000007613000d0b041e410302e5201c0c0550300500e06d004c00d88a080c40303607111030801c00031141303072120641c0040304040b040c290358040c2a03440039901602c281015821a40c80300081802e4140314103403100c40c86811039000c4154900302d20403100c803402c100c50520004801c014010301c0c10401410070340c0034410321b40381c901076070695409c02c0c108070103401304a80d108c1c982070070084010070032400388001074041c071004502d08000040840b0b0584101070446847e103884003240c0005580e6 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 725667068 1250 725665818 725665931
    0x709060309020a140d1e02010e0d0305090112061503140a090b15181e010b13060c060b090f0f13020904110a0e130309050a14060a050d02030f0901 64
    0xc45d00c801e0001552048400c2d82000002c061000d24070280c2c400500900ca80158091007062001c84080c0081d031b000f001c0783c0d0000000e12782107000501082590000e03010b84c1d0030844420284074003201000d581030b4009580c20503090342401e01c50721043c2040e01200c041c400c8c00340c000f0b451800018a00d90080d009200d21020203040c001d4580409812074800c0582569040448541c42d2000c01a003281007000700d0152001d1a215840c1c60b801c2607140f0030070341e030511881c4288400c0c2081c590500442d42d10441c414000640300c648649061020b030700204a00702c86071008204040c01050041c440900c050075100c4d070107084125240ca070341e1075072041c0004260315180d020a59100204000c0d21002e20203001ea0641d8886040b02a502d00d40a4134000305908041d0081000301c00401200c50425005142031005494880e502d24640c041101c00b071041800c540c14090000003401b101072000c140c242e01c41c8150100811480709110004400c01005c54107001088215160700c0d036050041c21180e6a502c0e6 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 725668318 1250 725667068 725667079
    0x60610180b0904050702010e0d1142010311010309020301021b031b0610030b07120c0f0906020312011509050409050f011503050607050306041d060709060309020a14 72
    0xd000e1180d44000158075044290038060114403205542418010a0b402072090b00003071124455110300959034510244804c0200164141e910051400c1841800c40003429041c0c508030405c10744c007800100000b29415581c0000c20802d0640c3e0f08142003580da8182d99114588a40941d0003000440180071803180c242d070315540c02c01c20741d040d9481c20313414041404000c0c0c02442c1c58000d9060b1003244010169140212078004004002142c1d840c0b0b028081a254015840341498640f280c3c11039800713099421082e640c034501303000f0220946d04840502014512950b405900c9901c55004a8aa008041d202c0040303411500050000364000c4044240050061030451200c9603114005000d6451400c425917084d0401d00c50708403003c1c820f00a8a41c034082d4250101c4046d840c5690702599044000d103401d080040210202d02140d90302d801940c03052030019150590801e8200c003440d01c0340800d440301c00228401c90b0340013500364000d0003099481030700180069540340c940100e1090001100c00300543c0304 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 725669568 1250 725668318 725668337
    0x50a060807050f030709170c01120618150f0f0e0c0f16080904021c1103010806130c12121805030a0609080d0e030c0607031503060b01090308180306010b070302060610 73
    0x31050304800c07800d100800780180b461900e01000940030b4681c5200b2858510304114060110301040203c0e000c10702c83c5e081000440c070400400002c84001907402060740407070ee0f003a0020380380c2100d114410603150403000301245511260308100b078504c0780401e9100722500901200200c40000104100b10728001d6244500d0045941c00050032a80400389a10035052115141c07150034a807481502c82d5500803010451031541460f42d8140d5602c401840c501d150340e15507010604004410703440900501e400d0300c121032242c6040c640318008103d10301d4200c0000d5903020103441d0031129080302e82c04544025020f401c0c3d9941e6a00e4990140c100f540040d200020200001041214284280c16011030800055501d0710350201c2d486040020207444c12007018108030f140f246c568800650403003169071080c40000d0b81c901d0301c1c006980c09501a030002e4121500450390401d4004a201d0740c681c0000101c06848041e80c8031600700c0410b0098030b001500503481800090310740c1c1070440700032215002034104403208 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 725670818 1250 725669568 725669579
    0x40902090c0d1b030207050c06070305030117030c06070804140604080a030c0207170a1a010f0e15091501092408060d0602070510060b0304210512040c050a060807050f030709 76
    0x1030b41403210f034540000e9001400c04103000d400d2140540d103543c1115082d01e05105918010020b001c10702407048541107441110f00302c100100b0442d4020300f01c502c00e8600d2490541c030301400b80310017140c096900140c03240b0301181082011840b14400c0b54012115401d14601d0701c0700310004d141940c1d00c48154030a141c40070541d1a00780140d0054552828010426010107281c04001c902c11009032207017411000005103c02500e600411064840d2000340307682c40d0342d82c1032801e0008082240b59940040f40e4a040c8050f2a413102001c408160303080e02d400d441d250ba28040c515203050f01550045446100c224401400307441080307602d400410040c10040c003980b2a44801c0100da1064104403040c3d4070800e091411031115006080042c102020b256041d131905032520b00e01a2082010b801c254418010341005a9016800340d460700f0301445441d1265150500e080c00c0303070160500070b261240040c941d0010303d29100c2c076403262003003680e699614186140080d180301e4941001d000308080c4210740001050 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 725672068 1250 725670818 725670851
    0x3090a0305070501020f060c04050105130b07030e0f0d080702090402040e0f16061d01030b04020f21090c101b0f080d32060d0209070503070e040902090c0d 68
    0x654020800b4040007031074107002916007030301c0114401c40c9400030010048041c064005a800b1070700203080140e82d8840524800d40081c407a604188910040814003806042d4001082d08c074405042d031725503504034000310401407018009007000303003201010081000103090020220360402d101400104460750fa1000c21428040340490046c5158040c140380301104440c00d92401c020941350030b015100e20140c0c2480c104941140d483c6505241e01d41568003101e44030356041760001140c0d00d200c907071510070311560100740108503c002e840d650f44071008681101030103d10040d0600004000102402c9444410b450a07105549a034900006c41e50209011408082c4010340c0302d4400e0401641da174584000714011110034990100312000c10480100d038900340d100e0034141009800050750030984d207482c0003540313036606c9403402500300002c81c01380040300380c1080c0650702601840e140e940e0800c1901080c00119160268065406091500401c5400805800a0a069031001800314100c03868203072491 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 725673318 1250 725672068 725672089
    0x2071112033007111005070207030318121209030203030d0c030510030c170102210f011406030a09050a0614150102070311041503061a120c0112020c0309 67
    0x2a45500001000ca200704400c07800103040c070b00c00e4592030901894004048101050041c0940148a603101410004040070840005207a0010f80c081c89986000c240c0251502440c0c842100031980400d41e940e043c242240300c80050b02d11203070490f40200581d80b1224074a13480303a800101400741c400004400358030300380000e28000c1d29840001c9142034562200600b298002041e016055450034014000600c9215020044960404031412080d00050000340248a00c0d04109040781400070180780744010650304900c225018440a200d40e0703a61050105041a0509081d0707010604000103964000303a9880280144e00500c00ca03207104c1d0640d5509811034440320b0142c112151104100250818500c80c45d4030b45400a2020b0030a09295036a09000e442e00c030060b042c4181c0d115052003c950b07030103240107001503402c0b0005108081c1d620980c00e80044d1858081e40c00b41e41644840401e0107c001032031409000182d440007139681060500500a4101c84840d20303041c00208409541590313410000c2 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 725674568 1250 725673318 725673349
    0x20c0c040c0c050105253006050d0c080d05040305070605032701050907092309151503060106050a0804020d0204020408120d0c020105040525090c0206040302012d020711 74
    0x80c01071051030305464040a502c91407080104451060b13510b20102d5040050300303c07c01c43c01c0040c014034404070102070010303904800c1d0032001005100d81032154003204e450031182041c069400050885c402290fa40c855800301912541c0446010020360380301d1002554051000d5941032003602d00c400303a0700300140012410740307503e83d1500180540b00b5030500410000348600d100c00c00518204484d08110121104280d280d820312030350001c0d0541005218020303c0c0d541c40170a4042c103184c214445c1c100000705001c0399010f4814140049203090091086440c24182c60b00d412026994550070056131848a1400300e070815002c0c030000451800403c0100d2038071902060700e03521441c44030b550004039602190a9000c6a040c4020301c8085600440e03140311007000e054003120701d1b1465049100348180d007940441c2c0c000c2e1030020111079032503011904c0b50044e4460b038024000801d030400d0200c0c00700c00c0d86801420351140c0c04003406015200d5030003810454030800030110401000c0300041c041c03850b501c980 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 725675818 1250 725674568 725674591
    0x110301060540090b0c0306011b02060c1c030c020c090103120c051009021e1011030c0a142a0402180303070303020a08090303011433040612020c0c040c0c050105 70
    0x801000b4078810810b17441411440c0843c118903203100020a252440c0340007503a83d1031121120340544d01c0315012140d550089804807840c0c06451780c2c07004000407900003e04002842d00e0844d2000600c040341c6c8a03a6120002c0007200c07540d00b1501c8118410f00300810801c24007003844031041c0012802c0c013001c05e81821030480040c401c40c1c0760060040d0026a02035465000b82005c0f0341c5a0075585500c8240310801305131908402010345001d2051441c401c40984001510600035510108000d1581c443c0d2442d206d402614845140c1d001c02ca0064031412111a00c00381c480503003001a820681d014080c942c000041c104d403200324100200b402d5600180c0c00780c1c0000d070001100e0240a800c044055003100c00c02c8001e52030341d80b501042c0302000c0424003c540c0701d02201d046030b42030400700001d0aa891030450030700803141202e41030311460640c0035100310350105060050030701000481d4403d84140d000d090b0050850101c07802c0030440101000403501e403d0000d03407141c60022904c00d218051154124980 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 725677068 1250 725675818 725675831
    0x11d01020d0c09230a0b0d0902130e06010501030509190809010e0d0b04021507020301020c0c09070e1e0103020f03390d05041518110301060540 63
    0x1000802e80e0740d480c0c80c0b02c06000c2d86441c10403d440c07520800d60407940c4c10b00c0c14408070021040026040728140d03484a10002c41c04610b01c1c108402c154009651140300b214420491140c2000040a80e01001c00c200e41503045600100000d500a40189600900c0f107800d41d01200e045e0008541039540300d41c000d554020010030b1080031540c118401c3ca10542d81241e4518943c4400e42e101540480000d000138043c402c910701c940c00c60091782c0c05a071045a4024001d5440b00c010403a0590364801d013151440c07150100f4070104c0e0f2401d0085003c80300c00351001d0020100d2141402e004003a000c00c2c554070a04250b800c01c44e100006c503507070000e14080e01c100c1f51030070001410100300c407000c031529030760040101e9802c06101001c296614201c44030101c2649020807140d41d2400e0a04e520101c81903454801c904000c60032800140001d640010503100d11015500405040103141c2218050301603d41c06c24403c4030b003020400c0e0558507603282000088040a60086041c0e2200c103007001c82411144d50b41d40342c00 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 725678318 1250 725677068 725677087
    0x20d1d01080f04030e1011210f0a0507060f0c020c010e0d0305090d020d0c060e060423031c03090209010e01121e0f0b010305061501020c01050a020a2a06020601080a080c011d0102 78
    0x100c230b0600c0700c01e80500d002d060034070700c003210603109822004034072580020345040002d01a0050302e20241e0403020400c140e141450302200038084401202d001405045855283d039030180c2c0c81e08200500240c4508040c4200d59410f4410782e000109095000c0e8050310b480f4016602c10070f50307141180c85088000b2030145001f8029042002c403140ca03e20454092100740a04c6000c46e000c2c13401c1c0034100380700300e400305a00c038042401c06040b0740000b2400c2c45282c5d0480d2203145c244c1c0110151501c29a01d1b4060740c0e980301040a030075442030180600501940c3e074036002040c01d01103d004280c100680310b0044000640d141e894400c0d2415003111650801c400410500409106240d4048041c0d0300e030889031030a020001307443d5040c071501c085c113101003c207003011014800c1210030805640140042c440e400c210307000001160450040c0760021189020104000b80302103901c9040720400e10007400030075126950211180c0280301d60b940c00d91741e01d8485014214900d4011440240140c0c00140d070f604409 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 725679568 1250 725678318 725678323
    0x51f02061305030703200106140a0f0803030a09032607030e15040b07050d1a03071203051e0d020a0e01030b0d0221031603020d1d01080f04030e1011 65
    0x200600101e440103464440403950110440302e841d07038189070084031091142c0703a01821202440d402c203107541c41c0000210725100000415460440e003103d1040c180369a6508144e0301000c02c1c02284000e40060003c200707151b0707141e08036410700c5129080c4040703070000141e0b03404c030034100310a82c03900440108802d201340250103100d9040287c404402914803000381c644103424044010704000c1441e0140b20000c4c034001e120f80c0c25905020303402c2d5014440c1441840b603104040309034000746807084c000c00000003240c0a03203101c1664100d5258548a06141c5140c10070381c60b40071042c4840a828170b0810040b005840b0354130080040d196240c6a25140310741800c0018121252b401015010f5401c1c4140c0ca80580d03910f0341e900c0b005030783c500c0400c58070100000a50f81107020f001c40c05aa001a07600a4004058011544120040569850000750034021b0740c04054260401c02c40ca02041d130180101d038030180409602640b20303010b4140840547d01c9500443c0c070380b07010440d4200018000c24004980c00300709 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 725680818 1250 725679568 725679571
    0xa05030306090f04021c02120a1a0f0702150c090a26010204180f15180f020a0f030e0a080d020403021e0f0d05150f0702010506120309100504051f0206 66
    0x101040f1600d00c1c10390302242d0050012030091320301101c00f16181d07085551f080e00108496002d40143c60b01c3d00c20614000d01180450013955030f460200600103104800345e0781081e0b200700c07510703401440e1710740310f50b081c03100c2941c0b001d0030350700c5a11801c010f0321240e0b455502c0d00030001d0650b408441007400041c40070984004124020415036401000304000700d481c8005242c50040c0c00700300020b66400c94518040051901d0001c0300c00e14010b4100c0000c06080000c8010b0140010742c0c024416100c414940508034881c204403040031401c450707e0310782c82a11030760040c805a0b805030111980c0b00800d4030b420300540c0100440d005044c1d0009400d10841c02d20a02c0c03d91490100031051003051601800200d140300407440c0c039800b0b40c02807a00c06091203001c21203640380b40c80315100c040550501802c030a11a03042150000050360800003c181d450524a13050348800040d88041c1d414060386900f0005804240f45002080041c240000306481c2d440c200c0016141c00d03102c060740c00c020300d44500642003600 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 725682068 1250 725680818 725680831
    0x10905060d1101030c090f090c0f030204030f030804050a050105010b1b06012615090a350307170a0c08010819060b060c0f0c041b090b0306030a050a0503030609 70
    0x100840c1c200000d9510200c401d0061000d0802148082c10b50300c0032910840e1a600c0506140000c440000d240c3c00107a0281d103030350403d0350f07561100e0004110207038164403036031100070a07161400b503a07500482d100d0028190001d11800596810300d0312030b140c0c40d0941e1001c0c1c218406a000000d003888441c0e0600d4000307c02420b100020385003941c540742491507103204000b00c900e002000ba0b005100400d02c01e01503000307000041e4465407a0b505200395020780c1c0e40603480040b03901c03002540480c03108040001f80c6204501d03003a100c100c0046143c1d0040251604007a100f1414802c1c180e840c4005038890383d00304c03441580c40c00000201d04a80304002011000c1c1a07000a100e900b200407501d0100103640480b0354116001000071446043c20400b0031124820700b1041c110130f020740030744411404801700c1c41d0001e114080b00c0501a100c2036082c0700c40e00481546841c00800c45250781001045900d202460303010318018207683d070100c25500c2d0a41040c01038039080301e413074100004000d0300746800210720750460b0 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 725683318 1250 725682068 725682079
    0x3030a060f051909090821041505061c060e07030503120127020c0a02061b0c040e0c04090203010b030a03090306151404050912160519020315040f05010606050301090506 74
    0x1885041900f200c032014010362600342d449020520074000e0150490310303002c0c500d211021101e40e040780e9054141d4000d0740c1c2142e080101c040c1103103010f40d85024550007401c0c0288980e010614001d180070000d85015002c0f101161505400405128184000c10003180100702440d0f550000c181c03800c0000070141c21204820826461400c6807404600c50500f205100c0303000140e0341d030860707c0e1051510300920300095010a0024070641c100346225682111b543c907400c02c03500c0040c0d0343c508100a0717800181c00101c160344042c4001c82c0e0791a180e000640541d001500001314045040301182c10149048416404034025010405c20044070740314442c02e2802da10012405141013010003968008e079281070300e100e103840f01c0201c1c80014050000f80221003440030742e81c2c1d0780d002c40000e00038074410740d1800343c80e1401400d48245125070f807038400e418210740c0100600f582c0c4c00004080300240c10054819140b4580340001d01000501c24030901c40944041d8030303800c0c0c032503241401c0c040c25904020300e45802075 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 725684568 1250 725683318 725683339
    0xb0916090e010b0705162105010204081b03010f0c02060c09040e0105070305060102060a050405150c120709080f0304051c05100c090e060315071d0d080301090c0503160e0f0303030a060f05 82
    0x55010407c0d151060101000c0e036a11241c242c04e1143c06401113400105203400f800b510241d60440d03400303c9000c0c0000c250b0007070000c038141c8442ca01c206c43d1650702440168003d000058442001d0078028901503800030310001d1601c01d00c001103421510100c58900100b907135101031054660701040b00b00d600a1100341d0912032884c184d0703510f58450107040c6802114007850000b1034940350206044d10041c43c0304007052045890728110080c10710440344074180040c000d13110f00c42e0301e40102008503410342d00051300c0d120f00b60b1041b1800303030842d5044100c142d455005001018a17407103202e0041d41510003d03035569215403814810356415104014000c0c134807036402008204085584140c0080e40b02000d41091051100440c0c003110890303141c440030981c4070303488000034410403840c3c0c0080e5050780e4581c0010410303810801c1d410744542c8000e64000601070800f40300c3c40001c034843e08519400d200d0142075002000d040001282c41c60b001a611030f900d0580760f400900041040e08001002400b0803210309400 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 725685818 1250 725684568 725684579
    0x304020f0d050c0f0d050105040c095a0b040b0a060c141c111e03070b0402030102090a0e0403030c02030f07140a0f14060105040b0916090e010b070516 66
    0x98940415200d13002e03140c43c6801010135030361800c40305404c0750880001c1c8054502860661442149030251600407454442d05040c105202403e907040c44240c4146408a24103140320038261024040211800720080841001c4080321400716540b440f051400101c1c2d800c4c10002000107841807107401c6402801d242c3d0003085041c0e807210392001840d82082d4411020905210400e050811881c920148001d4599003002d10315481050080b00407506016985980e00da0306a1442d091082110b620349035000b070181001040c052074002c3e8201d807004000501d041040300101c0c90b004516446072007081c2610007040289a05400381c802085d180b44040c0d441d2948003040442c0c1801040409447e0032240038001145041c10002c0208164100e44140d1444903c0d00d803109800c02441200d0f800e50054100000d4603080070b000721489108001c1518200d65101804000c50100c020640000c0244110000802c0e00c81c06003514060f101c007910241e070380e022900300743c2c0c03508119540c0d1424001612004014 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 725687068 1250 725685818 725685823
    0x80d0909140402040e101b11010b0303070318051509030c030a200409021203040312050c1e0a1407090605060f1608071b1503051501050d0f110304020f0d05 68
    0x140b0550495000442c8044020403d140c4038000039517420b11440e11000c041d5010b030b24640280030b00701c01d0369561440385d007409a503401c1e1808881c085416a1003448284000f0b4042d0404002c4101542d01c2c10146d00d0b542c000041034102c1c100c201c2c010b80500011031403620305041c05846a01c070f0056005081c08000c9039a01e40c07882c6111400c4a1840101c4074190100e6500c035007060300c9517900141240354030031192010076160751040c4801c4a07102a100c2c150300c40305010f00181c070302004641014040d001803607000040d0001c911545c01c62240198040d4000081c40c2800b010681b510305002804003d0805517640120388650700007a1098a040c0030f01c006c80d9210200b11070801c3d51000c04001c00703134003601c0d220006008140c0020711280c201d541142d00a84401007410454003440810061b048256006404540b010f484400d20080120301400865024000800a1103450800081e4003190603002c4000c8401085030307420a11000020b00041d481d10714660140c8960498501d40d036079803c0d0780c3d02039 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 725688318 1250 725687068 725687071
    0x50a150f030e030f03010e0907050a08120327010609060f08120d140c071e03080a150f090605031c080a050c040b0f030402030105161d1207080d090914 66
    0x4241d00d03251166002d0006100b0340d492150350443c01038480d610b03070343d000301410001c507800c1e920352141540002e100d2030f0503144502102d040c04041c2c54541040584954182d00040640c20100c03d003d10014038a02e03088504c0400e1180c1b4800018010300b041070302c0c415528039500005000b8030001c0c0c00e0040490201d4002c0251000300652a0b50300313090881d5a001e0520064003030f0079000c51204018138800780030020804a8460015410b81400f1104000440e00352608090001111304000031441c1d002580501d0700302415400c074034407256581c4200e071aa03035001c0c2c001701d012036103410b01000181420030942101a9508805190070810072030010610302008000c1e448103511a000300c0d00140b2000111405881c86d601415600c0c00d40185008440e4070582c0d040340698601000240301003040362005441600c550395500b040300010761503c62000a8094282d480b00040301501c01c02c6004003c000b000340b40c40745c05000c090521240180c035500142c0c3c0804884ca00300303020f0a1510601c104e405 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 725689568 1250 725688318 725688347
    0x1050405061e1b0d0c0f060c020111031303090e0601081b0c10020c0c1801060e22051603050f0c21040b06040e19060b03030706060f050a15 61
    0x700c2e00c4811079020074140004012002d510300c880041c080070b0381c0300d4880504500320302040072207044040c504401c031000b01c902c0308068030303c1c2d0441c000e420001e04540c00c11460810541f0001ca0100780b050080c045070703482516928109400070043e4820590030180003002440c4003c008a660300e01100007070802c4000500084144040400070040c2c1d41c0b4000a4450005116044030503040c551140c110003503000c203940d21464490000d01a085240503120400101c00340c18608291f0392178142c3c02d6582103003810b0000d5028200a5a4500124041558001c1141030300300c0480d00d420000c0300c50740f0800703420301101c00f0581000c0800c0000318410100301d4010108046e82d5035103a100c544045910541d030203414100190ba41c040c0802c0c007080c200317001c6c05410b04407030030017800d4594107009540b00c80c9401880005040150007a000c500310743c0c0490b040c00005001c1da85010082c2d96114201c0d2102d82003610640079210040c0801d081a5200b10003801c0c1021240300e070360807038250140c040040980340 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 725690818 1250 725689568 725689579
    0x20130501050c1e0f0f1006080f07060f1211070b06010c080301030219150306170c15070809060f07050d030e15070203130609050f04020a0906080604061203080412030b01050405 77
    0x1820b10b0140f040140790100000c0340c003a035291607400e4400c0d585a4258003e14208641000000701e8010008180c010102100794018192949440c600fa510000f003442c540c402e004909844400580c114000d07942420500e0328410740c0c0e101d06290400220402801250401801e6400310001070a41412039064a804484004220004e0440b4801401b01d039007115030a800c1c0012540d40e41038240c0c02c40802e540c0180c0a205a11440200060740c03202c0c01842d1540c03003040790004600c0a203807000145580b50058141d2450070341c0718404541c1da0b03070010504d20058100042d4410078000184000000c80c20145014441e075105402241c1c2d5a90b41c610030300042c040380c000490142c5008004980c0c4448440180907200c0c1c0ea101300c00703449000e10744180c03800303030b6851040805d440c40d051084035058130144c2c8800210750300b0b000007284d500320000c0000c0c0d00903940302c9020070002940711030791811602c259186900c5140c9481d04540326060702c1941c0046c1401c0c01e181100981c2c00c1003d483c240d8805841 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 725692068 1250 725690818 725690863
    0x90317040506030a1104090c11060619090b0a05060408031804021201031e0b0108010606020613171c1407111209040b040902040606180b18060d20130501050c 69
    0x40d111203482980c3c09001a5450050060042394200c12151005e116003429204a82c1e100340500c070140e082c00300c2d24041201c03000024042c440041c0c1c4030002e0300e8000782070405020745400c04a10940d0041d0000c640650002c07500481c0071103403046021038081c050710150304000126000d0300c28044107000c0108050041c901903094209051003006901d41c114a4060302940e441c051540203000b01e01421005001d200b000540420800c2512440103501c480d204d80b4030034039000a4030242e0042d849400301e0f40c1403070b43c8a20301031250340104808101681c0c540e5125041110026200300c212549541d0b26401c0b080f4445080e004100039241c0c1d9074801d1f200455116040340004004042211000794041c0c50408080307a403549c00043c1140c416200d124283c1c00039111071481034140220410741003940714103444504941498806031104c81100342d40440c1e02d00e0903003036060140d030310110000a0554046000079800c510007468400401d428244107140c0891980ca071601c80c03480260718440c041c007010 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 725693318 1250 725692068 725692091
    0x30a0605160e060904022b0203151909091401020a0815122d0a08040503150412201e012004030b041110030c020c010e100305091903090317040506030a 66
    0x1c0c000b50b241e01c840c0101c0e50b1f0702056840e0400007904103840340d641411841f060b500c1c0a003010410b001101c0c16284000e083e0700d00d410180405003000038800c0301e0100c00c00580c652004001d0010300203101c1540c440e81034528108913820b10107604a01454800c45100b2400e624040c0042201d0300b8005a80800103914101514a8180c80c03044900f007075803d100e050002014000ca0b8409803069807400c4043e00c1c10504524604c642c10f050540d030103404902c0780310320840c2681c01991581001340c1030100c0d10032032a00500605003803400080000c4010a081490b154a1900078841c003007415503621500c400d804c2c2d0139410300340c43d13002c1c4d400000c000c1000d24001c03401380301c9000c4800305208402005841d68110800000300600003021480000d440f424204c40001c1d80a01984c1d00c01c2c180280c82507a0402c1c2d8108101c02800024290b041c882c0102d41d8940900f00f00c0311106072150b4044e0b200c106041c1e00d9454201c540c951400782c0e0a206100c28003050000e981c0f4541101d400ac02c0e5500049450003192 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 725694568 1250 725693318 725693347
    0x4030309031d1f271a040506032d010801140604060b1e0c010c0c1103120d181b030212070e011505090303030a0605180106050f0a030605030a0605160e06090402 70
    0x3604080d0341c0c0844500d2000740600940c0c622054564a281d40513000b100c5e08902070203402107004095003d2000d00000c1d040c0340001003a224104107003501c09080c803103c0c1020228041c1c0a801039070340c69451302022500702188105844d04150180c0d0b04010701840d050742070341c00f4068503040c2c49c1d1350072080c5103580c15801d650041da685841450000c0050085044029200b9880e40360112404070802000c0c181ca0f2401041c0c204500d054000000c3c5400d5100009000611443c00d1103044131a00200c800080f55100111f65607060110400c481c4450441c0100689c0e1102011440d0440e40124000c0c0101040000300310304580341280e408200101381102a44c0e0750003614100741e0140302c0401008003520003900540c0c1290025280f4211101c1203100114115209004140c0458401c10080414080034402800700e08824600000e65603202d000180c141440210140d88494484083c07280310200225551a84241818a40c6070505081c001c12054000c5103001c0b44910350100300d680e20305192 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 725695818 1250 725694568 725694587
    0x70504150f1d070509010c15021b010b01180f0b03040215030a020414010309030206010b13032001090e04240608030a020a031101020f070204090609020904030309031d1f 74
    0x4409101500549401d803181c10010800e0328025005000c40c00328071501d004804445c3d246506039518a0019055107440c0c0c450710540d0b00c850000f46d402c02060070407042c2c2a40c980242d0b0503131800421b0710b42c051400104004410032071184159442c80003042070404002181088500d0300e10780316225a6a8000160100003109501941580003c02c0010b0040158020010f95000454202c2200100b02c01101110030300340340100543d001c54018000c25000070098086010680c5400d05100e0703c0390f90340300e038000480030b684008200c519089120381d07030411036100103406044078200d00b80c41c4c19100e038040c0c8100301c500380d4000b016401d1890034408081d040600502024400c0700d60300c490981e802035a40340c41310000d8002440c0b82c04092100f4106000f02e40c03685421407141ca0401c40c0e0f41c2c003000010001014100c1303001d5600d41e1044010b80780c40a01c18440c41c020348000036165980c3c20090700716031941954a07820b07103091881d810181d07610041e6800740301c4061007208003100c41e01d074190f81c44d40c1d1 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 725697068 1250 725695818 725695829
    0x506010f0b0715020f04081c110c01080a0e1603150902011421070206090607020f102f040801060b121f03020a09020a17040503070b0907030b0414150907050415 70
    0xc2c00203010807440c1f0b0014641002c200020000e4150011540084400c2c44444034405001d40000001059941c800c407501500400102000102c00031002a03513441c18007003a21610b0002100c900400c184201d0f8901c5e8000c4448101040c003888481e81d000900415424080304041500818280c3c50703110f40050200e80040000c10892160416480183d80d60004684004040c030614000418440c0b010032072058403190034000b00009060014841d0185c0921654071075941d409456194003410495041c1882c0242d102300b85999a050503070885c00e6800a8002113440481041032600c03009043c414a984100003180c542c51381017281821404051582e80069406844c0c11004910948568002c01c80185c5d5030302c4040c14412007811041072000c1c03c440140054200744811408546415031160b40010b00c182600d000b55240e42d641088883e0540c0c095448a240c4c401c1000745c40000c000400481005401070100d92420301c03e41079032080603001c0c441c007880d12011420b5840c00c80c00c2d1190301502 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 725698318 1250 725697068 725697097
    0x7080a030b10030f0f0b030715050c330402011b230c01030e010608030301060c15020301080102130603020304110f0d0f213f020d090506010f0b071502 66
    0x24211800180074041e202c0c100d03101c207171602000410b8910b65201c1c0481581014001d014024030340400d00301c010408002e10300a002c03041110b103807555020300030280c0c0340c426256460b21f020055148107400003c03c10350241c080d4200414040987e801c01040d500c4840516040c0e100c152152401104800f1042d20141d400302400e03008810000002c100c040300d01c5000c0c0d804020700c2e4a0540d101d400e9030304611800410350400c10040c01481d10a1034140d00250003002002c41c20035040340601c0880c0d02c02d9002c1004c40c2d6011070382e55514034180d22800c0c0180070510741075003941030644130180c0032410030307106070720588201900c030101391111240c401809410406c0503121041509150002c40d010900c4201e106034042801a40b0500031080801d800850354814030240041408154039041840702c540d1100b0451494458003400f18001819040300002c03021845902c0c602e0305503d03004068104182e00c02c42d06a00380040e4808100352140c2c2a04103c07040c1c081d810000d002c50091047d041c8920360308 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 725699568 1250 725698318 725698339
    0x180f061b0a02040f06230a210210090521160314070f030b07030509070308070822050d0b0604020706150e0108060c09100e04060816140607080a030b 65
    0x24000072036030303039038940c002d0b641032140c080140400c078210341140c080e041d80902c2d041c100c1203070048004440c5c0640c24024000c0103003075498480c45d00071020042903502d00100c0c1d2508080441c14481c1c0c151003c9030711410041100c5060100080d8003089550101d481040a061011215001007041103000c07110342000080007602c0f42850f0441d90201151700e102440350307520000e650700d254041c01c4e040b2904100c807200703142c6941004502615000e440c482c40752040003404008180804014000036116548040e60b80100c4a0200c0007002c91021003a001e10742804104070760344030300c812022501d42c000c520460f150b0301c0f400094000e004100014090a01d010489240402c82c0989407080d184194406151603994806150351203104407100ca07070381e510a0000c110b15023464406286030100034200b241c00b03040b400c00400d00f100d119520409096008518040b0800003041d2524050880408260800c0d009003000c6200381c480c0d0b0a000300b0340200058518043d5200e0703802103403d500c004090b004030 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 725700818 1250 725699568 725699617
    0x90803090c15090a0e0903040e070c030225090c02010f060b1c0603020a05040b030309100f030605010c0210050a181806052e11191106180f06 62
    0x45441d94600d80340030340d158401e4020307945803140654420840003060009028284410000c3c1c03004042c3c00726540380b00502020480002006085109020b50b0341c54804405181c1002071625220140659410f00c103801d583c048946450b69040c1503075400324001c00d495448136822401480b145002e2a04285010804160300500800420340c182000e10a4001294540c2c40c1c40304860b0640b00080d0710500417402007003e420560080300f101d09000b010399090807c00004580c0f030980424100300001c140b80c500c00c00080d00f620519015010a20749410102d16550108424000c1d01154070107000c0e000c25280b100d1486001c2e1050710840d16103414900c0d03a43c0d030f050f0b1021703501c080010448180c1010004580c50420803240781f1401d404068070004024109617410303186034016041020000305c1c0c00c00d06d24005040210303030041c1c8028101c060092186041800c4c100e14240c1615104d10b000308410404094901c0318068603131400c81e203019101c2e20120008200d4440c4042d0007900403203082000c1d61 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 725702068 1250 725700818 725700823
    0x18060906040209070f080402040b0109090207111507030e0618150408010c1b0311010b06040e04140105070c2a0602030307020f0705060406140f07080304030f0201050609010b0c0109080309 82
    0x7a41c402c1c0c96012141e103521205441c0812405011000a0601c20010300135180a070401082001c043c140212095101c1c0d06900690313004460995241d804404a40c80030f040c1103401e050300025400d0035034144003050781e00412a04000c10403900c60785010407109402541344144802504005040c0103601d03010300b04086441c0c01070b00c02c0000315403034242e030460400d000307200c00500d4031005605110030b201a03036025101607000541c1c800da19942d850a0275500d88400004102510465a1264070b0b46440c0c03070f0121441100c0d501002d03680c2d04000c00c0c000c02640001081c142e0961010044050030a1602400b8044a200300c0245030710b548484009044e41e0003100550003541650f00365040f0000d002c000d1550740000d4401c4a820180801040000501c2400040310036006031034001e01d0310460504179001c54004480c2520312100c00400e0204044e0811a01c2e502041c840c0001e018074a444400034206800500c1142c100c02c000203001010314000b0341c4424019540499444e1302e900713203480142c0d03 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 725703318 1250 725702068 725702071
    0x6050114180402160507150f0c0507091a03010509211c0f0218030f0d0e06040312020c031b0609010f0302120106020c150c03030601050c03040806010603020d051f0b0318060906 77
    0x1c801b800307210341c042101d841c0001d00301d408043d651100084407200d04811154031013a04820f5449005a420110300340029000d442041d1440240e1b0400c400d00c82401c0500b190030240012020358000b074103000713940c540c2039600c0c04002075801505868512094011880e880514404100340c0d02c1c029158546a03402d9000c0c1c2044010500f05000541003036061581c0c41c881003612007240d90010b50b403166198031901100d8900c01c0050031072410300c1d5032955860100aa815442030140c0c0061031640000d04040265102c0302551740c081018103000400462641e202d00400310341003154200c40c001025019030101c070846c142c107610036000303503079202002034461a50b5a022840707841003814816414201c03905a0300440d25441c065441c40d02c0344401950145d004600a0034580001d10000907a003600380907460081280da100907983e000050143c1c400c88100800d4105041c040c81240180d030441c240700c0d60140d640f001c1000740c0d262940040817402c070141380c40c000c0303040c4951020451040c20105a55 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 725704568 1250 725703318 725703323
    0x21121906050d110906030c0604090f0c0206190903210507020106090c05180a0302060d0c0e0a240e0310061d060d0b04150e06190605011418040216 64
    0x10410380e0385039000c0100d80c0882c1d14000e8096818601e0320041850840c0d03031300c1e0300094002c0c110f514580781030001c610380790050340c41070302455600d0244001441840c0070303001801503240f003e0529484c21404e0500c404402c0099481d08a940302219000c150055001000e4850b03011050100600012103180252200700c0c0c1101c01942040800103100c000350041140d5648561030304c0c0d04003c071035a4a140c80b415031010899001044030000000344e100c1c00001d02c4100703002c1c03a020a4103058828003408182c0da01000b1030195500c11820040a100d0207a03e03601e070342280d40c41d01011650300801300e80c10004803a00ca81d05000d0400c00d8111000e082d4040c80441c0c6c03008030b01c04000d0085040710a000c030401c0700d015421401445802d00018812039072281c0c400d200f202c44000401c1701c0100c01c4101c0303255841d140440d41c0726800780050300c0840484040007501e450300600c0000d0800300000c16041000030401700e10240416100952403d240c01c0390b241c400c0c083c1c002c645070910044200a20742060105 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 725705818 1250 725704568 725704571
    0x5031c0210020d1b030c051b0c0904080304060510351006050f0d11060c0f0a0c140307060e010c05010603021807090f0f0302010f0210050c0408100509211219 69
    0x222100d40c4d019004040e00d121b400e0310b525092046003114120080c42e0400b400511b40070345540b5000b80c1d692441039a00660061100c19142e141a15020b02103a40203040f11102e0700130043c0c2004489000700c402c208120005000303003107242c4007413480310b06162104039007d0380d0301544507241c0c40900f50703034009000c0b030b0b000700c41d5942e00490103800c2c0001031800010240081c514545030b503c01e8200350000f0414002148204c40140c0ca075055018240004110202c49c685502c550405c0384201300c0384101c00c0c120044005e0400b42d480c14201a140c0ca241200107070521180c1ca0903007050110a5121030001c6801070801e03c44000c00040300710908034103c96840c0840d04900000c07030a020589200070640e0f600700040e480c5079085070010b5501203003805100c0b0440c45004224810a206170140e18000c681c0020360a880b00d003029100c1d800d004070042040751a600c1d0604004643d4030016072003804003920359440100e41404420405540b1460032074030840445082404600d0301c40b0081d0f0a04881d04180 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 725707068 1250 725705818 725705861
    0x40b04091401230c04060f020304090911090901051005090603030903010504050d14190c060b04090609030806060909010e0c070b01081b0405062101022a06070905031c0210020d 77
    0x21540046026560320700800d0003417106000c070750701074071048020031041d004a0342801d55604c80a0262048414102e440700026910700c145c50400c1404141c000c682a4000d111a02d0f00a150318400e42442c45a24810503442c0d001c039101d83c805104503005a2006402401641340a081055540c1545189440007803040b00d2060f0317120380803e05070740c0000b0000c13070044008112000212603841d0400001e41e1560b5548a0044503075030340d4810303090240c0c45200042000d05003820082e240705170041946000702c0e030800a0b040c882d60b070031095506440700110318000741d403034091011070580240d040017842440c41c480042040c0d0300c0001c0d2515041e400740141c180c030303504103401d04c0b0640e00251145038210f030712181285900913030454506a08070b540c04c001418800a4403001c0c40342040300e40344030b40c0341e07483e0340002b4a0750a040c0800b940c00703001401c0c80000280341001080e52000540c04075405029503019903032103580300317100804490740340f1031066484943c440425402060b9900c400c1201060a42 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 725708318 1250 725707068 725707121
    0x1b2a010c031a0d0b041b120317250813020301060f030b0603070b190215070c031112030606030c0c060f060405090105010821090301150e0c09030606040b04091401 71
    0x502040b5025400190010300b511280e40700c1b40941110000805030495154010030140000d101240205001ba903034403840e49403250540306074542c05015a0003498803072610aa2111f80050614000c0c0303d84d14142c949640c1d09201e0703408000003410000c1d815420700300001407441e00f450b1707603c094038081e0411280503180c14040641e204d03203611548120320414007507245003010010002003456140c0c01507400d00092003510b0141e903032045940390701007480000000241507002240e890030f40750010003824401059150b03843c49010042000d845600c0000001d480100618159601848028103c0d111030601043c1d81145a2007191043d0180d464400010426001402498106d54030600039014041200d0300c0c000c403481c20b030030b500402c0041c01c10001d0180d403003d03c541c0e101c200b0140040c2080718141849100c4907100540080790b60182489801107a580101e19150407000c01c940000768100313000d005c103002d00011580580b902645c12400300d000801904490042e200d078480350488040001c = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 725709568 1250 725708318 725708329
    0x5070f0c02011b08131e26060702010c0f1106010e1e0a1b1706090709030515160503150405041103010207050c01030c0c1505070212030408040e1b2a010c031a 69
    0x41b25004940101d10008128a00910180c0c415904000492402060104034250300c1c11340300b568a040140e5540c2e054460a40e440303000c1040b00c00041c60310540200240d045d6a03a9642e0600a00050600c2940440d2101160307048488000844052020300c600d804101c080081c00f0720320107001080d500b025041c403070a200b1084010315609007241d03a080c9840b018280b110241c002070900d018413840c8000800400e0381007201c191a100b407110300086134540301d4080040f684281d4200000e215050050200d0141d006401d006080010b540001d110390b16400c0c455924620171030341e507425501c001121810700002040c0aa001031081e00c0902924070003220071221060517001c003911194242c44000409605604107540040d068411035810fa002417070100d61f0350b4030558045030303000c80001c1d003005503601c00d0b0421a404040591500200d01c1c6901411504c0c1c826061584500301c0786043c5c1c81a208420070001112011a5008100c0400310407400b0b030081c50701d40e614203148039001204915510b0306 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 725710818 1250 725709568 725709599
    0x50f25050f0c0a1805040203161e0b12071b02120a020103060509362e0b100e0a0905130b0112080f130e07031b0305070f0c02011b0813 59
    0x64000b2a040c02c40340e000b44ea00901002d4000c0ba414001d541180200c07a552490580107024407a6901740a50108000715601240c2603100040400040c81400c001407801040560710a50310304200d0300000304020b0381001000e80140080d4445041c0ca00d00611032800501482118401c0c0c8007000095103e00811129000c11a41c2540b9080381802000801c981d164000c03030150558424564058203200c507050410600d88480402e00400c0b00f5040711400114424440c43c200c002c07002c00c245c0c548a0003240c4120455040354041c4030701011203031401d80711441c5880007403210a904100900b4201e4080c04c0da00c41880d41610300d42c942c01c0010402a080e000e19841131540141034a190100d405502d01c050342001c00d9091805ea0b035201d0005220740001843d51050071a640c00240802d81d8058925101c00c1c00e0038210100b40ca00400c010703005030468481c0c04000001d080607408500c0e01d10040311030481d103440030845e8441c210412420041c1d1303680500b02a1081c4154220070ba07031140200402c0041 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 725712068 1250 725710818 725710829
    0x50d0c0516030c0e060d120e01170703020a1d0d0f2307050a06020f060726040503130608070804080c011e06060305011a030a020304020d06091a0c0a050f25050f0c0a 72
    0x220107c448030b001e00003040e00321806050005a4540e01503130700d900048101d68500c086600010140c0c03006610040e0405858017515500454418007030110308802030800c07006040c5400b000c4050b051100401c010400e01180c0c0a00e10845100740c000191181d04611505008070340c035140201e101400401d20501c0000344000415441c0c0d11080103d0359100614034113001500c1140c20013402007040e6046c01d104902403401950740342620744004400c00c0035548008100240c41c000d1003511640002156082900b00f42c0b200d80341d440600740c1a00410312202e00000341a40420400c10008042c0c10120407681562000c000903aaa801907032500150510804105070b41040041e503c2c038030f030b035001e980c01a00260902d014201540d03241e0b0221031380d10f0415605440811500505a200c001030194407001e44030100b800d05071022005803050041d80c60b100408800441c600000c443d50102c003480860948041001d120782c01d0409a84942c0c01c1d01540f12907029903198001c517800d10030242e104484 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 725713318 1250 725712068 725712083
    0x140a03120c081308071703010f05060304050a060c03060807030b010807080c0907120605060f09040b04021e0915070c030507090603020a090507120e28050d0c0516030c0e060d 76
    0x6550f16042d801402c001c88007103d15210070b00a010116010151140c061201001c0d01c035034a50504a0080d004e010075440b281c4596420020000001d00100784840034a030f0190b004105440b5880041d006051540c1040e60284a00c00000041c8140049901d04a505500940314641d440b42005511141801c4038240c101d08043c02241855204a080440343d803008000040c3c0f542c1c03a4000500039038810941011070050118581c140f92600d880b6501e840c0600f00c800314500314241c4003041c640d21861900c03295810b000701d41030f50240c5844c0741508018100305500b0799200758618050420841070300064a0364460000046102c0781c041c4205070649070003c004040700d900d03044605020f800010444010482d10104156201c04503006100c000e58280019040d92819840c0302e0342c03e1600801041c9140c9407690000010400119600301e002e20149007515810507d41401460030b441c11469002d4441d591000200340301007c4502c00c00e8800c0c0603000c08a907160f013820800c042030710040140520 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 725714568 1250 725713318 725713321
    0x30b0f040c17030f04090f0b2b06021303030f080a051003060e0f011b020120070f0201051b010203040605070c0302070b160f0b0a1104081f09140a03120c08 68
    0x404481642c6000b103004100c0c0e14082e08480402895003050b0b002e00000b985402c6c04404565450040194402c81505c1206d51a5000c2101d0496a051605c134004900310030075000c018000c20f5012207115044805111640765520b2500500c0480c03d4000000042c96100204084000300d0003968014641c003207215500d5801c50b1070304401050000380e141d4091090965600c5038041c203014000200300028400306030380c038020001a0a490044001c00030300c00d00c540f41a010010b132402a13411440e040f203013500319042940b005035118852091109042480c0850f058070058054009622403440f82600344055240e01b481580c9031501d892008015801082040c4210100e400203807002140c04800c02d035541050780c845a584c020001c0c410b03280000c0805c10002006154092003c11140c112000c1e46050b14142c3d00c04e85402c0b800c404d080315840b03076500040e81500650082812140c10900f02e500e4849684c1000313640c1c22403510100c2c00320f00f616184505500c01446a1b01c0319030342581b41c8628030f = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 725715818 1250 725714568 725714579
    0x40501090f0b0a0e120f0a031412010b070201030b03160f0f06021f0b131413020310090f240b030d051b1227030109030512130615030b0f040c 62
    0xc4c41c03008102140c00050150030103103400c0040007000743e80c07070400c0b0241a5a808604000b050001d8510080d10604e600b00001c441c1000b400000d50704503031102d99040d071540401e10048021703041c20140c01d079141c07081da0700100c443e903080c648600455038105040c04a455540f0028009070742184a08000750308038108c0c03034100c00441c0c3c0c0d000070404240540003c2c25480c0b00c000a07020411212288840703950303000381d450710800e050166604212940700a030003d4800b94000303a5070f0b144440000c2200b6407128114010043c8a01220729102e501050040d0000c0f03103103100a40e0400000c00b0b64910b14145071030410b047c20007140c0246206401d541d0745140041c00b1001d505403103083d140d0611180310340d120344141c00032208054410152401c03d5001c06400142400e4003004055050310310a905d040c240d0300000350008104c6160009020005115031354802800704658081d04002d0019410300501c10701400fa4040014252441040c0c1580d4548034020251590309080390010300d181c0305041c05102 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 725717068 1250 725715818 725715827
    0x603060103180b130507090e0304030212070510050c01050618153007060906083103030516050c0a2303130501140a17090c0406030503040501090f0b0a 66
    0x840108142049521500343c0d01c21050b000f04880d64118074015081c48004c0003010f10406000b00351036541446038a0ba040032054a85c842d17803000910440a51000d0340b0f10341010b2081340300070f01c4003c000380300c030b910341c00c4014016912885c041003240d4a803100280141c600510038210340c655460205c64581d40341103240210000d50b403000c56210160100d001644104a43c1d54080001f01101c3c41d103280a036107040b54a8104035400c0941030001d51031081c04902e078003824665101708600a403541d1845001400341c0108a180c54200403806071044850606d501500301304c1c0545503c036500e68800101d42001c603024000c1d107824071810703040b2180c07072000b0441c01001466048116482054011602800c885c0b540d448082ca05603040b1401d0130800c615070f00a00449034010b0640300c40b92511544200040407501480f90000d031003c80f10313000c9020803404101500218202a104200881c0c403810b2503607880e0807900c1407500054481401282080b41d05601d0411141d00941c09402c086249800340da = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 725718318 1250 725717068 725717081
    0x30f0a020a02030702030a1b060903081c0e10050f06031f09030e0612061311070f0327090b04020a17191b0f09050f0906031c0504090e07050603060103 66
    0x1811440213000f40b9001d65810f224101101c5e00c62010071019220401c003114400e0965031000003406000041000480c075403401b01c560452140c0e040300f40c00420510381c40006c4c002c003107509031217118118020130458000d9005c6070203600b184000710865680c020425503179540e40004240130210285003403001a81580002000501c281009800314201c40003162141e00096038114044021106004483c14150004510305031400310901c6500f00d803c0d2000d07500d20440c1c10040500d4050134540042c075200d0401d404141c2908000ea241d189545108181d0494030b81c0100c002661600d01c1c0044c1c01d14152089402002907515210403440c000021094512802030403a4400d4440b0301c00140e10340038911841690003290302c0f05803004d034551600146001071078036400c002d2180d421014082982c459083c101544000c4a001d82e0f00d030348045c0800d00700200031440c0450464000c4242007002d42003000350007901c1d43c6200400102c00140459030b0713502018419950844001c10103d02e940d48030b42c2101 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 725719424 1106 725718318 725718337
    0x102031911090f0d0309080f03130b0702012c1f02160f1403190f050d0c080f031f03080d150506030f06030a0c0e0f0c030f0a02 56
    0x260620215100c02d84c860071100220108152140004002500b400390541d51000042e0400300d9580c0c0005c0c1c40303100e41c40300e2040040380c0305007003c0c01d44400c1c640580d10844441c0c0ba42c03400007400e142d00010360a03041500e03811441652034901c4c41c20000e88681080c0b640000101070001c0c249a01e80c1040e803152070200200700701c4640300c1d0268006694810b200d80201d02c18010020385001c0490303039407000c038600a264420511141038032300003149008a094a0708104c4541d001c5408000e180300041841c40203214038030343d1000c02c00c0559805400140f19016400c150403010480003140d6004442072100081e106095504a003d02241c81288000b8107042c54204800030b4414000248214003640404000032400d54007003201c1c00c517250f040125001410380317420700002c544c0003c0360003450b0f0310b49600205086001500c00c480c0b2038103542400043c0d946405283c1d0020f0350100704e00 = true := by decide +kernel

theorem cover : BRFrame.Cov 725539568 725719424 := by
  have h0 := BRFrame.cov_init 725539568
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725539568 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725539568 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725539568 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725539568 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725539568 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725539568 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725539568 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725539568 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725539568 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725539568 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725539568 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725539568 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725539568 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725539568 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725539568 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725539568 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725539568 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725539568 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725539568 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725539568 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725539568 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725539568 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725539568 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725539568 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725539568 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725539568 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725539568 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725539568 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725539568 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725539568 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725539568 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725539568 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725539568 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725539568 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725539568 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725539568 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725539568 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725539568 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725539568 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725539568 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725539568 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725539568 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725539568 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725539568 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725539568 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725539568 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725539568 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725539568 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725539568 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725539568 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725539568 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725539568 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725539568 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725539568 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725539568 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725539568 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725539568 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725539568 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725539568 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725539568 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725539568 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725539568 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725539568 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725539568 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725539568 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725539568 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725539568 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725539568 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725539568 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725539568 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725539568 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725539568 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725539568 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725539568 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725539568 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725539568 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725539568 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725539568 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725539568 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725539568 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725539568 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725539568 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725539568 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725539568 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725539568 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725539568 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725539568 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725539568 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725539568 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725539568 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725539568 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725539568 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725539568 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725539568 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725539568 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725539568 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725539568 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725539568 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725539568 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725539568 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725539568 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725539568 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725539568 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725539568 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725539568 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725539568 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725539568 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725539568 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725539568 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725539568 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725539568 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725539568 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725539568 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725539568 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725539568 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725539568 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725539568 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725539568 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725539568 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725539568 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725539568 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725539568 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725539568 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725539568 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725539568 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725539568 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725539568 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725539568 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725539568 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725539568 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725539568 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725539568 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725539568 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725539568 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725539568 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725539568 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725539568 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725539568 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725539568 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725539568 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725539568 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725539568 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725539568 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 725539568 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 725539568 ≤ n) (h2 : n < 725719424) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
