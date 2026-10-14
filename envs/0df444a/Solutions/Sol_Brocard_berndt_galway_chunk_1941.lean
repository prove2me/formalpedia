-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1941
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T05:14:21.157194+00:00
-- url     : https://prove2.me/submissions/a99e504c-14f8-463b-90f2-ca6a556ea3ce

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 348920863 ≤ n < 349100719 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 348922113 1250 348920863 348920917
    0x10207050913020d020f030d110f1c080c1317120408070b0c0307292d0a0f0507270602060408130545160203041a 50
    0x22502c10700b00300c020000716451550900a00080c6000226000b5826500205590b50184841c460148440d81c9040103c1c0d03446001600e80f00701c2c40580182500241410f44801c1c0044031002c00e0750000341000d60058543c0f0501b291588101c242d1100c1d9840303c06004981c0032280410f1511800c9140100d40a0404a492801c0644902d11400840c0d0340605400c00c000402d0714094581080e0303a03003d407420041aa221a1040e1303019441501e2140400001c01c03070240010400070380c00c080034030700c9030300d134003020701e150300f8103483e80c04640c803184008100003d1401c00160845183c5200088041c0421709080d200501b0301e04107040820740e105085002c50041c0143c09540804803400e03a4002d21054483c1d031035400680e4041e12140c80351304036421022515890f501c80144140c440c916041240c11810a41c00034415032201c240a440b04118812008881814070700d140c000c01808420a580c1d06c0d40202079217144101d50002082040d164803201c480000b040241440384006101e00008250320202 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 348923363 1250 348922113 348922129
    0x8163201150f1203030f050a09030f02030c0601170c0d050f0c0103021201090917040807030b07050304020a180e15010807170304030f0c0e1510020d0e040e031b070501020705 76
    0x61201240400a0100100d0500d004030f0818540a81000110601c00001d1381007a100c08664180005071900c012004044c0e2141da1003c40c803425101440c106446040e5240d120321042c0b2a075501c03c2068619581003842c14043c100410310024500c0032101e4091820341d459506912003100580640880b920303c030750090003100c00a180d01c0e0307a482c0c0c2c2c40e82016403d500070090b00b04162041e400205814600d446041c0090010b00b0481009115a070b20f1460150107188009001c801000360a00c140801038450301e008600340d039001c0030048103000c208110304000700120030442c0054401c04507040521041ca001c028103a17007851007a115016156500f000781c0340c91100e0b6030702c40f56001b040200085003400d0500c2013414440c441c05c11240d0754401200c0c1e4499010348425424003a90f141c1032240d032824628000d15400c09002030410b440c0c19800280003443c00c54480341c080c2c2d8a40b1081c200000d0103004039003000301821090304461804103205540e44003140180c0b405803081030303004a007924100745 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 348924613 1250 348923363 348923369
    0x5160501091a030702030c03040308030603010f02070f242c0102030421030b09040506060a090e0309040f020c160608010b040e070e010e0405011217070816320115 71
    0xc0da20908001d0b08080896000a029400f10f000034001d010b02110288010402903019441654803410300a00709421900c0051a000c40c151040015900240031201c020442c0381c0c00020385002106004504801c910803042003000541c64140020310b103c0d091548440b5128911020701c040c5403035020202c3c200d104c10707130b40030b010780480841d0b00d904404503070000e14a80045140115030a5420720204010503c152000c50301c64100204001c600e04201a43d4002001e80303900600540b50750901c0503407a84030b40486c460140da00c603103c4850b0300b02941c0458070103404a0040350102d41409503a2800b42c00c01d405140b0001d40801b0000540c0a20722082e941a0303442004521625114298107440c135a03a100a954144220a107051003207075181d20425000700040c0329602d004a080f0719140807121300401e40680010340a00184010800c09001da0311660f07041524400d40c01e9080c00c1041100030081a21820300442c65020091001d00051070143c0302104002408140703a040c1c55403419080b0781c0 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 348925863 1250 348924613 348924629
    0x90501050108060709032303030703050a0f060510050d0902150301080d0c0c06051b100b151207210203160e0d050c13060e040c0609060f0509041a0303070516050109 72
    0x10086c00411000444078050001c0005640707000c00c40003440300d055420407290503010036034800070450414480e001c4d403080300900d01c0040082038109000a0039030b1801e00342c0c002c00c201d404154422070034103580c07120005507002014040f0b0a01c1d000c40003c5503034400d01826070075000b4004280c0d8864001c0424009240d03100310146400c034100801120b00382c04c1200310034000100104040c01d0342c442803101e50581524448040368403081441031000310704410b103071040d441c50100000c404980e13460440a400401e14070703001080720000492120180b0744042d803245018400024090305551101d0030f110081140d4480145100c61401080720120101201800e95003109002180e030340390451050300e2020403103000140039500d400c1788041c2e0540446003101c1124414a0601c1040c0e0045601c40c0280b40710b140c40e902c0c110000070010940d00901a08601484c0c440c012440621301844083d10032041c00341c101c94654100d810072507a02d5052801040c81051800c0021405c1e504c07400364041565525 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 348927113 1250 348925863 348925877
    0x110f01110304121a07170705040806160507080c06060a09020c030306101808250503030d181a0f070e060a0e0307120c0306060f360f0905010501080607 66
    0xb203900c40c0403110000100c0d1104e0719102080b240c41420059640944803558502070300031750701050001d0340600502a030003031000078070081040c20b02c00203415501030b10074002d042c150703580703180305541d90301880b2030050582c440464003084802c1c0c00140c00c0c0c0b05180c120b030b041c0402c56480360804100d01c16141c1042c3d481c1c20401c00900182000000c00404c0c60080c80c0c401428603c450f11400c56950613004194950401295080c610961030707220700d050429030307544480007442d0000007a542d2050440d92107900740c039882d4840c42071407540b156103203031608144500c03501c211144070403030900310880d4201200d142c0c030320100754180e02c100928603807004040c1c0024542611001c09650307248059403c40d40c0351054400114080d080000010b41861007071112041007420344c5010419212aa00003c85d404107103402004000000c1008087d41081d45d0355420442d6034103001e00540a10f9540c03849a007078205154488800c5041d13118030440f078011030003080141d0f00c03001b01540398241500c25400040c06 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 348928363 1250 348927113 348927119
    0xc030f150117071e030902091005090118151401030c030903052703010f0e151b070318080f10091a07020a2001030c020c01080403200a110f01110304 65
    0x422a00b8030b820442509101c007070752080501008184c0c0c9012601c02c0000e4842045008604010490315048004100945411410940801e051860506c1641558400e00b2050003a800d103aa0110090b02020540c85400986411b02001044070340045180013074985100b0000580c0b2a12400044070750582e90b6621b000d1428880247e4442074074502a0780303611071217008455079800d20400d54207512011010510503075a42d881c904082c0207128402d0650040c0041000481c502401307401c890000352809500d400e0716050403281030741140b00860308054214004104003a00048a079440705100c3d0407600e81aa200d0000c0003502c045040081040f000b51108200c0440300c0342207154000c01500c115606180742e500d80740b10070342e62009011500c0f4420340360344c0d0403564503010315081415180018004921650002030128030b00410103000c01c0404180400900b062040c4822101a208102c469a05a50411042d00384041454601c915800a0600c0300355003d80140391400d0702c4000a10b042501e = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 348929613 1250 348928363 348928397
    0x105121b0103020a1803060903110a1a0a0219020a051b010507020d03140a0503040c06360f03140f0a08070b0c1b0f0105180a02041805060c030f1501 65
    0x400d9040b0380c05e103d07015005102810901190301c00840c050400450b01604034240a03003840f41120825416401800508010600c41c40070300510f10218042180e136a510204160300902580015100e804a12a0725140440e4005a03c41f40203004034140c9080034500e0b08004c903a154040b001c01e0110348180802405881e04450902c9040d000e801c050a0070a648103a002c0250311991010021440c0030082c80305200ca10a80e9001038072042c1040080300030354101c074902c000c9071600f02c42544000341200d080540454030201c001441d038207140e16103040d26071800c100e20400000580005115000f040c0d00030500029003c1403050300300c0721552400e0721a0b22500c0b210304000f4221454048100055048000700100c1c411985036041e014181048201e20340e142035900242460888a44c22400d03203c1120780445d0641c81e03030307604171000203440360001001744040316507901c003030007034041c1504002c00d800a1100840c0b14450384115801c1c107907070b070903021040a401140114001040d142820024032 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 348930863 1250 348929613 348929617
    0xf12030e1c0c1502280903020a0902130515070312050609130c081905060a0603020906060d0f05070302040f0f080d080c16060e01110705030724020a080105121b010302 73
    0x70340503140c501c0c0c2d10120441c21030140e03400a2020090800c403a0344407820340740c5c111002007050a00e0318014081030301d95000561020003601400c81c5079030340080e41e8080403642c1d03902d40005280250064081e03040801702c003029900110015004201410f83e15412441503101d06845104000c040045680759072050752081782051104840d180c485000215040c441007180e000420301c2c4a16410b0340301e0799460500d0a201d0041c01046c08a82803040910050b030320601813550011065403a50380715020100400c01501107003542004041c0380005104013241e00d0740040c0155070061034001100d99544c44256000740d0240b2500700c1c0c2c0d400c12008480c5252051078002c2d00424012031250078461110702d400300e2980b440108440e269640e0820b0111000e00b030007005085100592801d041c4541c5803505030b100d01c620030f0010306000980804964a40903010144d0440b44428000c40d01c905441901070821403081c010b1610030100c101c1404400100000c2c001181c00d95404c1d9120352112110042d0065 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 348932113 1250 348930863 348930887
    0x180111030a020f0d06080a0309090b030604120c0c0b0403120f0c0204020306010917011506020a020102030906030405150a051e060f090c04050409030e0a0504020903150a090f12030e1c 80
    0x6000030008191200b00311702502d0098192040a011032074041e2901820004442d4030129149090669846181c7d40104000d0791003a0082c003100a142c055400896840382001802403a100d942400480c0c0320120401402c1502c0c0300390344010960f10155801d0f00e1001801c07a1002c001100c2d201050010300345600515044101070606040301c41c2c494a00a0031045c04501d140c20580d580e000b500301d0030800540b044020040350020348103203407035500000e45910402c0140340c0100e8000001c1001c0240c00c100c04241071000e602001d100c0d00300304000d603025240c1590b22000e000402c00b088e501e02c0c0400b80e02c650049500074040e6440e41c0c50a0705100ca6140c0040c041f580b02c03d0207110018154989001d005425482691141ca140d1030420410400c078001da00220301491041c40710107950b403000105e2800042c01501000c50f29510800044c01500c84000000d2044d10340c60b40000422405440406c0e05d000a80c4051000382c45018116542c6d00b420007009112200da4103e6400e80c0b4081c92402d400 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 348933363 1250 348932113 348932137
    0x10090b03010b06030f0402011e090b030405071502030a08060108060f0d0f0b0c04030c1a040b0f0904090317060d1110050c07030f12020a15020f07020405010608180111030a02 76
    0x2a4050b90002035480c4c00442d5614281e800000c104400c66a008080700c0c41c00c10758007180301d000642c110009001682500400d480768400001160030f1000402506008190060004d0359070703001d040380207440390041c6202602294552001c103025600420400348141d401420507401c182401007000205095060151400c003018552440883c001d00d001c580300b640e0103a85143d9503465483c00c0740b0802c0b8194080e2a9441e9203c0032415041c0d0074900300c0e0100c0c0c0c1240020780e120360701c1d074158114911858204e540d00910700f004c45810150403802244503550f102485100300c1d41c50f5400d02c0721148a0500040c46802c0024600d091460202410b01e41d515091038250f0500048902840c50000680c209031007c1128503a80c500b00031006140b404c0d8410140301500090009540d41e6180e0103001c1031203142190046103400401c4078640170340c2c0f0b43d02d40040c02407000d965641703406000f4060940710480389440c0703001d00480f02c43d014058622202403038155140717940d07220f240c030344001e4100300f0002d52 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 348934613 1250 348933363 348933371
    0x903030a021b1b0a0605090d111203031312020109030e062d070b06011e080601050702100e0901080106052409031b03010b010306060f08090123100501050310090b0301 73
    0x103404a0100181050151a2100030244403004010007003000344603031140c1c0c10046c0c00c0150407002c0d211120b540806581c8110508015504a40000e10114000380104e5680c400030003001000310010310b4a943d81030256406281526110904a00f0b0b6901810003402245003610010b040d42072a2000340300803100c41c4059050110b004003041c0c0700d0280ea105241d4401000b08040040c8541105c62680020007420081c0840c201c100e840c0e0a400601c00f402014012404002855079000303d0864a039903034002c000b00400075020001810050361031020034000c010090020491382c01c1441b03140c06a40300100600c11480c2e80c61001c1d05c1d19807130300c12510184042449425401e403000c119107085100d8458004418102c0c4405040c2190800312440381003500741a410000282c00000d40c2c08084502d183c000c031580e9a120301640940301304240c41080c60402154076407080c08642a0b14040c100c0034008029155444004540d10300060303070902841135481104010443c441d9005030346604024002003 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 348935863 1250 348934613 348934657
    0x11d011b0c09110909070504030201120b0102281b0501050414040b0d050f060601030203060a030b1b0a030e0609010e0309010c050f030a031a0306010e01050f06090a0308041d0903030a02 81
    0x90b50301803909041c0003c00030468040d0b504c2c06014a550142c1149401801c048c9140c0000340300c443c0d0b07850202640b90341c5081001d4545d20a004034460b40b006540b0150301005902d2aa200d10305003414180c581558800f22113802d949842020411070b02c0595906003018180501400caa025055a65500594809810f10a80c548440509149000794081e20408011180c0d0604200d030003807000c1d0406204204005040e0380c0c0c1003824065030381200082445a0315448204851104107040161003440402c050310420b81c1604000340c4481024165000e1341c42d541481802d031245442c031505260400c0c850100b01e940304054250005028400b221020801c0e80078050655000c10b0243e800243c03294403400b03007000c040800d47c0d80c43c4c20a03402405030798508a07168001c003a040c0180c911950003051181075545d0fa4406654450360300a003040000e81d52850241210f502610505a110a007641011480d0321100c803030520445265000d0f61555803010290710081d4041d4880e0880074600618103 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 348937113 1250 348935863 348935879
    0x1208071101171617090604030f03020c03041701141602010c030203040507090905120c03030a051e070302030a090602040902040e13030f0f09170105010f0801020403050327090a0902011d011b0c 84
    0x13502440f07130f00002e420030b03040a042c010079003100214403205040c0100820a400ca0000049404441024002c07042c00c01522281e01d001d03049a41480009042e0314080c0081c03607100300c0405c13080705019002040189900d100c02e82c141d020440c0e010f401504594020031450b01c25801c095603403842202501c061044015081041d9005107002441f1640b020041000c840c001c0e11036590402c8402d092244005070b441e0f040741d030707044d8001c0c8181d08048e00030002c100c0f99001a0090b46607294005800d5440c0c5403200030440003074000d8400c2d0604a410407002c243c00c0400b0b40710b00700b04a9003580e9500c0c1c80c000b1030034094071500403101c3e800c0108803c0502c001515050402203075440300f1502c00105141d4501405840e851045401014451348104010800a07000000311703054041a610080288030301c120b5800e804844e2100c45a4200741d1f0b210030040c010f01c0039801606018401d0700e91b0000c145940c25021409080c0d11001404240b4107803070020004140d42c500100c043c82080c4100c080d6440c1c0c064 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 348938363 1250 348937113 348937157
    0xb210106081f020f040803030a0e0d0905060316020709060308030402030c1c1101051224010f050d18080408060a200406030b040912020706031d0a170412080711011716 73
    0x1624440c01e4ad10341243d40e4100040c414040c0040070b925145000c2c0f03041600160f03141c030000d0141c0c000c4c0c4039015082c0b41c031a4000d020100007005202c03010002d0741d503607040400071644121402c91282c041d000500e403481c034140802400c40300d0100d2000c0c0003174034140e940104c0903101c0603589060140a02074400c3e964614500b2a1051110905904040d02c00d10301146001c01c969140b18144001c00d00040503850340304040d254040108600801e112100300b240610107400040041d203240350020f000f1408150004881c0d005403144d41080155081e8000d980c40940d4129104418140b820002004400e10070740050049440c02400022035003040d82d14000c400d6800c81c8001c0160b0480441048005d03014481c5004a08a02c3c1c5008e842502c1e4560298a0310b2948030024203290703004d00d82291242111050300d011302001d21402c4a51041d0b410b100c20307540c001c2c1d4400c07560081147d030804180d501c1a0000701a650355400240c0250f259903480d440d40e0b0032125446030405c4441102c01e03403030043c8104 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 348939613 1250 348938363 348938371
    0x50307050904050c180d0201050a0e0a090f0510060c080301050621040b221109090708060a0b101805011121030f010807080d05030403030b210106081f020f04080303 72
    0x82215603545c40380b03811116083e041c104ca85c2c0700e540180e0701040581d03000f800711144801141381062480c44d258000585c01c8241e6040402458500030105280ca11554001c0c1d0052245a041803049680c600b0100c83d100304902000300119030170b0004200a04128000d0840641c91041d01d41ca91408602c0e540070301c0744119011f880b008040814000c00040300d18110000303190119400c00034141325119203256001484509002d02ca040e40060a001ca0602c0040e0203030440c00d0070381d01c42d0709090031010301514450a5485c41000075000c500d080500030401d29850000e41510620120724200040d11030300090308901c5154024150340b40038442260101d02d803031000b48100240c803400c0601c44400c004005800c06c0300542d001000501983c18005000038110704149004c80d41c9596a1404074040c0c0340f000031180e0800f0a8141c089607654010403400c0c440d258020003080490355a0340c80a07540d01c001d100031400e00444c07458803111003c06400402000c5140340d100c1d0f03c1e0681e030760a06841c5600c00c40f = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 348940863 1250 348939613 348939631
    0x3081803070c050f060f1215030d0305010602060703020304030813020312040b2206050708130509090609010e0c0f0103020702040e0a030503040507080303190903180603020408280305030705090405 86
    0x1560a00191900d00d404c0c25020134155030b1641044002c00140d40d451183c040421000701041c00025a02c0400c84003d20412038040c060318407090070780f200540904401c0c005d440150064030001500030f0f21034400d0f42d12a6405075a4442c040d00d9490640c2c03902160300500b0f903010b003d0b005100d015035001000074030050001c100b03400e96039001032441071100741c001c0407007131200075440354100111a844029209400d03045030005660f16001e007030090038091254411500045284c0401c880d000c0e000c81e900780324144041c02407122920100b003a0780c4a140da03001c6180e00440d6200030600c154440c0e03020b080302c0f6201400003c2c40d08070701c0c001c179454082c41060071000640c00000300010050140310300402060010015800c5050055403000e2000c043c103100020300e0b42c1c5408900034107105118140e03d58003075038045651a910307080020701940c0540580800741c81072110001040651100c126034080f6900101122003009503030031034956201800d0102081020322004a840e41d0394410349010f14000 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 348942113 1250 348940863 348940883
    0xb0a0509040f0c0c02101205070504170705010f2102040e090f03040305030901050708090409151503081b16060c1403030618060406030b04050102030105041404050a0308180307 77
    0x80104070030b8030503149040100070308001d5940c504641250b02d00d1030165049420f904c014142c42c104454494441c5030b1640742c45d080c481804a5240c0007002001034601c805900110620500382403690b9040b68840c42c1d0024007000307010186c05204507034200e80c1c4051112880700d071001921113101603801035045601080d62880521584807410003407594003080d40c0d0080c5052a240d81c442d10f489000d50903059040c060001920420480d01d030301201c180c1500200100304a0b4203c0c2000040c0ca2500c07404103104030b150082601d111444031400c0e008403540080724070328000450030000a00303145c3e5002c0c2e41c1c0758418903030020812864070f1508400ba0500b50b45000202d4401c1c100b10450420296001c10690030801c284021901e035500c00e8ac24844910a14040c10b40721360010500518403079201400408000301800104441900110b040b00c400f01c03024440c1400a090340548450246c400401035800307200a000040d004000700c941c0184440480d0b8140280001400c1c10343e4032604c0120340170811 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 348943363 1250 348942113 348942127
    0x2120d08010509010608012601050403081504090b04021203070c060e040f0b0904020f0102030c01182310090c03020904050120090f150702150406020f0c010507020f03070b0a05 77
    0x841011140101021281d44a03113516010300580500350601840502c18100d10130054080f1341c42d16400c2c984040c034002004149001d04008180c0301c000d44000c040002440025031903031503d801410742a85e040481d07071f071141c0c40f07036403c020340310300341e000380031072901043c0702880200b443e0380600001000f040e00c50b002302c1d103a02c00800c0100d80070342107001040c0c1d10780b25048010340c83d500c000940c455410b907a030014801c00c0000603480c50080404920b0340307600b0000d596054411201c00c3c5403803648126020404600c40000e9120b6020024689103071561200b500c60845a01d00e82110f5002802014000c000380d03166000300b50317181405c03141515507070345030800e00c070f172016000b289103000c0e08640d00c205080c1111440000c2d4000141500c1c184901c088422800d080e500b25400c9a0700198020018103143d13400c20310465540d040340c4035584c054041c42240e420100350200b80b000010405039501b502c0c14100e03500304050144108100c0da0540304041c0e002c41d119101c4c00040024201c59100d083d141c6c54 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 348944613 1250 348943363 348943367
    0x170a08010e0f040b060d0f1e05011a0d0f0c0f0303080f06040c050306120c0303030a060518040c051302092e1e03020306030a1704180b090604020f0702120d 68
    0xa02420105508074288200401300e0140004980c1000c030441c2c580c0b603028605e05000303039130201100c40640307030107003500106181040c410342e41894148520024000b003030501c84180e01c1c03849015000c5812115000041c00041d21046009000d5071003004143d074130300d80300c000d0174105590303a4000300c011880711028004801100d00c0b20305c0c0d002000310342c00e020030508404000c1031804003404c0c4078054242d2860b040000f01003403041e072181c4580a811241c991429803052009882107203c0c43e800355040040c010000750b480c00065100707039004078000d040b00b4070b06000e01640240c40c0c00d1a4040c145e0030300c1002019600e1400e48000e100c448042941d8600c011014520072415280060b014403544c490080b0100306007202c200b007040680d050050b10380c2e13501c1c404a4180b41070154024a02c001400c01d80c0c1c140b41100000e80140c2d00400b0512030b642c15208902c0c0200e400010384146e0010581001a80d5498540c0040000c803107203002060404000b40c1c0403801b40c0c0c425030ba80010f203800c4482d02c192042e07 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 348945863 1250 348944613 348944639
    0x706020a170114030d05030a090b0f1b3103061d120403050c060315060c030705100b220f022b020702060711150427150e04170a0801 58
    0x810b0601000e000c0d10f082c40c00107503036000d156911070f0a02c2008000140000c0b4a50f20005210703400034002e480c0303440c008108240c0c0c02c6045800e00c038800b403070384640c40b490101c1c80c060f0b6025800714100442c00b85030b43e02514180015180c142c4c00d80708040b04011000810f240924900c0f040601c0840d030b003400c03c0300c2d030950804500610828440d0814042000030580001d0102011501541c100d5625181c03540c40001034101191010741199001404004a907000401480722501603015601008281122581034030500400150710800c240107811401070090081d030070703030a07101c0000581c4c00101e09030b041c160b801c138860090f002111a040c2c4104041005c0031895101d5020744214644072456000480d10301800001419000d400200300c003042d03c407080305464808030140825191a074a010050400c405c4501c1d04180c40c4d0b10041c0d00c80341403468001c10030303400080380c3c1404000d07040c00c03d00c00c04180001c205a074400688200d00380d6056481e030051141605558608460350306105404541c8 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 348947113 1250 348945863 348945869
    0x40609060e012906091c02040603031107050108040f060507020f06010902040603050f010f0e0a090209040c061d1005090307090c09080712020f0103240e19060e07050306060706020a1701 81
    0x68001d0b464190f0050351010102c1e40110301c00c88502c0c0d00036513410410540c4010400c0002d4000d4034040001c014143c00401c2c141000e200305044400ca0350f102c0307004550407407043d240104240804801440058001c0e0803230350f8814003e00c1102c03036003200422828500007081c1d0104817955400242882002d61601a2984c40320080c205441c46502d40010350076034204902c2010300340c205030340100c0d020302080c0e045a604242c008012000604090030400c2036030070144200d2001c0f84460100101e12400890340c802c001c0b00c01441907101414040040d20564040e000050b418040c99101044445040c841c4400c0740001c0e0359240095800c202801d1f15146464110f0a2a41d0740c4094110050f6500c0d07101e41d52041082c600070442ca182c000a40c00100e0001e0311010440c0c0d4040404502c0c0c2004001a510a07589014641190300105801c44221401e90107440c40c5070840c080051006c5014200554009501802480c544106a2660400c1b40c1103201c1c1007000071005044501c5c00428102940c0c05 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 348948363 1250 348947113 348947171
    0xc0218011a1207140f0a09051c050a060f1104090c1713060b040209060c0a020a12030815060f04030b1005101e030605030f01050405060708070c0803040609060e01 71
    0x35001080c0c41c40c030306285008240030b00300030b101440b032640c0ea00c1541c144c85003d424020303441d444040020007d01419024043d890003a8940b41011450202d0180088840c541041c0602030001d11074030760001a10340341c071a00528076160380080c040e0300548401000100407070100042e4401e80c0c800024118000c41c5030104c3c1031003075201805881d00e422041100026072041e030028409250402007000b80c000d0a03007072948401d01282d01c03000c81a01245802c1d16a108540410700c0c1501c1744200d440d0386580301310190009164400146400602188a20356403a004007480c1c2000c1440d054040e856100307410403070741c0c80c0f40c1c501804403198000c075103034029040840b459003c090031204018003100c0d80d02d40c0340d4010140c5955a60b80755010394066009803d000d01a6445040f003046001d01030321081c0e8046a040c81903400241445201c0c000c058001c1c04141d84010740ca09654132900780c190005001940d599595011090026000c3d20404450030558030020406061885114810140c90008105 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 348949613 1250 348948363 348948367
    0xf10060206010b0c07050405010312080714043008071406131101030e0f0705010219050706050a050f0403140c0406080319021609050f090c1f0c0218011a 67
    0x880e004520755040d81d41c40c07206036032190b6410080da868003249501c00c940280c5068008002d01c850246015072006440d110b00700e044d21000021107010051201201c0420028081440310b518a81d100b002c0c2d03201c800410180301406000305161142d200b010440394500c1c006100820000c141403517141911704600982500e140c030491080a0729030000707005044855449044203d0380c041c6d07010804103401401101e41c451985007585a403540d2501426015103c0c2d40e420a01072a004480700720303c01d500201401106142c40804d450a420045010041c041c0c107100482c0c01030a104040c2c4000c500650b505c0042d000c0c0760801c107007412001c0120900440c00c0130f9060040344000000c68480600204030110650041c680803030034103c02c542c20031041c01c3d8482c0001744c10445034200724004c01128103180c0040d11043c15041c0d54180084080c2e420600f2404c1c554000941400c01700d280101c14101740271624402d60001b4511001d40c020341900144100041c0310082c0800c101940317981403485058 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 348950863 1250 348949613 348949619
    0x10090e070e040905060103061e0501180203100b07060501090b181602031c0605101b02010507060612060515030307050c060901020102070b070e10080610110304080d0201050f10 77
    0x444040018080418029000d03041095030b10b4660140740c0386500281964a196124900035014000c440c523a402030301055140c1c0720840540b403043c01e040300d2589400d48100340c010341000d00a50002003001e040c410a040380090044180001091111b10a80000505604060303090044481003003940d80111203602e200343c250a036088529402c0000180344415000090320200e2541c490b0307074031011094001c54810032403040e20350408010b9901c2200c1c41c13840158044412144195281d910819214001101a0155000754010983d01e4060171010a0050700d5094054110542d40c030204c0c0c070180d40d1020010380402c14001340314a90380c11809545070458a80707803e60340700110028540b04190000301161243e000b54119a02c00394400640d914a1401c1000a025003c06245c00c6010b4180d00380c01000983c840c081c0c003442004000c1c087c00100a50940440b4030065014100c0c0c0144820003001c51040c1c0100044110018507030300210720f514002d524550340310006002e918a10703912150034 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 348952113 1250 348950863 348950879
    0x40f0c0e0406061d13140705191a0f071b0306020c0d02070905010f1a0c0610031502040e010b21150f090c04060f05130b03040b090f030a051305090c091009 68
    0x101c582e286c0010100343c1300102582d10a0625280303a20480d1701092810000d000543c100c080d800c01c403403018600840f030020022048200d840394207118030001c0410004000049c40018101203190f0080190340d020548a60b079440881e031040c1110310075940070312806403031036604002d230b040508601d6070706000e1075140404454440d0a10300940b02d24410001d031406a00540b58240d07006d407911001100d0700f078245840045220b020a000c140d6101e0078120b800d01c2e0042d12130080714200c0342e0ba0100070203242e1034a5441485034008284042d501101c0303031381402c1108400380b5400e0103007002c083c0d0785815188400801c07280c40c000b41411406081c0000400400c40d04031016a0b04580f41c6080c07900c2c03091140300713088031503215000701a0781d2a488100086410000c3c0c1014612a511619881c0c00ca51a42261103984201c881d030840c40681c0100808181288240b01510741c101c0790081700c3e0401602c0703a000900d21603003203034800450301000c2140d548a20f0603002c0511480101d0400c00b20643c282040c0b = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 348953363 1250 348952113 348952141
    0x80d0207030507290304260f12060d1704051c0c12020109080d020c040b0402120103110607080d020c07050907080a02070f022e0207050603040f0c0e0406061d 69
    0xc0042c3c9444c02004541006500410006400809007080d540d0b441c1600d4103100d2850001900740002c510121000300d400d03d0002124a560380f040740c001d0401d020300c9080d42c04408002d01254002d154010380c2c100080c141703d8000c111407203200090381ca0b1b0b802c02c1c0a1150118145500105c142c4000c501c034400b1030340040c102c20903120318a5108001481c40e000580d812086079000c0301d200c1c440c002000b1044e0340c0c08a81980b82890849050044400150400099000710749041d601d987c0390400403c000365403e1800100510042e02c4103040101c42d40b00e01129412640d405900d15800040e20700c0312600511101e000f4000031100c84020741000c880c0281003c0004103039140b034650000751401480880308031000a0766008284031825040c00c0340381c003460100400c2d540b803035154a01140f40d002e8004521201521800b40c4030a003156140d4680408820040c0c105580c155050100812020311003006903101d1406a40701140841c5001c2c10b242144c40c507802c0b864494403044c400d00c8208518019 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 348954613 1250 348953363 348953369
    0x15010c0c0b0c011503052103160807120f14090105040b0f0601021204060f0e03060c1210050414040b090304060f110c27150d152301080d0207030507 65
    0x2010302e4607101c0c8464080d0040690450600005044803800000c1060010b449000081d060810301422003000002403102c1c0000d888401c01036802c800d0482c10603104940184e4404018640072407a40c25802074401160701024580c4800c54513501c4060036000e82005260704258050f008000c1c5203043d80f16007121040c050700548520407800d002c030b0196882007021516500303091150540c5c990303803001c02800752800c0b01424408600c003002d90044528010a14070f2045003854840e23490003801c0d000400303200400800a08403640c400d1404585a111031003083e96400300405485160300701030034803165001005080c43d20740e40c0100024011103902004c140001c5119051120003481109542424400c1c040f40d095042509600200d0825001c10b103105510000311100324459181c4011200b5800100b1550a4001d0600c5840381c1c000380014951440380c11700c0800c0003584d100e050001c848907a0490203e0300e0010310038401884415024414107000072000c0c0018038000e8a5965032035100e080031300c = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 348955863 1250 348954613 348954629
    0x20303040b07090305072709050316080706050c2a1902010302120703020a03110f07030e06040305010e0c0f01080f07031113080a030f05070b06090402040b1815010c0c 73
    0x41c0100704118021000c05000d158001c00f5520240c1c3c4a83d04800f030b0510030300210080141d40014191070609a10070503d4098010014601d490641c01d101d9650403901c22088a050004200c6000891130a01c0b98a01402c002401503a488c0b48403500d055124480702e00c4c1024a0036004071a0320381e6403000030900e032029400500d00800007140c0c00107034000d000da0102110718010040c00c00414640c154010182e9003140c0d1010008200700c000241c0c210b00600c080140300c40d0041112038042801107070f0102c0c0706003000f41698641501e035a6114296806101004083d03030108205038803d182c240068580b03e142071074001c1c610704e0038030540790f100f4401420b590305055454801c01100382c44001103608540760314014171902c83e9a4580c4940c0c0b0700903450140d00094100700b644060500c00d900312415940c022510140644651040088148018200b00d038010b035108066842a01c4005406084600660381e41401d454961518400140703140e030440c3c10003500c0c0305100c2c002040ca21400094881d88 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 348957113 1250 348955863 348955883
    0x60b030c011407241409060a140a09020d0c030507030c05040b010c0b060a1e050415080a080a0221030421171803030112140a0305040b0c0c040e0c0102071502030304 72
    0x104c200e400c000160003000580c01d02000f260b2407a030998400d402032030071108603080c0c1d80d28413000301d00f2605007071500d40380030f400a008240782100702d4002050417400204020107400d81d43d52900200610b17640110340035008290104184040e088402d0001c1005031030a0203503c000c02e0000f40340f00141c4400401c0c4070682400302c2c1d400c1d203561525001402c100b21081d90003011a08040903400d0741403140d68811410900300d200e0084200b00854201c0b4100c200401030b6602a5448000c280c101500350030844c458440c03c2e4094001c0303400c9034080da4610401140e600e0402d428518918180400b000a10305403101c3c0c403017202640507160103442e100c485445609a02d4048c480356441141d41c441a01600c404400420030046c1c05000111040c42060032030360401c0d1005039281c45a000d0140034000c11414402004848801c000602100c000c03601036404060020f40020708540e801c0d152801698041000e0001950301042000c026000e4000f580781c190001d81402940c910001b04000d0018600f = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 348958363 1250 348957113 348957143
    0x20c0609130908030c0702040e2404030201021e0306010e0d0b070509060d0207030503061c082b15051212090f0607060f0524090c16020607060b030c011407 68
    0x7640c03110340140d0b0f120720440d07036a0420b00c101e01c3c015080880e05a2086103054410f034015140000c0601000320843e000c00600c051090f46001c004200400a809554003044100c0443c8d0b90300008802c1e1805d01140c82d51a81840c1c80014094603003101402d002d0703002c81c074100000c40d0901c10101d9100700c0c0ca140c01030759200c0c420040303085070040075503e400b0540046421810182c001015501c9004260b0310320300021140d0046010249015a020781008800c20169040300c0d21003641c0183c140c0030360252601646080248411115200c002d00c3c00040040024880c03441c082c10017814003100400100303000b030700010283c1c1c01c038420680228401e1030850400c807565182d1405840f402d641100f4108042100100c00c1e00203040111800c02c0ad403c440d84249218000c000307019070718040054101c03502c66a492070704803542e5101a140e07259650410149034010780c0ca000062921620a59001c81d030607100000341407402c0c805d0190f45040c041d042401c0c51804c8551000e850170541c00500320681068 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 348959613 1250 348958363 348958399
    0x60f0c0a030902030a050309042a05030709210b0c040506160507260d03050f15280810020403050d030903030213031b05031c0c110307060906030c020c0609 68
    0x641c0b1030009401d80a200780303d805001000c4058495104142d905110000a403055910005d03180407007030080340010419901a103104401841e88079203a170809080c510b46900c03105444007808409100c0483c118410b000c01c00005018030b039045034464000d1420720703052200065803405101d69440646904070220b800b40201000802c00901403840c0180410b07480c1910300ea84041c20385251000f91041890305000e051083c41414480c00d001130264030180c982d50a68128480700c1c881003a4032405060101a07443c5080700c010b01c6560800135004003007813601103081e0608007440b400c0b010180c41440100007060f00800d0410640c01c042c540024440c4407803405800a005501c51010240410ba01c084208182d490010440340c0c42c030f8004111072036560080541e00c19085100175800123416208010490284207100281071141010810340c40035440420b20f810042e41c8008005620003800f00300080e003510580f240388005101a00700d0a141c0400700f101446000c0b14580110043c4038002e507000 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 348960863 1250 348959613 348959621
    0xb1c110607140a0309080703020901030209090f1213050915060c070f0303030e100506011d030a02030d031d030a14090418080a0207061106040f1502041214060f0c0a03 73
    0xb50b00001d52002c1401c4003144030340d129151542180802e49030700c8003061540000a10b04100c80e801000c0f000c10380c0c215402d0221643d00601129054031a40c52040d444580074410407650210440325641c99500d00305a544c3c0c0b00713901b984668080c0c4003110520403003100080d5120b0040340144c80c403664a1401c80340349450000b19030f10412410300400004020194123403c040d100000c404c0c200e550468102414000701c0d0002d43e0f810303011034280681040b2002c0180c00c40c0c2c2c9a504003c058918140c0160040381c10200409440000207070384200e0070081a010481d40580c50171444000c504204040802030071003200908818041d50001c201c0045a40e00c6411030350035500c60158044c0040300c546810070341e0b07801000803503016019851000c5801d501c120810030040d26030400800b05601c0303607110005800b4080e0001c2c1c40c100801e40d904072100c2c009000500080074485d840c032064070490304010200e03004005a402c5c050300103005110040e08095070680d00524011086903595203c01d50540c020 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 348962113 1250 348960863 348960877
    0x1020a1d1e181e0f070915050c070909020405100b09040b041803080411011115040812040f051b010804022b03110c01030c090902160605040b0702010b1c1106 69
    0x1e03004402044003e2100a001480c0740c200b0150301c004980701c24161006076207046401e8800608480c1040200908078000380d48240414204a0315110480702610b0401c24180c0140c200319071918104011400d00384035241e8050300070008403424504041e02414648210410584540d480d000520750381e595507813010001508181780c200b0005c84918019090800840d019a048549080348003180d5000b84180300448442d60f014250785003400c80c0c0e8108210028005a500c10014815042610341c1c07449810300485c0601000c1810b00303851704d041d9140c460b00b9803041c138051102c43c20400060740c01004460300950304484844041d102108040c60b8000a8806900200c00408005041c07540090724481d00c2c440c80015101c000d8242401541503034000c020300d0000624000080001d41142d0f40946410048540b19060f11002030700c0b131328295202a60256075220101043c0201507030240310380c03514094140c464a410a030100e8607020b4410300c0d205c0241c20031410100e090190760b1124201d17041 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 348963363 1250 348962113 348962149
    0x9020306011e12050c1206070f030203100902040303021b0402090904064109030909010303110c03010606032705070909050f031209070b03090601061115010801020a1d1e 74
    0x10381c05160070013607543c1000c106520302842c443c40d40014001d002044240c4101d04c2c07900d50504000c03081d40101c0082d80010100c0c015126081c4020940e1062800141300850003603004040714404000d0120340b100c00a00e840e031040c4d10406c0502610388903c8030107a842600001d000515580807011850410a044050b11714104c4201a40c5400382c400d05848881f0090304410003032a03501d110302c1654a10541c00c00340c1c2d02ca85804010400030303200342549540d001c2020151401d003450080840c0c00d554031500640c0100c0d403146541010300002400c40b050350303010610200c02d004c2c2d40b52070341070712807806010701e001840d160500a030510008101d5400c404100900b10380c0d981400803036038803102005856101c601d0080302c038005040000030040e07a005c0c03601c0030050310407a481c0140c282c8500b40200880c3e6520301841404110400e0044111802049500c00141c3d8840c407060f002440c41e129054690740d02460610b200340a40c503452034100700c404070079141c0114414220002000e48440059450f6 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 348964613 1250 348963363 348963389
    0xd08010609090207261e04031703041703040308040b0c070c0603020a0917010c02060f070e190e090106050f060a0c080f090904140d09060e1012020c010203150409020306011e 76
    0x2c80301828800815011000c08906c0c1e0082510000e0040144507d12010340200c2030f01c040d180a181c4203000a5030080d01c2800b500340c80d1818030440395400e03001200c01740c02280b4070030200814810312421080e404a60b100c54180340001c40c2d0f0f60320b960000140550340400d540402d076440b0a901408a00019080c01a40440c20515501c3c09501800b03050060344018000c1902240e0a00082920310f409007455440b052044001042031042c070100b0f4030400681c070848024002094052006000e009003540c0c40086101801c02d001d12520354030340720307050380100340c100210ba16040d48094100100340d80180590385e00e40e00c0320560340082c090026400d90040780c0c20184000c00c95495200c0800e034040303000b0b460b0000c20200c02550620002d00c581404190310b403888071004d28000d898401452820308100d100200d20b0341c184801c0382c009804100ca269400000d1168060b400070394002420f10407201132103207103c5a030200780c88020601c1580200783e0486c0c40900e1110b0086001d02c094150b40d20303549 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 348965863 1250 348964613 348964673
    0xe1603060830280201061d040218060a0902030603010605060a180b040302060f030601030e0304090e0c100905060315030d030f1505151b0f030702030d08010609090207 73
    0x61400505038038201c0e919002c070303079903011040150054490701211160044141071540c81110390358100306110004655850340c0100d041e402051001e002250703c000404d1003032070240b05000c50301e500300e215450043c010f40200602a92928000d0068031100c440160303c1c1d49621000c04e0150000342c00c216844107000c29800d20386680000c051016080500d070f410310300c9a03210b010409a1150340006900641304103c5000007013060002160818811b141c00038503549c00d000850b086401542103044116207498116000b92001c000406096804803480007000da01c418006d0000c0f5150b205050240a002c00001d012500e9160045040380d0090203440c0d10310706841c001002081c5440b103031079441d450031446000d416034030380f545001d4801c061b11b041c03e1810385103031201040d0403c100c80003400740d502c080c42034212410321a0001102c11180115100c200b644105070a040080c030140d010400c540004100c682e80c4030380880d00301d810740c407001a0703280034900b00b012001640c003200c4201c0040d050100 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 348967113 1250 348965863 348965893
    0xe2d070e010303051201090606020a06050415090c090c03021810022401061103070308190e070e0a0b19050126091b01031e0b0402040e09010e01060603060e16030608 72
    0x14034070f4170b038242080303411a83ca03000311500715051401000c006a103d00d402c100020050791100343c10038051044004402c18884000741a00c0c1d10b058100d494030700344101000354824500070407040d0203007400e0542c1008107484403c04100500d2600906c10200c0c007503800c7c0700c107009220703203503e0054000c0c40810f0103403455401c0841280c02e00c5240001006243e283c00440408019030300901d90654801625480b814416101c40c0d08501444111a03074410020301c0c0c2d40300402c1000002d01c00202c9000c3d06103002c000c1401216089416140901e4441c9002c440c0004207081c17480941710242420650659000e000030038a424203565140c085082006101d092100020407039030426402c104540700405410045065071a90890810071414503840d00d5507024941d005158803c0307001c0c1005092030b5a494170340c1c0c01d142064910004e00d0f59110361001560030280200da0240c00320781420b0014510380f1301e4075489410010070000f00b803103142040880040c42a00500e005051000486046254039808 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 348968363 1250 348967113 348967117
    0x114070b07020606010801060203180307080f01060306050a06080303040f17070b04170c03040521390a050d050c090c120117030406050c100507030f0e2d070e01030305 73
    0x1e41c0c809840f648001854a62050301c60078181c85090b80036600b0581c82101703c9081480a903003642d418010b00b0000f00c1c4404040001410b00e407a510000309802d455420100200c40003e03203444051400d000342131043c141c00000312a00158000600ca2410302241001001c044407a039859005103000a108010b02402c0ca10380c0740964001e0481c840e00182d0003a00c00f110340700d005000001c580091008028900d4000c0900035021056120340199000c240c0d1914100108690b91401c2d500c26004050130440c0500720944510341241c0180d00e03031041c40380010f1001a9680b150610486948400508020701480084441e40c000303000d080140c18441c10700312071500940e40c0c6030303004a055000000e88461100c1b0b01c1c0c44440e01ea001441c94141058422550b607809a640d0400c984296640514110291710403688600c02c4c640d400181080e8107149074040c1d0302801004102c56201f09082c0075640c51340c0d0b0315152007141c07080c03c3e09020b810b03143ca406d0402e001c60f401000f6401d80040000245900100 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 348969613 1250 348968363 348968371
    0x1063602030411040b010201051501030c0e210601080304060203041202010e0a0905090d031406010509031c051306050702010e0f0312120403020105090607120207081c14151e0114070b 80
    0xf414805e965644004a0884004403014540c04c03882c1e0400490a5011341d000484d10616440d1103020100d200d00031402c4086107555a1095100c5a07226095481052052a024164550286107414030b4a20b00a640380618052031000d1000001d48504580c06008150811440500b107101c580703a0710034542c801041c0466031100c1c5805001a0014040d2103449024000002e00031005020348581c001160307241c00001182e50548a000c9401c0300202d00c0c40c0c04180e000805645955036465020708039079104405900c2001400030501c180740050707030880c5000b900d03c1070030f03540342c41050310540000e40f41c01036003520703140e01100001d02c00884c0d002c8203105600ca54002d4000344840d840d4618500e940f0781c01204c82100145000c07a15400005682e0003e0601a005080003402c0928040d10031100d1a001d0b600034440a0369840140190610101d4140d840320394101c000c0700c0c0114a10104420700c403d07030000541c9119400030104a0382c001d00c030062444c00300c0440e082e110302c20b41c504034010041c207403 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 348970863 1250 348969613 348969619
    0xc010e0d030c09050901030b2d0402010909060e130303020910090314060103150203040f0b0f06030d1b060b0a0902160c0504020414010c03020c1c1401063602030411 72
    0x164080c42c2c3c0165001011240d0280c41104a603103141c803440800e10000d00b02c8100b09070000d6828004400c01180d0fa02d00c00404440c004441c10140300150160003241d0000725860f0030700a08001e416280303082258440c400c0841680051100d150440c02071107800c0300164005240d80f0110030040e803002040040e603204002d21140901c0c03031902165100c009100080079035040250219a4081c0c50f005160072921039298a29075501c190355030450b450b01207030680b0283d0300600400c41585070401003c0e11074540ca05000c4000c0d201810310034100c102c04100540b0440c3c03100b001d8101a100c2c0c40d8072100a21b200310045454100030803800b00c10403601101680c9070036400401261914040c0700301e034200c882c03400204c03c3c0f801421005480034404614294103501640001403410346400454581d103410010060b210b0240c5032610300c2850040710030105942e8940507090280060075240301e100e4004021442c0b210a001c100d4010036002d10f034061b003640c540040144020409881909201b0745021 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 348972113 1250 348970863 348970871
    0x1090b120111040b0f04050a0303081909050d0c2a0302100e030303040308130b01080f1b060409020318010603060911010c11120307020622170a0312020c010e0d03 71
    0x1166545081e0b80904080b182810300400c41003100258603801010300c110002d42d69801d00350b039000003d061400c681e005601003500201001304040c2000d2781c5107510424004e0801920b2020380303400d541d030490748110304203101c0c2c035010740b00c1801100c031070101c01c01d101b038110040d5002c03c000610031600c00c1e0b403004a005000109040c11164042c2d518401c110380c1c0a030003542107540300d03141200c920750b0103406401240300380c00c031003800305078078005190103410303c01c0003407032101c3c0c040c00fa59240600400480341d00d13540414500089940305400c0314201e0b40c10b0701d00940c40e500da9818090111080541c5550f403903103450700000820004e500040c01740390150b41d0b6007030400e8401c801924140340350b940060401000400c00485481d00d259100c02d40c501c43e1044a041c5032080e8045222035221100f84050403500304a40221403c58401d1203015043c40d074108144ca00070130400d40c0e07a644082e00000e00b8400021403101d0180e00d943d0541c2c0802c60400d0080c04100340c980340d05038032501e141c07043c5d80c0040d080c = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 348973363 1250 348972113 348972139
    0x90a1506020a110d0201030f1505130605030703080c151f33140412020406060c03080a091113020307080606090a05090a0f0204031a06010f0c0308041a01090b 69
    0x302e14180b205410403d00d0840400380000c00107096142e002c200e0606648411900d0041d05500c6050307491030203904640c00403070401c1c04002e022030559041c400b91a0030a0300070b02450302d0100e40e404c00c8030303800300e00d0b46d4540001400d071600f000f000007110300c07180b542e103000c0118a41e501264405020364054840003c1c907290a0312420f244140d40752401d180020000d05400e0000582080c4040000c03407400c0c580c0f03c101002c03c040d003035015900001031040c4100d140710540c903003881400000c0145040c50742d8035028683c1c01a250701802065160710700d030b9808808003844038003c805070740c2c400c004080600149803010320700000d400644440340000c00c1034000403003904042c011a070904034001d04807100300c0d20307240801840403801040c20390826111140483e800390140003a0014611512860365890710709644003100000040225040186000d4400c2c003850704524040251034240c03505040390756490074121030103560f606100420501c144000110700f5000e030300281100c0006c0b9401ca0441034 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 348974613 1250 348973363 348973367
    0x1e08180603070806010c1403130501031107110108090703020a1205011d0c040c14030a1b050f040b1819091103360708100c081302040c030b090a1506 65
    0x840b903800100d42c0800c081062036010751078821b003891095101c017080054070103129046070400030350b54100c41d80e0f601c2e05124940c0c041c018120401520aa0300d414950381e900d1381e01382110091030141c180aa11030128210f01402d011800245401504c60285142d507911240c1403101000c03000d5a16502e000a03144031320010100011072004014000c280584003034007080010448980c2070024084120400c4004070890809580700e45130805000810300c0c0451102012001101103a4007041401c2016011016400c0140c4064a5021200c540c0380c140d50400c004025003281001307940203000313003201e04421842c0b210480c1580d100074414406203d6111400449001c252110038545003100d01c200e190021961a42c445400041d0b00c0301c0300a0f0391707440c61a08010aa40142c01d45400843e480004c0b80640e000e0f084004090345480c1556207000d8031040c01d499480b62009110701c3e120448100118481d402c0356510020080408036142840340d403d500614042c01e0407401c003680400000350b128 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 348975863 1250 348974613 348974617
    0x317240303030708010501080a0f11040504060803030f01030f060207081201090c051e16020916020613120c020f0406080c0f0d02060322060f020a08090705010207030209041e081806 79
    0x745044c0c07a00003160742004015a00710000a1080c1c00c3c3e207070382d814000341c400c40d0b6005102d0310000800000b0f98550400080c00103441041d049112141d1081042c00107454054082d9811640c000c440c40b1611500f40c81c003c0043d2194140280200b40d0204131101480c10b0001240c2c1204c407000c0007080300300a801d809a9842c00b4035013034003a1150410704805442e0001c2c90003840b92a8803140035020f00c3c01c15500042c034441c020b80d8484088150b1105440c000c40d01084403942100b80120600242d40040d41c0d08a04000038624190801c00e2014036402103454448c068840402d0007042072043d192201c0341281d0b00d6105d0510356200ba8000705c080305c0503007400349503909082d0700a880b41d45507645004000c010990141c1d41d03456048103100003034010420611800300241030030800940d442501c18002042d4030800b81c00450103802074282005a0781c0c0010b43d41084035419590b4101035511414200aaa6606c090b410401203840e5800310421403040300401c01100301182e4410f4418180e030602c40a8 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 348977113 1250 348975863 348975871
    0x10b0f0a080307020f12120a230910020106150c050c270c070501151e0807210f030e09131205070203190c080c0613050d031724030303 59
    0x680041080f40c0c09400d0a681e042003010002e000340001c41e40e0000c030b05141086003024440ea1681c003050200f01c007035029840c4074400b190441801c1080710070421b0709105104510703100c2c0c41650406030b10f69080c1d000b03400c07190046c040c2d2181c4c0b01030345040100c060001d5420441c111218001d41248009903c0c1c0381e4080c0c2140c0031158018603c03901c6c1400c1e6071301e00b843c010b0711001407007009102043c0054424003581c06003140c440541c1050904d0030201c1d4000984d41016400403000320f5070180311000001584d0000c035000c1c0303141424620300803584128402d100e2040940901034000b178180615420840d241150030b000d030b64941c096030365182c20114221018100400c441c0c1600070003c3c40d030784039a018000c1d01d40001c0036100b0169501c0e03080140d0204011045885c966811020403450900b880340705c030041010380d00c00c1d241c50803410007841d03500c00601455105000d840000014180301e8920103020380301c0c1c1d00756017030f0b50f040a80120912400c0015104400c0c0b50401140c501801c0120640c0d000d = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 348978363 1250 348977113 348977129
    0x1b061106010e061c0c0909121706040209010e090109050106390303110d09062009040510030203070602100b06040305100908191d03030a1b05070f08010b0f0a 69
    0x9503884050810a945440c0741e1321a5800c2c2e15200010045055580c0b03000040150b44000642c200d110700d480401c60303181214010070302c049488003074042035144803400d51220b000ca400503078482c03c1d60016514800c401c00c2c01604104154004122800c003a1302041c162560340c3c903190010700803101c07034140d504184034030f80860716454003903001080c2c6001e0742840362034840d0902160448942102d403d0f2600440f00c9054100c1d10b070009c0310300303000851164052403100072184c02d01d8094000b0720062244241d80c4228040c03556400014885400019140017540e801000d580d41255a4800203680320035194040d1205841c2a183d42858038100003101c04880c0e1250281800400c0c140424004025220040d60401801c214110460311134000d07040c4100b80075254426801d410b00c0d00c0d038403c120220041ca001341c2c020070221050303640094203c00c1c00845945000050b000c14130307100e810304060754001c803a440c101c4040860038040640145c20782a030103907051017000c10050700b080044038803445940301c = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 348979613 1250 348978363 348978389
    0x3020706050f0702070909151a0f03030a1b140609033a0c0c080a0c05060606031509090c040612020f0102070e0a0b1c05060402090a020f0307030c03091b06110601 71
    0x80c0e48081c0c104040c1f040c01143c8807108100081442800c0da544000c560725070303081d000b030044528034020000d880314003c20b030011402c00002d1100588100b10408105121040346c20441e8100600034981c01100c0c030000041e038506041c0700d20855601c0c0c11110241c800501d03034002c440740341c500c200a0a080381c01080d01c0c405a0000307034044500100381d109000740402c540540030b0004154100001c20314000d07165141c6068561504001c0d0170000040c0c416441000100203104064080300455015940205d4803510305403104140c10f0329010044080903049818031000045074880001103d01c00c50083e6054840d44860134012a103e1480b80102074811000714045908458280d0007460750380b00241288075003110340303c4900450307402c0e1101183d07140c0c4140c00b040114108a48030b19089920080c0c10350502265181c8502135020050090040581d10f802d414000d9201c0d401c90518640c000380410101c070900c00b10407428064a014100104410000da44001a00058003604031203c902100ca = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 348980863 1250 348979613 348979619
    0x203040510090f0f0c060306060201050c0d0b190e070f02010207050d030507090812030a06060212073009051219080717040e0604140702060a09060e070603020706050f070207 76
    0x4000c112000d03110203000d1030140f40041d031010708070000e46000c0c500070488107103098802020b0f200e16821207000c5904203400e200c005850101511036003800c0c0d44011034040000808150000310034003030400a03019080380040e1901c00261524028407095403007842e4400203030700aa083c0d10400c1e60013015076007c070403080030661080c1d11154010d1090300d0709903e004e6503450980c1c035129140c5e840700801e01001061142444041c840c0e68020040350020f410054400840c400c80d034090080058909108804441881e040030031300403480721141a600c04100c1890300005100420350700a0034055180c0400e0b142a1910028014600303280e0442e4045c4504070070b42d00c01a0303d41199404507041c46000901190001c200f8000d031014049600c40040d040c5069000c21040d503d2481100c503401d0f51050a0202007507001c2280350384007605060200d03e40ca407900e0b0003402801c007071000420602810b000030401d184e140e0020010035001c0d43e8144110384a00d011002d441c00c05403101e00250384180c0c010 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 348982113 1250 348980863 348980893
    0x30c030f1802150d02071110080f0c090d0f0515070e0d030525030f021c0905101812030e03030901050304021903060c0804140706020c0618040207081c02030405 70
    0x5044581d4490f11814050308609500a1703812a07001107507032209146984599050810501007409030a06d4401110b04000100744000c0d40040c107440c420400008000c101d03616441684000d03d58048003201d002c040504285454100c0c940400e040c1d4403003880441d540911030303d5480300030715009052410884107503906841c50341c030681006121404048070079444841c5d00e404401550f00035125200704581c641402410002c0301c070f01c041c40b0808541ca119031481e07800342c1d091041e00c0e42550f590750b03080c003075981c25a81941e90000300e20000803101070104010220003c035035030302c62007903d4070308007000d4070400c0548038051070b08918000b500a00c0004d02500e40100201102c0d40204404107000da201c0d110340040c0d031700350903944010410305800e04c002c200481c04c00105425460014080c100e0038031700025218603164601c284200d134080b4007120300c40e50702920010306440c000c008560342c050354a03040f0455000600995070003126510942480c6540c4e008aa00c25a80704025001801c100c1c144 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 348983363 1250 348982113 348982129
    0xf060f09010b040c0f0e040609060b07050d0f090e0c0c0a030527090c03131407060e04020a0f0e01121b0e0303040e130c15110d110601030609061b030c030f1802 70
    0x154030351098690000141001072841003001528007103082f96a40c01d45030904901e0200c403034030301c030f010084003d02c800741e02a8442c030007400740d034010030710003050752108550071040b409119004c2180e4080c0c250040101a0040700419051380b40c19910240c1140d0760144050502036003400c1a000b030b10500c002540b40b131050008683c403148011195140c041c0946440f030701d862000c02d241500d40d02486043c0261a0801d0350009500000c8405501e40301505500810b001c1e00d160903a414000c250440c184180c0c007070a0161400b000040c82017000c0d0003092190403290800704018000708400d9050210141008404c03941903441d2080ca403801da49651040c0103a503184030f01c1c1510909101030001c103100f41603a11100d01100380742d0700d91070010510300a090410072054218004d00401468241000b0408200b460441c7d400001c0060302c900141410009000c050b03c40b6618072007402051050b00740c1540c041d020f560550341c0c0400c0300340564a4000116985005c8044840601070304880c01482c03e040b0b = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 348984613 1250 348983363 348983387
    0x6031b1807021c020d0206060a140d06320108010603030f0e03070b030106050703090f0501020706030e07080d05040602060a02030f010b070f17040305160506030c0703020f060f09010b040c0f 83
    0x1c100c0d0301d141d9010010256051203d88a000160403031198091619410490907800000c201d88840750903181007504030b038178202c40c55990701804501240c2002d020a9500030410020001e50031092150070071000c501d06200d4000c20100c070643c1342e0011500b030301c05200e60000c1e070394161120390401031400f2069518030303510090940d06216160003c00d400d600ca001a500920745a15401e0700c4549074a8060100c20041c1c01c9403216012150b810800e41c0c1e4009480000c4079202d0400007181c1440d228124101441604440307024443e8030700300c85140e90b1000003441140c0007a42030b94160f440b00c84045e02640700c00d840c0003420390a20070040c0322603007003a03000300180c80c480c1c40d4007082c1610075502c24540e924030741030a203110707680440c0800601905102e582d100c02140f000d050105030804000807040c0c080548101711440e0045101000c1500030028010500c06402c02c541c08ae203800e0881c006010b000f25034450203542400001c0e00c441c01c09008034042d21525480d40c032540214a0001c07607803410030038 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 348985863 1250 348984613 348984617
    0x50c0d051603061e2a05190903021309170a03020712020f0118020a0e0402030f0303190e15010501080a140a022104081801050f1206031b1807 62
    0x20380340c16001640798031035a0007140b08000c0480e01414910000391402114035181c114281443c40d031300314102c0d0000c0360130741007035820141180441004004507642c0c06036481140d8038040e400b11440b04160403c000c081268401c03900700c071101c0011100c9000340c440840e00108640190054600466008c3c4051702d0702810524005007840b440d9150704007030000c1c961040000d0b802042c1001400042801150102001030714078614081c00e5501084402e40f1038891a041c091641c40410219070341441751613200e00c141000c0b0ad80b01e007400c0e9411740000b08120b0010b61018504910750758590008a0550442c80c40c49012140903860100192850100107040c0082d07541e071406411201c902840481c2d000700c503510300060b204d201c0742280d11840c20139003041171000c020240c01c00001034088402c451440440450155520450500584403401241c0450445100201c0d003c0340f0040b0f18049a031050300c045080f181001501c4031800130001040065a40006c046500510341c1179080034080d1b0018624 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 348987113 1250 348985863 348985873
    0xc180b030411100e0123120a06030503070312061502030d050408090a030b01092703050a051603030b090a0b0f09060a0f1805090715031a09010b0a020f0a050c0d05 71
    0x58000191071243c4400c0002c0400d8079400d001c881541d00046002c2109540342d03c9021000c00b0700b0b1064507134010304008402c85030320b12000401462507030700107100442e4403604407070301e4030710524003d00082c407840c0340b64200394a0030b000015402038010169000351000c0d00954600222103c10300e01508c0300401c103803416403003004090026200ca540820046000d04078404442d410800b00320306960503e80100464480d080c900001a03000c20804200568941841c80ea82c008a03d000d40d01ca00510207054040c0381011140028103815400c10104080c0403601d080780c540d03964003440d040710301da034a925800000310180d00300c990804484281d000500200b0324480c2c60f5464401c0414014650840c5800910860034035090207028002c117a0015000303006490401e080941d05c50001420340d00704410140c4541c40006036018941c0001400ba802070701401e1f084d0385030f89640e80c083c1c1c0604484c2d40144900d0000b03005265010030344090f141d60003006448085000401c1210744907048501b80c07414020 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 348988363 1250 348987113 348987143
    0xd0903020901051e1009061233211a07080c070221010b100201090203030703050d0e1204081203010f0e060a0e190507020a02031f09060609020903010c180b0304 70
    0x380f0707000b070030641c4455070b1000c1d0b05030b05046c00103000e1581c1240ca82001d81c145031410596278203504114039001e4006281c0000130799509100035101d10310740e116001061400000c5072404120318080240c1c41c0c0116110881c41550340d0a403000c00700d04980f81c0303001a0054000c507030665100001048107500060500c0300c031020310303400400100c1c1550040e400c103a540ea4241620303406c0060041804035118002001205200e07004240c4a102c1e41c000113040080004074020110015803082400380c010208440042c440703003a0041c2580d0090082999070b03c03802d44411808078a2000720f82c1603581c50020407a28501d012141034842d00b0280075680d002c05070140115013200070400551013070503503802c02e02c210208040940101c40015103c28119008455400b0150310700007003032070f40d01c1c10400c2d007002e0002000c40100d00030200c040c00185030030308102c0001403d00458010384400707a002c90003040791545085c0d007900c220002c1d1a0701258400c1d003540c00c01116914034040c503481400341d20703907440c1a64 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 348989613 1250 348988363 348988369
    0x7050301060f091103090d05070812091e030901122003040c05101d120c150c011a0102100b04060b0415020111031e060f030109050303090d0903020901051e 68
    0xe07454010b495036911030681001540320034007622903140b1140c0c1d1818a5420920b10160b11008075012000522400081820400000320304072a016a003803010a4040c0c2040900c00c0e031560b4183c5014101d5401000b0541600c10022048844501c416140c1c400c1c00034a00d0f10301400303001c1010342d40c80e015220340c108044000c80351005602c21880b4002c3c1075020b40c11300c0104182c02c103188170060104540c2c411401c10300061b0388800751000f0000c0714441400c1016092142c607042c1542d01d0141c00021035001c12402d00039020280014084800007844802c02d159203160103100c85540260041e800b8600d0360901d02000d6000d84003807a40584040352940d19480d402d440d543c0300364030210b031031040310128028565080c451001c0c09040b00c0d400c585181070a81c0410003007606002c800400d000c3d100c0c08500c2544d5940c403400700c40c2c03401078020b00024146042542e140e8004071115401d90003071400c4000035910072401c9501303981c2d00500c0b00c001c503420700c81403009403248180300d03424140540c2d440709110b079 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 348990863 1250 348989613 348989621
    0x9060906060306011511011d0a0c090605060a03180203030408150114090c0c0c060f0903060901090c0b0903072301350601030209040f020409060b2107020a060e06040b06030d0f030b0307050301 84
    0xc08c4001450790b400f00d0701d03103054601d0490307105050251a02c14203104035583c40046401d000b2151801003040001160340703003c10368049400950510002400140704480800c02c09848034207180c4407103043c0c2c1e0b01e4901902030b000c20020250301400d40000103004207140c50213007012800c42d60031181c809007000003040d9281d00003041560842804904401e041c541045215802905070000384407496443e0750b0707080d4a01190041200084010405041d986c0b4204000001000052030000c1000b4001d007444210044440000780041d500e2404103004040345000300c03001030f21108034480403903021410304040d6403028100c1810590200040601a0b5079401000c0c1c4400209000680e00c070302c2c1c01c5141d0b00315041070703110002c4618184411800c03101c0b4000b200c80780180044940040e42e403004e10480c20480d00700c20040c8200e162401490503890005003040c807035440b544015619031601c000b003541c3c80c000740d4000700c00202c40c008113407a094882d40107502c043d54082c04542e18503031100c0000b4251 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 348992113 1250 348990863 348990911
    0xb01060516050f0a0204110a1d120111030103060c050a020c010309170c100507020703170f040f0b1215090610051912050106051c0c0c0b0906090606030601151101 71
    0xa54001a80c04c400c1d071903e0720407402d21081564400d0719007000d4080c0504001c0840c0740b416010101c42c0246d15080d11902104001500910002c000c480008a8980c000c0d81083c0425100d617450a85070711091800307507040360f41841d0117030014040c1e208060011000b600c0010012191004034084210240d05164040c0c0b80b20b9020f070001d802400c0c10741880c00200d850007004001154444a010800b08a2422020b03189031801c0c076019035254284481070105200740e0744481d0100220410005554604034040c5c030006a801040c8605030f02c44a54a100340d02048440303561204400010a80f10700d802c00a0204854a60802c81c0c01c11540e0704460700b040001c900c850001c1031050601d20710500031485864050070003410891305058480c002000c2030344a440c1c2d2401001e654085000d8100d0150110b03c40c81a8440c80076515481c002c20020307159102654203070200d2149201041d268900801c0241c1031712000109180445604401100d03451450b00e8449515580c0d1441c010080300f0030414003070700c = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 348993363 1250 348992113 348992143
    0x201021c052517192a0912060203101a0a0e041104090e0111030a06060305100b031911161506030503090f010e030304030b010e0f040b070f020c18010f080a0b0106051605 74
    0x1095000b0a0240d1741e090141c0650401050070350503c0104001d0144542e882d802c51401a200e81d11100c80040480c6507421440f1110741004087c0d0b140000040240201c1400c1e035070300c0104080d00b105010139a01d007203003030751040e0030207000c18002c0c41e4440d481070411058140000c60b11000d140a81d40841e070050f00d00104681e25554280070f103a80600505400003400d691290100b0303d8034503400101d00000d041462805800f409950060f9034030b80110740c140100c3e0380300a5480c00001d0710700c0150b240c01e103821540074103078402004000f1480e00c504403c5036005000f5603d800c1c002c000b00401d0b4005c00240e641408800f940c81c10355a02e041002d03001661247c032400c80c0a506080540941200080400030860501002c102c0013401a003089070300304855050031044c000b44107101380d0800000c062901d4104015880202c03607000d5030811281200c40131950482200e4880c0c1c400e540751160b03a0406401c3c0d60054004110240c4544005c0800d610042e105241e0783e6619038031541003080c240c2d0140300c = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 348994613 1250 348993363 348993401
    0xe010e130b0406211202070b0309070306060501030b0d0305030601021e0c03061305030909100905100f0819120e0306011409060105030403020c010e010201021c05251719 74
    0x15007802d051040c40003a00210aa040044ca103481c00c0c6009218007035001002c00d400400814003081c02000300c4006040903a4500c4e07120724102401070740c2e460003440b05444050600500241e01d500922440c0141c940141034203641440303641b070a40b155400036050718114480c24020002d0303030015004410701d10165101401c403d240410415150540152a00700c4248003c0e40c03c00014a002040b00e0348000141c2d01484181c0d1440740001d41003160b42d00074884030b0704001c1007040d2110342c1a280816140c140124240031511354128507500c80c02000d100410b50321042c5018042186594030600d2004146085d0103071800a502181c104036003a400701c8001d07c074141074400d00f440c04005480c0e0060742840c0003401c600d49900d00a50303810080444906200152518400c20791003901128205440ca00903207401d9861030028400400046429540c0c0550f070044c124000c9c40c400d181030700b0846083d510024045050b0100d11040c030030203402c840c0180340d00ca4094010240601501808031b81d601071400f = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 348995863 1250 348994613 348994631
    0x19030207150e011b020409021c060c0516080f04051f0e0103090209070c0318080a0b091212090a0510050f2a090402070204050108161706070e010e13 65
    0x60315541c944980002e00a0951060781680d910080842041025605080d856501030002c94000d05800d08065000b903611070300014403401d1801d000d00d11328490310007001120703040e4404036540d000c1d243d03410fa140c2c2d0588280750041041d000c050440c241d04c18002074a0f26642e9400154103491103544900001e1030341c000b040c8a241c00c140c03c1110004282000c0c01400481c8d40014a8039100501800a0107960039070300782030501c120a031589444001d829201e00715112000e290707464844c0c640c02c0718030551650004040040c04500091607210391a115820883d00004111580c0307401888450176208011303248000c61010401117141884d0100f000400d800c0c03c40c0000d0f03c1c034800401c080c1d0250810f4650a0380f0b8490f80250303000c421032880c902900e035408600010060310a41c20040c0d4403a0801001007541d180205402404060140440d604159101d8658500348000c03021030102c0c0d00294009400640030f020041100704051400c1200040c00030b00196014120400d000303005c90b0b58070344613 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 348997113 1250 348995863 348995879
    0x1030b100c031701180f230115031404030309050a0b010b09130b090a05060402040314010617240601030e0d0816140301170a05070b070501050609070203090d0519030207 74
    0x9250f2441d01c8403040d50096040c0b002010041600c0082d9130a410f03034540e40c2d4624601e00c0c1e80070240e8185040004200400040501c604203482805200a00c10000c503105600742c0c040d00c200d10224242407407152499496880c2038004003401c0500b9100c46c02440e004d04005408500458041d040d40b260075500c41c41c050b0180300780703441900140c0d41490303d032400180d4980e9a108420b54400d10261010900e5954580803d000e802030350300042c000c2a004a04002010707064103c4001d0700d410003280c2542c0708940344040e5607401c5200e40056030300c00b08102400c5031549854002da2105042c10003046d0656a070801d103142c403034100300900000c0c01c04020301140c5071003003544030302461680c5000000110501c0c80d12440b844180303d091032441c941e2a80084082040c000c4044964106007174a504980e80c0c1ca04803a20351201404a650f94a4100050700900d010003807240504901d40c010341c20245010140220041109400e40b1148101c0020030007100c2c03031168085c0540e00c00c2c0e0103841080c0c984812 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 348998363 1250 348997113 348997127
    0xa031e050106180e190f0c03020403050c0a031208061807021b061911070b04030f0605060d0f03030b0109030b100602011a030c010f1103030109091101020d0e060901030b100c03 77
    0x50103101043e8200700f00f08401409110380028680404418044018100c1c0b401000005520024141012007048940b9095409001168001c5055800b6407260a0400505050707a010003001e2405041d05000a02c3c40340302c40c50f078014000f5100c0c411010610b22010b203602c40031100200181e21003540000019804179811003041d0054526030706000b8a02140308208130401003002c1008460210f0310007110040180c0b1000b00000070b80243c4e910f07100d0404105c2586900b5096071880c1c10f010115986040c0303a11030306079081e0001c108201040d1240d6089020300600b03041d05040006000020012901818481d07008100342001184120710f400b05c040d007510002000480c1e85041d003000340d00c650300c0104071030540030030900e0131701d030b15145048042e100b14000300c06509042c480400042041c808070341c00445540e0046c00084540e030018001241d549c2a41c0c000a03001030300e800284501d905040b40606115401414042191821240422000d0f43e91600c070b030000600e200036103800d168101e81 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 348999613 1250 348998363 348998387
    0x1217220e16030c0f0309020604050d061d0307020102070e061909020a0e03010213050906060c0f0102040f0509060a170114090d110703050a0209151c060c020703020f060a031e050106 79
    0x90500c0446840000600040c402d2000d0344e051540720fa00020844d600e1030221000382c80018015a6020750500b0001e0040084c200104d8030600104450000f850000060b00d4107140c0c140d009003111410441c400c491740301c010300616003040401710701400a084000901c40038101d1007000680f941c1c15800d001384040c06500c0b4450190340f04200040445426540040584d03200303968031985e54030b0301f40201d000c80c4501010030107a4040c403181980d0b0760606400400413070300c0344084c81c050070351a0810080c00500585003d40d0003c40844100260502c142d4210001d89000c00001002c0400d40b81d800400b5104480100640c0c00103180044040d401c0b04103108000d0744080245462804c42e5075481d69000c154402030300c2042c1c40000688803000480030280da4010141800007000e00c0b0003089002041030a0301164202c0c01c1181e5158841d200103021400c40c1c2d001010001c40307040034020b010055001070340d101c0405403100e03002d11801001e2200c2108050000500081543c50a54000c0034680c20300 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 349000863 1250 348999613 348999617
    0x605010b090306040609080f0a270b090f0105040b0708030105120304080703030c0f0f0b06090f09030a210c05070c0506090f270705131217220e16 64
    0x401091a00c0e2400615984d105500000000c0d50406504100c40d8900030285c1c444c0315840300041c4603000039401503420400c0710281c1081890b203240b0300440c01300813106000d08003140ca41401039148a150600008402281c181460f80c0740c50388902c0201c80c268800c403070a6030100c50004c010011410099a0303001c0c1080b44102031800e190501c669161149658031000d0100100000781900340b02e80d451000c8403103680030351a070035202100e2614880487e022150103104a030300900080d03040040540c450f1041d50030720007862800c0d240b082c0c251680010000c1d014448449401d0302444601548a4200c90700d21507210135455914919044403a40880e8204c1802850240054402d40e1200344000190344421a2402080f000c44240e0b04100d0b81810034080c1c00240d14030a02c091581c1240080c43d40a154404030559962901003600d60000e803a14020408601c4035201c2c40414820384c09403c00504480aa071810781d0520302180070545c90341c01038004581100280142d036201c5d11a2070103140c03258 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 349002113 1250 349000863 349000867
    0xf0b2e140409030807050703260a050f0108071a1b160807030c0b0306040921020d091527031a01050319020402030603030408010f020903010b0102031303030e0f040e01090605010b 78
    0x250f400500b03442e00505190240000846ca100800d03014100c0c820800850709040108960003c48488a5420540703520105914200100d00c00102d8420010305980700d0300d000302000c83ca40341d048000e00c0000c40d01114080014056110908a042da11192803441403005001c21420701c0302191603020315500ca000c0c1507221100402c00100321055183c1190100150191250b032100301080107002990401030001c51101036001e2206190007071078402c1003a40c0d007254600045428243c552010a005207204c07404d0f42100115124030a003251700d640224440f200c40f809145041400000d015070700121020740701c0440020120555800303850040c44100c00a10b10802c40b80e8070000342a0302283e0181c0550380010020f80251010006c0b24000c0c000b1400800800c401c10b007c00c0002d410862241744203500304040000190b200105455802c14001c51164a482ca15034050701c200c405144030030742100b1184000c40e0103503581d214880e030303d101a03000401c05540318603080084038816000350f0001d11007 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 349003363 1250 349002113 349002131
    0x10f050f152202090d0204051306060906030f1b1e05030d050405060a230d0e060606030717070309140a06060b0406170c042408060102010203040f0b2e1404 68
    0x10b01480002100c10960300140c0c0e0b011000c0c0800d401e100d40384006504a41420b00b4001300803807013080050210300415042009a450703c50501c00e5880710310000d008001e55210640210704010302000c1a14028000300d201903954608045105403070780c0100780c240206003003c02c81030805104103001c00101c1d14005292a0500d000100180540c0702c001c0100044049090f80c50080c0040e200c000710702c94540c03182c840044c0081c40d001307044c003080100c0c2c3c18064000440c142d401e0440941c0c0c0200d50588503200c0a5044503801190324000428035000c240d161003442001c5045070304030b1800317200c1280c084c005c801d03d40c3c2420780680d0025401800261410882049010761144101c03140c0c4d4200003408526459070710392a211030007103400a051580040191994042040d00803a4458075107031101030180d550b220069080b4042210085c00c0313400019000307800121001080d9602904001d4081040303036500c1e070840b00c1020400130310300184015880502107444803007004000701c0022503040c020614 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 349004613 1250 349003363 349003399
    0x30e0301090317060a08160911030108070b031506040b0901030509060105091f08010f062907080a050c010c020d020c0d020d0308191401150302120c030702010f050f15 73
    0x540c44481d03c5800300541c04a00386503074801402d80104202c10866000c10702c02d14194210510702e1103039255880c50180c1000c038011011041c0c1e4100e402000242501614200406e00b0701ea00041280300c3e5000180f00301111030382c502c0d028102030400035055540394080c200c00501200c5026182e00d00f298003c00040143e039440d05005075110344411451540c0080b00b4500071800ca00d980c101e0229942400032081c10801568024400c603101c6040c6d8019605900c0383c0c0040160301748908007890300c0c0410202000c5104000180040c2c0e0062401d00d00c0c06450b64000c07800c4409100c0400c005801108040c0c40d0700794100080e41c01d80c602200e40c900c0c564145d13400101100c81407000142440310540c005480189a441c0504003090420414082d451140180c006a040240112650321000740c5e12004001c0c440e20035a00d22100ea80d880d40059160180c2d600d50340e030401800710003190340b1410809070052060207400c1c051a1505030402190500c0c0385000440c10030151058018240310150030a00c00f = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 349005863 1250 349004613 349004627
    0x80709080a050604380604050c0a050405060906191706042304050a0203120a030c0504031e0503040f031b0e0609040f02031e0f06060f0a140d0b070804030e03010903 72
    0xd07602070580b890151400c4446009511803150b0f151a03a048110040c80f1254044c0041d481b0f084202c50070441940d40d1070000605000c0c1094000000d50240704c24000741c10020014a604a4000e18039820544101c038a110a020030700c0001d0001920304c0303100c58000e94092070795500a00101d9050104102440c00344c94107103585682440350784050004942488401d100e0811080d40140582d09c0b600350850b07000102d40e001c1c00b00703080000d18000c3d5070040e2a105005031400c0da54400d5000030080e15030302d0390f6080c0344030028060711503000c1004001a2400307423004c9440207601c00d500981c2e009030260911a5004202d1b4444004070358100d040009551b210980194059030117185010514500d0003ca8944007600041c1003076454080d00d80f0100c1c080000d500f00154250740c0c11074070355560302400d10040c0e62102600e950031441c40701e41400088094820409418000382c5413609a01041e203540c0e0505009036503810228003c4014041032590000f642a8001e0040c1e00a011180140d0b03030040100c = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 349007113 1250 349005863 349005871
    0xb010c0213140405030310050d0201080703051005030105070e04060b0702010912060b0d060f0c09050a060f0e1f120203040804121a01060807111f15030b07080709080a0506 75
    0x28485a1094490041c00d5a108070b420002d8200d0310300d42c0b450107190040e902e500607a0409032048014800080764600b200700001c00541c1a5683d034407949460f0402e4000d010042c0900c1051042103401048a840901c80c40744079404941e2041418400c000c280400c89d096900051030040c402c011441c00360b600030211030216100c400003981c3c042154103000d002003410040309039001d10094500800c2c00109d8100c0842e42031074480170440c0d083c10030019140b04103113100c0c8940011400000304440c80c000c5580c0344550741103042c000c0820080e240080c40b0001149640200c01500d600b03030403800c2e503010b00c40082c0e2800d5284110300d10b091035120701c0010301507441840a04001c0a00381c000b004540084003001541500c0c000e840c651712004040c10f9000c08641c4d507000290480803280501d2000107a03002c42c4000215048800c868280d00d02029012400820761901e015901c0000040c5244040c0d0b48190501c1c0e8459041d400c0403007000b007030410194484421580911b04038408902e020a8841c0c00c = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 349008363 1250 349007113 349007119
    0x50406061728020a03050f090a0317060307080604080703020705060a1d0105090d0b0105040509030a0c02041107080414090a020705060a1d07030501020403060f140705220618090b010c02 81
    0x1000e02c844100c10240c0c1d40c000c50700703050001c103001242d140c041c3c221314087c0000c00711300102940c030b980090b66074802d14500900043c2259400e40024001582e006802a8028041c0c46240d0784070714000f0700d003110594040380c20303031070020f428003d050781800a200600011585185420f000c07080040c540011015089075410040400705010b80c06541145c0000501601a00107070310141005004200d0901c03a01d070003203080c5400240200d8003c006c41e4030485240d01c0f03614004403030b60240320083c6110a2145840181089000302040032a40580000d003c6840301c201c2c40c0001f40f023800001400504110301c1c4a00500c0010005040411019070140c41464001854001c2510400415002003800060390103110000703c1813160640040c401e9a00444041c45010708521300f0f10200c8211046004c12070007108085180340d4840c1004084410203414443c03e00c0030790a00c0038561451036400380303000c19142c141609400884007031001c0108070758241004951031100c0040c25000f08008020700c = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 349009613 1250 349008363 349008391
    0xb0621030a030515040603031d030111070803090a05120304030306050604121e020411071709031c03140a090b061503060d0f06050405030406140f0d02071e05070504060617 75
    0x10601400307100081c0c8600085c000c0c06001e90b24200a04494142104a5850030f0340e4401052903060500a0004940c0320800043c030300039517501c80c109207810140c40c040b200d02402c40c6000108100300500b4000310442c9080c59640c1c2400d01e0041e007102d4241e40464000c24003803008110403010414841029034010010b41d41d52500c206000201484541c4002d5106140440c13030510340b8011005810307041c2c807518651a0281c1c0d0781e03030b88001c82d02400003500e03032503400206a200b0318843c0005100c00d01186080110380101c05030702a840381e03e801ca50307013081e82e0740d035446100034080c0740403800c0d0b0030010503203c10b01c19601141020203c0d200052803035000300817a091000c108030008503d81051a04683c080001303041030b1400f01d80b43d911510806000900281c2c111610760f002d1800c51302010440c1c60329610f004040c01c240000794021410554040000d405200000c00f9040400d500c0b40d486100a0300209042c00204030445802d0f4009500700300307850130340c2d6030907082c01020346400001c4038030020 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 349010863 1250 349009613 349009621
    0x1080a141504150b0a03050a02010311070c0b090f01030c0c1e08070b060a1a12070e040219020615150c1204090e01060509070e090613090b0621030a0305 67
    0xd464040300141c0c050420380d10000308802d121203036014407a0b000d100e40051150407a82403c00c0280451400041d249400c50880c5400643c001e5000800394035100c03030f2903410120b158449041046141c1d204120074030380081c001c1d1191912241c0e0202903034003420108042d075403100c0d000b051094920380040082031030f41100d010107a40c008002d640c00c0d03484401c2aa96828030300d40740804900070f4801e01d01031405101e0105804640d0031250301078003513208545082800c0702c400100407907005000602401650002080c03142c440e40000e00300389a40c0c40a21054805a0320000d1420b03400609030000c640c2040b040c1405940c8100c12100c4503c1030b07020090700c1d664010441d604003090030680000007400002c00040406880d0008442c07410301100030031555513a10103000c0080320440d00400001c0c0650450200e916160000b260070a1002d05a07107203944010005000700c420f050340c1901c044411008000d418501084c07048803081030210400c850b041004e0015070b40c0d0060800c00001d0640f200002 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 349012113 1250 349010863 349010903
    0x302031e070917010b0307140102060a020f040b12040201080619061409030304121205070b24060f09091b04120303150605030406050901060f050409080d09060204170601080a 76
    0x82c0301501d10140349900c0c0c41e80d0408143e00800d41c0c903044c1400303800b69040005154100044184003c501a00a000d859951180e100000d510920f070307860201c8014000451111700c910f0143c41e0640d069250030b41c041c10300f400050603810001702698807441c40c4500481c881940340039041c3c1160300398244081403600c88007450440c0c1c050794420035014440410009108071800c16021200380c01100c11007034060070103004480512441c14050004480c10000c114003501000d0501c1e42c996010640301e440d10618000561035a205c0c400c1c0000c00000401d2102c5580390241c000f40c2c0201c51a8200b1811485c5100076401c103000d1442400306003ca2031a031182414041c0e00030b4244c0c034116800981c2c2c03032503e5840240141d0015141605d51911307140020310a404d0511610b0140d03281b40303218608081ca0a800c01c00941500702d0204c82c2c80e5421b03c40c41d081e0160500030060014840c010244c0c5442c108001c05040081c60b407009569030b0701410041008a1000c1007401941d6000841340300500144040 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 349013363 1250 349012113 349012127
    0x30306030f050304061d0105160f020d0503030106020c030c10030b010909151d0f1b0c01050f0103060e0d0c0605060f060a0206190b1f0923010e010302031e07 69
    0x5403944184610741010400302000810540d80c0540b2003000b07404011804000c0d2000f80d91500d80490810442e115005200c3e032000c402051140c016415265940d501043d0a0481d0250880d0194008401130082c240c050040d0404d5602c2a4010b003440c07a60303940040c0c070703c040510a100505540f40302580f0941d10920545019040504082c841443c0c24086008136400920070005641c40c6070031b54040103241150348070b000e69038548803e40947c80e415201041c1d40c0032062030f0a40c1180408c401c6000350342c2801103920030200c040320b0400039032450804a007900c0c2d10008110f0700350090038a1410b03c5401940800350300750005000107095071680301050040b003a84281c03917071001000c0b840044040c2e0000b10359119500ea00342001c1c5104901c0c034114180c030100c00200b81d0101c4203000c04030000640c20202c241071501840c242d44030594586e40c0221950402031000c0b00c480c0041c2c4662040c3d600303d074140503000002e02e021840d6181054001c03218040d0180182503c822030070100b030090b8443e0403 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 349014613 1250 349013363 349013369
    0x302190c14031c02030a03050a381201050402030f03070c0603020c070911070309081207060b0d0b0915010e070f05070f0506070e1e060f1e1c0f0506010516030306 71
    0x40b100c0d00f4002241c0080d40d00c0e0000300c17130500000d08000010f010301c507440c000d1064403203441042a03042c0c040c040704041d14402c501c80c072000e40b140b41c6420160b0b66540708803050b40120460000070b0103041c40c0c018036080100040c13a20b14254001c20402e030004440210210403100140b60058444014010b01360426001c1d80c0701380d90441c10581c0d840000e013202c17001800d645101c0c0e25850300d001e42c7c907011a622882c1461840549481c03e00505001c11031303907009021000b0004000c603008103111f59902903d200c1c04d071203007860340e0b00c0104844044c0442030903036405080907a00300d12540c0350101380180306511919010b4200500810204100848141841c8200c0d40c05000d5450324600380b0303001841802d100f82c1041c81070300c041d10456224040d0700d03c100140d1402400b02c4d4601885030320b0b0705060381d0001c545100c0c4040c0c002980b51540c485d550140c11000910104044c1d0445580101030640c1c42025502c404280381c04140070b981e07a0490122140d4208998030306040c050b440c10182c0c002c00d11a4 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 349015863 1250 349014613 349014643
    0x32109090c0405270a0209010e1215090f0c062b020c10020f0a03090507080a06050601080106020c30031305030f0312010b0711060c0a0302190c1403 65
    0x6030600051001440140041e2007054510b402c50012409041c1c51891858164452101550010886409607500100a0418103041624502d2801c90204003804c02001048001e60065008000b0681c54041e01a800103400001009024126100140c544400121842c818400001d10451032400701e4811802040306620b8030081075440407952001e540300c02c08260b0716010b000d0070320400c0c80a5100343d802e8103440c01016814035240410030381c010902d1060980b01803080210018051404110006610f84a0f103408034035400d1020000d4001141030f0050025500f09124805086c2c441002c0e210802c45040203070121450070f02003640c900d44a5003200c0f00b1500000640e081c0d401840824101164400e4003110003071001c00716071545a025032006030f250081c3c148010400303000c5100c0078000c45405002003640511040001404603448100100340325040071034442c1c14035805005250f0101001d01d01c0c0120385100ea6166805064940075035034155000c000c5402a54800b00151941d0014030 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 349017113 1250 349015863 349015879
    0x10e161a04140f300d11030d0c0c0b070f03060e090303060103090c1505071b0e1801060b040320030c01141608040f2313090201021f0b041802032109 65
    0x35050004c400e0000d0280c2610610030b050310b68007180e1054049400010300000558107080b108130300100582a00150320301000303a00c0b900100070071112480940143d1850f140d40c4030101c0c1d04d00c80a01690303450782c4070703d0240900c1c1c0c0400c002d440020080b0b991082003442d0020303107101c1c02e107403042c0c2645090300f1240b1841500d40320002c0064004004241c3c41d030066048110144d41e04560764003480e144e010b03003005056244040742d1028a14104018081200c80001c100eaa450704c01301285500941d00550305e070407141180186850344c03285050048070041c0c1c003a20b98903410400290005268095640b1030103000100c480303041c0c0006640104499104810681c2c1c0d541d00c03402420030301d02038015150184440040158002c62480700703401460400b4101707035010540700385400010080340c10240e056001c0c020310483d001c10708002e10700c5460b550110004c0c1c45180441404102c8607a401292601d94441380000c0c0580e030f00040e0703184135030a002e09010b01c0c100540e5100246000d608100c642151b58 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 349018363 1250 349017113 349017169
    0xa060f140d060612090c03030c21090312020c031b060f0c030a020601150903020111190503190903022103190305040b070e0a09020c010e161a04140f 65
    0xa1504070600b01e900580d41c5629800c079101341c0004480d00030b03100408103110342c0020000217000e03000300840700d03000341c1e402c40340014040ea00304040780d0300350314210010f04552814820000d1400c2c00300d001e01080d200500380448040b0200c0c1d03503444c9200200205003500404a41d15559010484248400000100e0f48510b543e0040540d40d400c05030940001d80210750010030031801d04040c4c40380403070182e56007440c014510303001903401000e85542e81ba060302404007a80e4034bd80d8070b0620041680e208000941c0d903640075409109003181c0c503030b19400400000301400c2002d66103070704501160120b50b11740b8030402d0310100400791451203000c6042000b121011808c0c0003854249c0d10061060303006107400f540302d503034000003111070140d4100103580c442210201032140c6070595019240030300401d000002e030420f810701850b16000700e04600302c0305414030711000d1200c03e01e86082010380c940b200310302600b001e0420b058501005100a181805040c2c440b180640070342e58044014039601d00401748800c80c0348 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 349019613 1250 349018363 349018387
    0xf040e03040906120b040312020424020d020c03100209010c0b0403030b0f22050702010b060d060f0902090102030a050c010204260c06130303030b0310050106080106030b0f0a060f14 79
    0x15110300c008803480c00f407001410b1103800d40304140b1503611082d5080c45035076566081d84c0c5071f2248203641d0703080d40d400d00011958400158466004a0700d221140d103800800620003031400340740010040c21034010200c01c0800b030320b001a41140e2042c000341d000d82c6904a2000481c3e1342071180501403e4014034800303110a15030581c0c07040c0503101e0180c07140b1030411020b80c18444d0580743c01000790030b20f0b40b82d10708568003569a03070700041e0004110320000c144415072400060003608104294504d072640c410040112080e4000045c0081c211244250704203100c480c0080e40b280a011000030a225000a1500407444207504542c0540f500308002c0075260054050040c0301300001001c50350900c80e1258007d400c2c40e090042d0745030b031220f401a001c2041d0840c0d900300e01900805081e5609445801d05146a2203190301989001c1c0805a0751524190316201c00202078074219480c2501038240c00034001d101d5214020040142c942e181007070361340e11a4044d0101d95a0004100001910101040d0101518 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 349020863 1250 349019613 349019617
    0xa03031b08120a11161112030301080f010b0405070207030b07050408070b0a020c04090b060d0606080111070c0b03010302060703050906090d0c0515040f032405070201051e090d0305060f040e03 84
    0x3e1038041c1c08101c50741400000202a04c00c20b903ca00510134904a602c0000d24403120120401202914807025400d1020ba4246940c0007a000460306800119000f406104244200c0107540000c503418022414642c4000e0f4540e5068000900075080305e00018013010300a004a900501100c000c0310040e0381d9980ca907000c1c54100b07620484c0140200352440e0030b07514140c0295070a880e0040c0f000c6120b13444ac42c040114810341c042c003c494079511440d00003404c090070702c180c1070010301c49110248e41d21424a000204034282c2c0c1c00520f09014140700600150300c614095500d000e40c141051035440b2040c1c800500c3c140101c01006d580304080741000000c124104611008807403050b1048480c449074039107450701c68000e40c00354010000d4120010000702c0d110303031040100d209292003010141d10b010f501300d4040d544d007140d400300541c2d1901c050014a012480140c55108031200c681d1885081c00c0303003031584409100003005c08041d19100802e40785d41d01c01c00039032402c00c0010800c0003428910090b60f91a5 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 349022113 1250 349020863 349020871
    0x100c0506100e0f1510031814060c030702030304020d020f0306042105042909090f040b060d0201270902280c03230403020604060206150f0a03031b0812 66
    0x441d289010030705070440f0384200c0f03008040c00102030380c042c20703040c0c18807020716030040340c440803d51100206102444206410540c007401864506000b0300d42141080c9800782c017500902c0915400c1007003100d81580031041e00c1d042a4121882106c0890030700005145240805040703034180a948244010844c2c01d0403401014810716044040340032101c21b00340d92a00807482001c50350380d046000305605001006013601c041041e14405414a00b003803020400e8104126880c40802240c0c109000910800d890200e500401c2194081d5a10b046030380000c01400030f10f00b030108102a01d2003c800072036100b506040c0509141c820071511030146c0c142c0c1d0605620f0f01c10311229056881c12031199000d11407900d0030a56505134841d1228103480712010980352142043c00e880030700b001c0c080480140d5800340240001c1600c1c1e80205007a050030790129100b6070b0a011568411038a1702c6090407a42c9614081d9822250107041c220818111400f04451141248100034803801002420b0711040000900050003 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 349023363 1250 349022113 349022129
    0x20301060b1b0714060a08090f0105180c09190905011d030703090e010e010e1f03030f1d030705040b040b030703121e0e090a1e051803090d02100c050610 67
    0x9984c0c0c0721415007444400c600c03050707000726080069200503409807203101e0308800c00b10200c8988628400490f401c40c0c000303030b50700039083c8400314a00c500d060b410004a194102d007166940032070309000004001140e608004240b2540d02c032403200040c00400e40c414140080181c03844c4200303a055001c11078890340408000c4002c12840e040226410307145144e02c9060390f07050840f6030300517400c2040c9082c0008005081303454401660b0042ca945d00140b00d106401103100307440780c8401d04941c0790064120565070140080c0060341d031340e008186690004500d8121070054030006030480002000c10040c103d80c4010320707014410183c0000400104500d1071405e0002a40d6660f43c0748807034540c0300201860740c1d00090000301c4010710602c280c6000c0d02c4494020741c0a08002a03134506000c040e080c41108581c0c90760071a942c500802910700d40c0700401e1800343c0583c9000e10302d402142c070005540c000c028000030f4026540410500c01690060500c4500160000200c80c09032070300d602c0c04100c02c00d40f406030a0b0 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 349024613 1250 349023363 349023373
    0x304030c03022a130203061513120c23030d1b0606121106030c120601090504091b1a030c0703090b1306031b08040b04080d06141801030c0909020301060b1b 68
    0xe0106144252070180300028429142072403400c4d402d0000342c014203500400060002703c00550b10b20a10040550548514050303040d9170710b802d40c0c800240c0454600c2c0410346004000f040c05a6401040080d40e014850801540d035a80d023100b000c01c3c40c09103c1d00103280c10301d8000f012500c400c942e940d650340503204011071a41c4807010420300005000640307149038140d0701803100390b03c401d4815140903484107040c5068812596901c3c000380980c2c0703130018207541114410203019445444108000d001e09040c62107804201c00901e180c07005440002c0288808000204107001050302c1900d80e10020310881d0075a5889200140e90310400030214420240440d10344a50031401030040c084401d903603881e680303811080755655181c030080341da0001c00c11074a1761800c10030245104018070401014101c801604500c1c080c900040c0100046041c840c010070700002c2004200250000c05980b080d50200351020400d54010301c04603001d030189802080c0182c0004c15080078949d40007082c0b00310200340100702c0d5 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 349025863 1250 349024613 349024639
    0x31a10020705040c0203040f03120309020405070e0909031608030a060906180b0a030804030209060112060920030c041e0306050c03150a0b22121101020d080603030304030c03022a 78
    0x2c1e031b0301d00c1a17201c0e0200288008800300045512080050160340b01410041440c407010780c0010111a400c942c40404a46400450f4025060a6003400d03401000b500007185840c9616442c80300a59224100804000d80000011004002e542160f0f0040498240c00c1c000540c4a400040390306016007420342e84903150149045603458071400f00f90031070760000381040c0307424255001c0c4800c07807000400c510306000f44190200384001c028403400005140b0268000340c0c01e8801c40000101d07882d28003071002811414414800b06da02d41c04200c1e8110340d201a10922441a81001d0071900105075101614851802080002c0050003200030361080c004005080d102d802860204924001e80d0b0144c04400c0300309114404404969503401c0d44044416040f24400e6941c89400090940e1003101c00c456074080046020001c1d41c041045240b14585800c6c02059841e0100100350740e030100034006010000052000f5007494000c0c09202c44441c6a40803544140b000c085000c1d440c4845506654061241c6070144 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 349027113 1250 349025863 349025867
    0x90312051302040207020303120109020301061103030c030a2007050c04050105010c0c0501030513080c03040303141908040c0803340804180b0a0e04051903020c01031a10020705040c 79
    0x881c07050100002004641c1c0e5641c0030302000390400541241c151204101c3c1088a05500d0b072120b0003440c0010b00503130381e9030500d00000c3c680489040c0b0a58240e000b8418080d0164804041d07952040e0040030000c2c0c2c41c05140c80204c00c840c0d80c0d201e4043c02c8000000e00c0c0040c400007044030038111405450030322160343d0b180f0044441441103030780a00002100c075010300456103e078004581003079955910010a0b40f0320f8642c010545d0040c48003803c5580001010410150401d80e0011520050740c40141880004c420300e20a0038120b081c8441040a51400181040410640940949007000031aa2561420a0f110f4000c040100611100e1520682e8480c2c14a07040e0b8140002503600150702d40c201443c1056901c40d4407009881091050b03103c001d450000d484c2c401c0e0740001850010b8400140d8106424a80c1c01c01014040302d4013940480c4d20480080784e00060100201d500030b10f40000d582070052486105141d42450341540640c5203020040095030014800301074800442c0c040003680c0c0d2000003 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 349028363 1250 349027113 349027121
    0x108070807020a03030b01020f0d0305010f0b0412080f0d051501090e07051804060b0703021b0405070c0b061f0f0210020903060601050708090904080c0607020706080a0c03090510090312 81
    0x100740050b40403402e40e4002074480c3c1c014100c01e810600481e5900308001c3c2e4211700f8040c03090407250001366904e0040000600555a2000800340d40c51142d207054145452a0380703c5100940180040c00c0c00182110344074841c808440140e0b02c0b990381003119007000d80c90b50310a1409040c00b82d000616800020521404498503240284410340340c103413a028004190030041001807011541c4155130711400a1149810300c02000d260f80320703902425401c02015006880300242180150259160104000e00356820007903040e025a00a1130340c1c60b591361448001980b80d04d02d11140071394000440140c0c1c04541e0884050882c5848a400ba51401d060b03804000040b40100c83c071165050340310401207900e55024400a00c401401215040d2a013084a0082460b4990030355007116009000105e041c5101d07001c0c48141d1b00544a4070140c407206107040f6005000c0c02014040000f0140e0714407040d100217000703900c1310031802e81c440d0a452841402080142c014071030841c0030f50105500300250481aa02849 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 349029613 1250 349028363 349028371
    0xf0c010c0201050c2b02040608061906140702120d0305150306130201050a051e07030f0206090c122802090618040b0c0f07050a050c03010605090f060a0b0a090501080708 74
    0xc126007000d0b4815030740621416241d00b445c41e4090070801e142011402400207002400721511580840c1c00c1402c18040041710030101c0040191501500f13009950740601400700d02c400040c0b41e686c403102c050000900c481440c8561200c0b91151390300407074845416422591240f6900d81b01c02d45040303040e1062540380c00d01101c0c000703030390040461800c00660092028080e03038032442c41c000f41410310118911940811140d40c40d200440c004c0342c081c1c20941d005c04c0c01a5200110303c0a0101402c0c0030404595035250924401e03c96000d00c40101028241008041019050a854214224926a04017020520340b201c243d002c1c5400e0340004100b41461761580d8084020000c0f000115569610303800c0080901a00380400c0e81402c012040035100b060f030181c1003442c01a8041c00c2c540301d451810b10b01d002072a05180e40685d040000402c180c0c0d03100c0300103c0c4d1040038000c009900303603640c40000d0040c4107907030800002584049a00840d1560110303900c01035a0003030301c400e4840d0b203d5000558064104503 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 349030863 1250 349029613 349029631
    0x70f17030d0509120d0912031b11160e18011b030e1c050c06070206010b07170409050c1306020114190b090901090c092c120f0c010c020105 61
    0x1040041c81c2003580c0c03040340e1000200c4280c2c1c59000a00715000724981c41901020185501c1d88810f13024890340c00070383c1d1314401050408001c1c404507081d40d402d0301e42000801d6800d201c81811103124506040c410700d0280600101c1442401d6100c2e0f010308518001502c0d11321000c0101e1210b240000c00500c1085140c0c1d001408488081101c0b10044003c5c2c854403841c2c7d4600d0140c10250700444140d1414070090386401d486041d00e69580050745460000c009140398210340c01100100b142d4005507044640307450f00010580c4121800a5295a403886160b0003034030483e15013010016280c1c1c3d4140908405001d02400146190382e03500704a00740c0f40d150005030b21062181c400300341187d0254642d80b80f1507004010100f11070199100141c0035000448031b200e2035944440102c810885d000c9810009481d118808018880c800d80030082c0f03280c680e82c1808900c2801c0314801d00800000c100200c407040c10640180e81e10303d036801001605801c4400250340a6082860103a02b160060081710302c100551 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 349032113 1250 349030863 349030867
    0x18062f0403052508070e0405100605100c0302030c030f04031203091e0f05060c030a0e1606080426090f040903080a0f020702150901020d0207030309060302030a1b02070f1703 76
    0xf403519880d20072481c1d804003c20400101c000550900280002c034010805104c82c2d104500d081d08015040030781c400550722419180c144244032690715400c038014000101c0c41d028500159500d0305a00d140300c1e840c0401020f10000c140c0320b01002001004209407071080d910500103800c4d019081c1c040d00c000740c100a00895000e03c030798040125030000c0c3c41210b801040074103c84140d544505e4103110055440840b000c200208001004466008040709003c40200608482e2804c240304060341c80c5a009510800440e90041414020404600c0d0004135401c00300c522010300c001078000896110641c218058010302c2078a000ea481c05104500140741c15495095440e0b60343d10842006003840f02c03060010030790a200e19000f40c5c80300b01920350700305d0b0034000c25a6500d80c10400685020710900800c411980200030520000b5401804901154814200582caa4503155041009095880c42e00500c5070182c07002030104c140d00060f0141201d1f04c802c6040070302c98940280c1c107029140c5c28100d001550003 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 349033363 1250 349032113 349032133
    0x405010b030c100801090c03090f0605150a060c0803060103140f0105192103020f12030a060909020607030509011b1b0b04140f0d0215030702060915060418062f040305 73
    0x740c0168a0b401d08912340090001059601e20b01240600e00b01601e8807a81c80b8200030320208580c0c680951034204541c805040c91401c9802881103003107900c0109003503c00b00201e4216402504280c541c40d800d28941000d610340740d84a00e0502e282441418410301c01804012805805070004c07206a401c051a54034072130313100c22004894040001c034100c0c00c612404008001601c014040500c6490300c14603881c0d031380d040040f003210980725039800500c040386c0782c040782c20010390710b00007100c60141c0e1500340241c0769a44000180c465800070302e446500c0070042020b407010840050100d400c2c0404440181150948801c0c81e01100d005902502a10017003001204841303150220008220303e4004062006a1003603034046245076158014131440b032900071040c052015010310585600003000001082c0300300b200040c03581c0080c4003414603402950f03251605008041140e0320210400d0b00801c0912842d286a0780f1000040c86e94a0179464541d80b14070400c01d5101081c04072011650498003c01400007 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 349034613 1250 349033363 349033379
    0x150302090112030c050f0d110d020d12060b03040f06050a1401090908090a061e0f0503060f03030d0c050a0306050102060c0a050901111b18090a03030c03090b0405010b030c100801 78
    0x40b2500742a8140101d44580d440041d40030019504404800000740c0541c00d1342c41c1e00a00035031280b00b400401d80c1c07c4a0050088154002805030340740364180703010640848901120b4000785101d0700181122f14001081200b48001d8119000206100304030421150740d40010a02c04c9030310141d08065030780041c40040124139841e0b000031103014040d500d040e16184182e00010401021a8020b40c04240e2200c20303040320300038403000c084840085007004040340041c010300416910000381828400c0d03044282c4240c9646040007540c10565400344104010b82500b2006805504042c00d410002400c0000114540d407011030014058a02c1055150500210504c1559a0f80000b003040d810041201c40c1c42d0000230003041044550b240c402e0036054280118001d008400b44904103c00e0442801c1d0148080c603280002d01d16200c83e0140b800054603800d4000490240c00c0080c00544404110404c2c0800d210043d070003003180800880c1181c01c4a0040800e200c4545075407030101001c501c00a0040204213 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 349035863 1250 349034613 349034639
    0x3060d0201050c19150e0d32120105030d030b03030306120f07030c151409040504111e0301180804150c1406060f010504053007031202011503020901 65
    0x6490f200360380b40443d41c0c080290000350035030310503100c4611203500c0c0c0c80013200c039103e189480d2409102410401c1c0800384003030242480c0075040c0340007008480c02404a560340481905007800103002c817940d0b07259010f61031030040d0020300070b880c820301801c182d52030254024441c8030001e0340068099411a6510340410000e080c05c070200b11200e024a14882c9041041841548042d5124a03803010070a8207040b0500c120030100c0c01401c05014400e004040300461080941c0c802000490b0041146c0e82c50340741c14000a102460201d03001b40c0b00f00880350f0310014803002c09641d558294000c00c030303a880c2d03581d420584080a00300035003c610208414002c03000170100f107002c11001ca042180d800851a9a11501c81d07c0340c0010f08226007181050019900d000140700101440900c2c1c00c40c145410040061023140600c041a482c000d030360404160f142c0765002280d58001c81030000d40d480c1d16582c0c2021040040c0015050340154030f4181d815842900c883c1d034510903a50041e100046580c20545299030803 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 349037113 1250 349035863 349035877
    0x3060a0e0408040305030a0804050706080c0306060705010b13090204050c070f0f06180b010302180124020109020a06050a0801210803060d05100b19180203040f0c0e1b03060d020105 79
    0x340c404000110104001b0001404000ba0310f0f61622107034542810002d007441296000b4904011109052026801d10030041da030b0010400c80700075603140902c1c80c0103401016419203003600008030300070340d010380e44c903540c440d0301e0341d0707009940c203001603501d45800801d03c0c802c07820004d24070002d400500300440d460031030481c03000c0d100d0031000521003c80f0900c00c8072001c52000498181050030014003c41c1801c3c41e25080612032002120202c0d410100b66a400840d00320001c3c40e2040000d00c0390001c14802d4019910480e0050b00841480c1e440d040000c2095000c3c60f60500800c00c602c0002912a400c0e07004082c4a030610509c00040a80c0b5079529510f651018122030b0340003d07403d61200218105011400b003140001200240c1e00384884148600c00100030910a0a42030b54003040111260b03454580c0024401c0d03260041e81d03a602d40c680040504550b00300a0644020080080b840c0f034408a240d0340201400c2018000c51900304010361014030044841d207401001180843e4010b5000b40090202 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 349038363 1250 349037113 349037123
    0x111011a0a06050408251a0403110402071203020c0a020a0e09060f070e010804030e130b011b050c0d050a0c0e190207030c06150b0c0105150a03020d0305031b0a050d0b0603060a0e04 79
    0x301b41d50345d03c0c112082c0503401c4201015100002810001c00c03c0c80c05a0325800641600c0950034503520352a0030790480380082c0414181500020071800e10241031081e0804150300910700041b468807491a280c0c0030b80d0440300b078180c51040c4c102040c840b409a64240d032040d44035035158854924044c00455900f03602804c105c007030025050740384626507034480c10069122007188000034000001d6000520b4072480ca03c0c840d03c200ba41f13048820100d20081044448800180d4544050341d6042c80d140307250054441c000b030a0101054030200310111541081340c0500010000d520044d0884103003102240725008000b030200d0386c0c042e017160000714140c001d80c400c1100003000e007251640d0307221b41c81c520f03521109040000341d550303408000500185410354180b61905a58180c01d25055a0103c3c000c030124820103014000c01000042c000c034180c07071046c0030300c01e9091507407515891035180103481900244114601a428030101c80e40700d00f080c00c1540d01c0f84400034610b10155242c05460690b00b40082d0003a14 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 349039613 1250 349038363 349038433
    0xb0d050a0e4204050d03200d0506030703061401080f0309011d040905011a091e061201150906030b1605030105060f07171c0501060e0f0111011a0a06050408 68
    0x150b07140680d4007184034038015006422103600b4510700030100c0b4400314400000114218610b003040c0b0084054032072001200100054607104d0100103450200c1561004000508200040508120a2501504940c5080c003100e0030050100445a00c90003947c0c4854002403140701c0c0c580809038800c880c0382a211003d07000182d0303031465444290a543e070344020840c1901506d030204005040240300243d0240c94586805110360002c8031408030042c020b0807152048904d24a1700c00914001c0d8815208505810b008602d6555a80c44074030240c42c9a21041c3e944044607000522582c49481c180188184280d5406146a0808041290301d801ca00d039001c0440d00f0a00401c1e001546070b01102020301690028140c031f0700b030840c1101c940452a40a0f0844c4642003130010407c03150001c0f42111844001c42d118600c0c04c05207401290300800405c10544c1c25030070042e070300d5140c0110101c103d513580000e0b120149261707115101924a449248175840d215840310070080c080341042d909002180c0d1017450001c0c = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 349040863 1250 349039613 349039723
    0xb07051b030315041d0a0c080705040e070905061c151103090c1908010207060e01050c1801050d0b03030a0f0807050903060c0703020f0d0918090809040b0301060b0d050a0e 75
    0x71b180c044c00ca84211080100c030701003401001d008100715030042200300c4003406400e41340d201d61034a03404140f09a001c01074441004c24210f075140785804407095081360b409045200c0d14180603052042e14540720f12000e20789149403088601c51400c59200c0e5401d07030010305a40215409200104110381000900502166008070b0689000e000520105001d84400300d104034210a6107421160081e00c0c140801d8000c0040078410712202502e040d1081003401c0540d1242980681d40c00549030030b243c4030ba031500000400d030076000d800014081a0700600e54a4005950711140151458404c02c120241c2c03640c055000641130a07010001400e400d1702c03034416200204c00142540d464450850780785008140c0324032017803082c20395030a0710052040d0b0040d000d00480c41c45031650701e41da2280014550081d17403078079410038003a1401d4008400501048100729a01d41d4403d5090700140015a8040c10042c200203040741880703000944071142808150725203c0003041c2c090365511010582d2106c4840140020f603071 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 349042113 1250 349040863 349040921
    0x22021e040c02011506090e040809010e04020f0c3f0c01020a02060f0f0c0f03070e090112021e0102030f13090501182004090e07030b07051b03031504 65
    0x1c11a0680700d4002107109541200d041280100c80c2e0080010840100e1041103070001c004107140c3c0043d0013540080e0383e0407000004a4039241441c10030341d04035000150092004140000424421083c20181c450313410340c04190f4820715030501a4060440028000c11b5600d602c41d10350354414110b24007445181030b08218a45081e600314540d60f170050b82008040064000040c00c0056210204151900040c03a0045002c84180105099080301c004040b00056429000b43c0d01040900f5009144107000d40e5501940520030031412001c074015034002c6850209001e0b01c94203440d4125058024504054400805488540103038007800000040120001100d400724818075004e411410013141c024003e580e81441507643d01d0308041d030200d942c040c0c0c11142d5040401070306e050721660348000c61501e440d81440d0f440c005a0f50809040412040c0620940b03940080c001d22a055401b0114800c03000e141408507228001140c0e6810000341e400208221490306034070510441d5000006800031901d40140 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 349043363 1250 349042113 349042121
    0x204050d0c2607170a0b040b060411040302060f0310030c0305010b010807020a0201020703260c0d0207051f031e18020f0406050f0d031407060b010822021e04 69
    0x10030341d078035a0070305802d1046910000b0044103101c5000700c03420086500d00399842c0e0301c48092085030f000821042881032954001d10000030119000310040c0c3c0c640c1002d04003544005070590341c1c0c42c403031841d04800d0650104004d0569048980007012141419000c0321544000e07440204070f18040420041b0100c006130106100e440614001d0f0000a8241072100001d08003480241441c0c05540c00043c820300140c1e40003e109007600d0340b001040070882012100c000190004205001041c080810b5031506000c0021f0142c861b008241d0848074a40e5a68040c040c2d03d480d01c101c040d50386422021a119854001d40180e8144150310080f00c40e46012002018121000401c40c8100640059180415442c10200300f2031642d02c1180c0c2089640d180800045400700c01401c1103002e44420380c0c00d042450702404c6107983c004a1507035560f542e030355180740040c01420100c1f401800b150240c40484c0f00c5800c0b100d0f1100031061030f9400035401c05060740802400c0d12008400c1d0b403411000010128a030740321401 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 349044613 1250 349043363 349043389
    0x21070b061f08010503150103080931150506250c0302060a08040c090c0207272408030a05160c051e0a08030702030c01080a0e060c0301030b0901061a090103020405 71
    0x1e2802c0040d4107001c101400c1c4248001e0711990000402c00510200d4103000031540d28440c01c41d552448140803c030240d0094100c8952440741c41d1550000c0c0e08581d000c3d0700514184c00144001c012180c6d1076008018032402001e181c0c03188202d000d03028910014044041600c841d00899144980716580c0d400038016600200c800741c0061142d4040c04100442c12300400080d0010030002c0c040366134041da000b581c0d051940301d43c00c200d140740310050710001c00070030a4000b4004512024005224000c104596201c030b01c4a69081c01100c103070380007a0700000401521004030070b40d5030305c0c0d281079100c1c10802174401035000103554000e09644001155940c44002e4524440143c03400700301e800c8503804101c2c0c100403c2d401002d0680081140c5070041e600465000d040d4002420050b80036180d4880340b500411009400840d2071068000340440307104600050741c101d038822076140d004e5640352507405d82660315600c9200011503a42d08ca03980002480c0002d000b0f08070040c5030050038180d44000241607580300103 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 349045863 1250 349044613 349044617
    0x1503071103090603010f150f0e06090d0b0a0902030f010603110f04020d0501240503010e010b07080d0509060a06080a050a12110319030b10050409020703030b060c060921070b061f 78
    0x41c410072034004031000c0c203200c10080d402c0c08480080144000b409d0200c8901480d48514400030701d14405541d0006410341003a0028000a1140781411500c030041c503080006a200748030341d445213410a441400f50005484d485040c0105656035001401540e0f92702e2100154060307001d220070702039200144102c5009188070312409070500d03096107040c400803a04450703003000c21078104011b00c62505203440c1e26044a68800c48655160700d0b50502c80d8070741c003540c1c540c0b0302201d0420b000d124000c50000f0b10140140080703034003048400d0b13075080d505a81d01d5011100400a8101d040040003041506d4150814090b15017410a040009910702c0703810341d030040c084261075451640894020540c148102c8a90201c165a8960440701542000e00030707000c1c40c4070f80701c0394540015054081506c0707030300503d1010002034030498031455000f00c0181c40e01c804588180c040c0c81081c5142d00081002c403c050403441c00380d4107241c074008040c0c8030345600c0403004003103c4d0041c01080808141c80c1d422240074281030019 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 349047113 1250 349045863 349045889
    0x50c0d0f0b0a150504290a030c030606061202030103150b130603050f010507030b010c1401140a021902071503020c070e0907080705010c12030c03060506040b1206150307110309060301 80
    0x40307100c0c07a083d6010342c12a40c001c07898900e42441d40e421543d52030b0200b4041d946414040c0c006035000801c06070007600002d02e86402c8400c000100300032070f00440c0a541c02c6407600d00d1010301c901072410890109100c0540240c101d040e100c29400516401710040c0c4601070010300700c0c0300b00d0240403010348405a1003100c0c0356110781d080254001c028032419800c2143c43c075050040c42d20010009150002262004c0d0484480d00b0381400307805001d6000011144403070460010526010045200a4115503030702452510f100310741102c0d0500c003040c2981510544c030110900450000000c400035000300888040500c20210049070108000000d917100d4004040180351281c28800f51508024142c0d0006051000b00842000010142c0c0703144c040503012840c0018009542300401c40140c2130591100d078000c0340018001c80c400c0615002410381c1c001141c01000184c85070028441e52554104c01988620000d00101d00228480d220310200d4540003802c59081c42d20010003d8520303842a4445400400702c = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 349048363 1250 349047113 349047131
    0x1812010e150603030424030221180604020901060315030c1511010b0108041217040302010c030c14091507080f030f07020d020717031e030402031603050c0d0f0b0a 71
    0x21002075902401c1036001c0e42c109440c100c440001520301509034034550600340d0700312881c284030798166411071254907801e4001c001d5500003c241c40c90207031100900d00c40084d1010200003000a0900e00507035010b4042e50b0381f40e18104d070480013080300400c103282001c079030b00c1e000010510410085020300780f808014001a00018406170240b040d540d0706600c242d0420150900c944e03001030403990b1003504034007121030348009a9001c845800700780d42e40e480600b103188240400d140c0e0540c4100d61280302c1e52800c03c5030784400d11065880d18000389845404905c20810140f40d4202125600640285030f020785003064816503d03030609401c0561a51414203010042044440742100955005120350014090041c40500003c1d22041280250003040d0b01542c5074465540f800c108503280c10b0100e140b140c0d05061923010340c5615503c295400c0e0322034400c03803410802c024448141c0d0b404a03503002c401042c0c03844404050160030f17010034105036031080720340100703101165070540302a110701040c2c4800104070319 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 349049613 1250 349048363 349048393
    0x71a0909010e101e0603050601051b102007080c010e030f0d0b060301030f110a05101e02033112140d140d1107050a080307030b10051812010e 62
    0x140c84d80711061030316401c25810450a90440c1e4042544c032285030204035540c0e68801a00d1904c20760313208018800c1e0350483c4407915072011400501400000c2011701c0011091000c407404100b840c03c0041200d0420800305002600000007031803044660300c00802c0ca104550030040c11a0421008004400000101b10f0b034942003c0c4926950b1810440d5214210350460b1501d224080c54000d0080c8403040d280411349095540300f0140005110040000e0300825410f500184a880c1d0f4100c007480040722402010b44450000c004d80d22421180c0300000018051004001c52100c40c1400c0c00ca1244440200429603040020b00050054000c40741005111004590a07123440c4032000410304109000102680070000202103880050800740003003541e8140300c41490461240b084002d21500c03035014036008100350342014511030070071628204440a8401c051102c115601c0c240c41000030070801c040302240601a40354600b289024152001d070f10b0b444413030303203003102c0c813858803840507a0003200c060034418 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 349050863 1250 349049613 349049641
    0x3070c0605032404090c08010e06060901060c0b0a020f0d0912090e060607031707090302030d020c10080c1b011a12030d0c020a12090f05010c05071a0909010e 69
    0x460a86000703850340c900003104207000d000500c2600b10100441a21100560312a0000e0814540240b85504415507460703526000b080702c0c0c10001d110740666400150946000c1400c28102c48440d1a0001920510f555919154800401d640c00030355013409005107680801c0301502242c000c034a00026841020b0511502a590040f00341041142c840c0080c801410941d00741c0341c1150060f1490794841d1102e04d8180d50760500304011207100303114081000744031540100c605040f24000ea0507510304514000c1d040741c64002d2961b00c69000000c60034a082c1d083d11860301554428150048281007104425280152903080280c04046a45421600224003031490380d130b0100d03800032a010040d40150b40f280d280c60340194510340c400156501c5a000005000784410b0105680c00980c0002a80500d00e000d00000700a019401201c0320b0741c00c001c00c0c99409000407600c031039081310040c10854503142500001000c500008400d818040c82440c07809d441d40c8401078041d1040319a001031624100800400702 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 349052113 1250 349050863 349050869
    0x9051c2a0c0b090a0603020c07050301020d050f090303040b0402100e060a17150f1905090a0c020d1b0b072616020c010807050f1204060515040c090b070c08030c03070c 73
    0x21010008000f841d6141030286085030340604005d030b20380c100c2c00e40b0242032580d25441540c0550000990f2520461158003032445100c280d1481407681e215140056564001241d009110610220108003d40381082e0082102d504502d00700c0941e18094001c00c039140c12900f00a404544143d0f40121288008240c140d84540c407244070b80718485503840081c2682c1c0d20300004034001c0441d200904025140501a48007401c1c01070450f81042c1001d20304c0400070f08032082001c00500440210040c4584108003072580c2c1410b07010101d00036109500d4400e207500d00640749000703000e0804181d01c074000c1c551070016002d4403407095601c4a4540000f51841c4250307901b04042c215000440034140c00e80e00040001d8101c44180f401a840d480f05d04080385c101c0c840c42c1e1a10300e00c041c2050400040001541105100ba030410286040b07044c106400d12040e030720365410b944007180c00302c4070900c042040d001c05040c200d4040c81c90006070a5403084503a085501c5a030706c1020940000503a4824018420820001 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 349053363 1250 349052113 349052129
    0x4020906090712021e030c0d05010b0702011218120201020408010e06060603071107080a14190203030306130908070b0115020601060e130b040c05040501030f09051c2a0c 74
    0x29850182d80c01064040c9401c403d25069038045030000c42c1d40c0000c1001d20300c40c2c900c129202da0382d080c0500c12081702c2e00709050b03100c05641000004280c10311844152508a581031719441c520010b103010581c06002e03004464070b14440e4126503200460f0200002c04000350145e000140e40b54140000942501d18a1a103c04075500c0030342401195102d50040fa40d009030645040d818903440e589440e8249219903000c071a0b0b40c420b0800396020320940e0540c55560510301030445612422008010060400042c030180d899003051001070254109550380c85c000000ea0407001410085594602d07403507400040e400c0d90088000001841450200c074901114401d050005144640c94020000e04040102c0708443c0a01d40c0c0c6180b203e1b8603030306034020030f1a000004000f0300814140c120300801640091041c540080e04040c80c02c1e0b248051031080c4c0100540107405401520342c0000c511003c0c00d4500003040800607000442c2c401000100c00c052a00e10070620080c403d55414188241d0300c1c01180c101d541 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 349054613 1250 349053363 349053379
    0x50103050d0c05190308070806010e0307051c0b09100e0a0f11220f05010f06080a05040804180b09100e0601080903130603200a020a0b090102190804020906 68
    0x40818000101030301c90842502e0040760002042c500141807a0388500d20400ba1a84e5006001c10160040c201a10030400c540d54a50303641d45040045800d100c1480c00150180c000e81c80c28440e6042c043c01c03625040c0005444a80d150b0055a06c8003d801000c0310074911680010300e80c031101d094103000c0c03488040f045000a2044400310f8a80007050415200c00514101207110700d402c454a886911141e0800e202e18144801c1c00d0403074424000c6e056021070414240e1801c070003c2100741c010741c1c3c48800c5d10340c1c1b0b59841c2c0d640c2c1e5546400c0303401020301070b0050b50090010301000542c081252a0b61642680454011034006020300a105503d600034009041d00204e200b01402541e00c0c40442c1944a002440c0c0504240c0f0b0b03400c0c01a0541c410400445029400c0034800705806805070008514128284807034104c13418200c503a503400e0301403a002700c00160072181d41000480c000e841e1a82d0041005400146018104803071102e414200c091440041500d408c104025807030002c0300c1e50341c04101540c6070b030 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 349055863 1250 349054613 349054619
    0x1103011b1b0312020f07030305061c030e0a0504020c07080d030605130b0d33060803030c0a02010b040501090f0e010c0f11010b0901080c0a0902090a05060d0b0429040501 74
    0x7070308010285580c8801540060000400d040c40340c5041034040c111040210b6840c0c0844412000b180d0010100341c01081c101030200b842800c20300f00386101510002c40d94040104150307022580030394043c1034107070b016071411741c080b03010f5507a80300620004010b940141210791030008918185100b498803101030614080d010011a02d0341444002030055001c030004200c10100700281a2201d0381c903014080c0952846d11820380511042c01210001c0f900b0b81c407600301d1f440c021040069031118080e104040d04184003040c003002141c4c0242c91559807500000c10307115280c0e00880c08030b4509a1106201507210b1001c21809001c134070500300c407206120006d1250030840c0002030441c18111001d04104611108104980242035001d80340c003c034018800707003070746d40d5828031076568080c02030b081846100020000201c43c01948200d07021840040c040c108003519001c10000701d03401c00a000f03000a51508040306465a41d8820000620071294404514090f290741c1160102c83c003c07000c2d80a50314000044c = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 349057113 1250 349055863 349055867
    0xc0f0302030a15180b0603070911160317090c09130203072603040e0f070c0c1412030d0f180b1902190518010905060307080408161103011b 61
    0x540d004542124954003e01003050380036000700201401122198500c064440402105644084c00361400301c00300c90a8540f01c104e0705007160451b04a10f003018908220802c1400014488500302c503000c3c0c10110705034881041426079010080380d003002c060708210101c07211468442c000070380107800d041405441c9059580429501c903114000e0221141c080725480d40811400300c01c4a10051418080d81e48442d52000600501d03032090703500c000003490050001d180035219000450003039802c01c8138110304e186000544208100c0102e9416006111100b1909240c10b040005111301d403642c07100000c920f84007184039030880c0c6000321515101c80074041e4000129443e000d03140c0c3c0020b154140c035240d5084042802e0003e00c1014605c40344d52500021481c401500f01d00500031401c0803811481a0a034400d00440b50500f65000d02940001c040c070104080e18440c16481e980640301c0c00e41e072490613111884c41c0f194080c110078100c03400c1138024400740d0141028010030964003002c000303000a00c6110140 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 349058363 1250 349057113 349057123
    0xe04020105121005030a0b0a0b0f030a03050a0203250203070e070f05090f040603050303010306050903030115080a0b0a0807050a0e070f0f020703020405100510080c09010e040b060f070c0f030203 85
    0x2821865101800c080380d40c0f40603401c01d1600400c03004045a00c003040b945040c1416541c112030030b0b520350b89409034402050030220718034204000c6c020003412581e03225507415107498000c80000000c41c40107220318500500141821080d4542c105202c0390b03120f4480c8101440e05901e0380241d007041c02120144a5901d400c4003a0100185250030b0040d00c401d98200403e00d00701040b05029849401c0174000801d01a001c0000c0d03059074001c4409000560316410284d549120030300c660f1201c081079085120216108501c00e03a0486044400130800304100c000003190056550816102ca4006c50010003a900c0c002e07040d20020808906510f003c5c1ca446900900402c1c80d031802e80d018000001c0c0e42c52200341c424040c0c00040d6038024001c100c503042100c084030000401d030003440d00480b40b0001240045005402e21071040003030004592500d45041d0045494211044007150000d485820940300b5075a110043d0a010400381100354403441c042c01c2400b21050b265020400002d00d2042c14400342e240424 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 349059613 1250 349058363 349058377
    0x207080903370807060501140102071a07030f0c0507081c0c02030613230d030b010302031614120408130515090d14060709030b0c04050a0905090a08071208010e04020105 74
    0x3120b039003040c140e810610094440d2440080c502460100080350a10f0f05c0010f0801c0e100c800e07421a0b00c0c15803100c0480003090a40d0303103082d100710300900c140c40000303202e68a00080d0806034039101c90648401d6580d1171412002d5000103049030040880c403c03240e0312801840ea120350302440d10301d0700101d880d00469180c14001e0030401c1c0b9444840700c203405000b100008132800081c07040103a0300d07050507850125220540140504000782c200500348031558800e00a50780617004600040001e80245081541c0b0031260680c0c0400fa034100380860006142c01d454814441c500800c40a503881c16140d1910f60b1139885c0f40c10a82c86000749880c07038607020082d40165150280160340e06481401e1031706252600640e2a0900b681c03500c181c07020050f40c0c03a17100b09103404072403181c42c0c000b0032915032040c8201603026a002d01a04200070890820211200307402054002c1c0d441001d03503c010500da15845543c7e8460102699000048410b42350401d500c071441500404034001c4281182c10254002055440381079 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 349060863 1250 349059613 349059703
    0x12011e0320152113020907180f081b030f010903020c090108160306090501061a0c1501080c240f0c0d0302031b03041704060f0801050f0d12120207080903 67
    0x20f000241e400c0d200300c44038260a40c00500340045881c0c06403008000502050020317000098915001580d0803d8a0703044090700c1d0741402400030034000c0b0200350105941e044416a151180b41c180c00d0041800784503109149000fa0701800d01a016041401070002c0181d001124651101e0405450f15030485081d80c140ca920100200301e00b14541440ca01400d000e410007079035440c4010b225090080d02c200141042411038041c1e401040c1e492103000c8600c0c03424860413450b608141c1940405240400320302048024401e062404000c90402c81180d942040202e401e000100103608100d2600401c56461409a03a01e01980b561404820b0007501c0c410304d261004807100080089010800103c4100820303401300c1c14841e8545a8640b0014200c44e900a030310004640840001701b12403d05007800f03c181003016100910300405603880c511a5118402000100b0100d00d84800c884200d600091240c03070300400156850308488401c06042c21030843d00d200a205501004840c454106100c0700601e072050 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 349062113 1250 349060863 349060927
    0xb0a05030c0c0706030c02010b1806150403060203011203090920072303180a030f02060c030c030304030c02040f0b0d0209060d0213060603050c12011e032015 69
    0x1201907016034003070000700086900419001040c441da16502000d943c1005a00900111280c2010700215241c441d401001c0021040001031540c10070190512404502c0e402c45440c00d0350b2921598201d81003a001100c11207150300000d800e16038442c1d1003e000d00001e0000308407010344130300d10f4124440545d070060074407040403841a09010803004240c80c10303501030703540c4100b2810303071000b55444c2e03030181c0c1b81d50260307404058800782c05040100d007100c245c0303030b0280301202d20410039000c000e450b0304940354080c00f9100400282d0846d20003440030358001c1d0b00c2900c0390302c011341e007910400007614040000001300a240001451860703603070071014403410f50150f50111098480c24082920b440c1082c84c00b035002080c88205503407001241d4855030407a03040395000c000540300c81030340015038411001c90400401000005015045c810a000703da03d00e076040c10f103040d060b80c0390740d07140b03001e0056150449445e4001d01c88801c1070038410703001c0c845c110103481a240741040880548081200d064911030304980b203 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 349063363 1250 349062113 349062121
    0xf020705041104180902040e070e010902071e05160b25030e04090b1605030108060c0c1c17010602060106022e0509031c05060604032907050408160b0a0503 68
    0x20b01ca040b01c0240882e03003540398140341c40100e100041d020b110002c0340105d01c0e102c19030031020b9000c190041500d0300c40380090b90903460400d890001e900040b205581c0d081d080c461944081c400400e4000070103100d90041d206488000004051005050b03002c036194079010800c000140c11210032407a91840c440000084008040c1001c0310019a00055680c0052804200303100b444036800e000b0780300c1d60301c2c200031040e460303a10f2104441c140001c1c0706a01e250740c07000e40031070b100c03003d41d201030035549104c0300031611080d025480d007074150009500da0401048400000840320001c038141c0d11701400450000708625403602c10700030342e20040d0b115481000c011920f0a0700780e5210281c2c184a410342014014004c0341000940c268903603001404280100c00b211031418581c4240d80a824031408005243d28140343c13554907040d0300a5040002d100d40604c101103003017010004220300c1400365100d81d517807076211410200c3ca40d2400c0b80652440e010104070050402c08603a5810480c0c1c100c100c0c1d403034240e4407a11 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 349064613 1250 349063363 349063391
    0x5070f0c0f050d020c13060506030105090c0904090303050906100315020a0203120c1902060103020607122106140a08030d0b12030a0e09130b0c0913050406090c060f02070504 76
    0x55280700050460150040c120400c56000550151244084030143c222070f2103102000101c801c18816150018018001004039191407000e080c4d00c000608a100d241401010008040740d43d46002117002c2a0782c0c01c14040c050740200004c60340130070800c580c281c0b002d055031103070441303540d0104c00401656000902c040c1322504c2441030301c41c00b55445a0304c00c035500308407031140c1d2aa00041034070b50107040d510140043c403610000b8414101c0e074000e40420b02e030070310649402c41c00c9000286650140b016001c03820181c482e4200041008080030880001c193f400d01314541103014840c5086440b480c0a40e400b402200b0713022040300d40c05c0440c903d000843c0c03000c00002c03602a103e003000d10303507590101280607020103822207003030443d1840403601022242d0b0340404400ca0740d030f4070001c06001070030400700150115019000609003040010a001960442d140110064030030071241115801d8444c07060104110904c00d00e140541f0160816650020981c2402595030926100d040c1c030840c1c940043d58a541 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 349065863 1250 349064613 349064633
    0x6050a1a09070225031a16050d020f0307090302120a050c09090c060703090e0705030106020a060f110f04080106050603040b0f07050912010c02120906070609060608011b030f05070f0c 80
    0x22029900b0b101800c0c60341440292000400e02c000d46e40740c154025107903012000d901005124056954441402c1821400d04681a130032032184103242e65400c110480d40c4408100185116402d0390742ca03940c005065205020901c099074401400c1a40400d041c000080c0300440c1107105900c05580c3ca20304c660f24103050798641102841c0701d80e04610005058024142d0045005003550301e40914620281c40d151401c0716a40710902c1010010b8000280d4900002c281c1d800c0042c90184071003000c1081001c0d85400000c95003d2807080301c48000c002400c00101e40c0c0be000d024010101166030600314038164549036540c0c00003d084480a0268800142c0d8003070180007a6807021901411160f03440711003184460080c0b168101600161145030002a0100200c204951104c10050150703800d00c00d0b07641e5801c020342170000b4112450380d110900460354000911174004030300d80a02540c020170890010280846103c407401d9107059003008200021683c22030103e40c0146c030340d80340c00303001c00c41c1c42d003030451500d = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 349067113 1250 349065863 349065883
    0xf0301060e07181406090d1b0801061e0b09060d09120c2619020a0203010906020301030b0f0f07050708120a060f0501020a0b06040c02120a050706050a1a090702 70
    0xc0041c4090000c02c55208125a20112030860a0220981c44241504002a030000c11941c8018200200741450914501c082c1e40d02d481241320400704803400300c000d06801c0554200f4640c50f99160010411142404199030805548885002860f810002c0c101e00d1882003400300307401550300207143e104010301503100d441e205412907212404c0c0481c00c1002001c2c040e82d40380079542c900c001412a95400e4461100400241001c1011072400805c000f144410645c0102c628056000e60360161016807803c3c0a080100c0e481500b00681e00d41c11480c000c04000c00c0541002c10303c541c55010040c0b504625014190443c9081c01c00319290381140c038210300c80303103c1c065082c0c0ca400f40800a2046c006415000070741601c3c2105144008691a5001280c0d900e4031018060040c0508102082c818145540700c02c003960b8903803050b81d581240031844000b441d400a03420100190740090b903807040c03011901c02c1d0f43c3c03c031410b080103120704041e229583d148124121000f5124841803000300d14143e000300022902 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 349068363 1250 349067113 349067129
    0x604090e16180b0102060702250f030f120221090d23060603010b010203030a0b06131403100b0102030306040f02041a04031a01050d1103010f1a1002011a0f030106 71
    0x1a1a40380c0203982e54140e141c08200d10800d0505150000ca90b0020504510651040e40200a44c0804401c07600404581c04204000200720b10300105014403444054400355005903071400c1c02c41c416240004080140e5044030045401c8000e000c2003040d050740040d000c0e1284424030649806e220b0000558582c40341030018120303482c0348148500040420400d8920651300802c0e05c40c295181d4084c1400d03200385030195401a017003040005c0018071035610917111120060f158900f0b205501d241c132400201103400103c06002e5040d000c072100e1908105001c2c0e0074a615406100d403841c2400040c4d074a01020380180d100703540301e40000b800300c1151707410f55008208030b64165914080707801441d5069030140c001510705c2400c28112a182c50a00c1144a040300c001525068200b841c1d0307100e14248540023480e0340d03419501c0e4144903450640d68010b5511642d41502000300c0401c40e00c081001c031000302c1d90804207590421401410302055051440c94001054980403416107010001900400d075039006621 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 349069613 1250 349068363 349068403
    0x10501210302480d1403160c170d0807080a091b09060e0c0702060a12020a080610141b0705040213030c0b070b0118140f060307140604090e 61
    0x5020160041483c410707045000f41a440d5000c1c1c1041c03450000900b00b0050b130080900f04040b0001040840136080036454002940d0400c0075446070f07411104001142038541811003130007400b000721402d00000f1050b4200340105804c2c4019100501007041c001c00c0c038020f0000c03100008940707200d41c3d0000740c1c0180d80001115180103299040d41201007203402146d282d0741c81c107100400e00c841951401402030750043c5102c0d090524545c00c10a141e40800d00141c00c00940344002181c011060028044810302500e40c2d1400780780010601044e810b20392800380402004083c40a0031519040440e0749800031b600a28483c201640c60302482c0c5012a4031441d0444c0c40017952035121181c1c4078004042e6442152402001540c0c0e054144090085940c043c10401c4a480100030420210708071200ba0703001c1150114455044810300500301e10102e8084d25000450000c10410b0715041c00307610042d140c400b508200841340300c400300b042401140a0500e000366660314005050100b048666036041a000e0407030 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 349070863 1250 349069613 349069663
    0xe04200409210f050301030c030f051002030915150f1e06030a020a0f05040803030115140307020a030e060c0604020603040c03080f07111005091e18150102010501210302 74
    0x2c0d03140102c0e00b902c00020114040d070012180f003030049034101ca401908000d28241103032140610015400030484580c0310ba294141003e40d03407400518850401070002d0701c1c007075900c42262246c1001c003d00c0700660a8480044600c00d80c0c9a003204104100300784ea129000110301c282110111607200307802a8044c802104000740310b0280e40051482c01e01e9584e5a0001c0d030710070b841c01d40b1140110b01030381541c4c2c0c000340010300c403402052074100c003144014501025a4405110307800300b02e91068400d4030040e088501100e042c150881800140c0e00c900355040c61506141c40d001c1510f83c400a00002d20854001021070288050200798001031030304031501c1556814041500d0030580d10185003214a04034441d540c50b03052030110722032260b0101645507140307005440e000b000601441c000204040c208441c0c10b07a8200e454403c501c84030203409140b400031509004010381809544015810704581c141801841408500800000390742003038410308010b000281380a078181101488c0100428107003085407 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 349072113 1250 349070863 349070903
    0x20c0a0b06041b0903060c05070c03050d02120f0f1b01230601080f19110a0215010b0711061303170909180c01050c0a060c17010e04200409 61
    0x100d405500115420400c2000940c000c2c641075481402d524007040001d101080419443c0e0400c1c1c000e5551450b05030310703244086c2ea40c2084007031550400e49996001460704180550104101c403690b019015010b800c060422103100301c2403248901d4000c07209004900c030707550f000c6d04070ba94650703201c40c000082c00381e075400b40c20b0900046541410304440f03540e104c02190742940141d20850044030325400e40c0d07101d56a501045c0c1240700f68a0314032000e4035a1080c0720300c80b159225016154220441d40900980d0449008005680c031044c0c000600c001c404211040020f03001028103410804207660443d1140e440c0d50a5542181544c0d00160a5140c00c04003641c0c1040048010481c942c400c480488042d2a8a0b02c814405200b22083d980130390b001107804107541d0300403005084603c20b50340c115540c0c0302c03503941c030360003680d08401c0704902180d042c40f4082c000342c450b8182a80542005c840d11100f901d46629000543c00ca031591400044410701b0403000035495981010074000c1d00039a0154106000c0d03040c0d = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 349073363 1250 349072113 349072133
    0x904020c010c270e0402030a0204050c0a0207051228080a02030714030a0c030e2e030b010c0c06081b0a0f0207051203070209280e0606010e0108130204020c0a 69
    0x52100000c240c81607404030075820385041c500121015043c1100582007010703298007107070041c20030380c1e0600c940d41c0784400582e43d50003850711801410b1140d507180c001b0303070300b0192a05c0d585800580c85254103800002c8000d000141d4142c0c040800113442e04407501a1541da002c01c182c07044007400c330440006004044c0e0350004014104a031140085488010607500020f4603401480f01d1040054031007103404005c07911030400e00707501c880c0060454158140124002004c09100300e480440315001000441801c0d815119a0020040a00309401c80e09040d9540b03c110078887e00580c1c06008404010402240c0100682d02001c8030f03070506650340c0d0740f840e000902181d1060004c40d00500c42c441c4041403c1c20078004502d0414001c000075070a00840d9070800100c0c20700140440c42948090b0111704c031905010000400003e40310b8400510711401d012102d003056001030009040c040080126019030368002c8819038400c40c0c00148e9413a1040c00c0c400035000c2d214070b40414540b403041c19010414420215a = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 349074613 1250 349073363 349073381
    0x40e07061e0314061011070906051305090601121e050a021201150e1519061719020a090b03100f050904030f0f27030614010b1e0904020c01 61
    0x1003014200605154114240e0b00c690b2070383c0c060189207402040350750515480140c0191850b0529101600304500d0310740c60101a84c0c0b2402c01552200c00401c02401c24003040c000d0b81d080440180017900c4d0052083d9540d0780180301d000a8028802010010b01510300520780084108480301070405c40241000c035916101c0140c00d070310506414842c40c41a50052044003000c080d4410310311340301450001c0c2503000c1d041c004c00201d40d10008060516407580c070f042800031100d000308031220043e418424010f2a65103c446403034841d84a080c14403240401c1100a4800c80d0301c2c02d4009a620b000218040f19100e040f41d002028030311010084c81840c02c058400340c001c0d07600008803201342958030410040604010fa80103000b1a003802031042100784a5800c0c1c50210089060060214286812140c554040030505194104c1c0740f100a004105035800340c007075150703250038404115504207104c11a0074400c224020b1036014084c2c0e60924207070303907013800d07240c196100a0046444080c5401c7e114003802c07560f1 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 349075863 1250 349074613 349074647
    0x3070812190c0833010e010e0a0306020a020f061b0706020d0c030b03010e0a0f08090d05070b09091602100203100504050109090501050c1303081605030c0703050601050315040b06040e0706 82
    0x44013980743d000403800c101c22105401e15000c4800c42e12440151030141c4070b05510760400c1880c500340020740c0c44024500c40254031031200140c0d038102c0d00c0402810300d400e038bc07503445845d0800428040a02000310340f00d0122030f41c2c81c043c80d03950b032070a1400030003d11501c594020b490b4140559a0b0041e5010380c003d821111054009000003441130508680310140242c0042620800b1072040000c91100700107804444409001d0000b04002520f03401e1901c450340d4401000c19030005007036521401e194003015000340ca8161442908416064083d4880102d000c511201a034080001509007c0c0321140314001d08000d407007007040b540c40c1c2c0c1c4020042e103015070040e5500c0d820800403429042e80c2c00116250301c020324046000003825607442c0c80503a0f000b0020007019141a10300b04012030414001003c403110458000c0c040d5070318514200c0d00b40340c4141d01ca00d1294004450340d201044a42c040c5661007a882882c5040f2039841c200054010401001c81641a110740400491419044200c800d2104650 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 349077113 1250 349075863 349075891
    0x1d03100615020d02030301170c03101509020a0e0f04061703070b01060e03060a0b13050c070b0106030b0315090106080304030b01080f010b1003022b0f050903070812190c08 75
    0x80c101a0fa44018410508005a000300010400441d02200d40c41c84074031003405560822036104006440c1c103020501c0388440a13521602a45091452240d9034000d01c4110019400c0a49000e0b02612030001400b049000340c000980c00070280d0b480d03070301c044013410554954003100307444170720762030354940185404454003003840e400411441e02400b800d4031000c1008000b0f008590b10360000c50050a00140002d81040c0e442004200407112401175910030790054644903200c1c0c2413410f0100e01514103a000130103140ca0304c5003c0d0340548020800351800c48605c4241042508c03040203c50040c4880e80c00ba1f041800003080c0802042420400c00707040701c407410300301da8808001804580c22540818403c41e071145940c0c205142c900e0094002d082400e40d00001c01501c02100c41604100324940c2400c000326959400c08000040d09600c207207504650300b03100035030030211a0f0303030340d84102d03c41c030301703950b08040b821800050100d1441e84400c0881138003402d00f81b101c02c0300c80802410040c000c2e202c100b404065 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 349078363 1250 349077113 349077149
    0x6070e0f0405060f1201021e03160905060301050f03030409060603380904030e040c02010222030b0c0f040b070302010f0b12070b0d02040906080709050f0f06011d031006 74
    0x300780241d03802042d00801100c0c140f03540d13104100c407590f0b071030f01c104a903550280198552a11040e0700030000307041c0340800c035550307240852a44400d0450500c55805020240e0024400b0340c4a840541c0d05550040c1c441c0f0488070700344d9000910f1401554825043c1174107000c0c010401543c9904220912100110701e03d0f204030071107002000032030b8410b02140b400802d130500c0718021301e0080200b0350864002e0806010303043c0c3c544c0128007500d03107200003031001d0317900090a16091100da000034000a425101d00603051070455a602000c1c400207011007800410100304a0110122881120300501034460090b58600786403401a0103080544005a0403505e048000543c034104001680ca004245402400100341044412101d070317000070424001955090102240240a921608007c2d12a5074000d01702c0f03a28043c0080c0c151800244041d00c0790310182d05011005580d40d90302a0441c1c003d0030500c02c4140500c2031000203000c2c405941da45445a450081840280303036214206461901c240c9264003c4 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 349079613 1250 349078363 349078369
    0x1504020c010f180c05150a0e0604050d03201603080901020c0a030c030b01050d0812092e0605040c09060e030a0609320312040c030803011509080a0308220506070e0f 72
    0x2e246e210046000c1020451010780d140700f2040c21110103c0200b00e1030801d501d44010888480e03606008801107564042c91800102181603020b50b0340080100500120072220900410302c4218031000b806240042040300040e27009021600a480700940300c02e400780e940b403c0c00e4203220158407064802a60310000402d05040204940040a0b0099100782c50a04a034541001c03804004180e0300c2d03640900000701e10068001d0011b5441060590090b62600c80d00d5484801100d8042d0f102070320075031408910089607500104600203c1d84c45048c00091540a000420b04016941354004c1440c0d1a01000d00304000040d80310180000e01d000c900807410719034080801c0038128030500360b600d651061007401029030a008010364898400c444202500ba6659129000e0b600203801c65200440c1082041200942c40507511000f020400024084620a606e0140c580b10300039041c03514014010750003110412110941e003d00603800301c00c544161424980080c02d0f07410780f0020f503228407510100051a49 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 349080863 1250 349079613 349079629
    0x3171b03120f04020d060e010207060b090601020a1217070c030806010201091e030c1a06120c090c1b0a030509011202090907030507140301061706030102031504020c010f180c05 77
    0x1001c4840030305094445105030031200d10000d20490b40048031040c210001001801510f4030640c90100140c0c07266000e14207401502d032075014150040036402d00300400340e03a00103000da92031600044c1e085080400c036031044419000040c2c080448010510134070011715404a03049090034002c0d41c032851947c0301c910049007a6a4101005030074050315141102121886c610a07030800b9100742000444940b06541d14506070400c0340484583d0004d000c2003100d01c1c244a04002d07000c4440703c02810841039800000392a1507000380017120b03500004200c02c03480c0d001c1d04000da5600c04003d4201c4206110a240040031607110322409400075001d4000050740e0071032070082d120f904038020001c003003e03650008100d006106c0184044104010702c0709100c0e2004d203000c0110301801041d52482c5508203984003010340013001070b11140c0a030f8410410888540650301810303000d55000c50f0b0243c2d03904010b45410b809446440e10030f684240ca41081080900c840304081ca908500c90f150704030000359a20300304840300c = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 349082113 1250 349080863 349080877
    0x1a03040314120402150408060a150806011208030a090b0a0e01151208030901061701020301080607080c1206010e060a1205130c0308090d080a05030a1407020d080a0603171b03 76
    0x441082d0012500524000300c0200361400050307000c90415075075550a42c0762120035100c001c040f507644c00c0c072400400003200705180a480d243e1300404055140c1030b89080e070070b0a40c9101408141000c40424860080c07a08008156500100d0340343c0c05040c40100c04006041301c800101041d860540d02d07500c6092002c0c180404c4540304e40740201c0c00d500d80d80711490b196000602e05211075503a010003003090000f4440144980301041c00058a80d8100810305203003010140001003404029410081c0c0d05038200200c0b00b15090203d4500269221840142c42d00d0f0844007070b507503022001280c141c442a901011300700001080c10820302050b180e515142031042c541d84006840402c101009001181c000350040c038032441c000d028040c076200c141d21170200c1c1c0d0300941074940000300b00000b400720703402d414054128030b500c1c20203070108a820011000380d62101c032302c0c03681c00500c10f03418005091507040e548400000d5420031014181c5696490961b00302c0d5011890400400d119002280300030076001003501e400c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 349083363 1250 349082113 349082137
    0x7110609030406030905010b030307080703030524040b01030b1c1b0e040b091612050c090c0901030b040b0d0c0e070305040b0f0903070c09020a0e0321030405071a03040314 75
    0x50036040c040b044002c5c0010200075a642d43d224914454591001c1000701401400307200c1c000d80f281c40701d00c1c0040603a200501118941440071000624581400841007c19401240c000902c0200c80d4010f801030484242e111703a05c4040c0c2d01d6550a03002e00e12001c40e0a483c070400481c80c100b9903c01004c540414180601c1d01817801c46400140058551410306400c664408101c07501161301503074903011442c0703d4004562a40101441500300714040003d07000c05501128401c0d040e01e000c07000d01c400c0d40502a00c150425032261104482c030b0320b413680800040c600141060040340d50904200056090911501d40c0c1480c0f0000003c5420340b00b803090601403036010049601540740d0500b800c111400284c011710f40d600007007000c5030015180240d43c000601d001c910150f2216881c402c0a41805180f6910b58083c0d00310450034406100001e4a18910700828610152281c81364105103140c90745c1030700070452941d2041d00700d21142048102851046200760b68100e99800e10390b504001c14001e800318070306 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 349084613 1250 349083363 349083367
    0x30b030106090207170c0f0604080406090801051513060308070501060e09030c0703030f170a1a0d0c1e052106060418030c02040e1002090f150f1e040e0711060903 71
    0x2245d100c540000c004148607a002c0310155003001403c42c5c14072070241d408a8918400060401100e0341005d83e1070020300c5400002c0202e4030b0402c100b46199441c0d01007061160394001b1841d840201c05a01c00300c043c50304042d1035034503280d040c94241c1c0240681d009590922a030100010150320000003100c5c0040880005003000700c0c655981030b1010042d0032580400d0006480a81d0b10342d403604030200d0700c510707a411001f0a071a620140c6440c0280b40e4800d50f24000e00c0c41100403c0030408003c082821210b581c040c0c01050100044c01d1071054885d900042d5020461449461030352604000126904450317205485c010340b280710801080300c0d5031b40044840000fa280c24440480c1c0280d9440407001d001a00110388a0325100c485c5040010b110386142540da400708a8a51600384840142c0b441e007415200c000d5a950000c20200c524050302c440b61800c6480010f4824800d40ca000b80304507180e80c1c10ac0456121600c406058000c41c2c4c0c00c071500030005803440507c00c490800020400d00074003500703020314 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 349085863 1250 349084613 349084643
    0x609010c0516020d0209070f030c050c0307030503101e0f140f0906041508011a062503110307030f17010608130201090e01060503100803040b04090c110607030b030106090207 76
    0x29442c2c9041d4000d0380d0140c5181c02e13010168072120b11082c42031800790b03038100c5522212600901100c980425200030010180300e1482e5901000080310304031905420142e0301c0c4e46d1100c40c040d085c040a5013219a0320b00901c28001490048c041d0b050003500c08000c0c1d2080c620381c427440d603039a000042882c074952110100c0784208190800c030840c00c3c2c200c0d0000c0e1000c00d210124010018102442e98820320680c2e66a82000742c441c0f1415448290aa070200c505c50321f44040b03103201e0108000641c0f914118100005407040815001790521800d20010b20240d035110111810058180c50050340340710013160350131002c68208201d080025068903481d844604c140c2e214601c00d000c01c050011030407070500c039030004081107002204c0e4030107008040a03655541e40c1d28007100c94802a0f1180d500c07880d141c3c4d00c20301003400070344155801d40c0c040d40c03550800010011010301007202c2c06814441c17000b41e03a0048405100c3c6040d41038101d4091000e050b4001e004080c1d803440c0b0307403049204104010f042070728801c03442 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 349087113 1250 349085863 349085887
    0x30f03140913050a02160516120b04060b01020a060507031a030a021509040b0402030a0e0d0503130f080d180c050a060804080f0403050709020304052b0c031e110609010c05 75
    0x760308044d0201c1c0c01814440841c0c0700740c4600000080540d041d80c00020700741c100e00100101100a000010316242582c2550342e030b504012800074100030b06440d203035a8000150b03482044280003054100c607090040c2e041c0000080c0c0286910702c0d03a600d010300c0c280f114282e141000644d00280c00e03806003140009088000110611350407038212664015194181e90a41d40c0d1980007840c001c549500c800501d40303030075537803103071400d0004000f6a080c401d051003004044c15008020082841d007040c0816110120b03890b0403401d40c400e098a803030003d8a05048040c80d140412014890a03214141040065480c0c40800121600500ca404009545540020002a4040060642440c005410702c4c14140c690390f407507003000400e80204040560220070030060080400104446501001145d840000040084445421001d0410081c1708040680c001014401d030080341c1c0403600b815085801100c03107580246a400c1c03500032080b1501c00c500c042010040c061007005100241a20344a1405030b0030050 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 349088363 1250 349087113 349087121
    0x20a06050601030236010e0a12050c1e0906010921021809061e0402010c0809030c0907050705070b16030c03030221190509061f0807030f03140913 64
    0x1c1241016024401c5ca148030030444076210003012402c86104101010802d020207042054909604120700c84030340c00c4064503036144103c1650100c4c444000d050000d03040ca03528155048000c550440c0c081403c030b094400c81e040c444450f150048403142d1054483da0300440d4648554080d00704861061282d803030503082d8484c0b01d810030510143c01c0722450340031010070444108086411803c160412020002505141c1c01801d215150404070070791a410190002000032820780001441ca02e030024810000da6020442c5804540008180304030794502220010b019410003141201c0c90303c10180d020458441300d4081d16148400161020031000880e2001c41c0c00c04480c04c0140d0905500300300910031120001940070021900c1c1107029142d042500740602420b0101544080c590318001c20701007183c034085005608800702a8a50503650440308036000072510942c07150500c1d102d00040081085070316a9241f21072400b80d1a1044658544650848944161020a0740c803008d103400345507400e00704d580 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 349089613 1250 349088363 349088371
    0x4051309031b1a090102120901061a0322060e1009021f0c0b010602010c0e01020c21030f070b04050d08090d080403030e06040303060801050703020403020109180e06040f0201170106020a0605 83
    0x40d450540c080982d55030943c0c0d4034180c1d100300ca44d0350001a00520f155032040f40c1c84d00004a0002089024039068140b8204003540302c40006e0010000301141d0100344107003015050040c83d000143e82c0310f406281400007481001001c1480b4020303004000011221803150841d950b401801c500320002040c80aa1400545001800240001a44408041044031301481d002e000700360000908180412400b50055a1401c9d8150444d0705c0401002c41a0f186c0d940c034107281e50011b03070611101009801f0b5050943c003580381d400c5801305e13010440c2828451912840e60003a0f00440036100200303a40384044440b900f00b10382510140d030028040407030003403140c21603903400760180c036000600e9106d64116134100002550241c1c00640c07550018030540c030080c86490f0304000ca604045160910355800070304005207909c03503c0d10600d004c060350b080114082d0071401a640d90281500c07140e1034503240c0703290200030031070040e4006000080e40460088421f041141600c02c540c004042556082c2e8900c006000010 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 349090863 1250 349089613 349089623
    0x2090609040b011803060b090a110a0311041503090c090506031902190b091e03210903030418050919061d030c100e0a080906070507050604090204051309031b 69
    0x442c011341401300c2c10320080b000d10b01c11100860366104082c1000b0700703031001030250306034a0710300f4296800c202c004000b141c50241c2d80d800c000c04da1580c4110700c00214000c0c0d91201c01004c06900b1442401a890707444188c10300d10883c41c22180540301c4000d842210000c50b51a5050381c06050303040414051281d116150a200500c0c0030304200850400c0407004000341c2c400499080042100340c45441c00310100074180d5040740c424a80844030000099440058099400e40400e000c3c6030011146451001c42d01e080c080a0110781c1d8480c0d40710240034030103040c82d03060001140f600c2c010444507440030450140b140400780c0c1002d4200400d456060040442d10500744c4055110703400c1008030036040c00940811400d03900038114501e40c1005100a4403a08040f00232503420004030300000880c48401c0c2da4814809445441e01d440c041e240044c030745509504906d602240105000903007401e550014000c1e83c03c2034400400e031514402820090f11000c120041c0420300c0c0c1d82003540f0a044101c0202c42c00c5000d2 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 349092113 1250 349090863 349090877
    0x1080c101b020a0306050a140402011b030c061103041401020a0f030f0f1a100e030a17040e040804150201051003060c140c070305010c09060f1209021c05060a02090609040b01 76
    0x19900041c8143e4003944111901d0b41c4510800c40714604070b20641c1214040030740e601c0c000f4907241c0d0000700010390020051020804184441e01410f10942c1d940c0e0049500c003200700030310b1040d000210302c140c104a80481d00348022036010314142070f06000b5654500a00d4454400f9020410410b401415120320011027580c1e07592041d100c803221600641c0c541c010441605c6482e0f0000c0b00c14810801c45031400c503070502a1118030b1605d180c8002400303500654101c03245402e80441501511000d11480d071141818014207401d0109002241c030041040f601e440c0d600e05075200001c0d00583c240ca4084a400003902501c003000c0010509607000140e4806041c41c102080d109410000f04640e0844642ea41d440d0307000c42e40600410100b4810384900c21018100b407205240b40280080075031607007002103010021a00d01040003907242d90007124400c1d90041c0210405e45400d109111503800380002a0707014401c82010411140403403003155411a409441207140c46154020700002c1c1c00400a018104280 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 349093363 1250 349092113 349092167
    0xd0b03100b0906060705060604020708040509070924120b03100606050702040605014e02180a06020307020f03070e0c04030c06080708060f0d02030f0708010501080c10 73
    0x20a20901040ca0305184000900885080074011181c100a00080c06800100840c1020850015000b5400001101e01607940c1800745812242802258001d641080506c030500c42e02c2a00b010100044d13908000041131410038800a0f180040686003011010446404242d011240190846401694003400b1105a00c4a0f400c4110440f100c41c0d10001c00610045107007021403405000d40b4004140910302841c01c424034003440c1070910503a0443c801c4011000d10035240554001d4011805e1040020b1280840140001d40304040e500a5008040760700c4241404402e42c9485c4960f0415200554000e604080081d42400640c04d401c0c40d605505100303d4000050b1030310302c80c071180d20030501030804580351851072924000700740c541c1e0000d40501000c002004403595114070910341c48030f4100d5040381511200d4010601d403826103d4081e415000e0003402c08910400014440112110f0400070807881c0c0c0d070b40407181d4448604090041d4001010b05076440342c03520ae1480031003411001d001ca0340031440 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 349094613 1250 349093363 349093369
    0x4060c050f2a03151302010e03030f030708180a290108030a0c05010204080319170f0f0a0b091005101110020306060d020c060403171003170702060403050601031e0809060d0b 76
    0x5c80d0f4a881d185800419042196400302e103503401c903002540114100361100c5243c100c58007000b00680100704624001402001812007440f42003074045043d11006d8039541040c2944102c400347c0741102640d8451410110100d07100c0da03604840d0b07408095820706003a1070040b51003504551060f241907400740800314695106100500d240003402e41c03820110703d031003000a443d1b040700101c000b000d060000100843d190740f11015961200790b5400e02c14256554004100090422440350b64100307003080100480760020070303000ca05a40c01220051821070407010105ca20070340013280501c0c10b81141d0300c00f0059407116005190001001082103090880003030303441e01280c0260241840f00e600c200d0074070040c07540000486421003164602c0a00e20701d001400080444001d120080050501d5900b00c01b000d4802e00985509030780c002e090680c0e0f01c0d039906006548003801e0000f80c03211140039901028010314601d4100c2c0f00c0b6030103840c040c241450302d0b00300012078200201c0042407d4035031004400325a = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 349095863 1250 349094613 349094653
    0x5070203070e0105040e030a08011214010207060e010e0f030d02070c0810050103120e28090e060103051c020d030902030703060608150610090519030804060c050f2a03 73
    0x12040c09890b5009624010400050722243c102c0c84440b504200071030280c00c0d5200701000e0549800700f00a1410a85d140741406500c003010410300e0f0103520200b04481001640c0e0440c844000003a402800015818040e698580010b0280ca00700750784108408170603d000c54004e00b280c0b0340100030801c030080c2d46185460902103040c0000703040c242d8400040c400c001103070a0102c901135151818845503008e14020a030102031240c003540032101808820061400702e000c210000e40b980b000c1c00c0c421204920a40d550328502070104171868024069484020094001c2410400c600c0d0307801001d1108541c0e4041d00200044241a0b0f0180114070000c0085070381070040c100141106e20042c4200c100b0f0b42d00c0807c040c0c0d005000140716040c0880310b2050359500c41c0494003507035030865500340c1c100d054010265200109510007460000049000115903411201482405000e0f00690b40000e0004030f90582b60000014001c5213205005160b00d10400c0e02c1010207446c90700a01202c2c41000102c0b9151000 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 349097113 1250 349095863 349095869
    0x8061011190b1f0e0a0e1002161a100e09240105091303200a0c0803030402091b0f0a0c140105160801030c050103050402010504030b0109020301091b1e0507020307 71
    0x5421081842983d20581e0b020401030791220072552a000d040a41280c4621400303024440c8860b203554070040c0a503018890103500004020b011076440351000c10381c0c004e08003a14400c0d00d02620090090360030a601500d418410203002d284500464100400d40d01c0e40c000181c0001d89512a49594440c03078401e540004404141300c0801c48580e61401c4200019190000c000c1002407880710715090009800881d040c00c010615440711301c0b1040002c0c420761a01c01d415401a045200c01400007840d2000407000b980214000d40380c0d46402c0e0384141c030000001001100140ca111000c2081d103051010400c054200d107400783c640302180203c0c0b911100400c070210300881b0081d955660502c200c007000b1074507410719140e1900b0404203d40c55615101c0110000784106810f0540311000101160300c1241150055075001c078a410701075848111380d50094209000f031000192034001c1c901090b90100c1034842c59410950740d003080800c00281e8010301c0348003408400042c0401030102100682d0107001020103 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 349098363 1250 349097113 349097123
    0x9030c0501060f03150c121d120a030605091e0c07240e0111073003050105040b010309050604170d0603141204080a1205040b12160806101119 62
    0xc0f0038154108004c1c00301e09042011540c610b09400700b45810341158022038107040c40308000a20660b19101107244400b403185450082c012080c0100718802840003a00034100b03248d9081000549030360600500300781c140c800301c2c0d00b0000c0101240c41e8800481c89180d200c2418044c440c142500340c0d540c03409620040303050640b4424900030301d0280100c10722824402e080088002c1c070500725020351401c0f40d84504103010b018010044050206080c036400d0001c0700f100c555220300a4201d18a00c020000c14081c010b143c410b03401c2201c0f1040c50340c0300b030061002183d0480090849a1103da4607102040c0d564940041d01d6038050010701d1045646200340c4004501403103043c481c000c609800c403410251406d520003001e0034140303c284580e042c0021440706a981c820648403c1203091082519140255031210444190002e07050074840ca000c0701841c0110801c40103000c0a01880764280c41c0c20500301e640325000756250340c81a8885128844901100390342d40140c0310314000c102d205003c1d6a00744041591 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 349099613 1250 349098363 349098389
    0x180d060902030c2704110d08190c03081f08030d1e020c03030f0406090b01170d1403220503040b04180903020a0b0405100e070f0806060307030609030c050106 69
    0x40d810140601005044222980320041c6007810303240e800d040c0400c4d1440040050031001904001400d01c90900301580241020a85401c52038960001c2d407144101d825020000120010401d0003084003d60503985912102d00541c2c4d021001c940d402e60340b0503907100c8035496031000a03e07210140010728160203c01d00c045110ba0441c140b8400c507031008448070a466204001c1020100008400c0ea0b03040401c03129140c0789070315a405d0240180082d01c0b005041100000c000140044441501c2d1703c03c8a0402e06860264600850070780d42d07070302918450140182c00700001804d450900541107080886e43c0c1030034207141015240d141c9544c000b038000b05000d900019040c070266445045a10b0821681d400c280800c02da2941c000703485480d011402000c11080d00007103400c01c2014414540c642074019010019022a20b040f2940c0b440d00d441103452180b408080802e440d1030200e200d501c41d090142c014007440c2e10715680c0e04010703c282d0005608020b005000200000ca080c050720000b8030b032080b075802d = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 349100719 1106 349099613 349099631
    0x150708151c0803071214010906050f010e1207080a0809090105121506121507110106030c030213021c020408160503062a0d0e06090a0503040b180d06 65
    0x2172400342419200c45082c002c140a007412101107140030300c50700765944144408ca2126054250001d484140308607800e05041c102072035404244030480381300c2503031114040e00f080c0825404442d1214006901072191500c0b09185001d8081211481801c1d00440030349962190780f103510700e00045c403400004d2a0b55552502020703001a410301560030040140710312010f290401c85040011580c0d2580f8107042e02014410002500d5119800c41381d05403d640811160f040c1d9049120b4410744c007000489403100c402c1d07840c1c42040c92488405a103403400c210349142064120f443e0610048074640c0204001ea40020b0441e4100310b08040703d070b8501c0700e0b0284034082082000f642c0d04c0b0708040010500c6001c08aa030006410402030f20507108191115580b0076103804500e80058078951060101307001c0d010424008090982d00c081d0b001c0104406075001c80c0325150115001d69903560303103526079 = true := by decide +kernel

theorem cover : BRFrame.Cov 348920863 349100719 := by
  have h0 := BRFrame.cov_init 348920863
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348920863 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348920863 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348920863 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348920863 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348920863 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348920863 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348920863 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348920863 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348920863 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348920863 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348920863 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348920863 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348920863 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348920863 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348920863 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348920863 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348920863 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348920863 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348920863 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348920863 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348920863 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348920863 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348920863 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348920863 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348920863 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348920863 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348920863 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348920863 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348920863 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348920863 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348920863 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348920863 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348920863 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348920863 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348920863 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348920863 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348920863 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348920863 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348920863 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348920863 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348920863 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348920863 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348920863 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348920863 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348920863 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348920863 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348920863 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348920863 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348920863 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348920863 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348920863 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348920863 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348920863 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348920863 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348920863 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348920863 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348920863 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348920863 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348920863 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348920863 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348920863 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348920863 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348920863 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348920863 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348920863 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348920863 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348920863 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348920863 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348920863 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348920863 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348920863 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348920863 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348920863 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348920863 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348920863 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348920863 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348920863 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348920863 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348920863 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348920863 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348920863 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348920863 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348920863 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348920863 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348920863 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348920863 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348920863 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348920863 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348920863 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348920863 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348920863 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348920863 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348920863 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348920863 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348920863 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348920863 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348920863 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348920863 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348920863 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348920863 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348920863 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348920863 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348920863 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348920863 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348920863 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348920863 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348920863 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348920863 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348920863 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348920863 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348920863 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348920863 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348920863 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348920863 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348920863 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348920863 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348920863 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348920863 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348920863 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348920863 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348920863 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348920863 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348920863 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348920863 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348920863 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348920863 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348920863 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348920863 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348920863 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348920863 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348920863 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348920863 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348920863 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348920863 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348920863 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348920863 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348920863 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348920863 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348920863 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348920863 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348920863 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348920863 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348920863 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 348920863 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 348920863 ≤ n) (h2 : n < 349100719) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
