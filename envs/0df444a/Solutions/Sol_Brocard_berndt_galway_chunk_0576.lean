-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0576
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T20:31:33.34917+00:00
-- url     : https://prove2.me/submissions/d56d73a3-c8e1-434e-8f6c-418ad502b6eb

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 103417266 ≤ n < 103597122 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 103418516 1250 103417266 103417289
    0x1e030301060f090e0f1009060816050405090604150212130318060206010e130503030a06030b0a021606020a09080d050903011d031914070f170304030f0e0118 69
    0x10079400400c5000c0204280c002e1141c10641000401004a4155885044074001100585480d08445c0d07100006a0000c1d604a00b4400c0c08511400041107007807003101900310600c0031903034640600c026030f0340c02c45110145402000002e404900d851119481c2045994030051520b0b02001410f4400d11007681d1620305210415501c3c01015040600c0c0790303403190f45c4000741c2c24030392600030000c5d500c00c0c050007040c10581346140410000c10034a2100d80c1c0d010f601c142644d40740d1402d180d406000b05010b20066582c4002c0c0804903810403200c1c0700b1208801c0c2400351400254483d5200c00001c0c0d40450441d10400038403260000b5510414040c07200c62000d2a503da030740d10031800c4201402c1d41d011385018a0121403c4040103040803000003110111204014845d14008030b0f0708041e40c90003040182c2d219600c0700025104100950f0701100048144603182c68403441180d0964000c560000b05c0c3c0c0100030138510481011801c3c083c0410b071012110501d8020190b604482034030030303189070507480601e1021 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 103419766 1250 103418516 103418519
    0x31603091a0406060f090f0b010528051917100602030a0e0609040e0304030614060d0b04060603080d15090c02060402011b061b020606040b031c050405041a01020f031c0c021e030301 79
    0x551230f00448904076002d180c224100450060200c01ca040313003400120a1512805094075494094400e5461001c4000748078160b03020180b0025007803403000e00c24048010909000121300e03010300040300c02514102e81c025420920780c2402645c0511801e494107034452010301c03481c43c459860740182d102521000c40a5078445103036161202c140c40107a10f9040c440c0c09040104281925500c2c0d05401e5140c01270f032226103907112810301b20b0003404c0030742000d0306914001400302c5c03501007590028440c54024942095000d13642e0030527081241c4a1741c5603c001600140042409503102d082000b40f15403001e48030b000c1140300c030340d0740c175040300c0c0761200311079003060680e170058026901841150390188040e03c091001c00070280009807900e14ac80320342d285200009110101c11347c407490030380e0040c2138042c6c0300304040b003076066188000c4604044c2181c01445541c3c40701146c000301009070b41022088004080e00e80d000420001c01820010320004110b00c9403c1c103012001411400686054079050701656995 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 103421016 1250 103419766 103419791
    0x20a05030d0606141206100e0a030303050106020c09010b160302191101300e010b12030d060b0412080a052a060106030c08060d0f05070605031603091a0406060f09 71
    0x1200d840e944d52107149400d01c100c3e405c00f010001d000342d100c04100d07400c40311250f0005040d900e80c0c030300e18100d0703401c20f80000000c000c268040d88036038140d800c19003c079015002f42e5420800441c13400d00078180a03038424410760444401010302259020f1081c015208000841403070000340f00010303141601c0c0b0487e04940081d003560403d001210042803600d0100c0f200c8a21601c81145851020b018055140d44440c4800064000e42c494076101c64004d01e01c0316503200030901d413503036070308041c02d4000114502100055509850801c44080342d03019440300040da0481e44408001d50003012001040c0802080780e4143c3c2c40b00503001400203a00c2c8030b4061450070040480314906601600600189850f11410011b807e03080a4010361102084814100f00c8000c2c3c030780441e000d1414a0f0080c200d1180b1000407030076036005030203544074000700b56200280d8409001d044040d00c8001c20040d0000e0f821b400f0521103c400d041d2880c1d442402440086891940c5050f98600030307129601030460140c0c2d422001d02c48 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 103422266 1250 103421016 103421027
    0x609030f1006060302091c0314041d0705091804030c0b0901021803010501050d080f07120c15060e16020723010207050a0b030609040c1806090e072301020a05030d0606 73
    0x50f110f03601d0218100b541c3c02002c00d0381d0040c0603ca144556160409000c10944554450b454140764a0011525a0340c0d072070242c50402ca014440c030141c0f07580030001035501c0c0c0c418810364000701c030300501d901c1e601e01e102d641c0181c844501510540420503020700e0700011070040c83c038250082070070340b00041e43e0301119418201c80e080303940301091091341400b004000030750741e01c21185106e6401c11441d40d62900019201c074000c0c070a805004104c0c594110140100c20f411140a1204c240140c0b0482c50301e40160032a2811201a401549c994418502c04102d0700c2d08051076044484580340101ca00c040d465152050407000300088841c01150f21440f5403100b540e0501503880109016034150502506103100c0d40c0150100400413405501c0c0180001c040c04024181034000301185805014500e11441094028025501603848002e007405414006004005151400c44003034910108140d43c04104402400003120840fa046228410b81d071070100d00280010a19910400f90000700b07140342c80c5001d013a = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 103423516 1250 103422266 103422269
    0x607090806090a0809010521130c08030c0d0807050c010e0c12070b030406090c0b21011202030d1206030b0f07090b07080a0c020103060306020c0a050c040e030d0b0609030f1006 77
    0xc50f908911036a100103440f070030980b130761850242846612407014a00d108070104038200b28180c1c400b2883c041c081c1640d207410668061324040e1014883d103c0d1540c1103980e0742d10030108581802d03030107145485d4109110b25902c50b00300d0300c3d5181051a00104404c0103007554484002c507601500003030301d03407103c603d40722039101e000c07203401400382c02018904844401c59001c0100040c0846444034080400c102003c040d00000d0201320384410348032000c0c000403401d01840440544525501300001003468194a11000e8020303900400405481800c0c8100f00c40c4551011944003420f5268000480001c1000316454851380382500e507400d0707a00c1c0c440c600522a9150360b0007015003841c10004000031804080c21507000343e00e181402e075141045480100e000b800f807030740090003591000c500007007205030100da00342005000c0d400311344101180c60100401c13502210041040c2d5130007080303a03486e0070a44d03030032840388074400801090800c5c0682c004203007410310040003902d06400080710710000550310305c00e040 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 103424766 1250 103423516 103423531
    0x51509040905011a12071202030f0d0206060f010809060403110f0109141b100305101502152202150706090302070f0803030112060203060415060c0201080a0203090303071b050607090806 81
    0x5174450390348840c0c4407601409401c940c03a1100c1c441d5420b41d102080101c0c0c070120202d04031051300c00c140c64001e40b03c001c00e44096114001c1c082c4040090f600c0341041c3c1d80aa51408081c15941e20745603400e4941c1034401003501c600340291220300d1265102845101032450185800000f007603a4040c00b00d06004136101900e00180c04001034400e207440700005020310101900b000200c13600c030190380000c8640d9540c403405ea840c6c0c00480494525501149a0040d4091036100070103640703030310284180454021000c0e0f91440598446003025103401440d0b2200749009070b484601d40300142d140e14040d59003660042e400341e441802c00304904500400050000c3c51500040c7d400d45d410805550411102184060425600071022442c20360f500d0b0710018401c4501648054000e03a500c07000f81045000394010f078042071443c4005036440c0c3c114001c4a02c5042090040c500d181d80307032071050728694641c2000e01005041c000c2c245000403030400c08d46e8042c03000d64541c5242545802152490540001d2000 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 103426016 1250 103424766 103424779
    0xe040b03010e0c0d0804030b07050a031505060913110307050304120305010302030a02010309050c090103061a0d0503040302310504110d020a0306050c09041b2601051509040905011a 79
    0x1e8030500e00031565918840f802c039a403000e1803c4c10305144210303000d190005000000c5610501c20059080001490302c41340c00c2d2014042100482d12070106800c00d4454070750050402c01210781325240911303e080700307169050000104903005455004042e08200d4680b00400c01c0002230205000040003860030b1401c2c54901480203604641c0440c3d10788000e040001c1c181a21003007a10700700501440450b01012002d004400d40d5030f5030381481e10151020460a5080d45226807010301d02d801d00c9107070140607640120055290600e99404d205505c803a260000082001c03114620306401258128840c40094403400428581807908241869410350800c5d20300c918281e40b00c25005171146070301c64040302c0d0030a0000070140d9422018414031b03c0350044041c3d04c10315040e02d52616030701980902c10010030950782c002d184400404600c8100020b1a181902c40c400500100020302e4000d8541801900711072011b0300b881101c41c0420141c48a450086481da51541810798400c4000c03000ca10010030221043c = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 103427266 1250 103426016 103426031
    0x608120a0203070305090a0302040905100c030e0717031b030706051005180705042c010501020607080a0e0a1a06130b06040501030f0e070f0f08030414010c0318060e040b0301 76
    0xe0b6803803150b040c009050000116082d8101ea0328407903900300444c0c0240c803d00c200040e624107640c44480801c55050350760f240c6414025124072a1049440f04d00c0580b00604e0000d090500646014a4260701114180b008000c1403a89001c00900d80141203000002940c85004c54940f007010b5807801815444c000103820b80030042555041e0240b046100c42000340c030001d44807440120b4080c812a008640000c1c1011440012101144a12030032900144c80400703450340c8443c01261106010356413000095410707004100039140741d90002d401c440101d811188040c4196444800300035540d02c0b0060030011020070042e290030704001c038210002c0103640c10032400c6115000186030307001e14040c290405d981e0701c1c2c100840c183d065000d015000c640d4402c0b941217990f210001c0c00601220301401d510390301c1c008070001d0305c20000400d0301c0690300700e0780309504000c42c00d400446000c00003507015000c00c454100e445071070381c01c4842d0a9002d448076540301c010601c1410140015141c1500c0618081c3e85030108 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 103428516 1250 103427266 103427287
    0xf1e0c170a09050703050303070504030b01152118030908010b0409030203040b09010c300203180d11090f090705030c090a020901170708010e090d0906120618060812 72
    0x2119a80800c0440c030016102c2502d04019180a00300c0d00001d101d03200010a0041c00e94100d00584103c80c800d00c856055a0780f2070308e08010000f41d03504a032020484204190341010300c01082c00e0f010030700c0c203d0000780c448428081920600316034203058012900140d07050200303c4080c01042d180300740c00c0d181400312140ca40e500a6503072066108000281d54041640f06141e881128200d441e680c00c003494020610301c3d420790307141401c4080c1d404046e4031000d030008540e01c1e001006869441c0b448040003c010141c5805001d50320000c2ea404917542d5610401c00062a40d803581958021741d40c0030145e6a0520300308042a01d07010703141c2c2001f8400d5200000503880c81d501c490300e850740880c5c1c0c0b43d005a1507000080050b581c24800a5a403164403c0300410030a11ba54040d0006040b5270381a2040046078a69807000f58a6a1a82aa0000140c0c03100020300805c0d018044000050403009170000c0c400c0d0781e070140c0d02614114070464070703c459107a15040001c0141000018082c00f0a0094140380041251 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 103429766 1250 103428516 103428557
    0x105060306010e07030b130b0901080a08090d080708130609060908031e040b04030b04050106050604080d03110f04030b0609060301020c07150309080a030f050c03011202130f1e0c 78
    0x4903940d9610003e400080c0300320300c29000032030b528802802016012005142103405020306034603da01030300d010000002e980b1000036000c10303e03540045001d40303008004401c6c029240340241068546c094100940c0340001e00c80303001420583d64242041c1c0b0340784d09040000382000b03040d42c8910208000c0007010300c88160080101c40c21800c000d0700d40f03003079004198030f100d8003401103a20490740198081000000c0c00a451141c03403045124800820003640c603034003040b0407400340b03014144803544002043c40a1600075840110a514980266420401418441445035209400c1156882c4281c800d000c40c0c0c0c280b0764003941d000f5900318000d41c140001d131500940c1c2c0d95403a11814910118040b107100a485c080e034071150b170b482d40050040da680c00c40c20601070040c18424110742d40d800e280c00c0001c1c1e024400481503a060300c20144405c00507050b2502009103029540380c1d5155851780c3c5030030300301c00e1781c0d070311b11a08100c000c101207004100c03410301081404407000c0d030b24482c06226904d0071050032414580e = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 103431016 1250 103429766 103429769
    0x1080601140607020301180c0303030b06072001090f090b030f06040b040b040f06020f0424140f0d0603121803120f03021309020301230312031305030a050901090602010506030601 78
    0xd0b0382450702d40701640002409082d020306544141c58080e2240c034244110307804a07005807400307070302c0610500c4400344c2440141d200d0200b02415403001c1c446011410714416010049402051502075042034854001000f00740280e44003900013565140d1010090906000610303140e00040c000e4051031610f5101c6001d113410082c0014001040a80045c04218141003062815034200703100b15200c12003200c072030a0715482806803032200c80c908480c3d004000c1c1380311800d4921a00c9641da0410340b07400304041e00a540c000002c80c041400003448203000c00030030b5214440041d030040c45003100f414140c0700082c001810410500ea0000a1f0140c2800828408404034800c00340e10710342111102c0508004800034010000c60b549140800f100015071201c180d005103060b42c3d010743c11035442003110f6140c100142d0001c2030458054010402001e000040320000d03503408441641403020700242c607a20701d419a4054004100800d5001c40c4116040d61701c5503e04003d80800d00081141d410040002560765505 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 103432266 1250 103431016 103431019
    0x3010b070b0601050d18020f06090a15020109050102130603050f090d0c060b0303070308060102121312080906030103080304150e03180301061e051f08010b0f0f04061101050108060114 80
    0x4070004207445034801c1c0e00700c2d08400140703a402c101d5510520380b015006d0541c90320584c850016002039101929001044800c103840003068188000e2412190203072140300c0c1c400900070b65580d9a0341d1004030305c00b03000405142c203441c030701883e4850421402070101e0380042c00c400c85c0040040100b103680e84000911904000d418105140e422001e4548000500b440d13521090b014000490707100c0405802100040c0100002d80a0340c0382d4991200c01c1d4000c03800ba80030190300c4422100c07020040441e070348442c0303080e440c01000784a1500304d00e0004107030103500c01c3c1e03c202c0303d10000204103c140462181d9880460040b24000d009003c40c100400b541d034040c5500c82d10030a01203140c50440c0b45c0d0250710420051080c801000c800c0b19100107141d0709041c09204460040740c1c41c0348000b841c0c07494440340044402090315090456400e0192829180d0010304109000c0c1d6005c0101c0480540180c001e800200159610800d011150000381401d580043c0d22035929640b1010061081c40d66480881c0800b00c0e0 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 103433516 1250 103432266 103432283
    0x2220305030706090f080d0b041103130b04020307260c01020109020109030b1320011205010503150705120f01031a010b0f090319050109020109061d040c030b1302180603010b07 77
    0x525060502040c0c80151000345804000100c041f2184d8040d000b541203200b048800304a894980221061244800c41c0c151a0a142d540e43c52000282c13007000040e00070380050106e810064072942c00300c803030740300d0751f1080d80041a5004402119802c104401d41198030b0a01c0203100b0301d0041d60000c0c20100e180e000081000c040c0310000b07400c040c8604074200c22150000e030f900300040d100b1070410340a81c00300c0900d00e00280e024414800d0f520454000c150485074040e0090558500c3d800084c2c4e0324110140850040000820500c2c12480030b01c0700ca00e0084000281c0b9403525455803a0414a030040c3d15518440081d412004109a10104082d1244000c80c1d200380d5a0311580c0000003800c0007480c0102020074a0a1440f100c1400415448110818803c0e2181d00d2a161510380640d5029003050a1075201d00c0100400d01107414560046420b0603014207012580c4421440010320512030414480b11032135001c91a5081c501451b200d442c484c0b04103541c01c1389194140061a0240d11038070b0009002510b = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 103434766 1250 103433516 103433531
    0x70e0901090f09020a0902030604230109020304050f07141c030e0402030c090a08151803071e0f0b04120f050409021b070306060f050a0e0711010b0a060302220305030706 74
    0xc0b40d500712200265000f0141600c154481c2158030082d00300f510018011440c202220840f6580c0349000c0e4040d17505a44c0d8402c0d568600109070000c2d500040c021100703402001164090f00c682001f149000e01180944040d0400b0883c0906c02606070710348017400c09520100d1444003203500030400301420305007980d01603907a581f005429040c61080b940c1564100c036001400003984000415440b00e030340001680010f05850703401d00070350070348070b01c99039030719036400c02c018034400030b4a00000c0b0780c928002e65034105c142220980b14090a0401e55006aa2050f900010081001442c0c0d200f042500e013a8246070883c5100000001c00c2c900407801000c404640c0081d5404000c0401806049aa80088210340e86143c4a00c0d0542c054141c07846950001c8102600c049510700d0a103102c1c409450448198907401c3d03a880382c0480b07111818003045103845d580d5103220b00990f15001380702c801a003070035180540e580c0c44180200d10881c03940801030388034000e495400c0c4001400030003115a5140c11200100345007 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 103436016 1250 103434766 103434791
    0xf0203030c12033412060b030f062806110a0c0b0417010b0d0609110603150a0806060609240403060903020d020106050105040b0703230301030b070e090109 68
    0x5120701c1800c12210301c2481546240e19040c10000c40c4a6a500c0004c820b1840400c481031031410303010088107030807030150318a2860851161000310390b100617030f220100d1000d9a98405090b294001d039008a244403001c4104071035410f146103e0300c40c2c0342d80850344420300080300001c0d005e122058080d0000304114080300a44507082040048055a084810b03905140c1c0d41e5015245a41c0c0300384590f4002d8210104403190b41c05d41071084120950000d4031070400042c242c0d840b1801403400c0e280860303424808043d0721200307403138142c01355100e82500d01500414240500c10069492a41e81c030040b01c940c019010030900b42c8601c0300f9075800110176905d400c460f11100020101000d000250a09102c0c0f0110b00001802002e41001c030442d4060f80984604006a1004900344c442038041c0ca404208104010443d50b10444003d1621a002c0e00c1d005603200780b8410704194500c410300360b03402036480100061041c4a841c1c03c0749d0350000094200768501018a80c0842c4008105204045146507a80ca415640 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 103437266 1250 103436016 103436023
    0xb130204111305090703020705030a030c02100905100e0109020a0522050403080703110307020601140105040e0c0306041d150406110a020706030510030809040b18090d080a02090105070f0203 83
    0xe01c00c4070941d844078074501c15885849003a10460307124003001008922003501a00c00c4401240d0000007a5240007050b4205401501400d00b0400843c4284400f41d0b4842c1900d04c60104114460005483e02c15106620302c0165041c814811302164580380461005030ba443c0f16110840b20103440d04c0108118003003c6e490062560200040940e0501040100301035125401510888007500c1c100b10101d00e07042c90000600084a45c2c0003d80c6c44100180003e84000c522000c000405150a40c5450384550414035400303010b940442c58480080148040761810b8015480c0c00000303e010f00807021a06006907603610102c00600c4290251200030170300344006600f0196403200d840ca09507030b98150050009554010f10f1103400700003454400415142c9410228030003c0faa0414030560030103a1504c20400100300b000c482039400071406210b00b05880d143c00782c0e10f1242402c0009400800e03402403001d020814000c0641c0403492041024401c01d80e00328007070b01c00040e00300c03011203200704070781c40401e14 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 103438516 1250 103437266 103437281
    0x30e03040b0702030d080403020a0f021216080705060306013204080a0b0105040608030901110c09071d0a03080708030402031e011a2709030403150614010c0b130204 72
    0x1540400140401c1c107000440080044034401e804070381c0344111804089132403290948000340140c01011601021900c1c1e520440401d81c0010301c481d45030380042d82d82034903150408203440d41d10182c0c09001c02c242101848410000d180640b44d2514500c0c100e00020000c6092001124064440d0000d04c0b40d10a034600c192161a410a200f039951741d44c5400320f69903580802c0c1d1046940c01d0f1101b00104050070715015000072114058002e5041005110042d901181d580c0304d0000c49200f4001d048542e5940c22920500800c0c05488510301482d4004100d0b0075802104120b0740100b0138144104005260b40044411403500800403030340300c0d00daa10009080c0034540b00400d0100301c501c51a040301c80419484000002a03484006041d20002803e008108402604040728020340128421254a44409490b80090070740141c0e80b4081d141e55505030181210060944416600d182c00c0c828016107003082210290242402e00d2104040d55a2524400005005d0880a21904c80b0301003151240d401070350 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 103439766 1250 103438516 103438541
    0x103032307050312060f0307061d301c050306010c02011e120e0a02090c1e030109020d0608011b030c0c080304060506030105060d050c040c09090903030e06010605040b12060103 77
    0x25039581c020b06404201342c00660f00180f040c035403400320310142e02d40095502c01325401c9071244215505462040c60b404010502d416400480303034560355150442c2582c150903440c60300341c110801824403418452420804120610b242150100803070310320703074211060340e50040342440c02c000040034078401240c0009210110341c21120394008030404846c0c10822491400c0b00c00c2c00104080f40c0b5a0010943e1100380d19806504003a41c40b02003580800b0480007408444010100c2c05101c00842d03000a480c0c0d032090b40941907055010401e400311121900400c001000b82c903000740a0400c0182d02c0e01c07010041c080c901c40034107a46802409802e400303040556441d40c1c2298409407249050300b000805460f084400a1195290000050041c503040301c5801d600c1b90018014004e0108000c1403100900c00c881052081c0503031303040e0003d8030502c2801411011031081c1c2c1c000c6015072000440c60300c1e10106030841e40a00c4401d200c02d010401802d415074071202c01c1145000d0703c640b02c1c0001a070092000306c8214 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 103441016 1250 103439766 103439773
    0x1203070314070e1c030503011a04030c0306020c0c0901032f190510170c030601020c1003020a0801050105040602030d0b04060801090f0312110f0304030e0a1403060609010303230705 79
    0x2100803034112003511943c2d00195404c040410a920040b88840841e01e0b00030080345003400140908001c0c2082c00b6109501001100d1400b910394a5008200240d9030080714906d4000400d455815420300c40c11100c1101520718071000c0d41966503070040709443c01b005907802c10704c61228100341103039141c100100741c401500440f040707000d00e15a00d0064249014160059044451381d02da82071049507c0c04845200903507140b5a034554501d40c0500ba400a040310341144201d14601720141e54607200c180c0c400165840060f40c8a00349c0348050806441603201e03c0c180300091100f0886250040115041162102030001d450b03a004400140140020f42007124a9882e0060040810120a90411040303019131506070ba4181e0a00034801658844442a99401c0061161700c0100c403426003e580c01601c2070404421f40350160303020a020104039482006d0550481e4068085800c0900a031078016100791525103e541c11078130f018041c540c0071640b8419805108007042c4e01d00c5d81b40026610416800803d6 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 103442266 1250 103441016 103441021
    0x14030106050406060917030406020c0d08090301020409090209060a080606010309030c0b070201021c0203060d12052101150c080a141603021b060c060609060a18050103060e0307051203070314 83
    0x4004545c0d40c010707084800504190010322550010030307601150356603802009142001d0b0144034450381c840070125100d120901c030780780a59800f8009840a000165400119440c060040100700d24002c1c000078040c44107034000b13015000010542650210782030030041a440391601c0c0c125a00c841402002c0d00000081051107030055064000f00075100c200003c0e45466401c90700144d08920042e9000c3c1c2d84121b04001080025544403000704540f511400c22034205107075540d880e42c0207003c8082d40e41450b040c0c40300600c02c4031004880c0b1030081c417503454a0803100e240350307445881d00d210fa0703800c10061140108102c0082084c8400b254401300328800c181d22249118075005e56690210554450360b160103440ca0b4000b400d00d0015928440c2c9a50000c1502c0c4c0c0300c403414032008800103400c441d0007030031441000c200d10111082e4a01c4408003000000b07103a614605000c402c84620f8044984203400400181000c60000540b00f50600c031101c40a558a0b01d44a000360002c28070902c007211504100401c = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 103443516 1250 103442266 103442279
    0x70911121f080f060a0f020405040e100e0309090a0902210303090d05070203101d03070b01050901050a030b15040209040903020a0213050c0409050a0e03121005030109080414030106050406 82
    0x203840500700d80401000c1901e41c9034030a46442d10702ca00c15411090740301000003144165103402202c146d54019000515154540c00890203441003600005c0c00ca501201131710440905c00d21a18103035011401c091070801c140c000000b8210203020f0580710005031944280815580c9080d81800c01250100b404042508400c842c1600d0b5001202c81003628015041403410081c0507004403080c031580100075258111030180000b00074020360b103010112240c203002c6a418002d04000920680e8040e402411603580f6050801c080c80105800050040503840c2e8100001031a541084d9005001020380070308414407080400c00038060b038002ea41e400340c1040b00140605401003006031606000f60b985400e0440984a003c0c00d0b90f40c1a00c21104000c0100401c02070440d169120b6038000e9501036000c18484081080030f817440d00074103407900f00c1d84181410311403030301e800401410003404164002c0c00800f203152558611402280303e1a0f05031a0074803002c81003690300707601900280c1001001004901d032101c4 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 103444766 1250 103443516 103443541
    0x20d140f0a06050a120201180f2312070501050c0c060f03041a09061b04080303090c030f010e07030803040201110a081b0c0a0311010507060c050702100309020307091112 74
    0x329010a05842c02d240800d590520000840544210f481d014401001d0341d0b00444150301342580a0041c01d40e210000704240072114000c01c0201b2069404415404150b40c07400f40861580d0310310b604c500f541540c44991b0300700124031f0320215402406c04a8840d10600310380c0f400e01004403003c562080000407021004240e80018501590140140c4045074981216a15042500343c0726046da0ba4001400940304882401401c00d245a040503001c3c202940c1d01c811528540040e2003101b00c40e00100069680e031f003001c11424a00d0102d0300001d10181982550450b201d1131203001c0a801d00300c0c000700003415640940760b101600c00322101110080e14003401d04203076a4101410719030300b0b140d00500e00700040c2c50019a03072080841c000c060f501c8141c03466980080014244008a060040500a490100d0864440c07480851403544445036211035520400103d5450540c1c1001810b1402a002001d88c0f400200c1e03405486041d1000140004041e1005002d8060580301200c2c21424404000c003034031840c0f = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 103446016 1250 103444766 103444771
    0x1807090c03050622180b040c0602010c02030313030e06040b0a020601080714150918010603060509011a09100203090a092712180e130506070305010810020d140f 70
    0x181d500b008940c071140c00704905100d0486000590050100c56060301c007010b50310004030031032050309a400301d00c1e1036a5a45003041c0f04a5040d80c8464030380108028840d028010003100d50707120710186141d4601161112a16020284c0140c200482c4078010420364540034219000b5081e045005910b42c00c2441d4000d40d6807200f406040d5680c0211840061021610b070040300c4020401803410541c207044610500c010740084056683c40032809400c201941a00300da8580601007540c1d01007450780c00e00007417000c07004041e80440c41c103110104201079007996450640b030500000301c0d5642e443c0810000101c1ca54092165402e511801d0182c0000c4e2030009540320004035480120704540c03441c100c0c4410903094014000182050f0042c881004901c0e126401840b03682000c015081101c603190b15601c1d40712101100d003a500700c11514070041c11311404020840c0d202140d0b2030240255810080415182e808070862460000d402140d0500c4030b60060300075111303a45080c108003515242002900c1c0c03895005 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 103447266 1250 103446016 103446041
    0x2010e0d08070c0801150e1f170601060806090414160b13080307030801050616050712050f0105071b03050c0d0c0c091104030f0204020d0e030901030c080609010e180709 74
    0x720f00044500040c0a000d492500340d50441c2c40580ca4500010201e2600501d01500c1c4c000080c043c1d8500740019244c50007818540b8100c130781644404009524240c410707000b0900744040c0b002003140c20b41c0c9203001e966005a0184048080703190007140c49140100c1c0044608110109000120b100104407020340600d41020429280f20360382c0c0c0000c82c4c0c40340718510f170103030000380c0300700051203641040d400038181240c00600301e00d600022034841c181410826005240312114208804040c0f100802c4440c48110703007880200468204004050041c1003880c1c01080b08007a10054103080c540100161180c4801c950242d60030050104402001850311000403180c1c8040144042034a0325a40709018802000c1c150b00c500d0300f821074513500b561210000080740c1c8643c0070801154000b01701c0c054a09024044001141c41e42e0b200700002d0203660303240c54400c04001c1e0540421111381d40740020300b811500c4000300c410329600c40550070340f15003000102000a5104e4000300003410708a80e030281c41c01900 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 103448516 1250 103447266 103447283
    0x304081b0d050a0320040902090d06020a02030405040501060521180601120201080106090b0d0902040908070c050a12020109030605090a050703080a0f03290a0801111b01050402061602010e0d0807 85
    0x100d01e0604000e45c91042d00b40d0f2603e4080c4400d00481c0440d500820f28075600422401c400d05059480c0c8059901c03403542c4000507040440d04111a0805000c2c640c0548601d040107800d01c82c90708043c207c80018440b00ca010382462102003031001c0c02d4054a191224103031b100352507503903031100f1501d21100640d6100306e000543d00000041e441f482070440c1070a507002024002d180c91900c41010000e0041180305076842543c0300c0d140300014201a0080c280e1910030074600205d107207840e04004a003d0a80c2c840c51000141a142200503030b404460710054aa10000008103038441e540a40c1c0f804048003130080c5980300d2558040305200c82507003d0b0030000d03c255543c13452039400c03a0f4200c0c03c0d0760105580c00740700500b80d10341d0154129609030f80069040060440b00082d9581d840c540d0941d0b400c0512150b9021000a01c07001d5074800380b0342644400c0001c0005d2005041a41c08a4810f03c10075003500b164020702c3c42a502160300c1250080c507600b81c000e015404102072030902c0141c0c1da0081d0f10489070001c = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 103449766 1250 103448516 103448531
    0x1216060305060603070809031306020c0405070f020307081c02030f0a0c05071101050c0f06100302121618020d0c031d06010302091b0409090c0303020706080c0304081b0d050a03 77
    0x1403081c0200c910442019100030309607103030440305440c8100c02170314000407030005220103000e69640b4089103000705032a90040c038440703843d00203100403500050b21032000c206902c500300e0203c0341c0010458080070b50150740d82d0b55a09103d00d5140d901100f007d044c0520078000018403680003d040b40b114001d066410301000b51a4020ba401c0d102c40c81003000040445036400c0100080750f00580190150028003020703102da411030445d0745400c0c0707241114201034140044c1818815810b281c0749803038000310701500a110b22910480d1403540c608092050881591880c14064010310642e0142c6900c400049001e020102941d40003030090600d12000317024003841008001d1500310002115412030b5000342581c000f940719100641d10100d2a070003000a90542000000703140141032044c0c1842d07902070141d042c0c0d03043c1075181c002c2c00d00c01d06a02c00010003400e4002d005008801c2403c0b43e80056008200d03680c1c52803101b002200051034003289a00d240201c0110745141c64008005000481072a9070400448 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 103451016 1250 103449766 103449779
    0x3090608040f080702040b030609010509070906031a19060311010e0409030e01080903040e0103080910170a090c0b0a170901020406020303040b0402040908030705191e0c030302091216 80
    0x290011a0007409402c0c400610901103810100108419070010700045245031803030010a207440c6058403130306841d0f952401042040f48050002002078880c03c03005000c26491a03c0f200d041c071462110840c50000fa0314040781080d8402c80c4444161405202c00f40003040e034070304210680300c02c400d80c4d00d404078180301da032444a4500b0b481356001c1d083c1e26458002110f90404011a03410000a26009640c402000003003203040d40058418000e41c80340a003c1c0e03a0f40040e80a02854051400100301444040d0700b031142c0400e01140314030390040c0e40071000a03051629003440c16000354254001d0666080000e07036041c203281d0100c180e90400c10115031300d4025443c1c1140d01d130308070700c218402e0340016001880800d000400301c80c00c0a80046c0020000f2801c2c00190700e42c42000d0b441919141d01041c0001103c0c0c82e051201e036080c1203000c5141c00c0502c84000b1036000102d000e0f4480040e00e0410520701c0d01c290826012742d050751300380b03000944046449895018003d5541415500b2468600c0008400062a = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 103452266 1250 103451016 103451027
    0x105030d05070816020111010e0601090f0b090c070501060929030706020c01030f09080a08070e0a030213020c0717010902041512080c03040b0d020a080f060306190e07080a030906 78
    0x200e42e01024413854010480110764100340c22040c1281000040c1038446e61a590900804290442043c040c206552400342c030041280e420303607a021203040c00e00c680710400da502e50351050391008428441c944c1d030b12554509680140100c0d00504030907440c24442850b12010710481c28100b9a2143c0901201e140d608201940c84081d44180b00c010703800ba580300500e9500c00d401c1800300040e42d403004129859141e40c0c01515400c5440b191001407110750400c42510741c49500f010a00e181500d01240207411500804d146882003a140c011243e000204a04051810403243d4010f10b03840c100c4000d0003d076090311a010f46032069040c1e109038185803170ba085484080f1240402c8401c00f210381a4450f10b0341e42c2d00c5405130402c0c43d100000340020704c40020300203080d20080ca22480c107807400603034600b003103013014083c18805000d031149074541c2e80811495880010700d45411026882948030307a02c0f4072040010152503540d00034807041c0540c000000d00c1c10000141c00c21018407035101d0007142c07501c42104651 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 103453516 1250 103452266 103452277
    0x30e1c02010e0a08060c0a051308030a080f160f020a05060117070e150111030708040e0103060507030221060a0f091401050105070f061e02031303091a0d05060f0310050105030d05 78
    0x83e2604844085074020046400407c20840142801401c04440c0d5030b02e280d030b039042c0398088507182d000003440c84400350340b0038440340e40055400d00300b10303d50900b00500ca904c00c2606507068240400605030901d014020003001c240b00d5481000c4881942e150240c0c910402100d207a01e28184c490383d42d020440d0034080115901c00c0c42000c0d4103d08081202c0011200c20300111503440907070008001c1607012402c0c03480108040c180a07101603203c0d514602d480130440f00000d00380341c20184148001c840f1409001c105154122a40507040a45d4950700300080c0c149a0a60100344111081c8000054901554000d100e8209000310083c08903aa6840107641c80d200c1d044000b480c6003290351010002034171552141414020188105018444014001c0103d0b40103542c405440c0c595094920100340e4400d1265014010501c510601c020302024100124014440306404240d21100000d5482d1102d541464051400a0448070011050102071000307041c00c0c00740d140680a008803c0c040e240c010740440780d = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 103454766 1250 103453516 103453529
    0x2100905120a030608120c0c150706150b0403050a050c010c23030409060b09040b060405010c02090405030906030c0315060301150f03060302060d0c120902030303040f030e1c02010e0a 80
    0xc10740c0207801c19025030b03480b5036039031003c1c07591390100450003207020080614000c1d8641406940c0d201601001c1d0f103089030001c0000c2c0b0a00412640500e1003100320140c2d6012540504040f5910150b1500301c0c1482d1000c6e003060704811000710b0700106118000481160040c050400d8a003864280130044842c540e003607202424418440c03111f00c0e03420814127a0a806e40328608140c030306158403080c48000341d032181d9001c0045078101042d18815454188036807000e00b0070844099281614000010f400d402c2c0408010b4850032035940000c060044c14030481e0b0220300b00030001030350b03491700342d10701c3c020f40e001600c641303c0380b1680350015481c234100201202e0680e2030340304c1d0910301441000d108681612620410000301a01d0700e10020060b1201c402800d5604000c60b4042000001c0e4100103124401001f002d0b82041e05200a0002588010003141d801c5074010680101d241a01c0c2400e88502c502c80350300640100754034150341540d030f0b90862990500b501c00d0781e81100c0c0c8202d0078100700207034001d0702416 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 103456016 1250 103454766 103454773
    0xd020a02041b2f0109030e01030e0d021002090307030f06021b0303191802090c030106120209130c170f01030b010602011b20030c0309040c090e1b0403050109110102100905 75
    0x515550f59901041e0b81201e424010008070141e421503942500c401d100c0032404554420083c3d0190768141c01804101c40741e5900906820b241c17254025a13660b81da0714038010080d8005584003494406001c4070300955009105081c481e50280b4100002b5404412807040a84104042c6802e042000c0202d03170143c00c0080c1c0e624a0300844e100c500000b04404c011610f100e051900310b2000503200c200006200700740e00d003500e81c1c03a90302d00000a0070000320070800c8004980304000c41162951408c06010300c134082d06100003040701c480003050b10301500d1074001508101e41c41c010800040350101d9210705032881071880e5481d0340da0b00d9405909a4440c0359521650400441d0800b8165104008000c03000c400790102c031400a801c54480703802d40d441203c3ca0803950700001070340102c0d41860b001d0010415440d150400b10f4610340445620307140340c06800046000c03004c0e030002c1c00c404000015034015541000082000f01032600d0000c15041614920a0250088591248003074565216142c0405e8205024 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 103457266 1250 103456016 103456037
    0x10605010534060c02060a0c0e150d021b0a0201030c1b140c210d020309090106030b0303210619050a0e0a110a08040309051009090902120d020a02041b 66
    0x71200581006280310580b10348588040c0045100750098210305082a009080b903030405840d4036050700e5420400c9018400c40c01c0e60701d401d54132019100c4107503050b940300711600d074501c0c103c3c428042e100382d2100090031036414141100d85240820000d240c1e80c0300340c80401040c50030b01403d481c400401e42035201d81c044200b81ca00081448989500a0180700c2419240d00100700b40004150081d040d03844031820900c0d034200250340e1000c020801d20b1010600056050a001c01c0008140e4a414014070341056154904041d240d01d0420546040402106807600e0003900b602d40c00480090880e06c5038842c40d941443e1001d11070001c0c1d10441a100041d10301102103080004c0400120070191180004550f215404402c921150010700322880e416070b5201024141410003d0500900d908060b00c925542000709100702c4d00f1034200c204480350028013064070072483c000102c0350149080324140e240200b41810f11000c0c0e02103a800d010700d100b11002c20200d00d00d03119081101c0a03200d2000d0204595118 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 103458516 1250 103457266 103457317
    0x30c0702031c09050a0f050d021e100f080a0603080d0c0c0f1211030a0516140607050301090609060305030327031614061605130902030c0703020106050105 68
    0x1001220300140840b045050511869280220900c0c000b0001440411080c440ca10785000d050008185156007042418184800079140e0508800001d102d52500403010b0a0700300c00807100800300c9001010048050788628001d010b000d41c1a2401002458100000710498540c1c420350050f030703801c4081c0c5400d01d02c010110500134442c0c04941c4040c00b030a01607072000038481d035100129140c400c8090800120080c0c4024110b90301182e82d007891500140900f41c1515071000540310078240c400140307581c0b515242003003d20325100c15a104264041c2e1004c1007069500500110b0490300851420440681d071041d40f04101d4806000c020500c1c2c00401c00300d982a0381100d5100c48100d8540480d040800c1e1522045146510602c02e001d00c0d4484085030030248909040405030b03041032080903040501c5c20801e100d40e028000303003640c002d021010502041c002c840a40240207000c44003011543c034107180d07a194660760480801107005600f003182c040b03013075441242561460103282300ba441444900301e5 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 103459766 1250 103458516 103458541
    0x130b0708070201111902150c0d0504030905031504020f0d03020601030818130905010506091501031a0d050604020a120305030106030f020706020f0a0e1f0815210114070503 75
    0x24007080c110364a5140741180344410340000c2049901e22400c5460382d03030b0988006070501802040324140d0a101104102046000b6002c99641c00d8030004c000507196107500c0c0a5880f25180d0300500d0301071140000441a20301011859401f83d03008852150b240c003182c004110319152401c00060068010800400001c1c0c624405000540f0700054000c2c0740d444080d000ca40c1168a0701c070306003101c41c0c41e000000305000080c440d0076040341d0b00342d0700e19407070b460040901c3d04a20551007100e0304040d524801c0b1180005407100e42505941c004149140ca000942010340e52a48155416445103200341400503d070160390904800166040e10f5072421680307403031001e40017040c4061032480c49680070041c103000074101e88020840171603e00c0b501070310345000c904010484200390007820b00841302c40980f06085907480190760580010361403c1d0f1f50542d03850030802e007000103400d60340e40c000c50341c6444691507440c00e52010013000c40244c0200420040c3e4103052501c4603041d40c5072008214100081290000c040 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 103461016 1250 103459766 103459771
    0x42303010b03030a020a03030f020922061809050106140904140a050a061b0905060f16120c0b1302090f040602310b0301140402070c09110d05130b0708 66
    0x8000040301c440036000b29045600400040c40141c0100c3c41c041308064140c803514840346a00c03181181841040c41c040713100980b4102c40ca0700d92920b407008501c260401508032901030202e0311541002d07803040e104404040e00c1d00c000c0840741c43d403c2440c007107a4030310720106400e00000e0003805500702380c80366121584812452000381c03285020742002000403030700c20070000036510b20425000915002d03070840c1c1e021088030301d0850010031451070400c01507a84c940050701e031000003040301c05603201c2c0d800c032003584101c80c09903006003078401c0c001d07031800480e4108030003109580c05110381216941c1c421250b04145804154005e40c0424050085110720900c1c2c0350099015210301030041c41c20410f000e40c1c021908002000c0d0302e0307110140e90601e50f20881c8400e071038014819592020300b55410101408080085210000c2c0900da01099480038010081c075600028043c642003005800303040e00400340396a001d0142c3c140e4440c140b070085210101c80200d05204250480c140f068261a560411604081c01 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 103462266 1250 103461016 103461019
    0x7060203091e0705100c020d060b0303270910030f0b04170304060c18030b060607080403021804021806060912100c021e0609030a0c031202030c0715020423 68
    0x54500c9615105442400511a0b8000c038004181052410040001c0d102490418004020420058000603158850010b145651102c00411440b00460110303256000d041045182c054070305505082c0c40608a150352040310058454808a5558108a0300300ca04184001098164003111010220b540c00042c1c68116104210341c0b06445110100e0f8421038206032012303103a550341c40f4100050039820803800c17844000090003a4591601e1740e01c8400d0510b10060400e4006c55001480d44208440702c001c40700a5035009000c0140a103c900e45030181d1070085408a001c0c01402c1401402c211442841c0c51180700005e04603031514118009101c1800b074400c3c0400b416206040c115881c0840a02800f4814082076008040c4503084200c0d4548100703088038a40c280340c211a00780a802803000c400c079101402c0c0340c141071114442e5480c080b5284410190b122042901c080203220b9042003074001040010b00404000f444c0c00350b800305010880c4140e205841943e506150b02c0031814001e4180709418000 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 103463516 1250 103462266 103462273
    0x103060501171504110a0806220911060703050d050c070209040201030f0608030a020102121f0501050307110115061d01050a0e0f0d030309031812141603030207050a08010b060706020309 81
    0x1c101d00840e0995010074181d20380c0a1001c02c0521b900e41c0d001140b154040b5080360440450a80340c0184240b1020b060040e1850a490380614820b20100c4030b00d07408500405081d065980c002428001c0c4503400c2036071000201428000410422400001a125903d40007001e1f000e0a4a640e40150010031300e103002c2e4121140c5030300000a1851050028110079516500056500e07801510f2a100740c1c14001d001410300c01100c000a0414100d068044058800070b003815580c03615980016504d00302c07209005007866080907032008820041000200c1107540315201d5511a0644545144150b42c61001c1180003a60074000030030f00c24460510911071410107040c1034400310b0080040f81241c00760340c90683c00301e52039607048420941d11041c0c4141010404c4c0341c5609043c00d24100e40d10900f842c810150894040c10101002c0900600c4114500c1c0060000101d802d0303900d140182d00c0da1018801d40b4407a240c0040c0020f1030903010701034580c034004001d203014541500d035503d020094001404080d014403 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 103464766 1250 103463516 103463551
    0x160512091009050120030c0304020d0201121b0f0518040b010c08030405030304021908121b0d0e0102010606030204060503130f050a140c010f0c0f05010e030a080a0506010306050117 79
    0x403240700b072202d814050000400d400212500390015200e280c0440c4440f43d504108110701c0c1c401c02005d80e0b8002d0b9040f030351034030030400500040700c0e80c0160003090704500d4a018180550300c07021903031000440c1d00f83d071148594010f00032001e41d0f00d40504034820341c1c8951a41170b0f90803245810b90118002c0b043c141014108030801d9211004203420441e0308854070352000050000798644240340c50044800150140305480c14074804c0350b01c412001035416000a40480c403880c006038440e4514290055960441d076510b02181c00092402c0c111a080c10302552920401041e458864000c82d41540c1141e19418515192250392000e4208445400d80b6580c1c102862071002850a00180d661140950459905000800f0845040c10301950016040c0701d41d440342101c42640100c110001c1940020400d110000b490421a000d4403050841c003500d400005075980c0503035000101c460045d00c0f081e408024681c8d030500190110b9220740146400304644100301010030030340c0d00d20194400362010b603070290031 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 103466016 1250 103464766 103464793
    0x10806031e010b090a1803050304060b1537080405030c120307090e0411090901110406020a062f070309080607030b03010c02120f161a010e16051209 65
    0xc01d40c0040c0e056035100c84002c0c80603d01243d815070011031402c410404403840310401011195044001000d000010002409000459003c10140c150103009104084010400711903213600c00d229600100c0410241c140e03c403201d0103000090340f40220b21101d00ba5107451010b40345c10340000c1040f5800e101c1000010040c100610441241c0104410700329140e04080f04040d044108640151a500000c04200404a20040381540070050180c4401a550310350005050240502046423103201e90001800100b0950008100715024019041000650071006c0703032280c140703601019000c00c00f00000c05918404980da00030214213109051040d081607035000e04600b4501c0442c0e0300b002081e51151040094103082c003524a0b00032652002c0c24041c1542d00b5010403c1c0039104944603440408a0146880c40c1c3c4401101d1302542c000d140120400ca2611628800a2090040180325540309020500c0d504009054141c0c00c540d0341c41d511f040c0031044070b00e440042d000030300058180c45282e1808100 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 103467266 1250 103466016 103466053
    0xf09060105040924050708280902130c05040501090b1305010f0c0b010f2309070315030c030813120f030c020d020d03020d0e0a03051905070302130c0815090601080603 73
    0x125140580c0200d49860901806090b03c40000c0c15803840743c88000c4141c44e2301010780380c10020301850000004000308103001003840e02403c0340d18455107074684606800701d41d4010000d002110401d81e82d21003405d40b658680307a00303802101002000c081401c80300348550346c0200400f041e545900c1c6080c058400c0f00340c0703071000d10140aa2042c0ca10340103000050140342ca20702030144460003e140c01d4150317a039a00010484200000b40030b4010075903113507000588a11824070140c020341c0c2103801800003903201e061101080d13024800b50b00c03008040601c00034081c0c440ba4800803c031034000802c050550003e071015a142a50042d0807a40500d0030041800142d54050b544440c2c0f0303001c0c0d402000010504134000d4802c50240409512682c0d118104200140d00019148180583d400800344407501a00d0050f01e484210740000354401441c10345a44c040481e81e001e0050b04e20b250f42d5001007611001211203152604459890b001038a50000600f2035015510300350304820003404444175650301c03c011041 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 103468516 1250 103467266 103467323
    0x1201030b0402010e0a06020c10030e0102270108060303040303050903010f0e0a060b1207030609110d120806090f1f0801180201090e070807080718030b0604050f090601050409 76
    0x800c5500c400511040d0350b030000e80340c0ca6140b004c0e03d4031a034290400c200a9564841c03180054840d020400040301902c2c4644c02c410800341d0110000c0d9111031044030000c100c400e943c0c4001c0305d21400700c1c446401d0341d0700c140c2006000d0701c8040d0185140c00d0458400b11210384c0030440e2550159240e20441c1d100018a20482100c0340e850300c0603124443c407503e000b41c01c1c1d81e0011b0682e0700c50705506843d074983e00d6000c100c4104980e440500041d141c0c642c0d04e45840014102c01015501200d1484180c0c188060303164040408166135031803007a9503480c401000441c1c00141c41071145c05410900007445040701483d06411200c26918911050703a403482d40c103082d0303088400052040c04c2d107120b410341196000341c0c22802503c00d035610264a403508903001002c00c41d00610316020060042d012803001c2d402803111512240c88610043e9042b41c50307003440b00c9a182c02303686072400303146048001141c0b00c107070110050054041c100500226441e02d42040083c01c01c503403054542c0d03164000350410384641001000c1 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 103469766 1250 103468516 103468523
    0x1180f090507030510080303010b0a2003040e010e0108060a0c05071211120c1b010903050304031b080a050a0206090f04020c0f0105090303040302070e10030209040c081c0207090f02120103 82
    0x40c95103007400c001001c1d280064080c49480d250300d1700034021078030003009907410b44110304245915041c110310100c8410038100c90064401034090254090480040004d1065410410b8001443d90340c0d801c04100c2110248140206908800041291922590000410303403103a80b0340750f4180903ea4032410480c0d480c548044001c245800010100d070b40301070040c066a101500c010a040403a8014a243c59404010040d0190b05032000614441c0e0302502000d409550418100c0f42c031240c4901e00364111328080144a0240444c0301300c0003c601600090f440c1c0c034940d0000290520586590a0107070359042200d5190f4007201c0c84049a04549451020b000502003000043c0140000500340d6404c45101074020192390304100704100c080b90300000c0070b030210390007a4088007603680c8950341081c80c1020b0340c0000358404004000d0105100941c1d0241c4203549414003503c0b02058a4504544041c2103540640090b8102d403204104030021544103601031f40c00140d016140203094640b4690700d040980044 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 103471016 1250 103469766 103469771
    0x20a08060f06042004090f02071713090e0309010804030519020c0a050904440717090a0303050309010902030a05070801061a16020d0b070e0f190501180f09 68
    0x40740b180f4250050400f281c3c04419100601603007031100d480310340300f14021024030790303144e411641111445504a40d0b4168000d00343c40c41c000070030b03503000749584d2003000c0d21001d92450102c0401c24240320710894021415050045140c500480015110784900802c2941807040a2000002c0060000007c0030300034003a13400740249001050401c1400405c5800580c06041c0c20010040020301c0c48032505401107c1c8a5141d107100e00710344980c009040203814040f4125401c00b40c507140c0c4100140603000c2d50b48511071650b070607100f07001030940c0c6000e00c070740c2a0361012864008001080c0a80000c1d90400c818500114140c80030b03030040303860403a0628040b54158882141084a64030030702c50580a04909254400c00d42202c00c941c0301a40104603858103513006203030400046544038800513107803aa0085520300249802c0c517010707224204512043c0d00400e424000c1710384030b1424080180a5030030039008000c0d0300782000011607007580d50030403010200c8071b00d40300824410b500c0c840304401010240f501 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 103472266 1250 103471016 103471021
    0x606080f0a03090e0601050f07080c010908120a0b01080a0b0301180516060201020304050a03050c0c040f060f060203031003140a05060916050613060f05040909050703050d050a020613020a08060f 85
    0x40148045a2007121144ca210040c04000d0381c1c08011545c071400d90400850b00c0b40b102d404c010310b2500c141641840c1a6181c015000200110030b005840c04650084110300c03256540c941c040140e0301c0a0b42c0c414000b440740382c0001c9810320b0130742c04002b681d070015000113100d0101202c00d07141c03a0403001040e2a1907014030422500c0c601c1ca80c020702d000d00075501c02941942040c0c9e6070143d0701e50703503044028244000484c504003540300812086040b088002d20501800704a0740200300201030900038216480c0e0b0000f000f1421500000480c1d0140300c642d442010f0403071541d114170400c4651203c18200790f0240c902d41301c01007541008528020741584000e0401c103c10b80aa48059042603404a8040c500500103000080002c812003402c50b0100d090428200361203400c1224140704a0b0003d203503140c45c100001052101c00907070b600a407440340c0101c5a01c0401500280c4450240207080d030016072022000a141540c031601c140e228500c060314441c409a1039101e41400c1110840f141795114518208 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 103473516 1250 103472266 103472273
    0x40302040e1506100e04020d18030906030b011803021311030711070e010503030a0305060102010608010612050607180b0a0302070605070f14030115051303080c030d060503060712090606080f0a 84
    0x201030380110007221580c08100e1115809800d0b05c000745100c501c03655001c03d441c002500242c00c11014094030110000054030b003407402405149140c01100d0001c1c4c509004803005500810b1754000014ad02c0350f60342d10691555003040f4004010218130741926072940c6040340100811000755015180f90385500f8480e41c813030701e0498541201644050f06102002c0c004016170f4a0110844110481c03500d000700306c556034040180c1c0544002e604c080580d611341040010585074009007081040d00c80c10030703607003a621002011201140807912907944124218000c00522015100031304c01d060031810098248440d54031042c003141c07802c85408004c1440048030180304c503813000206030108400001107046504145218080703081a134104414040000707420340070707481c0940f10070f401942e0000c407a550b40c000340d4094544a0b00512501155103051940108581c80c003c607002d4810a142e60b600d51980c644003100c02c0103402000b01c281c1d40c8550382c20002c0743d0440300303000500f0150800c07002804450403619 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 103474766 1250 103473516 103473553
    0x51e0111040b0d0e07081e01050906070e01120902061207020c090412031a060408030a020d020c010f030f0905060103110f04020909040308091e1c021f0e03040302040e 73
    0x1403040c050450811050001450101c00d55240000032800001d500c04160281c51070a41303207400108040c8520f12846501c2c403940c10300c807040a005200203022584440c8a80c0e036542000b640c00704041846419840078652189141c85003494030204040b4107440300ea0007291190b80b110742c0540e41c210800c41008480c640400401071880d8042d6280031551a10f40c8a603903415896030071364400c054494410070761040040c64550b01c80d000c0184410350703d035039641c40b40e640c031303486002001d0140c050b801c6020a11800441c0c41c1d8100001238403040500940360340128020494000607010399035540e0307525008200100000c502031231041d5207844c4001b000004011580031100d2410f403089004000090b001d4842e0b0400541090f0b160520700c41ca900c5420f0036030b041142c0550b281042e1041e84400c08041e01c400280c40034115880070010320301ca034205800b00c1e161800340c03480d03035440410075252042c119282e03401701c1c10781064101500e091945944c00141619000c5001140039403250709600149c80004 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 103476016 1250 103474766 103474781
    0x170304150216060b060a0e0f0f040e0c0301060501020706230403060c080403030f061818080d0c080c0403120e010201110d050a05090c03060109050a09140604030305010801060b0403020d020d051e01 86
    0x5c860b25810303e090002c0040000e000500e00700c0c09004a141e0070b982c283c40c2c400712181000030040051007840704206075541d503030404070340081c869070800304c0016965001060f801c003035401c142d680c603000d00b03032410300702030783c400580048041c0c40410840080407a4240c410580c01c000165aa08034a0070720b41001000c2e100d82141c001c20061a0000402c10525108400801c1b2a95182d02044d840c10200364603869081c0c02d44050040003000a0700b20341c5520560110400035a103840d00300403504c07646004105c1d4055400700400125a00b444203000c0c1c0d0003054500342c415030502c00812000b4208000d14039580100d20122a5242c235001840400d000e140200303503100e03003da001000c0e11030203203000030790302d010600c959008203070386101160800300190441303461150040410041d0981c0c400c040c0d95202c0007110241d0009107450000f1500b108103000b40021070345286001d40c02e060035074082185203071010f0000c9a11580c200341c0b490003e4000d01882082e1410541c522595880e800c4a00f821344048 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 103477266 1250 103476016 103476019
    0x5060705030c0403021509150705060702010908040e060d0606090606080a1104030201080a230106020d0c0c1a0417070f0b030609010b0c1009080c100603170304150216060b 75
    0x620401040303000c4542618216174044510610310b4040d00e194680502c1002c203043c0d0042000c481e100b00c1028a000100940c901c50811581d4556030840103e0884107241d00c02400303140200400c00003445a015140d800001c020301d400d06501d03140c1d4603807003252070950010b0001c03912107800b0059290080310585d8040482503040c070030850f00e2040c1e400c042c0700c0c6020003818413050310003081c1022242ea00070041151004000007a800340380301e1503ca40e0000340320b030340d005104140c1040c03406c41c8035691112003039070b04c2216196294140540c0302c04e1a003160084170740c01c00d402d2100041c240f09413488052a41d1040c00503100450405d802c040c0f60750f860760442132100301c0c00c01c1032224a032182c140607411128180581600c860616402e42d0500710340401c500300403814082800306100c044002003a054003a4030807034025034440980f001c2990403512003d04007181c4405c0c10011a001c500003503a000384220808002c512642045030102d810000e8034501c54881240d000301003105502c40d04045020 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 103478516 1250 103477266 103477277
    0x40b09040b01030303110c03042921061507060b101806030506220b0a090c0203120c1b0606101b023318091902070c150309050607 57
    0x1001d40354507a0109040c80300508140c0d50380c80252a0800320780a0314070104800094a5645d955040d140440440c450b100c20031070141c0c1302860064140307080403603140300302c4061a10900c8810fa051000c0584004241582121002d0480c103103d1805600034050140b2a51001540310300fa1400d000c01400664550f0f4188450034007420082d41100031903104480c80c600d00402c1c1340e65404041447c10402d4807030110b00ca9487d5000307104100c1c4541102401304800da0718004c81030766a454020503602016606030150300100073303411a10701a141102c1d800711a21884a2400844410065405107051101c0440e80c2001050000c0341c6000b40c103070380500c01300340b0f407607001051903042800c4514001e54009102d015000101a80c1c9508a90940302c02c1481d142140c0c2580c2c0d0240c00e51402d03a2001107805100201880e40001e6880d0203da01c03809505542014060b103400c0c840940002e600030b600503564030748906000039078291040100d15132200302e40d03004220074059190041c94204090480c0c4140318 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 103479766 1250 103478516 103478521
    0xa05040b0114010e06041404050c09131d0a0302060121020108070507051c0f020c060c0d12020408060109091b030201021c110f010921120504020111010e010506040b09 73
    0x10444103a00d810340b11107003030300b0310944241001622022446134031140c0144001c40d00140c5642505905801d81e101910240595514000b40490900c202d4819960000d0640f100b07180050300d59004110300408044c0007680c0d0350300c5007200d41c074048002c0d5045006a024070010300c080c41142d91400d090586076020054450941da002031b000d10320041c004001c0020210340002486010071000040344518441c41c211440949070081c1714a400f4445e10004d0700c9140c0401407541009000c581e00c0a04030f9018080c4201010f004581022030401542741154092001140310081400214001c0c140b5901c0000c0380405490f180b20041800e0020204a5a000c0c0301080941d0700466070185155004181c0c010344003440340103403001c00051008094074880d440c826501c4890540c07080c00702500a000003400d00a903003401ca0075211101c03690030300245079001d40c085030304016000960050700c1410070140c06a400c8049500311034200d0000d01440c0c0d1140b01f80806030820327116007036030440281c55180052 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 103481016 1250 103479766 103479773
    0x1b02120903100213081002272805030d1403010e10080601080312090f06010e06031509060403110d020c010f031116021e0607080702041b02072103271d09060a0504 71
    0x851014004042e1401d0b0f09042041036079a0300c95007000015200440352011902c2791000c5000365072340500c90003803080184198040d400b070700e010320103010f60409003440c50382081000c0d10100300c0681042c01c80001204046000d90f0207002c00ca01a210000085803941400780b421003407180007030800c420f180c20841e10305030018000710f007007815154500080c0000b629850040b0b40391814030600c2e0701500c0c0004c0140300d200d01c00403407180d000d58000e650b001e500d8000c040348a030702c03034000d2118103000d0380c401110b41000307500400c107480761b0294505000500b0342c01c102803d01d0720350280c3c40603009505807801201c01c602c1e00c0c0d482124646034040c421008061100c01060a40c03086d1040a4020318020400004640d80d03504411400104001e405a43c0100c45102a5039803d2078000d00200c1000901e05242e21707003c0b0412940c016801d41d840d180680c092540c00d40c41c0010034400a0344d00c94010b18003040d1880c803001c1c01c0d80454600c4048951510341307240c6840c2807480c00f50a9180c054201014000071 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 103482266 1250 103481016 103481047
    0x7080303100b0913050c0c01021308010f0b1e150a0f120507090612060b1b21070b04050c040204060c02090f010302150d0f0903030507031b02120903100213081002 71
    0x1343c0c45050030001c1d45442c2c0c61016030003400340c080c024450350300016010801814100d040d0045a1000009000d051401800123059034541c1c02e03080e4005c0c0210503d00002c120b5015000c1c44000054415501b040e10900c250840354401d00031440441c1da00500d1080e0580e0002004020a0021038200414203020308010041711407441034500300aa5244c1c482c0700401150700a4000f8418442c21b107a40c1c840c1c3d500c004914501210740b15480c0e014a8041d0801d0f0407080040401f66400314119034a00344d056500d420419801600036103440c0b18a4500c5100ca4072503100a1018160710344032080303903158501c10040180001040076003000000c0300100010303292040700540002003050481e0702c60b0003040d1458002d00f58026005d0010b42450400424140c040d4065030240c1882d0ba400c0c4858240c001d00f800100c1904020607005a01941e0021400c080030005020700070401801e584040f4442c4100321b0907030b0040c0b00100c0303118004c44d10403c5074442c2000000070f0780c0081c8105608109400074031120 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 103483516 1250 103482266 103482289
    0x60d030f1409030102040603061d0103050a0311010e07080303190b03062809060b0406090b01020d050a090f0b030f0601020d0e010503061804110405130816020604050307080303100b09 80
    0x40c000352500e807022042000e070035502c05240140c000c40d15195a04402070290035244140d460344503440090311171601c0c0da001890306a03a0400001c1c1150b11307650340d0440708094440c8083c00c540d50b079100b1aa00112082c05800b0040c400d0500a50f1a400c00c0c0d03485030f0080c0c10440194482600d441e040310941d44000c202c1036800001d14000020000d40409580600c030000307034060504915011a800070810150b00104a030300c0706031400c0008075191103120045915141030180582d100480081c41548960003c200c11180b52412000c80c0c0d50325403100745050001e42210303078a0b40010080108090510001c2a400b01c000d10051008100251018104a0340d03000d00700e0412900100180c07941d11040d030f04024001e403504201d429403a25007000d0354a00c8211081920460a00010590800400f44007800441e08001000e1a081011000c911000c01440b8101d03000a0180000603942c0d0342401078100030404903001e19078914102401c45c584141c69000820100b10500c0500096140e1a14401c0d = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 103484766 1250 103483516 103483547
    0xe10050c120702031c03090302070e1905040c0906092313060e1f0209180c09060904060b0304080703030e15041509150e070f03050a03050a0e0303040303080906060d03 73
    0x80d0358100500110781004d0070b110040c8030003526912051403076a171540c000c20440c2c8c001e90075585074649408900101c40d100ba02d010b0f180703d070401000c5502c1030f11035000d01e030410711541c10303d01401d598040c902d054883c00c0e0320016101c2c0d6900e00131580c41c140c0e5801928541c2c0444c0d80084549859248007580001c46003001d00420b59600c50840d66141c10807074000302c0304280b0b180c00b03503a401200402d07010f0360260011900811031010681c031a0801c02880a00800840c00428104030302c2205011260300080e41c0c01e0780c401d464260006246280c0c1000b0b42c01107009903483da0781c0310524200607040d2845128410821b5000740031aa00003082034102a41250b070111a281d001c41d8003150f410003030041d5500203801c0c82c0c081c548100d00c05900d50700290a0b2000c03402038540342680c0e2000c82e803942105220140c4140c004e0050301d80044d00c03035030041c000c04190741824a40360b241c0d000468603540281e00100d010030244418803032034100810035503038014012543c00398080015500204003914407403081 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 103486016 1250 103484766 103484803
    0x9030a031b0b0c07060e010506030303130302010603020d14070b0c03030703022101180c03180303020901090e13150218010f0e0d0606141203070209060111010c0e10050c 74
    0x110010321030100d081c440ca8000164031160304018200503500d5200000407610640317094040004000d040c041c0f240316500c0100610305503511100c200e2a10710200c2e008800b1075684080110050b610307603410b10180d03401040c8005c0c1018901000c0c900d0200d0540007075080d038030140041e54540b82d00004882d44004c031403401680700c4400030800c9002d1480c11103051503101e1414008150000002102c4181030b00003841400401c80a48060702100e81049101003081e000340c42c0c250120340281c000380760205061501c2d068541d40d4240bc008800d105503139080341120700000600c1071001c0b007540c1d00c15040c3c628108510b4030843c1400d480c5400700c004029414440d1600041ca800e0703000d10b43c440b04502c400b902418511119103080801841c65000b0101c0c44045180c0c1d2007101d06260140024145800000318030342038564027005103000000300418100003981c03901c80321000d0203006115a0075074a0310b68440c001c84810810419044070b000c6903080000c00c0c048803440400004200c01c2000080f00403 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 103487266 1250 103486016 103486037
    0xb03010302061c02030a05090d0c0201090521030301090b030601140d0b07030f0e030903070807081506040906060602010b0310021801030f090b01060c0c08010515060c0106030b1006110309030a03 85
    0x1500b02c0034081e811442200384c800300820110f1000c1e5007040348180400025200c0750482c1400650f0004482c040103030000300845010701c41410700caa10004110f181300a9aa40000005005441c0d540b00340c12217011a9245d00ac640050306080040c80d0140c190415010103448441c8040740031904400303409064949901c0c0881d440900a521201407400e02200900601a4030341d0625600e81c032800c5220300901c2000d50000311141c000c511003040d40c403620040d0209100c08105d500303284402030301c09540140c2d2450a01c000500510486000f490f0903000800c4001c7c0c01c10400d0704249194a5200350140104401c40003443c0880688011010900740001d0340f010f14000c0a006103030800000745400c81010012481e19040107218000f94440d810405666856188440c00c0c2c0d10290361000c804000d150f8550f1003860a94040c1811541e0f207400014500d9481d181c40014007810303114200e51030b0326043c040c0b040d203034400b80560b1f8880400d80194030301680705010076074070002c1107000750400415001 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 103488516 1250 103487266 103487287
    0x40f060633030e011109030c030708060f070318030819060303050f0706020f1317010e0615010507020a0e06010f030e0c060310030c030b06040e150708060a0801020c0105150a0b0301030206 82
    0x24a804a4108000300a80400c400d01200a540206c000d1071180c03240b4091120240b40026800c010303034810741c2c0178000300c3c2c445100d003003a0200050a040d05040d1102c081e52030742990440101d828174001e9640703100e9070803d04034004984004e0a03043d90304a0070640c0c1480440d40210440e00310310754288910b07558000f00d0900b00028024551001c19400001a140400408011004042d143c80e05100c0002400a00c1303428200ca08403030660603a82c00030000240c0110340c04080740340005040c106036142c001030341d0010701c2c080016000300041a01c2c41042c0500c9590060303050b101ca80250078100301c503a03110540700766100d40d0450321f0351188000000044913174090500820081d03170700c2500011019101d00e0400202d074000ca0f00540200c0c581a5002c20b90f4030300240c40480c000d051480c201258a0703114080710803400040c0020381064010400040c1c00200f44024844003910000000c0d08e4144076851440050401c1358051180b100c444040c132000361541e044034112581100d54560f240580203 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 103489766 1250 103488516 103488521
    0x8010504090b0609070212130e060a030b04060902010c08130807060f020307060b0d080c010b030d05121305120a110601150f0509010c0209090d0e0306160804020a0509040f06063303 79
    0x801c7c00c046d150085250048a0240c07031032001580d002d5815001d213955280c05000351100c02c2d21001d800c456402010a010034400e41c803611590b401072402210034003064442d03020a521546600ca400c80380e5140030000f01c0804d01000300905003600c3c2a800c007220301e0130002c0d500c0c00341c0130024140940c0c540b106280f6a6941c0c800c000d1541d80322811a4030baa0350502c0c054000d26001c00c10341d00034001c005862140f94800c03011910680c5041502240c0780d110110049201c0c001c007a0b045800f48a05071201e85480c1d41c6c00b01501d0302c0c49180da07070310441a031050342440c14400181e0054664141820400318915040401c0b0698240309290640d1103403420401240e24a180d000041e4005180300c0c10300844500108490060500c0e036120051240001005d00da982e803022540140388121401c5100ca4076031003440d43c107170070900050040c01d841d0b45490003d030300f094003a2801c80e2200c8450300c101d4100011401040024100d28102d51000d00b4a0040e4000d1442040d06134031480e808004071600c2c0a0203039 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 103491016 1250 103489766 103489783
    0x5060406030c03033906090302120c0f1207020108071d090408091e010e010c020a0e09030901020607090e040f15110a02010e031c0504170c030a08010504090b06090702 73
    0x403201d9503042e900e003006095134844945040d05025440c1c40c100c02400102e0f0440c40140781d041170144500c1182d2a010001c10030034200320304600401c0240017009442801030310880c240c0c0c202404000350301e02001440d103034a03403905c0c8015a01c24840000580e80100c00541d102c80141000a005980c0c2524a292001020000d40d0700c032400d03205020522001d0809080c0b45501520110b030111040d100d0462001030b088016400661010b15480360341d40304208030403100d8400340861184a440b0340c00703c00400011901d0300b00c13561011807010169030341003051503040b00381b070306142d60001d0030035600116003680288081d1484c046803000e0401c208150451411a11301c420b003c0000d8104900354065a85c8048540b20041d070910300d0300101c6000100803182d60740446190f10b5401c0c09035150820180c42d004109890698020b820040600c3c500001404555031020107113aa03070070700385400341c50688180c20407400340740b80c85590b0000400d10310042d600010111626622a500c44070100c0c40c1c000e00 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 103492266 1250 103491016 103491023
    0x708030703080403080f0424020c01020414040501060521060607020409030e030c1801120f0203070905040b130302061305070503070e040221060406020c1002030112060c050a0c060506040603 83
    0x80c80a00741a030080c601801079100350ba074885a41c550180d0403c40440c241c4002d058440049030940b11303165003110100e0181c81480f400740c10600101046801c90f00b1551209004000c407183c0702101f403911b4030800e17026108504045080000d144840204078203800c0141c01c0440d04103000c10941d54880c000c2e1446c00744c1c001c00900c0703140500e1400070b2090064490f59802485aa0f04070b422034500700c02c4c4240c20407004410041e50342c1c40e007203081ca5144c1408100345d4881c080441d040016803820f000c007101400c41c810001c20241040c0c070f0b0807100310500400c2c2a200c4001072120100081e800308816400c420071011140742e80c00c1c2c078188281000703071a40c4a19407622544a00140c0135801007002c030301c541c1c0200c400200082c043c40075100d401304400100e60b4036401400008000580d07070360103422507512400480d0801d00840820504a034002c3e0850040740690b088103c2c1044501c0c0105007040003c0d1405900304200300342c01402c15602c0c0b5000808980e19103000420701d4813680d1041d0b0043d80c1 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 103493516 1250 103492266 103492273
    0x2030708040b123d09050108030417010c0804120e100903050c03060105012307060c090314070e010b0d020702300609070303110f07080705030709050f040b090708 71
    0x42d5001e203030007541d002c4143c42922001900000b1140401c801503202c030070300700700300c00d03400d0a800000c0040750600d041c10141680320341c0040494006080c0c8a65806001c0e01c900840e66141031100c914414640403c0301a09603040c00e4441141c280d0205490b60000e1344001581070108034041c06480c01280015540e801004a0090031203190f4031a02e20700859000e00c045e9401d1104070380625898030404d014050200301344a1040b50042c407960480001c4a880740006400c24416540da2030984494820b45000920170080c1403084c4100c201c0004074110703000000f0181d5900e400090189003005105050749900c1c0811600c280300103079011200c0c0e096004200d4090f181c6140d001e032070140d030000c00c01a0340307080d01c158400004d10001041c900030030b40d210040414a24681c1c003281e641c200324103048814001d805c01c020b1542c408001d840d0141600c00003400d011401c21092520b021019800303028012300300420b20005144001c5c28030f07005600000c85801590780e1044503131a015480e48502c00521 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 103494766 1250 103493516 103493519
    0x715090f06050105280e18010501090b120a0c180902040f1a1903020405060406090e0729090f030c0904111302030903030a0f0b03030715060501020609070b03070203070804 75
    0x9040d4060307816920112200800d04042c030000d078a01950903004800602e500510a01003400e00d0480c0c140d00141d031f8007501c100c4010706520070342564003c2e40281807143d2100b8441945141a2240c0c06c0055100070040070100c1c45c070b48a1148400300c61107084544081c1c0c180362024a152034102240164028005104090b082c0c0d403c1001000c404003858466442c1d202141a0345c600081440b45000001f004292041d06640810006010103440281d001d1f0741e0b980c0000b02200d80d0f000303e800c079060000c040c000452422859010914803091009018041034501140c68500b0b042030b0780e000202681e0b000c0f201108100800d1422510340341340b682c0b03d01544208401c0009044200e0303d40107054030b0160843d40c0c440552820390109551400d045d420070310001d0f500d4803d940c480094050300380e00100b1004a0100402d0443d44003503000d40d92000d840308a88200307560b5000b001300500e000e100400b46807504900e12906c54986001c4c82108800010200c0e8003140700300180c40c5200c2d0044032040c1e40f03d = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 103496016 1250 103494766 103494773
    0x40b1012030e040f0209090a0506010306150806040b010203031b03060301020f1b0f030403031d130c0c060605030a020105070210021c030209040506010c20010c0b09070e1b0715090f 79
    0x10b0104060192041d070500901d490710f10348074000e0ba4600b4001400300702d419150804010041c0a00410003410503035111000604150f0010040d2000845034492503102c4c240340050000381e65240702e0b058195841001440898404856040340c003242d41d04070f05449071680400603000e48120380001564003c0443c00141036100201e03140040500c080440d24401002c40134252a801a488080c0c04100810340181c40f00c440c64030354011610000f4501d0740c58405410781c40301118940b000381c030006100d101a03002040014800c00c005460218028a001c500c2540000d0441c42940f030001d015000c50040405501d008124500702d41c104d11407008015484400020001d400a604052141c3e007440301140702540148a02400150003412040d04543d141e103050104034941c0090604000c445141600403a0643c010b0b03030f001c0d200c0d20024241c51494100b100c8101d00c1c02800c0c601074515100800b40c54041d10b41e0495039283c1c0e101d40d49409980005040a0040070340f5680500058102203410007003 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 103497266 1250 103496016 103496027
    0x40f0207060510080105090c01110c121f0b031209030703061b1229010e060f030103050606090f04021c02030a0b0109150b040e090118050709050a05060603040b101203 73
    0x10f90b009031a802011070340c40449900b81c44007510400b156421a440c0e4070704c0e0307510909074640c0c0d00001c00c088034901103046010500602c842118000707660084d80045103a00441c1c60201403068803c1c0d0b043c4180381982e40020740711700ca0180f04d071a4928000a019005d500c040c4280310080d60864000c00c08031441d002d0701d50b440b686d0b040000703000807503200190300302c24811720460703110b400d146488412509540c03071806012a94088aa41803150740c150090711030359038600030a200320003d01c1886d241d525500d03105150140c0a0280c0344245a001c04200c0083c0140203050780c002d4040302c10f108946184d105d0414035111440002e9010b000f21401780b8280704004600d81e048481c012810040c0e069106c2c201c581d4902c09000e1045091410041003148061300f0300b4460700326803803a00009100035002e0b200e030700c4040c44034400c0703070250401c40301080703030001611520340d0214144034203002e68604440052319034400140020055000000401c4490700040c038040c0181c0074401c21034514218a0030301410 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 103498516 1250 103497266 103497271
    0x90a080607020616080112110613120c050402040510050f0f03040807020112111c110325030b010c0f140f010e070b0c070b0c010b0a060e03010b09190b040f02070605 72
    0x9143c4ca014890031805482440b200381203501080f5000e251401540c4c50300050075403024101c4d030040c4d0501202144804241006004112004002c404503031145007009180c41103502042c861441403204002944a0004038040320350146045991541850b6a03070b41c060142010280e09482c0100802c41000080307001010a18002d1b25200c07244035403034a60740255900705406801d031100502052500300380d01c6182c504182895040411318540d003102c107001c240c02c00c641402d070f03441d69100001c0f1040c0600c12000050462031500b444034014040010b0710302d0350011002001600c0c808000d00034031580c228031014080301801952003032554030240c180a000c81d140980614011100006111381c000070851705042040005402540c1c41d20703292400d55008600945d045548031410505a50384006030b040107000c81c1c0e00c400825003c400141b40c00c44104442507406901d40406000154900da0b6080609050a42011032030810301008500a4002c0a1800d00c070702d40081102020030005070070092 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 103499766 1250 103498516 103498531
    0x30408071d060406080709020904020c0a031e1103030c07051f020c01060504020426120703030501060806010203070f2405040803010302010323060d020a031406160203040303021002090a0806070206 86
    0x140d440b0700341048100c607210b1046000c90b0740100300030407240d000780c3c01914411400902c014204542c404035103081428103942200089c1074003e000a20116141e45040c040015181801d59000c0c0f040440c3d54910010305040108030010490600f009001c110180c6004a1a11510400c5d81d038180030384003a410581c1683c140394208400811981054820380d006c07542c51b02c1d000000f07202d5903d01184110031414081440b805a84225800c016914000b041c030544296000034085d0f00d0680b00514491000e030074181190006c020f0710010500c4001c00b003041c5500700041d601c540400060511103458105d51003504181020200414045107401a41c1202e000780c0f0148007a84c10b00010100c12407003e18000d008007030020200d4441d04200042410b000d00c003611001c0c5050f12900c854540401c19000c1022036840b0004000c641c240d5416009001c0082d0b0000714285400e554001e512690303001c031113000065021850740c11039518110f0000050038144207a50560a04801c02525140d04036960b8 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 103501016 1250 103499766 103499819
    0xd0e0f040c09030204050619060c02011205090d0f020f010908040e0601050306011205060d21030605120703060e0109021215060108040209010e09011b09030b0f01031a0903040807 78
    0x214264281806220000e1095036185001c03030303065500304801020b0103000c1e240c002c07030860800020500d040d0024000f5101304d4540f0280e1110603c00140400040c1c85068926070030f001c1440850400018404a41103107400c1c800450090348900f01d103812154184120325601307001000062101500041041d12182a0403502c2691174800540f040d00c801d4a007580010140c4228104c4021700307034089500290000d00e070400d0507100c0c4c0c5500c003989a1611b001124070003e01c5a04400321f406124410091000f0b552081d0604040305402e9182c114911000e4000d5072105014481d42c50300b0350100d20039550003007201a80c4156800c40650312051030110030401d01e5028041440d6601400300948500e074002c0c00340081da0f09100c00302c0351410b0043c0c00c0b07242c29904c4402e1220599410f0403083c100c02255078034180280d1071401c0038484148060403a41d074440413180107201140d4040000724407040940301c00da000f070b200d0900c81440c510035030f071221045000c0d0300c0d40410a601c081d0b05081900c10140081c = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 103502266 1250 103501016 103501039
    0x519020c0301110c06010b030c040b0c0703060c0306080f01060312030b041b08010609080a1101121805030316080c072301050106020606090106210c0c021306080118170310080d0e 78
    0x1081a83e10081d50490349c5801c042c4420002c0c400c5610041c500c821144060b20b80380b035681d5a5003070699500300ea4800120703480d48800d108a80080204c035405040c400024401c40d450b40c1c507800e910b041ca40c280501095250f0454203c6134580d43c1014907d546040710411903800e11440080500b80d0a0140400048038500000b410040008285103590b80043d9081204d10914005403002c6000840f0360071102d40f15544100700484202130b29a0017030044025607a00d1400c14204bd800742102d0750203400b402001d1043c0500e8509800542d281503500101100006940c442000e840a4143c50401035960034a00080f402c60341c0170a000e802008255040d0b5140c6c1d03242d0006840004c2460042200190f02004109485065402c4034401c3d402a051802000c0a507401203180d043c0c0407841098150740740c5104001e0004244582d11050381d44241c1060005080e03580d0340400001902c800c10341400101c040b030810700d007030310307c0f04000c040042c02c40b018070f120500040e090310000c00e2124402c0504002 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 103503516 1250 103502266 103502279
    0xf0c07061701090c090909030201060905100b071205120907090615121e0c03020408100b03030711060d05040609030207060207060e0103020711030708160b0702010519020c0301110c0601 81
    0x4000504054092034440303a801c1c0b02c40f00d801810208003000810000c020000780039403203842030705486800781c4e0012402c28100080402540c01c0500058050001c070f110030040405001d0a80b00c2d141d0780803d2005030302034100000c840728065005040c0c2c0c124215420300410240009600c4200c03980c202c424030201e83d55034803d001d002c041c88048004140312030701051740038005900400790502c26a103401c2d101e8644901080031290b2030f194810100750b002a0600030288200069007030806010320034400201000d0203c5d84078001c413800208502c3d0110001d02c207075900c0e04140c03441844080d008220600e4107003000d401030004d0280030303005030066000103d0040e00c0400c1005c20b403503c0f61200c02440d000000118025446100d0a4440d034001e0078010005035804d005841c000c203240303001001101a0a00c00001c0c481440c0d0085071803d108204200060360440241c1d81f00e80d00c00e12400c040021840001c0c0c2c01c00b96524003003603155282950342c035600103d403070180c6072030324220081394016070f00c414 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 103504766 1250 103503516 103503527
    0x2414011a03010b0f03180d050a09051c020603040c180501050f04050702030324030d1716020c0402030402010302070c08100e01050f1b040308040602010c0f170a05090708030f0c0706 79
    0x502c0c241d0b030404011009a00b544d240096402c090041440d4051000e00c114841c00c254034039178014001007002800341d0b81150310014a6000e468115a8140c11400e50101c00038030601d003c100900072280400050184032049602000a1081041144900900d44070001c001c05003405881c4c410f1030b02c4260f218450034244195440b448154006518603140d45441c090052002c1d1a41c0301d548903107600fa107045403818000c0800c103200300c6d213410f8444006140300c04440d2038001c1410018a42080360003810303d500082e01e0b882030000703403001a504e448500049020303209a5070041c01c008100c2400043c8100002000d00c1c0b50000c18808010420209010b5800e9440c2030b0340c02024906076070080b840304403c840c8021500061070083d00e00e015680d0b0760b0414907404c80c1d4080c8002d80d55414804070010b0f04104400e0b020620380c40d100058418100c580061350034042c0c600e4100d150707280005032100800b0042c0c0c40207040150200d03601d4504d0441003200325801842c0b110300600400c80c0c00158140140c = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 103506016 1250 103504766 103504769
    0x703080a0b0a17030903010926070b01060f052b0b0609060904020c0102190807260a0e121812060702060103080c031308061605040506072414011a0301 66
    0x2c20360160580350500c5002c0a16a22070140f02c00c0c0000c124840b0195000d2040745031300391051841d80c0015020419418010000c4125040030a40400c014000a901c200c40e25054800300d09000c1c0c80c0c040b001c00d003260326010b412a80e1286850000e07180100448000840c03c0760a8402001c6c890303503800106100560203400e0015400c400b042c480c142d1640392130703005030000221241c001401e060340030312040c4820391000e2941d4007180b00c0740c2c280b080095205515811603080545e1f00401d845198200c0700812200030005c0100641c0d0b04444550381206200300580d10b05000c0c00e031a100e5070541000d42c08405240d018910424044504002d003a201260540c801e152580141a050b807954455030240d500540742910113000030031100c0c0580c0340011845002d041403030003d0403246010941050303100c208a142d00d0a000b020300082056a540300e086440d0f0560103100c0c554810300000c01050300f032102c5009048031504181103058040b8509000c0c904030f40c18200903261509807150480d0b0113100a = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 103507266 1250 103506016 103506019
    0xc0b0406020703020d050c1503011401030203040c030308060a05030f01020a081b040b030a020c06011502190c0b0702030102070b161404051e0f0406031b06181a0f0a050703080a0b 78
    0x40d400b040035140c800e0380d03071001c240641d05941d11507087da00080e00c07484190b00c110384220340100060082130841c0301941d00701d89085c00c0840c40d40c2803a803a07488102e010340c4001401c100181c0e00282407a01e981d26031400522029040710101c6003e000814080c0d000a95554009000e0900090741109170f07500014204074195416440c1c581031103548903956000401260300150200141c9404407001c1001e58020202d14440205180705080020300384441c07050517262214442032048007140044801400b1078420900c22580c80160740701080c0a030082520292045001c8000c00c901004a603952101541c416a5118038a840ea00e65240c141d015900a540d0004a46c02409840850004550050700c000800c0d4919120440d00082c0075100c0940080fa2000c04400d16005800c40341c02606c800303040ba50401c510700400c034100024551000d40304000307462400b28403510240d42c40a045402008030042402d6a4002c004009887c41c1c0c0201402c90020382d101d80040c000c400b0314411301c0303483d440 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 103508516 1250 103507266 103507273
    0xf0f0d181a04080f0c0a0e060f0915210712080904051b03070e041808030a151502030c060c03010e130222050a050105010201020c100207030c0210020a0c0b040602 71
    0x10444a000300a142490300301c0710395020040810950b404201d0b0900040d0f545004020a0300780f141404100e080a600640f040400c050030f1140070fa80d0003400441124059440c04c0c481d03030301c1c00450f405000b200154541c00440d032000c249003482031000d803118010141d00403103020654850f10440400b0440c030018007411003e1110212074682504115005245200c489280f44c0e851001281c10398000d842107404500700025810b1542414085e08180940c44140300ba280700c510b4890342d40c0362200401d8030591315a216010110058000075001c01f0f04001c1c4c282d030380000b05691002e9540e61200360141054840c0c4400070700141c0400007240e068417030703074001c40401d17803035010420b0300284400508aa205c0580721161a02610408082c141c1d03100e40c1c003020449090078031321402104c406800c014116401008900c59029002543d074000700c40461f401640c400381404d00710f849001c030302c50003135100d0038120801092a07400147c0310040750103054170121580d0b0b541061015885188907000150b00f = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 103509766 1250 103508516 103508519
    0x200409111804230c06030708060114040f03150204080102040609080610060f0503060d06050a02070204150803030f0405010b04051302040c210c0201110d0606020f06010303090b0304060e0f0f0d18 85
    0x98071640b80310350f030a004211000132001e02e00180841c2c004880d0f000000700c1507420020720f9a0700c1200500401400ca904c0391519050a820340560304039800054494200a440216070401650445000b0300c2090000c40d10390761500c40c020f11000d0176118500c014401c240220712140504881c403011144583c940880c0051540c1d410380341a0401081181d21003d101c11441c080340540c010148685007000c1c00590321480d40c0304000c21601d08d000c00d08404007440b41c0c1800040000000c60381c0280c03101316004501e540d18502540501210340045401a0038202800b2108400e169096442d070300c00c83d02270190500c5450203d86942601c0e400c9442854503101011901c02ca503031041511011510001c9120b8414610740601d0368440508400481d80d6840300b00f00650381403240b90100c003071500c042c1c0143c0d491038400400e05003490007080090200040420b007001700c0382d1b200038001403a000c00d6511169030700211a440ea107401118800d5801a4107402106030300c04d071030121340601040c0b1500c1159 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 103511016 1250 103509766 103509803
    0x6030604030e010c05060f071209050c0108060a03050f070f05030c03060c0a090f03051e07060f030b0d0b040b0108101e0504141e1005060d200409111804 67
    0x110349104010381130200b24403521011820520100d80b04450000c038505031810007400c002d003c030b403200083e011028a004004400114046200c14100c2c40900c0d103051070382c5a0200280c0c1064090744010010301c2140c4002500142c0801e030603041700c0726800080d000c10381d0360b42415165000d0780e901d598543c000000050700b41e085a400741621901e0707450007510240d2103c1d1450450a0950070030384850f40040180900310740b60350101c0080c0a0144c001d40b00c45450540c01038140c06070b00d84480103060b16600341c00c1d41519440c400082154104a40308494105030600740341d0f011081c0200f000d80c0c05010f0400140742454066200c00301c23030010201000f40e031001c0c225002404060f100301c8144c2c1b80c2c03030b2444c1e810110420a10384490b490308800b42074002c0a122807032600400780070307443c4403a04002c10031215a8940314030049450700b0412080025404914902e11544174090a607170207450080c814090001c80f0801d0601220700303640c503103806400204c103004455021903009103c00307220007002050 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 103512266 1250 103511016 103511027
    0x803040f23030a030c170d020c1905070b0f1315021b01051b010609060e09100606080402040c0e0a090603030909060e180304080102120603011407120c050f040803030403090e0603060403 81
    0xc042c02040d00b030034086c0d90884040019032166184805d81030300840d200040010510a140d03084c035a1040b548040742c55696100e03185c501c035214218880304003050b01c0784140746000032a149203005c0007814002035258000c13499082d5450007201c005110302e05845951450841c03000c500120142c480605215a1208581c0040242c1180014070b54071800b0002c0c40c1c22243c01500007403e882c40e0b51150618040b18090b142ca1024940312409500b4000c0c2005066002102986c0150b0107450215210740d420350280c40c4100010201c40d0062103d24000a602085904c10029203210342d8a0135503542d6505005015a5894002c0e0300300780304030310301080c8041c1030024084480700b00b600c00c1d00d0419558480841c00ca81040d00c07001ca0f030000c0d11082002c00d140a02ca030004003040c20307101c0826810404c00051100e01c0348000c7c404520740d0782c200c200030940030340e0545039001a0004060703907aa8032038246580700e0f0001c0d00e04501140541801148076800780c8000f91048802130001d10103982d950301e045a1 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 103513516 1250 103512266 103512287
    0x4050309040b040e0102032e1802030a180b060102010f0203101202010908150f0604020a02330a0c020607050703140f0918070e010f0203040515040803040f23030a03 72
    0x5101303503a0400c03107101200a00296200e8407840d5a1218a104404e20a821130700508003800358441c000c204c20b1150904030b80407103410b0800c02c000140c0320b40d18071100c2001070500c9100002522928110101000b0201e036941b4840d450a900a11100c0f64506112040c4c1c0003d644000154292030014000000c0d10300f9400c13205801450400030496441c07248a003000758003034003250b00500e40410816490007000d810358100340195002c40c42c10b4500369000b511003144030810381c091512408128038032200805040c0d0940070104a842e500d08041e0600d030011300103007070b2000140c002c1c0c900080b281e500801c00c0e29890ba805032100700c02c00c00040c400028903880000000a40d03001400b014250b9116001603440303414808150204504001c00c0103001070700000e403201c0c10480410352400d46641e0110a03101250000c0d11a003910400044541d4818056500030701c01342d1001045c00038460440410980071074090100c442d1400c45900005140300118080940d0558000b448070000244a05000c91 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 103514766 1250 103513516 103513519
    0xa12142101051e0f151201080d090b0414150c0d03050405060f070503040b0c2701080108010510050402030411040203191505060301060806030c0316050a1e0b28080106020c03010504050309040b 84
    0x10b21b00281041001d0352184282c01409260780600c0284e0502c682001d600310241101142c1c0741d080c1850107040c40041194400c40c14001e0125107402c000c0c40d1483c006580300008050161001020b607114010001c0804403810340b014844c545c04918a40444a84180140525990f541c55907442e03840c0d22040e0300f07010307081d81e00c0e4440c100182e140d1121010300c007518031b00300c13851801c00511030030000402140040e00103240301e91410341070100f1840d885008004483e410785003d80c8a664505120700802110050307141c03c54000010481d00c0095400c011003051032000041103980000d284c003010a0540e4040c07142c00040400041c4141d501500d841640010024200c8101d1244400800d0501103080100c420440a5420500044c0f411840c214042d054203188080c0303030b032280d950300400c003105031180808540001a02124901c9580721b08800341c2d50b404401c50885902c0940148030040920030040180585545c0c03108602d8103001c0e6038080c5400030300860400206004000040c01d0101565 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 103516016 1250 103514766 103514809
    0x1e152203140706090308160e010914030a050304140310140601030209030a020307030602040f1205070605030709032108010e04033f02030a0c020a12142101051e0f 71
    0x400000f40d0034022016005d100303642e10741540c1400300001c915291807212010074040c0800c2501d007581da0200c040003c035011000707900070000100b0082402c180309000c01030024040010082161302426001120080b400c2d011511111520038019044403040614010203d403203c4c045011036200e60080c20721818000d040e240f0700096540000c0c54220300d9441110580c0e004101004002c1080000c04014150b500080f65042d9041e512140c4841e01c501a02040c0580400130951003882400040701542e8481802c3c161202d081000c0e8882ca043c1511000004414000104100d00000c9405000b15810344a00e04040c0d888098100132080300c10504c072130602d8080c200420000e0412292850380000f140069a034202001103000b0f4441c900380c4103080d94002c40c0aa00098082100e0400c2c00480d4600125035030640b8043d01c4081c41403c030201c01107500201000b80703900b403440d0601c0c102c41c02203070342c0c1c008501d042c215000394600e28051581c3c8040800070072800c500785200002c0b00e10315041101d = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 103517266 1250 103516016 103516027
    0x30c090a09091103070f06020304180b06030403120524090901230906090606010801030b06030a0f0501020307080f0c07031407050105090a1403031501111e15220314 72
    0x1828102c4030502e07400d480c0c285041c8800811400c0c00c1c050718018005081e001c10a541c1809406982c1b445113104400f8035011500303549007001369030fa006406014004041940c0c905242c180101a0704058601c1c09045150101003542d0303140107002610b00c1620010000d41c0c003a0101d0400103c81c400600740c10140d5203a8151038600d61a111123600070a80ca2503c1111506110814902c0c0c04801441150540d001c181801042d1ba044040e1604503a0b1041c148a150303034410b0007090401072884c40041c114030280e81c84104002040d00510b104440c03955850009944a5214a50403941680c92014600080100d000030030b100300343d101c2c0654000c0002c40d28100e525600d46017128400c451006881d000404002c0422084842220b03072200440300840c214140301400302c1c0c0e0805035040c61070501c00c40154424640300c0910251100507a42c1c649004030120000100e03882d14802000a031455455000103500400302411072030381000501d808440310700140c0e5098450344480342591621400a025 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 103518516 1250 103517266 103517279
    0xa150e071a0a0c05011e0506041116050a020d0f0b070305010b04060c051203010803070309080303041505071e03021305010507080f030c040b07030507060b09160f09030c0f0302011e05030c090a 84
    0x280310503202006003801c1045002c05000407c441020b840c080c450f504148550121101c66001d4404403c00d90802404900d00351a0040c9007669a4100079000307501600e40100307100c0c0b42c054440140c0d0080b588542e1b41d80c0e401004800303ea0090051000350031041c07000b8072090303200380302200c6050300ca00c044601018201ea55403850750002d078801000d40d80000384450030140e00002c400f00030300c0901d00030b5045007007a5641d0158800351a04034501c0580d51000124464420202ca4910800b00884250480403c000080c040e43c13005c2521041c0e8841e014001a80e0351180003110400ca03005114075040c90914010fa91a50f4400351640c00c0d013071070501c004a0b0341902e62006000492003034461903600c0e50941782c00e8040d54030101c9201e10402c8440d0800000a4280d00e05400700002864040012851240e06480400c495080944440d04e194000300d80d04260300c400100340c0f4001d0300c9030400742d18031065a0150107400f014400025205001261b0b4810200c80a4110400002d110025881d1070b000e = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 103519766 1250 103518516 103518521
    0x9010f060807080c1008010b0a05070f060902101b061a1302180a380d0519021e03040303110c060703201c06080a150e071a0a0c0501 58
    0x40002903107400000d41082110f00411141840f0501030310100d110135503240c405001000140b03e0152403d40c0010b03001d2119200e0001c555526900c415600122006070800c80003c1c420288201c1c01524540b03050041075018141002d04240c1c0e405040411154503559800038195002035681c4040407855880c0b40740d0390700c0d107107140d544d5030071900141c80d041049071880d2071400880606006050b80002404506e0291170411074038007003918090b00701c82076050401a0b0300c2591400650300f0101243e160030345486a084207004900c280358480f400c0b0210750618041f0700c070b92040001614103840106401c450340c00083c5901c41d0003410700080101c0c3e808802100e13070384007106400443d0080810014150740521070900910045a0440c01590b286d10124070305102c1d54415074085550325a00002c000c0154010002074200c00003610b80704012441d20b1900110001c01d4400850308041d06000f0041c000641d9404640300030222034040314a81000c0c0031143e2200175050f042040110006001c5803090 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 103521016 1250 103519766 103519769
    0x1020421171605060c16080c070504050a0b03011a0f1e03060a06060f090302030601180906020a020a02030f010506100e010c12050915030f01030b090304030506040b1603140f09010f06 80
    0x244680da0756140d42d803900508003000100300848000f814040006146000242c95118507840f1070381c40c2d628860b00300307031616144030307540001e503c6818481006600c01c0250056216048164001c1c4102c01c1e6101040800d001e80c2200305811080c6040941e145142c0003d400c00104074850806100c2c94041001c6400d01c001191404d484031345075a020055583c1c0400124008a15454104407490950f400245c5640040c4140a040708240c02ca000071240f13150b10411015500c10001c65a88141d410083d40312100d2480c103170310074055001c05c0104881e040c024680301d4103008002110b0342c1d40d402c105407072242d0848601d130f042081104071000010320000e55a8003642c3c43d41c6800782c0f200038507002c02c05203641c440102c0c000301200f40103001400302c2d44010107064030b44c4849014210740d070744861a031a600482e440940580314140600c0113101c1410145401050046c1c007420495100040c194151103902d801511300511000004445110120f80503403c4a1400c0010602d291000000c50540b0042d = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 103522266 1250 103521016 103521037
    0x270804090921050307120e0c06041403010b0603040b041211031206150f04170115060305041e05030306010f030209210d0306080d0c020402090d0f0209090102042117 72
    0x90b00408a08001c90110300c0c20710410b070b20b403491651a05a40c010302980c511043c520003991180100c4a403d0014090715030082c9002e03010f0f54450340e40e2130051030095002e11070305001c0d51030140e19503054203015040300d03c03940d08403030014025211503451405810002411008112100e160080344010030b1004102c10300b081e65409207141040400c02c0803100b0410500c0221000401c0b00c580d8005800d0140c80803251094520200c4440c2ca0000d540075006011203700800712140303001c1946509544010b02450103403c4140100741c402042035601000c0d1384000c2d007254001d200180907907104011000d40d00c800d61030054148501500820303a885040c02a2048403650301c80c2c2c2000405040040c5c0c4031954841c6420311050785130110854403030190010000070000a40808429521160120742406c070340039220380c0300001c5a0400c0d050001d40390404a10852101021a407401c030705009880668405c04914070025002d4001c3c03070b07200b00c4410b030700325010701d07012100c42d09100c0380d0070241c00300240 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 103523516 1250 103522266 103522283
    0x40317190e0c0a0909050304090905070f05040b06040504020901031b020f06250f0302040b030a020403051b0f0609120604240e0601050d14060403050c010f2708040909 73
    0x14042808260740d0090800c4101e98016103100300150366007040c040444a10700300014400ca4903040c00c5055202c0c0d81c11558080782050312040c2040400101c3c00200c0f500d00e40d00c0b4421075103480411081e17918076031205a000c50144400c0c0701600e410781c0185540e40c4141800220800316200c0d601e03d01c1000c50314000542c208901e6000d0000c4113120155000640b845414030629403220400c000111001010381041807000d000c01e800c60007a41114064100000b645407070f031070844d4645000e0340c000d00040300d4a0150500f10f00800d451440c1c40389030424001c056151111b02801444140d4129004003540070700841c02501d8110800c0c0b1401780154044c1c1600100b40b00742142040f0351400d290001c805403890f0131100c01c0854404240c132415500c00300ca0118600c856070804000000040315081c4441c0202000d200415801c4130051200d40d400d000203002e580d0011031301d0401c031201d00700e0041d2400c80d44405121145491f141050489214002d15401c080c1c40e052204120399401380c08895010 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 103524766 1250 103523516 103523551
    0x601111c0e01050405031b01050705190c170601170a060f0203100b041802070c0819060c09060801120204090b0f0a060b070201051801140f180306090d0503040317 71
    0x1503000500e04444642030805502d09458400800c1d91254103001d000e042a00c01185900c80d60b12809c1141e040e15001001c4409564001e207507000c810300801300c00c40354241006030016800c0311490728240e04d00030309400360910f0381c60030080300342030301c0303840040d40e801d004d41e2440070009071181c071841c04100281da01c01a241d2070541d1900f404003499070000402c2c0c2074140000c008540303203d261031f080c90052160161b111101d03403504442c4606140c1201e080350052a015403090b00d807681d03405050b240600c0c000d000224400714142c42c00d42c124040ca0000441e0180144003803007070075100d04541c0348007070000103d0f0202d0707071154201c2e80c4046c5d40c02000e221404003400700241c2c00380500c0010b00110005240b40040d16400689039100f0007950001c80f0950f03003d07805690380501c1c3c9401c0782c0b07901141d109030344226181040241d03a100101200411400d00c0c0484814140051070500c20113a0500501210f41d145030b081e15180c00c0180220204000480300129008031082d1840c00380c0d40c04105d519521 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 103526016 1250 103524766 103524823
    0x60c05031218030f09191818020a08010218040b010e060f0c03040b222d050a0b0d140603030307140904020d02040801140708130204090f0c05100206040f0b060111 71
    0x8208511580c07048078064421f01142180310201904c00e038021800141c204038490790040b0f601c9500502a5002603070400000d40c103003064000b00169900c94110f184124569070400046032142d0301c0c8540003446000076181c40303041c4000184004140300031000e081c1100c00034102d280d40c1c03168201400c0b040c1d0100c1c208118800e01005602102507844003403580a0500b40521b07941481c8405a04201100b0701c0480103d5126903842c401826003e004a04000c1c2c40307501c00741d84c81d0320035440000540e25115030a000001000f0905001c5d48000b00910304d0760f12011404c0311f90a24809082010400810503056a42d03194801800c05d00b907a07007405a122403611000c1801c64200c4541032406121143c1006481540b0012483d8031066044603e1158400d90001c9402404103080090480a50554041c1405440d0901c1c0302100d01c200d4800c440d5000c4003000700e8541c60281c174010b0010a0710352400f4002516840b040c2d40c050300614001d030b101201100014609144103c1011140080f4039000100 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 103527266 1250 103526016 103526029
    0x9060206090106080318011107060f110a023a0f02010f0512011701060801091a07020a03050a0f0c15050901060906060504032a030b01050901060c05031218030f09 71
    0x10701440c003c10950f882c003440151248500b01d25562244203c5000070810382c0500d25840c412003001c0202c8180c10349800c00940301b02c1e01c03100302d030011036510181c1a00d54100041d40d0000306601420321692a1081c40070207502d9083e0394010b001081e00d80c1160a42d031805045100401c7c1d0107100c04041d40d0885000245c000e00c0000664001c1280c00c102050420180d617002c0d90445030640f102c100c0203440c1d402103d004240301e80041e9100e500b0681c07003006000e26120010700501407500740541d181c80b01202130741c2c0c8829074100100450014030034054080d01680407000c1e604c41c5e9050105060304c00c3d40c0e4541840008a0b02c14180e1a41e036800d00400e441c02344582000b411902904200745801c01c030002c0d116004600c4002c0900703c01300046245002e18100b08003060902c090b80c02d6071642c0381d00d080b12005d202400342500404140000281c0365114612000311705412201a500d003d48240c1c403003103c034000500807800e12070000200300540c14204002c2c4070b05107140e40081d46031142001001030 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 103528516 1250 103527266 103527271
    0x705100b0603060306060904020102030c031303150b01020703081e0d0e060711070509040804090207030f02060604020f070b06040b032d06040201090b031902070f060b0901150f0c02040c09060206 85
    0xd078001d02c1000f290340c40000d480d54120314200d6803141c03659600c0c40100c0c0f95109000c0d202c01d2030b00000c54404084c0c000300d5080001d4a21815024950800c0101140300315038513040041e0050740000d0f81000818015170080c00d40d8102e46070740c0c3e80503e16110302000182d11821110445941e1014019481603003448000e40081503480c01e4040d0103d260030a99864060f070007500d00c40c0140d200401c2c20816050300b214010b01e1064020b41d1200c0c1a820041c003681086411a00913000f40701c00980705103418421519640008802a81020380c540c403800606040281069002a55064440c21030f13a8104443c6115000d1840300d09804403140c0800d00b0f05041001c84c084160b4030400910005030b0300400400240d5500c049039070740701d42e1128440c078010f016400410500d207200185410511440d4440316050500641d014480c0100b04414004103c01c24801c4040c1d0f41307441c803c0203c20502c90300080c0c40304441440c03c501900d1b244e4001400312903541c841480800c8401b4010002682c0601c001c5a = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 103529766 1250 103528516 103528519
    0x5120f0f0a0e1218090f04030210020c03040306111e090a08010525090e070804030e030d0e13060515040e0106110319051c140c0406020c1905060705100b 67
    0x1d00c00340c0040166603d03c1003407009010440410303c0e00211018505542c48907000800718011403c1c146a0308100c45415502940180190f01d00d0b400303664401e000b00c81d10380000d04011803400e840d6480e1307440202400700c401d100c080420041c16201e00100a5600024860049025601d0281404001e5170101c80e40c003146c240d0b410001041140c030880254031482030342d5041a00f155552741c074001c6035080c2084d0089609113001404ac4070025a01c5104030b8443c40c880d4481c5040c50501208166540120088040002c0d12018400189040c03c40008850030b10921000c105039450b8000154032000944031141240004641000110308445450740101001d040c4078030744410301c001241c0c41c0d104040b1284c5d500203c04100040700c030703c688100c680f8642d1303081c20300c0031f00c86d5140d84c0389024240180ca03403926402c0040c0462400180310040350304070741c01500184441e034484e009101d550700076003400b000805a00a00096942c0340c40c070040403603510a4000d000c7c14883e800414080b52010b01086 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 103531016 1250 103529766 103529771
    0x108070503011103040b100308070302010510090911010c1509050a1b06051803070302040f0902030705150d0e1603030503011e0513050402030115060c1707030215040305120f0f0a 78
    0x4043c0c038007030241100e80040c4c01c140c060803a0b6440140d00a84042c1686c802400c0043c002008414558194400d83c042c4a88540d0b402c403031582d034920030301a99010100a8100b0941e80c0302940d040d8009d104043c40203108a8481c0741d81e844607900c1600f259462242540c0c81c0d044154420200940319005840200344035241004180c03c00704001c0c028050102040310f100340700500b4101956080048174001d55000303000b8010703402810a4400070b040c00401c120b00170300c103425000c075007403400a0559401200390291242080c0311440741c2070242c010462100b056000300d10101d0300103000c0c000701c1000f80d4044d4481560b29454054031004038880890400e0042090010034085959140d45079021078043c400086020386440c0000303401040900c07460004088219800942d003600f0030345880e100c6008200107a80d500452048041d40d01c1440300007401600700b50b0402c0c1005860303410040d0080c1c0a850b05600f068144c04855641744025900d042413260ba2004011410b00e05c001c02a9120049000c203 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 103532266 1250 103531016 103531031
    0x10507121112040f0f05030a030212070309050619091202030a0206010602060c0409020f220501030b010215010e100f030305030a06090b1e06090306131e0b13060e01020c06010807050301 81
    0x30403402d001802c000c0000080703910380307002e00c50400700602c149a00481a650b175a80110740c00b60080d030108030200f01d080c6d80e0400140d1202e000c6c6c4114110f940d0820040c200c1540c40724101070004200203541c0a00c036503205240404560250102000d001c0d0355001541d075a180040c010b441d00c541684000115400f40b0b0130880d0b40e03441e542c01e8804441210038096181e40100400c0c07445030044190090560308101003808490100c121000308840080c0c900700010f84100c00120703140e40d55107608000d400c007050010041c001c00483c005600610559280c00314988600305c1708206607443d442500090400320031300082c10120b01c42e80c001090090810041d41c1c601d0004100036080100607040c01c1c0c04030701507840c2191142d00807200038900040648580345410010310b045210034a0b400e4500c0c480c0500482d500405411940c000e0603040b043c0111284d42c0c40c250020000c81c072a0049592985600303407240402001d00140401d090158050a160360401403030340c0c40d290070340c2d00a510036810000c4 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 103533516 1250 103532266 103532287
    0xc2a0405250807090b0c011d0c1809071502030702010e0a060c1502040b0c0303010801060605030118020f0d09230601180203060a080703050d03150f0501030b040902030105071211 78
    0x29891582a07460800700d4540d610000140e031645001e03440340545801c00102c800c0c0b619810362040f081580f0300d11404555030b80d42410607a880300b0108800740c0112404588400d0f08000d510050750003004641142d402c40e441d81141034260350124082400740c0c3c80881c00d8011503800143e02c000c406010303240030300307204e107032078001446013005000141c017000e0983c4110072010001d0b0100c0e4082c1c22070600e482d90310102000302c0c6659038030910942c0265440c00002280f924403039001c4a04903510419a45c40380e000d20600f44000350b010541186201c82d0410185498241c9070044240c21030150118940c4112100c03c20040c502d246000c0d186603810103001030010480c501d020b569600c201500040c1c9a1b503a40011808684458012080a115940f000010050002204800a1003a6a090100c1800c00c3d00442105d07034a4095100c0da0012400c045c00f042d4441d80c40301044000c02000410900700c03e8003c2804c48209840700000078008408020019006000340d40c1392200c060341c954a01b8441d400c = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 103534766 1250 103533516 103533571
    0x30307080c0c0a080313051006060e060307031808030402030d080f0112021c050105090f010b0a05012d0f031503050a02090601020a05070b0a0f030902010804080c2a0405 74
    0x20803001a0380320126641c10000003c000003ea50340e40020410380c1c0c0c1c104550a0201040710040c02c81e4288524044d03801a21460b01464045a4a6440b5001c3c03c038014410000b407500300034141c2c0c04150b525005000d0300300c400c2d44a40d1703055010344e1440d566401c05006141c103124282c070290041c04a00c03400d000c2c541c5160a4620704640701d00310040c0001c4618400110070740c01d0401c0301c90680c2c40b610281010700c041980224060b4946104449000307641c0402a4240d90001c10f01c60342c070004071074040265500940c1041c842c0c8802c0c05c18003120345035010401c94612101c440007030010b05812a041d202ca5014401c61003036015202c0919049403860343d90f01e03590340c00920000e004d14030710f10119000c2d034020800b001700309510400ba100c17201d49404007681036801c034002c0100015142d06007500d005029125070111190181e44504841d525600d07041100d50255040308054828a01c6019aa201d4800e000f0203810070100c0d21000c05201400304016a0009009044103000d20292843c100041c81c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 103536016 1250 103534766 103534771
    0xe040209091602100e030c010c020a0c03170405190f120c03061113060e01080604020a0219080f07030c02150307020304060c050c0904110103051f060c02040605030304030305031803030708 82
    0x103078a95410710880d01c80490a040603074600b10314131400c1c01842d4902c0721001c809450036000e90f80080040c13a9207401e0403030b034a1150f07903409403000240c10360500c08030303101c1581c10b840a640e4100407458565036a0101c1c1012660f0240c5900d408080e150030f029013180740340c018004026468101d9406100ca40343e01241020a100042845503120b100402000e0a0000da031042c3c41d0003d50050210355440d4081d000104000d0201d000501e000b0002c4c02070301c3d15100f0740b0b4098605138000c0c40020b0380301c80c100b00c140c40114002c0d00d1502d4180000000d62160030300401e409403007507443c0b106651003032043c06000142c825041d5480941801000b0740c159000003a03404582851074164001303503103800d00c541407501403807981d0f0304408600100130900081c060341c3c800f11503081ea400c001d541e80f070111200c806014030f482c0008031500c0703400810032244644400200140006c000241959540c8002491944564000c602041c0084200031801144a01552907454100040d610b5450280130090509000 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 103537266 1250 103536016 103536031
    0x327010f0c050703020a1e05010c03050414030f0d0905030708030405030a1b030b0a0c080a050f0115090b0309060417040810020c1603051e07050d030f1209080a0e04020909 75
    0x344501e01d0601c01c040001c0320003150003402003c2c880d9100d040c00c010700c508031901c1c1400c042240f400002c47d94410410000383c6e681554410f800c040c00c0200440052986100700c2d5410300ca0210908282c00e0207001d0591070f8001910784076201032428041c18140380c2142c0c0306080706d400c00c0c002000507803004180c0b140140e40c400c55170f00f203501e0850000c00100c8440c0d00f001d0f000083e100208010303603089500c18042689a611290460381d0f50410800c203071282260340704104c0301c01c900104a0485c40c2c10f19008008424201211015240c00329900260001c070755941e084e038419428031007031041081c44003051003002c0c031a0740d2400303060403181541c03014000d0301584616030024281440b0007042c032802d804842d00740d520618240d6a4180b01341d540f200d4401c8554800035600d1400300c62140090f020084a078041c01e042d17402c00302518141d56000688201c0400d109100820000c0e1406520840a66510903582280c49411203000141100c103d04515800789104020f88a011355940d83c016a001d01c4 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 103538516 1250 103537266 103537277
    0x1090e070305032b0c0507110d021005030603010f0212100f0f0b130302040c0309140703050624030d02030d11041404151505030901050c0922110301080327010f 70
    0x502d00240207141310086103110a01d161000320622241d11000804d0781e45e000311540c1488198500811405028260f002940f04c084200075410f001d006001031607216100600010701a0080000c1c50141e034041c880034050891410108100490520814005801d028440e000796a0404100b0f004154007401030548030103000c1400800c80209820200196a0251050000074450300b0080c000c0d0940c0b80c42107442c46603085151009200000e1a8400c80b50024018265505c44d14140c0026400d0780c1504003c1c00c1c00920468150b86041001100e4401c0703a0f4011035860144290800840e81c0020248014150412041101001400ca400c502d0321044a0000f8400d102c280c0c041880d007003540c03200510f201603030800b256003a0070101641c840c0705103030000d102039900e903000d02149211b81d034510f56000485e42c812040c0850034a400c542140290a00001c4401101e00320060b85d400c00d0b0300198084d440040c05640b200e5040c001908141c021440100d1031040c0800007034151582d00f05031000300207 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 103539766 1250 103538516 103538557
    0x60a0501080d05030a050c280f1b0312020408030f04080c0307051807020a200a09050f0117010b090412020d080f070f030213120b0114060304110102030c01110301090e07030503 77
    0x4c03000f1003122408010341c1d01000b203c101e0050038142c823407885004140072811004081d00d465000d98a0709200300802c0d56401c60070030803694261585800300380c82c4003500c0d5080c000440ca000381000107011a9156040c002e0303c03139152217012480d003126110514040d130400401002075031120300342000503180b0003a0207116a40c901e10201d140200e45407010349003041015156040d04401ca01401c1c501c0000c9da480c0c0300603178407140c400c0180c42003035031202260000e00c4010400c40051000c00100071000c0000440d0450f82d10000414401e016502078600e9481c000c0e61080d09ca40400c160100c800490600c0225441d0807a84200900c8000f4a14814001c401030042e44a0b0301c02d50490f0658132000c00d0401e8140d4840d003248000300d041e42401c59400384200000305100440e45000d006804000300014035607613a40e51001c00042d400011641548814040003c1500b000c4c0102c06506000c40700c26900d96240002c502c0590b603165800032504d0308510024004180048111248166108a100c0000 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 103541016 1250 103539766 103539781
    0x90106181511072d14010305090a0602030108060109051501022e0509060a0c08103303050402040c17060d030c05060907090b09060303091002120c060a0501080d05030a05 74
    0x410004848040c0500300c800301d904000c01d03683c0e5110076034000c90008a4400307035804240e21901c4d4011450540600003840c94150302c01c1d005158092207035001d4a4a4480c941d5844081c1d03007083e042104150031400043c8107890043c41a81c0e070001c42024900304051500c00041d480740080249141c1c144600d40c11b10340346101d1481100703d0000045410080ca1030100c09460700c40205843c91a00d40c1c0c1451a407103030319441012154092481009512501403403c044601004806c1e00702024210700b022080305240c2226482c000e0030f44143d01c0c0031459103131910402044904540c200000e100b040c140b40514036203401c191035440882520001150740a60605542074100c23041c004000d0302c20b060820803d00804101c0d05c04661590100340070400429003000f40c0d5450866180350103070b1091186290500c0c00c2d4141008803100e0f0300549224400884881e4555444034007810340d598440c2c003c0c0241d8a00502c185070040c40c429011b801044000400240300e80700140442070481e44420114021 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 103542266 1250 103541016 103541027
    0x10e090604020903030f1207030e070608190c030906140108150c070501110d0509070b0d051b1303020f03011a060a050c010c0c0b0702070302030d050c1009030504050901061815 77
    0xc4440201102d8450b807446204121b00d07402650421030220000b00400d180502078000e201604000f800542900350411008858002c001022001c207002080244d18002440e40702c1c40074003440c00e0341d010071542a40e0826206445000f04041f150000801c0100005840070643c2c07542c90501c4103c1d0140e5449400c0240b01600070214040c1c407030f510b80a011507200e40c10310300801c030b000100341c02480a6507034040b015844a007507220710764000c5c904000e107002440306603108503403250328400820380c0c00f009400302c0029a041110024081a4119010700551805c28280420104110000d01820340303444801c3ca520380b010291140508004500d410a00e801841907a20240d200e5000f00017080714400c00a00a03803555000781c9002446d2008298000d1003c030390074058075000760042400341c48104040b90a50b0203540607c00c1402000415403078000b5030702a2420160180c8c3c3c4550700c440c00c10041140000c41a4420130034000031110b20308580b9581c80c41c0c401252441807030700f01c0321682020181c80d03 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 103543516 1250 103542266 103542277
    0x60f010b0a11010606050307110102090303070807030c06090b06040e0705060f0c03210406112704060e040b070f1b080306042a0807210911120d0e0f010e09060402 71
    0x483d50802002084050f1301002951003403aa035a43e4010000396107808070300300d1050421007601a0000c011810204140314000c012241c0300b0b141800880e07145850300301c11605030200441c1c00d803020740140222464103000700c011031b0350120003a180c06482c01c40012500d121f01c041038406020040340d2900c0083c2d061044c0c400603195400015002411500307142c4030518100c804481042c600b4a155044007202400c3e21780700c4080711070a5032000c09207110303200b10000c41c44265600a13152003002c01c2402c80c144c211070081d0701c1782650141d079080c040c6003d0540040702d007002c4100005601c2c4810880304001036041b80030303002070744030b0340ea40c0350398000c18003422032180c3d0300029440c01c541c8403004a828445007105d141040e070752010310b0307166010700301d0707110306020000300900810b141d01c2041d1440d158815003900340b00e403000e1446103150402080740000c4d60452441d9903000284258000390b0010007074106e25100300c90740802c000b0318100103040685c042e02e0842c0114910000544c084c1c0711380d4121403 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 103544766 1250 103543516 103543547
    0x3050606042d06210303110a120e0115090e06070e06070803090304150c110604060507022112030906010e0c0f030718080307051603080306061804060303110c0102060f010b0a 76
    0x805402003003d04211002102005c80000e4034018458140322285015210a0303401c41c1d4840c1440b203c0c681160000e00a0344e2011001551b176850315620741c075101c0c1c4881d801404411004212402c0c889106410a00000d103114180700440e003541580da0755200482c0d0900e90301c03800c4107450b0b8071010059851030003943c00401203000d03c0340c03401d0089070301300000e8800c807882182120143c140071030500c1400e0065104540114005000080061a01041008550044488482e04401645d2007603250980c07420301d0241c911800010b100c00c82800744021405403600d41074912890070208001c1d8580d00c250100180701c81404030114402a1107401000c0c00c11010f44200d01441c1d446140e880d03103e07480404111003070f2240c0d01308403001c401c040300b14408407604103e42a05580d110000d01070b4550245052410302070749404114072513a10b612580024500035924504200742d001c080c07500d0304a0200345141954082c0c020002e04500b110355060540700c45011a9442d1020164191010b1550762040ca = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 103546016 1250 103544766 103544789
    0x20a06090806160e1e060301030b040b09030901020309060309011508010e010b010216030605060118080a0209280b0a17030c120f030c0304080c0604030903050606042d06 74
    0x4105601010400c15515201c0039034110340c80b1021981d42800003d203036400481e02c0a00d0310340413460000e000016480c500704d079030b5482609041c000741c0554400d8000721120b065500030310080c881c80070354050744207505600951400c2100310000c1c1d85ca0048030b20052080d1400130006803a0344c020b4208100c013144030394122800d1521501080c2c0030f481c0d40690703d0940c0d03181c002620580d606c0010480b518603222081403100609680701c2101130000104454180510b540f070803407550313100581600007400203501030041181c8174070400c00103410107800d11081b040e44040340d800782c054001480c44070088060002840c06c4c060800708030005000da00c0621179000004070100421000310040080100006c203541200c2904100b4044601420303004c007000c424103000159a00624400554015009003c094203210308124107500d0040c04450440024820403405c00802200304442500003d00715014083c42c000500c03d1411061280c0c0a01d00403002c25200074400340060340100301800e5441c1c04c4 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 103547266 1250 103546016 103546019
    0xd0206030403030e1b0f040f0e120901080601081905060a0503010e0102071e080301090216020a081506040e1b060c1e0f070f09020309161d06040b01050304080706020403020a 76
    0x30f4010040b10340f9000850091901062400f102c1c0c02e81c01851840c0240f0305408080c4103801d1000406400a088100c035031785408070b28100740c3c00c2180103440142e0480c403c1d915440a800148003500240005051000c100d040c4203201c400b0400202c0c2241c2e06480000e0242c3d180400036815034003a0b440190554030f13151110004100c190000c2200c4c5009800103003403c0c1c01000020050342c1c4c0300e60301038000c881c2440180550382c00303070300204009008020f07022000d404c1a000102d0212095122805d80e502017600d1940211240c5080f80c0d0009040790204124a0390f02501c54032044a0103000c6040c01c50403040d04034543e1060b0685015040e1501240c0b400c13190100c0d288144030310046441c0d064451042c03ea0500380d0b000a000e8141e540b40c8110404403490100c5400103508043c294400b94041d4211140c900000c95110b58014041e0844007080342d0540401d120f9450006041130740200c6c2845c00e81c6000f40d81000403a6005540b0142d00c60b9a9419810910000d0185802c000e41c0b001d10f5980 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 103548516 1250 103547266 103547273
    0x1605041e18061401030807020105030a06030221010e12040501050d090609060b0a090b060d090203030706110d0f090203070308071e030e28030b060a0905011212090308070605060d02060304 82
    0x1808642a80300e0b0300c04204042c0e4031000e0000303180007484003c12200e0308000c128010f500c02d60146800881580000c00c049880e84e0000c0c1005000402820040440d00035480d0501024007039218404403c00c090504400d11300c501003a1846030b0300802e07040c800c00040c2c0c2d11419989a001e0014250002010040754000340380190103080d45039481440746070496000300f83c3c04250f10a2078180c810007045507181200350035030708024242103401a40c0c103000c1440038002103201c90041c20000d51000c5107180d522012000004111a010b00314003903228035190300600140c90004070041602c0c1c118109a45410103480c201d06950403802e40c402c110301d4002c11003010150030102034540040c00322480c86008440c10004224901107031010003e98064034410008900381c0141550483c101421b0f0410040d21081d1020a4800a070f008a04803c011007240c0280201c00007001c054502d5403602494191641d04c0d03040d0766005211000c0d0501d40e851000c00c5155480390801c0c69843d6010300482e032203142c00c0c01c = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 103549766 1250 103548516 103548551
    0xc170d030507051606090c1e1e080303040f020a12020312130302100305060108060f0d02010e0102011107030206041106040320031f09060f06060f080c1308070312021605041e 76
    0xf04403001500500701003903280c42503d00b0b101d0380c801d8223007030f1520600d0038210362083c0c0000c00721001840040030300031501c0a030030f0000b540710f0b034024003200c0c2c103201a5105006140041e5440003182d07013140b0f040100180c2e03022038540c1c400110080d4480e1200140081ca0107405d6140d0300080d4012200389246918a8058010a1244000f62541c2d605c6550304818425800d0b800c80c0308503440b4540b400410b00540c0500001450740c003061000280410750781c0b94141c1c0710303444a5000e40140e4004004c0008000160080d50740c0f05d40199400750a051450350b614908410300c550f80b20072103501d40f0303207440d041d01c0411070003003141030360003088012405e0b540508008000042041d590b003424400c1c1c0d191204514000c5000710750703284d510880004c00740c0200710343c200c10180510401800c10052244440b0001c0709000c0a45800c5003e88410740c5185000b030007410380b087d064000d54001c21400303859141071529038012601c0a030380c04544000590440e00d284298800c07091007a5180c00c409840350075041 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 103551016 1250 103549766 103549781
    0xc0302070501081003060f110c010b12010b0105160f020a0f0501030e0c03030d0b041401090b1c0b0402120307060507050301080d02010509030301050f0d050303070201090c170d030507051606 83
    0x2a025140c8540e26040112a48541160b45950040441e1020070024070554801d0200d500d000e9070000d4250801d0203050f01d59442951824030503034460301d4100c5a81380840d5603c403244003030402008140c02980c0040d0070360140040780320041d440050301c0b6040c0b03d41d058036000504e5004181a1855403110309084050100d4010240024a0103880503070309840065014038030800180190705103405034901c2d07006072020300c0751150030684503081c412400e01d01e00081030292010b5040400c030341035500c00707104841e801440c2600000c6210316030340c00400c8040640e0b58000782c05035038400310141206582d0f451803086120080001e4540340810022039032120240d4180c600a2098a11401454201728207a0b142030354249055001000104142d280c41c1c1d618181121000d410801c2c00d0f44a521803c0c15900300700c074548003507516512100200443d5041ca034025200c18010011a1039070665080c2c0d0360074071041d0400505540748040744003240900c0c181c1c2c580300c21031150801078000c0c500d80310011b03185d031 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 103552266 1250 103551016 103551023
    0x20a0f0803070e09190216020d140c180a050a09080304051506010201020a02030d020c070f15080f160309020406050a030807150204051302090118030615170a02010509030f07060c 78
    0x145030301114501342e034820f80103210741c20107007455100c0500740344000e501c50981d40010318529100ca43c01600d07a10762004005005001c584120300b210120141805006c000c424461076101c04c246c000d100e01100500d4201402c4080041e00e69140346240008003460040030f0300f500808000c102c200007001070b03168040d000c0407034400302c1c507120304005a0070703030150a100c64003681050146a08100655000c0d0405038020070071182d005649081d0f03800300034082d401c49688403009080700c0358483d1b00708404070381108070384000f44121310b04010101680d41400401e0010940c4441100d400d544d2560800e501405008080c0b928a9a9a18010310f03540e1003200d084034602d001500344c24044840303101b0380b41250006000141e0001e03040e00c10100a51110f00c42074180710b540c80055500445a0003144051407060300000780b0700307000600c08122504c45600440a400c031654504602c00350128200c403403642c1c2030034a2901d401c1000300180c244590a003805c0510711680e08005003095003c004444014003 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 103553516 1250 103552266 103552277
    0x9010207060c030213030201140906190809151f0312170a020307020706050c0124170129060f0703020606100215040f060b040504031101060f0e16020a0f080307 70
    0x180d0800e80603801405c07010b041001170702c031040026501a0420790310611a1064075498030b000d0400044558001c1c8004040303843da107450004031350380c00121454110ba40c45004000c90214030601c4020008001e080c036034028107003001c00326001c5003110384030041d661001624950b040107010043c20f030b000000a480151040c5404196071614030f04c03c480c0511382560162541c0c0c1d050820990300c0381c0c010210041299a16800001350300c3c0344000b540031009240442c110f55134074007110b02e00000849040c0588a07450141000c800010403ca000c154400b0050b001800c20440400a540b0303008107040389101c80740c006580801c0580c0072401601c00d00c001c031580d000040d000402284d40c3c00802c04c508200d0045075001c580859925051041000c0c4103120203e84d440740c900201e025610f0070303641100407601a07007000511500a00440f00a8411011004401c80c0b5091046a0f020030180c00f01c081c070482e810400081c0c034400d0101c048502c1d04080032440f10388041c945590154400c84032640040c8 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 103554766 1250 103553516 103553531
    0x2203030302030613110304021c0b0103051501091e0c030b0a1203090b0708041e0914090d03020a05090402091503040f0b0109020c0a0228080102040e070305010501020307030c03050f030901020706 85
    0x1400380c030900d40d0461746070540170704582c3e031a401d10081c40d008100d04a500c0e2000c0d21600d0000300c0d240384407800303140b1030300186c81c8030f110700c00d00344a40d40c1060f00214425410854810040350386d4884c041d82007644da02011520700c0320b148040d002450b007540000d0700909021400f0506c003100390b4420086601c260f40d44002030380d844a10a40754014010014405001048200807280c0ca620607680d40b200080c10600e810742c0d40d01078400c103ca42c00240040d65210041c00c00c10343c0e4400780034082c11600c403400c065240040200d030081681c81414480d40c403c650108959245880d214bd28003800742d81c0d158141d0356410300d400c0510070090990001c0712601401400860904158026500301e02004402020900529401c2200c2a464817901003520b10b0000d00503121a01c9901c02c42008020306000166102d0904503254014000248078006050800b070040246d660f0010454200c1d54042c6080380b17294800d480c0480b0141701b034030003a9000383c00100c281320704148194024081548140300411131103 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 103556016 1250 103554766 103554799
    0x14070804081b090a021c0603030c1208090c09190e030c0c04020702010c03110109080307030c0801080f33240405010e130809040c0306031208060303070822030303020306 74
    0x41d00c1c10810f50040c20b001c010800520454005c0e20a6010300c0d8181c0a403208681c1c2e0213812030706203900070340000f292840c5950510449061003004180b240c9803803491450420140390303950300e1003c00035004d5403440c2c00041040c540d0000c0a04c018190610520040c00a41034080c0d9a400002440056000e0180e121078285407502c220382d0300c960b040c0c56400e072291058400791400b0210300150000c65403281e01100004542e14011441600349880c000762500d070880e4000d0845805801000c41648080700c08160400001109100c00351354030549248408043d1050802c4503401c1407030031590f0840300910030ad0907441c1282d18490418000015035089101d170400043d00c2083c1704041840c8004000718490080346000340c082d450051010503c1c0001407008a4100d446283d50071000aa81d040140100700500c00b01424100c05880c1590705820030740c000a884e4030544c900102041c0c000202c2c41801d503000b04038624641e01a4000e480e140b6074a050203006544211000c40c400e004002000021 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 103557266 1250 103556016 103556053
    0x80d02070e0106020d030e0c040509070906081504080307120c0c060509011503140c090f01082e020a0309021309060605060711040b010203120a02040906050105030702060a09031407080408 82
    0x4903040d43d8000d01718541ca0301c00c01d4009000c1c601d00042a40940c8901c480c00340c03220301549008004078001482094a84090001240ca040d000340105070010004141c805450541e15a001500810510340d0f0f91580d01041c3c840c680d004090024060400034500302407600120296107443c081d440900a541e541c00c0030794201c3d080d5803078046003100908010300c0800c500c1401200040800d5080380c180c85440c5002031482641164000c0011003040d005016078001400000e03801c60f6005800303855080b500c0120002c80f428800c0d203d0051794049503644040d4441c7d000620031b680c002c0d184502c108108401b51014040320141681d845080000025032414544211440e03d41c0103203041d0441000442040041d02000b1206811403109000841c008010004224003a07440b0f44001039a036460110300c4029104903920540c14060240200003a43d5004100706500031002c1400007110501c0345002d44e00e50850241124030902d02041c9981007111540003003043e2011041110b40b03103240540043d00 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 103558516 1250 103557266 103557269
    0x4050105061008070e0301060f300201080f040510060e0f01060801080c0603181e100614120f0102031306060b030c1b0a0203100507170103080a051c0204080d02070e01 73
    0x1800f4080000d00c1c107403082e030007104070307240c02030001c01e207a9030f1420303e030901c4116500b0504000052032440042206005038148003c0c40244101105041c150000b03480b00380c004114103044010174000804114082c03104030410345064000b040f20f0380e164030302150382190450740502030020070320011426034005c107503050407141620001d10038811224180b180d960400f811b000f00040320f90307404000c421828400110b14603000d0340062503c040e4056070915014500c540624841d00d8241c0901c00409040f100010198040d150414480c1003a0501071601b5840307081101d07039500c04400d115006000441c1c0307490260080406105c52521400e6624981c0310036200306c1c602d440200000138004c101d40160260f8a46503400340da0311414550007082c180354004160741200e81c1e441301000b03c1c0701e4206080c40d05448504102565545c1036940344603082c07180000b800140039002c03558408a44980c560140c003c02090780c00e5440303603a5080595500d41220b00b0560260240c440081175103107070001c2090 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 103559766 1250 103558516 103558549
    0xc0406030509060907050d02010201201c05060d12020f0d21050f13051e010903110102130b0d020d09060b0102011d1c09030602070b06010912020102030708160209010e0405010506 78
    0x41817514003402c0007010b05140034100d044d0b54a1300002c1d52000ca0045d003504c122401284245c0c5d841c01d161008102842c40c04986015182c03820b800d1040070317242e40291003c02079203d4905640c001d9128020b03841c1090301108403205200b800409600241c5c0085440c0310b82241f951388038010f850f0484044269070084820001c1109c500c40043e1049450488090b2524060b00a42d01026102d01418120365500c0015501a03910340c000c00c410554000541c035214815140214202440410480c010074a540311320200b6003c0402d0708800700c14568101d401021619104100e0b20280c1c0c42c014010348000803185025500e0a001075442029001001143c00d0301c00c00a1702c1100c01c0000b0602000501c8418901004089440440041c0321440100a950b0046a60110030700d803203030005040380c551350401c00101c0007007111800142d0f0000305403400a03500030805500c82c0c07407090801c01b0111603a00c0180d8080b0050000180b4424032101050066028100078030441d5101420311001000d92034888 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 103561016 1250 103559766 103559773
    0x1c0e011817070209010603020c15061f0207090903030605030609030f070b0a0917070c080705060a0e0d0f0f0c060e0d0201030b0f04020d060e01050d030509130e03030c04060305090609 80
    0x164001403a0030749404005000603841420704000d80c020454120382600030101281d800940d51030381040c00c20262404003140c036036544491822001050f0000b06149010121100c6101c01910042c0240b00480c040c05964004210741c82003818000e024041038440c00b07000c1c0c01084041102d40d00d0200031291120310f070440043c038081d09a51401c40c800401003020100c40d6440d2283c1c4001107030401096419030703104094648649450401d00300048490380f041000f07501c4000d00704410780325035040da80011081d08040c0003941407600894180d4030310305401030400c004038141d5030400400790443c01c0c20701c0c020039490310240d4440070f0a90380090702000b91070b409500c4001e050010b610031342201c0c41018000d0181040c41d00c00c0d80220302a80c00019410011075141d10083c000818000d80c2d40e8014201196807080e01003560f140544107104404029001318100c0722180c0c956070756600a008200d240c042100d0303580c9003003401c3c42548e03001400b4280c0003904041c04201e1421000a80394010040b03c00039 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 103562266 1250 103561016 103561061
    0x312140c0a030e0604030c0b16020d0c060e0f15070203090f09041a040b180312040b0c040305030a03060504060501030b09061012110403061812050702040f021c0e01 72
    0x505007a00110480010540c9035942000907010500682c0d003d54800e4440d0031341213009181c00e40f249040103002100a4054044009001e68001559203600d4000e0500060f0f1003c14108a805404100c0c0b00943d14840c1d03044d40c801c0d076800000d100320b0490103080a0112174551400490f100d1041040c41544642a403520b85410b28080c45280d400520445d40010f81e818405403d04a1150032a4142c40c0c10300c070302d810402c3c1140040e0000342440c524a02a51520b0500c0c0c0c0c46158205005d0005002c401c2c9030b40000f03608004d001e0403100a1908a13040f662102e1038060000d000d00614040c49000f14240500001e455000307004000204000800f4804c03a6030310042406041c05c1000304283c100082c6d43d241e90052500c5100e10f0784101c4c161040207036074070309500f05501902d090440c43c4004500c10201000841c01d82d901005035a1080e2404d1540c1e40c0b87c0b800003801510007039003a446072910004880014847d0f0060540c2c1c600c0c4910400d20821059110302400c0311708200008510b004c00c0840e = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 103563516 1250 103562266 103562281
    0x9060903061a0405040f02040e0304061d03120f040f05090402060a0e060d090507050a060822032c10020f030a03020309010207080f130b070314031e090307031214 71
    0xc520402c0e00126100400d0a000019040d03c1056034150b41340f0402e40741020550500f4000c0041100c0c40000940c9400d141941c0140911480c480c0805070010703812421715070b03650034068110f440d00c1003142d058840c051955070395910352040c814201c00410b003030300008280c00e12030810743c8101c5e0010304a44c10000c1407007041d60b14801c5410540c0d4403038020840403103c0c0c0e071a4400c0c140b2076406503000341421030a0000f40800d5110340d800c6041404009400c00c10000720050442d2040403180c4440c2200b0700701031409440c0385811402d24001c24414400e10300d2440406100101e403c50220344a40607504103540580e1521040305910303c0a4104106000078640a900210341014000000514060f030700c1c4c1312400303c5d80118000e82048640001c2ca02c926030303001072038a4090921200050b25120031583c2c00b030500a082c2100402e150b401100185c80c8800c1020078042040307841034240d00c185170400c040c3d52650301c24501100404c504400e08042d80c00d043c07107803010b03103658122406005e40390500f = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 103564766 1250 103563516 103563521
    0x3090f080a02010e03030a0c080603010203091908070c0b03070806120d1103120c030709080c0f0906010c05010e0c030d03180b061207060c0c060e0102060a0510050301060e06090105010906090306 85
    0x300480c00b903649074640200503c0382000210702c5070300c1c07403c0001091490624002c00820b07028100c0d500c40da0042c0b00388610500003140d0000305000100800c80403a680e0310f04200f482c0110701c0c010b07160304200840058040c03c480010f5220b0726859860080542d85c0008000c070362501c100c05448581d100c681034401c41c6014440d0000d1042d2140103d9081100c81c03680c2c81481c0104031aa01032801022050111064114021601404041026105000d0600089042020318843c560700c211003c6001c503c80303074014a00002d896821030000d0251b0404010016a00d05034450078501911a20002c041801e1280c400e080010641305100d4208040359124194081e0b0050207140d4841c0c012209210090001c206503401441a0340328503140ca000c0b410700f00d003112420350218040c4080258920103c0c0c1c1e012070100e5203c2d108420014560b11a4084241e424400f0f421260300740d868a5070110307141441e00f01040c0304040c12503904040fa0380306d500444040e01c1510942c40407946814045c0002056034 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 103566016 1250 103564766 103564777
    0xb060301090b040c030b0106020d0503040308190c03051501030603020607140c060c0f07060c050c010f11032a070308120c09090f0406110c0705060c070b07080d0c03090f08 75
    0x1000880c0701101500c41980d2074005640481c0d00480c0b070b0104208024209000c1401000c048c00946902d40d0741c0c1d07901402c640f000030001801c22003080e00054003035840304841d840403043d072075041100404000c0050020a4152000d180100003500415101e604c43e000302e03130549601801003810f110143d60742031a1000c0c1a440908030b070140700308004403070b243c14001d0100b000e82c0c0001010140d000350a0f0038140080340d00709004220340814440c01107140020310355142075003817034a50714240410030100d070010058821200280400a4041c2c01d040d03030084100c900082629681f50b0301083c9007072480e0307117074070500c40105024000d01640c3c80c3d540401c1c0d43d0503072010b02d050429207000300120014029042c100c2d08010915400001c0c002402410321501c0c1c50700c1a241040c5207000c603035a01903503640f036480c45240d128035400904200179030401d04c0954000d1110201c103a0f19a8035074681804e6a801284081da03401d07141980400d6002d129002e03203400c280e040301881d9448486900d880e403143d44034 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 103567266 1250 103566016 103566019
    0x14160305060a0b12010e010b091f0e04051005010e0d050a0b04060b0402120f0a151404021e09100504060906030b030a020907080712140a0e1609020a14070f0b06 70
    0xb03030000007402ca0600d500818030440c030994141203e60601e812a601c4440607040107050740000d000700c08494454480320396000c00c05070288094404030120841e02d13607a62000d201d80150602c2d061003c030003001034012041d42c2e0240c80310000c84017040306101d440c02c41c001000e4281d40c401044240803078004103a55400034014000030480d90401c5011600340d0b8410503a00e586200c10204110440b215040c106400c0f003500002446004868103000d050000c031809404079900340e0a95010b03003907540742d049903002200c2c480b0000c00017506c03c1c0d0102440e001000300714001c5165840a100d8248213200b258180e6006840d02d1011a003000c0c0110001d0a142403640e4040c03203100309010140e5a40000789202d600c0300d80d905030880c64601001890b0149a106603446642060142030201c10581c0c840c541c44180b84000203080b19000103401c0c83e001041c6102a00700e41c0620010a145185400410700180e194175041945100d1070481d040c20b100301d501c0031b4003070701034110341b04001340840e0350b1242c10110 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 103568516 1250 103567266 103567279
    0xb1906200d0801030b01060c02090402010f05121006170709090f060503100501140a050630100302012604120905030d11010c02010212040803060a1d07031416030506 72
    0x140800989400c5444044001056282d00100100610049040d001d4500f524269a034031500d580400c8203450040c0000781409103084114114510070000d4078140c0c5c0d0303c850062041d0400600c2490314825034080c140c001380505030700c8002c184c80051200d0087e405070380c80b500c40a01d0700c1d0200c802001440564859142c41d05400038180e035007040303c04082504207800060303652400090804a00d65004c0c9240201120203003004503907580400c2d181d90540c001c80c01e015820784419031500e5000c4584221220710307021b0080c0306c20101107403100070980307200703889070034108194009401c50140d01d40c90000d14001c0c141c0c0058000395250310f400c018058a41001e5900d03d417920002030600b002c0c02a094001088494514541c030300900903001080350a000844c40c0c40d407012031a404c1e843d402840504072102c00804140181c03100010240108086140f005118140c04051000d00c8001c0e42c062000074142010780300c0125000ea0914000c4048001720368080784182030543c0580303002010f2550042 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 103569766 1250 103568516 103568567
    0xf020313170d0e030a0e1005041a07080412031803020f0d020316081609110a050705070f0902030901050a060e1f1208070b0903030403050702060904090203011401090b1906 75
    0x120034002c0e01c110500403c0955203400840e08002e0140c5d1001c03160b1803060001000c070508003074120781260117070f481c0c02078000c0c10700b00c480504180300c0c86400c1c0700902086002600081001c440803d1041e081e10960ba8601102000148500c0c0ca048502001e54812a03000700f1049900d041d84a80c08000d2000d0180d400c05110340c604010100c0c500d50060700203420885c1c0c030b1404542b030a00001c000e03000c18142001030b6094410f021010f40a1b5012032024031100107180d50900c181008904000d1204e2504203030055100c1c01040042c0d0800e40d00005a582400b010a4808109016980544040c1c0b032143c40141d9070b003d003401403c400d030103040c000c000003200080794103042c00c0c6400946a000c7ea001603601c003404d10f0140c0d00e41000804801e25500b092040c040040d921400719241507070101d64a90325000d544000400400c11420008d506601c0e000c0c3e00f55042d05417101c094100c99003807904003d03001e00c10b4244007201450701120396002611000034081f050040710040540509074510301e8511 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 103571016 1250 103569766 103569787
    0x1b0f14011e080106020706050f030a0c05040f14150307020c090c09030f03040f0b040602100f0e010f1a04020a050306100306081e0d0306031511090d150f02031317 71
    0x400701101d5200c00038162000511070640c0410024005120301d00d495854100780e60b000841c030b03010203001a1003280d281e0548400652003901900e000d840c1e00040420803c0e940c4d9407800741d508401c881c0e0f078003414080ca06404245900381c103582c4524800d4000d000d0400ca00c108004103007030000c1c40707050720000500034031040d510100703d00b101d1031481d400110360b118103241400000c03c4265000c50f001c502c3c1000184a1680e010640791000c1c0541400403510342c0c4030740502c1b40a026040080e00c42d40d86480002009600650001d0500c512140f09440d44140c0c02001e01081c0d104070900e2502040b400c001260290400703e00d160780b903900ca80750000384075807242101420f0000b0005401c000c50203405089009940034003900c8903611a50908000c014035654036030442004891b070002d103042da0b5100814107007078954120303900e0350b03001000056488410314045100440d22a80740c051686000b8a903c4a022140300322030042c1e03070851440c00301c491950b40305c000c030245559854201920600620400 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 103572266 1250 103571016 103571057
    0x70b0c040906061101110c1c03061502030d0c090b0a1b060e0d080601020610030206070335010509070806210d030209100c0b070e120f010204031b0f1401 67
    0x20b0905682e407a58103004201445007034602030914034034140800c0120782131f16003000803114400e8001c104008002040030310b054000381040c3c1d00449030f000032051040c244941c00701c000c044012200d82c3c00c001e40c816a21089031220540e004501031030034100801c507152406034050100c1d42c111800b0010864181d1386d18001aa018809081041d07444050260841504403142d246d0040084c40244010324043c620b81c0051707000c4d888080d000340400280b10b407d00d0710850f04001707454400b000940e80644101810580c51208034101d18034040d001c000801d1900c0e02030407442c011262a50307040840d896180400000492a54203a280c2d0900400e0318244101c080c088800781c0202c68400507120322100c014014100001d048002c200999031a4000025080b51b000c2500240607262100c000d08a078804100308042361141420644203411454201c94015002082501d00c22008080c00001604e000d40f96500c0c240600700202000d0281406900074007450036940d90414503040c0d81e40c1ca10803541059 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 103573516 1250 103572266 103572269
    0x22a0d14070c050d2d080301030f06090b011502010f0e031e0d09030309020a060201140c0c0c1302040f150905041a04020c0c1002030a1d0d080307080a05150303070b0c040906 76
    0x200e10404101c114403680c80040c403200c5003607080c05c5850443d9002e903112121440140401410482c1000a9609200040e4051184140c1c0206007801d9541c45484038000003d402200c0c0006600f4501c6240402c0720340d008041e440880d0000030750410141003c0b00c8130b410b8000030311042842e42805180d1100400d4061020f00901a407000107811500e8010b118081081c0c3d001a02907a04004000c08001d21001c1259417102c881e0f98060b40741c400304980141455920030b049a0301103441c07400080c00c003000e46e0080049502100301c1c080500d55441c00c60740d1200401c01114042140020204410f0034150041802c445c1800c0550381060620710014007203030040e00ba2204590300034800c1e80a54204102c7c030030210605800290b04085601400500d013040801550800740c03201c1c0340e0301311580c49a000c00034249600158094484c940110000d140c100101ca0a0050038105004100f210b01984039040c80e82034040d0281d03181162075120f0240c0311101501403c40740200300000908520240300d00d00 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 103574766 1250 103573516 103573523
    0xa0306030210110d080603030c071403010b0d03050307050705010f0f02070309050103020915070804091b0206281d10020a1706060403030819022a0d14070c050d 70
    0x104a41103006210781459001003141c01d0240720148100030341030010741d1550f41001450304170300da581c4a1000c6401c601500c110541c10340308000d00810314403207a42c00302000d228103400070030800148004001d0307030229140740038020801c108046420700d4800c0e4018806c80303004400216404407030001940440d00c0850540035007640c0803030780b04201603006603e5001000c2c2441c1c158203003c0003000186100113142c4095103c0403002900c4030401c0700c04030948000305014602008003540030000c3c007140c000001c4120005006081c001550b10f62003092120100080f40b00e0000c00d241c80c0c0c5030480003407070104403090300801c404100809880c1e0800102c7c601c41c070340d8800540c0320041132101408000f28490410800392902003040402d8540601781e40880e81c15280c10117440c0c50b0181d03002d1201c088035041110f0a4000200c040320b2100c1200107440c9080420b1411103a001201c0d62191201d6030300180c840010403014000d18500740d02c2001d001428082e000700c0700191f0342d8100043c02c03419810b1046 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 103576016 1250 103574766 103574771
    0x20904110d14012306040c23040f06021506060a0c020d050d02100e0d0503071205010e060901080604030801061805030102040806070201110c0c0d06061502060105210a02060307140a03 80
    0x190400001c0c020364002040074000000d2482003130b02c41c1c00200707500500c01d034001c0390703160801c000d018410070000c43e030380b001490b505103c000b103072507101c0199205006030600030a0041000903000e20000b41024400080d03205108151101010004a40d1184244c8001c00c2000804040545d54040807070500710304c990014840c0340b522000181c1000f50480340300301485e14149001f54420030201d13000c0303082c8801d072500b183e032543c03000d0707094491402140398580c0051411001280415600d03003501d0003098101e4034842c86a86e03906902c0c0c0c0c0c0d8072003160001c0000715028010010180904800401200f0005905011984a0b4046402c980083d0b01410b9283c0c08a001d0000f5544c0a104a40d4041c1c000d51082d86040c07000b2007401c0e0364a40445e0414002c1d07440000ca84140100341d0b00540c0a440300841086000200f03100095440c00c0078000d240c03154a0000808200302c4401c40134070340c41d50754035000d0b00c451039680c0c08000c083d40004014400388462151882c40b03150240d002030000321003a4030700 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 103577266 1250 103576016 103576043
    0xa0f0f0c1206080a0503030c031f06020102090301200714031b0309090105060717030604092f01031503030e060c01020a1106160e060c0c03010608030a1d0d020904110d 73
    0x2948151642c07580003000390780050342d454001c9480401126400100702011668a03110003104500380d545001c03602c0441c0c030b6a44c00100f00303da4190014185184114003d00c40f452004280001d8407509011001c140d4804104800010b800c90000b90b00d041040402e503030400000b41914407030710b03602003d640392940000a4440140c940524a1405481c3c2915180c0c00e042c115924170f100b52a00c441424881440400001d1803640d881d0070244c04c07a070340904400308510080c105d100351960f240e850407089200204101a280d4468810504000c546440c200710380e40c91510150b4005a80c040d9060304010200301e0314503484401d000a0282038596a41c1c848007901c008083d5003009000f800045000304d4484480844a1b84400600180f83e0b0403100b603541e071801030180c0392920803540c000c00e40550070200005070503880030001d40051034850712410584070303e8003400701c15800c01c0f15038035501c084443c800c4809420120181d0758094807524010440c0d89200d40001c2100d50340c55000c94a4a0442e80c0 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 103578516 1250 103577266 103577297
    0x5071e0801060f030210110a050a0f030305070f1d01031103010e010302030601060201021306110309040f020a020d1e0f1103030405060103061d0c010f020102070812040303060f0b030a0f0f0c 83
    0x240d4801007880303c2c2c1003140707241160700141c0e181d60030790152400c00110000092403420140803020216500c181140d154110318900b140f2541e5882d01c0503004039180030001031006010b00e001609156441c2c0e1040402c04800914403428815500c0e01e504159407140101c0001c008000114003900326408095025855441014a4580140c020700116401404000240e201c103219800c1901d4850400303808040c0019152460741c0a080c03100c641c010b04114210b1411708140d40189078002c1c0079401c0c0c444007148080c00b1349061a51032414895190310700a0700300460322500d08612140d202d0324143c4401c081500314945140c006480956030b0380c1000004104200241c8103002000a010a00e1001c0010f080c80841d103440459401e941881f6202102d0070106200f076046034004e541c424000341d100c400302c1d038140c1180321007260100c2c00f1a00e046d201141c2c441c5d010300d8410440320001c508038915540c402c040320140a103c0c4c14202d409441d035030094083d4901d80a022400034140d5500c148034030b140103 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 103579766 1250 103578516 103578521
    0x1b0304091104060c0f060b1f0207060e01140307050c070e060123031614070302060f0108010e060703020f090909150609090c19030c060f0305070e0a03020d05071e0801 73
    0x10448078401200300400c21603190840f0200a02a0700442101c15118107400e0240251003100f10b1190f0103070501281c3c52009070810501520484103600b114095920b880c0140c130b04030456140280420209904080b031030342c0c054001d680c00a13480c038202c0d040120306842980703840216002403071160b100d042044a19648150004480300311500070b0740604000700c040c40705521014000145e4254101101c070040340c050042e482c100c1156512103980c40000f410b00940b28074007500d548008407a0100000b503284414041d6504500280c009004541c4810405034003c2d41b04c00a003080e880340502690856545e05408140b14000c01400b51840382c0d010501c9444103c0c00a1072503100b86403c0041c484210400124403900083c1a9607030340004070b44110a2400c0051640001c0c0601308140c5c1c003150259000c008002803104946041c0040d490310341094450fa0500ca030b40541214084a04201524005036200c07910f6000ba410f40b00b0090701c0c0c402000b00c1240f4061091071031171034108100400d01091 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 103581016 1250 103579766 103579781
    0x30501050c03010609060c0c05120a02030114090304050118091b0e100e010c0f120207061b110f0409060e010501081b060702060306120d020a200907030c051b030409 72
    0x740120b46103606003000900601c405000e07007000c01800e030054404100e028080359000d8040100302d4828154200150396844240c1c8030704900070750070200c80c442408048140e00e07021300c0350380028500b461304000046841680c0000c2c0c55142c1000e8050004441801744512030340140903061005100354003050203482411445050f600620340b40441084140d840403404924103024030700300d92400c220381480b400b00340103d000039003030101c1c04442580d00c54000401d1003c4035410348440c180301d0301ca00010450300d10407031300280c10000411070381e6074035141400100d02034400040c400120011603071906002c8440a0f0445501695100010b0213009420000451500e054800a014420905c80031a041d4003030310340b00900a001c0480455620707900c0d00461841c10b1080b2003283d0002560200081d501c201e5048166544c240300070341c449003504198103048040d48043c01c211742c0c0b5141d000c4200c1c024148080c1d800f040020134030142d20b10356038085441c11301c556060300458480703092200010448244 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 103582266 1250 103581016 103581031
    0x1b02010b150f1b10051e04030f0302040512030a0e0a030507030308060d060513030801050307260a0203191703060102060601110c0d080301030c09051312180b0c16060e09220b0103050105 81
    0x40000c034113540f100c1081c116a1048d07043c0703489402c1210842040e000f9000e2900043d40c8202d01405804507048004042d0034684d0a650300c01c0e400314680d0080c0410410343d40009401c0e0b8101c2c000500100c1e009110550704104060b241006030002900d40f00d00301c410580b03402460402d082c4081e800d05a20481c4913024003012005840454507101c1c0f4907640c0c0d40001808106c214580b40c0d1541d00107018040c0290755500541958070035130381c200e0b46e0090046818801c851825541c6440481c01c100a02681c2c414001078000340080d44540005561107101407410003030034402d20070120400c0d10780d00b0300c03540401e00c540b400036103d50461501d020301c2950703500000040d0b0329200400c14821080070310620031a8000f80780003c41400420101e41180c9440700b00f000d200700d40d090008070461074600508103120203100b5285480308189540144842d02c0c0b00d40800605600103482e031034500b079004980c0180702c580c402e038241507150032060281c590200040e00c122101074010001d00c82c0030700400d54000c22 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 103583516 1250 103582266 103582291
    0x1b051f05240d0f051603121209030504060518030106090207020f04090b0c070c08030a050414091b0f070204050405030a120e06070507061508011b02010b150f1b1005 72
    0x200e41c030100782404846030300039100c1c0450074000c4051100521401c86001c0010851000f056124140028641a880d503980001100b5001c0311640c03011340c0c480c4007403165040e511030340f400b458a601100e040e001076a145154001418040042d80c1e000d20500005107000c00c005a1540b000c0d0040285400d00b03c10790300e0055052003441c0c0c0c00030358140031803070713001c41603000c0d1949820060401240d0403919030401d83c503521001070401051071b04034000e04120b075800b44446a007002c0030024400900015140d44081030713003020300d4040d41480f2002a150740c00001c00807500b0b001054001030140c03a0161016031f22500005187c0d00031640c013005080da0880546010301101d41c00840e410360702d140050002007044404200d040420005811042840303075070b05422850140c0f290580340c024850010b03118031901c2000030610001c3e0041c09141801c240c020603e89960000d030f06c41101c540d00080a8038101030080040e450070000d40d81011442c88c0312007000700740203017208690742c3c100c40c006880c00503e1003 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 103584766 1250 103583516 103583581
    0x6040302030c27090c1f0e04020903030904140a1b050706020912010c09060f09060e062104030c1506030221070b040308030f01060806011b051f05 64
    0x1c40c00608148103040645200c100c105603100c014040c2070611060150300f509010a00c025035500040008100e0b07400c5400c4140e000181a00340401d68500c0c2c444004115595900380103850a80d02501ea00304004d0192850090014001f4085070341e1100c0c119000380b02401480710303200d980d20070210b4080300b9889800c002c2d01c01d070300c0150a90164020042c074031900020380282d40d4544071014500e400e500b81c0240050090b148000d807050390b02c0d0203803c1c00203509801708411144201c0842c0300701c8030b103900d5000c0c00141032070500150750301202c00e40b034007071550061181c10215082207051003203000f40e42d4003400d5a501c1c42d240c0c000340d4032004152815070900d001403000d030382c81e612005d035007030b440c900c441b07108d08520110a410044540d000041a42c004580003003840700303a50046205e40301c2d440340304580ba0b8840c0005ea410342020349520340020242859401103c05900540c806036001e002140c00c1113000300040704040300300080c41e0401075128014006080714200748080094014000b600280 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 103586016 1250 103584766 103584769
    0x324010507080d0b06030a0c1707090302091806090304090e0726010605030d02010f0b041b0507050715110d080f31030512010b0f1c022109010b06040302 67
    0x1401405000781c00101c000030260f4645103142d20206030302c4000391600703440380750004400009214807c000000b140102d403003070055103c010302943c440c04180e1211041241035030240440014010000a50b01c0704055103852095801c1092602c281c2c00800117580d110f0a02c100841a500c4540007204e039584040c1c800e0149038042c82c4100800310000b4030000c1e000c841075030120f000d050642d1000360180503101001c0c2a007541900410081500303c10240b1000b18260140400c035a20004600100502809040d001c03074802d000404c3c1c5d26000e0030071108050744800950040349500c408440200d024030010015a1000f132000a44401482c10200c505160445020069200007000b4450842100d03400b070700144641811038420000c2048000980c00c201c1c50054107030307031100125104003400030f0300028511445104850b2484118940c01e4240303900c07040c0302250fa490419450058036000d100c4c002c009111451030030502101003603007120a0602ea1161401c540c08829054080d201c20001480035 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 103587266 1250 103586016 103586027
    0x6090608040302150903040515130618080106080c100810050127090b09100b070f02210703031101020c15130c0b0c06072d0e060f032401 60
    0x111402810440312640d9945412414900305070501190741d600c06007030110365440000a0020343d031094900141c8039080c02c1004040e8000da200300e00030786a518009002c4140304084c03011074240d00010340e1000c1501e51071020b0a55031560040b40c10f5502c000052600391400d402c1ca0282c910b0242000780345400c2000c00b510000782e85000b104c4c10b00407051050b0300c0740e0400c0852595000030106004e450551940c082d0300141c4810008544100f4003400411410421440b0120844d0790103001d5625000e0746640e5810300702c8c6c60210580e440b803144840504180c3d0316020714000c212810014200035030443c5009230032500220601d0007181e00c1803000d41d5400724006041e260280d0804000301680d91400d4400d103443c0c14522004090194054000a807402002c0140c0500030400f4150798240da1440e03412100c540104a408908070200503148121800c548030b010b00380410340c90031041100b00c0101056040e8000040540c0352000007041180e00c5000e641d5541d140b520700803409101d4004000000e01 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 103588516 1250 103587266 103587269
    0xc020c040606020a350301080c0603010509180a020604060c021306060917100908070506010b130e2a0901020111070503030c0c030412060e0c010309210c150914070609 73
    0x2200c1714005c0c8070045e40b00301540c04961480a420024030010b24010b50300f903042841071500798400c607010200c241c50603600340e03030507510b0150403e08a0741e104d140d400b10903507150842c4150b6010b06100c010241c1c035010b009002a2201d51030700348454040f44107000701e01d040000340a101d0340c5442420710141e039001880c6011110080107240345000c04800300340c02d00302c403a003440e8200c2d07203055903c804000d801000b9164890052056030340980c4d8901c540d03201c03071044a0031102800c00131b01d0184030700c1e59581d0880c2d402800d220016688400141283c0881c240c90082d0348400c220302061200032980e090040020610306e810249003420701130380e01c059490002428013694404089503a06400204005450050010b03140d80c550254250900c0300040418075103110060042c00c103440e015500a000c0d400c08254407988040551055501700c00c2c180440e039a058041051030500301010442d28107902029030403040b00050980300c01d1074010413101090351031883c070b40c200c1d401c1002426008a203a40 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 103589766 1250 103588516 103588523
    0x81003110f0102240f0c0408030301120809090703020d1a10030507140a0903060b01020a020f0f0a05060409060609050306071725170a0e07090f0209030601090c020c040606020a 77
    0x318581c00300d4010707800c03c950583c1d034124800a0550400a80d403004036028001d03585500d074032241c0c0e1548071100901b482580a88a4654820001000f0710703041d80311000d05450080611a043c40c03003100008035805000c0e41c5c0b6200190700880c1c40b02e11a22144201c0d00340c0c100d54286241440d0000c40886c4400503825850030605980f0400940024080c0c9c280051424030044042d541d03030909000648100b07140c0c00203980003480c140104c4142d500006100340010b40050050001200f24001c1003d001d140c000c8040c2c12440700f240014003034450748050805000c03154000314000c1d01382180203000d0302c42c680c40a4401c2d400502400305841e04220320030351000c0c0c50300e03002c1700c2c03650380c03031303005010110528040c8807152000b88a0030a0507601ca42c491341821414558048940c440c480c0301010307683d81904121458200d1403040210443c130703502c5151314a0000c0c00140c1820003e2001a04201c0c00368450328200352181c10b84074200e503040c891310a0050b01140e00300686810203500030350354009504000d = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 103591016 1250 103589766 103589779
    0x30705041508030c010207150c020604060c030e010207030203040e0a090305030112020102191a0736030c030305030a0b0621180f0f0c03060c0901120f050705070308100311 75
    0x8028900070201c90014001000071607a40d0451800072078001d501900341035600074001003005c0310314401d83c01a0827103002903900801c65074840da1100001416145110403c2c9a40c4100410b0241c1d0203002400b0518029005952038034031b000e445684e008d2000707120030780241c9011500c400094126007030f43c0c1910854401c1400d03024487c40180c0c50520744c10690044010000300c014204501160b80702c060498041c156003003500c50345429180005081d40710f034405203400228140d800071001c6860480640aa41014156600d4465030101c5020fa0002d4000a800108000c4482200d0007104d151003402d413082850990f001c10183c44d1039174a181d0780c901c00c400d1100071650400c1c1c41e140c840b50740e003e4602030300c04141c07848500c81e90310356411180503024010a40c0716000ca10b801f150140c440c81d480c0051a28203400038004540c002c0d2000f40a240c066a00c03035074102c80070040e100300e40c0b2a6075192a507a96842443c1805012688010300c2d81151680c451814000a0350141c4221100300058541 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 103592266 1250 103591016 103591031
    0x1060c03230418090605240a0b0a03090201090506030406060e100303021906020d0e0c01120203040c0e0403020a080c0607081f060f090e040b010905184209010b040b03070504 76
    0x140d0300500491803024004508007000d000380503a001c0d200e0041c1c001605000141d041f0400700f8042c42210790b10600b98100e40a04c00400c0150281d0010740601d4414548030030b03040e484000141c81604192402d03908a990303800f05202c2c21000c003d100303030001c000b05140101180355990003556064409180b01411020b0541c507000c0041c1601981c841ea01049028008490180d04031a50348080110348ca0001e4600070011160020f00d1003202d00550b0001c109002090910f0501800400060003c60452061524690104050740060040d041103400900018201000001c08203103000c1c000f5091f040040c100441c0d0041d491022030200c424500348510300c0350304604181c0d142502c603804000811600c40400c4200400c0c45007860680340030b61004c00c40c5848200c40305248104c18054821694440f940c80c1c030104a0100c1c071040410b4020350801580000e145801001403d03d07480c100400e9005820301030303048001c2c0261032500070291410012081d4880009070b0b11462849418040c9994040 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 103593516 1250 103592266 103592309
    0x60f130303020f161106040b0306040b010908100f0506010e130b0120030316091508090307021c02090718170a0b0112030314070804120309050601060c032304 69
    0x6a40c445021070503003130303141c3c4015031311118840012541103600e4200782d903076207045c1d207041800d403010768400462030317800c0d030380c1e40c2c030074440240b01000c140741c14071000040000303800c8001c00c07040e2070888402002054101400103800203981e0041d01c500c0c18031a070b41089250903101c5206502d254020340c0c1012511055800050b25415440740e0001c1c000500d0007003502c0351103800402180030b2405400071180a00e070024046440c0f1049010700c0b1510b4810b4a000f02c005449440d0094201c1200d0055a21305a450344c002032015540c000782084c11040c101c0c054045d40b40c01c0036247d51011080c02e01c0840e5090b10003524401202d58002d203065a0801c00782d031018414100001e840d210351000d8007170b178076507190390340c084030414400b900705d00080c01d00b142d003940100a03500c154069499521400d81c25211076a502000c142000a5030041540c0c0711001404501c041002078000c0499441e60380412000c1d080003410000c040d020828030048041c030303104103444210101d900b2500380041c0c21203103002070380c17 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 103594766 1250 103593516 103593521
    0x512040c2c0112030c1502042c0a0b03030a0f1803030e0307060513050f040902030105010605041805040c0b0c070e0a0c0f08040c090f0e030d0b12060f130303 69
    0x40003440e42048400c80c1039400c1425241000180c5400d0a8591180c1c0e60f8a02141c61000c0028004002542034400c1e40300081c11104140410180d000c0094100380d112122540d42c2030030805070181148400b10901c02d0800381d01c01860300440381e00d4040c846195080c000c01c5d607c1c850340340c040042041040c0c554050340d2140586080c0c103600340d600708039040e0342c82c10000c1840c500b0340300d401d10a018915000989601580441d070542d13005440c2d86640d01c2c581000c0180140300b015000f500729446900d030a00582d802c0c420749000e011151102503d40381480701580e0108980241c0c0c009991a00c81803002149002c061841121505600c00e680d4548410300941011103550050700325103400b0003402640c1c1d010741c00c100d031580c1c19596001142c00c400764040300c00c00c605039400b91519009107014028018140c210741c1e80c1854210340416902c0014022038503541c00410107081980d5117034074180b4986004808519801003680c003c0420f0b06140c4040007203003101500d201e4180e85010880010140640c = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 103596016 1250 103594766 103594769
    0x30306150a020a150c030c170109020a050705030a0c0605060409020a0306020f0c0318150301031e0201020c100504051201020f03180703020a06020d110f0c010e0f040c170a0207030512040c 82
    0x1c6070194404ca407400c4980050165803451401080c01c0120082640d0300c50306888000b007019104421607a46032003a14002540440e64107020000e00700300141c003181c8208000c01190b2041d0391803413003803092800d005040781c138090a414822402d101c100710150380d601441c0d000f92a001100180d4407004095240400d202c1c2080c494010702002c12911f44551404085034807500080d00c1c5154180c0c5184050381107071100340402451130784c40207c85061661800100b042d030901c18011148051139090004003c103140140c20000510009014411410032504030303440300c1c0c0c01c0c0d8000e50800740d1850429601d4080106042850a800c18071100c603564200311090003141c001d803407942d5071034950500a440e20301c4442d1020101d1002510048261030010301c03410609481005032090442d20f10044070440307040884154440640c0c07501090941c0c5078071031180c2181d070a03142c0700c0d4902c1c07e41c030840382202c0c4000c2211f001e0a00c18020351012070340240803034034412110740a8801e242d9941c034001c000070a96 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 103597122 1106 103596016 103596023
    0x303070f0201050f0f13060626030408030702010c1104050c0405100206071e09030516080d020c0105030f06060d05090115051e040c050d0f0b12030306150a020a 70
    0x842141c582002c84200ca08040300306d10740740d1105032540354100b0722920304054004074044401d03c48801d00e08040c00c020314206407038042c503d81c6a0040e5440079042c000140000c208211f002201c445045070018000c00503410506c0c2d40030401c0d0410b001d0340c2d0042c00000b480f242c506000182061159005541e0000034031103581c11081e1840160ba407003024003200000100000300107002c080c10138060301c06084601440c1041a0b46402841064202507402c900034030309075030342d00408481e03102001040d0050340f0744840000c1040d5105255505200a14140c20300c00c0c03862040d04640320f05c072610800686540d441e48100310340700c00a40e80c00c0040c004200910940c40c20076800c400c0c1c01c003c40d82001030811a40c3c41d00101a01d100344c4040801d0341d40c61680c1d040704d14040c1d44416204006074019419443d0031400720300b0002030550800c01125021032095040d0b8420828510a103a0 = true := by decide +kernel

theorem cover : BRFrame.Cov 103417266 103597122 := by
  have h0 := BRFrame.cov_init 103417266
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103417266 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103417266 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103417266 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103417266 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103417266 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103417266 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103417266 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103417266 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103417266 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103417266 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103417266 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103417266 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103417266 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103417266 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103417266 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103417266 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103417266 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103417266 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103417266 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103417266 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103417266 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103417266 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103417266 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103417266 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103417266 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103417266 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103417266 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103417266 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103417266 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103417266 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103417266 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103417266 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103417266 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103417266 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103417266 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103417266 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103417266 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103417266 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103417266 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103417266 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103417266 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103417266 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103417266 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103417266 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103417266 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103417266 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103417266 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103417266 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103417266 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103417266 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103417266 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103417266 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103417266 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103417266 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103417266 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103417266 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103417266 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103417266 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103417266 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103417266 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103417266 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103417266 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103417266 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103417266 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103417266 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103417266 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103417266 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103417266 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103417266 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103417266 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103417266 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103417266 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103417266 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103417266 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103417266 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103417266 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103417266 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103417266 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103417266 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103417266 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103417266 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103417266 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103417266 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103417266 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103417266 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103417266 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103417266 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103417266 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103417266 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103417266 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103417266 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103417266 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103417266 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103417266 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103417266 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103417266 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103417266 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103417266 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103417266 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103417266 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103417266 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103417266 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103417266 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103417266 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103417266 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103417266 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103417266 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103417266 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103417266 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103417266 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103417266 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103417266 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103417266 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103417266 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103417266 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103417266 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103417266 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103417266 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103417266 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103417266 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103417266 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103417266 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103417266 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103417266 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103417266 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103417266 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103417266 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103417266 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103417266 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103417266 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103417266 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103417266 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103417266 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103417266 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103417266 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103417266 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103417266 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103417266 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103417266 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103417266 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103417266 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103417266 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103417266 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103417266 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 103417266 ≤ n) (h2 : n < 103597122) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
