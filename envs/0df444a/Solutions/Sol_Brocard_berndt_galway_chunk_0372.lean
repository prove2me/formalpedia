-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0372
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T19:28:50.381974+00:00
-- url     : https://prove2.me/submissions/a0ae0971-c85f-44a6-80cc-1aca95b2c149

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 66726621 ≤ n < 66906477 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 66727871 1250 66726621 66726623
    0xe01030b070804050c030106030305030f01080d3603050a0203063102060412030503091207030f05030a15091512050c0d030c0b0f0f060d03021b0d05010603060203070801090504 77
    0x2908200010300340d40c40b41da8034660141c080c004030740303000028602090071150b082e00180c0c001a0000104031a00da801c0c0040343c01840000020304104212680040002c846070b40c1d80d00052440700c4006003032944444002440210520300f44110f01c2d52071820070382d030303220f2040220f000380921400180d462031140d05c05000341010766441c1d64580a200d4040f0101c2c02800001c0340e002c801071002240907072203490901c901e240b10391644d070350700d007803d00a0500d003020900c0440c480f207604100e01e000203984a020580080c1150405980380c1e00d90801441c06051020500f401680b61800d0014515111740c10840171007140d5106050802c0d181c1d9204000707480c903100064007076841800340c00e4290501481000031325000349081000e07400350355623400b0220f009640420080ca007007014002c45140c1e0481c8560800d801f110140c540709881d5602a4950881403800e44a0350304000d0f1108071500c8a0103141542c583c000020807503542c032841c005d4001c2d041992240c0000e844540081071038403003817140d00c1c029 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 66729121 1250 66727871 66727883
    0xf050c0901030b0301090516031b03051209010c0210230f0a050a0903080412031706030601061b020306040605010e0105060c0a060207061b020604031b0b04150e030a0210060e0103 78
    0xc2040c440056000e403034500c842e283c141d96035000d243d0124000b440f840c1c622820000d0351090035445d60030700c010401c091030f01e0b081540441d60000c100080300002c800410302d071060081e5444240840c016a4000180c40001c0c1d0400110200f0400b0541e00441c1201c201d402500c1004c030b402c0704404441c1d014010940050320b103003020003840760003a002e50081c00203110f841c5800d502040d100e45d25840079030010f501a110302503100d0301c050100341d0406840c0d96106464003040e0b256242c2000004d665101c180301d10014000c000440c10040e04244541e54034503600030f0201c650302c0c2032514044009010920804104560000c00881c1030310f8145e048a4550010000401e00c000503a12404000e60250b90200e44450f650202158207003a01078503044285140d0b000740c2800d00d014240541003000d030050303e070910311610601b0000600c4a0121641180c0c102405512a88800040000170b010040e015a140c1c031001c50342c01c401e683c4c00140e0b00b40d0106240014803204e071f5101c1c640c140ca41001e01004000d = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 66730371 1250 66729121 66729127
    0x60c020604050d05030408070b190c0f0b04050c06120a11070201020a060f090f050c04150b0d0203041b08070f09050f0f04020f12010c030b0603070c0f03020c04110301090f050c 77
    0xd842c0050403003d07220302400030f8030718081c7d441380c079140740100d99841428180404650070500c580008856202c1407c28200181a075140b50340340c81e1034002e2500020441d04034a4003041c02d2001c10425030644c6003010b051503a81d50301540c161646c0780f0040b0740781c510312800c011901780031140c0c1c001614402035041e002003549603441d03a65040913208246440c0c110a80d1401c0040104a10710035082056000d4400f400911310b911040c042030390540203041100c1400c18a01f008261a124115030100070f0000c0c00586a842c1d40c50200c6020400302d01b07680600741488004900c02c100401d40604407004100000300445d80c2e44c1d0000143c5100b1a00b40c00d00124102c001a00b001d2100f044a921510040040140e07810b40703030016103a032440d124200c05685d5a181620501d40d054400c464070450b04072074140c107624184000030022954000f0080203204440341040c200740c020444240740f1080140240b025a8540c4e141ca0f00c1c0c2d807c24403170b400c4030318103182d0303074244090030303440b1301400340580c1414545 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 66731621 1250 66730371 66730379
    0x20d0807050a08040f0602060604090213090501060f09020a1e0905010f0c14030c10060f060507080d09081e07051b0118090902010f0206070503040201031a030d03090c060c020604 78
    0x6194100d040c080e00e15004806030072000655020082002c0c00c031081c04a4029402e1030402450044000c110303500441ca0400c0c013801698610031041016a118040401c503401103283c95409040140e201d00020044a200403070a007026801070640c44150765a60200b001c055034840407241510541480030884c190401d00c03e55225102c5800d8000caa42401c00d0111819961100451301c03c540011054001060740c99101d43c0a0040007442440340301c00303205550030310350344814007a82e40c4140c00070f2010000b40e00c41000120340680316080d6044200b00804105804c2c0fa50b0164000c10880c41d20310340c0c61038030f007a215a000c401e072090380c0d03003010040c80004200744412b2110712182c0102818002024003a09c1007042d085450380213001c500b0700114600181d440090708050207030700400250340080040040d0b45a04c1030507030b41e119809180100708540c8044c0d01c4d105210302102210307098050101140d4a45405810810000d4800c441181c140b580c0c0f01070460f0058410300f0300139400201008200 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 66732871 1250 66731621 66731633
    0x70b0706200d0509010509030f031603060305031305130e0a0f03120207140601050a0e07080604110c0a02090a02090a0504110405100906080106020601151211180307050d020d 76
    0x12803010380320044007105090a400204540041404024643e00c45041100d074807004c0c0070303081c0c1103e40701000314141030215500925500004002007141141550781441d8507200c0e40082008680000c10340c0d581e100b6a1940681c540f004d401030700c3c02134005040000411402e803050601c91841c3c0e802502d080505555410410901c000c81501000808170118140101c00d2000b41050351203141c5500b441032061010b0750511005a218903c1104120420841035400e1142075600901a16100002d9070380d29001500400500400403110310000c14038210491000494107840ea0084400344126580e07008403805038841d1190b2680c00c803112880421003401c00e60000462200d803139040c0e50070030b526000420001e150404424002072600380e42005041d8000154501500326031014107020741c14907800c51000b500e01200c800800a07281c15103040e03d01180d00020303490080702c05480d81c5000c007140118076044d42c400b00b64070a0060f088002a0f41c41d104943c610342c154068042c0d60540070a031a1b00e = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 66734121 1250 66732871 66732881
    0x1206030d050406082a09090c0901350414010e011116031103030901320f04020103021210050f09010807051504080703051507030b010e060a03110304051e070b0706 71
    0xc080c2502c209040d1017501124410a518150f0440b120140ca400110040112600028000720390211081012440699020701200b0b01c60f03a00c42d9003902000d00242c0b039861100301921540c2e040310818402e0008014840c0075042d8507607020f2000340705401c588202c10b400c0b907a104840c0c240070355042141c0320380001c02480304810140a418024800010300050609503402154036000326555183c804400b0340c00800040003100180d60b580030400c003007000c1000e00c0c40000e072034004090441c81c0000c085a102360112014421400b01d10300342c030305081c035900c40d501030b150007218072400911a48103020b06010307000754100d48100d4000d01207145408107000440e290710780c8460b001c400411001c90041030400c82400214450380041031980d11250030310315400e0307018201c2d908050810b000d600242c0e0348400a82c8004c60301319821690381c00e09120a40c000e05c1d0b204540c5c1c96418000c070030081440760100303164400402c0192510103003054400026201c0c0c455026106848109100d100e0101d51a580300c = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 66735371 1250 66734121 66734131
    0xd0f0203091302040501080708090d050304020f040e07030c1a040504020711060c0d03150305030a081005040c020a05010e01020438040e040213060b0702010e0411030106051206030d05040608 83
    0x540e46006030460105040c00c0c11070416600d5181c00003001c200ca035a21030144c0c0d9008006152403841810600405901c4a0380110440100b03e00400800c05640e60b030000b903514400010000c0101c3c0e4501a1070359110302642c4000c0d9000311400304005041c500c00e40c441d10403c3d07070074800c3ea403800e4202410080290001c180c1583d50f202ca0f14042c07001500c0d0340c001400c0c00420b2000802e000448204000d0030f0b00c0116040080443c0707640000c10000e83d0000584450704101c2c02c1c0b407a07040e500d1041c80c60600f04e0303a6100c0c0340c1c02401c00c0360744070a03da00402c030000c440e8003440090001d10703221040c141c243d01ca140f00e1010643c02021780300c1c01c500c5823002d030384165010104458186d0180f113031001f295500582c110085e4488a01c050104520380b103d030f1100804800c0c1c0007840114680700908041d4016050043c1c14062040591001980c4940c442c0d03504085242080d03490b940c4034803000b00301e604001464181c003501e00011030054640011021418203040d51100e01d4a41010401c42e60484040c0c4 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 66736621 1250 66735371 66735373
    0x30c2505030303011e0b0f0426100e060c040e0103020d050304080102030f1f0e0a0e01090c0b09030d02010e102406110706080c03131403030a050106081501020d0f02 72
    0x200216190390188000c50003412100e0b0a400f44080c1c00880084425040c0d00814690000300a11401d032074030402940c040702c141d542040543e084498880383e08180a0707403500410301400d0700d8140c1c01506039001742c03000d08180c0304850741c0380c0d101101e0032803c3c0b0030b5018000001e82860010001490700844511a4622a00c150b0342400d0f507803041c0310309a03001a00c910044140507420003e6800e024859410000003d0304c60401040c541580200d000700c010717049542e00e40c2c0781c000040da4600c0c04d4200190169200994070500396503046d0f56022500000c44d0f59109000b2407038407203003562050041500ca044844080c0c64440c140100480080103031141081035003907031040b80d030309048420122030002d00150700d90200103840c01c007103a414118140c0000052007807076014000b03070030069020780343d00100c82070618041d80381500f40410b040a15614015851000104212003140c9642096040303c01503101c0311401c0e142d0400c00517520310808141030050740400c400c030f80000e10509071048000b0940c0 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 66737871 1250 66736621 66736693
    0x5060a1106091b041e0209041103010b040e130803130c0e041a090102040b03010b090f15070501110307020a0b07030b30010c270918050609030c 63
    0x3034105401c1c044120350446240d00801c1084580c00f84203820802c1c20402168100903000a80f4842d101e81500f03010f4800d199640070601c0b0019803180d600911001d02c7d0200459201c0da901d2610543d240c0c01030189100c04007091011038490080d200100381070075800101c00341595104218a503e00400c440b0542d240541124000fa2400c10135a0190285020320016022007004080782040311401a16a01c0e281c0e20421042001c5c00400c03080ea03055400801c2c07056922009500011030100e0916003090b8040b641d10080012040514000c160040c0b01308024001c6a1500e1154141400f00300c400101507005a01c0900c002103c82c0017040e8088410b040001d581440140071a240080242814030304406086050014024181e400031707140c002d0700000d015180e1002002000000100c0c05c804107001c0c003900e81400036003003c0c2c120001d0019410302708504420150700c00003c6007401c905407524068040810003104021003240c0c0b0710b520a4000740300070b08d00d070b00e43d456500600c5420704541062007 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 66739121 1250 66737871 66737897
    0x9050a0b0406090b0a050703110414120304081501150f080604020304050f0706020a02030f0c0a03170c0a030509010e030115050607050a14030403020907050405090106030b03010b0d060f0b060405030705060a 90
    0x140285801036005c0d200015003441d040201500321640e10b07941d8051000e0a03c8200200c410704826641c2204c0243c0d07890004a98003180310345140030703541101c1c0c070384d0240302e100d82c08024a0180305812120b07899000c40c0444100c4000741c40e40a4000140d0000400380d5001030158200358005680040c86031048a0409549544c40f508100035900701c400141c02401c012029440c0c100805030f001c0c0d482401078219998103a00168003800b05110041038941c2d02400c0d402450a00f03000d69004034100403d0303841003055480c0041c0b0300d5105242041c0440c0c500092000c0c1d0341014070a1035601512001c10003200b904010800c03405410806045441c1c0c400d40036000000344040702242400e00505000319115801d5204005040500400c003408014050000b0032580c5d46103030405044800e41c0c1400901402c99501107405818130030348130b540051020b240f05040111320b5103c0700a40b800d082013003041100c9101001594803e074864240d0542c0074480512481c80c10b503000340f40c8803125041100c103402c0740c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 66740371 1250 66739121 66739133
    0xa020a020d03050a09090e0a030305070c0c030503040905010b090102060a1a03030f03090f0f0606040510031e0303050a0b060f0f13030f02040b040e03270a030b0109060909050a0b040609 81
    0x3003801c1100000c0d00403601c0424a6040031a1030041c040c0c40303c050003900e103851a02c580d42c455111003d41010340f640003180020f4020824030081c01d40150b0709400707450704c9041103503036640607201e0118828500400010f40f4100c41d02940c060b510168041d1400d174483c1c103a04009082d14819210050608000035011507a00308014a4640d02840704d0075103e2402000c0541444490380380000e00f9040954216100c0e84041280c50388504102e800091540386d002200d00f074814103030401820000e80b80d0034005109441400c03d003880340b2a50b0b05022590711015100113541055800c0d5030401414410b200e403e02046000d480e611604040e001c2c01e10442c9034012521020b01c1d4000d4071000c40924080c42581041d004400800c0d80940b0207020405062403615582e1180c0347c4103030f003400342e000b1419010780140e007246084000c004000203500e5803a41000200c03060700303100f108030661400030002245507150003010401c44e002005041c498210351108001c4020045c4119a0955074000b16400548 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 66741621 1250 66740371 66740389
    0x6130c0f080c03160605033106050f0106090f0b030a0e011805010f05070903021c021201060501081005010c030f030906020f0a0e010c02030712030c050604030e0a290a020a02 76
    0x6041402800a0b0b2607030000d0608001d0000408a00101000d4040c000c481c3c000046a40160545103600c03000c40d241201100b1490f9041541c0040000e000c10403814030020f604101e005940c881c2c000b24030390343c0e5094140c03000820742c41861008141074504020101d020405941c1c01a040c14001c0341c01041e21009900711a4a182840c400360190300062062203001d10072030246a40e040c0040044d4100700741c0c040e004c42020b00c0300070f00c500c05021209003112101d680c02c000c07480d4098400c407061f0044030140e50180c00b043c001c580c00203c0480000b0810000c98000d0313412520182c488445092164a04940a042c80c012090500d600c500181002501a1009001c50042070b02c40c2520384c1103041c401001c41d007100302d00d14100409918400050b0341c011419401311044c03100000306004035441c00b51441403100c003010307105005100410050581010b008c001c0750b0421140281d205440f0403142d40c1034064042d01000c2420b0750441681da00d07800d03a0040864141d01d00440342c8841c0b041c4d00140b5004 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 66742871 1250 66741621 66741629
    0x13031b06031a0d030c020d0308060f0102060103110603041a0708100b07050d1b0602030a02131d130807060c02010c1202040303080606160b16020c0105070506130c0f 72
    0x1110400414455040248194010344918641448005160000102ca0b4001454001e201d19071020700e04040500600390b41503600d42c0981540b40800342c1d0708010b03104031021030700b403402484101100b40301503102080641c1625408210036a0910b020710602001e40c000420072200034681d400c01c60100b1401c404840e10680a6582d0481c2500d484403400288d8051a4404403c06609000e1900058401b003515103e2402c60718011060180b62144c44c000e034601080007904c11407002050cc00c86c1032541e00100000f40025020080180c1c0d240e0031540130840e11416170304480c0706200070403084514a48180b50301c40c00f42c0a02d82c03c10a058507110102d410500b60100580e640724030b8121115044078a4461a04003050110f040524644024000d180000c0600d84100000512500d00942e408650424181c000c0b01ea50a940343c0101c2e00b40d0440c8030351055002520074954110015846802160000f42d0302001422003a2a9030300142c0c080050324104803904102d00300c020500c203a003485880014 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 66744121 1250 66742871 66742883
    0x60d0803040b041a0105090f0709090608100501080712110406030204021204030e010503060604031e0c0f0e0c070f0f1106030a09020909120307050d020408031606050f070206011502031303 82
    0x1600f400d01d0000c000d0103440c0c0c0e07150340301c07071036040100001d0f91400d42c6960b111583c503032042d049030b03102c0c1c004441c090b05941260045915240300803510300000101c7d8400c03910a00c0301003280da600ca40c01c19036900d8162269060208010000c81e0000b60710f00e01c0124104405080403590684a42c00101a6000201003000c2520f00a080005041d40000404100713002800c0561660a2402c0402c1b240c0c0b159001c050030340c200c92081c06a0b880c1c03101b21540105600301c000d51791200d4031034070240f0341c000300c51003078500010314540803d494074000801c890100d039101401d007014100315626281110302302d07042543e100b2700f042e4035466140c8584000354032414811200044074101031040000a0034040d007061210350101c445000b01403102c40c22680c000c2202e042c030700e440d900414001d6000e4443d03034010b202d0724000030a40c0c601e04a0184103100800f0b21071281403000703030f076000003160392841c0071618840160720060040024044603456500c0d145a144180c034500200928002d41000c83c2c0e038012600 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 66745371 1250 66744121 66744143
    0x5090a080a020c09071e090320030c060703230c0705121e0609101109010309050a08040810060b0c0706031107081207020d0504080a080a1106090a030e0f0102100203060d080304 77
    0x3000040079040c005001c02800c2907180d040c08c54490020143c0d0401c1d5008000006502028160382c00b00f08080600200900044d5079009615004180000c0c036030350515900034030b820010016140b00240d03400c181040000b054030ba441c04040040400e40c5048844440c000e01402044201604842c03046034520000200103a0920286161801450905080348185401030300440d030010382e011100c003e6024a0041081c01c5c0500b0068104030f0f03d4440202071000004000440000200740b050110346841c0c002c20502d6501c5036040c2c1d1038030072825030000c5c5401010003440180d0281e48190041801d070b0400b90f013000c610b0703962496280d01110000d0205101c5104101d0103940c10483c140148103140b500504140c0f800800b16581c0d039440c8001801204041a03601c401803040a042888803210002ca42140c1407940c0c2258881701500300c2031300040c2c0e08054001250402850114000d041a402400c0c50035510031100001d4001409003540410040d0b440b0300410410400366000300c4c001c2e004214 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 66746621 1250 66745371 66745397
    0x40303060e09010b03060108030406080a0510080d0c03140f0d0f0b0a0308040302040b0f0307060c0302191209082d0a05030c03040e0912030406050711010c120f05090a080a020c0907 79
    0x883d046c8140d1080100f648100f100707116840c3d000189175008050703914082595114040c9055450304141c201024900c99851440c2c8140d034010494009140207031201094195012039a142500c19071a803801920405c000107240100c16030311079400c800c2004d070001000443c9800242e00d4880c10b81c0255480040810203105501d8070b8030815046210403580d803140c030101d15010035100c540b184a10003d101c442d000b00c409040c02404144940359080074140b01d002c0030352506000d4000c4011807000081c3e5a5540411802070005602078142652640c8a0040e034010001c0c3d1010514a4510101030080784503810008100704050030403990b142c00078588a60400c42c110240d0400244030700c030b195110790075450b03101c08803804070794019411080125142c1d90703502c010b4070b5102d00900103041540c41d00c145e404515901c14040469449180818070800c0c801c40e00c07480603908140c80c030041e6a000380c0e42d4580011350200052030920f285005070342c003008198000688040085500c03002040c0d41c03241c440 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 66747871 1250 66746621 66746623
    0xe072c0333011203020a0206030408040b0f18030f07091104030f0c18090201050f07030314040b06010e0105030609270601080a03030c021504020f0607020915040e150a05040303060e09010b03 83
    0x50140811402c20300d4040f44580b0000c1d0343d00c000e4880640500b500001190501c02c01c401100c02a080200303410b95601d02c10120004c0c0c13035205802450344071b011100d4440b000c0c503010502d40030403c9100b00802d503003030030040440c00810060002d294203140403c00040042c9980244540003405200c0901d4094540b404540840c40d110a00b048010700d081e0901c40141c0e0480c090758400200d000b40300343c0320a51445d09a0003080f5240100840f0300b200310804c401c0058428886100d88002e0341c0d2039040c0d00c00d610065569000527a0200c1c0c3c03110942000481e01c3e80d5583c001748c40508441d6004140380b0750a0045800c00c2e0082e0442c40709600b2540140082c160540241c3d510351602d4030091452854454172032100d403202520081c400e030700d08030098804d6075a1005a49056400509d4072445040c0900300c0d81217082a0020180100e0601241407121880401c00c1010100d5207003002203030396140c0c00c3c002c1c01014020310031414075507070303900205004954800e0345200d2101c48000007012482d0358201 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 66749121 1250 66747871 66747973
    0x60c0f03070b07020d050a0f0908010920060903030f03131202010507080105061804050705040b040602010515030f0307110a1d0f0109020309030d090510050c040e072c03 74
    0x19070190b40c000315481c5c521952000c00c540030010300b0b00e03201c070812000e054225409a0540d005120541c2804c0408051182401c030800502d1100d48020b88540c4c0f40ca021f001544c060310105a074180c100b404059000d0004070001c40c2d02c500e00901300118848560b0310011007440d8643d840005079035680c100140117410500d46030241408443d04ca0404910700d0040020200340400640242c5d1540c000c070300040e014a00340c5015140350b000b047d803103d8a424000380206401c860302903545590001b110700754103000c900b00d034100601c5d401035441c0400640783d0380c08110001d50079a41220340c0b41c0000410101030300f41c10317014110b10952000c4a040c0820481c40d0800e040e00b011950901c100103000c0d0441c000000c0307a9100c803640794081071300400740c2052400c10f070b211042002c0072403d00003009a60603002000b031040d11a078054411941e282c112040301c0180740c1504403020a1080c1c11100c0c1c4040d810600b01c2e2180e00000c040303070341d201c0303c40201a00741503403151030200a02c3d038005046000d81d4951a2 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 66750371 1250 66749121 66749131
    0x3040803040506150a1e08070603020a03061401050301031e0c060c031205090c010c08040807060c0c08010e07030b060621060f0f0907030522120305010b070b04020f060c0f03070b 78
    0x241c6500d240f40c004c0090503180c0544036007a40e4080380154030b483c0030402d03544c80c0e004002820a483c162556180082c000c9e40c17040c0705900010703142c4840031074401d01212140d0000b003010794485065070300f569103074030b50100e03030160001e0541c007556a5900000c544542400290010355110036005240c2d1030b010300401c04503130b60208004d0420017001a40000080c180c4110785091a004400c2c00590402c91920310590300041d002e801149000f040541d0448510f06103107100342c2c620800669202d65860132112441404203003504070700700c2080420b1952080301e0300040001d100034038042419500300e00c0100c400410242c000d0300c6004010940c60000100400b00348141c941400d078841c81000121002002840203051503503030400300d2540c078103d801d41f0300ca0541000348c04c00390344528101900c0300c4101007071040c002805c1c4070005c07039802420026905032960042290003162106d908110a050618004035004031081c003103280f150404001e42081a42c440000d55a81e07140360034452012480140 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 66751621 1250 66750371 66750391
    0xc050904050c210712050a1a1e060703030e15061c03050d0f020909010602060603011d100c020f190605091203070c0f0b0c0c01060501030c0e0108060f0603040803040506 74
    0x200303102d07290500811640300c4841c9102a400f0380c0c2d607a01c1c151044070001a609154500d00010032038061101c0d44800c500611055160080011507030401000c910b6903a8880d900b0103884091101d5400e00c40060200d1510904000c1403004072180e56901d80102034004040100e0b101007446014140640312502c50076581044408110741030b02d018186210b680448a005a59004202e4421409034145d0b01d507440300400c00281c2c0d595550009541d5202a1016403003941703410049400315035600c40c200d00e00429440500200b611080c004401042c407900b0440a600800c60085800c0c0c03000e1100c00c0f0b544d8204000c1c4134284140d82000011140000c228038886e612588a42003041d915005503680b104032840d10302c1031a192450011441c81040100810130014203060001491481d4003074481840c50381c008100e01c41d0750f01c004500b9505d0000ca2500030a034549070702d1109504c500e500560040003e000106000d00364804a00c01d6841200c00703581105021040c8420001e040c8001a005a0544 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 66752871 1250 66751621 66751627
    0x6010809031620100206040506060303040303090e13060c0201020c100204080303010e1005040906020715140109020a090f030f1406060a0e042301060906050a0e01030b090307060c050904050c 83
    0x5010b242c6201404040a06220680714203001c224030160503214912030090440c806100102d400a555204180c17000c4509016a1000420b2401c0c00429034003200e4040d41c5100b540d516080542002110140906602e901e40c1044000826000e004403521161542c0c001a680d00010070f0f00c13428202e080301c020850a0041104000b00c103000010faa041d100e140e0b1105070240c96050ba22442d103252070f4011500b0500b0400b0300e106001311540070745500c03809070002a90081c29804400221003842905400701c081150041c01b0304582c42d03010740300c0e10209040202c2426141c112022494245a00c01c41e11020038102d040304100d92200341210b0503d4010081410307060000c002559129070703019602c140400480042e003805031540e81d85a1000f0f501010480c48903444000f1713400b03024540584524030f805c020b00001d0b9410903c0765a822901405150101c3e0303421659034034103a0390b001d4a03860341d510080c45884085a000d115180d43e42d00952075042c3d0310034034101032109584006004030300c688801c4c = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 66754121 1250 66752871 66752887
    0x17060405060604050c0c060403021b1903080a0314040503040603110f070f0c030209100905130803040605090a0209070c03140a020c0108041b0e0609011401172d0601080903 75
    0x81c2075900700c00100c0d80455a652078030381d02030242c00344141e09400c0744034003014001403580101d91803060b0900100c940021a042500b03000c401250350300914207e805e42002000441c0c03065020380480051864003007154a00b015002846900c1928166121707003002404200c8940c05100c1e914008202500003401c04090045007101030143c0d09018000d080005054030801c0a0074860300e018543c01440b80b00703076003403042d0480040c00c40c40c000e00359014980310204440b0215410118401548800060301e156529074400000c0d00e030190100c01e0360300c219403800c00169141e0b40100c3c031900d904d9a4100002c0c400b818010b111820400481103840c00802008500680c04510660015800e0801b0020313030320384d80341420f0300304010780d508005003280d98404284001040f00ca9070042c101150110016600d5016400d4000c0b00c00041c5e0b4046241c0b048445458002e01003a198880e6500c0f90030f0020300d066040c1500f090240d0644482c0e240400d208001141d03800c001d5164004120400031414029a = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 66755371 1250 66754121 66754123
    0x60608011a010f0f050d02030a0b0a170c19080a121d0901050d030e0a080a0c0f050604051e090c030f0708010b0a120902030f0102090a120b01060c140706020717060405 73
    0x50040810003c0e01001000d104e0302580440f109010440011543c0e8a0a90030707600080026000351071051284040c00a5030100c0d49070800110581c5001a112030004102005140d292501040c030450220704c100040820b0300340258000103000d003075800201030344074400920114034120708c0150610640f402903d9905c4001001e410b50300141c80d0130f10360318482d00b81520a58841060302d580b02c00000d6000c5007101000c9804441e40e423003039060000b002d0700d0300c1c00a0141c400350701a050300041c061204000e689084940b000c0320b500b410307507996083ea01c00c40104018180450380c5000b0400c00000b0311030080310b16105141e1083c005d00c0d058400b94188030060409105001c10001000181c5e0300060a8090783d500c0407038402c1c0c0c0103048404650011007036a011f5001110712904c0303000c401390001354011000d6090050076034400e013204421303820b0440035115010380c0c40d000d60b145001d030a6145401c0400f04008400351443d80c004250552a0403403403840941c0103907800304150044414400000c5e0 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 66756621 1250 66755371 66755387
    0xa0507031401090b010303020f01060b031b0a09180212010b0c25080718050705030714030a0609020715180f260f03010e07030c0503040b06060d09060608011a01 70
    0x64000d4108990480307184800b4090694a040a8030001481d0000400c040c1c0001c0c410903c103144038000e0003516646d4210b44c1080c001211201a25091380881c620008084d030003e16001b007150805001480c0c41d001c4500030316070500d80340800f80381d00041685522058803411401003144408862802101c01c1038aa164080c21350803200c1d00c00c0c0082140389520303456000c800034040440032100307400e90b034a03070300100c000100e45102002c0d0320349070215008034810f40440b48920480c0c0c43c0d0011407000002c1022083d80010041c8200035a0342601041e030302d0b194001040054040d200341a10700881d0000c1c0c804481d4500060a5a1500c1044120014503000008243d01da009502e140f144440200c101c0100842d5510150440d900012540d034060401c0010318140c49003000d0000c030f03a6403400da090f400c8440b443c20030804101e00703200140001341411000340d07204030701034022803c15214240c40300a440302c4c400c084540c1a1a008284881c0600b445501440800310b086049801089000601080 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 66757871 1250 66756621 66756623
    0x180503030a0c0606051201090b070309050a0b0702070506030703020d0b0405060f09060d0f080a0305010b0f1804110d0b0f041a0111011407110d0c081c0f02030106030213080a050703 79
    0x200791840d100041c88450b44c02100180406090b50f056091504801c0d130080820300011200f0b0041d440100d20b005100c5e1207000151f503170240081803510400e03150741034506401440e90007107108210004c5000d88852020b140a40c009807070251311982410b40500641c1c1e1841c81c2c1500891170030b010000320740d698066400800e03c05940e14182a00d81e00082400c3d00c0012201400c107440300c2c8115010400c840d4000c0140c414543e500300000d0f40c032a02110507512444c50402d140000c10710880c0c601c100b000c0403540d00141d008200142c0749400614020303842d04181c4060700416a50782140e0101e081203480082d2980003181d04000ca11402c0e80381e031110707001890300503041080540c040f280c80d02d4250301c00000800010404540c0d4902684000d02c220074034000c04d916030140b80f068100d80d80c0610469104194080301c601e00f454104074848440c825980041c05103144c0f140c2d00d999081140c0d01c000d60203005d0300c0c0c0c0c1c0540e80c2d036644243c01040c002640c2c48010240d03c1380c4510004242c020554000392 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 66759121 1250 66757871 66757877
    0x6121a0d020103090209070c0c060503041110030e0a0b010f06090503030f0c0709060801050703060501030207020a03020913020607050708070501051806161e03030c02010209031c020307080301090c180503030a 91
    0x2940c60004070700070060f00100a400100030020300c02c141e82c0080d03224038401d210304d800c540c1807902d5003c221154001030310001c08a100e0743d03504030b000c0d151903214039201c603150303140c0040c40e840031111262074489290b0056594503484c40040c813903034401c942c0c80b81c060010340c1030082d41c291500010940d613128034088044034000c041001c107460303030041c440103008100d8040180b0100342c032040924000c01054034440c01007482c00c080010154000e0080c0c89141e90000c201003c41495034007840780020008110544035041c51460300c0040e40c3e0a000381003044d006400506955042c6280c0c9860003800341c0001d1306205060251120003030848400300c605040684620b500c42c0000400d8283c5017864040c005d0680d0121a02c1009082040c00c40070400e80c002e0b40c0600c10002441420f80c203d00c80c21000340d825800074070001d907000000c850340c080c0100d454411a850a0070300c0c0c8032900e10750000c0c1c02418010351180c103c004040c0d07004d850702d030461030725500c0c044042e481c0c00c00003a80d0f0b104031046e802c18 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 66760371 1250 66759121 66759139
    0xf030f0702160f0b0a02010e030a030606020c0d021e0105160c08070b0906040b090a050604180501090e19080c161401031104090504021819110c031b1c0906121a 70
    0x995100303400008e18007040d0b038103ca071102d411038000f4010344030b64040d090040c403800d44c0001c3c4610b0400710360713000c664010700101c40c1c2c1c10200042000c5a034401540074140201000000c0604142e486802d1700c660243d101d40e407141e41014101410201c6c285d03c401400e00301406107404c2a80d03011308840072500b0f0b015005641d030102e0310110b400c2c4080ca5101c10390100000c01c000860078501112188082c500141c100b18580e01e07070802e08100c95109100e202a540203a681c580300d13040c50418118054000c81d1402e090030040c0d009180f070038034503590305810700f6200030042084004800503025440d5007402d080c00751000002204481d401a071040304103503a124004901903466003603c80041241511015000e4541540500c00d00440611108031013890003150843d540c040e003090f564104000000341d8a85540740d507132581c03c950103002407102ca0040c140030305000d00340c8401c0c034000b032a5a5200e00c21f21515000340500904100b80400907640c2c01e0a01e20120030340c690b034294040120440b0050701d = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 66761621 1250 66760371 66760387
    0x1081c120902061903140705090f041d011506020f0d0813020301090507050a0b0705030a05091302030405150f060102070b0c030c060901090c06320f030f0702160f0b 72
    0x40504030311400070307400c0b2000160035401c070551240f0b00c5020001d103032418050248194815403002c04115901f50020b9003c1c8524440d0b07242400078016121002040800d03245079403445031b038005c105610480c1041e903554800003c040f0300740f0b403010024103060002c1d040000945e59101e0b1507408505c0700000304421080080d0300900d01f20382c10011240c01500801203a955803800c69540c000c18054148268091070b0005244d000d0003040710b0b0799039400301c0a14100303018120162400d410003401c45600402c04604582c00c1441c40c4003070b520840c000c500a1101141101900c2c0030004094a03401c040040740c0c0030402180d0700000c0520803540b0310300c80c00da03441244101c180c0c1540201c2040200e030703018120038046c80d41015004000d84500800d501d0091a903251800c0d01e858041c00d07208041c1c4541496032a010044a801c0c442c101d510b802d40003031404002000e031040e02c0c0e0044800003d079408c0103090101007603040000c4914008884c2f4000f480340d003400601c407400c01c5035203d442480400061031031 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 66762871 1250 66761621 66761657
    0x8010308160602070516050f18070302042d050409020603070e1203070302150a02120c0309070e0712060f06020c130e01050c0409200d0e0a0b07050702030601081c 71
    0x54120b42c00c9001103448080301d2074080c1d140e5a40c0302403045c4078141304030302240f58544070301c1420b8001d000521001d015121204107409200c8020300c050203040e4240400102e00b0410201c909000710001019460303940392484603083c55060390400d42c05145003031150342c01600c07850100c903044440c81c05c0c0307505800a6030f0000341c44600046405c40c1a4040891004209900060f6001c00c8806007214032240f651840207140481c0181e031000d218544030f0b0004240f070050300d40d00940d0007106920640b440280c0799150b003d003602042c2c6070800041d600b402401c1d003c420314450034024120149200c3c0c2413500e0000001c2d43c448103419950711031a0390f16090f0350f0302001c2e50710454030224001d000b846185043d102d8200c240d02f1511490079080c2c01d04181041a5160f16050450013000301d01c82424004440711060042c41801d0080000c0e1040f0381d00180070030903a101c41c42c030440069592035510380042c41410708081c01a07102c41c45590000b0012a000c03111002c0c01a0702c1000c0d0702d002200e00f00f040b4070701 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 66764121 1250 66762871 66762907
    0x5040203060301150b0d0605030c0a051009050409030e01020c010c03020c2809020901170402090f040f0c0b030a060803030c040603020702060d060e2202031f02090a0b04170d08010308 80
    0x181c1d0741016240c00180d81c05c2180003810303d60070f4a803410002560341d4014542c4440e080c0040c56400180e028080c002c1d46085000e001000c041c528041d42a07a4844000c101140c0321800140c02081240003080460769041105940c14039080c80e003551000c0955502030b60b217078022030000d44280b0800081c554039801c65a03070314500003428000e000606a64000c140c0c02544454189070001c5c00560a071440e680072540218082c07680503091144540e05c004c3d20100c00f03070700a40210740141010100f01c000c00c0800c000e4401911400040e180e50f8185404028200d13089a40b140030300f50014400c010017001841c081d5030494550f4100035944003042c7c4001269071258000c2d461312141703043e002003044500039590610a080343c6079100b0324114030242488a4035442c0300000e5159111540300c00d2600c044a0000c048008141c4000d0b00f000c2e08503002804000341c07134006081d0200c000c101001010f49800d401e004404029001c1d0030a40420400200b980d00305000140948500203400c06540d160a468 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 66765371 1250 66764121 66764141
    0x20a140c030d080703150e04050607091d0402130212011e030804090c050405060309060f0a060503030316020705030f0a0b0c0f0403060902010207260c1f0810080a0c0f0e04020a05040203060301 84
    0x488903040d12107114400c47d460a179016145c030f106075800240e100d40109100d1056074980662407035100360f500201200c88100410807608011100141410740c01c00340007600e501030764080c50000c43c1d810480800c6004410107130125184034207440400c0800c501c54111810749015107404034101880c06410b441910607540030750f07044a000810403a90100200d86a4024248443c0100c0242c0310810004d040d0b410701c1c0540ea9140d00200041018818042c040840485060054030405907407480040d06100c3c2d030003e400910b401c0082000208101061600d60180b840080e1034144102031019580c58003c90000925483d1354038000f0301560b00070010f200050035002184e628441c201c0310070000210b9176100c04021403040341c004201901e002130f0300c08002030804030b140514140400c0c00321680b050107810464941c1251a010031051410710242c40300754040d0303207400b00191401c0135003184c0d41969030003841c0c00f104a07024000140d40c0e0380450320860704129805038072615041e001038010040d200c1 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 66766621 1250 66765371 66765401
    0x5040203031201180501080d080a02030a0f05070e0f0406060207030b090f01050c090f011416060e0102072301050702030403230d020c1507080706090f050d020a140c030d080703 77
    0x204012082150104c403501100207201c1643d0f5a0a9107650300c3c003903505c0002003041d031400160402000d5010315840108030b280400c4840c1807141080c116082641c0010001c0d140c40000360385800c1c900c2805041100996042020300e180c080c00a407200503078080144415103003008529000c0c1c0400c07080d002100c0c0c0c200200414140b52203065807035803249001074080da0180029070410f41c0500d41c05500c540d05894143c0c50916486034108000440084c11503a10b9507429a6081e10002480981103d902ca030400c503984034046841e43c100043c140105207150785c104400c01c2200e59020043d1400c40e948000e0003e0411404020704065034040c03503481d81c142c85529032034038442d54001070286e15000161000f60101a001e080c0013168460010003901c003402c01c00403280001c80c65031011a01a0141d420b80d04002e0725540c1c8c0609007005a424080103a0103004a1002d001407904030903801032100005080358424200466161066105640e00780440c0c240001d00d843c0c000e0b08120003490401c0 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 66767871 1250 66766621 66766657
    0x21504060801050a0608040c060315030b040b040204060819060902060c01090b01050111030901090b09060c030a181d0a150803040b0415050309030f030405030403170c120a0504090504020303 83
    0x3400400340002407052a1040100000018446002e040c16900458100d81ea480c803a038200001a0050155403600390441d076501c0c0790000100b0b050710049800345115441d60451410580100402d907002d80c1c0080303407190072509421890f6060200300459150388410301003002c04141c00041c080b8051106140c40a508000ca10700c01c21484820b1315059410036252003103a00c804056842e964080d00340124042005500b05021440c100030241c0100c0030700400c0307185001030000e402400c581100c0c0c41400441c1800700c0c0400c040061941c00307405804440e01c240c04c1008140040340c60000041c100a01d4107645034003042c0503e1111440d44081d020403000c60ba40c0b075580c0d00c000c41ca00d900c07503c104046140d80d4561000f50512520880380030300c0c0400002d41c02d180d8805a680300d1688058007c03941c1d0b2204010010010384002090314029410a81d041c0e1200308822040c0d045c001c030f043c1c80000504040240780d11407900501900e058401c0708000060f0f44d9101d202003482c0d8401d080504d1580f007c00 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 66769121 1250 66767871 66767879
    0x20d0206040e18030a0918020409020c0703060b041b0305090c09090312011a1b0f011b020c090105310213060f0e0d0b0718060f020106170a060504021504 67
    0x40d202ca54043c0b1050400c07400e88890162109450303006004912000031980c2d00200440540c407821044209000400189011381d41c1c52880e00b2039101e1024280700303800203402041071041521801018030003d840a00070003001411042d226040c04c400a81415600c001061400c5400c0000f04044a0003802e1800107007440300249580e600002201c0071207050020010030320380a400710150074040c0328080c08c0d042424100b059002080c0b000044500c51041e4850805011424055100c20301810074454142c41c0f10f41c070000b410b0850041c550380c040c050381c0e0b004205c00d496240b00390388000c80c03120440b45214401c0c454604050480491070b060b160000c51f0030718461000c158980d040b9103060725201c00401c0b00a40030b0b10251407500525a110244001d2403011454211050358000c0c2c01c0c0c6401c040104c101020401c890243c1d8100d00d0020748560f22503a4110b4091240d03170090042164607035032582025010301d586220b00b01000346019290300c00f103821520b031069050501c000c81c0d0140c0d0744840e25 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 66770371 1250 66769121 66769139
    0x30d0801140301060503030403060504050a06090c0306050711060106110a0803040c14010c11060304030e060a0c05060601180504020702030114090102030601030507080402101d0d0b060a081216020d020604 89
    0x828080c0e08100c0281001c00701180c60144101411a130001d0081c3d07041a140d92180e07801408000c5c402d403024011101e8810025000d4400d9807212803191400300ca44900718140003045803401000e02c414061404007560326507000150090440300989010580d42e8a02002e2608000b2400801001120044140000c1040c0c010401c0e003541c0311207842d036003404010401120b1451216402070501c9081c030890f11200c0c1400340065510500038180040c01c18081c0000c9030059020107a00c500084d000c045034410004c080c80780e0798100400340380050b406071407201c5425003860207200d0b41d0f00c503560025003041151020b4020300403440d49001c4211291800340351880c040e5004440c0f550010340b4200c0028081801030700c4442c040e0f600030302000141040400242d0f030201001c4000800394104803840760041d80c0740e150603c82c90b0b00c21184003085061080a11802c80a550000340042d0402d0582c828801121380a4610588278034629440c04080da001040328640f00b1040690040300024010a40c1d40d9 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 66771621 1250 66770371 66770387
    0xf01020d09060b090609040303180206030a0b040506040e120d0609181226100e0a0c0305012c0a0905030d0c1b111003021303050607080109060608010b0a0c02030d 71
    0x701402061029050f0041080840c003011542154048108004034010a10a038032050580750796000e4601202425000a0a2600200c6282c04c0e02d0b1f480780380c00c003643e0600d070180c690051002d407400c1c4403550009500c0c0d911058000d1101086010101e00d0a0207140d42e1381142004140d01030041141000f04104e00789200e850a50030b40d1040c1c06540000d0849204890203003020300f0501d06120783c2229090600001000030f040007040c9102ca4101080a860a065042c0185070110001038226041e0002a00b40c0303405910000c51b2242c0003603800c040075100300702d49003030038008080c00d201982d80c0410b100c01000c8091000e8094071010950130000300781039203c2051032400d41c07030300500c000504c94609010031345540d0040004003500315079881030502172514210b410381e50401602702107a61070000e900c80003d600030b0340c441e03100000b132040c0ca540241c00e5074090040803400307000090506034050401041803103420307050a000185649014407540c03411702c20030703030003026642d48100c840c1000388582 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 66772871 1250 66771621 66771623
    0x11010f0905091e0f0906220c061d060909060108041a040309090605100c030f020106120501090c0501050a0e01140c1507021006080a0b06010302040503030d061a040503060f06030f01020d09 82
    0xf42415011400c0c1184400c512441008540c004061a6440c40d5076850100c4102241301a2414849562000070385540380c4500941042d0391280e86010440d07218034204400f9656250040f08104a02e1400f510b841601c2a40040b00f070a2062142d100c920b0445c0d16102801c2d04400000050001c0c0810113500440ca074003141c9003890140301d9141c5a0b410000310003072640c0035401040314030b0012800240102180054a0310718000003402c2da6899054030f84d00e00c90400100e0300381c0d540e00240300c00c00c00d11070b0308400946000e00c0c02e98100b10302c1c1a401b815452180355454180042000c62a94001c0311108072400c10400384c0070f0f141503200494030308022100075180040540a41c0d452410154101d106203070031180910001c026100c40313034459052041000d040d0301d04154080001040b0f80d00c0070002041c1c0d00301203090020702c886c035207031780703c640036041a00001300104200010050741c0d40020300c1030b80040c1c048a030049992078140002c1d1030040c4980281c02c2d41c0d4000328180d0f100c0141a400180e6039 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 66774121 1250 66772871 66772921
    0x50d0302180a0e07030e1906060509090703020d0f05010b1806090702030f0a0e120f030301060206060406051815040c031e0e0304060f09030803010902091c11010f090509 74
    0x380c500c070000c0002c000800c0c011262001d034280e0015540a1194004007440080e1405075120f01a1404042c1025441c5880c15500d80f61034001c1040141004015150710500380e201030121103003960f0010311110f05602d80504030010000840e0140042176001b5030110302c0c02004d10b61480540c41032040151400c54404c0d10415010700000d5001d4004001c880c56a00313800c20091a082d044141911a8614401d21030b41000204284640d19441000300f00c03040307580c0100450b129031404400a01d000001400301c6d000fa0300b4144200655104d84034002c800000907151301289076503007501180008407440e4007036406410081241d0100d83c040d8040c0303000203209080301540c080a905608180e941020031a411035000b04800c12045204490821035940c2d10704c1c10944542d40c039103540f00c071f58000382c02007100d1590020701c1c0d004518000446008403500c0d0091441d50900c07031748401f07120032141590981800121310310800324521855068002c0c06008003041114100301507020400030400d0800741300 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 66775371 1250 66774121 66774157
    0xf0a0804110f060306100219080403140f0a0f030302070f0b01090e010b0f0904050f01090813060f171005030609010903020f0a170d020f03070804030e1008060913050d0302 75
    0x2605002c2100005800090700007451030b1144c90500207003000f0601c00008500888626243c43d5a078809403207800c82c010402c1c551224154101229042034110b040e4015034002c2000301150701c0c1c04524914000c2e0807043c007124450403803c040e000382c031903217400078001c0302820fa40c6010085e0018606040e50b5258030100110b8030845012402c860100480701c1c0d01c0036403104d100f9010700d882c8500d194000c1c1700703000b610b103d20075040070b039400d455212104030743d103c4010522403018621008080010320a5181a20348103000b0b940c00b8101120fa04051042c01a5000c0040c0c0d415480c5a40705004000103000c490040c0340043d9643c0c000d0051180480040c0a801c01c0380703150807000511076044540080540b00c099401d1b00d0400d02c0e41c0d000006102c0d4041c4c0a0000d440240c880e817010b188510300e0340e100c030b0140e840d10f403400510700303d1000f5800d8405c000c8450031403540c0b5400100560300c682e042d161019140c40b2844114160410f540300142644031b400782500ba4294940c01400695900c0044005 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 66776621 1250 66775371 66775403
    0xc11030a050717030403020906090711030703050307030c05030123010306080d030207050c0603060a0605250308070e030102030c090402070c05030109080a11010605150a090e0705070c1406030103170f0a0804 90
    0x1131a44181d110295220102a0102d003a070300c0e002000039000852800e000c1c0340a000d01d40e2840c00c40c3c0040b48203402151001c0300300501d00ea0140130384110242540303440d40c6550b06104110066420050f248000e6182c4420701c402a0f0340a0b900c00300c0039082c80c1049510b85008100018040d62003140e04842e10b004003484000203003800030699008240050500071640d0800008403060703000000707800461100400d8440a00300b241a00c2d40b0514000d135200051441d1001e00030300300c47d02d1a0040c0d4000d030b00c1081040191031100b030503212445421100940e58288070b042002210b21290096541546421034800400040100828421502da102e1320400c1111b140c2203403c840f03141c0b0840b500001e4003d50300e21345564032401084110058106403c03010b45480302e5051801049400a000c83c100042100030710048440b038800421101c411421801105800b103803a034041884001d08801c8002e18041e607000c000b10954240103110300c011521510000e000401b0000287c40c2690152010b400c250 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 66777871 1250 66776621 66776623
    0x3090f02120d12021809040c2105150f0105010e0102030d060905071211070f0f0b01080601050f041b0f1e02030415020d0c08090604080106141c050604030c11030a050717 74
    0x155114408070214145107000c07000b0700240d00e50042040303505019561001c40c000000509d0b2450300750707442041106400107450900e01c2d0039141680380c4040d5a100d410000d210042c3d4082c103056800a20348504000301c0c2d0030040c2d1840c010030030314101d00380c01d207407001c901c4029540c0924403074082503481d10604002210701c2c008130342c400854006c0050f01041110003040310713100b090310428410480e510b101d02d20741c0c5544950302000e070001812604a074004008518004031428030b0071074102d0b0300b000103120010001d41c01a0440d0302110034010030605810706680a89010250400000c0c030303804071003604000007500c0c1d520a004091180c606480c190380d040c1e100188600144045895246c00103083d130300ca44050750400c81140d41d1181c010400403030414001e0250200801c40b8000218030258100b013000800002c0001d1504101d806040000114100148640d04940c142c24904000607480c1403940c401c400381d43c210342c5c1521030445070380108130002034654200e0b14091031040e540103210040b9 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 66779121 1250 66777871 66777877
    0x4110f042c01140c07060506060c0307031223060f03011512050d050f1204060b1002010b040501080309010503190221040c0f0b0403021504050405071205130b040303090f02120d1202 79
    0x690400c4d001802103400181403a0701c41c0d90070500040546040c855070440c4185140d019120403000140410320b88502c404050068068202d545400c140f1400c1e114800c0f100b10550007405548543c61040305c03010a40c0302903008090194142e100311610f251120303407880f02606480c0007103405229460390548043e100700156540f9440300800140ba004182e080308d890a54042d0056401e950b80e1450110907a07207032a920081c92215800100703040741c0490400040340c2050380308824a406c2002111003e80c2d10004807940210506c0e0004020001071104100a005a10040e800d540e242490325044190650419108511906859801c2d9860301201c007000c0c01d60303200f040e134440d82c240014001072904c1d241c207120041c10b05401d6400d20323541e074000505481007540e1010118401005002c0ca922040c065070b0391140c800b04003d140a0710690342c1001c25071006201800300343d40c03014030008000b18400c42c41c001e1900101800d540c5d40d04010000c0d21501c000a09501241c0c00a0600c040140c040c020703 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 66780371 1250 66779121 66779131
    0x9030304200904030305070e040e0114011d01060804060f05010608160306230d061103070f0903020a090515030601061101060e04050a0303050c0c070f0504050f04110f042c0114 77
    0x11400543c40d02c2e5402c3c0c014010151440742488821040c00c1c4c5151924490300b00301110480010a1040300001d03103030202ea106822400c4841d08040c20041e00301c1280303245c00e045500b245881c01540d5520304000d00107000003040c5940e02c0f410400001072466005440d28000c0441c02c01c600e4102c840950280c04440e05881a83d400c054601124605030742028840003020038040c2245404030785580c0da08088441103400c2c1c0154000100a003c4400d45c802c0050808501c0d906100b80f00743d0558000a003420380a11402c081d1f030b500c0c0c0000a801d10000003c103a9614409002c030742040d40c43e450003802c04080c1d1940b0600700d41c604040040c00b058940c030701c03601544d0808064900c205040d282140a04001001070054500800c0340030403000341002104002e05960380042c88483c10a1b04110580703e010703000140c8881110240300100e100813141400c4210200d41d14609510180f001c140074042d0084040c541c002d200307404010f003204901c0b840c0c248003a607100030415007128110083d0b030078070245c0e5 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 66781621 1250 66780371 66780379
    0x30b0901270f0e011b020705031f020306040b040212040308060301150b09060c0a0b06090c0405130b03070b040e160507050a030e01031d1606020606010c0201030b0d0602030903030420 80
    0x41c49401561564401840c01e001003a0100e0f807659810b00160a481180c0044140015103000341a0295410300410000e07100c101c0240903081702c8403190f046802d031028503401d0034660000200745955105d41c00313035900b41c2d0040c0c000c0d0344503141d040c0d940c60b090b04110780640100c0da0b008000340380d9241c1840750110a4011015a42c1e00c9820710f000e8541903000724419075040348042080e03103030002003040418001807080c8428070a6150075400d0140d0b101014010720304422041c00b00b40f080c2d6941062144c038011103180000f404501d00000285013429a520201e031039a030001e000b02d8030f801003150092080c180030031301c0502900c284000b16054440e05501a100d50402000200080d20500903101c1e681030525011501c40c80b5100c440c1904441220001c9040e8080c201400e02c4c0e507803051a080080440e4006480c0c1480e01400281c4070700344208001707041550b0381c0c1c0e4601d401d50b265030700e04100540146c0c045460b032505400300c030794940c81905d068820142000441d60070501d0003901e0345034240d02030 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 66782871 1250 66781621 66781679
    0x6020c15090a0e010b071b1d04031716020c03070e060607080f0a0e030d0305091f060e07020a020102060a1104140d020d0303020306040b03060624040b040303030b0901 73
    0x26410004903040190056406500d002e000503a4020b4215450701a0003e55502c0355070ba150380c44e228103840004150301320071100901c0100a40e0f210965507401d1180b21020b080d00039078803407508880d0421500f481c1041c0c14160401d0155000945145c802d0041c2daa800f1203a1341c651103010540c8d21491403190103640020200001c8490400e00c2c080c000652044440b6414413a40320143c05441d041900b41200144449141407900d00c0c040010203840e01850030b081100d81000c07a103290300c4c0c2c200600b22000340002c115016803080740d55408007006042c541402403090a08810080d101c0141403000d0b4014841c070320105e920030303415115048521140d041803510b02441c0141410b8030400d41820560b020318100041000b68441584202116103c0c2d40c0040e0f0b6440d00e001000112003001079040e010f540544104103162702c440c1e4041c01a200f07060615656400301c1c040302945803085400400c035007035010400004054140e0040e80c1a00320484208200d40c1c6c0314105020382d24002070003480036038085 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 66784121 1250 66782871 66782899
    0x12114010521031603140708031005040c0c0204050705070f120f09080a0f06090203100f05130b0408070f0807080c070b07080d09110a0e010503010501151205060a0e040b0a0606020c 79
    0x3d00712008000c1c1c0705c0d08101d080e4001011119400d90090003066a102d600001000000d0075a242582e01400003241c0030080410b4074140140384943c80400240242d5440c004a4140b41c01401925030a0740d020300011a45090b51501208911314607002d070000c611040100c1c40d10034001c4400c0016125480001c003600b5000d44c031408801d440c1d010041d603003d66103424480240e1004c2c09040c01c604c01c602404183c4800317100c7d00000311178006180d5128100300079070480024828002040d000350700140741c19103504503402c012200c4410341800520725040002c0700001c1200402c0034049809100f001e48094075038840c0400c00a00c6a00e0004103124400c0180c1800c018265001010b494020301c80c0707403a903030b01d0341010801100c065007241c2810495080100814602402040e014000b18540c1d0340284084c040f000d001102d40702d0708420450389490005004e6100c1c1c031b00201c0205003c004504031401e2a0230421803d440640e40001a28200500401d0f0240002460b68510340003500140c400003d07 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 66785371 1250 66784121 66784147
    0x306160c0308100b0313030908060709030b1503030c060f0f010308070303020d0b03011d01051303080105120a02031207120e010203040b0c03090d051f14040201211401052103 76
    0x140028142010898042054200b0304c018510400b80750300c181444e82c14030305000d01396919540c0002010741c80242040b40d110350000300c030300072a50312040d00403085e110080741d106d1800c601c0745129094840070520300e1812000240490040000c100c0d9085a5150325103041a01d103407d000180410400f0403508001034480c0d40201280c03851720800241480f000c000003403e503000300c251161400040310001441210138407070503800c003c0b400141324441d0f0305c076580a801c4940c1480740740d00c10030354041c9170040e001090020040155000302501c20310600d03060145129041040c080d252004004000d802c030754010344240448020580065085ca460154a00281d038080c41015605000c18402d0401c0b03515940e5641035500e03c540007a0240c000b091503410081c20125912981e52814141002200c05868815a40042c0c0a10340411101c010344808440144107484150b400746c6004198100b50750300407070103410794804a40018103251940c4043c00f1601010390480c145810400900210001d = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 66786621 1250 66785371 66785387
    0x60810140603060303070b04110109061718160603061d0402010804020910050303031e0c03160f030207021c06060801020c060f090f0a05010e0d030e0604110a0f060c020306160c03 78
    0xc002011a442d01100750381f0481c8080003580c003180c072031088c0682c40515680051010000d4070141c60000d0b142c0f401500141800c1c3e0025100020b411305124001d010f491084c804101420500d500222440da0b030746e14000c005180c244039500110030711890101e01e400049088500554059440000585440e020001c09040283c0a103002165003030001403d0b4600b4005548540e17210710f21210070080424000c08545c100404900d110343c801c00800a1028024940321003919040c81d0120042c1e000690983c000d100f50340020307500690401160201a445c101d00d0806144560002c1c0320359541c41807034a09030300036280e0081c5283c000800081f1500c12a40700c1c40c2d84a1860b034102c99080b200d0a0700241019203800d815103041e5103400c44100ca1000c100404101c640140ca410000b103042c100010f43c440c0409007000305615490b0300540d0b5190340e50403104003e030040d100343d00c0320159036200152a2842c01c2008034080e000d000000765000c1d00c803190300624201203842e0600b0501441e541115513513 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 66787871 1250 66786621 66786631
    0x50102060f0603160605030f01060306080706050c0c0409080705010f200702030304030209070503010f0812040605091302040b18040e120a0309050a030905011205010312031a030303040507060810140603 88
    0x41314000c1e0754882c2c0071140c040000201a252600b076600d060400041034811016003255013810304152080101c13a00000b806811a6190304c6c2854542ca10010014281501403034000d600505005410742404040b0004186c3c0380d100d900208441c0b0811540c3c0c40942d10110014600c03a003d0845007040f004e1501c0040c444c05100030705070ba1901c0c0c0c4941c0010389030b80381541c54000080c0084014840d18141000da240904449001495030208080e000c1c902403145014000421102044141080d00e07151100b07000c03104459002c0d500d440e04c48010341e2198116a501580c03250740c0242c0300d003840c1080e03c1003c911240c884003030b1800340c0b140500200183d0203130021404043d6a00c80a0300802c1c8248a2007840074801c0c0e0b542c50405117400700042204604500100446160000400010341c00700c8141e00910114140819031802d0381100e079002081a072481900350000208100401c4000704203031059600d6074980800c1c82d140c0b01c05070900d1600f540030700a040c65580c1001c20062901d80c015640c42 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 66789121 1250 66787871 66787873
    0x3050903120c070f12082104150b06070f0303110d0216030801150c120504031407150207230a08100e1027050304030c060503060301060906050102060f0603 68
    0x44101180881c0ca001110440c09560321008240008158002d01107030006241072101d012540e030401c14640651604000000d044d01b0000400440b103051054821241000c0c0340d0800420b4540ba0070401180c50a50b080380318450302d0b0032159051841c1c00003e0720307800c03900505031003684041503406a00030b00f0200c0005144038000d1094800d80180c0340001c00c42503500e16a00004002c4a140203007003200c0c1178001c1c0d603243c8488074402c080c0a41c00700c068500d0503080b0341201780701031030460103880910030364001078400381200c08020501000001c4800440f400d094140c1c003138100d003040c02c0742c540e40c480c02400750b60b0740a00b0442c60b00281542440421b420700400101e1030590354042d180c6084c081d8261820556212505a007010b1070512501a41000300c0005010006500090303100e00c01e2024040c5103216600000070060143c20000c1c2c40186502480391402c542e00d071400584190003c47e039203403103903003005008542c11302c00d401108110b45040c0c00a1145840309200d210301c2c080c0c002c14040d09 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 66790371 1250 66789121 66789127
    0x20a080d0504031704050706181d041412090a14090103030e040209041427070302040e01090f050609060601050f03010501051e0a0c060b18041e020910050907020d0f05070305 76
    0x4104d0051105805240b048009040310b40c9041c2c005416040b07000b090707064010514500700140c200c40c841000c20310400500c0640039070f0325440c100001044210015071039115071045107603001e041800030101c10000302c5910041907900d010701d100c04030754440c010303800c00110030041001a00612644840101c01000036041654450104044805c0c204004040301404c1e01070003c1d8107091008031010301212075050410810320a5110368070f464500c0300038010750741c40c0c21940560200f91b02c80c6801c1c0781c1c0001901c01c42c410f68180165201004e40340304102c1d004041c0800e04940c02031003100d94080354003a001f41580e00e801c0040d200e0780c1100c40240b046544100b603000c101c2c1060002080004003035100c104410866080800c100d603807a002203401050002e000c1c0c942440c001780c0071a449603208242558400703d114800300074210b0b4400c025041a1440d0510100752058a01d1405952050700c06416654031240102d9441e60446082800318444000b141d07002c80c810801400c0183c00703828698a = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 66791621 1250 66790371 66790397
    0x301051c1115070b0601030c020d05091507060c09150e0d050f010c090f06030207110607080c07140909030a0804080d090c0b0a02010b0a0803040504020d090b0a051501020a080d050403 80
    0xc8040c1c0407455503180b10368001012000c2001e011009908203000f032808015130119804080c0d031b03c041c0c004000342844800b1a040350a0b6455200301c0c3c03410300c4100221a1102d40c140b5000c0050420b104448000c074074007000118a9021440958013609070b640d41c0c5142010320403013400171044c0d10b003a040d902030003a14441500c2c40d10074061500025943d07a00c0c0e00001e0310700003255400d55000e41002c020140108005004552088100c0c0816041201c0c2e039a551021894014118890320915540d40d0180c04400540889030740d003281d200340001c2d5148003d82d40e524a01c942c6a00c01c0400f00004100680003290103c1c640300e010381500340c000b901c0000c510b165901c60400e07100b016441306502081c0003d030f81c501180d081c01800030302c1c1401d940e000e003030900740307007895460703004500942d40074070b07400300d02c804282000ba000342c401d25400104426050418410050107090304072843cbc000c9107099101501107500c0090072450702ea801418407810017240e500c0c0c03e4040e02025105900b04140583d02003 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 66792871 1250 66791621 66791629
    0x130311010c0b0412020f0d090b090301060513020703080105090c1902030d06080a1a16080a090602030717060a050f010804020a1e0806100f050d022409030c060301051c11 74
    0x94040e0f4000c6130309082c006800300000745061a4550000380e960401d4040d0b0601c203400c0a812400c0e514841045038444140034003090040900b68030003980000345202d0307803007058425401048054002d56a00d9890303030b2188240141107500b5681310600450070412007030001d150407a060301303030300305441a40d2911030800b841030f064400a8101c8103954020000070001c0240c1003c1035940c4a40c2d00e001118a0710f0f000b0b14000643d5411a4004180045800003c2c1c402000d40d0000050691103c801c540b203042102c4018456086054102480b00442c404650241351050403401101d800400c107010b0001d2540044a1001d0090812a0400d0902e5004140c06100240d00354008500d0300d8034062462610f04400d01c0c00d80d000e48019100105604280040c1e5203264120003038480aa8050140c441e05101292042d0224043c2240308401d00e0b44d81038070400000c00501400c1d500710100c1d544021940200302c141e20080c4070b15a8025840c1a514036001d85019254419500600c070000c4a410814046 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 66794121 1250 66792871 66792893
    0x306050108010204080f120301060c03050f04032f0312130302060304051c090819080705060a0c02010b010219060b031002030703020d0e0105040c1716030f0605010605130311010c 78
    0x50442e500030a00780000c000401148040a80d00d800804004640d090300402c2848180107045c10480d10200784030905026600300c03101d0301a42804550389030340d24103000b00800118000720382d4096140b060003500c004030b0b61000c00114401400303006103180420542c5030700d03449004940c50003805008000b003d030340c0715070241d88114001c8024101d9035000c1403420038260000c09001d401c1c840900c10501064000051444003122941d050340100350103420002c940e4003550400615600ca01c0f01040301c00074a580054181800d81e80080c414541c91000681e10390044092aa118010441030f180214ce2039401c114076136400075040d1103011110b03011100a90b802200e400020a4001541100d075035200d00c0340c840c0d88200e0100800c140c1c10581d031441903420140c89000000548091201c280b64801d1203c1c4820b0110141640c070b96669038901014244600e020543d00c07117281c0000050014040c1d01120030644484052040803030860b5118100e49000c903230303c0c07410032514010403800035400100d0 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 66795371 1250 66794121 66794129
    0x608010504020103051003050307020609061c09030906140d05130507030f021305060d020909070819020306070905060d0e010f0c03020d0c03020a0c0b0402030c060f030f0601080606091903060501 85
    0x12800c1e1905000240903035002611000092000b0302081021510100c00e460140364101d404c1d50707903a103044c40010030a0041c00b0054841ca11000c4402d843c0020a61158404520a0b06caa84c1c1055540d034080d507081c0007640d001507050030104421000360000707500081d40002841d94001c1802c095499080c1b070609150030032200c0000f09034080066241c0507100d807428445840083c80185408000301d488074200c07000003400780c0c860001041385a981807140308090807008084400e0f102025542242c1a4100c00040e4000d00510340481da19604c02d070000425903102520851400c2e4450354840c0091000c1c2d07042890956880c44540102841030154104840c0719607005600c64401d000781a04950040030000c00b07040c0704020250031150022000c80080b03803c171030445c445560310b00100c1d0a0101c0300700740660140b800030307150040c0c500c000065400384420034140e000030f03900c00c5d00540c1d110100359485540000d0906c8200b62901d4900f1524031424152804e4400d400d90780e60300d00f000d4030401c0e00 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 66796621 1250 66795371 66795373
    0x303050406020f0304050d030f110f0d11010c08070f17070e031c1b020a15020f15090606120c040c030608011a09150a1508060103060b19050c0708010608 67
    0x5040041c60b0b410464001c04040f0030700614030b824078200000303003840940030340101480003044180700401d0190180090f00300d10f09050325220300020003825141c40100c174904000c14032032068070703810f6038051041005129140d114640b550b110080705079000120740103140c0410041c1c42800303902803604115a402074500c0d8a400600040102c2098180343d90740c43c945019514075a00e00540f80d900a0b644c14004425a281501a51550011584040c200d401502400559400c809901580000d84402840080050340c0301c13032114030f02c04400c0c402c0c00d4603810042e5210303202040c800c0c503000000d04101c0701c18804a801e580c50440100d4107030340a920343c4001080c5e136040e0410000d10203000b40c0000300382165680b4040011040064140103016051060582c2d00305c1c00641e50f030b180d41744004094004442c0c1112500c88552000b06008011902d403400282002c1300003520100d21810782d00304030381c1100885105145032408a0f80c50300700540b040650b02c221407001400351b2003031003500c019000da14 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 66797871 1250 66796621 66796627
    0xb18120403061d06150402030a020c0a05030306010e0d080a0f030605030d0c05010e1504080703050f0423040c360906080106050d0201020339010c0f1407140f07030305 73
    0x440c41081040f1000481c02c50380c02071000c000e1007409010b5400c051002c00c807001612130320707105280e400a0049040f4100c01e84507110b840d805100000000d1032213401c0982c1c0700004111120180f000018400740c000b0010142400341c546414050480000d0300306c00341c500001e00c0c0d69983d002070328081c1d01040c0304011441c0b400070f4000703004e000e0084110240014008000c00f40c10044401200c010091014110040210310541054858000c440a0b45811482252525140e154500300c1c05202c03075405218a603184d408850608250042c414141d07c141c6402642c154004010b0b0380540d5840c0c5c20310058954008034004d600c41d2506420043c0c48801030020301141050021403c451441d00218400d02c1d2882880340143c1c0d00004a81029032a61407448460b00f0040e1168040c1307048604c0f084003000e4202c1680e044072415070102c21600744a0703440c50302a1240c00c1e0155800501d242000c0684641044140003060030141000b02880300307042111f481403d500c080c2030500c0d095405c2180051000 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 66799121 1250 66797871 66797891
    0xf0e0411071406061903110607060e0601091803050d020309010906050108010f150e0606131203050702030c09010b090409030504030503030a06231003050a021303050102130e040b1812040306 83
    0x208202c942c000000d030740030f400c21780400a6541d030003650b9210060007954101e901e001e06403203200c285c4030345a61008051100041603010f4070340303500c407d01510141d14a000720203420f402d00b040364091019056220b15107003da00d2100c20000c0c1d400101010000c2d0b488800d040001005441000d0007800000000140e03500c8090102e000e43e2407052000c010622210360a10128010f941059048001101e20703a543d44001c14694100030481d60008040031009aa10300502d50003c2c0100010b40c800c03400e45071600f11394800c0189202081c0598102c5400901c2080040d0034207600031256240242050780c1890365a42e1114a541c1c000c80c0c000a1894a0f01e5080041212002d40d40e80708a000c2c180389200300f09848040f034000d500701440034042503203a0300810f020030500d41c101c940968552280100d456164101207010f9030081303606180d040d50b00d604c0022984200e02d8a68040c3e079000d014800c00e903d42140d12602400030021800d882e0081c2d9580284101002006000540c450f0001054035108 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 66800371 1250 66799121 66799123
    0x309051203041503020c07080105161205100306020a020109050303040c03020a0803030c0702240a030509100204032f0901090501061b030f141b031b0106060f0e04110714 74
    0x31411200599105110a0221950180200b54441c1d114a401030b100d0b20300100303040c544000b50b44420881c1d440c0006004140c3e1040518100ea80b00d00d0715070260081c3c041c0d110408035942240c1035101d4840c6e6107414000554075400921481c03080b4400030880041e075480c2e6509691003641c0480700046c01e564100118180100c0380d00040c1700c0c80025500b1464000000c048a00c0703008002481204c4a005004020100d40c20b0074034410200c502c025110319080703501500a16003540c141c0c0f42e82c8240e102c503010039200c50080350144e0b40d00c2080e884c140164204103100a03801e0b40c6002d4848401c0f0100c011982c0c640500e418000c0c901d1107004078555240083c041c190403a40701d81500c22407403100114021a03000000780d07003911003501c1d20701d00a503014200f80d252402004032035462601e01d800e842c2205c450020140500c120406c10f2002042a42d089582c201ca02c50302c04c81e4046010002201f2140340280c9140321006405403000c0750020039015505003e902028046400b60f9151010042580c0 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 66801621 1250 66800371 66800389
    0xb0c0102041d130f06110a030902040506040605010e0904110d030c030e0a03031b03090305010213050a0e01032f030a0f0b150901090b0411120108120a050a0e1c030905 73
    0x8a014002c100e414040c0700f0100301400c5500140096820b000c0031001c00410340e020030360005010300201d4840b003000b180200a8104003070203920807403e20000c15001d18089c46901c04441c8142c48049074000c481041c065407110051064405805441d81c0c06c240380c5410112030b1185110341d480c5c00100440d89070103460f06411280050244000d610240b000a411460418000b1510902450803071800e00d0112101082500010402c0d400404c0e031802d840c0700039404009542c002c40314110304503100d040385001c4500900c030280c1080b030a42a08024255030034010803610350806020b041c07102c601c0002c246000080c0c0011100e800c10001a84c0c02e20880c2821aa00705091404803400f10381c0200000f1201c50060240b40c03031455851100718019500e03603214405e81c82212249985070200d60040051349002413040120310701900c01585c0701c0500d17020032500756100a8030ba040c1008003c0408650303030b04420700c465800c0542e0050310701c040b0b034240030380890315446503030344040342800d040901c45292 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 66802871 1250 66801621 66801659
    0x30609030906030121020d0804050a0602031804020307090f06020a03030506040b0d03031806110301080d05070f03140d0e0c030705030109030e0d080f03090c0f06030106020c010c05070b0c010204 85
    0x90001d200e518116078644040b00d044407020401d44500100c00070144402a541c624001e6100c1c4130802110200a41030002c4c000300c400450744020650b58034101a0f03140e100700440180c085004400c21042c0346025405944c11104074a4a500c07426103a40c4402c882010540190000d41e118641e600101581800340f070307601100585003484200782d0180030030650200f910000b8181a1070741e103c600312035403c8003002c1840d0b4028005121041e54000d03000d00313a500a0051440e58010741c1580e00e20180070b082220b02c41070b440350700781368440d81603101210306006180c400407d0050420800c0b14400550080d41e9109040741c024025600f1240c003098504126903024034000d90501c0800c10110790042108a405441950440034884007490800741620a44007108080032000c4280403c0c14400500e0f45038006054030900045290f9a04000a5020910942c401640a604a41003951240c460003204520800403211055114060091190000440209543e6001c90204401d0440700c0f4010303645 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 66804121 1250 66802871 66802873
    0x120a0b100e1801020c0118020301050c12010902030c041701020a030e07052d0d1b0509041205071a010909051204080309010c110a230f030715050c010911030609 70
    0x82071420009042101004001105401c041901042c0018081d011114001400e2000300120280110420018043ea000030b074007030340c6408001280c0f080603038200c6011034038010484030f0f1603107002c0081d0080d40c030051080c418400b00740400240040e05901c0d003156070752004005030301d0b85840e2000030202d44588200c400c0d640d1184104201035225060445541c80310b50003000840d509001800901c001210281d540051a0000740410300c41004660a0042000c0032030303c40300c030ba40e681085900c000c29203006d008091071000110180f0300030002000400c0c0705200c581d12a02071498030a508203800d0b4801800541c40c0c10030042001400e024032a00c450f04560094206070409070300c2070392401807032181c5040c4070341c1005020501c100d40303038556107404000b45450041500c035680c00c2c5020300c650700c925105140d43c210425a910341b009142c0c0b041d100140060000500d081031030380e80034010030008401e103c02080b124070000c6080c015400e0007406681c80801d014500800d040c0303400b030700034401d06007 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 66805371 1250 66804121 66804151
    0x5010513020112020a0201110c03040e0a05040317060d1a1e0c070611070501020301260109021f0c0602030903070b0606280909140103150b0f040e0705120a0b 69
    0x1030780c00102d43c24900760501401a110045440181d005140782095103064200c04203002c0e2106400000500aa0710520703a00509a00c3d800b10400030303a8000d8800802140c1c00019600b4804c011003440b03a40450000c02000e000ea465031a6403801405203c000c11440701100c0c00c004a20f54a0309080b115403103d05000142c03454060134018481c004c1850040505417200700c11500c4600e1002075074075171070301b14000319580d594402c949a0301524045010070220303e244002000910184294059503401500e40018001031126104000071011600341c24071200d4645200802c0503880603605c80e6103254002c640c2e508030345c14040103690300204040e00c00c00c070802c48242020b1616180c58900001180d2004405040a409580041ca5034112005a41c64001c40c1c8402c6203180340c686040301d000b50001044018048515401d641c1031205441d00310f212190b400d4401c1c02c3c1a4003110f100083c0905442d0800d032568000b40030078905440007055680802d04003002c0c401d10f9056507402c080c01490f5000 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 66806621 1250 66805371 66805373
    0x108070510031e0b011d090a090201030b030f0c0315160e0103020c1005090613080403030305040206070f050109030f03060b16060908040b0d0b240a090e010609030c140306010b1e0a030905010513 85
    0x1c0300d42e1004000604230380e00d49035070f03d046900a41200c00c210000a050f2039041e40300c081d085540c0c9004c001a10b110388101c0f202282d0325020841c6482c010290304038503102c0160055000c0d1404403403842d209040607820000522540d40034003501075100109440410356007080940381f40b40c010003400c810070748000c3c801500000fa0603801103c0489603d41400310f01c0390b171140002501c50054070030203040b81d607070029460100a019442800303014800c1d00d03145811b11403190220201c401c180526250b403074080107070041019040001420307035840b404e80032800040550312141c06800551000070340b64000f0800991684e103d0191408031142a10380c50b803040c0d0044010b0038154000d0382c4090f002e010000d410107010744901280b40103810f52010056465a5a0348000d00d403401c6440140c40003400040b001c11100714040d101000907500030014101c990034240907031b0705070380704007490750020000011580c002c04024024040402e00c50b140091a842281817450a455008200032044015000280 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 66807871 1250 66806621 66806629
    0x6090109170c04021c0c02010b03060604090f02152d0a050f0c0105070f020f030903071401051b01050118020a020703060b0a0b0d230108070510031e0b011d 68
    0x104035104042401e0219800d503160030300707107000e00010b142c1090002a89a920100c12181402114800f100803c40c00700c0b501822030890703004020559154004502151a907d41500801a01400750843c400c1d00162a8001860f4070300f4803008210b500b0002ca040c0d0000c200011382c1d825011108c3e000144016401c04410416201e81c21350320041c0300d004038903070030b01d03000c4441500c0600304180020003250801140260900f0b031180c5e0740d0b038010722640e104002c6443d40801514040c900c0039006110a5040c0003a00c59840c00300300300d980c1040740604c0080c280003031120401d2035078000e034800042c05504101108840790018201410600d0040241074091741e40014503404403034001c0340001d4942c0080000882c101019030094802340d40210390300621204c0c9034844074070161041d4403100c00a200012501c50700300b0903c603c28541d00f14440412450800307290303031250b20085181c0000d00d518140590401c0503980b814540b604d03a40c80f9060f08955820601800d500f120004000d441c0c00306000000d = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 66809121 1250 66807871 66807887
    0x80105030a2609030d020a0c0911040302090a02070506180607050307210e0a06140f04020901030f0303060302090f1b0c10091502160516050d0f0f240b060901 69
    0x4811000c242d5030052840b48552003a501039042c001c00303a800307000084000954075041e008041c0d80c071104100002440c540b00703110f445540d00e60941c80310305251a6408100301c40000400c2e01c2c0340303070b030302000100c00107213060148a1041d6100d0001420300740403002000c1c5040710040402003071100800901034010341240c0b85003005561100103540c2d5180300d20304e58000d00039541031418a449825415010860341f03400540c0505d200c1d044005017645c075020150307219402078a0103904001424014008180440c00e980d12a50007810085a03a587c2c80d0301080006a040390082c0c4492200b5007403045e0004854a803401c6098001801d5003015140c00c44551542c5040c407000c00f5007a9a00c0c1c0110030041812880d0b040d185442d94215110300300c030603400d00c007082c800724101c0e054000c072800070814240c40c01c820000c0c0c80c0d0151000b000320180350785031036101d10700701029504001c0c1d20b0342c1e100000c0c950000c0c4625012440c484032080c8980303c400801980c0000d08640d02c102800c3c081d030151660300143c1 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 66810371 1250 66809121 66809153
    0x80105150d09020307080f15090a0b0103020d080f0304120201050907030308070f020f01020c0105041202010204140603130203062401020c09041b0e070216060f0804060f060b12010501080105030a 85
    0x61140302e00e1001030716010b001c0c2d20203400740c00f81e4140b118074030b1800f1414883da001c034401c40d100590780d045001520b400d0075820090402203610014805802c01002c0100302610683e0040e14100c4601c0d4503818a4000300d80445000c6641d091442079180e0a019503a04a0001070040c45a01c0c15503038081e218180c01050b41041103000c2c401c541d601d91007040803690134148040215138954440c90407501811045a0070766031090440031100d0440e00c140308071022038043c948400081d960840c200031071903001074046072040615001d80e07400741c0d9007448128002d6549480408100640441a02c0803154800c4010706540080e2170346210340e02c40010950b0b1155114001010640307111241520103036042e0485841542030100300304c110f07500000c0c49012800207100103c0c40c0742e664241216290403008454000410040201e00040c929400c0603482c110303412800f00d20541c8443c092100c0c2e800624000011400d6500104400d5800000b90303401b52030250003405a050786a110801004045c0762 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 66811621 1250 66810371 66810397
    0x60a0902120a0216081917040309091806050709030b01170705040e2503030201050c031302041104081b101106040b0604060b03010801090605010519050904060902090f0708010515 78
    0x2010f44000344004c4880b00d100c0c1c2c0c00b5000c0c40e102e001da601c4880c180b107407800c04600460f80030040d003400440761a0b502485140d040c0e6a04c04c2250804440b0800f809070403e01d803040604180000c0c000940c5030107441c0c41210316903900403409185042c410620300f8180d02040021048070350f420b50b409004610001a910180d0b40410766080080040c3c2c40c0030681031400115242d100320031001c1c2a245c01034001182d010354004d104a40354209014010312065880c1520082400082401818280c1000c501400d490f4145400c0c00c1d694000c080c1800002941121003180c0c14440c4001c3e0318050000303010164081c94050209401034074855543c28015101030308501500d00000c406584903003003d4040c140c09a40140c495030b440113900c1c00b1300011003041340d009081000104d998240240c0c103a0341d08202200c03a0708074a00d05024859043d0000d0000d81c0c005407900481c41c096100c00210074000c02002a181030a0324110800400401c0c042e084203108600c140801462442c0c40c0003070380c0d41518044 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 66812871 1250 66811621 66811627
    0x902091503100b1207080901050126010e03162010110703020604030303020306040e0c0319030e030a030509011202070809130e0d0f0e03060108030d05070521060a0902120a02 76
    0x4000903080142030f8000005442e000601000812016049030300405580e01d0302c2d1107079180c0d81c904509854090284501071864407080032902040803211418421401000090800e11800c20900310f500102422401010000c8102d04000324810454502c080400207017120011a1000070446c601e030301d44540401441c000d4031440d0380422300c101801194001c100c01e580b04c1c1d6030314010b80a900111903080c426848d10701110502140441e09001143c1c0c01000707810340c20740241c900c43d00020415400c0c0c007000702a25101c3e040c0d0b10100b00007044203000c0d84a45407106002c20004140d1468181003140d024018084100054003034002e651701301000701c8040c0b40c04000003001600078020454180b06034468500d00c005950740100540c0301550860f0703114181082404281940c910f001e04c40c1054541c010084510300008070780c001f582200061070414904113800702006c6414840042c688a503180c040c1c02d20a20785083d00301e0800620613002c065051406141001c8401c0800400841d4255000 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 66814121 1250 66812871 66812881
    0xc0d02090a150c02010e030a030c02011d120307021207080c010f0e0907080603010f090b04060b0103061502010213060f0f0806010e0409060614090928081c05010902091503 75
    0x11070010740075045895246010501600e0001e01d140c0303580400340c3c041041c8484241040c20049150341e40550592100b1802480c02e60044891450b420702407540350144080c1d200041d51a02c40c0220000ca10000440e00c403100c900400c05002109041e0101d2603200490810110602050394600e10000342001ca610091244080d1007a0420420031640110315038108015035401141c443e025030002d600030802d05c000032141c0310403542c4000c4080d01c8410080d0004001580c03d8000685c6540d0624001c100c1a07030760701070f401c418005400c1c0c00d40545d40100380201c410f40d03040b41610041034140f401c104c42108090f00a0854bd10b441c84501c100035841001406a0f4001c05052820060107032003007000256909241e0003c02c01401415441200d41001c00f00034a00762140f60302410742640a0042c407860145402c1452286484071107205540d514401d001c14108001341031020383d080c469003410f0080300040802c5800503044031009d00d1050010310316549401d40c50850b8840b481c2c10365a40d039151 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 66815371 1250 66814121 66814129
    0xc0903120c03021204150e030303060607060902120f030a0f021203011e0e0c0a1103030103030503011509180203040203010506030703120f0507021f0207060302030c0a1409100305010602070e0c0d0209 87
    0x13800184002c040000b000100e8000e0708440a841d040b00d55112241070784100c0800d40c40c1e2009543c0b887d030082044c000140400c100ea400458464402044030b02c581140c0071545040c0780001e06c8440180d000400c015241c0d41d000400c04004007a503101816100c0082a2203035900d0006002e06020710740b00c502141ca0003004845100081c1080307506049145c038100b400202580e01655241b8002880f0440e140b5481e0b40000649068a0303150b10f0b040e0940e8244400320341d80201d022840000c000d1012000101010001810b14030403407185030140e5a888e05005250130354402502190003035004134800c01c0030800c49a400e40e99004140303000600c0240101c0c003224a40109900698018101075036451107844092114050300310b0b41d000d54581e191707075020503800c0307002c1211243c0c05d482003005001c6400b0b02c82c900e500c9081d0b0b00c0620385400c00300154045814001d038001062301103a0b40d24014056142c04002420041c0f0501034860f10301d103020080f40016001e200f00100c400c1c0d401041d907841e40d42d2 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 66816621 1250 66815371 66815383
    0x30e0c040510080f070e04080a050f0d15060f020606040507020106170601090507080714030a020f0c0607081323120f030a0605010c11090406022b0c0903120c0302 71
    0x80040061100d41031101c08020959418850000d4521861022030310040002c1051000c036800f403c0460600c0d5142d80324801558020495101004000c0110694001101001d42030380020400002410042440140e440c0021900b00c0030030b0101080c000d5610035070000d0001d501005c19900070a080d107850005901504180d0080402c5c100c03007040340c480d10031000540d0750485010f07160a01150321172b003205a94035a400d403550720004020240d49446442984000e5800006003d0014949001814840c40329006144400042e4018105000300e056002503095049a10703010180d00e043c490781e562250340b4440103500201c04851448012400c141170055070485003605541e1075999079240015a400e6204031503d0440c91311381000840c46522031540300d00a540e00541000d1226410b50400c407002ca401002110440e400700080c1c059110300300c2c00082960740303d0b10150380590408003c4020384410040e42401c02090503410001f00c0ca5007284055404550300b084101010f080c241281404 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 66817871 1250 66816621 66816643
    0x4020c03070b0a0f0b01050a1d0a060e040501231201111b060f0403140c0a080c010c08130b1602010209100c0209060a0602030f16020a0906061206030503030106030e 72
    0x20002040744414002580c007264852880340b4401c01034090b130103e10000b290080c88405001807405d0008004141c0030303681c02040074164040c4045982301e0040040c03110b01090300700400092084c40c007000703039013040d004a5008d4001c1c14801d00e4100c1401d40d0950101a44110440c4114188907848920403800c0d400510480b10b60131a40d980d400e40004075599003040945040707002d100300c00008a0401c0302ca69150f001f0743c0c3c5942d8504594001d0100c0d00644e07000314102c0300c580e000d0160b408000410040040200710f04240010500700729108016000f041c2c020a5010343c1c602c501c2e80d40001680c05102a0b0b0f0064041d50048032510200104a00a000e548425038200f544040900703a459000050382e22a2442214002d000b5074031203083c031161a403644039080140c0d006002d507498403031701c503c05848201400c40c42d2112409054000072600c60465011402070fa41e00e507000d1210301d0f4040c03050100c8400401c0c3c240150b900e10b543d059038900c01441071408055407041d40c40003505081c00103420705 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 66819121 1250 66817871 66817873
    0x4020304080309070b0c1c110706210b030a0209071803080403020405070203190e06070204050109020318070605030f060103020c15160e15070609140307030201060f2304020c 76
    0xa45840c0c54551000da00036541401d05220711400010f030402d0714411100281500409000c0c004046000b201c14070380285032610901481d485030300214001088424001c00540e42c400e403d285181c604e11040b0381c500c1c50b88079201d50030240054210b40b0001410741c20164150b80540c0540c5d034418044030f00c0f83c1d4007602100354812940b400400d000d41c0a0182c001e0307034000c50f01008607440304041640d60f4459002c9120700c964413840110910b50081d00c01d018401c00107410545014540e031b00103411140c3c00d07000101d04a502009024540c4081038444464400ca04000c0043c242400000761180c04000c109000407100040015100c2e4401d0301602d0b414403100e822101c1c00d1207074520350f43d0b0099085038942c442c0b101c3c115100d4003061066100c0d50280c0d0001e44640c00710920b0f2a10303920994040801030303030030036210f80010340003820380b861000031292507501031034485032603240c000d081d00d030f11350301c40c4025660b041c40c18000016404404e4500c090f851405501c041d4051012502a0141940103006 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 66820371 1250 66819121 66819127
    0x112407020f0d020102071106030105010c02040905010b040e0f0610030b0c090102070b04030b0915190e0a020604061e0503070f030c030b04051e0c07031413150f120621020604050402 79
    0x4415015005031821b240728610380d02440d0001d4060202134002440713000e0005510030002c0c0c01604095000551460013003002182c4d2011620219094621700b500e80c0f10545c8c441d01c55424080c10500c11140c024214401480c00340d886e40d1584d180104c40603240d410030000015203842168000c100002c01031004280142e200c95403401d00503181c0501302c2d103000b0700d030050103180c00b0401035952050748100ca406445c940000106200d0000420803c081807800344985440080560384090103000242003603a1007510509013140c0b609a5140020302401c103219083c804e000800d50081480200300e500c9241c0019020b640007012005801d41b00c40e0150042e10f001d040c040340007800c003c08407640d148144041c4858803407a031030300352500c1000d101130001007003606d003446962042c0f401414600ea22003450781d041ca45581054002c1c0311460022404104d489100000d00c54000b2021610000d45034001c22003245033280c41300c800c2d2241426052201040c0c03650400319500c0c02d00341d030040c1002030803c41d1 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 66821621 1250 66820371 66820393
    0x23060c0c01140a0f0b01082401020c0a0e060a0e040201020307020d08120a020408010e03040803070b04140706030f240605090112180218100b070c050d060c112407020f 73
    0x40103041240d0588130113818100300e1200765000c0c081440c0252401180d07005c10304040769000d100007401019150441c01a40c42c1250385582d03640010000d0013021065044a040120030800c035130a0b80e60004900d4100f000c01c010141c0c0e0040b080c0c900241e016103c0090040103490010304074800d1000c03240c6101e0100c801d0284401280c4d015100f5100ca260080110624a00003903035240075501c0380483c15072003004100c0000d0704060786543c006100b481480f1401c641944103500b801d601c0c1e0410b0000035605e03011080346c1c02142c0662044118030451048251505202080c038282d8980a540244040010030321202c0e4401c0b4018071142c403150100f00000129000301078a440c0603000c050b03220744000f103803800d10541c4000c0402d01401742e01c08100b2034a441d1001020035900044025036001800d81000181911802050200e00d4030440001554041845020f05001c11000700300312158007030828010f540c40c03242c41e00300b42070141d40c0072008a651801c90403884c240c541c880d1300002c0e00440425103 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 66822871 1250 66821621 66821641
    0x4050c030f0a0803010311192409030b070c03020c1809060108010c080f0403090902030405030a0909020a020304090207050102040807061806050f090f0411031323060c0c0114 76
    0x18480000300c0039651860030208800c0e039070b01506240074003808420001080024101c1d049140d000310060a80c004c400d1034940e1450b00154168080101403030740322140f80e0708036011650022624000c0c100341003820b0440d107480300f01c810001c0103882804842910310b02414000c011500c0c1748080140111401501e1100740c3e0206d200680b820611480381c000045078039a07040c02076119003289030384e03004541c1c2d880c1811145a980f0150013a410300c14042c2c400b04403441140020b5100d5406440103503915142c0c80700c000c00541450b4441e05c040351041c850301c00c4259000c02120101c071100100561201d03414244a0700900c0b882d40404400c1c4102407001800c2a0042101504103c2c101e1030510281d680740c00a4601d482480c04840404804102c0c04001d494404e158001400c1c0c00740001841c40314040c0c19641c50341c401c3d1031041200320319106e00000c21502e054a01c005803c12b403141c180d0241410746980d540c02001d05802c0071a03101240b0480c807007400354841484501c10144a07600350800c180c542e = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 66824121 1250 66822871 66822883
    0x40c0903201906090e040b070807050c0601141002011109040b06090409110108070201020903060c1c061707120b010e04050a08070b0f0a0b090105040c0306051207080d0c1106030a0f050405 82
    0x83c001041103044d00203080030440504502c201d4100e82c0031050b5641c2c0d20b60032a440a001080355040c00350501180006007070811089018200c0c038890040741c02500360421400c41118202181107a0500341d042c0b140e070070032109480184c00151004680101c1c00030015803140a00840f03103400614151405040c0030607050900240142a25120025103400804a080c0c0c03240022564069100001248c1c10200b9180140022a4802130a46c0902900c1c0070400076511560301080b00740303c1d0700489024030101408043c0007001d0040411040c20b08036543c121f03428405104402c00074010500150034014148100d520281d4044441c2381d0b59400e9143c0401c8602c81600c5002c043e01e19100007851074001c511800b101b00030300030055180c5a2801c2c003080041c0c001c0c1c03410b00040544400f000079190303c402050144003941100540482401e000003540381040c210b1340d040c01c105a0a05040225116a030400b085800a039585a078070ba8492080c032002c3c003601040b034900300f0b14040c10041441004556 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 66825371 1250 66824121 66824129
    0x10f0506190e0705161b0303020609030a1d060f0d05190203070509090705040906030308010302030d0207050a0911121305010605030607020c0d05150403120605040c09032019 76
    0xd998000785a4480d000001409010703030112000701c0c10110b15000e0180b000f900124410007410000c0f00501c1d50307611000d154602e89030a0146a003d0240105070701406034a5121003500000c5080c03d0307055900800e4034041003555003882d0700341c03904840300da11640126444c1181d0301034035030392f13071001c42003082d00402c01210a881c0b03003490100103000c01955402203d00598503541d465041484000420120f0b0740081e14a100f84078041000040222185c0581c00c000e6009490308040ca40c9180181801c200000200d8000c641020300103000c00e84d00c2251210541e211b0b02000180c1035030f400b00a107560b102d07002d8110341c1107290104101464130314a0040200e113105034000d2001d280d541d010305580d601c054a001025800003140c4014500701440c00714201c0e402441150007260141c142002804020344e0140c0001d4070074082446002c0540c0500c400404060382c00b081504c404480040000034240801009205440317400106022100c0205008000c000d00c0f0132500a00850140c469450b00d00c1 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 66826621 1250 66825371 66825379
    0x15040b18160618051f020c0603040201090e041b0e01170c0102030405190e040809100c0b130501021c0605010f031505150c060717060f0307060f030905010f0506 70
    0x40801041008651a00014070744a803500119050031029142107008040902c09819154000100d41d40d50380c1c4441e8041000400c1411a240d00f12402410b0003109400315004503420070503c401070364441884000c913110118400100d489074609820008400050000c822070b0190010a00c0f18030118170504131400c13005c960500d13001c0d0207000c1e600d0340b0144076400d003d60401d200c06c0010381407604207400700880076041c1c5001c103611201d00d8032103a00c090340c0c1650701c0072001ca400395850404485404030303240079050128074900d461f964084400c5004010703031102218102400c0c00c2210940507601440c3d4441b100f590b041c031074440b145004000a01c110340c0000c0751180711904160092040510007440d00b40740d0ba6580c0c0c00d04040c41440e42c40c005905030aa00100032802d03005006005660040286d5681d0360402c2100c007611b00302007034018003503030710401c10006503101e10341c0c0016040c0202d400c0e600b4461900072218000384d0042c400000c0190295082c2900d0b807006000c03940c401c6104500c111 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 66827871 1250 66826621 66826651
    0xa080702131b2601090209040213081506180a110405041a031b0a030602090d0b01031407050f060a0e04061a071e08070b04080f0705010b041a1c0515040b 67
    0x41c248142d00003c0c8240048194814018011070b1080d40080c080320401400c0903161480b01c9880c9010b40e40c0b203a111030400e0300300d40c00e03070500b81c1007075600e0030f400100c03c94080d4540005a1100146000d01070004d084c5036540c3d003241d54504202c44165401000010005c02c901413003c0407000901040342071035403080c001d55074443c0f0744200004039000e04600280c410203c0300d0940c2d640c1d0f802544a480e545502c405000d140c00c0002c0c07011011503003c3d41c4035450417000f001d16404040e00d005016000507200d041d100e80451841e840d000d0a0320070503105031030041108007201011500070301075500503c0401d804042034600e80c481a400501040e48260074a00d448442e003502c3c0d20300034084100081101c0c50402040c070101d115400040d800c45e00640c5180d26002d6502c04203005644100011a000c1e512038100c50801e2616100d00c003041040518070801c5681319000040817010314034032100301e001460b50130700c043c40307020056281380060500b024501c0b800d1500741458050b2048401e40c8001180c2 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 66829121 1250 66827871 66827897
    0x302010b060301080c0f0409050313030c060203043005010501060e0f1008010b0a0e030625170a1e090605040c06090501091403010f140603010b0a05030a080702131b 72
    0xd408483c100c0d00034502410b00000c20000b0040c0004610034141da10580352045800812000c0c0010001c05003e280c500e20160f1540c5000c4a0f400740c141c1c841c4065400520040044508508400249074802400410380d0701425400000e903414101014080398a0032001007442034002c00c40c030802074012103d001c0410340a408106101c1c03a2590740c8400526218010405a2102c201504003c802400c20054980b01500880d01c0c12404840042c210310b50364010f007a10000320318a02944d0616480c00c0c5428090b680e15804007404060541031906a403841218001c18040c40314a50180c0c940c0c4080c0722950382800d01a01034a01550140d07401d944240f400203040b4040d2250341c04492040c0c441103c024074014480c0180c40071901c110350195260302003003200c01d00610030044100041e4010781c100342030134400d05085801a200e014015112403d060046680010300720f88001c0d4046002075403201c55201083e0414441407000074558100070035200568a00e51400740110b030503607039100407040310b = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 66830371 1250 66829121 66829129
    0x3031b130b03090a05010c0e130506010206071b02040614090609040510270f151a150403020904050303010608070c0807020111030c1006090606090612150509070503040302010b 77
    0x5101980300040034005001c009002906000e03640c8420201c0644070095aa42c0303a0900303407100741c0310880006141c1d4442c0c044510300940c0c0210521140e140400c020310b441d100103950381d400648054248819a202000302c0f0f03074080c031164005a8003030018030149649200311006c4e02d1810710980d2103460941c00052a07400c014211500c125003180003020322a04000a42d00241500f841c0c0300d9504090b105d12440c1061409681c00029100e806142080046410018684003c0e680f002c4441800d1000c4c0c05520001d05803030115940b1b048400002c02c40c80c0100c40345043c03003641d20003900030007501c00f040705003e404002355040782c036a625140c41c641c2d58400111020540c4400003444600180142c9000d540300b401304403090003481c002c40345400c500b076a10601e013010078010425600d0300c4100c00d000c03201c00d074040c031070041036070f41001c00c1c205081c80e802400c42d0228072000c0304102c1c0d131550345814041040030514024080500317001814105010000e00d154030483c0c05030b0140d07007400454105824 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 66831621 1250 66830371 66830377
    0xc02031e0306060717130806070903060e0f010908210f01122d03020f03032806050a03080405010216080705010e01020a05030309010501030308070201150b0c150103030203031b 77
    0x854481520349448440030a00803608041c1225410443c140181c42c00580511000f40f151035592200da901c1d40d1800001d90801a015009241c15401c40828000c02903005610041035991000c000700340c0c40311040c085803525400b548001c050f503082030042401e006100000300900c288000c2070300f0200c05884c001d110b2801c002d5030440100400300c1c0041100140b9a0001e142243c03244603000703000c105451000e100804406103100303024030169115010142c040140040056403100a5419032410b03810304124aa0b249815490034289040911025000303a4465070140c0340062100c88041e4890a01120325002405094007503c550116842240314a000308401c495400d0f00900d900340c200801151964000c80300035040d88110800e440000358280003651240d480c2000005496240d03080041c04040043c002c401036924000401c410409010490019102455180340d0765411030840e103890041059280b6101c242d49a0000c01010742c00b100650040b101c0d060300c0e9001002d46001480144 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 66832871 1250 66831621 66831637
    0xc1e030903180102160f08010c0309020913330b0d020a050f04020409020403060f1121040f0b04060c080612150406021204080705010c0306030203190c081f0c0203 71
    0x780c42441100a040b068110301010b01c00184141c45242000c844179000c074000d641c1102d00320118141051082040910070000461280e01c0c080c0090240d40d004036011400c0500008071a0515042c80d00038013454500e00342d5040d1041100207811801100c0c500c0280b00000c030240300c00760500710341d03002d41d15006c445072444540003446840060719103c10007101004841410360002e07001c0c4400110f421107840600029801800041108503901d00c0d40000c0710398510314020f0b201014401043e105140302002480c0030b1801060a0321920b55062000882c001307200c0007096040d8180c2003204000c03294011041c0c01c0ca4603160740649850300400c1145280b03007080c51300525403050203c140741c60b5032103030019005400342c0001841c01e080e01502400001048605840e031400000b000c2d810041c003440303950702c00300346840c0c00c02c00700c1d086074006610340e890074002d072032800c0858800300309020040240c20000c129260407500304100c2044082665a0312001001d6500c0c0f40c021203400a43c00402220302c02 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 66834121 1250 66832871 66832873
    0x50d0c020102030a0818030a02010f0606050313060506010e04020a1e0f2a121e030207110d060b0402030a090309170d0503130b04150b0d0503030705090112050c1e0309 73
    0x400c0c450700417501d150000741603e440d0341130020740c1d0782601400d100805c1440000d60012900f849209145800c3d108130350701910030080104104074001a85030500c00034a5448203011429849140c012180803c0480c4483d910a200140402170607820017851444500710344501d09104010800a50b0104014070300d040125003415400851403042108405100444080700904c0441c15162149240c0a4521180c08154904c40ca2200d900c004058826600f038540b40c19480d0010540d40e0071010541040e0140c0500c802c000454200300040c1c21201c40100058411901d0303282041c00400a0b20720100d003907000c2006c901022664100c04007041b00d00b111500010300101048480c00c5403260b00043c403038840c0d402150010b4000a4590b20b004c0d0269000b103980e0540310b0a60124002150f05081050f0303c20031701e103480800018008019a940903801c1d06000c1d0700c031054a4010303140403018154000b0303202d16101c100529120020003a04d404003684071032040072659039442a11070322064a201210b = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 66835371 1250 66834121 66834127
    0x9030201050a0e03120a050c07080a03020d0c02010210090506150d0c060c020a090207080901260a11040503070308030906090d0801120218070c0201020c06160209060607050712050d0c02010203 84
    0x1010b01599083d04020310150803a0304152000281009a800030040d803000602d00142802102c50100500009010f1840160100342501d6030080d54519800800c1000e0002004100041d68002d0080c1495407002c0d15042c07003070303800524205466640c1116040d02d411081142401c450602030651040160f105101400c014103201065403810031700e240403607002d294880c000c40c002003d400030702a01c078030400a20781c4402c1214005810000b0515054000144030601a101100e4002d141d90b003201060b44e00241011a0240c4c1904902c202d40145800d481144000020000c266005502c41e24001b0241c1d10344d031f25080c25207a1140e4400d1101d00c002440400140a0012140000f14100388001c18403015511110001c070f050340301c1210544003140380101102c05650701404405040c0e01c040b24403529013042f4025840d00c4002048d00a07010380300c1040062441e8950303004485106800904681415030f0303504444074151800e1800300c1d0680680c400c2810000d025411400c03a00358160041d40c2 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 66836621 1250 66835371 66835387
    0x61202060d0b031507030c1110110d11031504060b03070e0d20090f1b0f0c0708030a030614150a0c020a0f0503060f070804030f030207060f090b06010903020105 70
    0x3600350429008000d0700c6507a0407480140f56801c20504c950b20489000681c5680342140024040369503424008092000e1200354403400400890104146111803070300240c0b0b180f00510002c841c3c001d0b04070406003140344c218200c4d00940c2e0000618855248042600d8a206501081c0320540b2a24451010310380410310100b00024091100c0300c401003005001040c8a000c15216107084900314000700c030468034003050b40c1c10581400c085442d032142c0400c64001440c100317003401082030007460b22002015007000c00c407640008401001c0b42d846061110441c0c0c001a01c5050140d100e6105c1d003140400b00c0c2c6081130014641d80c01813201041840c3c010030020081e1a803070034460040e800350032041f0070803071820070020040e516844001e02030482d55131070188850070241803518102003e0f0010814040610401c0101d9900c060003a50182c5c0c1890305041020351902d040e4040e020f410740c02069503081844202c1b0300040c6520508405004080e03140700340d1120001941d202c2541e010107030000d48200640e82c = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 66837871 1250 66836621 66836629
    0x302010f02030d06030609020906040b0f010f09080706080f150901030201030506060c10020301080d11120a12050c070312140c0310080105010306091a09030405040c350a061202 77
    0x34000d1501401034901e440d00c0d9102140032540d03590800c881da166108104402c1d410305400c00c80e8403020541d001c000e481805800100e600e80c40030483c40c100071624044c09002031240445100902400c002c5407103850721100003070143e80048840c19810a01c040c0040e8041c8020240781046450281440026900b50f030011009000c0007888160000000c20540c01c201e64100040003201300100310042c4c0365414a103403a0b0511004011090402071452001843c5c51004a5003400c1e004001000e20307914615040b00b030300e0410f215000310080510300000c11050000c0400141401c61080c1e981c0c601006089205d40c08440204010403512103020300080c00011a80e0015504082c0c0b484441c5041ca07640c06449007901e0098100712112901c6021580421803200c00750030f1143c0508086242c2407800c100f078103541c0d01031740c41000c1c82541c48405503400c00e030140b04180b00309144503501d0101044410290202c0b060b01c1d01c1601e0007a5035401c000303002a102da104020540d002d1031030404004455400308 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 66839121 1250 66837871 66837887
    0x30403051905040b190219051504060b090403020d180e0a05180a05010b0f040b090c0d150305060601020d020115050d050312270109020d0305032502070306060b07030504030201 77
    0x441072003001c210100b4002900806080c101058080d54a440f0071701c8600241802490071440e01c0c0780c0c80c01a504000100085100712144030240b07080502c80c0d50f58102400504a41e07203080390807008420074001410f5010880c2070040314551106426400703425002b20b640b010622410040400d035401141404c00303290442e5030401000d0510a0041641d0031806081032100c02d0f049420380c2d91103024900b01d08103203448940100003220f04001c02ca2022000c40c007070b004010f0510300c001c00001407101140400303034400d0700d000700300403e41c0d56050349030f1030703d140d50784400d42c3c1140c00340c8a41030242d01010710501803074002c40152000c10420510b40018000f1050b9541ca0848a901042c8141c0c0f2020381c41420b0f403032107016010306102ca440301201650f468102210f003142002c0c1d04002600d0003684964140c1e08115074103103015580c0c0d46d03610b182c2409150140070100d0100c190154041d500c1c2d82d0024400b01030303900402d8100a0a50303945c0000e1298411b03004010040f403820b010800256001c2e0140f = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 66840371 1250 66839121 66839167
    0x80105010c1403040b0405010327020d060e060a05011d01150e15160c0b03010608060d061d03030712140406110f040308040608010603140a0c1709060108010506030303040305 76
    0x5000a00480b52109a0458100e40c00c04480a00c01007410842503915000f504480443d00d11300120865136035084298000c4a0440070b8001c00b20120000d0401c200c550254299002c96001d80380f590501d60104400f401c401e100d0170790062410796016014070b0340e610f80c0074101e50413250105501000070100b964001c0c1140400759000031442c0c11180900d0440c0014154171034440795906002e0314514100200e616a50020b001c8004103100510030a41c002034000c1d0025401c556814080f9018a09403025108482074408103161036500e000200c0c60020141d4092502e6803611001d80c180480d41d142142c800540790020701c00344001103008910664003038a41c0582d0710101a10b010308602240f04140d110303900072202c007040018100041c6074030801c10b41c05000c941c9800d000444034154004a400380140195030b05c0d507602ca05a030106030023500d400348030b0100c0b208400007a24040306c42c0d64403290b00b489070300d4095081c240000d00030700d030110031680700b0b035495147c02e8142130b02c4c0d8611261901e50165 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 66841621 1250 66840371 66840383
    0x807050c062208040e010608010b0705060106030209130f06050a1a030a0b180405060108120412030f03020c010f0212090a02062d03090109030f0201060803040317090910030303110703080105010c 85
    0x41844080b0303c04800400284c40c140c240d4440ca945043c40040200c0e90503440701041d04000d00c10754000070001700d4003d04440840c80d000da107500038103000482170115031b41900b840d14a405511680d8012030307040082114011981a119155100140c0030010038080070003a003140100300140c0301404135441070b10402d0018105002c007454828280440303c2041d5020b80b07190303020000410150900f080408410022a031029040620340b2241600070058500003c0c2404400c016480c0346911036810f45001d000c2d1100244940c0d071041c0600f8009600048400002c07800c06400505503800000d031a0200942c0588018517000108010f804005510500503030450b42142141502c4481000514000c170309c180000100c0e801d0600d8081e1003442c0b070f650300400396410040104400d0002005880490f80c02c42c1214400c0304202c0b0720039140f84210154960b002c6044411f1003801c409030b14032403003968801e803010800e0301010907001009000752040100018101c0c0010710075075224102100080b88207138 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 66842871 1250 66841621 66841681
    0x100507030b300d0903060e0109020a030b0a0905101d0f031215040609141302010e060703031104060201021b0c24091002010b03191a091608060103030807050c06 70
    0x35180c03414100403c9060300000e00c1d0340c0c400d1041c0000392007131480c61a4007500802280500f41d01181c0b0148007448050305a17140d5200280c0340c8071940d0001a8030503408402d0390001c0d0108040a802085020590740424803d68400e000610002440f41d07140690704000350f042030407403402d106031070000501210052803040c503030481a484a000b07003c0a0403000c070000c1105000010088009403009003080c09080140d05840b0150341c0000082046008c1a01d003c0c0d13560000c2d040c160b0107020a04951008147d002400007a425419405041007a040c1a40c8500400300c1c510b1541ea14025140c2465201403d41c101c03c3e09000c00100c8440340c028807503c45800c2000d0800001d1914103529009000350b51225102c07285031405110030350105d50701d41d520308108400c0f911111f420108051035202c14844420116120702400c20007111545c030000419004c041c0c80d00324080e200c0d4400e220031008a940d000119201e580203109039130611560100406079541d6401a8841d08030b02078800700c201c0038200d = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 66844121 1250 66842871 66842959
    0x1061d100e04050c0117070905151b0303060a0f21030c02030a060501090506060412060c0e030d030603170301030305120606040b0f04030c08010203060901090b06040b0408100507030b 80
    0xa070000c203125901480c054118102960300150180c424004030b822a00c006000b0801d44a1708519403005840080c0c0e400039a03500e4403040450070b88146540c1140c60a104450004409400402148a00f20031703106080700b0307070351130703004011350082070007460000c1c0c1200242c3d00c4881e00300f02c842c07455603000b4a0a02c052100c9500030070304115070034201351101c0c0e4940c0300504c080d001d10300a00350802010b541151a00d4078051070403040110007580240841d8a60001c1c40102e441600c0174600034100400303a0b482c441c1c2448010b00100102e01c000c8271450082c2e105080042c01660503213040f80d4043e1201d9103002c200000143c2005c00041841e0f51121060002042424240700901090b04561414a580303c0c110b040c402b0425100d90701070b007070030703801003042007502e40304e11490f181100c80c80303000070668403070030030020b80305004941001e0010840800c0028172041c0c005490044e0400e103d00800070794a81070803c80c00d41d0781c01e440d00c0b034000040b140440030382c01440103003e100101800e4400c1c0d00000c4 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 66845371 1250 66844121 66844139
    0xc08131b0f090905010b0a1505030a02121f050d030f2d0e0901050907140a0207050301050a0626060c090406031202010c14040f051002010f050403030e0d0201061d10 72
    0x207540001c12441d54845039101005001d11480d650310300121202060985480e06a0400303612500d13216080002c0800401c14807215901600e100c4003440000c5c4085140c803c84020441c40c55007105582d41814010014590078089240580141c0560754140106812032090300d80b8100c1440e05c0ca52400448008004501049903c0074441d00580d20074090b1031001c0e04000d0411410780000703104807801d805100c41160040382c4000041940e503010341c0c6840802c01e090b4188146a4403144c1c041d401c24007044130050259103c0000e07180c89600c00380d95006284840301c0c0402280841c441160b207c2000b080742400040c028003191034004101140c03854807a074a20150314042500300015030746804440c1c0358190080186428000c0d11503086080c40d14029425400f14201d02c203843c0502c0603d01501c54440c400e40040c1c0c6400c9044800740920b0400380340040c0248588600c12402c5c2c01100020030980384180580750072106000a10203ca1440100503007207000090300c04621082c00b13140c00280550 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 66846621 1250 66845371 66845399
    0x23010507051e03090307061707030914070608180303270705030a06020c060f1605030402040f0510030519200111120d0501090b010c030c080f07050307060c08131b 71
    0x60040d01464403045018181454102d068112102380f08a40b030080780001048080c0c41e40c04881c6180100d1440f42c1c0c0c0c10102e5180d199800344101c1405200c8001c1203640c1c006520328010000d90000c5940381d0301c0e6a80d0300b074482c041a185810641200c450108404018139001e0800031040025100e2103aa200006403034494105000c42d03030547c000c101d0308282d10041c803800758040040c480190152400002c050b0009031506a0f070f100340b0401201241c19911282d020780201080546d00300000e08029a07580003820051004840d00d12038951513808174083c81e11000552903108a1400032654007245a8002400001100b030410443c110045010381c2c00704070100e0800c041988480d9180511400501960816000304103182d041290781c03145070b42c3c0b140d50b0031002034051410018080051030050035501c2041020328039040042010001d10001000501c5014840d03101040030401c003110984945130708880a000111082d4100000328000c01445004901601595070b00f00361500300d001d034804 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 66847871 1250 66846621 66846673
    0x20a090903080f060a030c0306020a120f1a03010c20011407050d060b040b0a1805060c0c09010e010302101101020c030d05070806010309080306010e01091a0703092301050705 76
    0x244402d00348a91507410381680c41c0c001e00c003520551050350554440e1410034404e88801012507500107552503090744980500303880190000401e01585190800c6140a8903003c0f2020072441e600c0c40078160300340340500c64000d01c00d402e40c81c0e12a170014482040341781c02c00c123030a405496548034441044070b41041d40ca424803801e1140c81c7c01c0e03216042d041080c411182290800200c04000700814415500c650068401d00121072030b2900402400c11401001c1c807400c0e902440d0001008242d11040c12004501405111020344080d5040c0e03a840d200150740000c28800603403c81c0142e0b0b0400a83e611500c0100034500b55030700050b24092000680a242d40d0202d242c03034006e166200701f40011580d0009003d50446001d103418040210507403a607c1440c072001e041d25041c00342c840b00c0003441d81d005800d4030005000a044060001e4003204003803095600503072048000030720a4070003007031342141e03061028800c03034916009140d6a40c4101c01980c155021400940b0944510a100000b84558403910b90040b = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 66849121 1250 66847871 66847877
    0xf030c021c0917030304050a080307170903041409010506070305090604030b0103050a0b06040c020606040506030a050601080706020601061103091507060509101d0c1c050f0706091706060d020a090903 87
    0x240380c180e030b11030020742c0501c510f6100d400070130610003c01e100103845046203070040042c982e00d440f120b805a0715400b05082c41c90900c0d0000d010000c203134401101900c201c80303015580700400c41c041400c0240d005801d002d8103520078014403454000c00e00c40c47c0602170304038010b00317001d20303054403a100e00d10307148000da00848255220080e050304202900e004960469015601480300c0d41e2010000fa481d082c0003044c0038000d90390b0303d00003002035500304400d0382c0f1141c000c415207045585950103551101c0e00d50150b40c2c058410080001780389841140e040002060070b030081c40c02c10350b112082190f200c00c0b0842d185001c0c00280607090100f07030795119481c01142104010300824090a201405451007000c1d000c107800807039040d841990f0800705650400c000704880b6071441c20b9a0a449007041d020301040900540300300c0400706080c04001a612041d904161910030300581e450000001448550000e689140c01520104100e41070000e4890102d9100500040c40d141d110400c8608450f200c403003d40c00 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 66850371 1250 66849121 66849137
    0x5040509090c1801210303020904020a0c0203070b0c03073e0901060e0d0204050402060c011404030e03030301030804060f02250509060901141002011512051b010f030c021c 75
    0x861503e045081007030001038010001c3c5601d131904d65000825140d0b80c03c080d40c000d5814502c109882a4100d4000307100c018000c644880206c0c100600124200034200d00900c41c4420101c0c100a1030b00a40724002140f40065145c0b01865603a60406c4149602c044804140f4000505080c5100c480203c0101000c010141e0400301c002c0400030b407000c060744400e045c8440aa003005498aa90303001c6d0391003e0301946c01041503110392000c14490711482600c88041c1d464101c2801c04180c0346092980102d00980e6000b150010680c10151a407000b0712008200c041e0401c800c0119034064802d21225007264016100d8a04040040e00c071701c000003000c080044040382105000c00d141c11a80300d80c0108069440351115070412410201c4078880b41032044c03244003024030002002c0e2003500002120386d80d0342000720440c2d9403a60403c42c0f034403900408030703654011408604402071120708005180c8105940b610301058140006030000e064803980304046000f6030101d4907051400c40d0351000115200d03a14041 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 66851621 1250 66850371 66850393
    0x70f080715140103020f0d0201020a0609110312211909030e01030f02070c260708070501110f06070806060c0f0303040c0b0403030c03030f0b04050915011401050301150504050909 78
    0x104842c0c509481c0c4071030250700ba0050000d40c482a2086280e40c0055070311040065090005030300c0e1442c203010040060b820512004208524070000c400c40c04410341c11990504003244464016000318845c03000c0e011994151210b040b000044540d400c1030f40d1140c1c80141e159001c82c084251200f4035022b0340480d1440000c8486942c1c0340c400c2000c16950384c0021410008580e9800c150a003040c440e00c0a14401440c0060225074140a00e02036642264212051265190480d98076040b01d0b11a141c08905a40c1c419a82201c0100c0c0e0055070482c0704000c1e10450342c800c1d01c2561035420140045c0e401a02c00d002d5001000f104000b00c154490755100115200e2505190114144049800009060000740010400240c01410b40c001c02a45420049400501007002074000c080051096500c6404c15083c0142c550000c0b50f42ca012400116101c085d0343e07200c4000c0c014541600300d64074001002000100002c030321405104803400c034107151203031406555a0015003454015074000034107800c0825096 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 66852871 1250 66851621 66851663
    0x9050f0f071a0d0203090102040803130504140906070809030904090501050103050d1403010b0306030a08040303030c110d020307061503050d02150115050403020609010908010203010f080601050d05060606070f0807 93
    0x44018161901288001030300c2d400400700c2c90280d0014021903540220105a00175802c1d01134030040c000d690300300c030345615501c1c4130f6408016191050600461034405200e45c003516140d004d5110f495824010306081d16091000c0751810740c001d01c00b0000703000a1040d00c0e41980c95020300000c0d14000d1001042d1541181401403e21880ca4002c60a11441c0021b4140c01243c070410340781107603201d00c0c0ca1512035480c0808079040040529000340803403030020f404410160180c0c00502809001e590b481c2d8292015013070540c2d00c014410460000d40d05c240199000510a40c11030b140c0051074500d10342c001036580e940c8500d014070181c070707007400340c0c210b0000d00e440003034040344590052040010090310090100d101820b20302c0341d400040c0c012000010b04e84402d0b40905241c1c4000d0004100841d03480da52030010020b040024014a48940241000018945800381c03080082c00c2d001b00140c0601e444031004c1080710790004074210791000403402c0050100d02500e010b0301c03001d0302910440380c484c4070600d010 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 66854121 1250 66852871 66852883
    0x20a0b0c100c02061807030209040305190903080301090903051201060201020a080705040f0303110319081803090603070302130807090c1209050c0103050903040b04090e0d0503070c020609010309050f0f 88
    0x1c00e81d41e031034040c0c1020b0761680042c43c960080c10b00e80740c0342108050100c0650411089800180d042030591040c40308050b40800100711001c2c1803414840b0401031448100c038004030030b01c00509102c00900040c00752000c2c1b58028a9020300c030b820b20728a800b01d080b4884c1301c5288242d02800150350301060407a14103030080d000b180d01081038684070b4981400e0400c03c00e10f50b0810302010b01009048259030400e0390040085032501c24149014043c080d1035854024000c8400b03c500701070164101c52481d1154400206a650b4040f00415640c159510144100c000350000c1034003544440da00b00000070340610510003040a416010030100d100901004090410980311800b220140d2402018034041900400ca09034180c409207404640307900c0e40b02c0203a1450145421500000c0b500040c00550359000340c3c890088440180280c401680c1940c1060380c090008076441400719001101c0f030b40041c5415002002003d405041c001080c151517111540f03406044603a00d403d0f40c3c0030b40250004c1400400c00 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 66855371 1250 66854121 66854143
    0x40b0a090510140c03160302072f030f07261204080105040b16080f0703231602010e06070c0623040c081209060705070302091f050306060a03120c020a0b0c 68
    0x409181d420400a0301c00c546c80348080398410141c0c04204082003100e01c0e4454100024640c1c4103188801a00540e010610f000e508003074400d1007102c50b0b60001d100f01080c3c4a045030140641102503001c0c2204003442c1c690442002c0304540114811b1003050341d1801d0280010f48180c90000415103410f1805070821000a404a0014001210380310011507124007410351044003024880307480c1c0c5540c00c05601074055a5503000c40703600304203585050320b1201c0c5481c51040b80e0810070401400c510319020307400c0300c070f07404486c000a41042e000035104900a0301c02d080c405101e040c0000d82f65150020400078601b00c542812600c1d00c3c140d0900050180072211540a801080040c1c4074094403030200c0c01181c4030708000b950240c1c1010855409222048c01b248000b182c01400071310f01441c1c41d00d6020f4240c0c461003850426205032990104960400040c00c1c1d2040b08040c0080030910b09585805a20841c0110400d0406c002d100406005840d0401a44020444128540e4403500c1c2458010308080302411 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 66856621 1250 66855371 66855391
    0x2060702010b031c1b0836181009020a090302040c02060f01060e030a050a1110030e070902030a020d1b020d0507020904020613030f0c0f120506040b0a09051014 70
    0x3520580c03081108200c13011031081420400040070103100d1000058007594409007462001081c220030f07042c030408110300f04900c52089224801d00c200c13490340036294000354041d007001040020b102031100b1910015084881c1800c000c485503610814902660311029400c0e00050300d0042c2041103041501507602d11140b240054041881c00c81e9601503090014445d100c10812092180413060310300b40719400013580c0001c142e60100c0c0a40c00c044441603c03c50319140100b0445070307002e028910900c00c02c250b103107a14000d880410702d440c00c0f00001e500080c105c5220158204801d40c0c2044051044000c02005c940c3d061080300b0b00c201c0b0282c1005a050052000d10400b006040f005a640121081c3d00c1903040f2140303511408400446141d13140180c00003400491400d05050134071520460200844015404070f003107068484007915100f4075001001012a440040440d00027290294003035805501c4800c000b071086544c1d21480d207440b410440e5407a0859682c41740c480f503640c83c0007205038414403242c = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 66857871 1250 66856621 66856633
    0x501050a08070e010c1403070b0105031c14190806040606090e06101106010b040503071a0d05060f06040f080607020d1b020303090618040606020c060414030c1002060702010b03 77
    0x850150000000501c010100318488904040c2a03001706044000e040d0442e503103080e070b481004141903a0741e00150f025501207100000014540c0341c0040c2e002c44141c0070499040011182c03580c140c8041d07000d206d00f4036841ca02840002114040010140205042039648a941c1c1c14a1014003085074419044001005400c1609010035008010005c0d08564240d64080c1641000c1c401150807603000450b10f0b5141c09403c00004400384c10601600c2590001ca060383d850347e690306c141200d000c02804030018203160034807c00040b0b025650000d070340101c0103040d1a140011400004103039074055080301c810403410321403d206040041082990141c40d03400141400e00301444041c5c0f074064540c0c0307001404050400c0c07040454506106503010210090178068450300f00196440900006800c003500440c541800083c0352440000d04801b00400904118a86030901d02c000074856400c0424035051b22a04070300000c0d80d1509818166100c0f03050340680414208040000c0c04c0d100c2003840d45120b58000 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 66859121 1250 66857871 66857887
    0xc03110d0c14010f020c0a120305040b040308100b1c0609060602060103122c0405070306030c0b07020406150806010212030705030c0d0e010603080c0d0302160f0f05010203010801090c050105 83
    0x1080362054916003100030350b40b00082c0205180c0c050400802d10110040c00415954401e120024208030003074801c28900e0600110b082c0b01b10101c0324101c4c0c000d0a035403004008507010078066013546800452815080c901d154a5a248214a511010804103141030b41c0761401c4080405216850151041d10024440d641c6447c40c025a9040180030151001d02c0d46003150003d039000752140400302005980100040c031030040c01c0100c0c07220101245004038103000020751022321a11a40701640e500a003545045400c003826901e80717070403a01040340c1003075894102140d12a09140c07109540586551031001c0d0b0319156000904000c00300c051030440074001d0081c41000f0741c00c0302c2900d17070003180140c0080d110007248030614050445001050050b51a01c0c00200071f00101c14010105000c030300e800c4550000460508a00720301c180e07003040084c1c8012440d80000103403120131050903240a4030140710070032050f840e0503007240d0080e80100d4041c1c0d501e0b100c4104010042140000074002420280c0c145948 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 66860371 1250 66859121 66859127
    0xe0a050d051305060c0309040b01050d060602101112010b0d11120901110a05030402012a030c0606060f05041a07170a02010c1b0219090617010605030304060f03110d020a0c03110d 78
    0x30041f2082c426611003010f800c80b039115400792075600100d42010f0010b01e41d07900d4081e4a0f200f40c10f81c241031072802d0030180101131072124115201c000700e1441da20b070035030302c1d00001c181d0380d42242100115003030f26400b43d90301041c035000203400940380d41c0c07403080c982c1d040913684a403c5038030f8001d15808800b0188110b252081d00001a207510940a0901a50601e9682004070850100c202600c0c8034a00c51a212401e00d5403190f40070583e944503200c1000100c0c4c8944060343c1480d4801680c2c1c0000300100024029110030040c4640560701038075143e400d02d0019599601d00c0b003000d505644049101040c00450180c0c240100e141e21961401c00d0400c600c46101c0302c02d1012005038010b8000e540e100e0114540d4800079103582c009007481017040005d00d03200c450741d09006c41c1d000410303080c943c02c103c40400d80c0d14000c0101c1d42101c0e4503482e400002c2c0703880f203400d6026044a00d1015803080040c0a6402800d03818002460340c9103840c1d841d5590b10300f6520740070340b0f8a0901c0b0210340042e408100d8440714150 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 66861621 1250 66860371 66860377
    0x19051903091a0903120114010329010c060f0608150a0504020f040506010207090507020d020c0306090703030809010207050304092306030706050d0207140106030203060f04030801090e0a050d051305060c03 89
    0x8140b00155903640d1840803e6285115030401010450741a000010f0002003102150301d10303000913138060041040000320281c1d88540a90010302280220007400c8940d070080c8458400b8074487d0401280c80c0040010f9141150555441400703a5009140b4600c50711034181c12541c1d1214950000300245e0425030049001c1e50310a20039140a251349a01280d100d0f03000708480001410f2101041c8949e03d442140203480750820600e10015100d510480342c0e0758540481c00d107200e1a50300008010ba2442e544003100c0c1c0c0000a0301e1030030785540c200f2102c0041b900500040c8050420180041910702d48100408840040641c041004075030304028001d46035400702d047c508607620391420a84800751404810024424242c0041030350f54140b44d09858010190008801c50f4022000d03284103598403101400740b882c04940050000d03900400600072150140d200c01d048001d101c08444c01860196a841d00d0078400300c2c4084003107100414801072403d541641100500010740345503041110b1040280d0f6640 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 66862871 1250 66861621 66861653
    0x6010f050f070809011e031d060103020603160903142a030705060c0102160b0708160801030209040f0210030b0f04060303021207060b030601030c090f060503061303051905190309 78
    0x42c43c0081c40f00302613803040070400c0604140c00ca2200007503484000180042050203500050020000c0a100804402240d498100c03078014003d1841d6503101c0c1c04812281242043c09800c1c4a484200800814481e029041c1041003d90081c0114402c0001c8540300c40390070303070501c220058030828407902900d000c01c07102d044a00940d24a501d0f104d001240f64068001c0e40c521215184038040300c88140414950401d008102c551100c150316140e0a100003106968000c080010035080e000409c010b040088007154458040c0d07c40341406100d60f400036038907043c2c2c4200d0100180d01c2d400d003c4060702d400a88030510160440d4100940c81c5182d9010b92580414100020382d80b0012a031b04080c4480c3da005800e5040000702510f000f0340e103070b2500c1190410140a0034246070300e41042c00b29034030031512900c0140c800080c000c01582c2d84181409179404e1800004a04021060020314419070783c01d00403915020301901c03403d48070740c100401d04141180c1c01019604240c00d00c1c003110041030964803420240 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 66864121 1250 66862871 66862883
    0xb040617010b03070e151e031006030215030601170403031407050c0c22020d021608040602011113030b0a090204020d06030b06030304240c02090703060608060a2d09050f06010f050f07 80
    0x451056401c1f084050800d403080350b0540101c0410f0741005895901150950303108544a01d186100441028118041210214040345020900e20400550070510380c2c0c1c060321915001c22200f040440081c000041a40e851000c181e0200c1c050011000a0100c601c0070401500c121049240c410004808800c400420301d58865001a10303071104600d6404942c0000110703c5e40d4a20f80d811454080b600d544a4400c0e4001540303010305021040c44008101d03040ca44040101c00d2081c3c3c10358443c45514040986022036284da52071072000140c4030f81c0041c00d25501440e0300001c42a1541c00c0c0807511640c0100071a1007030704100814001c4c00011416074610001c0c440c1000280080300005a840e400a1706002e540b02188034101300c0c605a160f04003c01b07481c0b00d6501e000395501c5207014088081d9603400780324a0803d905458000b0081c06005601ca5401b218044042c1f4681da00d50000484070180ca001c21380c441c03031600b040001e50304401c01e40281000c615100b85403031810251300c813440c003c800d801004 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 66865371 1250 66864121 66864139
    0x10110306040f090b0906040b070207060507030f0c060905031b06040506040f020310151a0a0c0201030513060207120f050414010c06060b160302070b040503030d0b040617010b03070e15 80
    0x40041c403036204012031944213080380001e0030544001681c41d81d08460445203900c6820020b03100e24400b00e02c1404442c100d0311024103094030f50360251110520103d4840400c1100c111800105600780201441d02d800b49001d1035642410301d110544190f490031000056030711610900001400016805900030b1b0446599844940d5901c002810b082c2c4100e20007002c6814900380a1900d982111700000700d0720000c01c0780a81d9515040d0707602240c003500e024040030a04000c40100507501036081645d0181044604d00704010300c44d83d0300012a0040842500d005110540c40c03004e05801580056900341c003424500d04041c585400440e0b2800140d22647c10001090080380420099800ca0800303021011415a20b50444500506906c0701102c41a0011700c145540002c0102c080320848058900141c0614030b4051341c03245c41030252a08460403a0007545d10000026480c0c18602c6055415007103100219110f8050000c26281908a40110454214000034001080c561031405510300d00c080d00c0c1c4c500 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 66866621 1250 66865371 66865391
    0x10204030b0114040b12030a08060d210207090608010203061003140103080a050d14041505090d05090a0503070b0a03051608160e03070b120f01050102060606070f15020403051011030604 81
    0x2170040c50003030b1600b1207815010800d01080200161016804954410401d80d903041c080009c0c2264845001c0c001800303005060804403032010100441d1800c03801203810882e03455407980d0880d42a58001051070f5400700601c0842c1c0f40c200f19556031703200c0380d103001d0024204c1c640c0030f50f004040600c002400d4a10000700036402c039004405941042c1c1003281d040100241c202100070050340110307411034070071202503e00f403d0741901e07206503030203030000b24003c069218080e0420b54441d03002e19040c96004809900003d900c3e42c01f040450b01820116682a4403200d81c103001405640c00588414030040040c0c8208000303035800503503180d220140451500d0300e5000014203030313800c0703c0100c3c440d90580200100812006c0c14900204110000c00d036100c0c540743e0721140e29802001d4280540e03401608501c021400500c0c003400500212400340c941d40c0c45100d82580c3d9411500e00149002410a80201d0708100380001880650500701c0910402d100408500c00c4080c110300c030060140340b1035035441900394 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 66867871 1250 66866621 66866629
    0xf061401050417071d071b03081303120f14072c0616060615080105100507050f010501090c0908060402090106030e030c0307080d0b010c0503070605040809091801050702010204030b0114 81
    0x78005c2c07a10071258150141008242101c0e0001150b040f0007094620380c0060034801c0d00808500340369055500d44030591500c141720510602e000205404103d00700070008403e190f9031040700c05000c4c1c031600001d03062003451507460b01418002d22a0f020320010010540c1440c40714040f0030300c14240818480c0107420400c00040440c0101c80c1c105c041101c0b4000b1b500d0070000540e101c030301540c08001c0301d0900d03140a0002200d104d030b024001e054210304072509001c1000e0080c2d0103043c00c40d03c40d02c04d88412400b810301c06802c4030401d0340700d140615102d200044a00e42c01c10302e000007a203036104c090f01c010b240c0b42c0c0108198003010310445c0109640da07500d240300618103000382c84481c1078240035259035066905051115800a10b454100c032441e0428503425507026030001000070b5440b0020b5403c22506885010046c50000e100380c0c0d1000b0f081058840d1a92168201c0780314000007a4002c40038010000c900b402c4039801018201076a10400090000c1045034800a0440301460302008114106401103 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 66869121 1250 66867871 66867883
    0xd08190207060e0c010909270302030f07050601030210080c090114090406030b0f0a0204050904080f09090108030304030206100f03061a060a05031501020c0f060d110d0f061401050417 80
    0xb9068602d00610004a03040200b40c03001c0c0710707209a035041c0c03900d034036402004110341e1002070307030503c50160020701c4522082011075031210318001c0c015681462407810a25100b80c2c890306003201c0c10b80044005204500e03045030420710b00c20b07480c90140e65500e0312290b442c00034400c00901a0520001d04a600c1d02d48001c4411194601c5002d04103010b80e40c0c4e00d113441c4681020a50740548201c2c807003000500003210a10a950455100910000454072162501013049c1e03c204010b580216040050702c49a841b01e001c8607000b400050011583c1e032a00b400d00a041a0001c0c1c04145d013441103500820855170005c07070303481c1581d8108000281010515440801001613101c00315002a404030309040e0b0700c3d400401441c4245c000c1c0c0c0352190300c030184400481e03d40d046500100d03032000d0030b1400c43d02d45080640c00b41c01010030f6070400040000d150b850000e51500408050900380e5201d4080300301c0403446000314001420401c04d84500840b24400103042400340d13015480c3c44090f44000c42d190f1080030080 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 66870371 1250 66869121 66869123
    0x6170105040509100e030903010f020f0702060d0609060b030103020f0102071511160801021314060a0c110409110a050103050c090603100f06020d0801080604020a03080307020a08030c090405090d08190207 89
    0x820405c0004400c241d0b41c49070010300c10a48203510b0050150700c43c407202e000300c0ba080245020321514250143c0c1c00c000070340d0402c88240035210342e11030011400218034400d0501601c00c0ce0412a100d40c918410082c0107222010800c0c11034104020401601c2089409c07404114903a062641101000882403458090006020358280e66100c80c0010508810b5009017403201030400104d08c420b07110396001c01c5c01040301e981070b40c104504000d00e404241c0724141c0d000d00c0c1403046c404032080761050000036003500d403107a80c20b40d5100100e107501d504a00d000300b0001c00610382030805122030b2030b09000140640c06080c00d45405000c00000013660150140403040150412201c050006a1181c1d8020341d00d9254043c90703008100c56100108101700001080c0784102d50080c00101194210750718080700b80c00c00303001c0c0015441801c0c004000505010017440c8600300c000c0c401a181c0e00d14400304001d545c0c025050034015080024a207505a900c485500d47c442c55407200d001c1462408140c0c4c100034450108 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 66871621 1250 66870371 66870403
    0x9010e03010f060807060908071229010e09150c0f070f0f0303050c030c07021002070503030d02070b010b0a020a0605060f130f1109010e0f04060521010606170105040509 74
    0xd503030102c64003070740d0040040c1c401c6082214001d03078441030240c601200314019a495a4403419080258024440b504044248940c04000d41007070881e04403000e42da5100c408100d0405000c005025507800508100c0c0d0085403d4000c0c403001010b0802801146800742200e1010a400903280c400e510b5880f0440742e12a278082200900d1110905054081c0c9030308900440000342810040f521583c001001c0e00d01890504210790b10b00280d40d42002051a801512441980543c00700041d8568090000d03240007103824034050303642d00c9286450076262005800c6920f4401c0148544400c655001540e005003a601060000f003a0b1125000501c00180551000d54800303030348070582c01040c490742c10404031682c803c0c009220100710805081400d002d0303940b0190020b0303000c9071100300615208007000302400c8050000141c290721000810741410700c07000d0440380070103215003000c8001402d104030300061034031340380c40c00401c004408a04042030307040c8a5035104d6a110070205076000c03418084a005041c06403 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 66872871 1250 66871621 66871631
    0x150303040b07050114060a150c0503030709050414040b07050c01020d020a11010c08060f0402130b03010803280903020d060b100f020c09090706030e07081504020f0609090c09010e0301 80
    0x1141111072540026803c50716542070850b0284409402d4400c01d005801c02001c50060b1402c00807504603040d180f003210001c2003150300038000864401d02c0198040c94195031001c042905000c02d1000b960014020014130040181c00c22010450180a442c2c0054044c500b440c0d03100c9030504100e01a00442d085014010f100140980c1d0046e00204558501c080040007804454507003a401e587d6200101c80007500034218050429180c80c0c250b00900008002118650509031a0080428103800136088500e140e80001080720100c0d010f00d481031010034101c150401d104c08020402041004a848001c0c00f40c08a070161008021143d0400a040203002d00002e03884440c004004000c0049406890058041d400e4200351504010a1040c401c0ba000300003807490a00d018002c400034080b0480103040340c0030f00100480c070814140310303440070004900d02010460409004003e030b22491021414031801c01044800030b0f945402405d0b070b500210741d40215403544040340050f1481030900a0071a415407800e = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 66874121 1250 66872871 66872879
    0x4060201050103030e04290d06051003031119061806050f040b06040b0904140a0503040605030f0a1b03050a110c01020c06010510050d0902030703140c0108090d1715030304 75
    0x158801d81c100ca0003940d400341c9200070402400116540c03100d003c2008030f801100d00340c5012190400509159004d804000c4683c078944070a17040311000d0380c811140e000c0415040050583c03054581e01100403001c050492a000500700810095003030380001d20361900c034801c501241551100310841e0310303000f0005000c0c915001c00d0740c100702c200c102e4041b00c0000101010500b58202841400f0019101400a009070346540d11410045204007810900c01d12941c011440020410301c051300040106031203464503414001c0700700480a0006101303201d06440c2c49030803070324210710044950f8581120708001846890f10301e81d2002030920307000d01e0320700050000380d1104011815030080071280d40280c1520f9450342c079501004100c0414140300c0c800910241720711040104954008034455200074210340d4065502da460102c1c04880e201e00740700c150002c180c0020301c0d58200100079401f14540010f01110002c18401408445840725114000c81810340003410b549000120b021100d0001001c50761603075a5 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 66875371 1250 66874121 66874123
    0xf0a09061b030e060603031206030c030a03020313090b0603010303030e0f0304120204060b070b040b0a090f03030204080d0806031e03130902040302030d0903020307091116111203040e010e0408040803040602 90
    0x410308800780000d16188800c3d00640001c1401c50150304010081c516007041d10f2484000d145002d4903660303150088443c581e2aa03a410400444042d22940103941c44840301040c02d84004113a0380905409420300611804e5603681c80c04886c1565418100003440070880460240303050140104a481440005404144000c060040b222020710844041c49041c0d200d000e012468041c80e01c004001246007404200043c0800c0855944032146d04000910a511501c1d48422104c84042c26404294001400e01801d001800002c0400e001c0d4106140a410f013200030a9a60000d290080c6040030803c0d03034404a0f940c1441203400a10408040c0300d0b560b6280c00c5200c0c02940f00c0d1104a21038800e03c40480b1004e402454500308a81d0010701424103d0300d0851a0000380500d02d41400d484d010030081400c8200c9507198101a43d4010b15181302081503030001d01000306011049981903900601007040b2041484c080c250641c3c0003048403040c10344480c80c0090540c003031740c2c0098186010126010a0480d4 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 66876621 1250 66875371 66875411
    0xe010e100c050414010e030f030409050a0b0102030c10021e0d020310050312091318121b0803150102030720100f0813020604050604181d060f0a0906 65
    0x14140041001d22180c14040d64030b84958440d0310728901c00f0308100401c0398080c8a103007510000c0603081e552030050021032107095920940108032281d82e00d5061029809417449042e4038560280000c41c40d14031401300340741d600c41d141e48c90406010f4000503003450034040e402e41000c42d110342441d03681d2129041080300019402c00c4640b882d50240242c00050a803a0000e5484440c54101058502d4a10b80380d00384040c810500c1c0500750030a44070b94280881c0301d403980140b00d00600800c0403252003000c143c1c00401c0e114000c0b410410113004080d1120109445600b100e401480c00c1c81c410020003203000041c0d0440c096400041c000c2483d4210340240480c8131010300c040c1041c22114104035820701c042c1516080d055880c034100266040000646030100680c00d0b015581c0010602c904007655200042c0441e03000303420030020b414000704401143c829031301034040507841010f5142e031403800d5406104e58801c0c0060a0342000500309020074449405039000c618001c0d0401c80500c1081480b00d0b001318070b01 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 66877871 1250 66876621 66876643
    0xb03031303060218040c0c140c12010f060506040f0e0423061f1208030a27022103090907030f0609050601080f010308090f01110102040602010b130b030304060f030e010e 74
    0x781c80d40c0404009403515202d0801580d034651141c40b11070401d522040da0350b19070341c44040300034441d5480701491030b5255410100c03c852b040e4004210f00c100c41d004802904c5c1c09901c1940122400c0c401880b201881544030002c1c4c414a001e8407070907075100d00f8a10181a000c3d00c4680420291803110844e00001040c01031050b6081000382c45498087c49442e04c07000d0081c40b4a5065094001c102c900190014000396007002e15502c0114500111400c01c1c44403910b005005e44031006207184510450510750b12144036003e07400304882e0b0804188440756141d00c00c100c2400d204284800002d01d0183c0690701101d074544450031304024240e200d0314024004c1005031340503408134081800007048600301c600014182d0381c0c01000d440c1404004070038001d8001d00c40c0c0005040c407145080d10083c18200f440070340001d08843d4004244081c0080610031307644520700e405c2401ea410070040c2d800070b842c000300b103800302c80152811040c19140707150124001d010241e8400007550800901128924001800d08811 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 66879121 1250 66877871 66877897
    0x5070c0e01170a0f030e03010e06090d0201060504020c0309010804020118082a100f05090603160917070b03040f0209040f060b0d021c0611030a02040807150e040b030313030602 77
    0x41ca40c88041d06540300c43d20300000702003140c82841c0c480001d1241130301080a0401400200b2041070604c07602d410004115040c060356071100c441000c0c6268240107050090070140d40462804060005042d1244500c43c4013606001550740403404592040410000110401c00c0c01800140c55051484e00c88115600c0b5031880b015045845ca10690700f0700001380048001024020340c240c2c2c0140c1525910030721190b02017409001d01c440c7c8540d481d07040043d84a241e0128031307d101599456006404043c803500001c082030541c844012010300001030720016111383c04200e40e2a5500c910307100912000d0001d0003904490a801804200042980c02600b9180319070380c24000c843d42001407010400c1441000795000d0b024624040e0006c0b101c007407903200240110b40101c1c1454024480050b164410741c1d0000780650b000a042001c14000d04c4030402418ac4000c0960601c0f0b015100184034024248245104503501c0500321f0559404008a0300900d40c905044892079a0b82e080901c000c0d00612080849 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 66880371 1250 66879121 66879149
    0x8040b030c0d060b160204090201120e01061508060307030b060f040f020a03050705180f0d060c02070303020d180b030a060302030106150e0409031b0309030501140105040f0b01020d030b0105070c0e01 87
    0x10b22910401d484c00b1300e5036124044940c4c1c05c150200300c0509050310069044c84580d56644456010b50700a400d4245080c40000c03800514040903105982029148042003000b41401c4c0007003aa804a43c1400703c0c0d40000c4041075603101e29000942140c400b030f0016610a15020211740b86c04446c1d000f034246a030300f03038404015a54400c2d00c01c2d030b00d0303210f40c400011400038040a04013a92030305c41c00e05012070f0006440700c0003581d21a602c02d0212800c0c00560405030b88600400c108143d41086a4115054103181a114081c1c4030482203a03e2212402070f18441c6c4400310005060300381035844203000b550002c0c024840242d540f18540e518111600c9a240002c0040302d1b0b031075050829024103c0041d51580c0c0f401d24100c100f200004240750001400c80402401c5200000460310900454040f40d45034841c071101ca515001c100702c12984d00440c1115118244442242d8aa070080f5044043e0f60740d03402c1c04180103003e400101c0d0b1a00c070365480101545882c55000c1060840360950310f040e280010a041e032 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 66881621 1250 66880371 66880379
    0x8070e0a260a050706050706150801020903060109020f04090c1e03020d15140108071b03030506010e01030c0e061317010f240501121e0c0206100513050408040b030c0d06 74
    0xa1030b141e6042010301641c0c4a103c0403c540c0b44a900100049405600c000694403100000418010300540c01003509a4011601446524091000703030300600855038114544040b0314107120981c0540c0c890902060b40d5107101c0302c525405140700c0e00d00003404213107407000c1044100c0041c0081d001200441c84162034525041100000c072640344081e1421604c048030781c46c03050710045030b50000007030000c2c0420040100c080b1b02050301c2d01c07554240510a4138041802d140490005041c40d5103402250b0405003401c0c2003190f45038005101c858880c10075a040340d9160516003066500060590042c500600389050f483c0085206600c5001c11021211060115841c0300300d041068040e04150b9503000071101c002001558000d87c0503204603246024041140b0011850034660222503950321700809071590403550f8900e40c10f0104075481031040082030780c1c103400c200100701c5003503c194482e0a244e41d524081024400d216094030010407248903416a00d25205808482c1604200e0841c0005400d141c0041 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 66882871 1250 66881621 66881623
    0x606031802010504090c0c050304060801060f05070f02010806030c122d070b09010309021003020702010e0301051303050c01090203060106020a0b091b0f0a03050709020711041b08070e0a26 82
    0x60440d50140c0d10a41030508250500e401828899a20f900b4403041d00c4400c00090b501b8070141c00145815183da8039290b00d00b51000c0c040001c01d000b200700b0042c0802000d4001200c811801c80341540a1800c08140c1e91445e0102e4030b8070b08000c0440d07603c00480307480e80403543e4000402d0250807401985903c16501400340348020780328198089030090300080b40a0044602c500c002d018024014580841e01080d60b4000c59003200c80d0444590000c1c1c0c0001d401401e6580042c05445410303000e40003080645000728280c2015485400d0040c1002000103000342c4500702500701291842c2c0040546c0d0312965118406940c1e2510600122800e00b0080d00140e4008404100003e903590802c10110540351020200b042c000014280f0316442600044084040f6004102c0c043c05441803120040e591580c5051903501e150600d000b8038441c07410100e8914200c1031f0040790302070481841c20000103507110f813501a92040000111190040f11b03038240043d2110902d8198000c86100545840c01242d02403549 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 66884121 1250 66882871 66882911
    0x91d150906060108070c02040f060e060d03050904090309080d02031b0303090616030f0c110c09100311120102070b100608040201080705130f0f0303031803120f021606060603 76
    0x9503406400080c0001d219500a40240350321041628000c070101046900044c100e0311004074840265540307a03414405040145c3d03180340c02c1101103030110105546954014243c1c42551196400755031204446410075020b14110005000f0302d4003542e6a2446140c80295241c000c072141d201840b040001500480c1004070440b801000802d0281095540e10741040096030320040f010000c040e9521030b86003d201080c031480700f500421350748419511114140c174610b400d119400c1e2074840c15250b418000c1003802040340004980c0c1c01401d03640280e0240300000e807924402c0a0400b42c40d40002020410040f180e8078051140c00320800082d801611201c00726280d420403280203012904480c04526810300070805405400007407140b0f411400c0d02c1d40911902e8039455882011816500d0b00d0900806416009100c20342442c505000003480450314020b050341c0d20400c01040c031680d507114820810300180c040b99050840718094103140c0c50316140400080082c0e00c6620700191070034105014240d0f04040d0 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 66885371 1250 66884121 66884131
    0xf03070f1103040302450108070e0f13120801050108011508060d0507150e1201020c120c0a24050c0a0e0405090705180a0612031d0a091d15 61
    0x2e41c1814215400e100313250801900315050225200085400078224550803c0740b0100b00c00c5031140c4040d04ca0a4000c100410381240c041034201e83d41c1403202003880d405907640b11403d0f0048020f1078807100ca000300b024000c07003000303481d030300000c109083c5982c1c101500604a4000b0fa80341d0070160380c2c9200d81707a03442115000e07000000d05480e0210f1040c0c41e141c110000b0032401807094503103140d9a44041c80494101d1150721010420b01ca00c1110149003008503200181288002540340000c40c40d001612800841c103aa0640f28000c941c0002501003089900c405e154007080f00000501805c02c42c840041202c0600000c031820f050025551a03820015075a4030103154031000d011f510707005c0c1080040d2100904543c8144100c60000949070340340da64403a480c80b1074264030b03036860030b00c00454801c2d5a0160440c12010501c004140d0029074041c03c02103205100903220b41c0e12084070400503450004070340c011101603013400300a1641c0b184045508000b1802c043c11030312091800c568130300c012002154 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 66886621 1250 66885371 66885373
    0x403080901030203060112060801090212010b090c0c0102120106080412030912110316030e010810030b0103020603041e0809010201060905010b070f050a050f0601140102030910031a060f03070f11 85
    0x110340d8045500a4019542000050500101da04030705000c0400b290b2a43d4800304890f91105606020750805000500d101c5604500074461101000049007842c4400307031106260003400200c2011556080d4103a0350760038003400341d505d500d5039105d00043c115903003070b50203807610140b012101c202540203115078009141d11207a090f08191107004161011801d1180e9000180800c10170f210f115030a045003005940c0c400d072259102504071400040c90208000c1c400d48034001c2109060001c500f0150815045aa04503644c5990303a4944c90120702041004200082512014000c0b808115072000501401d800a81c000c03c40743c2d80d100c485034240c4100384101659801c04100342000700d013414003052030903405641120400002580d0311440d181c081840c0d04c809401c04001071103200309805074401c808009200a60402640d540000e00c42401071300d8640a2554940307805590146105e501050b2040c000d0140d03850f5400503103414500d40c001c541c01000504110890342405016862460764601500 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 66887871 1250 66886621 66886627
    0x150f060f0617060105090103020403081210050306010e041e0f0302060a050a020a08060f04061208090a0b030105011d0109150305040b100b0708090103020423031b13110405030609150705040308 84
    0xf03001961540c1c05018100e0400d6000c000110104045600904001c0c0c403d015940300d6141490401d1030f500707420b400041c4213400220040002031000c02c8440e403c941c00c40540d8101040c5458100222041c03d2001002c42254000200030306402042d000c1c0700d00120207003032249070760341c43c0540b040b480790110082c08926840e01007000e509254605511141000d03100003003480d1540341e402100c4e404004100c403000702c00148200302d810045c1500009059a41516066504000001c0d2015020030f00c2e0030448044180c6100b4668403500843d0010900d8202c06c143c00180050000c1c0903100441c2c050f143c50a00d4800304203400c006286031800c0300c005c85413507400c0c0b52040e80c84c01810780c000380c40350b4109902408041106041c1c201e800c0d070300b001f00148001000c617800e000d01d401d000c1143c24200fa002c480003000c148580b00c6c00318010224898441c00502e58241d040300403d14025030f00420341500c551070401001c00c00010b01844d040000c5085c102c0c0c1a40c6655003101d25208a0200414044040c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 66889121 1250 66887871 66887881
    0x50610140904060b1315080c09060903070e0901020904052401050c0f0105010609030b0603151b0c0d0f140304030906080601020309030d0e0f010810060c150f060f0617 73
    0xe001410107848010004290541e41e801d011031300b41c21210070092805425902040300394403034603608050161501780160303103140c201100703404c43c001c85070628043c45e40010091501d5805010341c1014252403494010541014500d2038003d400c4580c00c98050f51600003c0303040488030000f00429000f004c141005411908401150280c100101d00000c03403043c0c3c1a14900301400307004081c0640241d0b40d03400e21040c41c60902c03541e420005000680250001181c910702c0d04002d004584d88100c0380d0442c045240b8050203017450310312a18101800034040e0038402000c9980c065844418490183d8072410742401c2c01c0340c01d9610f4030068800038045a2050703003c010030350044201d1540890140103680c101151140440d082c103d501c1c1c0010f00140c044010780800e49003030400200c51800038641070100d49804035001c2d80b0408a07000310814014050b0512081054101c40e10b09814007101d0207000c14401c2230b00384400f40c45180500180c0c482496008500d0b603100348140c580d55440f05520140c1a203031 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 66890371 1250 66889121 66889157
    0x40f0603080906160c180f02160303110d0513020a0501050c030d090f05060a060801050907030804090b0f060c151e06010305090f03040b0405030d030209030703030f030b09070c0501050610 82
    0x30252040320311342001c80420010940c5e072400000101040d240355945036881407040c1080f581d00700c10056120f0710601002d44150700524030611601c0c0e250400082800c440c60301c01c0d00f180952041500e0f0b0f6400c03e130405c251704103d040c0c481100c1d8801d03544400816214001034a680c01065906009603200340002406054160401300c0b825004400140f4006120f88035581003000495403481c0740360303e99004111240c024810203510510f88005413410a00759a00e01c82c5c03910841c031840b1032450b160781c8428a26038402981941c1c9400c01801c2c15500d01300701c285240c0392403a21004211400740c0100117005c5015440140508080360320216031540d0b100030040d0000d00c00504450014800c0da8011411700008000520150030061003141e111413404041514100301140d6640070140144400282030b18000303509030a99604d4201101001300c40c0c5070490081c901252041d500c40d01c008213014940740c0040311a243d00303010300024843c6541d00c030240103da032a42200302700000d211140c00409102 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 66891621 1250 66890371 66890377
    0x111030c0708181314060a05030d110f0d0c0c0503070f030f050705030105070207030b0c07051e030d0603110102010c031a011d03010f05160305070e090411030a0503030105040f0603080906 82
    0x1200c0f461240b0349580d2901084100d1001d900034001280c0d2038102075001d19040c8401e503130104040fa00400c80a041c180030984415915244009210300744521801c1b4080610840040c0c0001c081110340c5950356650040c40e01000382c01c10354140c40103541c007245600340800c00e103050700c048482d000c405038619921501c8150039904143c8140c0034080020070030396028050b440c041c443d00e5008102e0300d811410321400720b00003d016a28070300e4040244200040010a022032503403840c0c0c542c21180c002140b8458254402d660441f2581840c10501100f00282c0c0154050303079841c02e80c020490381010700d1084e4221105140c1c054503210114003e85225840b070624003c05240480101c00180c03c2d80000c00e0070350b8440e0f4051a505610f07601006075418203030000280054940c0b500f40020305002a02414898070110030601800408002905002c01c0d000398186404000c1c00f210481151030500544907002805a68443d1303040ca009180350404501814042e29045071040c0d28011540080100d80d41c = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 66892871 1250 66891621 66891637
    0x3030c030408072108060a0e190203130803010e040303050603010c170619030804031e0b0103030e01050c030d05060f0a0b0306040b0a080f010603030806010f0c0f0305040906060e030111030c0708 85
    0x203104008404415011501c040680700003580b101d00e01810048108121f00c000c0743c1100da050306040c801c101000c4c03103516030305d10806210720340166607407143c2d614007a81000d4814050032060000000007180c882ca101c1c501d1145000e603400300001d0711100c00305402c0c0c0341511800030015006868515080c2c01035081d442c0c1004000304030310209185250100f504104541c81901d46003000b20f41002800071071000303800d400b000020800c04440f501d40e00c3c441444d4041c0070250400943c0c0b00d6100450740280c0449107000000b80449480e42c8004140c03001a140072103c030382c0560900440c800309420031a10703100030b48101d114400c1c00c60381c902050100420001d03d1140c0d1001d844140020305900070300041d108640c1080001c108a030039804c02604011015281b54100300d4151485510b142d40300000d09025940000c480840342010305007112507029642006601a05d803010000340950814010160380000ba0000e100b080c1d2a58000e030300d1800301b205d5541c0b11a00401003580041d2001001700900 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 66894121 1250 66892871 66892883
    0x2100302190c15020a090e0a06030816020f0604080d080a022b06050108060d0609030309230705030303100612020403211803050d0507020a03061a090903030c03040807 73
    0x6650100e400d41d400c0740d48882100491007220120041c01140e00c51900788256020041d86010841c05009190301d615200d0311188540c04000319000302c3c01c2e0f8002400464210307400948440c080c041182d8101000c0070120b02c140b1458101c0c070385070f051890a540840d00c03031710081e101101034a001a91030350401051b4410640d82040f10000684517a82c5000fa141c3c002c081e07040c0c034040b05040140855459403c0241071003030510410080b6035440024198080d070048012032500181d103429009070907040303002001c0003040100d00d081c0c20600301407001c8880d10741080300d40c1540c2d10814180ca0384400e54200c401c0a9402405000140c0500f08007600d50103401c40044c549913698131600700204030f241c0c1254074004030103004114194891844000b0019146680d4989444c0d41d0341c00c1d40d5400c1141590041c4030000c25010705544c0c405e28450002d5400000500065a1807900c520b076090100030b44e244138480b2807020451303643d40002684c0c460710040644a1860325075031211034407500150300480749 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 66895371 1250 66894121 66894127
    0x190e1315020705070e010b25080a05220e1914160210090302010203061e01020601060807030e060109020904150f06050304080d02130501020d020d080f06030c22050105010801050d02100302 82
    0x40400b01d41407084c02003000c0700c101501c80102e24002c00c22088000c0850050052402120021038046801c42b1810010b5052090b0341c3c240c0003403ca1040b0548034000c0503541d2902100050074031240d94560710420107040070300f0300c010a01620300100d85032210009003da0181b8001054018005940b81c01f0206c10f00480b21206403c1c181201030b10141002100181d40110074040036050080c034a400f411501100b1051807402c03040001d55502e0144164803c03c0007040105101d60300039030015100c0005401505c0556840700c00c1d050181d4002c4140501a03032502520114030344001e080da1054031100141040e1461410008488607080504142e40c203080c1084038030311590301840101003040c2c0003401c808280e407a0000281c100103108041c0c80543d0003440400c044541d000307645c83c4d1310800340c522030540da13250704021910785816074192036003000024003d44091826540d0540c101860520240483c1c1c1e20380c4011a4411001c0c03080c10b401900c003090500042c54445904107102c0d4603460b0042c2 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 66896621 1250 66895371 66895379
    0xc0e070908030703090501030c050306090406150f0608041208060a060f030f020301030b0603370606091103040b01120c090b010314010f0317040b0702060c01020702190e131502070507 80
    0x30070350f440944200d0104070310340410050b5507014001d5003d282414200070f815440e0170800310f0810740000300700606256507003803000242a0340c008140040c20140e0320920081b074645801520005e82580d05031401105001000002c51180c5202849400e001d8401403040785032035026a030302060441450103140d160840e070014407680d4405140214011001c9103500c0c10b20b00241b600300303000c40c035640098108001d0061622401d50390185154840010780340c8800b1294101100280119040b454556052456085401900c44041d6006a02a00c80355660340d9a8225038140040380a100400340c028032501003201035466803164400d50810305005c40c0e10038102003520104282604203445a1803c00014414821501c0c0040c011a4201c0d4900785441e09104e981c803030fa80601c1500074131401001a030301080c60800c6d010388c1d50a0b40e002d88082d40d105546d10415030454817602a451307a200400d0001196200754020360780140c0d0304540d4681551904818000c042d500c051320542d001d21620740001 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 66897871 1250 66896621 66896623
    0x209091009080d0c020f071505070203030c01061502070f05151e032205060c03100902040b0304110108060f010509040617010509071e05210613021201090c0e070908 72
    0x300c030701c40c0305000003941c964a40701403004403004816001c046620000390b1140d01e00001880da4141c50002d0101d500c501c0c107260003100d481c414008025018040803c0362440000d05410180903156111070200404104007402ca0fa20040d43c400d10041c0c0504004c10446424a0044036001c0c05050400c149490b8500c8890168168292008010040300000700400000d9041844903ca07000c07681d0005801801d44941e5540c200c05449156014000004510b8070494943c13400c00801040c4010740d29560382d40200c4c0d000382c2080f1000e983c1c610195065040545c41441c0027803080394020301c0d542e55401d0301c10044070f01d600071100440e0000e98841d8041950032905030303440303000b154490001ca0146030040401d0305100c104d40c03000302810480c9400d0b00003031038882500e0741500c80549a24a03d240031050000410020f040d8081c40c0d40120014000c400002c081c840d0055070003601c08a04814614036107a080b00c007461000351840794107003424407105c900d0030360494000460b40340c540c060b01d445072901 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 66899121 1250 66897871 66897881
    0x170a08071b090c18050a180c0224090d0c0305030712060b0d0f060f030206030a020906160b0402031605060a0509060403020405010b07060609050601051801020a0b2802030601020a02090910 82
    0x20001084c602c480c0303850800301c1d4031034207800351400b03541c1103030102d18180c3c003002046280c900006180303890b107500f420154070801a0a07440302c0b0f50842d40c3c3e018005000c0d10b00090070250b0b000880d81c05501801400503000d9066403040d580d142c0e0700c2038616518107108035569007008402c031528035240c4c180000c0c05040c100242034254421600082d5540012400d00b0456007e0381c40110740c400c11380400c0002d41d4628041d03903441071403c0c03405a0340d40c40b84800100c181c410b5030447c5132031395040b902ca8018003500340140341c8124429812500d80318807981d8155110106841005d601100030004070a00e54480c0340689401017024081c14200350310b030f0b4005000d03038000f40c1003450045000300c1d0b0b038000d00409014000060851030820055410030000007400c510130b59410110344452464820400d034403c1040303101540e0415000e401504001321080140700c060000440720b807260141402c41810a44212401000305800030040041e240d4240310210030000c01c459aa400780611178800c088240c02a = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 66900371 1250 66899121 66899141
    0x30c0c0209071101050603070f150c0f0c06020c0405010f0b0703090810091703090304120827030c030601240207080307060b0109061b0206031503100501170a08071b09 73
    0x150784220b01c03e24400b40d08484e4002c190754420303032200d54100880740c00c03d40e4403000d40d6901505107100c0810700c0c0c0141ca0b080740242d130041800c1c00100c5000c0c103114402c8242400c0e0340da141e00352104404580b00b040b00b41d520a01410309580d105032020410058110000d203849886070803d42070041d0baa203401820004050524003100d51205099020042400200120818903401e114218140f0504103a0f0728041da004a51300c440c6119101030520580b00c080d41e0351011071500c040301203d80c880d01c5503d40f00c600c04016000b44502c4404900b249404142c40703040c0c0f101131060440e462001c07203914100c04000340081042d4060480c0108160070306100628903d4010140442c100780c040000418030328003907001504000c3c2110101d511004e401c207000300c5894040312501e882e80c442806800c0c100e000444903650512602001c010f54001c95042681240c0c01d08042000e007a0041c0d52503030f1900207a0304002c000070b070200109000100d2503102e02035410311010001607407079250385428044900340c0403 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 66901621 1250 66900371 66900377
    0xf0604090b09090d020c090a2d0e0a0b0a0207020103020408160503070e090d0f020709090c050901050102032a0a0206210709081b0f0612040b0c19030c0c020907 70
    0x1540700314034101007801c2e5401c1034000d0010a02d001907500029280d08080d0340c010705c205107480201d07120101c0e54001482c0b440f009d14141e1101d6400080c00c00c00e075141c1c00c42e0101014103182c200f1002001c0801e50b101300940221001c4a141d4500c11108003d50007544121305040e424040031811040410071614506003c81900c0c18440c1002d040615105031343c2c5c0483d071581d07580410820308200104450138204a641408400e000c103024090303082c5405604190120f5160900c50800c0c800f800b07521034219903003500c541860741d886000490b183c0c415407032030000712180700c450095641102c20301c406014401c8415140070310030941c0007550a0740280800e8058184040d03e00c0c100b00184070000d41c1200c0f05090190010345890780850b2121b0701c0b00303504101d9044000104030b8540301d07014040c10034500145119611141d0b0300c40e021f184102030f541968200300c3c0800040000c1031900840b0301c1c404100403024249090204210007400ca0b515120b020003403224420703801602c884041500400440d2 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 66902871 1250 66901621 66901631
    0x30b0f0f0d080c240901020a0905010507020114130501180303020c1e09010e0f060409020f040f1b020a0c1a07080a050d09121d13200408070e060405060a05040b0f060409 74
    0x258801320040002e020391290740d02c104140255140c114554404960003130800e55115180d900040e11740c8035014203441d207190000105446801c090354001025110262645020b588034001c0e02201071000d4040140035074045104c40190345400ba28052101403001d00f480c40808109000c100b0038a030030b0340081000341c1c00d47c060003036001d1526040780e40064281d07002c0081070015000200c2100003204401e009984e14621441081d6050704550303074800124440072803210072100c00a550300c210490503a0100781551000c5070803090b0440f2540c905c051000311074202951919170803440d500450388401030140c20040310410070801c0c0100722103640240409000c403902510040d1060001171140b0905104d011407816180e0303541c2c507480484621107140041c203071340c2984410035031003500c1051100c850804180058100030002e204810b66451691450b00380e29000c041c40251003094139211343c800700032a03042c0030782e0505500c20300221a001300782c1040040043d0100b01258095084000095168 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 66904121 1250 66902871 66902923
    0x3061b030b031501090e0f01050f0109140112031823090105101b050a14010c090603020315010c0215040f0e0117030406030e0705060d020307030b0f0f0d080c 69
    0x103228000c1c00d100c0a038083d0095003155048002e82c081c0500809014540c1c07040201e80611702040711090103a00000200a00d0030400941c13542174809210f0849a90304044c3e02100240c080010079040351024509000c0ca1602e45c0d0782601c00780500c0c8440980c0040317141c00095803440d604140100b6070004405084441089028400729220582290b0b00940b071605100340c000d0342c4a441101d0005085a22104a800700d2400e18281240300c080503041c1c2000c0c0c0c03040d81e00741c1010342c0002500b0341507440b040d8010352703205002d03426400100c641c50b403011034942c103c0c109940900552500c2c28402480c003112029083e40e40001500706400c4519501c280c0c080510a400e0031080300c501404c1c46402811600c110341e000d440d903074451405804209500c0320190071205000b000040003806c0c0c010000350300d4000808124000b9001141c840c00080d0401e102148a41041d12028030010009400c0700120650903051042c6d072001e0500440d11080c00700080300301107500f800703080e0800c16201c07140302c150101 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 66905371 1250 66904121 66904127
    0x120f0906050c030f041814090d0c02040912050a0201061d04030c0302010b1203070201080a060e04120309150207050c0d030906051303080403290c030601200627060408030a0b030703061b 81
    0x1101f0004144694000240716540c0c4002440f60034508507840e10084000107440840c001d010030600003010142582c0d980b11030a03400c44040c06142c1d205600802445a8070301c181d064542c00d2451520900c0148408103002c60300c00c403400d00845010f40000f26084c20360001089022201d414641d441d074001007081011582e000c0441908007914032400d0243e50300700800d402030000081c0c4003c205101210700a084a40290403121460780c2041c0c0e03050300c0300c000b000d903280a5804110115a41e02964544411903d09220b1490782c06426a0311a01114146603055031503501c41c1300500700221a40c0030001c0018040001040074511403621700c0a030042858240000725042d5050300b22240202c01042030440c64641035076030000302403a1001c0301e090b803401d40407003140141d08006064010300d001c0201103c412140513091021182094040c06205509145c590700f007510f004203824402c0001c52010002034000700e1003103400906a84c01b20b5aaa9641002ca8070000800d00c0483d41800b2400c01d8a60 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 66906477 1106 66905371 66905381
    0x4051c0212060a02121e0601030506010e0d050109060c050304030507020409020604090509060f09030f070605041109011d0106030c0c0b0a02160f120f0906050c030f0418 74
    0x8080003003c02035401004440325099108010480054000d03500f004120b0352010310340e901d1b441d0071004501500340548003d04002304100140c420755100f09510324118494000098000c0e076603d8544292903804244e8000d00c4420310800000c6500401105c12140d411035000072001824070018100340903d411018107a49040100400c031000041c106014130080440e140c01da980d1460b001c0d40c0c92040a00d5158281002d10400c0d0004040e90040b0f504113101340c0d5824014103030040428000c5400f40d021802c55420603000c0da1b05210343d18800e9000d0482842d042c04803003846503026107000411a0001c2a0b107000d41c000580201042c0d050741d80c001c0000c0002c110200326070802940c03110908509a03141d48440f84c0d07000d42d1078014414009401d019440d0303820b2661070800241e4050300a07400301b0700c040c0010800c00d03581600b000001d101030a00404212080c101745901001141c13 = true := by decide +kernel

theorem cover : BRFrame.Cov 66726621 66906477 := by
  have h0 := BRFrame.cov_init 66726621
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66726621 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66726621 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66726621 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66726621 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66726621 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66726621 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66726621 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66726621 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66726621 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66726621 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66726621 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66726621 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66726621 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66726621 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66726621 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66726621 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66726621 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66726621 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66726621 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66726621 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66726621 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66726621 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66726621 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66726621 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66726621 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66726621 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66726621 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66726621 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66726621 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66726621 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66726621 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66726621 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66726621 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66726621 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66726621 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66726621 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66726621 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66726621 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66726621 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66726621 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66726621 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66726621 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66726621 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66726621 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66726621 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66726621 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66726621 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66726621 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66726621 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66726621 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66726621 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66726621 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66726621 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66726621 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66726621 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66726621 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66726621 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66726621 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66726621 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66726621 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66726621 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66726621 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66726621 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66726621 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66726621 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66726621 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66726621 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66726621 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66726621 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66726621 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66726621 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66726621 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66726621 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66726621 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66726621 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66726621 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66726621 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66726621 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66726621 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66726621 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66726621 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66726621 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66726621 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66726621 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66726621 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66726621 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66726621 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66726621 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66726621 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66726621 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66726621 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66726621 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66726621 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66726621 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66726621 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66726621 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66726621 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66726621 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66726621 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66726621 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66726621 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66726621 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66726621 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66726621 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66726621 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66726621 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66726621 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66726621 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66726621 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66726621 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66726621 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66726621 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66726621 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66726621 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66726621 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66726621 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66726621 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66726621 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66726621 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66726621 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66726621 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66726621 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66726621 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66726621 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66726621 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66726621 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66726621 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66726621 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66726621 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66726621 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66726621 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66726621 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66726621 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66726621 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66726621 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66726621 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66726621 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66726621 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66726621 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66726621 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66726621 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66726621 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66726621 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66726621 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 66726621 ≤ n) (h2 : n < 66906477) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
