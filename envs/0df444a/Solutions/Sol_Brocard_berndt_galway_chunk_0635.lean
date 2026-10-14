-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0635
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T20:51:01.118972+00:00
-- url     : https://prove2.me/submissions/4d8265b8-91bb-4c62-8309-9135ca6b2682

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 114028776 ≤ n < 114208633 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 114030026 1250 114028776 114028781
    0x150e040e07050102010b0f0105030109050615070b04020102070605120601080c2724030c0310030c0b030f160e0103020304050f010603030f1e050a0e011403130b010512060606130810 79
    0x10b42e0000e9000340003c2100d64140509100003400643c006101000104060002c0340c3c1715942000005020601444601d60195403a8001d0013007a02c503c40a142448115030b01008040000c00581c03e00a05001c0248110305400c0750060900381405000000207c0d850101c02c00c503640303894811601640c41c000e090000340448524000107001c0c140c525205d1000416042c00d00c24544071501e0010b16586da100c01c41285c540014040001488070240040001501600c03508040c1c00c40b0480d05440e441e029007003640f40000541081c140c5510000c07035a80c4698818943d0f84065001e0070090382e00e454170700d0014a811451740300401507510300640441050b034841e0701280f01c003d8994401050004038200070b1803400c03040300c42c0d20108508101e1125101e024084109089805040c0911102810000400107a00441c1c01208485d02106078134104080c00d001c55000d0401503941071038480c210001d07255240c1000d0f05240c810b040120700300310080d010524406c081c2100302c0076031b0040750500210780013 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 114031276 1250 114030026 114030029
    0x6021204350c090a050f0403140403081207031a0f04020a1202031518160e04020c060a2009100e0607080a0305181f0f060807080d0206010605070b01150e040e07 70
    0x802c000c0a8045a00c070104da004a501401d6001112215612191350940701c500014410404202c070500002020035608006450381104000ca582042c0c5098500282101d0f172080e02c011003079081b4214a05c2d680c498140020403142e0940300141c4e03418003094281c95464802c8150040c0074000010413061000c410a400d0001d0003c1d91843d5041c040f1641b03c4040450498070708508c1e2038903400309840390b40315174040c00001d10b0190006150031054603081d42080401c031810701c001500c503c005070a07407072050709440000281001c1e9a09110441c000681d10090741c22001c02040362200300105195500da04598075164060702c026070726491003001074080c00c81122905005002c420b030700003142001040c00040b500324185900c04440c0c40e41c070700ca0010410341d12000306841d03440b200450b41c1041000780c04068040741f002007002c2c4101c501e000380381c098140c001c6820040c0034402c080004d02400390207410341318240c041d83c680b6031301c440d000c9840403445c0405590003411320b444100d452002095190 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 114032526 1250 114031276 114031279
    0x60403140706080112110f1815060a0504050405040602090901080d08100b0304030c05160e1009060810090f080d021c0e0a0b090a0506090709050106021204350c 70
    0x701410755400d0152020f1409100b02200c0c008805070300e01c002110440000714034500104040d10b1905448086884000700215610f000e044c02001c1c410b03030b0f04085500c1c014000c421038441e45880d01c030080050490040e032080354010703500e81d0003203010448260103a400019018020000c030f07603580e2103095030ba00704400165003c02c2d122008183c0131142c8000d030000342e50010019500c1c544942c0e904035100c000391102929503000f290454500c480c0750301c0c0713a14000c2025042100990910750955268140c845d07105070a00362038241b04128029012600d0081340300050000500f400407801d11154100c0320100041c01c0000000d0703040044c03039466000e451407040c62006a22010b03801000c103800c40d8206034440e00c055010380040c01c001030030781092030340c0002c1c860156469072803d0b588031864880180c800a07410340000e00280040010b80c0f00b02c600520f41c910040640a040c0d0046625610560103824076000328195503803840c0141c040c04141c4199194510300941100340095901e40000300c1c5400e = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 114033776 1250 114032526 114032533
    0x18012307030213050108041a1017030304020307050616151a01090501090513060f0608070210090312050403020309120106140d2109090504050601060807020a12081506040314 76
    0x218018407078401da580000f86107031440403260510b0010740340d004006200b140e25880300d00c090031140e42203003122405980704030114a4020305051401550310344440c5000c1c45c0d940b00f4400c010140e034000841e03100b1150159940c82e5603005100444c40e00c400340000c050072100b0f00c05403c3d20b0aa80365842011500304140b004818601c00b0001141c18200c1845100c1c00501c00703000901444c90142c010100d000e022540000d1000d5841880c42d4031140c044d80900049070b021700c204080c0c0b640600c4a884080780d50001000303a03501590300a014005160b224010380e40e030b03c0000404050003003085030314850b00101000030b041e5031004020b000c1e01030713800350041c0e60a451102c0340341420b040b03001411842d0300c42c650450b4681c003e40034044054074000300c0c90030000c501800141000d207611501e03000d81c2c0140d000e40125030410b0300103040154050541411580540368880109500307041078520419180390102a984801e4640304c841d20801d501d180d40500f0001c0c00001304890020000d94116006095 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 114035026 1250 114033776 114033781
    0x50f06071b0e0a2a02031201030804061103040807031716050708071403120903070e0a05011d0606090409060e191a0601091401051309090311011104030605180123 71
    0x341e044d5200120800c00040d00001075031107a51007074034811401d260307920441c0e00700310035045c07000030300d540030b81c010b941120307002505000456100d4503010000e00005d009518180c03604080c0c03035682c282444041c101942c44400721180b40c2d45201181e00059000682000108a508200351241010310800c18648140300c0700040584005070109180ea01c0180900b52044284103003141c2580072800c485d50601030f2010210f81010380e00040e0b8083d000c2240c00049642c10507100c2e400795071909001c00c040640c03240401001d9540d842c110743d0a090155008030344407000d032601002500d03414010b010540520410501001c003040385541d0b049001d401c0c3c0e007a0381c0b040b4030245001400180c85603030010b85203d00c02c2c010f401c601c031301d07100b0403500c11301d042c45c03404150159070260f80f00300d82c010440c0d01c1d4481c6003c01c10306500a09811400242000030440c0485c60f425034000c82c842c030b220040080d5184c600140c000011081c00081d5074a00c0c50007400f20ba034cc4100400d450015507881c03080305a008401 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 114036276 1250 114035026 114035041
    0x10b01030c020f070b09030f0d02060405070e060603010b0702040f0c030b01091401050f0c1207030507030201141510030e010f020306010f05040f03031407050d020f011a0307050f06071b0e 82
    0x30004042c2c0f8640000e08603460a24000c0038580d1303c0004410380600c6248410701611100300416050180d60750701800c26400c107458100c0c00d00107158000b0020203d08401d1207800d42d155000c403811a00341c03c0c4240d542e2901480440c024000907081584082d03d841220f800710b5415806c6a01205c000340c0e924a05117480d01d100030f07a51612480307090b00098003071007111102c0800200400d072000c1000c007103c2ca5010350440d0441594080d0004a000902c00700d600d80402d502400ba02030f0310809000b4610711458410341c242081c42090036414411442c844094002c030380a0781c032111000320711b030000780300401a8071404c074041d41c802e0f02c45900140d81d612907509198032550903a8261110103002c0d8000503d1500c049400d038100440001100208019000c000fa00400850128400c00d4007d0245d100004803582d0031101000440900c5944018000d116641c01080400c00d95600f241c01c0c010090005002c945180640c074001001200c10000c02c4400c01c0c07030040c0f40c5084403c0198aa85281d0365500d = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 114037526 1250 114036276 114036283
    0x10e1b09010b0702100c0c08070e070503090c06090a0320150316031a0916020f030703021c0216080307021c0302030306010e06092206140102101a060c010b01030c02 72
    0xc1401e02e0001c003440980014600014400d0319401c45240c103624244403911340807401c1340c0d030350b0022400d5403121504001200090914542c40481810b119082d85070080b101512071480c502d200348501c80000780e20b8150364400c0039110195400403480d1103c1c071080310b44641d01a412035031aa21900b00603c26070280038943d0f044901c15420540f0829111903c00c1d4298041c160203554422201e6140c1003020440d181c06008611820b019a03200d5681d0b1609400642016905030804144d9001040700c14042900000c0c1c4441101c405400c0480d103c10386582241441c07805403000468004510b00007400d03590000140030424003c0780d0a0400a494205100d0000171485004000d6001440003e401e5801000303103134a40c91b406040e5502c1d102d6400001503400705c0c50510385012102d1184503030301210091142c0f0f07010702480d1001c0c03903000c080000041c5d95600e1610218002580320803004c044055418440d0404150140031a030b01d81e0003248015010384120780085d8006031804100703413216403002 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 114038776 1250 114037526 114037529
    0x90905010e0a120c020301091212200909090c03030712080a0204050a030605040302010921020f03030606040e0a0209030312010303022b0c030212070302071e080c040b040905010e1b0901 81
    0x21050f107a01c00e91499040d1006804800d05a91555030b030314130b4802042411401401508035503480702c0705904c000214400322007004640c1130320240c0f60303809202c080da0078400311001d00380b040358004241e6852680b214980700c2c04010b455098000400e00104000180450310340508007501d400c60345a8918410030206d002d98411070390300c64a427000c10004500d540c2d01880d0031034028070000c00c0c4049140c03650139041682d03a80d8848a2191a0103518006505101e0300c20b1b180300070380140d4070f175042c20400540240a207003e01c2001c0381c200000b090541000382c0c11140d1070f03000942520349803403080840c0207520f04248070641c003500036955805070504140440e401c541c03034500350003141d2410b01441101c64101d03060003241035200c1c0c880d51443d030786290406400700920175030003440401c0c1410407041000c12484030001c1440c04401e0f040c00300030f1002c03510066200d802e85c0c0000300c0200071030000b030190410800113031165207850a49404c401001c1150114050f10503100c9200301c80280034403500d46001d = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 114040026 1250 114038776 114038783
    0xf01060f05030103170919050a0605040e0c090a0806070f09090c021b0609040501030c03030306120b070320180102010b010c05060c0307030b03061006030c08090a12090b04090905010e0a 81
    0x104011300024800b80f040c4002424105c0900d414507a10801184044042d102d150026103001e00d410000da2510380c0200c0c0140400e440c0c440e08040c039220030071320196005480c81c251880b010944411a498041c080001001d1900c1110101c0c2002c4601038407403609807a0a02c0011040315000c194110a80078000d401001c95004141c0e07203405903010f071115100310400e154441070800005950780d5850084c02d003c0c40c00f800880d290b040c0755103006412034159030f000c1106c030100050618041041f050550b944220203080100d00071110400c3c0007400c982040401501480c0440e028175060060041d29030f5420302038000300320a01103040156018071000381c00811a40c0b02000180b0a080104041c603003155581c01e01141080c05000003904000b81180c908a600c1d80c050810404d841c0c6c18012a5403400c95420300b0300c06c40c01c242e481070752152070306000a0032200c180d4210380310f03161041600000800d50200000d03141c50720744880303c0c007500003100e0540f440d60034400aa10100c5000c504540004e80c07 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 114041276 1250 114040026 114040037
    0x2f0d0305070206161b0503090618030c03070b07060c020c0402070809011713080c190305070b1b04090216060606020c01020f0708030a0819021201051e22060512060f01060f 75
    0x240308460040405241c1e10403035407800181700c1c1d1501a209c402c09070041c200040981010b0004501c141172402c0d5a12401a01c2035115900410010f208441250055900b2541c081500411510181c1c50300c003201000a421905c0040c0c080103200080018144400c0240c0e51040c0c2190382085280c50b05200703591441554403140d00f2940021040f100510801c240e20342a580c022041042203090a4000da6080c0c01040c0b00081101c02c11034201306940d404020340091070604d07008290400041d0180c0e000d090800f40c1e002031240b4829141091140c4601c2d80070000f80101508c4e14002074551b44116980c0e4054819041481c440d4034020562000f41c9030400c0040d818003110380c40403140ca0a020300103141c1003022110b0800300060500003007620350060361034103109505d0041070010550545802e12400122600ca59580f50381c4e4050381d01d0444a0303121980302e40640c4121200041c12903912040d4000d11500ca95455407501181641c42800003020440550f0307030b1040295118003c440d40400006c0 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 114042526 1250 114041276 114041297
    0x50a1a060a1a0a1707030e06070207030503040e040206071410060b03040f1e060f1d0c0904080d140a05010302090c0711090a230103020f01020d2f0d030507020616 71
    0xc10110140031107030200e1601e00d20920786480c664910341c001750780180019440355000369483c5020031401c1c2c0c00450030f2000f0b0045a2031a1140307070b00d80c021401540c6040051001250641d9034840c01c0d20340c19900030301c10400080c2c249402035980c0598050b803c0380c03181010000111178400c0c8050f03922682d0040d01600c04d0440b1595503450b24000d50000030b0080d0031402000b40412103501c43c0c03e5415554410000f20114102002e030356080c0054208491607124044280c0c464541700d0080741c1140d8011000d036151150803054001800180321880031480794002042200003440c1c00030f0341282e00a54560f0070356290100400071900c01d810024103c2c0c80191805030190400c0080154088605000041d0074084a1400034824096502813446a11600014002d42c6407845004000c0e0304240000c000808c0c0107140030704080b82800c031384030900d566400070b40503017000482c0e50341d000d0720020243c9400b0105484064018001500c00314014072401001510756a42048021030906141d250200b141c2c = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 114043776 1250 114042526 114042569
    0xf020c0a0308090d0c111203030a0b0301060506040302061801021c05031906030c15140a0305070f09080709021b01150f0f03110402031504051302180114010c0f050a1a060a 75
    0x1070031311b0000702c0c0c0140000f11558040881480035500400c5030340c601080300e9225504250035622641c20540c4a50030400041005a031030604a98002d042d401606028240360320041c1c0c04c101c07191110f012201483c01102c0405173340300f0300540c801c522280d190250201c581e00d80d117040302c43d82d0200070001984884140b0184280d410003181c010712528250410360040801d144460b0070403144a80441d031a2018441e0994105281c0e5000c6021791901c6000c9910309044507940391958451480340c140e0014442d0107402c000e4000180001a2100a12141aa5428000c6024131a03c95400c0e10300c1c1d9000b000c0303070003c4044e98000c2240c1d0031500c0340742001c050100f000300941c4045d0044101c0d0503210401a1543c4940c0200c80c4104905c8141c501050040e0050145c0d2104561120206000724801408165840350040132002420700e07108511072910b1400081d2b040070382c100900a4490890713144d040200c070b08a119100c001440e0185a291030b0b0806100400c03880e8042c0d00e00f0303001040b2007401c01 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 114045026 1250 114043776 114043793
    0x7080601033c0609031106040209070324060e0112090b01090b1c030509100224071101060b04090c030b0a0905060301020d060305010903030b01140f0d0f020c0a0308090d0c 75
    0xe18520707071089440d500241121100030840000c100c3d601ea495007010b6041c1900a000d651410003880c002c0c01d41e038507180c0d000900401d4000c09040030b0598480301602e5104070a1002181c512009181c41c154a0303c0d0403000d8011900c1c0100180050b641f0046121a84c1c240d001d09001154080d940702a0b80e420401400041c2a2180d01550420321a440350b4171100714108030044e289000f034036455034600c001d10610007903009481c100010341d405041c1a01c0380085031380c2d81c1d14000010490311030b216181c280d411143c00c03000110344c5400d90f003009030104c0c6000c4060000d000729810f401d0704120340c00340c0c08000c0d015240040042e6500041d80f117030407c112440b94220582c000c00c0140010701e0011943d443c0002c075406900252090380d941c16260040640510890300305417000d00b81900311403500b1044404501ca2080e012006503404a105840490140c001c02c40c01e40e80c03030a0654075003940c645019680d0119190940000785640f0204010b4980031411448510b256a191f00d040a04c50b19400385 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 114046276 1250 114045026 114045083
    0x7031b03031d0d080d090c05120a080714060a06061e020c13062c060402090a060f120501030503070302100203090a0f170a080901060b0313030e010903170c0708060103 73
    0xc1000c865004100004c0300c0e030006000c400a05100010050703068181989405c3c101d0300300c00c0c041c10010341e062010071000640482e0055211032456030303401d400d103080b414110f40000a000b440c452807041c00104907030b542200c2c040e80e20175500c1840345c040e01c1010041e081d01c408058800358000048911050030990702c41c40e09010902c202190311551920a00b0400049807440d40101c4080e440c852503141002e072810b0b4011b14222000d5090507a540f0005031001191f00c01c4074240002c802501204070b0103019030355003115a80703004100c82e40e90b90502c50740b240d000b194100c0050103a04d4003070011003580d100340c80c043e102c03c800500044420f40d41e40e42d594408079106840c0d00c95080010301c4880040700041c1102d02c81d9548038000342c1400d50910342580c4042e000140c0d11302041c4108101c01d030704600d01c00f80d00d40e010f00e405024841c0d40c00045e40e10301c0c2c940e003014040740900d581c035821543c0c0710703001002c0d0300310314004540340c80d541d50a200762141028080101f01108048441400c40e858250110 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 114047526 1250 114046276 114046279
    0x6040209060306281e1208190c05070306021c060806070e031002040f05030708010b010e0906041b2001050f0402090c040e0405100e030702130509010b04020c07031b03031d 75
    0x900c0724510300d01610260340903511007600c444100c5d140c3e042c01e40404045200404040410400071311080c0c4d2006014040e44552006140100f2960305541e4420b851060100390401c00b600c8925440e81401c034003030342c0003c0c80d44c0e01a160b16142401c1e001028880d03201180c125002404444d00c0e000d904441c0e02041d08020366040c81030160400c1e200c1654401040280803148120103810700c1c00c802d041c280782c1c0d954042486c80e4503014192001381d810401003070346000125060b8506548800025000308bc4004846400d0301c0c8100301e441b0306540144401c050141341e4140c01c07400503140071009007a2281203031880d110300c0220000c00c00500b00103070960382110ba80c4050500b00354036134041c50341e01841101c06844652051141d02c413503091394881c400610311501e01a5152440d65008100c2c0005025404403d0f5030340c420000304810002e50108450840080080d90782e80913014199541e51a180000d44c0c612180311000c50401c803030005104116540b6440c2c40c0042e02103207030186079503c0401c0300103 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 114048776 1250 114047526 114047569
    0x9010c0c120201141207030c121503020f10050409050a02040b0c011410031e03020109050f0313090209010522081b0f09130f0201020a020d0f03020607020c0a0513090b011d06040209060306 82
    0x404260403500422b8182c482d64400c0b60b84242c84d500411032050005003295008410780c004603c40c240d0700c4800c81c1c0694582640c04100c41d200c800d241402482517911240a030308000c1b5441d905c2c090190000680100010502d01c81c40d02c4001150511110500c002082e8040b4010703000441c01d06065001d0103179000f400009450039094842030708224003c480395255420000304074004550701c985010140c040f080c011030800d6141c01c0068001d20510a0081e02040c0d513410b040b02a074005982040500809002d9590b45400c1c69106407120200600d15840b4102480c60750300076040421001d0300c6000320b0b0f00c1c0d00c1011035107500d40c3c00792488491002da04501901c0444070240c0ca03003503041c5030464401c400da80e1010310181002030900030064074800464124100080c001d0341d5644048003550030441e488110403090400f00002003008403401072614604100020b1000803400c41c030201c04030010903950050b582c103001c000481c0300d10092207074809014404941c081c01c001540107035240f0b80d150003 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 114050026 1250 114048776 114048797
    0xb0409090f0f030207082b12060b0c010b0a120201081b0f121503010e0715020304080f0d090f0e040b0406140a0e01060e010807060509010c0c120201141207030c 70
    0xb411111520724000b5000b59008003020000381c41c0420080d02e070013541200030403807041d4407101c0401a083c030003086001c2090118809900314055800540108012070805588030031080c10180a01071600f6024400e903a08480001c8080444a440c1d01082e4165500c2c1c00e81e0f6103400f50080000340341c6103000503d000902180107d036244100425202022520100141c5854078142206040c80310465000e81d0405686150220000030f90b1f07020340ba02c420682e0400b40b41e10000f2032460150b80c0c03145000c0d1055803548141d001c00491303410f200d80d21070343d42c0c801d0840e00d551500f0032509084c42045640380c43c00300001d02003241c80d20525000341c46410049a24140e0b000100303c0310405403445440143d0320480819003c2c0240715000c01851030b030380c03142115850509120f13100e0085104bc5802d00c10001590407107130f8421144200740561200506c03a0f4240c95914107484250806000c0b40416001c0c0c4c0b0f046a0240d99105850310300034214403002d4659202070044001e009078170703800814080385070780 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 114051276 1250 114050026 114050033
    0x909070909050a080d09060b0d17090117010e040209071b030c020607060f05010801050a060b030f04110a030813061409010f090906080c04050705280504050603010902130803040b0409090f 82
    0x5d00c4464085040840c1040650810100700d448a800462083c0e1004440342d000410b400c41055040b09214021502c0345400300c0183e56052580c05000715100a40b800070886d41910901c0ca8010750007911181c3d02c5984121085d03440c0c0180d0031036201ca041e607001d88900001d00c10390182c0c000c2440600304a00b0500e03140d1300d50042d144400d00416150b5120001400165001d00c58260b000b542c0d1001407184614051100310180b0000c0c00d00005030042c10006801d000c8040014110030714050110201c2603620304188403290404036034008181105100025017134403400c1c0d14455460b0f0039446130710340a00300c170054070b03240e04010400b018090f051600003136142080c40f800c402000f0704070103450b412007008d0401c41180c00c0100100d05004060004a88510b0b2a10f00c22000b40b08244c03103020400800201914280150b9201030b074018000800403420102e0b6802400003440c0c0711400710562a1180c042a031640113074065030007441014003080240d4221508029950b60155180e5500244c1a0300c = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 114052526 1250 114051276 114051293
    0xb06040912030525050f0d020c07180e07060e0120190b13210201020705010207060b010813200a030f0503070c090204030507060e0f18150909070909050a 67
    0xc0d07008a641d0b4402c0115203118000c8810210400c2881c07607002c0c44030713010040e10500494100342a000b0380881e00e43c6195940da03044804100760a806c5440480e030320381c89030a546940242804220f8109841100c100b540058003c081d64000d1321344c05202d42642004580c01c0d8160000b01c50107203900d00c01491410010302c2040b00000007030000c50b000401c03e090001084101802450ac82107c040c60b900219010740b8043d049411540d00c4a032642a00d544224068020140098529480010030504005c826880003004039020b03210356100b83e88801405049510400b8041d0200c01e8410414549140c0d822021002d00c5008201c0001140c43c2d44402c0e405c007400e0b1404441c103074000101c3d1028403144641d60700007000201010351a0504540d50307181c030f80741c0a03c100428003114400f00d20a40d03844c0b000741c02142c14040c101020f40c000161201100c448244d43c480d460b010303c0c1c80340030118101505464803d40440005104d90fa00c0c0c445820000d201c0c9450540309400340305e90a500088201 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 114053776 1250 114052526 114052553
    0x220b041203172a04080606011b050615100219020402090102070305031c0b0303031603020f09130c03050105010c21110a06020309071d0610030608030403060218010206130b060409 78
    0x12002d0f0b900302d042c07440c54600e0510361907509188188003c00030104005030650b8801000e20b0810f114802da110859560000000b004110303009080c10131a24a4402a12070302c88401110705031900c2506031810b0741c4a10246007402006085020010007508054004200c400700620484890b20764036221903085801c0b40480c445131900e00d0001000300161fa001b16041400c0c100c000d107245040c0000c4c80600e1846c040099014540c004c11103442040001d03090b2224940060984004114480c942c00d008280310800034004c607282000200d595440f610705503003016440081c101c0004031a410b10491580b010210f0710411152444141c66403800703100521200f032289070007507105d044c02000c1506041460f0000000d240e04c25200c00b0b1401c0889201a4000d142520030400750794466400704c0241800d0707081038826200c0040c001042007030310f6000748045040c4c03030017001500d0b01c510012a105ca070242e401b0710a08001200c003401280e2051410747d044400240000307025900b0b96500040c41514 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 114055026 1250 114053776 114053791
    0x1e040e0609011401050907081e0106020c0307150c170d110301151407110a09022b05060d080c0f0a0605010815040c060f020106030611220b04120317 65
    0x2081c0040c0300c1c0300740503010b00407002d03482c0c01c0e1481d8100404101d80b0040144540e007000030480100e110350100c2098600214240600e0000e00c0da101c40d130180d52444494510b9000744564800040d01e22150703c41c62055040780d03a107030484c50f12581c03a4500203004030747d5020324041007080210346c0115148a4212859558440c464032580340030310150008625825650500c0303040106912402c0c021411510826071201141a4a2140501040d2a00d12580101c000c1d940700003003205512502e041c5c40515449921001c0c03640da140c903004141a42c1050b224580c02c15814040440010b00a030040c141503042a070403280040060351003285050209a0300361451540d4070014800c014040c8400324440c1c01480d148492800c06030307140314409a40e80304020411400c0e402a0b60554401c4d0088070046420030700521420111020994040e13114980a03612000d184100b26a11100754683d60229010510307102d0420b80b40c02c056540344c0c0711030503049080200b81405603042240804100b4010f060 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 114056276 1250 114055026 114055033
    0x5061b0f07091d010b01082410080a0609020f040e040201140409090201082d060307080601090b0405010f030302060f061809010903080a0212040206070501022a010c08040f021e040e 79
    0x6150f041601060f11504074410340e41440009255660446503c1d90403c281c0061101400035828a20600d6581c2070061b1b41d10070500e1140449040c2c0c0180b210380101c40c200720030041d85a441d0032030b00881c40354000d4408505000d2100f000101800307078550341e100c5e0041c10040307000045610b0303806841e406900f04001d005c1d80c0361203a07010b40d680290490b500c80c0310140c481c0d07a20284142d1a50101254002814114251070005920340c0ca06000cac0c840107280b08001c40b0305030b503103980c00c1d1409000800462400340e440d0500010768040404150740880390590040d02c465111440c1c401078504c0c2c000c01c450340110080031061110060300a080b0b100f084a4400010060f40d1803600a266a101400031103c071070040c0154050b041483c0d82e100e1304198100d59903a9103600c1ca00c1c040380a806005821000d00c1e24030300c05516a9500300b41500c4c60140c0010080104042036801941c10110035035000c0c10030760205c0e1321880142050301141e03035102c0304200c10049032000c00c400202665003011003000541c0 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 114057526 1250 114056276 114056291
    0x60e09150105010804020108060d0c1a041409060901060503070201090f030f020c090c0d0504050c0a030b150910120201020c060301060504030308090307111003060909081b0705061b0f0709 82
    0x20001a5030a01524091800585906181e00001c1401d40041c104a00c01d070710400c10001080f10325004080108104070f03d6400680c0082844207841c0c000b44218035000d00c003110502040d00e4400f0216100303440051601000d079003040390490302c0e2740004000303106566850580d60301240315480c50108180c0300c0c0d52481100013043c00300908100b00c100f001c42c0a04200c005115600b20a0301c05ea900b00044004000b41d07079500d60400a103080d02c9000a95048000c44401006010384000902c0c0320f926503801140ea040e80704170900c129600221203150302420721103428000325107ca01e200c00d40d907005204070b9050000c1540002c80f142e20a912440104200050410815130030070381d81d683c0004000c028508164050701c0f906881c1d107000c00d95502c2841403510340d8044900950207040500350704901007101141c80c1c508110b141c1d01c2074516461000f0022170f9882500710010f20f0200b980c1c2c01a040d242002c0d0b9202011180210084907210180106500c000d4900f008214140042c840c5040115140 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 114058776 1250 114057526 114057553
    0x20f10080f070318080c0115230607020a08011d0a050d030e0c0a06120e03070c03030302031306050c040608180705091b03130c1a030103031b0209180d17010b030406060e09 75
    0x1a484800360003100c00940710100400c0006041015424028000d602a5227040030300140c010f200d80d0000039400315180c14041180c20b015403000100303040c108480c0c10025802c0c140700e65503150040f8010941c1d88001d03060303071007240700b6001400010903003c202d032840c100b400c00140c0074800540160700064000029088000e030702e4084d1855019000b8043d52621400d920740f183c150102d8040641496000000316405c200122649203c460304928100704074200a500d2007115401440396900003202400444c04c20b49165184060030800302d0011701e1810300c1d2800740002c41400901103900c078104e58245100e996031443c000c501c1005208000340800c00d1914040c149648103030442d40c001000c4a0614540382a5542107c1c152034041c14005e501c102007400d881550b4801030b0000790020004400d0100351001d46a60310500170140055a0301240c5200d000c55544107c01001c05400040400421080e80194001d41c0c0090185502041250711a0307403180d5100710a468500c0158800c20521404 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 114060026 1250 114058776 114058781
    0x10c020d0303050609061519050f0403060b01080601030e030a080406020906041d0106020a080a1d1c060b04020c0c010302031509010308030a050c13270513020f10080f070318080c01 79
    0x2204851032000e50811114447d290301a031016001c0410984807000d0209000d0810b803614100e03c1c4508ad551175850b450315002900301110b206012500f03850105040398000d0103a81044050350f401142005040c0c0030840300741c40c010300181c03220341c3e0802071003200340c603441c0003480501071040841c40f0f20031500700410703000281603200c1011074010540c6200001c90040444411010318600825504180e00c09154050384400240b54002c013000082d0600101603030f200c680b564003c1408208400700d070820311040e44150340c040f0340f494102c044e140c081e82d8000d42c003540d00040c182400300010440b4001080c50b948081e0001d966640d0003108000940c0703131714025103900c98034030701c5828100320390903482803110382c0c02d4001c400100c07096420f91000d48441d0000741041102105060005007040d640444c9405070080041e40184d147e0500441c01d03003084a1000b070f07280d00e640c0c3c86507601c2d520f040c0030410340b00c00900b8003405c050310394040b58540800900700c4a080d60044900030342d6480d107241c91508 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 114061276 1250 114060026 114060031
    0x1060e010902070c060c11031b01020f070f150e09040503030603100c0f052808010503070b07020d0b0612030f09120109030909020d0608010f06090506032a010c020d0303050609 77
    0x40640100501c1c1c000905500800741240c0b250f007800a0003903014035010b003d01d1f1086120507014440c00c1c50001c543c0480c0900800407045c00e0302650f041940d0200e011b6210440e43c001ca203401c40c0c00e10400c11001d900101c018900c41c03082d25041011424510002e8841e90342902d050701d8545c00441404040d243c1404100429104100c0811404010080151032000c413030911000380440443c5d030259401d01c0c1c2c00d4600301c3c0b98004203109011091528042c010b040213000d402d0007032107640000b18002c0c981108403100c1d16002032a4680e00e000d1982c0304130b60b06034002e00c1a40c21030700321019040341d54000c102818400c0c403802d501989920180c01805151303501c109075044940c1c1001c0914001c80e400051440640705c0b41000580c1da0b02c10810200054203040d44484401c2d842e2882c0c4010416413039000100751401400240040d884107402c166071010703802181b440d403d98404c80030550046150b03500b600c140c0181800040030100c0d40000303210f6a4200d4065001c20303261010400140b4100c4030139036 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 114062526 1250 114061276 114061289
    0x3160b01050319120305060103020d020a08041202030c15040507051c03030b0a050607300203040305010c0504081f060909110a050907050f090d080a09080d080705120a09060e01060e01 80
    0x5484203c2c0e40b5028009804140440141603032200403c5032a48290100c542c0c8240281d800e660302c041c501300007403000d40211010345d588401c407800010314510120483d9440c0090304010f0040070100d45403080e11700e902810480d07052261101c001000c0d03d402c0c0a001e0300400010300c20081746100d0134043c0580d1076507240301d0710804584405108640e40c400c02c0d80d54040d04000c0c50491303610405034081d13091a21000c25801c01545140203140941c1c00070060054a00c100c0013800400314000b000c2d161800340340034440b030381d40100a45903246105400081c011008081020032100c4d65140004d00b01c980080040c0c40201c0704155602d044d040c85540100105000d5858041a10b400030000349980140e03070b00d42442640000d40e000b25690307020748410250b030700400080d641e5001402e000c3c142d0380d4140704880150045103003000c842c6000b80c00c518030641d8039844607407500114000c1c503402140001d0044441d00d540d100c0707000c003080403441984003100d0760314000108542404031184640b40e05a00c0075 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 114063776 1250 114062526 114062563
    0x60105030c010804030305060d05010203240a080a0f06110d0204091401060909020c0c09070201090209011202090c07030201200a1b020d0b061c080310061803030f0203160b010503 78
    0xc06183d0748844601c1d442600f6203030010f07041c1c880000141d0071098242000e0510360010007446110fa955982d0b490304004002000c0c4100c03001034060100101c850300c200980c0303400ca041504003140120b0301d03081c8024842c1400146001c42c2c06c0d1b444100b90040c00102111a90100d01400002c910313114000141681c14005081589042801410306c60503002d0701080c01d401189005544500700441c140d80075000703040c00071515081100a00070000c00702d06a00c00c1038840c00000300e402980c110381e044e1340e0700074042c03102e56a6541020001a0b10882c1e04070110340d0380b9031b02c40701c5035103e030026200c94001d02003080fa13642c4a14100107008030300f0180c2c80390350755074021441001643d541e00e040c050180c3c48035075007006641e64030004040c0d580c0300c94240c12940b101204a010040124021131007944204110024035450b558201d5400606407404903065075030800900c007190003415030001c2c030768281c8104d91815075800c0c1d003804503180b4500100d4034001d94500510280ca01840600900074040700c40 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 114065026 1250 114063776 114063793
    0x1a040b0109020c06071b0b0c030a180f301101060602010e0601051003060f060309020a09091101030f0b0604080303010801050a0c02100e03070215090114130303030b0d0501060e0906010503 82
    0xf880c1c46400c05400d802c14401c05054002c40401d99014a00e2a03c0e00a03910004919003100c250001d58000c0740c240700d8840c5042d881c8044012413204c13411883d87c2003400817000c4c600e030740e036030404440e012040d209031503548001400c0c841e029099038407000891303a5604560619444101800d482481c2c20007400e5905002c04a0302602000450f24111441140c0003580c10829160a800070300c82e036000307100e4000c105040401da050301500000da8051003980d0903440d0700c2d9121038903003c6581c400d40007003555050424101407507200e6005081010180c0100041c000c2c81c10000031810b42c45540080030b250000300042016203000e119907036004c000346609021050581030001d403902d0600c15003405160303a5803e8400300b080104141e980595014180d985d112900c820060800c3d0840d15400c3e0001d040200969104603480d000e40c1c01e82545004480c200c5411680e00341c000e401340060143e00a920150010b002c00d03030034054080100003110071084503061014940c0e041c40e4058200340c0c082d5005041 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 114066276 1250 114065026 114065047
    0x302010c0305070203040531050106020706090e130b10080106090c030b0301050106023a03020d230a020d2301030506090706050d110c011b020705010315120f1a040b010902 75
    0x1230448100c0b4030b4020f000d00e030030303455841d0190403010920a00c003201d241c1b1001148081d000258603068414540322001402c1e070b10301c3e0b649500041200c410386007010204e0007000060440c0080c03904070003101c1070714008a031242041402c580c150341c0f01d00d000e10b40b00c074150020aa0148074501d0300030350540083c4060b604048020b076a800035092100f0403074032150200c400385d01c01c00301400711514401c181c00a90a12010004000e504002d103081000e500e00109042500441581001c030260704c1c1d5108000d50f03a4600c507010081d0004041c02080310381f202d10758010340f5a0105421364400d00780704880d5140d41981031403407030084020421070b03a41d800104107105141d08041915000c10125102054045c4003056120303550290b248040c61541c204080071800c0024010401042a590f070300700c403825561007004409a03000300300c4031000707a40d88240900800500c600c01020540c0a60000c28003150b0a646403250602220484071107401300100b440200f0043d13040742401040c80c1c0106500b0442c0303101 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 114067526 1250 114066276 114066289
    0x18060d0f0201021011070b01060503060a0513090f1b17060a02090f0306070918060b16030203160507050f04020304052a0d0308010510051c0f0b06070302010c03050702030405 76
    0x2010300050360038003100c81168803c21009503490100007052022001c2642410101d4000400c00c80e40d40c40300b0400410000d100c1c60640c0d03c9004000c0ca090002d900d04414811a1070b100085001015100c0004030f020803450100c5412040c4985004054903900310305140e0b40c2100303074009401c002c40c800304045000d04001680760300014140001603545181100064041a000003a1601406400204207011340c000045100715100c1d900182c10401c03400d40220211a0b441c0a4259034541c03d00c8580300c048610389064040c18440d004803854a0b080e503400c00802ca000341c00032100c42d403040c0c0040c0100d080c29807040e042a4010f590550a504241d943d4039101d00119140c410317060f184081e4072004402242600d544041c000d016a80490340c2d909000384404024002d450142d1140d0b950700c100e03244200f00710b170561005400c2c1110114001c070b400b0005020b412140800180c6c4909000304203503201f80040030114802e07000040c1c1003440000250582c0c00007003d00d81550028001007200784c4441 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 114068776 1250 114067526 114067549
    0x30c030d08041b090f0f0c080603120d0b03033001030804050603040606230a0b0a0503190e010c0309260901050c01020d0501030b1806090309040513020415051806 71
    0xe00f101800010b000c1201d01d4030352103030740700755111410550000607044543c0e10500c56031258441c01d011302d5020b0281500d401c0310650720150540e011401c0304017807a800d1805443c103950311910118403000c0c0701380000d285402410007a900d540ca1041c40e0381000b01c0c07003580310b2220b9440d0001c0e29125899a2114801d60041d8407906004107800800201080020350000020346800320180c00d8001e4410250315900c00102221070103491022804526202c801c0241c4e070340000b0f266601480c60765402c1c007145000100007030b404801900d8011041d203d400a000e102030381584da076000568581d06003000010800415880042e400303400c10b010f00d040003041c0840307005150038205942d41e2000c9440c9c203402071160741c505248052808002000308034001700a28080d50262000b9103900e88503980b083d40b55172050700c134910f0b0b6074010442d60005082980042d0740c003100103280d42580c1d1103c3e401040c103540705104046014110284180b0051a040003108003025014407030b9480307813405001052591252 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 114070026 1250 114068776 114068783
    0x20d02030a030b120d030501051504050f0d17030405061e130201050a090308070b2a04030615050d030201050702190203192d0203190302060f060105040803040e06030c030d0804 77
    0x31002d10b100144c0310004940c41c034040d40c2003240e101c0000350000400409080c002c551141201854813004d16800c2010740d000e40740d0050103141c0c00c00c440010090110035415085980481c072003d6285016480d4001d5403003240214040e10f15803800da0b1102c0769207034030707805407a007580481d00034808080c801c4000125400d41c2070030310a81d41c1040344400e0b100c40c0c1f410380c001041450001081420010307603143c014054900031800c00100084203802079030b01d00b11361445801401080c0420408102190003551a0039050f540102605440380b020946442e00d06c102500541e45031405d00940e5681045490b00c405527511081c4504441030b40003c0c0c0751204101007030740c007610941c162001c2c82001600c188440300650030705000042d10302c0d0081d013150110001684240501a0f1008410344080311043c0c0041c0c2c903a0240001e0f41d918200d900d00e110b0301a10560401a042c0004905640100000d00c0901350080c00c00149182c884201032a10903030240c00d500981150040c12202d50300400e074540c000d81d0 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 114071276 1250 114070026 114070031
    0x106080406230a0f021308030405100302270f060a021b01090501021b040f021303060b0a03080403140a12090317210c0705030a090914060603150f0a03080a020706020d02030a03 77
    0x3c1e680144c0e03000c1e024240040c5040031101c0c0c40090520070000c024421076105442e5181e0004072000160101d000e80881c00c40c100e022a00b212050840341c407541c0594000003845400510b42c15030204c1e45982184403c4000359200c1e0400030403101076a60020112102442c021180c1814400005d4442404813803c4440c08038586070210950351303e40140a0039003c03504110748442c40503803030306050300d10381c071040e20041d203404004000d074105000c6540680c3d400c0f94016152500e15030724001c00c04040c892422583c040c032151030001804140410000c000c083e40d44000160031030411700c044411801a01c003200c1c01c03c000313500d104d10030004600c4031051696040207850b42c1c1c048282c8040d10a1100040c00b6000008030226400d82084444007590404601045094105410164807000549580d540800e09000151141d9184c03210110408030103000400507000840103e49000115042218075840111310f00c0f0209a0411403000140140d100811641340807110194880c8544030f6002c2c109038 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 114072526 1250 114071276 114071291
    0x303050a390309050303040b01060f02070b0405010f05070c03050705031b0906040e070314030a030c02031201031e020301020706050603060c0a080c070f0b0901200c07121a0106080406230a 82
    0x9000f90b2040c0301050b00300341503966038602031506000300074003401644082940710038080340e8140b001446609680c05c0f440814605414040150341201c0340012003020040304110f404005075620323003c0d0004602c918010982d0354100010982000c507240c14264189101042d001540d582c0c0c000140d4110300c05560006801145d04811801e20075241c001600b0002003100c0d18140c1d44c030000080c0140c0300590f42c1000600c8414004a0f100c6c85018140d1890703105100041c00840c040c00c80d84154a511114180c005800c130f0b0340481c1c26a00020030a9960795610070400501d41414403480b03500c180d558031013507e840c4030300c2030162041c0c0001c3c0607840c11070004a0418100065600541d040c143c214907100c030300e441c004400a020f000000c1e148500e45030115408115686108240c41803141614007030281c1500308058005041d10301e03001600c01060500780301420001c00366059010b080540d42c0d080c024941800c01c9016140d4003900008410324400c5502030320f40b1141038036504030209480c04a03020 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 114073776 1250 114072526 114072641
    0x61203090503010e120d02070f051b03150610030506030102130803070c0b0c060109050604090c0305011e0213090203060f18151c0305090a03140309090a18020d080f070303050a 77
    0xc40304407004005110b13400101c801e640d101c040602e100bd00440407265184000b0040b10308140d402e81e803030b581000c042daa05040b001d0294001e07980c000400303000103040c00e400300c107840c48160541e805441107410028141c0c080c01011508040902850401245042c03184420f00d940c600052280c00c19407655880401e20390340e00d942000d00080e8016000c0c024030f58032814840c0c02024902440241c0b016412071541c044c180c58020b80d104074081901c018001480d00403400041c0d0b0004019560003c203140420816584060060440d126581d0034400f081c41c24044c0304410300000094075114000c5c5603803443c40c1c982c4544c10a80170640c10328169486845041c045001e080d85600000d000c41e560414425540d000000505014502121099074540302c040c0150300b12141101241514050180751101500b86030408c00d0b20310f0f101d140794030310746501707207403515070703075003200c941103000a07291000e2107070030001c60141c80c07281441036040d400e801034600641080c3c00c0070f07a50600301c0e044c09034402c401340 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 114075026 1250 114073776 114073793
    0x909031b0724020f0c0105180f04020f04050a06031118011e021c031b0e1f1d0f0f09100905041401060f080304060c06061203090503010e120d0207 64
    0x1480341d0007504020100c2c41c90001d6280500d4280640107118440c0d01c449400c10010b012040701006848240c980040313009600c0726107003a50001c9411550f40c2080700c605444910051485c000501ca61a0700c0c1c606050401c421010241e00580c00c060038550031b0065030460500b12480e0040d02079409000b0f12000005035010752511880000d0f20f00c034200d140b400c107a000318000e5903005068245c4c6c180814580c40513070498150010b040740104441040031500340c09010003070881c0000408080c2c005100c03086003e000104061180005100301b00420480704240d180b101d81c40904584c0c4001d44103003580890070103028400c04070300ca00d005c0404103c4501420110b01e026040d114018000c5103004d0412050b9400b070b060002c02035600c1c04c1000100703040080e80ca5410364400b10081c40c5080e1820b03504680402201c04241e0b0f80c180e80c1c0b100000e4803211400340d03032580c0c3c0c803a449605c806407034041003500712110140128201d40002111854081c207a504a802242002c040140c44070042d043c00d021 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 114076276 1250 114075026 114075029
    0x10e0a0609090507030203010b0402120c161e030909050103110d0201031b020601050a0b040605040605090a0509070f03110307020c21071211010314040f110619020c0909031b07 77
    0x744903140150b11030034008003181300d809490080d8001d000303807040141404102c1c880da550b603050f00b13188100451059041c2c18003c103848c3c90341050802d1146402d80310000c109030f0000d0b03906000104c1503a11800c06030401190341c000c0c2011001002250b00d5038540c45440d002c038200d040d20500121072308004581c02548032000c030402150f41c000e0340d200d2060020b03550340000e0003020b104000007400041c01d2141035080760191086990742500781032800d1029070b52604008039203a07001c00303024004071b80c030f4940704413880c0f0840d855601d02d0007141d261800078040f14952010820700310307010001c020303041d600002c801d6030850042c0c89440002400c0c5d41d504013043c20f0200180305600545a00084082400f111880c01c00d001e214401c890a892100541c2120045e86e803080c4800507100000300414a084007642c0c0d4140126800d0b0008144c0200045642d44401d004401d40c4200c600340c40745d429810410f80c00300708826141c7c030ba101e080104203640c0e6030203804100380756004442030000c00040103014000 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 114077526 1250 114076276 114076289
    0x160914010212041401020c030a0c0e0712021314091b0c0f0610051806010f03050c1207030e010b190909081b03090f1012020f070b090309040e0303070206010e0a06 71
    0x10b840701c1d21211a2008100c4c5400100d0041c400c0d0300d8003031504c0c42c000c1246855141d020460314000c2d03142101d018224040204003070207000c0c0e160010003409a01d80005c000d443c01c3c2d0441c1c0c41040d81000f034400c1941b83d180609500bd0b01012041290014094856441c2132407645005a00e03034000c3ca00c198602072101680b05074030b0040304144924000700d4171020042d9003040b80e140ba803030700d9403400500c0100c108541880c00180d02a000460701c4c0d029501054001c4452040a4501160150354050344074041d103082c000030b5616519000b400c1400e1003028010322040310100318078040341e090a51083c400340240c240c038540d1082c81108221081c0202c8007064403171b412040b52200c1c03c081c0d0b10b1712900a0035030140070764501404036201d0714107600000d4203a041600c580e132a00709100902e00c002e4109511100460b00e041000c00041103043c81500d01c00c00181000b0b40e5103400c01d07000c0c0401d580080c54651199807003403085c420556000705444e41910307801084031400307681d180c0c1104050310240d031012 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 114078776 1250 114077526 114077563
    0xe0a0206030a02070f0b060a06110c1c05010507020703060e190206090301090b090a03080a3b15150901030f030f03090b0f0a2909060f091e1609140102 66
    0x640401c0306c0840501d1080ca811110181156982d68095803140d0000f113500c5500c0c2c1196441c048146060701c3d8194030018040039040c0d0020460f40d81e00d084030029560000503a2183d2020002c020440c05040d05811015010b094548120300b030442e50b2848583c2d000307200314808103c03e285a00c09501455869401c40403013069410190059501c070f810b00c0b842900000c03000360014043c03108500034140c01304610510596540800300000900303030001c0b00400e44091a03001d403052003980408c100c20745601603000142c1c05081804824000144104249015205c154010000b05203881841004550035003001c80c4026455032046000f4804c17150b00404041901c0107010240d80b11040c0d1510402601c4004c01c08108411846568090403d40755500041c000c042d00b01d40341008542550031880180030045e010a48030005030103003104448040031414010602c4021200b082d00e40340c0c0080301e1000c03001240b446c020000309015154051800032300302e07900f10700199901c200050f05004c400840c80 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 114080026 1250 114078776 114078803
    0x11b02030d0c050d020115140d0605160e0d020603040b0c070c030f02030c030106030506180102090406141903110d08070209040303050105010314010506040620100c0801090e0a0206030a0207 83
    0x41c100c00b042d000c0a80d034910542c0c92203086680140b09450059040825000c4001d180c5840300d40c1c003100200701305400c09481d042040000b038a81c0140d500502850440e211107160f8804020107009040066a02c140e10030144800561103010440c0d4002d900222610b00c0c5a451108000c402c0c800d4150041c80c51480c280c0000a03c1908540c14074468404c030181e070b0390240e00004045c01d075a06404064802d41013240801c845032500003a0f150340c2c4d01030f04005407c0c8498000007504a5406a0010304d07460b003914501465864080c030f0320710041420f01c007001d81c02070854507210612603011100502400b441580e840a00c07a2050a03102443d5004144281e18942460000c0c0944420f02c03038903000ca4102141d003a998100160114181e4401034411420b05140520403a00c000040078500f891225400b811480e16800380107091a60386498404100c0780d104082c000c2c030011050b48050b5810b8500741e003c4031103120100d01d44001980486401d5141d803a40c0e101c0100138810080c0040002080701007 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 114081276 1250 114080026 114080053
    0xb0604090206130b2718070306030203060115080108030a08130c0b1812010603030203160201110a0503030106020d0503060d03083d0b030705042102040f0b0910060e011b0203 76
    0x80c44d0402c42030300a002c00c600600820784210420385105d41d8070561700082c41c0790440e400319449a12600030300e00820299565004282402802e8005a90066101c0c010004182c0c000080500610782e240065207003480e1401e00802c0560042c001e20286401c40301540b0520210344c01c040c1c0500b0700781c9146507441c02d410501140c40452428240c0c003882031075260882e0450188540f2003120342680207035180040c90250711010401c41401207043c81007034009036039103920400c84521840c0c422002150703a07504000001c0d10388078455550380308101e4100f04021868035100e01e585c2034a981030510f1038142d00c81e4010b16440d8290500850502060540c03ca40c0c000d200300d05105441c0303849807001d1681e5860b207034825640c0c4000c0300e00c4808200100000c100c540200701c00710a105040a048901240c240e0340000c0a0740c84803082005540e4440c60800400d10782141410b40013000c24090038903051410031b006e800242c01545040c10721004920144540120014032109180d008003074170b005414100c03 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 114082526 1250 114081276 114081299
    0xb0a0804020a0605030108120d090602030106081503120901120f020a0c0303140f0412031410031b0f0b09040b040c050304052109150d0510080c0402070b060409020613 73
    0x80c0d060344200c0b40d00d8000a9118040e6040b281070342e407032201500f81480f00c417031041c0345075000d0368418500680c1e83d468a07010406c14805140601000e83d140d45050510b0342103010325009400225100c1e070084081e078080050a4800c0310001340303007801d010b075000c07135169101c50003000b080413000c052500009070b214001d03511290320b0000a00c20f1f24100009240b40d4085415001d013255900b500a10303010100d008507172622240c010354416841d0211301a030304c00c00782e1000c0d628140c2e8030461248410b1010f000f0020941d881c0c108100004100700042440c3c08000f1550544501c40c030b02c260100040d0740000b6483c1c80d00010581c1c3e40140007803080d19047d05c0c0c000c1841c1c2c02106c060b1440d00071500c07004902640580c0e1403000c0040c9400d4581041140c80420418140c2e81e440e42038a200d00300241c2c00c542003a13005261164000715504141c851070801c0b814140381220881e075100b28410823100780040c0d081e94015800c07040070386000403824000d1010912070312070010668070003203083c5030019594003010b = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 114083776 1250 114082526 114082531
    0x240c0207060f08010806010b0c0a0618060509010209090402091308040806040b06011407060f0204121110020a0218070203070803010f180612060f06150302041a070c030b040c0b0a08 79
    0x1a550742c46003101111080b2020802801a03241d0f03900020010131555648002803d40612040f0945481c51490358400049030800e080789480c82d064401c40d01c0034000c4600c2030030360190089009514010b000d41c00a08007070402000288200015408600b14840000080d800140e02c108615900e0340c40d0202c05039550022181100c1c0d0074542400200c0c42d510490144403d02012803a03582000b206680d0200641601039007031000550a1100003402e0101c440030100c141d00410040d46110320074014009003401c4441c0d107800b507600c00080c603c010703203070121402e04d200060388030001580c660b004100e0a5200300c050140121402000120304100e00e1040c800848252032011121b03145400308420960b8000d02c12600f0b546558001c50000c10507a41020510003880d480020f10a40c0b1070712100c03980d2a583e0302c45030009501140600400c4c92809103140d12007440035109040820640d54482d07030308494000144010541c1010800700504138100d08040c040c02c6c800c0e19110f90900c074004004882c00c = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 114085026 1250 114083776 114083789
    0x20d050a050105010c0803040b04080f0a030207021531051f0f0c02090403050a1e090504050c07050307120509040501030b06010224070c0302030c010608010506090a0b0d240c0207 78
    0x2070000000d03056020703901058000d80c0c02203003541555070f103403108045044000c00581f0f0400e4200900c60295480c85c00410a0003041d460040c0c40b107802e801030000c080700c03400c41d240710b05c20100b201201145400061130030071501801585c1020b2a00e40c1c4206807080d07158407940c2c200307000003400380420650b8501003500d220550344400303608840120488581c0c0301d070f07040a5085a00b01d00401c010070300c568010700700701d05241084c03e01032074030780034041013480091940400940d805005114a140a00510b6048000002010f00f0300d40c0b00d46401c1e80382e2254031801051007240007050014076000308182c43c815600200200031540c0d42e030900180300700c0e0440f0814010f010b411912103081000460300c00c1000ca5a143c200b083d56035902c0f00760360783e2407a4034007074040d0b200500001345505024013a01c1c0140195000104103403c00c0024441140d401130561132030503040c030001c00c50395200c0d01003001c54690029100010040b000074800d4004120b4400b1200e882e060180c072090003500000c420003142c03007 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 114086276 1250 114085026 114085031
    0x1e0e130522030507020d140a05010e070803040803160c030602040b090f03010e0c09090c04110a0207051002030d0c050c0115061119080703031e060911070317041401020d050a 76
    0x1c1e0030010303400e10008454001c010503c18014107015041110403285018462000d4150a55035844c40f186440c0c0c456200301d0303440c1c0d1128000000300d0028800c1c40004e180400c0114107260074a0b01c099220300441c042c46940c044c401429905101a0f1a240801540c100004655075902c440c0907013420340c020741409002e50440006940182030501c6042844250007020b801c194541d1b0040120004001c0d001522030720658000d142d2070381d514070425011078014410742e5510901c0c550701070b0070114503a05c103e01c40d180c04940e401d0700580102c1195501c0a50f9080000e0620041e401a50203000d280c9205100d9032801d4811030780245c8200415007074030b1312500c908541d41e00c810003040e510488031440a51b00524581d500c0f0024440e40c0142070014868100400d552003684001455140400140c04202d511500308010b0403150348122030110011140392881d1034415200500800c00c80d104a60300c00d0700d804002014031851014009003441c01400a55440103403d04c9480909020303548551204e1 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 114087526 1250 114086276 114086311
    0x2070b0c04050108130204020c03120a05010503060412030c0c120203030411060316080a140f040b1014091f091409010c0c02100507020a0303051215011e0e1305 70
    0x1000030003510211041650395041d9a40e5642d4201e40e020701e0240c0c00ca07007154003400750038600201403000c0c055110b2801c0da001580d141c5202c441007030b9003060f4800c6000e40c2000b028003002c5000089410041c0415080210b00c0e0088640d08881c140d100744030107001907100305110300c10302c7e81c04001980520700441101030188480d408025161006a481c4400b0112007c0389104190148140c554454010b60b8001100c699150656180301c4007141d00100c590a07070006c0004110344102d070707542c0010b8002e1507588130038108a1011807062600301018498442c2c000024900056903400503031b5000816114480030355600c0480c409406452071070514043c07420f000801480d014403038101f003038020b540c0c0c0c4003000c28550240103010039580805410400100310b4500961110721181d0000e61081ea1000c1ea5600386108240041c54060009040c010441194031000d80e880040207180301c01000800003a10704005003030360705003002016607400000d040795212401c203540e072000e489900074201126948 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 114088776 1250 114087526 114087541
    0x604090f0e06010501050d09080d02030a05070807020f030a03091b091b051201091d0f100f020a08060907020106030512030603010b0d030c0615050607122606042c0102070b 75
    0x40310240034130f0b070001e90140031200c1d08810700c0d000005054016040c140c6400b4020000e0401d0ba802192510300c290340311804e11402ca6030100c0656404003003071028044d80c483c9190860f45034882c2c803880d0401c041c5ca40c1134032130504c1203942001d00d0303800d5050340f070806480c0d03502c1141c0040c3c1546420703005405400d40d0b4021416001d60102c0e642500c44080980880e8203009480006003120300d4030b1480d4100340700140792035050400001c00c0d084000c9000b001c403191486286015505403040440f600382c010702c441c0c02000c0d0414001900b0a100319424082c4d65030b6050b0490041007241e20141051043c01c0800100540345c01c0214011701c01035000740034100f10340052007420084417500800080301e402201c00031800c158014a41c5500e00e4940d002c810340d0319030000d14141c02c40d1030251145140c565407030f080c16800400000d0701c4034240031011140740c04060215400d18004120354001c580340e00c040e61360860680081d501e60f048003407944610020207064a030013900990012254001d4400c00315800303 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 114090026 1250 114088776 114088783
    0x60507020622080304141306050f0f030c131505060a170c07080304030807170106091e080d090e22140106090222120201020307120e0604090f0e 63
    0x80a030058201441c1c030b01e58a00740d00480c95040d120b14000076240301c02003440a42071000300024041d14104142c0c0d00d1200341000311110b13800a01c40a1140b911000b04150780300c1a449011811049441c1541018600042424601c0c03003156036500c5601c1c4070450700d0034070b665030003041e09000540030100e10302d854105201c528030030f403503a207008520280700c500400d00c51400e4a6030310510201c451800d08045030717200d460640041d1412804903016404019a665010f000e40c0d50a20100c031034611b255141c260042d203100c1c818028816120100c0c41c1e2403003041255042034005082e04001c80c1c2c151907210400500b0000329010740e0554100040100b840500036004800030084240f081c1d420304591503480c80d00b0a07031000d141180d20754840c0f400043d600c90600c0544030800d8002d0070480c910710080d04060511100360040d00c0007210790b00a010150f40c1c00402ea0380c2459100c405044180002c20381942d20f400e055110b9030340284009404200c0b01d002d80c103c5013005820150600a613160399400940303 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 114091276 1250 114090026 114090037
    0x10b070c1d160203190f020105100b040506130308130617090c0105030601022b020d02010e0615130504080d0b0102011b030f020409061502060f010b030f18010f05100605 74
    0xc48107400001c01c41003085840301d41c1c0d40803800d004480c0740400103c01000d21070b480e880c0b184045860309040c0498030b41c0a0003015030103040da00015295a003402800c40041c010340c014280a1803001c80c034044804400908040070715044031619403100e50000b00c2919a030101d001d42d000280c0100340d8001c0400d1101c60040c0608161000381110050000c0111080d0304010482c0d030451050542800603241c40b0b640c1748100105503012103164a03a0801c01a01d0404940301080031a0b15110481200b000b0208006420400740c09600074803408000006075108034515030700807143d182006000c10000c03500020b1007c0c070140791003800080c0c4044e00590072030f400714004504400d03000c1c2840100c81d110340d1100d0040794200000605044e140c8101100315000c603085401011a90f11140b41001e8040040071381c003028103004500c440d810b180400b5240d00028103040d24a4104c07401082c200510300c2c0140c002d681d100c0008100b130a51024200d0050a01510164030101c90041c0104429103d04211413 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 114092526 1250 114091276 114091319
    0x1404021005070b01060e010e040c020601210b011401030209030f06010e0a020705030a180807120507080c10050906070f1b0501020d140c01090c030317070309020a0923010b070c 77
    0x3c015078a40708055840741032a204403410401c0403410741c0780a0341d40380300d4019424110303030051039250b0520001652031400c0540703140940c00703090403100015080d10180ca05403201c04ca4103d00c0300e404a00180c0180c000d841c0c026505000d18090101c8070b00000030382e070741221041c01e001c4005441d20b440400491080c0314016186401c10403103890100d012f03128038005200c0c0c080040552a40c0c0740d6960b41071200681000900c0b07080f202d802e400b0f004081041c44080d2401502400140d00b0607000603000a0501c0004014400082003011183c0e684c1d400782d410703194000001116281d80c910349081941d03414000d602d089418800003007402d520000c0d90b00c450484544580401c1e003254100300d81c8540250700760203807964035a03d000c00007070340c80801d48000718400d866400d0f4a1003060211070f44002d009269004162619103890b0150780c8084000040381d518500000742a55076000000f2001054044c03058042a084000650261042c0040030b401d4020004107945a880d850b12200d2a4a1074880300c = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 114093776 1250 114092526 114092543
    0x7061b0303020912010507050711090105030606011103040305060106051b01060b0421150b120105070e0402031807031401110301050a0b030c0d0e210309100b010201020904140402100507 81
    0x440028002e600500160100803c4030082251302803c250075628101d0321980028004900c0004000800300302c0420094110390003411581010b0219a5030000240070f0340c100610030080c20018232080c0100d402039600003090b00e03d10f60b1941c202518551014000f0811848030341800600c081d010301c50b84007555008100c0515207031034186081c5071800031400398421700c0f40c0c461103000012007200e29040000f1000301e01044800503803080000503080b409041100340d050200300310086a06c40c1c030041180c203044400580760b44030b0f403c8006c50b125101144032000d101d02c6070080f051051854003020a001500001c3c0828101c4510303011490100b841203503045040c0c00c07024003800301c00501656201000441140c10b05454402c4031040c1c0740300c4c4c0d0010009404c0066565103001d003035070701101c298013503204082c0345041c04031555640b00b6408080c4080540e03580c08543c41350380300f90100d4440002c0103105000c40081d8070b48054000320280c4040380b00303407a07528a00380c6c41340c061801da40805400c206103 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 114095026 1250 114093776 114093827
    0x51308072d020f040e1209030c03060901050601090503060f1308070f030c060609110f0903010912030b03070603090f111c03020106090507020c0d0303020c010f02030c18010e03100b060d05090f0706 86
    0x1406065081039003a00e5050280c1000075049c0d0303c0c10440d0318490701c0403070004246400d09100140c1080c115812260007504520b0401500000e078550392500700041003050180410302d424400d00d1350144001c01401130101d010103109143e0300107a0313401071a0060780100f00b99603640350404c084030320a881170a5510b10510480340117040180c05840180701c00303000411000165a90051113100c0c020045000c04d0fa0340501218a00b010000d0300040d1006060800c102d03070a684034540b80c070124000081561403250b5000c0201d0305e400c06c1400da034180d1440d0b00b8400d440b00c0e14010340a0040c0d4010700002e0380c940740002e04003910002d1144400c003800341c070801200c846601c080780030350b12214100c0c00942d03d4100b400506800341c0b0003144100702e18190103446101c545e9109516401004155040006041c0501070035134000c00c4100a41400000000f100c22100e40811118091848080d03000c43c40d0404204400601280a058140c15082564003d5071030f00c40940c0c009200d100082c04c1d85050050 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 114096276 1250 114095026 114095053
    0x506030c01050c03040801020408030703030c0c0809060c010e0105010801020a0809120403021e0904060204170a0c050d06060b0309010e0715020a03030507030b130b13051308072d020f040e 82
    0x42074000e5124013601d181c15150a01642a644290f00c507141d154000034044061541c9072145003034120091030f0180001816844001c00c3e4001c3c00c1803d881201c00003481050f0000c258000e090000031503000740919a95046028001c0d0058005980030401201c0010546075001c1400d0381c001c0503030b212040c146410340d02070101c1d280c0c100201c64542031549120780115600d004c41d0701e202d2031269402603500c07401c1900c014000b00b01600c0751081d95110040300c1002076010783c0d500301594404c2d501001880c1407410310601801d21680302c6400b48400000f4041d4008040d0051180c806410040f07840441c5da69403050318402c90382413901d005130410112900040d100b50000c1c0d0b00b0040d01d00e00400c429180c5000524500c114904403040385079101d0190590b410241100d41da0a10b035500304101e9440c04100070111182500d6000f404d140c40011044104440391070002c0c0f40b0b0300ca400c00b819440754006004882410301034400d07482024600003031007a0745064051103045181d10b070098804100e006c82c = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 114097526 1250 114096276 114096287
    0x2130e07050d0612031d03100e0c0409060f0c17060f0d0203030307030c02010f0903140a090b0d0509010b0f280b0705071404020702100f0512090c040f0506030c01 71
    0x30040810000104000901c00910f8003401000e1302111505100051161402a202001c00e1030f680d000304007101006d50071682d0105501c884260409004928109034161103400d02c2c0c050b0031240e500c6490b1201c0f900038010385034001104000f030000300b00b100080c0440c00ba65910158030500140222490008006051400c0544500100a0440c0c00002560383c0082c0c1907420486038240065139404103c08c050b9424010040354545402c000c100550041c2c4004205200c0a482c0015002d0001150405503204030078103002010452801929900e242041d0b2010b488160303590300c1c207582800401c800d20303e0403052140352600c005003805c0e800070100000d81250b505d190601c0d01048802c550014042c8807580c0103000031441003010740b0600f41064010b80311400c3c4149501c0c0905e1060000c4c40c0143c54030b00c1e01400b840540e05040204600e16903040b5260320840b02780c11207103079402c000d02c94080000540e1101c112001c5806021400707080c4031850880385c044601950650004582c13840650103003 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 114098776 1250 114097526 114097531
    0x604030518040f020c0606150f0315060f070c060203040f0e13050d030f1104030c0e0c07050706080103050d110c1c021c02030f030309030f03060d021002010203070e0402130e 76
    0x103071514140c50000c0000342103070042410a110b8a8000541035041c40051000c6a4000b1048810507075030300d6107018000ba14010451201c204c258000041040d90010801c10a2000d00c020305035661805401d00610160300702c04000c0b030301540c08200207c1c83c0350001c41903500b5206844041c0c03c0c400e14106054003069009052940c403940076240c0500803805c1030000d41426091030300c002c152407590041c1038049030050000515038440c10700c414030000b100422424221101d949515002c0d44500802641c14410404014801d20541c140003c50581116016040343d01501c240c400e0f50400741820784080040e0803402ea8990800d03448400d892a01d08002c011039150a00f005036820055030201e50b91082d4400258803200c0404040340441c42c04104144080791164091800d40c20003580103a80d03405401105200e030840800050415142c041502c1340d0542c000f170914400240d4800040d000b0351040e11050b0024003801240400340c105402201d012440e200710042c0a01d1030004500c2c031840c0017 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 114100026 1250 114098776 114098797
    0x180501050d0c18030318140609010f1b0b070905061804020c1e031308030f04030209041712160c080301030b040309080f070501020d0e0306190608101b0c0506040305 72
    0x1000c2184100410f8003000550300c45c0e01c0e41007482410446410310625507501142045201f50504d414039210402992150756083c2040d6100c010840800c2d5030055008800b03803980b0f40c886102c50180055509014020705498440308072268694041c00441d20805000340b1a00c001d02c12a50720700d0810342d00501c582e11016040c2c800c41d0300e5801003141c28648100d2a01c0c019800424894650f0703004000b0500100f0088004500c1c012114541303c10340e0107240b00c040d10960402d0000307405d200e6980c680c150046501d828159848100c8000c0708411401643d800c0380003451f113201002418001d84102030803e03040711155042d6032959030758044075400100110300f045102c0100062034070f02080014511f440703400180c4012820200024580740140000204000316140d90706090344001c9034541c1c00ca91903100f031407112400840180041c0070250312081140c4224070341d0280700c1400340d00069002002c3c9000700c4101450310390803207064441d1840545030703030040d10205001a000d10014a0f04222 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 114101276 1250 114100026 114100037
    0x507020f010305091f0f0e070e0723090105070f200306010f0b091f0203070501141501122406091203083c0619080709110c0616180501050d0c 62
    0x2050940b0405241f41d03109906c00c2a09102408402e00b01d903622101618040104500d00e40d00a2100c518044a902c1c1d1854000382000707040c1d205030103c603c0d90b9000000c0c074295505610388450007070303401019140802001051240745207030204c0c1340341c100c1b901c1d90011031180d410807255481c2c0740c1c0030149940e44189d002e00c0a8602c0c11030b122803805981c5498000e140c6910035410a2825a80044000200c00411104000001190720000080c4104c20319001e0051441c41c0c3c07282000700350001d41000001c4600503088003400200451506840499403500c0034503581d00184c41740100c80e920024042500480043d944042e00b610a0800c490510b2500010000c622107901c0c140503101d29000c84e40d4611070030040b05081090b91100c080407008551301c05140341100281d1612241d00510310050384440c004112010000706035411101362600f5500181407024201c080c4051980941010400e1442c80c1102c2c1da844502417802c60b01b040e101d46107065040700c0100c0c010146100f04000f4001c = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 114102526 1250 114101276 114101291
    0x1814160c020d0302011409120d0e0c0405010e0a0e03090310051b0a0201020414030d021c120204090f0e07140d03091508190204060e0d020319030507020f010305091f 72
    0x2a070301c2e1110820079000780c000155111440003500c180103030080005c5800c5c1d02400301040d03161403400c01c5071180924250002450488010140c2c00c148682500c0c540c4642850000318060001c505114000d2411500030044841c11a420136140d0080105042c0e15030081e0005a480c180c164000c7c0e42d100b80e2090341c41c03900940500c0800916001080c00c0c3c00140e43c0450305002d00c03d0452006840f03040b04900500c09035402400c001d6403118060f482105111a04842c00b07802400364001c0810a0031020055464a0722010384400500f1200e01460400f42008942041150003181c3d11095031440100050034090481c1030060608084d00300320308016005400142c0340c889181c00296580c81503030307401480e04002d20204100044010718125003441008204000d5401c69040340c4440400c0d50581c2a2030380c01d00009050030400e8640307801010704401f1100070558400000c145551084400f03010007884440118201c9200f142c8401c40341d404018440051451001c54060302c207074010340418504e = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 114103776 1250 114102526 114102529
    0xc04030203060403081e040b1f08030c030903070e01050603161701081509070602031b0a021819060308030105120c040e07050414060303030403051809010f1814160c02 73
    0x100b0115410750024106106000d24011100d1000c518042810300140d0700f0304040d20740d04a90380001d0300d144051a0918043e81c2e4401c150403941c0010128002940e407207501d203e0800381c0364ac0c403c19401d8460b0060180c0031039100c054400c254181da078007501440c1103613640483c2c600450310794071040c024807074010041400e00f154052158068401d0300c01500030300041003c2030103186d401800b1401c403a00410003d0215503400810381d07003101405031120403802000310b2410b042c0401d01001a401001c13444a441180d600c0e2907015010700d0303840300010006e06512a91008a484502004102d600c080004102c949401d0901c45012451081a10000e802c9030001404580c4200d8a2221035002030354200302520f8544903081040010035210420f91801000181e2207100c01400103050100120301c010500c2004518a82640e8010b00903c903903503110225075549079064800c000360400742040200c1c0036800760148410901c09500400502d454103011040c28141c5054840304100003000b818016 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 114105026 1250 114103776 114103783
    0xc01050f1c0606020c0d0510330602070807030308012606310b010e0c19020109060f02120c030a090b1e01060c05031614100b10020703020105120c04030203 68
    0x76103619400003851900c0c01d1000f81c1001140d00d0302078800c5280120746004903101040080441c014000c1c0028821000014061315105803485181410304071000c1c550302654a007400019a800c9408481d802941e0b040038696600c414080100040c01e40801000340d544500da2000341c003050082e8402c240c03182412000e180c510222540305000b0307072200caa02e00261451490300720b00300c0d0080209545803682d40701c14540c084103201c0c04080d0500c81c00025094418003080c1d46104800c644142c1d03064145080007801b0304017484040e501c0c24504000b03c030a01000303100301c0b0242d011840c10203400b0742e25070601c8419a00300408080120791134a41140005030803c0610380702d02e5041c00180f0907032080c2140c040e481c0780140c01910510128403c1c0d070340071420000035a04030340b004040741011010140382c2015804c1d100540f102441c0f00c1c030a100840d204e0550041c045d031800079a07d44202010080c0f08a80c1c4031401e00c80603000c11001c20210350700c1c4115101c0d03143d101c1e114502d01482d281d030381d034003291030f = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 114106276 1250 114105026 114105067
    0xf0209120a020108070504120b09010207080d0606080c07050c12030d06060c060f02031b070c05040c080a050c0301060c02010c080c1203040506161b0302070b1b06010b04080c01050f 79
    0x403035030445440784003150303004840340d44c203c081ea26059081500300140c640c2e820f58030000c0076180c1c1022400291901c5c100750100c4103815841098907848501d0a95454094459030245601085806d0b00145c8400040000c0d10482c079000401040060241014000300340f50f00082c2e014980001c00548501d4910f6000d47c070b00418031030b0759030440c83c100b0b81800b100715000308807606a40d500400902c4600349008205600e0040d4284405658008034905000c4030345d240d611480d001410301029001ca982c004840601c200c640c0001401641e8a00b0310f00c5049100900480c40400c41a00a0030090b5101d20301803800d86100d203412a2608050808a500c2d0070714507001450104000010130040040620190350002c00304003070007801d114284c002400f028070440e40100c04150b141742c1c0e50180740c820403052000302120300c07a181d45d500712070f24006003049034403060280300c0c0702c0d01c000040c072000307140111000c03108400c0c040d10721044210011609584880c00101c1d000005200d0b11902a150081c3c840 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 114107526 1250 114106276 114106309
    0x1020406020d030b040204030c0e0c0d1802040b01020d020601060c03020106080609030301050a060c12030203041a012c15010302070305040b03010f03110603040c1e120b0a050603061006030f0209 85
    0x32140c6154003d003920142009180071785d00520040002034071844c0c840003a101c900c840108144d40b003c0707401c2020b000d801c0301101054200650b1020780b08854007002e16050003600c0c14810048080c0043e0303582d000c1f440703050005038410801000014070680910043c0e41c8280b00104100e5950500d45251500995125050781c0000004015505d45a00250010319982c2802e107050090f944565603000d145180d14824140c0000c00941040015004076402e8208450740d10b031156111447d08610900e041c0382181d900c407150841c1003060600002880c400c10038207454892400b04040114042d40000c40121b0030700c407040c4000309602c4600700165001e0180d44070b107038101c64594140300800c415000c14260098a0030000d0001207a002d00358501500e04020f0030000700340600404810041c03407680101c81c3c900440c100842017003000c082142c024060600180429281d90b0201911410b0a440c4540b040070911410043c00340650098011119500c100508000c8040e01242c43e5003104500308 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 114108776 1250 114107526 114107533
    0x6160314070f12080108120901050f090d060b0f0609030703200a0b030402010207150c110604080307060204030c091407030c0e13090b0a180209040f0f080307090e0609010e180102040602 81
    0x4a501d154002c0700b950043c81e06e0002840315082d1110507000380e100710103040e03040000000d03840407562041d8084841004c4060541207461503d810b00b04000c0c03103001344852140d14003122044951030682d041d991900c000070040c00781545541d0341e2813034406029118080d80f0307800303841003c00340d030b110641d6000804c408078000795646800c0c070009040c80e03031580045034030f141035030311000c034140e44803403040c10309948a4581d290f0341e0402d00008a41d8003466009110901c40020480c0800c043c036005002101d101c2e8a5140031903032103424400584192500c002091820b510018000c1032186d0012070707a1846e00d003001c920821050006c103c40e5090031021204203503d075240c003402c100760540041c0c0d00a000c0c69040040c42c0050f200c602d00400302c1c0c03502074800d810603000b103024850312165890080390310071414401000a841c0140301900101c0f69000030a06403a400240381041441d441d204010041c00c18250740c2c07c00c02c001001c09005841440169031007103c102e14000e003440200040c01054005 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 114110026 1250 114108776 114108803
    0xa18050a03030c08040b0f0718090b01110607020303071206030203030a080402010e0d02060d0e07080102180102060f0105150a0e100207050316030215090118120c0506160314070f 78
    0x6801e403021040c4010810001c40304101c003186031030041b030707410040c0e4400e030080319102e182d411a031001042c50865030200341c0690000380e80c12694800094908284c0301d01d0b110100941500c1e40b43e010032540c20b005a0030030000211200d118191016103440140c00c005081d41d01c0350013003441c2d50410940381c004540044144010f42d0380001c9486a4000e045450040c000d407658003003200f50042e40c841c80d541c03c2d19801421071281c1c05121410103010224021074450500c69840304c94000901e265a016005400126101d01c0512002d07906954010f044100301c9105512508841ea10201780003040101c11f1441074415940c00c10140c4c0c50107003a41c001c1c00c8080c185801c00d400d040c21004050b42505446000700010b8603100c0d00481d08020b044081e5481c1d01c0307048010f0314003050383c0914042c0791901704004102c09400e00290b6008500806142d50b58688440900c00e0310702c00c100c03004d014100910303240d200180c810112090740304101080c907420074081e130395903491040007414100d681e03600e0b2600 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 114111276 1250 114110026 114110033
    0x504050a17090127060f0201061715010602070803090f0105040b0d09060e0a05060f07090b07120905060301080a020909030f13030210080403050406030b0d02180702060912040501080a18050a 83
    0x208941002e40c0501c0c0a085075030700501612185034801e0106010000c0f4182d00c45500132740c0801d000700901803481807900d45064009445509950030040240c200c5000811032502c001422025650310500541c80c21105400b009144c903a250f00c0e0604000080002281c001100d1000d03001c070b03d41294000c148a03007549024415188050104d031701d1340d8068003444010400c00107400b03030841c0c2d05200d40c1406469040e011181c205541c0c00020204800107180c004000c055143c041a070f0b103050740c80051140d1a4010414144420701c00c0700410345c007500070600546400c0449a810400d83d20880b8034000300d903181d848080d00720f44640c40c41c1c0d458802c010019418000c840b06414409031405c0304072440c140d600584203002d14050b4904044d500c00c0760041644a410b21011041d40003000e40f00490707426030010718510401c441d47e4006000e01000f0a40860740021095074032648418142d0809050400446013004c000304004507583c0c5075102ca0b603c00840070b852000c107038004e4019140c1400d0a05 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 114112526 1250 114111276 114111287
    0xc0607030608010c0c0b04020609030a0b07090e01060c020402130e10170102040b040b0f040909080712020c060a0f09090f0b0117060d021c0c0f1406030c0a030504050a170901 76
    0x500c0000d0baa410800d14010b4158003641450358154010f100e1841d680702ea0003c20384d680100340c1e0745505441050f80c0c180070b20075a014a41d1080196a88102c4803a8440302041d0305201d0078403980001c03c3c1541c0c00b402c01403404d41c002d4a204080d803110b8040c41551880366110310340301510600100c0391124018845a4142d82c485001161218004e524040c640810800640725520800707a4145000c41c944840c40d2843c01220b00401c0854802c1c02207483c58100803005030701100c0300b00c541e8602056a1400e0310b00120b00800482030060405003007480318001a641405203141e09400c01241c1c0001040c8405144240b0007588514100003400d0740181c3c0c005081c101305140c10700000e110b11002c100315646c03401070110350980c7c151030f40181480010034201050031002c10040144082c07070808554158041405821070315070414000c80003d0000a0043d50b00c0280e503c06080c10341040a081d01500940103030760000e01c0b6408032001d43c81c160300e5076520034907101034108580300c0005808010f5039010 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 114113776 1250 114112526 114112529
    0x5011e0603020306030c0f0a09020d0b10081b030601020106030b0103080c070509010b070f110d1203110903061308090607030806040605150d0b130c020f06090d081b0f0c06070306 78
    0x509003140f40d4100078001075920340740d89403410b120f00c02c42d80c00302c211070725100c02100c01003000c140c0640d03ca400d40d80450000e030020020081c012007074000d861201c0da20491513240034040c9080c0b9245200200c08941019600051107075056641307030130000000404090b4001d000314040d41000303848611801c0705e07034145a01c66120301e10890322100140000c80055048401481d80914075401c2d00b1090301c0c0003140030028ac40602ea000c115092150140a500c2c03032203141c07900c12035604004200403000d100d2103501901c04544e81543c803080c0010050b2440c1c40d15429501d020301800360403e440c3c600000c0071548030745402c8000130248802e101c0d090030a03006035400780004940210800d2402d45840e2020f003d032001741c4000c140c03940606c94503900c803168108040200450113000454207404040d41e59220b4000f003210340d10404000620805020888440710340b19540c3d441c54549814201d81c21460f4100340c850705800d801c00c00700001c1800200102207054041024010b2841c0400d809000c0301e030716 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 114115026 1250 114113776 114113789
    0x70506090d09210c0e0106050a030608070b07020607110d0f0c0609060c0b060a05042f070c05130209030102070c06080703141b0d0603063606020901030f05011e 70
    0x240d00c402d0002d9401580f22510f50109041a0700d45442e250508064603a40c55008004200b034000010038215031100040c0782900c0c40752014861342d40e0319040740d5902c105900c6249401082403088ca4014540403000b03110840c05200d03c402e10601102c00030f0140c00500408640320079080c0d18900402405450b00f8004046078140443d84a00d17209018181100340040109003400307101c0045e41c03542d00d541604026002c00b40c02040f48030f0700400d41900400113007880b800704030000b03070810340510f16800403504296840b0749000711442c0f038541401040c1c841c41d00c1e4449429003e10101c4c0841c0c500344080d04445000b4246002081d207018805094428043c08850415003080681401320902800050304240b0303111070340000000c2c9110840503402618146d10328581071503400800c3c000d09411080039401c0031400b60310800000c900070103208000014206025081100c15400304001e075003d040c0403c018140031030030b00300080c00002280e03070036081540c000841240c4001102142500b123000342c00c9 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 114116276 1250 114115026 114115037
    0x100e0106090614030406091b092a0302070c031e1203050708010302090606040807090b030f0a0302100203040c0b0a02100c050a0801030213020705060c2104020105121b070506090d 78
    0x1415001070007801012a40f00c20800c0c000003007800c01034298800c909160304225428038101c40420414403c030064400c62000e40d04001e81c520f9040c110f43c6c0b91841c020b009030040c01c41e01c0454102500a500951401d0f0741c2183c0185000000c0344c1460303941002c003a0505810402c52a41d40b821604c030310300d40c5c1c5d010f1041502d80300400406035085690a81505c0d0100c80a610f10355403600010900d00c1107800c200e880d40541140010301440340d8002d420986421025a2040011000c600d0ba03251201c080240c0180c1c8503016a81d2280b40c16402550000c4c059a21b0364800d83d01c0d11088189035200d00113410059002c40c1103030091449a02c10300c11148c5451030114503000130312400514a00341800003070b00c620f0a60010100420042e0b04641c20b280e44032094914514000011080fa07402103012074555103050840700b0302e41d031b11388003426110740d46c140c42c0d080c182806070030220440d1200034210740c2914642c200c0343c0d43c10403001025080c001e1088000b421340b464a80041400e04050750303056010b014 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 114117526 1250 114116276 114116279
    0x3120702011d060702210f0708070b031e0604060504240603020c070303030e010f18050606180a020901020a050f010f0b09060a030201051305090c0c0f1209040c030b0405100e010609 79
    0x80c2d0300c03012a41000e40440d240c0140d6101d42125071031306d88500b50340303401521501400d0759003c40b000c26807204030750404055034022691810720302460b200c00c40d800c081740440f048210002c07115a03450940c1050024200040340c40c2c846010070200c4050395000904412082c5580c000101c2d131400e00809008289025800d107001d1080c403c0da1091540001410b058503110350011185095008052081c0c81d840c041c811105d40700f810420f90f1404200a8640c4d008845c0003844500340900311704480101c41e41040c01c19902d010050340250402e4403070f181180250103085000c11810019621105e0b8264000292048142000c5040300e2400035100c0c0244042c0040054030b60f560890300040300d40a00f809039a49508044000d80c5d0440ca8008990110f0103070184041c040c400305c05080311204ea01c00321201c0000000120360f9075030420508880700101080602c026052640101e00b801010b0300300400c1410205000900380d0300d08560582c0c024600c40d1041084460303240340b06005040034180b0301c2d0341c42e = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 114118776 1250 114117526 114117529
    0x3161119110409120e01120203040c05030d1b0f2a0519080a0201051b03030403031406060705060c0a1205130c05180a150305060f091c080402040c02010b03120702011d 73
    0xc502103501300c001d002c03501204401c1a4001c0c0d481006140030100110f42e24034280c5401d5030004110b0091034000d00c12503c80101c41030003848c4010551030048a4219049a580e4840a10194401040350121503c00250704100c4242400c401c500c0e8600180300d45160502c0c0600c0f1004106080310b18441d0250b400400144c007000c540341c1034180d020320f032170fa9843c61750b4a0b01009209210220b400c3d184000801c0000b0300d0362560107001100040401000280c0b508002c101d143d01882c64058059001200481c00a03041107005103182804c80c24010081e450011944040f15800c94152408041d0440d4440c100454174200c040902001c070340d66029101424000542d00f80d00601d4246030340c2d6643e044220714509050210002c40e40201107600500c0c200049c0301c40c825003074035505928801c2001403504581d0b082c1c900c2c01c42840a5490856564903902040080c12410310001c0540d541c5078502e40e4182c07030074030003480d46003140e804035550340c00d25200040c2018085502d00c0181d09803020030070002d = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 114120026 1250 114118776 114118793
    0x2101061413090b01050c0d02010207020a0b04140f120102120f0a062102060f0f09090907081908090a0305030a08220201030e0106150e031e0303161119110409 69
    0x180c03030340b4210004400c0403850040e1098840e00158442c1131081986404405070f0540090401d203209985001d212a59224034140c140203c0c080d4110090440c09059010300705102d00b0007160000030b100f08003003880b1206860032a032010b200c1920000302401088510250312000c140c1105500004104252030101c0e90b03e1090a01e502464074804043c0800066644200a8802c0a40c038102256595086d800c904e824951080741014011103141b0000384515401203900011a0f44101c00b41121842e103049a40c080580c074041211060411f002c01215078890f00445c1000e54401c500441d640c0100c00304c050403104000700445903034450303460100c041d060f03980014042070740d0a0802040701882298902d0251140350031012168000c0b00840c0045548400ea56200d82000e80980e00680e0502c030815008402250182080c0c3c3e008101207501e000c140351340c1100310401e910b468031144142400b00c5081403006502a4102c0c9011800c503824480c844180d0082c90704103c504229a4805940d15142c = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 114121276 1250 114120026 114120029
    0xc09171b0d02010816051c06050405060d0c1e09020a050408060c0304050d0c051f050a150302100507050f030309101b02060403050d0b06070614011220062101061413 72
    0x10304525100050700860003007055510051f0b00d6241300c0c0450340e0a0101a00601240c400d080c851414600030030304504040e0002d007109a00a610b100c0803e00f4600c07130010ba80c6095203021081050f10100040a80262003c2e050b2401caa603280c6a840d4a0a5041c40c41c116000d40b404955103010000d000000d10005030415403a580c41c2401c03002001141050b03030402d1520030f0030400015090103810b034685850b91215100d140c141c8000c001d00d203155092400f5852a81c080250064003010340c000d601405680075161300c0f4440d07411143c041640f00011400c40c0c2041d0b0740c49c4040c0c0c0c844089220308059501801c0721890041c0c060b10141800820002d580d80d201400240a00c4000604c5019070f4a1a410003541d00c1c2c00903040950f160181c5c90950010020320100c1d41210350040c0c00485e0b8030403100407020344650400c0050141c048112840000c40824540c0590711a5003007124800b42482808903890000300c0d100310003400d603d440c1016041a842c02500340180400300170503600b02d800c0301600030 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 114122526 1250 114121276 114121291
    0xc0501051204020f0d060c0305040516060e0f03010b030a060902150c06040303050604020409060e0906010602060601140a0903060533180604060506121006050403020f040c09171b0d020108 82
    0x840030300c2d41300464511840c031900030f4111403c100b614880d041d095044140518884e8084900907003403881d070502074000034011000003c0d50903080c00311798078100030081031310b01b4002c0c00024031014060019241040c1403804070745d240e442d8194001985440c03a0388041d403250204040b42782010803403003181c4814004200070141a614170106080da01c0d1581503d0140c40306481c100811503c4e0301c1d0820510713004881100f00c40c8114400031070450320101d400c5000e0300041e12950a01000601c0c0c00310b8540090056400300001980008007003086ea01549000e02407014502d80c05003000c2c050703040810707012610303480030301c14003c8410a00d88440c2c0010001c030a494182107a0390b01c038240000c01510306944416402000410180344100e00d41c41c459004000c011451000705648050030784a031b0150340320180d80200782c9044c1019500b040d42200c43c0c4823109141050740c490b11904075554400c2918031111a55100c4a4201240c15064030058041003049881041c152003d0340028441c40c802440c00c3d = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 114123776 1250 114122526 114122539
    0x1202010513020901060c0c03080a0504080c0a120b040501020d020301150219030207091113030b0f090105010f0b0a050c0d050d06050402030c0304060209012c100804030807210908070c050105120402 86
    0x26411f003c0f84d9801c001c041c40d48880b04031307503903140c000c00103105070040d0040007018040d1031071500907071514403940011030300455195100d4040303d483d51108261b000300f050741d140d5000c0003e2403d42c61644001c601034680140140038032108420300070314041910031860b80c81d0910100a0012a400103400011106070220208040043c1c0c1281d00140c005c9841064241503511008001c004501c45968440d005402e50f05600396a071100840c240c0300288509000d550f500760003031024042040050001340b00302c2c106145040056000d091500b0b600c90241c40000b6404100c5160101d950300440c0c0041c042181e09509504007070091440038132010704010143e640c00035011616900a4401d807050a00300780c0d0b1580c120491486040030b289440c58440d20511202410040d180c2c01031800b940555007590f0f90981694440c80256207210003501c110280112420701c40101511901400c44403a21400d85e041d01c0e400c152901501c00702250300590b041c45814402494082080381e00d081c1d1264048603407 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 114125026 1250 114123776 114123797
    0xb070f02010c091e030602131a030f0a0b01111617010606121a0a120506010e070219030e030d0c0507082109150c030a020708011e0506030c0d120201051302090106 71
    0x29801042d074170040c141c84c0080351005900410020000494001c400100441d2050b59600c50300c62104a07007510301c030324a1401142034500c0507484494045170604240c3c08603c1e1120741071340341c00b0045411849040b18070000717010380d072203100c46164a03800031002030000c0707800c008001d49080300b00403111503029601e01c00034030241c00c00070280c009508080c054030300a507210ba0038008031480800d001c0c3c0e42407280000025030400000c4140303100d000142e0141c00d202d01d4420843c00035644c0c446064080254826028050755803e01810307201c5030b001d444903180c540c00d5291460900c3d159500c9420280c028070100359001c0a603603034210600c0b40300c00001c3d0740c401c1c007000040d2400142054000c404140415558200d110000003800c01d80120f4007142e9003580e5655a80d802d850300c1400140f1441c0c02100d01d50f241c0e02180c0c100359003041340141507420f04a018004101100480340307040e60640609a04110312035020b100f1150018001840b0114100032500071445518062040800b0000a0b02c0c1 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 114126276 1250 114125026 114125069
    0x1e06010f0e19060809011104050d02040e01090605070c0506090f070510120c09050301140709090b0315070519090e0c030a0e1b01031802090a02030c070606030b070f02010c09 76
    0x700411261030100200740d542d80c50345001000840c080310285429860401800080c00400302600e088580062801d000d44c0d0041d400d00002e0203a846e2498120b40d2a1041d00002070000d018482c8030390215914080c00c41407504005141440c05449400280c0001c010951010000720b10201034500503a80b505503071001080466030720b00040ca40740d500c9840d025480110b075601c803031500c0c00c4960480c0280003502e10100102d41c042003da6480c80465014002046218034642081c100e4a000405035954200086900210b000b0304039158400a0320010301040294403181c01051034012600c0c100008030704002d0300c04c489c48006040308031248408400030b0220a85600b180341105140700c2514115040b81c1000048500d4102c0c003140441d084c0040322032101824a8032036403140c1c0040500003c6d80303d90103000020751002d401004210410030082000c00c03c1400350900451064082d11224540540020302ea4840c41001c8401c40e41411107010310340c0c1c1e11440020641b0310341c40c3c0180100c1001d81 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 114127526 1250 114126276 114126289
    0x1b03040c080604030c03031409060103022214040c0b04061715130501060f020a02030a06020307200312011a0318030d0e03090a1d010b07080409050901051e06010f0e 72
    0x501901e8103100314800c20003050303449400019520310948042c0580a034018502d40101411103600c151580f04400401c0907150020313601d000701c1c000301402d445400000b80d042e01500c44131810302c81c00504180500c01080308140442000302400500b15040070301340400140401300350506031403100d0750a4041074000c101921080b001c4040280000045150343d041d00d005410244250404202d003200000a200d0020455200e90b80d80140030b0640040d00d5038400e0000d41001e00414204000030141010008581001d04000d03070040c401103842d8960311441d00394500058004644038480d46014092190240c0d00350b81d0002d103c0881910342c0e600c136540322032071402440c0760001c515007001c96403000d004c404002085c1040c015145000340355102ca040b03640580f0340c0005100b4291060f00104044080c00c0042c208092049070347c3c51503c0e5a81d41d200080d50020340707400400365902c0e802c0c400403030000100e40c10030014900451500d4903001001034030381108181000140190980944440c0d510007 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 114128776 1250 114127526 114127529
    0x309030b1506070b0907090c022e0e070806151309020d020301150f0803040e04080a090306060e01061d1309060b030a0303090b01090203010e010b09030102090928051b03040c 76
    0x703800781c2e8440c090360902e0b549041c0c017a64254003078012407802055215003405032101c440e10a80052401110060002c0894144400303400c1206c84000054090590f4a024008406001a000f02045800c01e58a036091040203004c00e8410342d0004030030542900c41d500000140302d901c800004800d40203002160025028a0000f5455440c4c0790724114402004800a002d95118040386000741d0b450340a01607407403099000341e0300c0c800303840c000003000103883e500148421000c6140100e8070139a40d6035040152400c9402c804542400440184000759114203000705849a00ca00b2082080f00740c40400c1c0e0200d50b01001c24042925100302d60203010792504551400301c0050200d031340c00c9000b810010001d1005a504a90f25840c407000010355015500030b490581d0140c074031051459103020440d494940c800c2c00000d4255400340210108c0e903a4000f540c40c818a13070b111700c02d840384410112580b40f4502c01c807000c0d21418a004140308050092030f92a1800c2620b9010060b50fa8445003032443d00810503 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 114130026 1250 114128776 114128779
    0x20105070210050301081501030206180d0b0406050123150c12070f0309170304120c0902030f090705060a05030109050606071709090c09010e0904170a08060a0608040309030b15 77
    0x2c005202c440c1548400254126104d03c403d440a03c60050003001c0ca030340c0c082c40301070740c400c2c420b004001211841e15464020105d00400d9190040d8a03a5108451803800b105e09440d01681c940042081d030780c0410021010200206d0100c00010501000820514010400a18142d404034154200720001c000030005170600c035400743e0700d400d254904110090300d60b0700e040300040d042d000e00080c00c1d00445c00450800700040003039402c06040040303140038030052060039500109032440009041003144001c41c000c03e039010b0f03c1c2c5140c3c030744083d44a10300407503644414043c241c20400d00c07514070351160a8a055880001c404100c585403000010403a014940f00500303480c400104004074280810300400b03d03c10305841c0c10b0595900c078001544140204121140403c940c00300700f003a946000c1e501705a0244c400c82149194081580c4244030b2078112123500d8011484103030500c41c0c10701d0103c03141d000170521490304030f540d4a841ea40041900d142480700a0103903066102064850340c0002c20820071800 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 114131276 1250 114130026 114130039
    0xd0c060f060b09040b0405011802070515090c0315060d061107120804050106050901031707030210020307020a170c0c06071e0305030a050f040c051003241d01080c010c0201050702 78
    0xb140c0034089034551005030710a115510380108130074642418004c550490f240101c00100280301000c560002e9800950100c50318001c403a4044e80b4200b152410034050240c95004009503d4002c2c2414a030402c0b00860044000e11401000031030340e9000d140694444c4d01000100e21400e000d40d80d0f246500940317800030321007480507102c14002944050360b94402e500500c0248a01603450302881031740d42003800058880c64102501001303148a0304003c204a9100784116901c2d0032604101108070380082d1a03a00042e00036008160500900b00750a002405920a0b03452030003001d018500d56440c80c401c0020700540f070225128090000756040344410152074240b0008030350b803503d8001c0c096803082761440001c52601e0041200982c0c00c08a03c1d100f25800005d40442e64200340c200141400d809100e5010141c4602d0442c02003a50a0780901201094004094005040a440c406001130240440c02c400c1d1111004111351103001900c00940306080c2088810a40c00303000407581481000c001940041 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 114132526 1250 114131276 114131279
    0x7030201020c06070809030403020f060706060b0309100e0c090705040f030506010e0a0c080606030a0b130507080c0703140901140309070f0501090303020a1e020d050c041401080d0c060f06 82
    0x64040d0014841e40300444107880450303541407019200140103840c402260740c0709020520040c280343c20a80c410100007812241804420b50b101d10544000c0d03000040001408001c2c050942002c0041d00c09414a81805010b900820b0650f55991070700d414100d0302c1845424003090800d401001158050800001c41107000340e1203042843d0f81e420203200d9016158101c400080c800301c401d1050380e41c11007281e941c0790300742d89030388040020f0b540010b1b180c0b01907070340c0e1456185995554402c069145501e29580440c0a150404024081c500000d100101b40a010440000040d6000740a414802000c60419480d107000400484106400340303030044001070000180300c0326801c0091030400311484000ba044030b440c0c45400440e60490503100003005644030700d458a000075410712030648900f031280340c07a10348140140c002903200300d01d000064600d500440c140c54102c0c109070161007031f9000302d003001900c079526200d081951028440c0d0054108006049107404002d80f07a0801140184410000d01900d03 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 114133776 1250 114132526 114132533
    0x201020306030d05030f040b07020c10091406040803040603020d02072a060201020f18030111190e0d020d06020a0309120513090b060412080708030103030e031011090d020406050607 79
    0xd40c400e076055071007441002e900c0c0007071500c00d13011070f40300b44a00c446c2c102c9691116500ca010011014001c0000e5010742e014819082d112950300115a9280d07075100c1110342d2a1010040105003400f02c4240510b070b04201c1480042400001c076411500c9900c2c0041c0e48042d500d01810084c0034518000303080201c0c090803141e00d80f02d207942e1545481d10084604541d03640c1c40c0c40c260700301d1041e440c0c0c02e815540140174142010107074042d5011220702c09030002c070b000c071403071320946406031300a014102c1e5800f9250014401036601030022000100c0650700240c18000c603070005004200c000c00001c082540020f9460a6141700b80c04c003045840e80b04003004002c240780c075405401034010700760141c04030314040000102c0c02c0e50f5002ea03581c1202c01500c514541400c00705c0c00b10b10380b075400409550301c00c070800850000552440085008601a0b561007202c5900d0700c0415050510400000c520181050010070952130541d0407208912401c40d03000c0b407901002c1c408a8050301007544074030740c803400104280060 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 114135026 1250 114133776 114133781
    0x41415190e130507110c13110403050106080312011d16031409013206010c02031f1a10020714030c041a04050708010e0106080415020c0a0b011d04060522030201 70
    0x2080607481e00c03c10849032408039039440c011b42d25042e034003920340025540e030b0018541c050280c904800280519280c3c8980780e81e802e480380350780309140a90002554038003160440414a01510034031000800d003a103000c255000d07520000c0d05681c61515a400070f071400034040d900502d6881c2d1076030f080744404e00d8140b0fa854000c0c00000480007103104100e02481c0041e2000380c3e1030b840c084d018040010240c958800454012002c001d040b42c1501c28001222102d800c0000fa1040f42103041001082c1341e10404000041c0b8011004800d000d03810390404880300a0b0003144010543d0f4000e003c0b0722515607178400280ca491442020643c115280c8950b041440948100c8120500b40956040c01036485030501154242400d01c11059010040401401007602c9052125007241c040c0040f8260003944440d140b00700da016010341e400c10b41c0a6200708042200798401d80c0d004103da01141002e00310b18500c225615580148010405650b84001809010340503041503e40c4010b01d00c2070307002c0901450007900 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 114136276 1250 114135026 114135031
    0x705160b0a0513051b0d140109170a0516030905100c0c050a0501080711030d0501080f07080102030c2a06010f030c050405070527060c0102041415190e1305 68
    0x215500300000140312078012400150310984c4080180398804000d00c0e90000e14584c1200030f0382c0711704418481c4021582e42141e141403000300d0000069010b03450710744400207240305002002406014842000041e4000c016101160304000100c4401506460111040d643c1a0003180d84140707080c0401c0c5415500c40c88500e0f100d0b106806001e40e4903281d004102841826110f03403800542e0803c00640d5892091100201402c00403007181c5c101341f5060442d0007540c20903081f0101c42d40c0100039201d1074001c10402c0c00001c19002008514506002d000c2100d24840c1482e840304180b1100700c258001c158116206d46d404003144107642d42c5584803140100d00084602c0190780d240e0318600d020030a0b2525101e1280500002c3d2600c1380307410035580300c50660381c2c40703508118000111110006882e4441e0750082a50090880005035650305000f44400854000c1c6c980e580140c070360311544810300798081c048400c2e103526042c0040043e8207462044440303801d011081d90b00100342c0d447c3d5034803004041d00001d0 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 114137526 1250 114136276 114136291
    0x8180a05100f18080403021309080703050d0b1212160c09051b1c0b1309150e01060510050c0316050304063f020c06040f0506060d05030a080705160b 65
    0x1005041c450440f40b034203640d02c40060315440e070420003080145040d60803490540038111011803802840d44031040c3c15002250280e0219200103490000004207100b98070b02c00d80101c840240e02c030160f200702e40d510382034510030000300500001c8040c01002196150b681d0a45c0c00008020007075103400c4458040c080c10b0314419007400e000f18501d24480c07907040903900108100041902403a903d20b08503005009010034064009070308205007004c0b0441d9024855841c1c0c040c0c503241030140f030502a603004450229004910310f0349031003014081a51075810300080040301e40341040e00c6e201c103c4603050641c030802d0a162076480b00070045204108021001c1c204480181e220b0014030070040d03888411003407402e450983c02c2c0616400d000300350340e9140b0b025a6250960280141451032442c0c60354039021040d035007610015898030880302084010003140c0d40c800c605803125884007945079203080d40c0c0d0058480701c20900841800084885110704180c540c1c0d41400312410301c090b0b885e800c201004050944180 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 114138776 1250 114137526 114137531
    0x20a020f0303090d110a1101120605060a020a0209010f0e06090403050408061504050a0216060c050c071403011d0a0602030402010e0a030f1101020c0604090b061308070602010b0108060108180a05100f 87
    0x58055480215003c01c1b203580102904403900e000d8001140c8141c0d2000004a4482d9a0b5030086000c1d1100ca0142440405d550004d15054100d40100005910142e01c800c0c06510301142c24406070118801e81c80d0003102c1924442e2113078903245804d03900790081703030803800d02c41c4100000c004058a010041264245007510108403640320760b4107910980c860341d03c1490311718181c0e101c0707840080c1ea00d50218070000a1031a0441c20300c001010100d0411701c581e8411201c0143c580300a029515003031140c04400c00b9419039802029a050715901d8551044d40ea0144c44160301100150641e4040c03154490400c500030400f0144a0b20391401843e40202c40d0400d88210094200529042d400001c140b88407000007041541418034003490000507014584406410910901424108045155494000d0400d02c1c4c007400031181041c0f0024211001514a64100a070140034084c259030416400350300110300e0011054406001e5410500e0080b5043e0020014440c102e489240c0d10300d594408504804025420f = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 114140026 1250 114138776 114138797
    0x603022d04061d090f0706030c17070807050711100c030f08010605090d06020d090311150f010e0c190503060a080703120813050f0105010302040f0915020a020f0303090d 74
    0x144801c6030700c140194558941401110900340807600e19050344107000004885c0403003203010f02c50b8103100b40c0741c0c05107001c02d840f04049481950441c02c0e440543d1426807010348540707070280b4020440030014200070180070340002d201c42406144100c6500e020070107803030105c5400b60a10700800301c074540f040c16000072307458010611480d44aa41114101e81d1281e071201d00b010f406404001d000072213184100c079416400c0054000c000024020715014901a40700c0610302d803d041649170400e50b0783c103128980380550310100711014040c070b0201c5041d50f0166503000c6040e42c48a2042d0484c1c03203180101103e44207000d100e070a4066001c0c00861140350241c03140c8100c141e9a4050b140c0d500421f000003881881c40480070f10440d4801c0c0c0010b6800a2990151303501141036443c0c00c0c1c02c000c3e40c1c800f40c0b1160f9440d440144250f003000c1c003450003260054102045441e8142e281c3d091401c40b401d54240349681c000682030700084c803c0244a204000c0f103c180c3c1d03540c0c1008a1801d50f1464486690404544d542d0003 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 114141276 1250 114140026 114140029
    0x6060801090e06071d0102010b0d0809150412060f06120c05041b0210150315021e0a0203090f030309120102040302030106090c08070806060d05070201051f060c02060d0603022d 77
    0x403d14001e240944444890074801caa40260245000014904542d40d40b90300e075905541b01003000425134012820b06aa49a41809200c00f030400c3c1c4240007041d01c0308001c03c21030980b40700c00d2280c800341c008000040d103404008800010707007095030025082d0300f0401401c80a00c070004510380f085800031a0100909601482c0171072001b40c8811469002d031300418150825a642604541500600000190741080e2656120030241c050510120105580030a0340d194105e0111801c800326001f105800e81480700d40d184c021341d244a030001c0d00d4041c019a211060080e101042030325071020780100202c90210410396918000d401a20069201e9800c0c04400038080b1400e10504058204c1c0341d0f250075045e038404a0503211598094000c0c0d4014001300301007010f104292040305e000390714540c00403886003001c8010448259001000a6440d10020b008102c007903000500d82c4103441c2c7c152016034403801d181201400030429a44041e4203c04000b500320074408940c400740e0304140e0618059209100800e0 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 114142526 1250 114141276 114141283
    0x30906161806050c0c04020f0d05090105040f060f0f02031501020c040204050a05120c132406081f080307060b0307170a030e040b030d0e01090b03090c2206060801090e 73
    0x2250309001e100003100501c01c2600c5840240340030144841101c60340c0404e100410100e9000c8440d4503105400480d0808440b0308034041e00b0b4004220b04000d01240c20541c5070600840100c0b1001081940d4449078541d0700240c41d000960518070298045480f071a100400780205400d604401c1e0060180e500040072a1038648242c600340e5002404030300c0f24038242410321040d180c44070900d403064130504d00302c0c50903950f82041241d94180b42c00c1c0003096518408036a4460001c0c03089002c0460100100184005d1341e1020781c680d440005135800e00d07440303003840f800d260b0b52100310b8010002c0d900000901d05c083c8084c43d00281c0000307400b50120f990465603142c0c080000900c0e00d14491240d0410382411010911445400351103ca00600c0010504003c00c0060310b40a08038208034003194040702c01501035a04401035038000d00b00340410701d1451801d6629241c1302c03829145610310408201002503490010500054800c2020003010041c0545609001c0c01044007441580000744c10400d94094551020 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 114143776 1250 114142526 114142547
    0x31602060f0a02090a0b0d06030b0601050930060103080406090f060207050f011407050d0305010801020708190504030203101506050403020319060f060b03010306180b04080307120203090616 83
    0x284801c1025203a40401402130351080716000d13809040c020002c905490340c01e00420f10095082d000050180c61441c20340e5081c00700038100c9052003000c3c4038114694640c1c00c0000c6038600341c64003908000030748240400520760100404061032255800200400c1a011300070030546827903486080300c442d60f078011001c4c038441034054000103801c8030404000604041444030780c0954141046080c0890b00c8000b24115081900140c1c1c1030740c070401003030b55001d4052040ca809458088000e43c40c0000944504c0520302c81e40070101690200c010144124910920070345001d141e0050aa50361040c5c0c041254000d8400507401c1d082c5944c03425800a41d20340034a0403a01160790143c06084145890051403e200c1c4003c1020fa41ca40c1d11005a080702540903c1400b01030070820740d20584a5045041500c22034004a05c2c030000c01119280307402c00705284004007544207502c0094a95280d0311300d5800c0b1041c4030301203070150b074a0b8004000d1250340c140114410380304030600103910140b00d4544004681d0204075 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 114145026 1250 114143776 114143791
    0x60b130e0a080d0b130c080105010f140304020607020d0c0303110304050a06030e0f120d0b04050408030105100c050a0b0718180207050a021507150c050a0e030109050f0303160206 78
    0x10000e070001494000603003003c05a042e000180983e5400201d44d90707024444080340070b81c5c2d60704402400c440e0805000c5015220178600000910040003014100f0b1104100401d040c2102000040840d035500084a40381781d0301421820318074100b0300d00005d03209101e0008401291410441400d0800000b003030350101c0384020f200c4681d4624080c000c4d4010f050b0b8680701c0f00c083c02101001408450100700222180312210040e0799640741d41171a80f0102c400c82a0704500c42c50814ac24840465221070030b0368196401101d00f0a501c86006070181c440c80800b150041850003041c40300d4050100758481d851082e6181c0c0c42d8000c1d010300030160707551050303c2400faa83e20021007541c2d082c0c00b10306c00c4d07018141340f5108000b2116450031580010f0b04001514090f44032030540001c002007000702c6210034012507004402c0900421820420151080c003a03101c5200801c180c01d013103205595825080f40c0e4459410400ba01c446442180c00207840754000c4890500e091301801c0c80c00041480020098818550f = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 114146276 1250 114145026 114145033
    0x140109020607080a0c3201050105060703030b03100501090f0506030303060a1a09030f0601080c010504080703020103050415050709141c08090409080a0903030906050705060402040f18060b130e 84
    0x10b29a40d1030364640c01c520101000c001031100d00d10005404010204034200c201200d2003494030101100300941d00f030b40182c000d050307410400100027a450352002c0d0361415502d0705000c41d41460b044040791801051004104080d420080002a580c2065220150907150038200380003e40e1064103041d603920056411940009003040e007002030b9298400340c0407810340d8080e10585803c1520780040d24000350f00090140310b80040004000d40502000850640ca00030f082c55401c103031510655644442d120f100290525807a5400101001048500d0041c0c070360b260801006a803c1100c8000d00b45090303802140c10340c0040c0c84400e207240c5008219100d070f00460b0062040000c005a450401075003041c102c05030002c1d1200c50b45000a14080d000d0518400b00f0703903628900344d1650400402c002c005600c42801e0000820000b400302d2404110282d100b901514041038036048218030700018840e03c2422610b81c1c40c0700302d0242c1006140d0b00030a00501c400c5500113981c1c8032542c42c90f1b00329900031011684962 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 114147526 1250 114146276 114146287
    0xf1215070e0306061503280c0512060d0f060e0c04020d050f0f01080a150b100221030c12060a03020301050a090318060206220606121203060e01061206080a030c1401090206 75
    0x84401c1c0000e40000c0c41c107241d2043c5c15002002c0f1000d231404424414041480420300041d030072424450140d0103003044594101d0120790340c842040c111041c0c03d0103030900303448410318010300e2402c201c1030054800142045641d0341078070051100400e4243c41c000b12070300f402000b0401e5801c1c2c000c2c80d07034142d84040c00580300039421940c41682c024202200102070301d881e900c0480b51552141045c1d0725100d004c0e000341c1110000c03003802ca01c02c4410038415048031102031050000080c40341050b24074074690044524010340f00d2200288000380306502c02035142d8200005c0040041d110307040034066038840c0e03d07a00400030b4162010400030209000b00030050707116900117000c1c4a0400b200c55103408500b9050041101c1c0d50301c504c030070350340a030b00f25107050324580240008004100c41c011505031098075003000b1450400c41041d29105043c4500400c12210100010714078880d40e000f00020210308048807104551464040d00c0c882440c0301c10340d41916803d000d02030a0700180144211268020640752504 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 114148776 1250 114147526 114147541
    0x50307060c0317220312050109051009020304080702120c041b0f020a02031005070507080a030b1503060d0219090e0a030e03160603150503010504060509100b0f1215070e0306061503 79
    0x14284e41c0b410760401410f03600c11400407980e4446c49028141c44078001c81c03546407511a95082e82c0d9544e100c0007030913104104210103d550380007650b448590498260803c0300c05441c066251106003e8490b80c0f29242c03083c90a0344182d1004820b020340519140c3d1343c1500c5070103000b6601d60300030000103501500103a40b8424a1207441d440140e001e10542030190400c0c03c5a214803669802000c00300d808640d40e003204401c24134040d009210b413078201d41c0c1018a58580540494058104804002d01850b0350130700ca84c40600c1c62240200c050445030f00100804110100c0890780c9031960742041d00890340810041d5070b141800b040b1101c0900f00d0046007410b0702d1510104a004115407007150030001215a40841c040d80e080c0035541c000d0303004040104090501c03124a50411000c11110201035180a80045564039000c4140508003c00c4404a44c0720115844082c1002c41d0404500124030320f00701002541d9030020a09000c0e88019001c0b55565070303d241c141320203103080c1801c03040c0b101400e0000600341d = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 114150026 1250 114148776 114148831
    0x90303051e041d070e0a050f040f0b13050411010305010f120c030204111206091909050106030605130b07031406060703141b0132040507050307060c0317 67
    0x24020281c03061815035280ea400001c03280c15419948280224018440119482400b02c8070b0b0761401c0300c0c910302040c60030000849459441400f20b010b1600c940588449502e16071102c140f82c000030304000c50500e190f03083e060042004980c12282c0202c02e80710100d842d44248038042c16200300d031540c03140e25400c0860f0340c0c510342e100220460710014200000300041c1c450380110345580894264141c0c84251503075040c2d01e9510000c00c0c0b00d008030807034410400700e800101c400f801d41c102000c100049042c42400c00d1030250080c1c8d080501094101800d108c0e038114000f0040c0742150168015000540759604100d007511200401006140382580120704141303403220040c00ba00e03102e801c100c140138080802c004415000070403051400d101600200c03401c0c50f021700810880f9481d0800c40d00041c06083d4001c100d041c2d6501030400c602c40382c400003808100301008040080c11008045455440c1d0380c18004205044c0c04404500056809086080301c1143c501020700918282c00c60350b11000d91820031094 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 114151276 1250 114150026 114150067
    0x10b090108090105090c01080c0f130e071d0103020a030912050304050f0f0a030509040f0509070510030621051218040e0f3403060906050108030427060302030d11010c09030305 77
    0x49c014804c0007240f45c1c81071074400801c1c0346424140c03207403c040e1500504440e5103000034030103400c0c00718400902d5118401c1c440420400813003401c0040e15407003488800c030024480920001c080c10340b2400240301094000b406107210714801c1e070881d020f406141c00f1035901c0f16580c00850b2030a0780303d6910350000a0254014100482c40580005030304083d00840805550b01500d054805030060072045c044c0c0d04050110728200c001c00e04061001928069404084a02280e00210060100c42907201000341c00e0082c151840b9101d81d02e9074035040078412850342e20341d6000c0c86501c2a40340501c0005651000f0031400704448108019066178048012500700000e00c5000c001700032030900380000810300c82e041900000d18001c0400154481d014035015040f00c41c180c20400d40c42d4014041085440686400900001030161041a0860304910881c000d4200ba42000b9818000d11240f000c00f150f10a80280400041200038084406095029180d0200c00d020240000d502040040304c55841c500718400e = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 114152526 1250 114151276 114151291
    0x3060e060c040e0726150306011a030f130807030801091802010c0b040501020c0a05060a0501240e040f0f020d0f0c0c0303051503070f03150203070903020d0c0509010b090108090105090c0108 83
    0x103800c0c40c2007602082c0203001160000d05101a4904046c0b20b81020040c40f40034059841040351609040440740d0141d02004002c1c4d00000349980000f010172040d0290005001c0c1d0214801c1c0e1911002d10740a800a4000d010366a511071811000c4202c1c140d21061207800d440e0183c591700c44102050b01c0350408080000c0080d01c5664003048a40ca0051041201103203290244010b0101401d02c140c0b030906132a03040c2e0103081a4403e0700c08140381000d0f24074031028141c405040c103506400c03402000c01c000d0310702058409502d600e0011641d1051000b0303001081080100c1100b003004144900c1c0d8a0100e5030507009000008440c0d4046000203030280d841107070803202e6038007546810314001e40024034281c40d64102c1c0004211600d020801c01c921591460700c054280754041d800c40c07601d480010003040403880082d20442011403000c0502140c5024400078110252000c1d14540e1681a40e03c00384d03210b200040e000524140c0007a0700c40c10117118682c0262030f1000a4801c0e66058001110b00c44000391400 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 114153776 1250 114152526 114152567
    0x2040f060e0702030a030f020301051c050127031803030e0111010e0a050c1809060c0708130605180105120a0c1710031406060307090507020c040603060e060c040e07 72
    0x114007001036840041c450501580215914010480d000b81500c800e660030160050042c0014080b075510181e4150815800c01050940c1c84014208980507006d01c1c03480d00a02402c40920064a007086881c007800540a0740301c9040b40318240078200c50100031480040c0024030901c100c245a076110b5080c18072840c032403030000f08030f003403030411418200103900c2c3e81102c55510a40060805013807124a1700301e1404c0501c03400500b07280900c032160300c030b9400030143c0300c40040015400b010401400291030139041c06603107202e150760b240c001c003814643c06008040310724000151140c1896229030200c503404042d031000c40d03d0035120a000350000d408941103c0040c028200f100c440082207650b1301c1880b030001030384180b05503451402c0c60701151003c0c428115107500f042040004a880014643c81142c400610000d01d940d640032089050a0311255450b41c406d040a20000a200c0700d03801c09513000c17260400380c5a82e9200c1095510310743c891882120418480c003800a006179008450703480d503d180003c01c8 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 114155026 1250 114153776 114153779
    0x60c0a050f03090f0a030c03030e0a0306141918060b0607120503100f0e070c02030f030a05030103230706081e01080105160302030705070b10031a0f070207050108010302040f06 77
    0xc03a41441000d440a007503982c03001c110428545071501301404020b80c182c42d0000e12031304684540b0380356221800b001c0c0038041050780181c2682c46030140e4000a41c2c100c0f2003044214000412060750303c0301682e40c1d980551030b00320001281c440601c138510341180300e802040d04480c0f503a03071450302800340304881c940d00000510100c800301d015030661010071300d041e5507003507943c1c130b000d0fa6440c11200d9185c000841c4881901d40c107104c0f03d0000d26010b0f400130620f05003130300e40100c6880024071b0924011001001c84c0030110710f0b008010381060166060f280701e19905044074803120600d00c0d5003084907a180c4480d9000e14810070816006042d80c9402004182256143c500d4800020764100020382c400042c5a6460041010f424090040468003800a2405518500b001d20700104507014480c8090040920400860407800d84800b40e0401141c1c010f01001090f8a48402440c8580707040754031007400c1c042c07040081c030130901c08140720081e203905031101c0f082c99086809010080c05c40203084402c903a40d4210 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 114156276 1250 114155026 114155033
    0x90f0b040f02091c15060b07060c0302040515031003020618011b080306120304080a1a0601020c0a1802120408090307060f0906110a02030115050f0d020a151206030b01030c0806070905060c0a 83
    0x14050141110807c1a9a03a200e1803074004112209070744110300b010710502003070041d60740705901e1a40200000141c81d44a869030400448444503d0303000039407220001480421000400600311400c030b5003600d920002c0d254450499120a81c1c0d202e009020704030400c00a4100e02e096041110000781a40840303040c0341e11041550314100d0300c10000e480c0d0004840740c44419611110405900c03002c00e101605140400d01c0c0030450b134150724015001068940340c02c1c0c50a00c00d4542c10740e985900356401f820b9440c1024200401d260b4401c0c1c00c494040e015500000c14101d0013036503800001c0c0d100755648070011345400802c036014041600308850600604461b8800b6030340900902520182d4007a8a54119203044100403240703000210040c0185501602000540d0303402441504850032407074000400d024100c1c04460030b01049044161052414102109000d04182054140c034070032484012159111f201d00c50360303264220340700300000340c401d0380030310241c1000c80241100350034800403541004140c2d41c = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 114157526 1250 114156276 114156281
    0x9080c18102c18060103020402162315040b061009050d120305010501020703050a060b03070b1606050106110d0e01020c031002030f0105060909130804090f0b040f02091c15 75
    0x4902c11400c0030585060301110720004103900240041014504020000c8016885840510000c1d00c190f9010402201240b00d61170300f04003091340080480000c0c1136100c8050300302c0341c948040903428880c08043c0030f44034098100790390085030400342c0714007540d45220411442c84040c042810800c08903080000d03050700c3d001511681140f140b0ed440b00780c030800307407001005c48005034031060441d40710b48c1c0104003041002c00d4642c0c03081d8100c0808142500e030b08012a240040551081c2901d00c800990850300c12032080c43e4083ca903114610500c86640d890034121078241051030f600f02560000040c905403140074840c04103480320180141c0305141d410600290611002400300760b1160340000800c0180850300c00b24502512081b11882d0406c901d6001180201000800c0b4071000d11400d005d050510000f841524014820400144036405840038900068001c5d00e103014022400d08803c2551a001c5009403584120090104031850402107252903030b0a0348110103441c0d80c00b0345138600481e0405070 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 114158776 1250 114157526 114157559
    0x90f06160201020d080c090111150907030314030c1c091b1707080a0b0a0204030524070908060a090f02040e160f0e15060d1401050109080c1810 63
    0x40e828901820614000a03040100000c07410b4200002002040440310740b00c029074801e00428a042c00480075041282854030208242801c0ca94080800f00300b8051000142070b015240b180e615802080f00c0c0031b4800521b404160f40c13003170309040f09005200700d01382d40d02c1107468000e010f010042003001540e00e40348145110a01036070920078560354184620751241c2c2e6918400300e00400106409442e04554030344407540c6190041000e4410808680d151240c2d0301540c014580000540c1ca02904901e08000c0d400084030082605d2400900024100b40c00344550070700300c96140b000b0f44002e54a040003400246500d2130100d030450b041d64140d00c0961518172855410704c815000030b0007800c140406040003600943e00011800b0029075060091100b030810b419082072403080fa1300450600c19002481078050284112481b0703160580e4030380e042d050900c005048503401c1c1c070b0fa42c084d02d40303078103e4980700d1404c0b0386043c1d0445c1b45144e455400810035040c203540710440d0030a0111b0141c0310fa086c8c40f2008841d = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 114160026 1250 114158776 114158797
    0x20904090b01080f070b030f100e01080307060501060f0c0314040f08060106081303171302030105070e09010b0a020705131506120b010906080414030c120d0b0a0509010b090f06 77
    0x110050000120802c46610001c4d004d03001003104038605110200e10b844010320190407038a012000c581da00754200b01550103000008580141980c40d1003190740e03260090001a0782e010304000c0001115401000342150101490b503c021020340580c40556201d001800d400c094030404020009240c0000b200e160042c0401d607000d8090303545003400c010301440000d0f0072507601508102c049800030350480070084d0324105044441105940d00b000381420b1a4803e14043d40550800c0c0411450a602c041581039607181144d001c02540d817a00c0c0050b80d240260b0301c0040c00743e440801e080c055444c0c10f02c043c0c44140360751080810700b8801107a03809140440d41d8008004540c024089030100d50031401400701c41d500030b18000f42900d00e040344c010004000504040d020900350051b040f0b030910240111290070300150201c44640002112005c0c00360312080c2205550317403a222803c038483c60603a0840c0e003150001401c107403550f42004100358450b800500d0080d4048400c0d81000f60076100c1801038600280c0 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 114161276 1250 114160026 114160043
    0xd0f02030c0f0f12030121031211030a141306021308010204060c03020c060702060f03070c21080c030124090905010f030b0f0603060106030b01030209040e030703120c200102090409 79
    0x200005940b0346500401804e024000a00040c81441c0c000d6000f001d250340c80102500098040e42011382d50500e22030303806003c003820130b4509180a11120019400389446410412040ca514250110b4803c0c003134450b400c052103494000310200f40c0640140042040345d00c004d06801d82c0d14028207003240e0290740f01401081d10a10b106040c0754043c0b0510340c5990068032821315140240d80080e501e80314014140b03992a40200c046401d6521a0580760310450b444000c04001464410380cc0031181d06134510040050742a00c001144a140030054a04031106204240c6403480c40380080485d488084034050100040e09000060240d000d004540c024200d240001c8106403d50405ca0304d82c10300140f581a400380180280f11a030748000030320604503085e6142c0080c42c00e8510004034040d01c84d17426550351007418034901c125880c00100003040b88a1103a09c030108480c0c0401401d04c01e40b01c040408602140c00c000d10300d00c0340581684108402c00c02c11000518001d41d102c0080c0454180030000d032403099 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 114162526 1250 114161276 114161293
    0x3140f100b0301060903120309170306030c01020307080403060506010c330c09051302040f0e0708060109030308010e0a061806030c0603060e13050f0a050303060405180d0f02030c0f 79
    0xa442105400034121a10758540b46604100d406490b160395444010070b03c5000c0b444030b20401c0c2c420b40c0711180c80d03a40020000300d80c0c0c0081c0400d50550300180d032060b11901034a0b9200070150300010403030b4107450744140058205807a40e103840b4001c1c400282001d050010b80c4280d840025120308180120040d54070940000d00100401c0f5540d1041d0040362046891500444000494001002c04111042122a40c01d18200d410441001c1d0285621003401321080c02008500d828140c20340604c10030040d030721200140e5039900112907514030352002030f01051942e40140014950300403a580c0c40241c850000c14055501c22203844018100140d8210b002d550b0704040c0100041c0548031f41c001c03d041e2a040c403500e81000f05d01e000000019000030032040880c0c84407820000b0034030498451201c0e00d0251a403110240c10308546036441142e105d88900d00d40070006400744d2a1004003000168520010200350651007426a91100000c8119041d0701c8107001c0031142032820018601e401003444040c18002 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 114163776 1250 114162526 114162541
    0x110d02060a11030112240e010902030c0a0302060726071b050603190902120303040f0c080102130302090406090c060e01090801110a050703120204090501080c0906130b0103140f 77
    0x82c0c001201c950807040c02040100501010401812030180d004000c4000c0b0954034031250508a140c8440b0701e5001e800c0c211400d06404040d840650907a000b9010b6445500101c0104813414080c0d00000350b1241d021b001c4c0b0700c042074183d25181000b016554100345460202d40d0402c001e50401c1c00115080600314094180d88007014062200a10b0250b42c00e44c25801d00451403981e0040c0280c140004664403817100c01035685207c0498080c6c0c0d654402da030754904040c20071081049500308155030385100540b0020f00d80700d05108666210310014101030358241154208580d8a0007e4804d481c03c503104d0010310301203688501040001c1c101030b1030303c403001441c5000142454500c1e5004d0700c0e059140801c0080085111811941040054a080c80da500c4440c50155001d821a8004411052000c1360208a455441e80198145d5403080125240300e5080000c00946020440385190007400c019000c201c826030f00e411148108005044c0031952494404149612081c01c56042c0c00342c09001e81402001d = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 114165026 1250 114163776 114163781
    0x31401091a061c110f0f0d080a08070e011418030706020c041a03071a0d050702030304060e0c0a0603020d020c011a010f0809030a0525060b040b0607030905040c110d02060a 75
    0x1030f110301c4440c0324800b034a5440344c0d89101c070004400c1e409103907001c4d8110b0203503842901880500710024a50101414141400c0760f03103412408510380807a041d0b902050101d80558400f10f82504140d503802c0c0020b00b82181440d05401c44401c075031841e441310100c841a99018020140540352030780c01403a51991010800066a046174100040066004105030064034040b41070000e4072012000808004075089600c00c1c0d0b03100d0034070f030055080e00e070809212001d9804401940950300803d828803030402842405900d4005130ad01d041e0b40b0100461017004418000d40140084600c80c03040107003400c1c11000e40c2420340d00e1181174406000c40112030f141807581c21001000550000d850701042c0c5141c100380c503e65034456001348105001d808110301b40444c580e403000b50911080c080082007000310740d290003009828007030b103100e120398200141c42d400c90030100207484203940c043d1354030002c080c0340c02c083c800244460000b181c10049954403444010101700001c0010300045d0b801001589000c0104504 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 114166276 1250 114165026 114165049
    0x91406010605130302060c0c030a0c0810050c0a080c130810050f040c140a120803090d081b070c0e100f060912030f03060f0807030b180304031401091a06 67
    0x900078140050f119814041459006403903050790f00c3c998504c1c4502c07250f45014655442141d01d48140d000440801150750100c000300c0e0581c0044400078104841000161101180c0c0b8204a4100380310307005a03648500742094010001030003080c60080103035408518840c50383c00100655004940701061500c252207202d600240300e24009080f810f01341d85000c5280518881d2451342281401c0d0321103140d4038020424010480c0c441500360f850550310b42040340340c00480d5940000c0c0140f103c003201180c0146030441c80380c800602d00361300c0c00015014043e03454000c0f1206581c00518000d001c108403070b11881450180040c0f0300200645458030842040c1c4410941101e41040003200041101038400400d410750950b144c100707101c81b400c08030000c6005040c141e010300303901d80c404000091100c0703020880c101600c0c0250b5601c40c0f20b41d00c000602e084401701c0d441e1615503500811041000c181c104103104515402d5000110f9010107a86843c800800c0d1707950700058020300a0140329161078075080807a07 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 114167526 1250 114166276 114166289
    0x20a081b03041506150f180501020642100c0b0f15090103060c02010b0f2815030615020c0d0210091a0406030b01020316230109140601 59
    0x505a00c150034034401400050710040020409140c02c0070410001d03004240075180c41d103052243c40100400040c07048103490146004900c2103241a0140406d008014003540c03010780041c5104d403030b554444210080d080c0c0046000c4400c200f40100b0039848103003440b02c601001181c2c0c81180c0c0105041085c0003140e02504014080194801d00004001d101040d034071100c0040c8200c21541c903402c640103441c6007504c00a0b480502c440c008401c01000381e110000325640b5a000b08040798510044c00192701052200c140c0c013500c0300a0752542d030000c0b258000050038002e01c03501c0301c50303a44041102c45400890340b0351004c6030b02c80c20107014148201c90000f4900c94548010b01d05024404042036441c212004040d0040407000420315600380074501c3c4000502d940d0f49240e28003900c0707034015903843c1c000340140000a03041007207809140d0700c00000d4541078400362180145100d980c2d5102c0031f0052889000021000803c06d00911910082c400c841d05a0700404a043d100c400c09181c0b2401c011058001a = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 114168776 1250 114167526 114167551
    0x30209070f0206010e1e04031d100203030604020d02040f08030a0305070302090d03180b04030b0f0702010507270509040f0c05030706020c060d02160503130b070b130c0308030901020a08 81
    0x6880c040d400603c080c1140d00c0d0740f10360038554079500045070b982c3d199100c00760350265001381030108040d480b0b81c0700200013040700b980c2d000d004001410000f0050340c00d0b501c240107a0050010850700d00d46940208040180c04034010316241c2d940c4182c003c01c0415510501c40b6400100b00c00b550503415000d4a80e10560718581140f038040d100e80092102c04481c5d10203020061840d008610344440c060074203015100e01f07003d050f2110343d42e140c5040d802d541141c03046a11210076010940311401402000d0061820f40c80e0009151007260152582d90055240135403502c05804000420303480d102001400b1764010000507000c6075030790800d42d6130b1403400c2c0c1c403107806940100c030200700041c0e021030080410141190115a00ca1024510760068000c2c80302800c2c0680c0c52074104d8042081c000014940c02d05c14000d00e10312540d4581c2044800e02031403201822031480c030000500c07046290440754500c588680002518240c99886002003900b0498a0b1070440e0760019100b041c2c0768104c0c410344d03840980180d0300e = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 114170026 1250 114168776 114168797
    0x50403030906050304020a0806240303040501090b03130b0109050402010e19150905040213030209070306030305030f2505180a0308070809030307060f0b010306051f0509190f03020907 80
    0x41204074280300b00010844088007040c119940c1d014144001c00310751048441b1814036180d0b2411608001881940084200e0848400c07400e020042d1022150142c40726801f8525101d092441540003c2003109254076a51944001800c08481700b406800d061800042d10b240c00c0c4009044650b0426046101341e5521072040700702403940c2d0081080d58140c159400154243c01c1090f0b840d01c840ea00400c0e8820300110b1522480c031135070800303441100d000311403140d141e0310341603c00d404540040c04080d00240302040090000307810b002e0703400d40050104180d0159129030950760080404040b421a001510004089080105003400341c160110700710b130a005100e00e150707078403881882154070040184501050803800c03a03405000351b4280d143c1022051101140d02c2003a0b20084c184082c42a000c00c2c9407200104007802e0414030f070a02c2c0404a030007410403084c2d082080e500303600321400e25039120b000c03440340c5804400207030345c5d0100818000054141e242c0c15481084a8080014080001c00040783d21 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 114171276 1250 114170026 114170033
    0x317250c1d160e010201020d110909010f080303010504110903060a090606060e0612070c0209160f030501080c090402041806060321020604030c0203120c0610140109030213060302091312050403 84
    0x40c00782e50344054244121054083d1006038064000d14800c4d4003814580294000480108801005404012507032889141e032104a0302054200d41d001d400c042e03910a20044c4031a00b890740c441c030b00500ca01000907040001c1000040c0c90103504442d85076000e42c031640d04008100240c0030341e1740503103054108503d800d0600300100d01c10380200340b2007008030350345240420415406070f586400c10540103040d07242c0364070382401c00d1801d420b0440109000603041d02101c0029a1082c030031541a1889040034001041400c42000280c9202900036648150380b600c0305444490a083c4c0030810354801c0c031001c04d1203495400e00d2029400941c2c000c03000c131142c81d000010a02d50110380c6030f620551600b13100241da116400840e140c20740d480130030500f00b440010300a400400008000e0300c07803000b11080358025a00c0d034880c0900304448180b42408100d4841d800e000510b02411005061080c80c070b000520345940350001841000180c4503418158001c0a03c1e105000c0901d0400344150810b0510790719091459a = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 114172526 1250 114171276 114171301
    0x19030e0c0f030307150e0a030c140d0507020d14010e010905060a0b0a0e0705040801020706020301090c0905060a050d0905010903050a0f0302160b0402040f140115090317250c1d 77
    0x1200102552145d0820000c08100b03980180e07030040b1414200d94582405280c0a4104001c02c001940e03080c488a088802024001070080a071128941c4e0b002e060071660390034041196141141152a0505101c0a6450345001d1194824030052000086501c2050f41005420324602404d00c0c0840ea0602daa15511910741d10812001c480c0d2190f840310386c69a421030211003d0085400810035035000091140502050390040c50594100e2030041006ca905c1007419500014107124080d046a028003540494a006401034001200c45410104546040d5035442c5d0840c1e044e03803800c4022a0012513654401940040c0840c841d00550801f140340c41c1808540c0741c03080b010800010603c411450005007103440704e80100500607003045040c0810344903210b1240a000e030902070303034482010f00040d035000f00d4828484041181d402444000580c654403a03002c145502240b107031044004101c0c1840840c800016090400f1801040380c22000c9040040d00804181c080310150021002d210a0021011040 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 114173776 1250 114172526 114172537
    0xb0306060f0a021002030103110f03010203071e17040506010603050105010801030c05040f0f020c06040b060f010507060b0123180d03020607030b1903060203060f0402071703040819030e0c0f0303 85
    0x1600c95490b458125412490542c0719101c511507640040000804c10210300240e43c0300c990704481c2421103010400900d400c030b00044880c034001414600e10f0350204d01409121808100b15460854154010340a100320b03605401e480440303031a4020130040001680c9486013602500d001d203001c0340c45500d503446000d1504103d000f060320455441c5c03409014240c281e440302030341911104055442d11704109810f40c41d4241190305480411104c00000c0d107501d40074585100c4000141c50300d5090030266103400e0002c120756000b440c10720407500e0a085140e10b40d495401a4203060a0081d6910350b600200004030091846440f8020ba0700c040c04200020780104000740e012880740b5000441c5152540012405981200380f50b100041fa042c0110600445070010340c4146404d44065414810040070320049204490000e40349030115510350030b202c4840802503030800d0003240d00c203040c40010800b44154100a07108079022030707900e4271419940c01d01400a0858064102c440d480f00d40c01c1180442d40302d1040 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 114175026 1250 114173776 114173797
    0xc0201050f0c03040e010b07060605220b1503160e09010501120c0207050a080102180a03050d0f020f030d0506030c03071802090102031603020a020111010c120216021f03060b030606 79
    0x100b14005007460400584001300400d01c010700c210350390786081008075030041c0d9041e01d1041c100100494141440d203c401c0911a640d244c118454901c1070590000b003449031052030b841076480340704600d5038460802450041e0014035079142c0300403102c0e0014081070a07a0110134050b0b9001c000403c450707030300301d880e1950048a103000890f84910000c412803c2c030460340c2190354400050718004c038141405502078420129030440b0640811a00000c200c45490940f00c000c2030b03507100324030603d00306214100142d0f8440150044590200764074004a04540241030b18002d000d030382e0700400c4a03603c1c08200c41c8501c80025030180001d98100750400004038100c210010241e900001c0d03c0c10b190b4401c204035044620712010785c0c148100146030094603201110016400200140340601d03007820107104101d0045075684803c51030990145c44030300650001c101c2283c1d4031070074103850005a04c0d600951010030300c0d50b1036a190f290101c8500070302180c00c3c0d5044403041c40c10a10411001d0b841340d50444402c180e4 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 114176276 1250 114175026 114175057
    0x9030e010503041e05030c0d0c020a05010f050f0309060f0a0b09010e0601020c040e1011040e0a0c030f2a0c02030a020904050109051209030d0512061e03010c0206060a060c020105 78
    0x456040c10407190f00003111244d0880b864218980902170003102805030300102d0015200202090407040302c6021030360601a500c0321070400104950740c0a18134494000c42c160400d60308283e034042441100f40c2003224180080d030843c40400a64500780c3c601a5400b40b80020200480c4400e00003142e00745c4414000d00d813603030401c000800c009a0082000c444070702c0b4014000c2c00481c0d4000f050719192510000d582c00200c1c105104003d50210590a41c1e050340d68140101480d5618000004090f050a170702e02000e1558404044402404a01840c81c00f0740112071040100a02c042c10388102c0d298820441041260940080005a4000c200f2002d52134048030740100a0312035080441c0140390b4840000c0c00d900c1203028541c00b250f00e078005440640811001c3d144000c034403440c01d4680d4803900309080d0b5030240740c800084151508442607890305280b8540000301e144440d020a084800c4200020050707440754003040b10624000c880c02c000303020286000032817051039900283c210b006085845442c00d0 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 114177526 1250 114176276 114176281
    0x7060504060b030d021606050708031909060204060e1008100b07020301020c01020c07080d020601060801060302070f0203010f060504060510090303081f12050f060c0a030b01091503060e070309030e010503 89
    0x44a4110b10184100281600c0c92104ca0f880040d60340d000c185c201c00c030324030460640040c1d03060080e0180c0e54055007004506195035204c0c1840310650504106c1403000303540e00c40200020800b64805030001d009a13450700c95501001f4410858264644500d00c810450450200320041e11001040012034000017142500c1c1c6905100003400382c0075800040c00c0940c40451091203605001604200319800b983c2644d480c0e8040030001ca8864109015070070210b000680104080d910950090078282c1c00f804401000c9016540000c2c01e44181e6400700146944030f20b0b090095240521516000708801c48500031400f5420201810580e0184805810302101c500001d8045504d0183d0305448070901d102503941c181c9401e50010f500c0e00740da0055449108a40c0f4a540d4102c00080700c41c024150020f00f1030420607401c40482c00382c0b82c04480903041090110000918011100b016002d1149649012803050b04154144135014001004c1c4000c16050403800c40102c0c0e0800710b0004289002e2810aa0380d6 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 114178776 1250 114177526 114177533
    0x90417070c050925020d05090d03050d050903090a06050717160503030108030712020102070c18060806010906170321060402071e0506060a140402130b0307091a03070507060504 77
    0x1c0c25034003007500030304001d042043d000d079025040f0030b4a403218090240200e4041104030303607400c05400b0040c040341041015402c54500a2098a8550f1203071a102d407901e080e0600c151b0981d01b060780c9035402c0350f01c0444c900b416031802c1d01d2030001400300b616000f4201112034443c06c072698110b11810441c0800041c6032205184074140d1640b036550008102d03a500c0d651025290b40e6a07008d8801942c051407080a140461403040c02240c120640000d8406201d6003003450501004000f4204502180c1e510b083c0041d400005004150082407115400901c4030b24003445255000e20303800744801f407504100b0408141e00c13072503d5255544212407000ca4100c0d40c0e50301c00701d4000d20a4101c094600240f840f584882880d250381a80300780c80c810010b4030410784a40090100161a90280700700c3c3c2d0040d406510f2841c2010ba0190100b240c48040044d0140c0c4d0303592040c03059500c151030100003d0207811081c0311484003824041c4455500c402e1140c5140f42c205002002fa00544c10300600290711080400d060 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 114180026 1250 114178776 114178793
    0x702222a080423150406150302030d0e1f0305041103150a020a021608010209120106080703060b030a0b01030c03060c08060a03020d02040902061c06171c18090207050c09041707 77
    0x8005115045607110071503560116003180046404031159418808030300f00c1f0300e21640c450021244d01600510840200704402d0319401c1e0350300c9d07031950055881c2080309048281d102c00928048407507100044d03030782090f003030444440304d0301c082c014000e0748802c0c103e04218400345949948140304010058a0304000303c0100c1c00c10880a100c1807101c1240030010510101c1980105003220084a120342e84400411265090741c000d48110100d41e00110b8081010074516040014100c1004003a1005248a40d0b02c0d01140e41e000c2c2c03c2035a1081040f40b082c0704200c07040c814441c4c94051070620440c18a071650002d00c20815070300000b805100803036803100031911682c000e5815181c2c0100760945030800c295920b0f410201d00000c06079150b0403c0030000302c2c10b039042c011b04940d0300705202818002156820700b4541802002e003030340c100300038010b02003180c000310814200540b881d01400350760769825090091400b45c10402d220307c285220380c24040066503031100030402080d260015626180c441c2008460b = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 114181276 1250 114180026 114180083
    0x70e0414060711160f090908040503070306050105010f0201050907150c0b010902030a0b0a080307030810120305120916051002011503050304031a04080304080702222a0804 75
    0x2039030311580082c0031103190444020f0031240c03440f00480f581d09241c82552224414039101c4c103e003120302403000388448003440c0c200d605c1041c01800d650b890560303075a011034501401603000390b80d000d80e1000107001943e8005280702a0b000b50348000e10031820700001560b01d03000d072482249204c43c115481c1c181e02d540202058049503402480c58072440da50352051002a5100701c0f40c12030240d240c00d8500c074040c038058941e0010340d66007000545c2410460b070340039908504091b0150f1900d87c03038104001024400800008080b0740310343d84191315100307041c0482890600c0907002d070000780c218011101170340d400b03000490100e036401c5034103840c1842c0c010002ea004061010b024032940109003008000d2000000003002100c1c8190084449030402e035000c594000000d65004011480c01c00124010a01140251280900041824200d250281400c0d0f0315446140c1032124080e460700048002c2c4801c0d00c1a040d1580600d014100100e0342c580380060104000820080c00e190010700800808003800080bd030 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 114182526 1250 114181276 114181313
    0xb13030c0602030f0601020709060f0e0c0412030306180b370f0302030609070503120a210f0507141c0b061209010c1b02130f1b02010b0d05070e04 64
    0x15a0b07404d0030058014045000c80d8140d025100701d04000070741283e81e11641045440c556154210141000302c180400e07607010340701a900080078040459681a03103000b1110300f0344aa01c00003141464646580e0110b000c161260054500c0d02400800304d031110403002007012040d02c8044c00e1005981412840700f400b0f0b060b004a03082001c80041000302c3d607035140d0015a80218210b403a02d580f405811076441c0303114000c40381c268101d032244c0c2c06142160000382640840a0600011400c2840f0164030407803002c03910001066261549241e00040f14800c1c2600040949455900b60190304030410a51041c0c04443c4070a440b001840c61441082d03602070a00f849004000700c2d030b1000c54165107404004252121142540303020440079a1902030256007460903030000c0039015007007050702040380c000c82e0708008500701c6454421071440c0072200c2c483c034881a8155100400300c8451600000d08407004000014001d04c0095600f00108000080d080d046590729003140a1503507491800c0c00c84181040c0d0741c83e = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 114183776 1250 114182526 114182531
    0xf02191b0c120501050c04140d0c03060f1a040608030a1b15020a02070f030b04021012090804180908030a0c0516060207020411070c0b0f0f0d050603010501120b13030c06 74
    0x10880300c0c410b00501100c42d000c0c00c024010390f00d51180301c0c0c40c903209900c540d0200b880070b00d8603010541801c280c00291140202c08080c0c0aaa50f9160745080d00c0408204117442c03030ba40c4494031029044030300c071549014000e0f00c0404c0b019081c81103440d620b00c6400d00d86c1c018071040560300e10321061000c04800c0490360040003d80598444501d000180d003201c1c0d81c0d0005030050500215070140f078081a0806c603508141000e9154565800340b01004100310b4040b41001248501d095842d5584d002c0c1541c0d1a11455105960307501e0101180e2402c6032141c07916144d5818000010086070b000000e90741c01ca144d0b44000107a0480c080070030760300d0344281049408410b5140380181c00b03019255000d408064002e85080c0f04629405031060424424100300502d2901c41801c140403845a0201900c0040c5000704120704d004035690b881c80e03403034001e21003450340d9541703480400c00681028081d00c0d00401290b00004100426940c0f8043c2004004003c840210b02d4482c02c00e05261154040b40c2d0f8240d0418400c = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 114185026 1250 114183776 114183779
    0x3060207050c31020d091b030201030c02010e0604061a0306040303060e0c030601050d090203010b0607060501080f061003030e010e090c03040203062d0603030f1306030f02191b0c 78
    0x30985480d48403240c00c3c8100a000c2e0091844502c09140342040f0484948084080c030100714020001d401408a1015265840a07910000703100c0c01104881c070700c0d011142007000c92940c40014213a03400e42a280301164100200b02400e0680083e40365002a80440302103102808003210410b00c00e410a807080c2e0610611040c04103161305a40b15074141c51401c041521326a4030300d03008500510055800b0b90010390200300303000d805c80c1903070300c041402c502c010700104071020004005101030300002c006035002e03075482e00100007245040103081c1000034544045c2043c1c1c9812444401e16000c1884080c051000440e0941c80c03507803240c0766580c03001d14010454202420108118280e540084804900920414001c1154000ca00d450681c4507030014000e010380c031070070521180e5014009403001d070305440180040020b09824a000e01f0083e185040400c0d43c45103004030040540c2e8a00c50240c166510405c0090940800760312100d810880d10304201800180c0610302000c10341540d0006001c400b040c040 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 114186276 1250 114185026 114185033
    0x1309080a090906080304060504030b06150c012406050f0708090a0303050c010b09040b01170717030a021b010c06052212030606140712170f070807020a03171003060207 73
    0x4080042d0740142c00204011511000303a1962842035004260110300c2c10301040001844d480b69881c0d0000b400f40400c901160010881c007081c2c1c01c03d030305802c04d81c6d44660307102c80c001a965500c1c4000c0c1440d10040302e030030b030b252140c09000c1c2c0c070640b0342c207051300c000004003001400b445600315441440003a00c40e40b1000e541e03040050642d0040c04000c0712035400c100c104425458007e444902543d0000c0201240383d2030000c1c000705800c8100001d0219005041000542c0088400101c91109002005d541c2d10400440300a052001007510410003500440503c0c88999000c210100d007580e105400080685583c220b07160200819910035040c240342c0b8071010704100042120000c1d00410380c43c1404050348611040d00c02d0301446c0f4012290f5403003400524081421201904000010341c14200a4030103529854131400204540f002030722013510042c80b45a1394450b01d201c3c2c1c42400c51000d02242030302c9030f5008000e41c801e00803001d51003040300f010846236245148144021a440042195200b01518 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 114187526 1250 114186276 114186287
    0x30b0403021e0c131b0302090f0607060902040c090311040b0f09040c2301050708131d04050606120303160504090606020616020c060a0c1a0703020d0c030c0c021309080a 74
    0xc100d98000c082030040745086900c1d50044004051054001250175829140304800a4021100c070513886441c25601d10420b443d41f07402041140d0040c4404200802d0720b0041c002035602c1420341c82c1c01c20104620401c0864807084500042480c02c4801068200c5503000207100404c0c81d88407550300c00c29a0003404100040300025504550b0728103420702c0204840004d81c00820050344c180303400304004100e44e50002d641000108201c98140c418482c00584504130000100d00b4408507900300d24601c4144403d2080400c981580004100c410559501c10b03400c45036120700029100f6200b40c42c10300103a01406c0d000b20140c4014002100d0708129003507035510300a540d000140c50603810012030982d52441c4d20704c040340c40001020050400e0703107816140c030380031602041085000da820f905000c4075031203455040310005016425540e80076840319585050071045491f101150b0007410301d4000c0c842800c40d000301210842070340403a180c8000c00b000e802c40d10003400c01c0690040480308002800080e858018 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 114188776 1250 114187526 114187543
    0x11806030c09090b01050f0a0608091504031d031f0e07050316030c080c0102061603060503100c020d030b090601050d020909160210110f0705031c0c1404030c030b0403021e 75
    0x84204c2c1e1140c0e6650401d2000f0510700046c41600a019803c05100b202d01602e84c8076000580c0d03038121800c0590702500150042d1050b0341c2140054080e44042c2c1c1ca11101c00040c56071214100c014103031881c800c03280114181000800e0002c41a22021050800403050099400a11000e0103032062100c040484460701240c81c003080391440b031341f074802055500002804d804a01410b800520650310b403481002008044604401d04054503024042000e443c28003180012031490030020070103401000d0040e0410a290040004152802e0914005079035822201a0030840a0070a02e83c0e8050300d40d0008040c1c03084002158010750442c00b030190129550540c018041c40130750a5400e000c01524112060303d40250070082816001d001c4a440360724070708000d012141c4140c040328544442c60194055643c20542085001a41e030944a540030390801d0503000c7c10b2624020707480c42c0078215555640c19040798000075000000c420002030401d80200404c0c400968010008520841c001c01e141e0341d40d4049 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 114190026 1250 114188776 114188783
    0x20118060b0315060d03030b120706030c03060e0402010f0f02010908070b04111e040c090e0a0606090f0305070902160b1602190201172a040f050306060306011806030c0909 75
    0x10001003011082c203102d43e01c1c0c0500402800304103e0016600d00300c01509092100960020341d4481d103150000c41002107000030005600c000c1021650400040c0480b0350381c3e80007030441a9103400b0040142c0c1d0094410442154a0511010740b00d5101022401000e10241c01804c0310390020710241848108039240d44290f02c42c0d041444000800010b20004065140c182240e4803400941c1e8151890182c118005407011031030004a080d503210aa044889410b840039000c484d520f2000f0304c002c640c00440c0401a100300e586049095103075a40d803542d104040d225032030709a0303800706041095000391080c0240b10f03a00440c0c42680ba0406055010448042a811501600c01c4004110100c0c1c401040300c85419016101c010098551080350682004014051014190240042070a1600c007000c3c07002440700345000141c03100d08281304285410129004180700c5d502040801007607036030000345103041d00c40401481801d60301c0e00f80c3c0749014048030b030801041100004004030b8009042d0740001e100a00 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 114191276 1250 114190026 114190033
    0x4060e01021b0c0105070c090c031404060b0910050607080d0207020d0b0709120803060915190509091518010603020411070605100b09010f09080a0506011e050a090c020118060b03 78
    0x11a0055030117201d1485c001f0300d00030355028204907805055021a2420800d4103010880c0800503401c41a0740300100c03000c85180c0e90321103c000356070030210f81136640451959095076695050000151b000d00841000401c0160f002880c0e1880d0b90440c1c0546140780d42c0904610050941c900d05600050412110b000000f441e9002c0081c1140032020f03103004458120040518544980c2c040c0204208024900c65681c1404480f01020382c40e020418040d0090b40305d0b08803001030611040180303010000c0c0c200c480b41c1d030040c8490342c86040f60380300c12500f04502d05000c8982d01503d8080c24090032050b030000c0d501034580880d8828000d442c500030318010303118a00400050351040c0410601c0f200d540246581c00c00d00f0312035581154081ca295046400040c10002c40640e83c82e8001841c001c4030b40b404840903040b40004010300a07441844a01d002240d0164144481c140804101200010721a0018294403034102ca02194000c0d0701503580c0000c6170741d100364800154200721014124200045002e4030 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 114192526 1250 114191276 114191293
    0x4090519051e1e0613082209060603060909080301140d060c080703050705210601050708040b070b06060c06070509011e020f07050402180d020303040e01030f05150105010c060504060e01021b 83
    0x290702165a0317104e03c04041010a040415807258443c1d40c102c00c0e0010042d200d400c0c04038401c0301031411424024017039100082401030800f00000d081c1d90199104a6182e81000660b40c0062000c40549040d100441198200039074148001801940d085070003030a981d1500903480a851f51001c00030b403142040d5203051205455040c030444540c400e034908811072020030500411503001001e90320f40c00000524049041c002152200340260b030080e8460f20400390700103112000c12541036004c42d03000f00101c2c1e40d581040085048540c903542d0050852003004400144d010250303001c0c82d2266200440d05c4c4400404590b0208042c1d583c4a0f143c40315045840740c600005941d00e018022075081d0340841c03855041c05000c202c184000c0444409013240e25000a10000c59031050205000c1d000318000c42080e10741700c4036410400d041c101e45030012004441d0160042c44666085040f0b41a1302e5849a00058160ba035401c0c050002e00807000f040c03510b0b5000140c081d403985451640c1010620380c02c0700b51000407 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 114193776 1250 114192526 114192583
    0x3080a02120c0604031706241306020303090705040b0907030f090b0a140c04080d0c050a08030c0307090b04050604050f0a0312051e0909070507050a0206070b041104090519051e 77
    0x41b00850b07501e6807050248800607100f01d07a030308144288506da010101d0405646511006443c80d141e040900103070310200c100140b4110810012004200c00d89003003004400401c04034003201001403d04060507180d4100c02004822980401030068001c8494a01030424a10101c003905003030200c42d0205c9011030110b080454260100c900700d81c0c4142c001c003c403580c1c2803400e6403540d45081060310f244c062401a03001146d00c8000651140130000d000382e41d46d00d03094801900100c9948c02c00b40d96075906003c01e0003070303031070711800c66090307600840340300a2604650000598001c11904014001e0b0f85c0c3d29144805a40c108000d41064107401e080340e0000b00c85200441054080c80b001684d0140300701c80400d1086000d070004105144c000c8061320405107550f0041409a070003443d049856024200821041c0300c2c0034004c0d61107581003150280036100701078070b80594034000041120201d030030308a02442004001c001c2a1140f4200914102d44050b007401040e4441607010581e080c00300411802c2004c2 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 114195026 1250 114193776 114193817
    0xc0901030c03061b12110405030f070e090313060c15140a0b041b0809070b0f03010302010f0203030f040305130504061403060f01030c03081812070302030f01110403080a02120c060403 80
    0x1059443d45c0c0b42e10a6408650646000d80042462088403c41c10800464651414002c141061404500401751030b0715080d112a150307a0010301c001c08540042c09090403442480744450b04176449890030001c040a242030490913406000d5565291900c1c1c220000d030700600e40d45030103119201c14003080111159041c1404140c400310903241c158820580c1c50400103d0141d0402c582000741b000c2107403800f0341c031078005c0d08507035204c56003000783c05601000400440d0b0b40810082c2601040703202450450600c140c4040114201400c0102130210116480748070840f0b00050000415000700180416a56101103242a102c01e04841d0301074014400041c0940d490b035441181244d500403c03044615246444100f955004809000354644200a454513160744a0b008146c030008446e01510655186204044c9000800031480e005641444440750b22560901c0c180d4040b00d412014540d520201c0714822400d1480c441400300001c00045629481903400081e0288558400c1d21131041c0d0f0045d80454001 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 114196276 1250 114195026 114195071
    0x7030f0f030902060909071808161505030a0b0f06040b0409050108160909211821081303020a2702090907120b030d0c1502030c0a0807020c0901030c0306 67
    0x410220810841c41c5d03e04041084c1540300780245020320402501407042c65210003194000b0342654046461188142e49900c039000040615680e219441050300b14090070300c1c000148144011039440c200c1c03001584a0b034007840303200c00700107010580c0c49403121000e1840303410a01820305850700c2d010000c01c00040010351070b5031b5000c0d940e0781f03c0c042c0e51030560100007900c4084021194040b18406500b200e0b11105100d0980c01c1e801d40b161200319030700391810344424038030398405040e24010340703003010fa06240b0541607415150030042065507100400c203100c1c1483c0075580000d40103103400800040303801c80001007164198504420540b9818076038889002e034003615405c0c55109404202040865028917800c80d0140340803213000c00c02c469440006814445109184004592034101141c200150b002910f40e22031400003007103055042610318800d0900607154004284100c2c1408070340e60354000c021250607000014840c492968607450305521440451200700e804d40d0910741100c5000141c07848444 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 114197526 1250 114196276 114196279
    0x90c0a02070f0803040b0d1e05010608060a060f0f091a0301032003060c030a0f0e0102091c050601030b04151a01110105040b0a020307050f0c0109021c050304270207030f0f030902 78
    0x45c2403030f0403d60603e1150f80700748408901c0d82ea40e10301600d030200e00e04e8500103854091640000d881e40c58040b000c2c02c1d1000c000c040303070702c1060301c1c00060100359004459040c11028900c0d040c03042c0055100e0548a0b10301c260008461501c1c0a00fa420800c40f210740194140c0c2d1051a03198070105460044e0081d01c1144000760750f0540240e030019035440d400390040c692152040d880450081c40c107841020803140f4898911040b43d400260207015801c1500c01d080501606a440e0700d03417032606480351034581c0e0040c0001850811450045001d0110303407030382000ca503000d289081090380303c103026488402c20128405408224403501c240200c42c41071191510031303070301b26422002c240c0d1107085110017035200900f14800e0000a02c0221040e01554005d8140e0484d107800025641c03440340100251007829180c0da48103402003881482c000348010042e00c0846903a0b0352404503400c0340041c0702800550010801107511303c081419410325a1281da940ca184815071200f55500b085402c00714143c69200343d020b03 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 114198776 1250 114197526 114197533
    0x90604021008042a09020d050f01120f020904060615020304030201080c0c0606010c080d06060302070204060b0304080a050c071710050c0c0703030c020a090603140c0105071101030b030a02090c0a02070f08 89
    0x8411100315201c0400010313503034480d920506900c5204a408a030050712181c4a02961641040510800c0454043c05404182c210003540215540d1789600c800d03400300028043c540e4440882c0c100883c0f80c00039400781400400ca000c2d4450040e01c000e6590700a8402070380064036000c08a505200b03c2c40450f9013910010000d0b00c03480c2d96417001961030002030507084840c610204050342c20702c02203105100140400d5600542e94803c0707801000f013034900c01d8000751000e00003001480300044035582252803040c0981442c0f0b0f03c5001c580c41c12400d0180640c00302421009000001c1a00c0802080c00d081902d1a10010803064440c85260004c3d0f002c0c3d902e10b00f006030b101d400144013180c01512801c6000784001c010314034881d21004110250703900c6901c1110a032002c40307540400e8500600a202c40c2c020203180c51414198203450b80303d8080d6080284606155032051056245c0d20103104035481c1c80d401a01040e42c03800d02c1c424800307450344240211401802064404540c00e04583e01800c101e40b6688001e = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 114200026 1250 114198776 114198803
    0x3210209090c0304031101020c0d090f0e061912080306090916090e0715051e030c090d02240a0f08040c090518010903020a02090604140c0318030309060402100804 71
    0x402c1c0341540702810650500c00719102021403d9024002003414903035081c09028900216036026015034280d4104841d264441001804651090b10225030722000440c1e0111080b080340001030301d200d20715040404191f03a02d580d00380c140810a4001d50041805440f00d11290380d4801d40161603502003a00000e80c028182c004010041307450304441583c030400340588091039600d07041031044031200300f10310020840c007185071030302c0400d040642c8400341d2000c0c12142c80c5140a1881c140c00e4450700c00c20611401b284075510b02036440350a00034603000f1200c072580420441e0040e600c21340e41c1007c08140d0001300302c01d03103099072103104002d41c0e4022688281b050203100c0c00d00000002038a0f0041a07521880d0440481120130203090203426404c40c0650081c01c1c0f0000680103006191038010601c60150b4101110244050051110039510450321880c1544a441e6450740080141080a12440f00c0c403021090094110b4003152141c0618401c0350000020004000180c6048200300d80c05001c810b40b0180 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 114201276 1250 114200026 114200041
    0x21206040203241306080a12090e06100909150f08010603150207020111030409051b07030507030309150905070f080a030206151503160e010e240403020405040321020909 74
    0x8141c1c28030400130041401c4107141c4032003030110b4655600144e001d6100d94409002d00c120001100600f101da85040e1101c03500b00200c401c44002c1c09488030b80998500d480c40400c00e0306ca401341c08050412258203004042050400f041c0ba6000390141802c2c001500c41c00040000f414400c01c02100e6000700e001c159201b0300c0340664000e4100d1030080e414444407a407a0303d40d54030140014400f51804d00f200150130304080072818021560f0300c2009a400b001040300d00c002c44e800400b0b551000381d1502e80404c008889103800b13000c0301d07071008250b08550b0500724a01c00b04030010070b000b000d403901e5805102d250f41d51003080e01d03580d29400f000a000744c1c11500115000c4840c1c241c24003420310700606054800c000c50040e09515600488040078404502d00c2c401d0300e1030b40e000c030310ba00c1c00b9042441c2c140d13842c4034102c00103896203610211540c501d0f0361000800b0401c0d80c644068400940d002031082241d40380c181006001400e000340b00308080c40caa50040143c03507445100fa108210740160202a240c2e0719000d = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 114202526 1250 114201276 114201331
    0xe0d0305060a0506030103120905190b0a03060f170c03070501090b13051009060e01020a0b07030c030b030d02030c070e010b0909090309040606031b0203040e0c0307120f021206040203 80
    0x4003402e82104500402160300d45800c0000c40c025846541c10400000c2c0e2020020b01e01c1078983c0055210302c2c1486060305113041d6000341d91094405004200755034400c5407105400404880e0f01c003280010b5086400201c0c07043e04400f05007102d503042c05495164092a0400d40c880081d4000c2c0303408603411850a100d070000788400b520b00000203c5424500e030381c44100054290010740c1941d070009200c21000c2c00300703580c0f0854068000c0303000c0c001171148200c180d40e1602001d000511100800da0381d6020503000074407940100005403400f0b42130b500418418080203482c1e901c03480e0103c3c000d101300d4100281075000c680300c4604a4281912007414640510200b1242c40c3c8090001220340c030091214200595813031040e07600600c000c2d00d0025940b084110b8078041d5400c0f1140103800d54100381700421004803040410340d80300c03108480070342e540d81d40c0080c29540400100d84d102c262030318040848151030b03400c1e4010b2007810000907503010340759030344005c21050344070894840c803504200b01c4410500d0a90003 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 114203776 1250 114202526 114202531
    0x9030f0f12090d0c14150703120c090f084c0605041b0806030c0d0f14030c030a030b04020c150421200304030c0b0d060315020c0f010e0d0305 62
    0x500f01c03401088503444c0c0030030200c0607400524081c0341d0503640255916001c03001d803511a0908094604011036610040d00c52140d00c003842086544800390406203500c260201400341c00c2600d04c094805807143e0314581d4a5a103000c41c9050385c1d503d504010340851a0700d42ea10710800031412910b81544844036612180725180e401854080d441e824046900e56035801446061001c07035018040c1c03d10030580051038000060842c600a03000031450346110b460b00d19004004603000740261b10f1003150361034203000c00c18101910f00b0180c000400c2e103030401e0030040002d00c4c2418590f6814058880810208400c910450303d0b941803944c4603010303603200b5000b00c120103075015001d603c07090a681002000c101200807008a0100000c01c44082c1d0305089006103194040c82804000460400303046640701c0300d95090320f000328080d03403501213034280d514002c90300800080c6a100044d00071141c0381085c28000383d00f00d9030007072410740614402403d150360b05104da1501ca11286000b00903440307030340c003003030b0b0003004003 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 114205026 1250 114203776 114203779
    0xf070b13050a080c090c0a12020c0c0405130507080c0d03110f0304080102040e0f040503030c0f0c1b1804030207060e01031803050306011103030c070213090203070b09030f0f1209 78
    0x3104000a8150340781c031040001084000060059242280104150140c2c01819102e2014082c0a14080568004040107400361941ca0060b96044040c40c41c500c1c082000d0000317580181810300700b000700c0122040e100c811501c14021200003d8580000a80394011074844d0398203c05480b1182c40440d01c40c551480c810a159010740b503000400c0b4042c03074250341c40350b0084c0b041690009810810604680e0130598001071903540740354039041c10b41d902c0b0b03201e12001c0c0000390034400c045000c0e04001d200d1000c64048801c3d013011038a105414a041402c1159405ca103d07100e8030f61005403520040d5003000c810702c200c0d410b40c05009072034203080d819281d0851030b00c0309904265540303d455259103115115032007800c0c0251108e50b03c1e8900400010180d0541c10500d00003500107005000c4461005415201d1241d81201e0599282c1d420001000003021403000c082e506100303200740040e02002c603d0080c201008260140c5101030581c0603a165079110025a000c100d501101401d6961440a409400110700 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 114206276 1250 114205026 114205057
    0x160e0408070f0c080f070603060b121017010605040f09210203040302060d0e06070906090302040f021909031202150f25030b01021902010c0212190803090105090f070b 73
    0x240e00c0e449810b42464111084d07907402480f0141e1300714420030418008020a2405020203405c1c800c001c1491300030700240c80240c968005c04154a5819030903a8006080041c94030192007004180d624080d107820300c40c880c0250300c0c01440f0b41443d5514041c4080c441c0e00b0045004035400103180581020328841c03500310860200380004001030b501d22000302114019080003103a0b403e840f400450030900003900c881d051040d072160400101d80c10842800460303404030303400251604034100350300c00b0384214058440145da0050b10700c1c81080d046082102540d000b0354480e0741d0f9040000c0c050341d50b0010200b450044408240014044001240219601c0f091151440000840d620b00c0461115004000040425100c8001680c1541c2c104034440c49a5640982e0300000c2840d90006010303840c0800d0003a004c2c0c02240031601c480c400410019807030360341103110711050f089e1500f4407584075081030b518451a5400d0802007400340d540003d10f0440032070980050300c5110f1074090b02c0031081d030100c804000f4080 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 114207526 1250 114206276 114206303
    0x218090c0301020a0c020a1502060a180c03150605040221041b060207030b06030604080a0302071406010f1403010204050f01120609050f09010c031b0e010c0f14160e040807 75
    0x4800b80041e04d10005692501c0c100305200c2d10401a000c034080d00401515900035404049160707002400c290801002d060005e200180315216040074143c80300049c0a40d0001e1100004101015903602c0342c0307091110341081040e4881c17040006912031848408241c90102c43c881c03540c0c1e603d44821640042c452040e0184044034080c03516440400323580000051b822807841003090105000010380e1003c401ca014006502d0540d51b0442e0500401240b1001c141d40420f2050801c40c801e809801a16495411100590394401907400c0442c050f000314140740101e04661100781c00c3c14000d0302d0646100802c418105020703403004403145901c0124520301280c0b12500002c2da20310a11030213000e09800c040340a4039203071404c54282511003504c8030400301403030031441c0c60114014048040c0030b42e21920302410100b594000480d1050024000906904540f01200041003d190001d1040c0190403040d15100251814904101c0c0010310030b038800003035600d00003000254820024003100d803296007024841c2 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 114208633 1107 114207526 114207529
    0x6010914151c0809011808070902071506060201020301030b0601020f0a030503100806010e10060807080112080403060e061f06051204030504080d2304030218090c 71
    0x14980d28500d00707440e5500c00c200060001510500404155140e007488812640025042408140d03070381d91807041c40781d42e208400211135030302004e020024940700e1590065401507500b00c82c07458401e46c0701c9a00717010600c40c400c007600042d1b00050b16507041d860842d484c2c4801070156415580000f104140d245400620b800300641d0510300503885e0745510410f501c8040c0c0030303003049030140240c03030000c0740b4118090091751242035081c3e01412140ea440809881140060b00c400300041c0c917181c014445180b001c440d41c5070640c8945003940c0741954a440354411941c9041c090a03954006206000703110825604110000300040d0000280c0c81c90a50041c00350b01c914010b240350001640002010f050080301548d005181a1042da8041c10048000604c400d003120b074200b00d82170000050041c00388040003690140c0364042d0031525044002e860080c40b44400130718150140c402c004c1d036500e49 = true := by decide +kernel

theorem cover : BRFrame.Cov 114028776 114208633 := by
  have h0 := BRFrame.cov_init 114028776
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114028776 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114028776 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114028776 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114028776 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114028776 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114028776 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114028776 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114028776 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114028776 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114028776 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114028776 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114028776 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114028776 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114028776 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114028776 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114028776 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114028776 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114028776 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114028776 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114028776 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114028776 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114028776 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114028776 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114028776 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114028776 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114028776 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114028776 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114028776 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114028776 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114028776 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114028776 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114028776 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114028776 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114028776 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114028776 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114028776 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114028776 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114028776 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114028776 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114028776 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114028776 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114028776 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114028776 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114028776 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114028776 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114028776 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114028776 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114028776 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114028776 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114028776 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114028776 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114028776 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114028776 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114028776 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114028776 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114028776 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114028776 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114028776 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114028776 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114028776 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114028776 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114028776 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114028776 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114028776 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114028776 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114028776 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114028776 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114028776 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114028776 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114028776 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114028776 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114028776 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114028776 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114028776 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114028776 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114028776 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114028776 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114028776 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114028776 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114028776 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114028776 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114028776 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114028776 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114028776 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114028776 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114028776 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114028776 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114028776 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114028776 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114028776 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114028776 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114028776 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114028776 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114028776 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114028776 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114028776 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114028776 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114028776 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114028776 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114028776 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114028776 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114028776 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114028776 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114028776 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114028776 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114028776 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114028776 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114028776 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114028776 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114028776 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114028776 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114028776 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114028776 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114028776 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114028776 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114028776 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114028776 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114028776 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114028776 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114028776 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114028776 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114028776 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114028776 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114028776 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114028776 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114028776 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114028776 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114028776 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114028776 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114028776 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114028776 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114028776 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114028776 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114028776 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114028776 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114028776 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114028776 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114028776 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114028776 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114028776 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114028776 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114028776 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114028776 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 114028776 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 114028776 ≤ n) (h2 : n < 114208633) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
