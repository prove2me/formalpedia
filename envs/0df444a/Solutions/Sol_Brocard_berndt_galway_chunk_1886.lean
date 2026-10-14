-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1886
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T05:02:00.243987+00:00
-- url     : https://prove2.me/submissions/a0d71362-2dec-4eb4-9206-cd176e11e1b4

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 339028776 ≤ n < 339208633 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 339030026 1250 339028776 339028787
    0x5031014010c0f0c081204030302010605100c080c12130501171519030f0c0e09030a020c040903050706060906140405010e13020303040b031006140909040303020c011514030c090403 79
    0xb95007000e40002c00e040140f40002041800354800040c1e40075903c5401340b0a100306004000b10b9009500070b001250b2518104000c0311200800480030031842d069100c005041c10303015001d80c6200d03a084c1c40041d404465920000c0d44005500d100108502c0028003031517070031001c100c4400c681c901c512410783c903050292807032550411000da0703c10002e403c08450090b900c440300a003d107520003e030003014505480c0201c4000380070700400078201c0a078030004044190000540d04116070945c020825142614103003c01030061440990070040100002d80100d00e442c0102401010020000601a854034011150248840b242103100c0ca05140040200c3e10408601d507812825070009030780b508102d8030000e844c41c480e03076000034000803000c000c01804100c55602101140c80d6a20341520f0907142040100440c440c84443ca54001e103900042000310703100380c4c007401e003007880800005200b03841d51044000c141890313403008190301480e0b414102142070901c41c0c0e005068040c0c80c1c185450a0596002c1c0c807 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 339031276 1250 339030026 339030047
    0x40209060909030904020d1506140706020d060b13031b0e060f0609100c0507060309051005090c0307180e070f030803060301060f18050106020c01051803010204090c0503101401 77
    0x801e09611011a411840c14802c132262a00e00510855070b80200343e028030050300c4220601039003450441c20000b0700601841d5100b40001c0030307052151600f4440c2c0c3d40e11009410280d02c8048103a41c550021503800001002040f0300325001c0c2814000e145903290400c0403600d0100603041c0110041c000300300084c080441607420010803100383c0384001c48031002c0388a81c000c1094035540503515205170318559400c2021800054046d03001d54050985400c800e50a60f90305010042c0b0680c403511400003ea01140d0200d40c000342d5038400c0d01d030403401c03640000380b8025407600300480c000c112141150359050244610141c0010404c0680711161520400c00640003080c803000d408110000000f82c007640c1d007903104002800001c40400b50050300c440354440441c8101c091100720300e181000100d885400028400182c540594825240c80d901501c20007284400203180f50b0550740034400840c108400d0b0240392403103400e50b40c0d40c540f01c1c0f401c4161500d55610316401440d280401140c070319003d9074800503680 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 339032526 1250 339031276 339031279
    0x150a030b0a0207060603080c0d020d05090904020a0302090108100b0a0b040308071104050406020a1b020a3809010f1805042304081314060a2601030c061704020906 71
    0x4829641c0d0908000a0f00c18280c1c0240040c3c6001004010003030b0b41030140018518030003c03102d050241d403800b80e030358104910410000c01c105204000e5140f4007140c00c164040c0c030182042d8480751340c0342d021410045081c0c010401540120080c5041000c052042e046451030894a80200c0380ca0040d80084c0d0384900d0001401d00307540006ca4005020481d04003c1081401a10070007a611b02803c1480094104c2800702c8002a01140304000d0783c25036008600d00c03941c0092609561a14004201000300024951801e2441c400b404800907511884a003031400c03040d044560741c5d10035034400010310604403030f00b007002800340200d0020319101c260b880600c00e1700c0047d240001d4800a28004050354140042e0108511602c202003104020302c0101a00d02c00030b0007a4007201e42078070750700c00c201008005600560402001d00a0702c690910860590081a80c0d8050702844040d60f075400c80e03c0282d00f40c105403581242078000f0005113078850704000383c12400d8800c059103410142d001810340c100150115 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 339033776 1250 339032526 339032543
    0x603040b1b16020103050a02030402030705040506132307020307110f2206030b011a0f2a030703120204140f030f0d08150306040305071b05090109050f150a03 69
    0x1424069038030720240000040008600c1c0c40c0c012030496111140c0441c00100e00082c20400812802c22444c020340c0d00641c0d0040161101504260512000700710003080c0c10340c0802203c0c221006444070344100e046504c6d9003c41d4450f00f11100c80b003c41d4105010f030281045601c104602c2c004980c5403804042c0c24401100c0c64500f00c601800099800f4510309072038501d2009100700d00310308007016400f1500301c0e44a400d961703001d82c0c0e1320740e0100c11544a104168000d6442040140c030301c0d07465200105061440c201c0c054108078682441c42181c0c000840014106620016401c030a06030010a090011030342080294542428080782c03049030880c2d0310001d402641000300f154056503040c4440015215108200c42d0760544240c4010300c01e14041d2400c6203564100d24441503a4100417800501c41c4e50162075045c54140280d07120a04104155814120401c03000008140342d83c4000d1624020010030b2400714803402c04526680d222071010f006010780a8050341c1c8120720752181d20060007101e8000c043c4 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 339035026 1250 339033776 339033781
    0x4090204061a0421081b3318030f091203040807091116030f030e010e010c031406010c1407030204020304030f0813020a060c0501060e01060c03020d08010518060409050607030515010507020603040b 86
    0xd94034100184401e035105600c41f280c40c2101c00c0400620320200c0c0f90403100010300740c840c00a9002e000940e0510514241c0003005403d9448604400404040784c0140103020340c94280c41160741160070a4004101da50420401003010550600504128140e640d103181e2401c0c402d00d05218517110600002400c2c080340c02c5c03104030406d0090344090754100c4043c000340441c40c0311510440c000c00625100c0c0c40072030b281c81443c0b040c280401c49804d109403010385448020f80d0f62a11900c0d07040007411003040340c920420307074080700588550000d54000d6102e5103e040c0d1100d02030300702a000c20f800505107140c3c00c5881d100f11025030b80300e1211408803090f505283c3c8003808070f414158003414007500702410303a80041d00000b03540d1340d000c225103883c5402035082c1c8035a006400c1003201c07800801e21615074001d400c04501640220000401900681c00034000650511203946444c2088011507424001c02d903900c00b086111081c2040180c0152402d00c0c00781d1916810b98001140d6020140c809080007800b00700 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 339036276 1250 339035026 339035077
    0x1b0f090b030a09110d031e030212180304030c030c051f0206010302090604091b030b010e24010c021e10020309061c060302030609060907060305090c04090204061a042108 74
    0x2c514003026000d00f0300d441500040c10064100101f4800b145414505842e000e04498824800c1c0e0710b02c4100e00000e0089501c80c09402c1c0385d10030b4490f450079203501081000100140d80d0320019001188103000c0108058500304c200300340e0b01031804807031080e9100c83c40440a0b103a808209070381941d5040f5020640b036150000410005d15022000503d081e42601c82c1c802400740400c101004c907442986d400095a03261080b03a0312035a802d903218000e030f000003e0442072650015800b0400403c06242901c400401600050343d1313900c0d02c0c110000c910300e544050703440504020744002c50225080c001035182001c0305001c6903032032194200c0020b0311429000394100c4442c05400c00130056800604407500c4d400e2002400d40c5038074050352046454800e00c900000e0180c080d000301e51083d5000400703070038824603050611024254100c0100c0c7d00c20741e00c2d100810500303031107440c04403004005105a5165410503610400c0c020140752010b01803840e00081c1700000e07480d10110b0700f011844006030b1b040c00c05100e1 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 339037526 1250 339036276 339036293
    0x6041d040804051908060c09030a08160b0a02090102100501080a061d0105091506030d0e060a140f04090e010506090c0d0e0a0609020301150312050f070203011b0f090b030a09 76
    0xc0003a58003c4c61060080904050708103000180d401c40700590b00f4903150f1030b240c290684516500c054250704042031b07113800b0070601c10151040ca0f607100740c03040d9025002c0e5a0104c1c0200111102d4132481d030f011a03003090f80d5078100f10403e00d0108828007007200e54103010305113640d185030100c028407079612042d0900010500d00014254819044004e00c0039044c0611a20b444d0380f540200c0080804000300092030a00d80002e00003003004040d00d40f4140385400400340130883d88002c40600a201c100440b621000100400130410b40000024103900c490400c15a03105560150500100340d03810102440944d40c0c6141600b500220b5040c2020b40d9010036990910240c01740c890809810b000d2501c010090102e540c207c8a11184210020003903074190f0350740d1440200441c04090801d482c05040700c200345000b44024a00400442c4d415810001c2e1580000e00f500d0f030315443d2a81210442c0311030b640c102d4100403030782402030303103420000009800e10380008542d00009000700803040d120242c0300144099035 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 339038776 1250 339037526 339037529
    0x6030708032b0e01021e0403150e030c06180d1707180e0109091101050304050c120a0c0b071407120b0402010c0f0b1009150909021507140c06041d040804 67
    0x954107103e0780854282e554000d4000e004c2040f200304080003c407444180d01d001f01c0c2c0a0320741c05500441852407001d044001860907445215403480704015503207600500b0081a480390420424502a030300d0300039051404c00c061082d4100c180a20070081400d104280c1c0362440d4000c1c1d451502c1c4014421409042a80200719803141c8161a2003000204020030710740c000400e1280507000c9154000040c1004503424803046401030140e4120085c541c070305141081d0414503c03c80e000494900c0320345921006900000c9907c40c0040900001d04102080900c05401d400360400d400900440d40c5000101c080c81c0311000c3e002448403020704009000c682c000c0000758140d64000403800255503091404a4081e0010744801e020702d41e50400c0040c1203200d0b07014440703a003524050341800c2c0600c1d00f04c000010381400403003243d000382004c070480300b242c16007806099420301413410300c0c00d44101c250006041c2807040c50550300409081100b40704c1c4d030b104004406410401448900c5039903031181007062280c010b9 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 339040026 1250 339038776 339038857
    0x110102150901020403020312070510050603120c030c060106030608070911160503130f051c0602043807020604060f030b190501090905060d0b090a15140603070803 71
    0xc202031000a031030543c09081903d10980441c0d5200d42039640c0c450950044920060660f80400034508441c0866044030f6000f01020b0700301e03030118114801c0c15290342c01403805120340340d10103c0c13950480318040209034018103d82c2000c20a040c00c0080164407980705008202c40280c82e860444076808201d000c594000c0e4160080c050902d40c1031500a40303a60042484460110305c0d500c0100304e0142e4054100c2c1120350080c51030581c030b08900300346006420060b8081d80d006600340300000346145101d88018102c0103140480e02c0301c427423031320316030f0260307442c4110340d03c080b800a00c441d00040c2c40716422582600c00c3c0c1e06061440c1c1032202000c43c042c03c9500101c0c0d03005012180e441d0084140c8407c0c0e10f081d0f620907281c071603800b074640d4441d00c129a01240c01d95407284002c2108004904030944940e001008001a1685055103884080040003e00d554010096480925000e1a2240d00300c0c50b410920460140428501d00303818070341d0b2405003103070440d6014800b002c400020f205103108642c0d14800d = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 339041276 1250 339040026 339040063
    0x50a20071a01150f08010503030a140f04030615090212070e120d091d1311011803080a030c021605120a0506041103010b240307300b041503110102 64
    0x85030522443c0a504045405001c102d25041140d0041c0c0141000e034144e0740c001d0001c0d4186495071400301c50325040c0c0f4400f2071000101304a09003800300c8402c0204081e5000d00000301300586000d040821801700341c0c0c0140c103c20320500010395044d84041c0c215401004901e403641c1d00000e02400600b4244421070a4041c070b10601c007010f48000e07001035509044481880300603a00003262000100448000c6901190b1070503090158800038210280320301411006240404c81c0b000007294003044c03007090b90000d9070344210228240840950601403800d403940217102410f08002040e500034428402d9004030740c85040850707080c00d1414070401507421855001402c8a1071814030741443d044480000c8502c500039428801d1808240c20202c104c9d1401c44046120740115400e04d40700181e00790170240522041081403182c81c070304c01c4030f4401411014004250b401c0720315019a0002d000300d1341d14091242c00396040140904c2003110300001c040449403c100f10780310748110710004030b060685070550180000c0 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 339042526 1250 339041276 339041279
    0xa0e1309050f010e0c01090b030403110a15060f060516080d0c0903050705220b0312120a06050103050606070f050a120c051015150e04021903050a20071a01 68
    0x10100d078866202c400800c21881801c15180e1140302c61003816001c1001008200111081e140045500601134a00740150345228200c5505092042c04150b1704224549643d0b055140503200b03013402000340901040c110381c83e00314040c0c00c900980f2081c01508400b011802d007803201c018100c42c00c002c0d402c00104060701082002070061103282c0426109441400404907590410b400040f10511070200303100b40f4103070481b0844014000a5500c280c02d40200c2c221116812000b802400000101d484075000724a02800c00e00c0c00c4811315400079040504010602810342c8035601286d0005030400c1c01c492210f01039082c00c515101c400c910091641c400c00d84100003103540302018403401c620034400e5461040c00030180205446a2640c43d002c2c44032462420001900140b410042500e0390f4181880300300c9408000070100e80203d5581140c00c5030080c5035000c41a8940302c0d056025a05002c02c00c101d0410420003007903010480740da0030540000041040c00e1014200b0910a0000420b00005503903 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 339043776 1250 339042526 339042533
    0x5030706030e010e0706020303130f050d271401050f04030b0a0207031b0c15110f0705010219080307180b040609030b0f040b1603061d09070602120a0e1309 68
    0x500141e100d101c480d500e00340f1380004091020035a48100e0302c0c2d6038021420b5403140000070441000412040341e0701e0511844000c00500c00380004142d040c2c2c140c840c5451003800c1200c1c44d132401788518401c044208841c1c0b0601c200020310483c520f00308004e10b8400e4035414082e0000120707108641010348440042007c005801e40e442c7c0013031020710302c0303a92031a0700403445006000d41164242001020a03075210b606103c5c03403410030480645074a06191820000701c0c08800b0314100301c034128094642c0c0d080407000b880319507010031400c446103060035420300000e19a61280d105c60700018080400b00840b1845401c48a0707444190714000d40314245640f56180c0d0340740d202410342550342c17000b00e40c01104000000c201c24000a0310740c0c4102d030045c001030f6065552a000600d2490030012890074151340b0040803c03840a403412101030051305c02d03107c00041c240403030141d03d051100c0c0d0240301154070150402010311517800540c2d003074450a04089071800c2c41100003074083c040140c80044441e182c4140401030 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 339045026 1250 339043776 339043781
    0x4051312020708160f080303010f05060a1b050109050f0312010e13020a0e04020306070302190e19140901120305040e09031c0c1d0f0f04090b101a0a270503070603 71
    0x5c4442c48050b41599039610456503071240424401d00302c041300c0c40f0000f00a1820044014007a00990389015901c100f03440d4801c03218003040207801d0301c050b9980e801c0901000b41c02c000725418405000000c600749a0608070080142c0f1050103060705404c502e0020682c1c0741d03421002904030b50f40c000c100d009011344030740c1c44103040c51045401340d100f03202ea0700104072320501a01c00c031401a04000340f03400c00d800010400703444500360303c0042070300a0b00208070140702c0c140550013200034081c00d080300c3d030f0111544020001d001e881a0050b0b03c55040c0c5003070b080c00180d08030088031b007207400c20f1440072029514030708c01c28210b004400c80d5038034001d80340131800c091f13491541c002d0705c00034101d8942d000344038000400d541c0400500c0d982c60b80c10003a912a00c0e40103103044034451034000c50003072010503d0111592066103070a016114444060103a000c1800f090400011490100e816143c0142c1800c0150000401e1542000307c640c003c0c1e224410600d83c1516810110342c0a4480603085031105660307640020b00 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 339046276 1250 339045026 339045029
    0x3030f170402150a02070905161106310f080901180f12060f020c0706080c0322080c070f1a0301080a0201030213090c18050405131202070816 62
    0x903800c51034011035000d144a66801260090481e1540c1c03690101140f031070303a00030a07103d410740c496480c0000d21040300340103080c440d20310f8400c0d441e94080b1081c0c02411069000c0284442a001402000303072400340215000362202d00f105840d801142510411005508146005070011074915150000e00005400030072100f01d081c1e83e5803030030340d03040d13018405426118080ca1601c078450703440802a602d8a400d112082d80e00500d00020100e05130303411765049034405400002160080c880c00c011980c0c004681e141d1101103004441c0c034601e0b0008040200800c0300c595100c01011400700c1c1000e0000c880c05840c500c288c00b0f011115040d40311501307664400c105110b2581000788501e004929850a001503904844c40400141803482c0e40d640190040d400620048503000405040020307000e0441c05500004103d5882e0030880c600401000c3c140d20005810441c0202d0a01051040207800f0810701e20201e0b400111b0803219003207121049044c81130300c0d030002c0f06c24032400c0c0300700c5000c1d03540110344030 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 339047526 1250 339046276 339046307
    0x215130b0601110105310b160302160606090b010c1e0f060513020910030b0c030406021905040906050d0803040213240f0906121704030b040b0603120c030703050c0f06010303 76
    0x504524555480c0f012101e06e6800040283c0340007004030300c5c04012151502264211400c016080c00050100075030540140202590440c0d01c0707005c1001200741d94030903c9002d43c0b0a00c1d0081c2010f00715201d4092988503180e4030322072041180c07100814455215000360845070721071400e10941c01c0c103c2e5140d4064060315000e03481603400c440030807081000c045288080329400f035840c2945907510015030300c00e0341005006441c540c0e000c0100b868140300110500b4050101e43e1078440d20356040080c0350302240ca03190001b0380507a04581c078400c04501f80c007096a60095045448007120000e55036002c0c00385c040c900310155140710704500e5a0079110302281c1101074031040c1d820b0f01142e03039403040c0d20070541d0564480d21422210101051020412444079915001a0801e00c98a082c2d96559148402481103d05450009a601c01d01c55180380500038030882e0030210400070304260200300b40035242d1045120003814444005004050000240802c4c048888941c0590310150380d81c2c107014101004544041 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 339048776 1250 339047526 339047581
    0x512040801380108041502030903120109020405060403060507090f080106050102060606250507030506070305060f0f01080606220308030601020607030e03070b0a0e0714010215130b0601110105 84
    0xa1101d01050b0310a80600c91040224411070b0903440c019a007541c406041500d229688090195624449000841c01030f4031002c02035a60b0044103080c1c0c05060f0041c0c005150040c01004104125654042030b1400c1e6600080005820740700d0f02400d5800c024194003903c040b400d6a480010300103010b5010804484081c1c081d603030b165480c1400c00940f40320b5984000c480c1d003c0500000300600206692558141c811000c40740352580780c0d10750034605032088508000282e150010003409052240c8040b4080c04260b03880350382c1c0081400003a2250710b009088a0103200302054040b00c00d048440f00000120118078040d02850f107e007841c1c03410303900413503c50740540708100209844520174030403680300d019080003840c10f10085a403403100c503c001419a504268a07045420603c00090182c00020441c80110074148400c075400641065542c940d22021001131078104902c510883c104440441e40c0070182c2c2b426aa503c20058600944c005040303c107540c13a04d0100541c072a018200d40d403000300c560441 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 339050026 1250 339048776 339048821
    0xa0203010632131e020309010c1205090d18030c0305030d05010e0c04051915080a0606020c0307050d03090f030309051503010503030a080403140d020d05090c030a0f0512040801 77
    0x7040e40071062924080d08600000e0710ba040c001007a9003c1950280303010140c4c1c100b20700c14400030060381c2080d6205d005070703550b41403900d80864200e1084500601e5804007840546024001eaa07107540e0746001183c00d01850117017940e034402c1040d269201035540540030790040c07a02c03414556540c2c0c020030818074001d131810001184c510220010284108071070b40f02d07185814188030a0000307030031210088a81545200d0000306080201303400844c1c03058500e5594a41e185054207110003610383e80e074000d8040d5041650117204507180414100c0a80e48242c0d001a5205042d24040303410b101c0c0c9a200307001380240c0c12000301c1015400303400b5200715101210f0b11007503000b118a42e141140300a01c0f034543c0c0343d4020040c02014034080d40c085a0b01c05e0282c02c0842010080208461140e400140d5540456074000742c40300721511144144d5400000b9034004014644143c1d011075034510a007200600111b182c002d0b240c0c1042002c0080c0000c0709a9031901c20303244e60392516850b02805000e843c0a0703608000806 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 339051276 1250 339050026 339050099
    0x1207020304080d0c170a0302031918110a09060b1308070e010e061807030905010e06090a03111006120203061b0f0a0c0501050403020a030f2105090a02030106 69
    0x5a50030b54080c03101804501c640c00505454402800c6400c0320202038544000682c50a40005080e1412540e1005617503403901988003010440b110804103005440c1002c41006003100c0702c81083c600c1c0d0300140c02e1200c541d020000541c408990761040504038101080070a485a183c1d001e030041c4030780c1c407101c160020740780e6044688900440c01040441f1041200400450415095103508048003030a010181d07001c90401c03952324601200c0040c0401d071943c0001c1c040140c01d20445004034115805003c40781003443d1015100ca114210140c00c2040501111461032001e20a446055210f02000c10041f0f0391074401010300c900c01003041c0e1090250000180c8a9600b500c041580c21988010b51880c000d582811101c040d00621914001c01005105c20030000e4001d20035107000d14000c1d002021b2540c0355190051244540d10500c1c1c0402a401030050000515456150740160852001103099590016520720b0210f040038003079850b6081c06000030b0b108200540080a0480810340c3c4454240b0800 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 339052526 1250 339051276 339051283
    0x71a010603060b1c090213050720031803100c0e090c0315010318050a0f02150c03030a091a25260901020f07060501050405130f020d05031608120702 65
    0x403c03210901d400704031501020030662a4800103d001030000642588070713030040352080d4070001c005119141c2d2034003401100d51308000c110200003414070010031a01e49108685403240508a8481d04521101c1210146035a00b40a8065035081c0d90004100300b00d84454002d1840c041131401c50301454114012034800900b20707085911416600c07480c140c4d28044680114000c000d04a032564581034a00b034054002a1300748441e2003103a002d00c410024041080c0100b04c41201d85101d000003502c4200110410808040709a0340c3c84000b03807100040c2c04c0e000c0e041c01140e100d14511298640750410003001201c81c1001840020344080c00d01480e62410980c00540300d0010b403002c07594410703131100c001c05406241603400d154442c031001c2c009801d1800b43c1000480582042c0406c84d08640c4402c01800540cc042c89420303404010118a400f080115464038203200700c1103040680201c0c100386128051081c2082103070000360b44044100380b03050090170860b005402054008034548205404150b6607880007 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 339053776 1250 339052526 339052529
    0x120b120d030c0e1e011101150803040305010c03091a09070b2101080106050a030f060b0916030e03070b01290c0703050c030606012c0402040f060f030e0c010302160602071a01060306 79
    0xc081e1914613140090054802415202c2d1032200e0350340b114403c00301203060f045d14000403d8000d00035a1210304501c0c129095a80520800e020540741c0418900403864895060b0750f807001c101e03481002a15601a070b54101403036904564480c01c030000d542e4145003451a8007400c7c0158201c00415136980b25a0791340e003a1241071040c1507001c40c51740e6060001c685001101d9048074440c09001a01c1900729000c075402d1030045810814050f0301100c40b0750215018010364549908520103585000d05c160b441040a40040c01942898910079401101908814001c40c1c0c03c0001e804c520390301c40e1961541d140d640c00c40360100301c80c14001c80000c2c1c00c2a05001030407a00558050711242045d0300c2d0140101d543d08207020a41015000550b050490ba031070301d1006202030240324039020320103030a021020f80904c4600c140c640800d4500707003800043c3c020100d52421031010074038015a4501214400c0c00000c510010080c04680c03000440d00104104406030764000c4036030f41a02c4c203582e80d032607100742c089400a = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 339055026 1250 339053776 339053809
    0x3110601151101060e09060402030706050406020a030f030b030a080d1503150c1803030f0806060c12030c13180b0108040f0209040f0f110f0f01120b120d030c0e 70
    0x76a550503265015921104004291100005506946040803418544181c81e5184903402172014001542402d1100304090080e0381400ba1900c1c1ca0600020f540b00c45081018080152500703001320030754400e400c0843e044100600712102e2002d0b0307090070401540440745800e811031401600d00300c0819001d040380c0499401c0400c034107080c4018070f50080980322a80306401081450440318100061a501c1800a1402561480b03010450034a01802048025014620400f404c1c172800c98140000200850b240e041828150f40303d40302c1d120000d0300e90060911100c00c2c010507400c04a07401070414030f24440520b0407081030081001e00b40064404500503a805814124001c600e6409030901c02d082c0c507005442809803a00724245071b11b0b02d6034240c007016000c4035030034050000c6090701e242c851a80f0307a0040d000c0301c5240c01012100c00280500d01e490b1140d010942d26010030a125648140b4614181100700090712419252110300900505003403446d070001c100c0c400340b224180e0a0480301581000b8070b = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 339056276 1250 339055026 339055049
    0xb040c05030c0c03070b09011a0a050f150408031b0712032003070204020703120b030f032b0908040609061b060906090c060c03020f010e03160309031208010303110601 73
    0x44500c024811584071100c00d0f040e910082102c20001500328240c5131103080241c000088410380c040c103405a4900140950b03201d00007068043c00291360304140046014400c8640000da0b450107040068580200d601001c11400003054000c0c8030f0070a64610000042064196180c20f52078042402055041c0a03000d400140201c00c04254840a032a1b07400f600860a4122820504940d0026080c1c0c1c0c40018110002941c4d084202e2450031b00d40500a5880f60840190010784035012034641e9a0040c4465640c0c80b20220303584854000000d1226a100c40040d241800320203042c6c14800c1e01c0d58042c0c4510000915840c900244082c843c140606180b90041440010a645074540b0070251030071035000e569044d5101442d000117940c40100d2401014030307403607000380d1100c3d6040281c10041989080b4000340d04103140444021404800c0325100715503680800c011007003a040c21100301e9080c1d04001c040115580660050540102c0e4180c100c9100c0c0d070726000a041040c1040703403984400c0c400c0c201d02030f9 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 339057526 1250 339056276 339056281
    0xa0201061d16030e0d0306050f040603031d040603120503010e0a0204050a0b0c0c091f0b03040209040f0318031505161205150618030111031005060f0c030c0f010b040c0503 75
    0x181180301010324400d0b03c0c5004607207851200c007003508011030103600202080d600c000400190422a41300c00c40c4540071030f0200300d140c0c0b454078090000c504004914005c40d803140010040d503130b00c5a00080195400c80c4280d00e030010701c0c480c090f04592003801114046022240010354000150084a05842001e49240002d41c540300c010800703904170741020700f100d00480c40e10200e29201c00e82c0f564460381c00a206102c81c2e90003003c42e195010700582118281203000c10800015031521055580c1103a800010203500c0a12810201c0392045840403c1c2000c070b9511b2400814080016145a43c3d11350840c810001601c542c1070a1241c0d010b01c0d00e605011614010212845025581c80554403240d0070003210030200a210010307000f80c2c8222900d400c080c42c0b08851007000e040900c2018950b0580346802403a43c10b0030000c00040100030704c40c0034400c84000030846468003c140c107130343c0c6020403e4203c0e41c95030003408000c0c0e100c44e40c40707420001a40c031b001c20700310a40c54240552040d510072921a1483d54 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 339058776 1250 339057526 339057541
    0x30a0302150a0b0319060c0f0e060901050412060903032a030506011808010204140901030803040807111806030d020d09051e030a03020a031205010341030a0201061d 72
    0x201c0000d1120506682d2801e0000300d03a2800c2c04030324131000f0202c2d070b41c502115861800c42c0c103c030f03001c1c8814003c000e03030b0680b100311042d08a40096a520000c4400c42e44541e80035004807141d00c0395070445504800303080c41d02410003140b41c01c445101803007034030b06203e02c5045281d080039407410140145500a04e000752502042e0182c0c1c802c0d03400610600d0100e80080040011050340000e59000d05c07956940098200400d16240fa100156282c080315041500c0d40341d500d410100d130101400152140000241c46010030501c0d01a510390400c0c064400c05201e0000c40b00000c44800491318079002c3c2c0500707001046c08900c04285070305010400d48401000e41e0800c03045c021107a0f540800113001c07010300700c01c0c81d1569801300720151000b072083e13000f0404d030b041514006010445152404ca0700a0529006100243c40c00d00c181c2d092020105000108000844d00e40052411750003900c41044141d1082c0f905000d8080010000048140c000b8442c2c5903684504101c14074004420303407040d6140c5000b248a0 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 339060026 1250 339058776 339058813
    0x18060a080a0905010e030f1e0a0e01080a06031704090b030c0102210702060d0519020405030a0b1509070503181506210304080a0c090b01081503010204240905030a0302 73
    0x402c0d00440001075151008541e05156030b0010301134114070b0501007201c1c030240c61462a007071068802c0c4a512400c1c1a00060b010f041c1c05031039050141405a604001039840485600c03101c029504900d10b40c1e2040000c003800a0158400e020317070f000403070070020001076500b0700042c042441c1c0c02c10303802003810780814030409076021035060501b4941c4404000c0500566a803501410282e601b2007000592800c001d181c4d100b060080c8134031100064014802007006a80104e96402d4054011190b001c01d44d490b11301c0d03201c03406100c2e800c4560190204d01404001d60380500594412040b11100615005210100c00d0707a41251812081c1c10b41180b000141140c140b0904076141c0d00d45d60440004002d410075041411a086600049400d9010311800c809001500300030794000c00d24594108910035040300001c00e02000109001400884826a80c41e00d407000d5046800410030f090b021103c032620140358072499401d4480d642c0024003c4900404c8a1801186400d0f04681c182c0042001a4845200496 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 339061276 1250 339060026 339060041
    0x4021602060c12070803060307080f0319110109060501050f043b0708010e0c100f0e0111030c01150b030609070e0109030b0c130b1c27030518060a080a 66
    0x40c0350182003c80502c080c96507018003c99485140000c1d00c901e410002d05190103003d5115036400c0e40240c030714542020001c02115010b00c050804005001c0b00c818060340c001d0350700c90075880c00b0340ca4a000705050044a501c0035050740c4d011078880d402c801d5044108020b0b036011101011542e0299107051009104110b1545044074030f01d2a48101c4034500500c49060011652200301c41e651031300440c02141c041030000c50640207089601c014014440c030401000c18403041d0000041c442038606c21049a030203000c80901000b50b00e03040744d0340e4400680455006c0c04500c051407916605090000c919000c1e00020340b44244000751600550761384886044680d00720180300d290601910440200104078034403d00c41c882c40d94611000c0c0d0301c1443d101c42210040c40c0391722000240074188034201003020720345030f40c581d6818608808100b552240300031140b244080c054088000d18100c4108040641160162519454030411130b0a81414402441240e209601803103001a14400010703103800400d600019 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 339062526 1250 339061276 339061297
    0x90204150e0f090405070e0609040f0605060d0b0109022a12070804080a0309050111060f0c070311011b0207090c0c06020705030d090302031306090b0f0a020f0a120e0402160206 77
    0x2054001180b001c070341142001c0e60306540c2134000d1401448054542c41c401c0340c01010942e003407012803070141c03646411144131102c02000140c54502080d1250740b0400c85056680c0c01802d0541d180d43d40b2118070000b944040c040402d502803d81d032000b402d14142061041151450f0064410300e0503072805114a80d210702e604442401e404d10021520100812a8941e00e9100f078450103803031810000090b059041c442003807012544082c0c200089442070403412500403008002c0c046c0c8500503840d043d00d2201c0542e99404181d843d2080041d008400c0484043d104600717078003500c401170f445091040a0343c481d88111404038070341d2021080010042d81c0141280c5000f142680e0074030002500450070b0b1440f81c0001d80050b400481e6850682d84d0040141004104a0400d14105882c0c0228540c0074080c0780d000890070b2801180c5e40000d45c4c002c0c0b08032992000381c201907030b102000d1807500d10341c5400a001100000b44030382d0400c1e581401d15100b09c034021801c0d43d00302d44459030603500300511a4000303a07406 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 339063776 1250 339062526 339062539
    0x509010b092206090636020d150f0501230a05042103030b03010902030c04021605060106020604120f0203070f03020c060d020d050912220312020a0b01090204150e 71
    0x4150a8101411110300e00c90060200303c00c1e203070201c0a41070b1841d035001213100380e1043c145442c908417419440000f1000e40000f00b42c030041c0c6048410002c0c0110b0240c0c481181c185400d41001a202071100c000b510405480c40b03a806403a50011640391072a07040800000000c85c885031080044c2601400e50a4504c0c5851413403c1c0d03d035454a081d1565046039521505c0c3c061404104054050240340010f12056008002c21703a42038000aa8030406034528a001d00d600044401110b1003070124401e8054019040711119699100300035941c03c1c00305c800b9203520480c940c00c51065403240c13040c0078010341d8a9004504184064981e10760401400030701b1029072280c560cc41e02991603d0700940000c4040890041c1c0310305804843c0425100014040e4445410856062080c1265441920200c000780501070004500260740003d1400090300090306404407040f1880d041c03a400180b01d100ca0b841407001a4a50740e807601d9000680c0101d00854001042003443d80c070b9554401c1b0a107110000000741003 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 339065026 1250 339063776 339063799
    0x60b03030912030915130902070204020906030906010e060f18071205130c0801090503030423060c091903050c01050f0d110c0d14071e1a07110303010509010b09 70
    0x42d503007001e00300c001c00c40780d0004501d540790381c13401d9100d0003901440b80f00403038601240d000034540b0301c40302e0340122074031154041400003e64445078142d560080c00544400c0e66800c1200e42c4030390712030091181401e45580c80d000210035040c04101c2c40313060180505000d00300d503480354034128003041c000e10110810040041c4104900c0d0580200c90003152032150030040d035401c0342494030054050703421a4401da030409407410001800081141d9206401c445502c0e0000c424860140c2410b0a41891000c1845404c0500c5044050070700244000c0c601251150341070001c121544400441c00e01c0040e10f40c0d04005164a03040d40500001c018007095200340518080101c1c2c440310840b0110880c281a00d030300424401254401045000f03940e41da01e0409280c0d41c7d040d1001650148640f040060155040060960800c00c00c0381642e0b0003143d21202c00e004106150300407220344a07080b84e5000c002000551040c055480100c11241603600103480440c9070b030700344260005c00313500001006810400040b003 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 339066276 1250 339065026 339065029
    0x60905061f0501080c19020703050d020c130e0706031a0306130209010f0b0403020f1516170c0a0618080403081215130506030709061202090702011503060b030309 71
    0x9038840c1c040660406041d0600045085000d4865044181070100d62824081d00d0006501a203080584800740b102400c121080228246441d1b81d00080c42c511410070b60304201500070403c001d02c540c080c1c0c1d00c9c400020350b01ca071040a891040a0320450703a0002002480840d109410258049040501e400300342c4059102003440e008086400c0004104080c00e107000b1460001d4499006000b000c04a2100d0b40c2444644113452103a03110080c820a541c20840600381c407920f40e03d8800c4041941d140d5100c010001e10800800520380342103640283c01451007000845050071307140c0c0301c1201c07401068110301c00d43d0392200501c45c5203a01410480c1a2180070700180d500002800503602c50020141c132802c01900c00240b54801030000c2c0360580b0001c02e05007440d15800000c001c0040c01520120f1942c40740b102007814000141c0004904030305180000c113003200c145065510b5140f003543c103120b007992815404ca088410020707080e02c03000d0b03220744100045500d80d04000a03000009081d640703861100340 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 339067526 1250 339066276 339066283
    0xb040308070e0d0308040209060306040b01180915240803040506070c080f031b061302190515070201081e040f05030f03190b0f0102031b030715090215040506030112060905 75
    0xf5021030000f0900410041142400b0400c1c0b031300440f05400500b8a42441d80d03401e008000305005400a05c415145810484000f40d04105d00440d04043c0c0085c070b000c40840401d0240c5440c584410b01404a100d100481288010f10001103030356400c095400c0c0b0b404e00081140c04e034810101624101c800074004100c0d840248010310b21104100c0045603a6000c100018480c10505050201c00381c0011080102ca01c9410f02c088440702d90403140b41c000d401a458400140c0c0d5080d401240d0008542c4000c08a0502c405000b80390050007603c400440c1c3d0784260348448103400c25450100c40c1844c09000ca40080c08013100342e548203100e00b05582c20a125101000c00d650811540612451020489000750010318815444400700a0398202f070010013160010303580348035845140f4000c11440c01c0d1240004802d00594241c02d50100c5050700a000d0b1030b1609000e8101d50138241d103d03080001c0040781100403003048604440010b481c81d81141e18043e600700b50108002c806452068980e6040c2000403c1071 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 339068776 1250 339067526 339067549
    0x15040b0115091703040611190204181b090e010204080a02062b0b1e01080c091801090905060609071d0a05060d06080c010e0f0409050c0607032a0b040308070e 69
    0x30045840d176151040041042c3c041c0c00d13488900c0c1d0884d500401820040700058082c80381c0644012a0350014105a00343c0c091140324003030840e076074019600307207218100d85805040380e0700c2e098103000c83c0c0071b4850441d08038400c6210300310755075001d40d40038801030801e20081c01c0c3c07500c020a002c1e115204059000d030740012801020310a41ca58031841000ea52800c2c2a07d4810f100c040043c0e2080b035118400042d051010240050501007000300d02c604540e82e03902c2d40c800c2510394101c1a5003c0317507542e15118024280c00201100c0602441d0300113103039818258040ea1003146245c0d5000070842820054030ba0301101c80d0021341d000038a0020205880e02c454000300600740c074444000800720720300b291903030801201c2007805e410810499000b8145647d030a400d0381032200100c45c00517030018280b92140c58909001880c541020000c603030a020f154001203800c030707100580e08948044a28000b400380b80001c50341c0000349046c0307075400881d000c01d1203848220fa1281c914203010b000c000480e000640f150021 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 339070026 1250 339068776 339068819
    0x4020f0f04080d050f0909040c05030f010b10030509030d09030302130303020f01050106030b0f06090f041b03050601050712030209010e06040902040501181505070f08030f010815040b011509 83
    0xa070420854000700642d2164030294a00070b0304208032100d503403219214201010f845100352001003820700c0000041c0c2d0b401007100804642d138801c134020903d4003a01505070000e2140e1112a03032110f1560090041501c60410800a107152611911002000b00790042c0280c003010360a22080340c180c081001e81e42e001c0e60180d0000d00030300310303101c60190075600140c00c018205400d200c074800460f01d5940424107038070000c030b4805031100c504502282840c020030031000e82c01400c2814400104c10302c0f40301c0c40d5040c0200c0d80c080c451942e071b1900654040c0b04002c401072a40e100b40c3c903510b040500c40d1b805440b800c1d0051410750040078040c030028140b41c0107500110810703980000c013000340b5a0007450000801e44802c0680b4000791a1103250306d048a61891400180200001d5040800c034500f080342e0488e55001278000e49909090000e1228404240202e400d06d1203400389050700c281040c0851841543e00c11030994143e802c09201e0007c0004801c00d60041c860511008244c00310101c801400c061036 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 339071276 1250 339070026 339070057
    0x130203150609070215180c042309010608060a02090d0b0103050f010f0e3705100e0a051c0e09011401030c09080d140c0607030917042304020f 62
    0x10024100b00038810302519000540d800360405401034404814100d80c40038200c2c40000c01c0201e08112142442031075000c80f5403103441c101080e141c0c1008440304c150090385842a0807803d40e2480081802c8030002d01481419030301c034900040c1d113408143c000344107a06002e05880c200d00c00d1660391504244080e007045400d0b410030119911910000d114040e0400c0c1e030900244186d000082015445a0020100c240c102800c0c18100084000c0210000713044000c001d0040e008140d6410882c0d100e100c1b42403c40c090038107045810101c02d200040701c0800d070b504030f0054054404441c0c40115965034010031030003400300a12030910107035601c0740c00c20f00034000d8080e20318580e42582c0005040382c2c8400444c5090140c007087c18020307100005090010900c0904010f034082c0c5511207001c409019004001006210750401c2011966054001c010810300c1110704a1280060803960740031802140a1810302061140100c0038606c14402910010a000307040185490309a400b41d040940c440d0039155858031 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 339072526 1250 339071276 339071281
    0x6070b04020108090a080403020402071e12020d0f052a0a1103150c070803060d080c0307150e0c011b0506010f0e0a15090902031204060201230105090c0313020315 71
    0x143c00c00310080d400f10b860400741240d00100e60340d03c2014001c81c0000b074081c07940800c074901040031042080c103000400001c90080700c030440c509190800481d0700c0706d0006004207420b804102e4003640d0b40c005540c079940c0303840381000282200e55110b0918260384540701c46003030040381c0300c200c014460b20705400e0043c181c92002d1010035050610307255080742c1100f0304030b40110412004070110806e0b910701d5540006200e9484e201e0708005845120803110180c120300c000070b00301c83d2819001004001c034030300c280f2400c400c9410803032429044662690390f00405802000480301a98860315000038001064030700062120304540326a8500b00702600b03c0e40d0648480041030003440082144694041103001041c48255120302034180c2d0440b261043c08240340d181d084030011507805018000c0201640300c4030310388440c0e1740c000c003c0c00391518002c0000304001c0f540910641c20408081c0ca0b0585178040c01c0051507840d08507802c240c03580005d010060706003040322010b00503501841842844d011040d5801d8060 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 339073776 1250 339072526 339072529
    0x1052b060918030503071115070c030e030109021e0d08040902130902161403072f03010b0d0f0c0807030605180c0f130f1104080f030315090402060906070b0402 70
    0x45550000c00d002002d8110034481c0069440001c0700c0d8000082e05c0e10f02ca42212060001e4642842e0001040900144408110071190b1007400d41d030304540030303549010092980005140c200d5181c0e1078080d401a4142240344004d06040d0803880384220302800310740d0701c0452505c1d241200c0e049a00580d02c0e2640020703440c00701100211003400508400c0f4021443e0608424101c2050303a03420300700400920480e080214041c03070a0058414640d0452036000d000c40362051000300c1001c560803c4915050003e214803180c1c00c05101d440c4070400d010b40340500c0808e89031508860001159002c0311041a29100403035006070510414009510450010400b401c0a528454603a0052034842403958090484100039546021451440c280103a8054119000782c0190002821007030100700b107010f0419004e41c000c060550001e1048500441c1914403640d41044010384070b10007a00d21038401e08034034804440a00d0900e07011a0014030003040a468452000045840c2c0d810449059405280446c104010b5 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 339075026 1250 339073776 339073781
    0x1709030313051f050d09030509041a0406150c0b091606051305060c15070315030b01080c09010b0d02130306230c030105060d0f021b03040f06080f0601052b0609 70
    0x160f441000340001c1542502500070311a004d800080400a501c0d19150001e250140086034078508020b8014084000050902058580d40d01411801249002c6d03001a05480f5021103543e09201c0741e6420030124000c1d1148c1d248940c1c0500182c1250081c3d84074140d60500000741d040080c01c0075111991101002c071203c50f00c0c02d81c2070b030100b400b890080103465000e04021a10204c01c42120300405440d80740d07041c04600401c14030542c9054008480d10110a100d00501924120781c106030480703101d02405414024071b040300b0301c00d00382101c10521052441c400c5135000360601051690708401c40325500d131034560640d9014400c5062541d0082c2d2065140d064480300c1c50f80c07101c0c5106416146501d0b15020804070f00c208400070f110503907100c44403005460250111070000c01d10b4036038211000010340e40244c4a40c4188a10350004c05500701c0015040c3c0100d140324440d05860340d803152599200d070015501580f00003a400c40004e54080700403c024001001e00481007480400052403509003600c040c00c = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 339076276 1250 339075026 339075049
    0x2b02070618060309060902090a021b0307030912050a051615030606050f0f0904050702010b0910050a061419090501030b0d0b010302011b0f030216120f170903031305 72
    0x4001000c0c0080d0408034072060072904841c428980014034061a0410b400201640180250310110141c00e00050364a80c0d0007400c00340342000c036800030007208501016942c1c49280d00c010b001c902118010028880034021b02005107000b9000d540c1059100e60f180750a00c0c00504003c04403440020051091040210b200d980c0070340c060408020045c105203014000e401442c800d16451a400561b0390244d007038110a80f040f203e03018006000318145144044d001e0b0444582c0c0ca40140404800684040d022060b40812241d005d04400e00090400c5011104884401a4440421820841404036511841600000c0c542d16511304591604184c0010b058464075124244240c03040e40b10300c00171039040000941102d60901700000459880c01e03202d90a00500500985810f40c5001800c0505d80c020a40810301d403034500100d408181c40c0c8011180018110901901c44500724001c3c1e400100e2003020300d80d90304c085070040c3d07003000030010002c1c0c40c0d07600c1b81e0385410786207040d440100810f043c940325401 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 339077526 1250 339076276 339076289
    0x150603050108150a0b0a03140106060201050f0f01060e010509030a11090a020c0709050907051e0f09190b030f0d20060f240604090e2a010309052b0207 66
    0x2462440422201e40d05040600115840d5a8031517030000e480e5240b908000007554401c0d05170b884140c2a50742c0714000d014038411840994201230005070b0b6003698110b40307881401400007a0440c2e900382038048881c00f00c5808454140401040600c01d180d80400850001c40c0c80f5141d81c450300110513050003980344000e045200d5031401840752000b041d501040e42d2050310310482c000991a60380085503881c080380d5901480e0481300b20a038008a10b9188074660003203000a5601554201c0000284901441e0494010381182d0600c8541c91010500b5040100d43c05d4004044032001c106010303030903040c00014040000454590f905184003510640b00c2070541381d810070b001d44020b207000f2a0070410141c004282110020940885000c240d500c3d00000350160009411903481d1034448802e01d00601c01151007040341c0c400c00c03002401ca044907001c0a035201c4034529407121180030000064014190301c00c411501c6019074000b6200d107400042100c1322901110705a25841c8954140190915042d6040744 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 339078776 1250 339077526 339077533
    0x1110711104104030309091a0105070209060a0306020406170a0203010e0f04030201060b16110a0f14060c010f0203060112060506040b0a02010b120721110d15150603050108 75
    0x30901c01100c01000c03400806000c150120300e41d04442e00103042005942c4040307810300100b004024981d01103e00c1d800d4820074013041003564001c0385038071091101844400d0020748100070b60300050420710405504035070090400040d2a4407903641c4001d0340c02035007008001030180000c88050816030030103d82c0000443d801140b0750350401b065804d40386001401078203801c8507100031a04040c403d42c0000014110741e47c034103442d89924030390802c0c040094403090b12a14600500d0791160300d00070210f90f08656051401d10f406915041c070701070544180590f55a4055024800d00c2075900b0203001c2c001c030010700b500006a0b280382442c009000c051079003001c2005546014400c4c0025142c020440d0152604034420326241c610981c0101e02406501d0750450f0050714840c01800c803085e0015003d82900c0d450580000c01c4000924440d80c04084440701030201d41c40790350482400d0800740c00000802d40100c0490021a012890840039290000f080c0c21260012040800c4110350501c5418050300d400b1001c7c = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 339080026 1250 339078776 339078797
    0xc010507170f0d0504061b020f0607031805010e010b12070b091516030c0b0901021617090a0e01050f01080c03070806190b07050724110111071110 64
    0xc9a41c07020350030355280ca844034002100707100688420b080d40c000548040d0240080c0ca407920302400900360999810380b030305084130044071006001182006040003401e00034815641d076080d040b00542035175094000c01001c41c050460109074280a0030b60740c100d034180041040c00442083c00128140c150030481d4907003000d0010710811140c0f001b00d070b030682e5048a80e4081c00c1c07400e050a203501d12072202943d1010014075551002c0541006c80300510a0140802e0741895407082c1d0f03001d00380d104182c803420040240d2215000020403926103002d814003048021410075901e9804140c10310381c10b4011a81c07044844004110307504c0c002007000700c030181c2864103000e50304140c82455510b01002d0000c00500682800090150300d8040d00e64540340141c03620014440e0b5103d01c420240d0b80700c101d0968440c068408045026201100e01074182e140c40e049144e18094000c1084911210f8aa0034003465501c407809019140c0e1608040c00d10745029440100000ca0040e04204624405030000d4041c0480400b2 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 339081276 1250 339080026 339080033
    0x30403020d0b06131811012f070e011211031614130f02070c14030a030c03110714010206100605031906030807050604051902100f2309030c010507 64
    0x4100c4a035076449800b6207101c0d26003a00048003c96a0030554644521300700c0822101c14020340300c00822406081c840020074003c1c0c0c011200d00340c032103040e524584050303407890424906010050780700c0c40418058038011600d402200203007030320030b038040b441c0e0351041e4001c0c03024401240c0c41003012041c110000e20b000b400e14503a08c09100900e208002519019102400241d11010342c641c01c0610580c10403c03c0740000010b14009400c1b540f0180e491356403c003c08548012082e507007a45140d00200104500840e9942c104e5a40288640880c02c1200081d1400d4541408100c0003015110b0001f4691001c0e8401c00028580900200022a1035022010030023010350003104494004042d5040e801441c0302c4414600e025258542c0010105100080e8010030b01102250b201d005a12850507034804294441d00c1c082074489204020398010f800d40b03000c41e2141d0145c0100c003d0100181000032581c010800c401141100c0401010410030000559104230f28090220400d94203003400d15034184403498a = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 339082526 1250 339081276 339081289
    0x7020618030a4401140a0b19022401150e151303020a14030717250b03040308151c02040c050720030c090613150503010905060603070803040302 63
    0x80480389943d160f802d005400751a48151048055001c980355004218280c015001c0d44001d105030311520550400c0000d4a182c9911010211a10000c03003d0905003244158174044504c040440c09600c00c0c14191884102c2080607500040c0c0c06071a08215580341a43e4400d09201044041d4100b0070851000541540c98100200540202c0491641c503001201040322092171250800395100310302c2031000401c49542101c964a40700241d090f12001940c500c964260395030a40c004240c0c80e001b48018029055030080203407168030a103c80b101c04560f03103648424060344160b40c181c0004941c1c1d01040107100500340c088000c06019146411428920f891080000106c148002d208a483c0c17910030008610402c2a1620207405c268411812a90b2300c4828480c1d504499501e4041c1c016880130303481628000140c0c43c8295005400141c0450071101c10500400340403072801407241100001040d03d4909108000302d86205000501040c2443c0c4201454848980d1260301d02d83d100700801e000503114903 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 339083776 1250 339082526 339082547
    0x7020108040b0405030408070b040f0b04031a06150c010507030c0f0905151b15060303070f060e0703120f03050105100f050315040c03050f0a0509060c09061207020618030a 75
    0x10080c207030b5440b40c0c54a20f04501c10b50340300b101c651080000103c0d07400e034450f0040003211030041040400a036100401c80c610301031072101410b01404402482400000122480d5104000414041d8210010540e80d8001d42000401c05a281c0d9104104595160184120085500141420308101d42000c60051010b400c43c003601b4000c6018002c0100305206040c140d4101c0c0b035801551501020090041d01e0786c40d500301d9100302c00703800c0f4203000ca561424007108450040f0303000216a080c40d5201d0b11480301400011624004900c5075810020104d01c002d007621035805545d82c0c5180d80201030100040583d80180c1059102c0c0104980300000b0b560002d461030006685824255242c2e81e405103145c050400013202d070f68126051419140405030715a0210380300b1a0020303202111138035045074103030480c1e5003110300b0b40341c60b0701050100742e42c0984100600041000242160b1500d1455050078036040010b03a07030b000c09644890240300401945110041004601c03100860a26115210081458100 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 339085026 1250 339083776 339083783
    0xf07031d070b0a110706020c090109061202041a1e040605032803140f0d0c050a0903020f150706020d050c0c1510051e09060301060b040e07031409210702010804 70
    0xd00b50f0405024501000d00300820800f0b03140340c140e84003000394072642140d5103513228204910001c1040c11181c45003006030381d4685c2000f048c0b4440b660a0100600d91040031005200442c1c01d0b050841c1d442212040c100103080e0040c07802103004400340003c1d10380c50b8000f240301c1d4020400c0c0c200d80c0c44941090700410401703040001d90014040c103050750b5820b4660580101e8200000340304010000520080000f105000350400041d654010101e80601640c0b0700380d0009404c0100070405442c1410b007140b10000c0007001c41c91000040c0c2581c10705603100400c2110740c00e40103e49010043c482e48103803948494495400c5140c000784030145030711005c00910003000d52140c4008503c1013038880400b480034050141484000030200305d8401201603c42c601103108005000000b84241410300486007124210040c1905103401c2036008040014020f00d003408042d605c65400854900c0041c4427030240f981c41c8050405100300c04080320203540440f1801c51096400c000303000060f44d00c420001d0b40640c1 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 339086276 1250 339085026 339085049
    0xf1802180c090603041a0112080a030518011503050c01090b1c06050907020c0a150f231201150c020a030b1503010614030c0909060f0711060f07031d07 66
    0x1101c41e1500c9540c0180c205a9800460201c100410008007184c00780d20342c0040146e0070b8141c0e03a1030394004000c1c511101c0003040244140100418a40250401c0c0d410600ea44082d0084402d8030204508640c00d110306440c1c0f080c4140c41c02c00a000c41402804200007007031801d05201410000500071520400c0f00425021081403200b4000881a600580107080c005080d10144c1c00c001e41c0080d50b0b090708918151003050030380e0001030003581c0e84201c10303041c0d289038603030030340c0104002002d584030a0003400b000d03076950045c03000741c0407040004002d0030074450b50312a5803159410210070004280c1e1070312070342081c0507503d18800056560028240c085030340c422591080359584803803030303110581e64580650f0158203108021901c10381c0c44040c5403080206808a030645801c61040064400d8140c40b01c0c0038a4104801243c800c50321140ca04d940200300c1d00344114200c00c400291490088122000389001c2201018420312607454000c1c0da095610b03500342102618070704904a91103410b103100f41120b00380f = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 339087526 1250 339086276 339086281
    0xe1b0a0c031b060501090c0c03080a0c020c0907032f09060705150108030307022a010c051207030e0103050604092d020406120605060108130201050901090305060a0f180218 75
    0x10320950341d0340015000c00b507040042c000d05241c0749010303100a010b079181d46810072041210f038610550514036940e41582c0c650307080340ca900700d10900424001030000c01318040d034070081e0701c240c03907000c11540104003a6a00142d9030a00d00c40080003911490002001e040c01c4010031400c040a5101707580200f2070881c0c0036a591030483c600945800701600c01007440d02420b0000141c540c41c003001444c42400d10b90241c0e54a20300c240c1490264031010074081683d9009560051141d5200c0d4500f80c45c960b100d48101e400e154400c0600a045400c803c004400052038101e00c00403550b418011903421003070035101403000042c0c44d50b0304c100c0b4403612088081c903254628104080b010f0080c4114140e281c0182040040c1501d90a603403202070901e00d002d03a02981440003040b0654403030070b1980d2190801019001c040346907940111015840741d44d19504000c502c600110200e41c041c09070900405c2000c3e00000c00c429032840b210705132540c4400f02903890b19104002005619103600d01c96041c1c40421050b1550b9 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 339088776 1250 339087526 339087533
    0x30206090a3c0606030c0909022407080c03031e01031a0603010b0a09150f23010c060627061d18010c05071505160c0501060317040e1b0a0c 61
    0x1590510b9030300e1416100068142c2440780c0c43c1d10150540c0c0c0221100180d547d100c01081c020303201c10900080d041001e00c1c00d00341d184a03008a41e1541100c0348054036241100c9034403091b22642100580380c05a8100009100e0f503042103e8903544500c041c0303003e40380036614584500004180d40f118401d0380003281e0b4001b4403107940c00c1d031020310004001050300300101e80328400c0d40000c160903021040011120344001c0780c8542d200601e64200c40140d0f000c500b4403544424200c1c06440091f00940c107021030f83da0920001040342c041d0801030214040a20b441400b14405800008049079800800902c2c00005201d80d122440411810b0a403ca2040c0307400e03201c8811414032461926200e14480d440c100c402c80d41c0c1c2e5070000040c09603e01607840c4d1000308184900c60411203005a519800c0800c0100100d5909800b41000c520200d00403800040c04541da5181c03913540304c0c415224900000342c001030620003544c214641d1904011003203400d00780785800901f500050b01c901c1c2d400f802405160001d40d000c0 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 339090026 1250 339088776 339088853
    0x30604020c0c1f030b0604080c0d1104020304060207050d030e0601060f050f1201081e1c050d09060501080d08060d020118091406102c130203090a030206090a 69
    0x88000143c519906288440d1444000c080c0004000000a081c541c540080d03203482c9055a00342e032002005401c858144030104081c151003071804940303103c100d07400003a540d5502d2018603c514060a00035940d1100c40ca0901e003007100a240e02e00030b04d4035041100d004840b0004030781d81524000e003850b8100b43c4184070300341c070940615401c00d0081d03540010304c01011241442c80702e049813901ba045a558041c41c680411000c0c0c10408031094542c881d0303854103c809142044c05020541904000740751450b81710a95003510350007201a25020384070001008140c400308a079080000a0349410800b03801e05000227a8684400c3d100039040040399104526020310841000004255800081103e4080550201156070f8200c03444d51040c00100700740024907001e2640c1e4a0600c1c0042401480e000002500c2d400c18140c450321260800c00b404030400c0c08081074030085006400d807200400310100302c0d03e0003d14017000140718984a8124946010018440c1e440709880107005c0800a501c2c0c00c1e00c050b80411 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 339091276 1250 339090026 339090043
    0x1c020307090b19020610080d0503060409080d3806071704030303060501021921200606040605060415030b01030902090414120306210106030615140a0b030604020c 71
    0x3410000f07035140506040c0401d41d10510740c603020303103806035901d45121515010034811030000781c2000308079114841c41980210b80c800380040000130070100503151100182c100c0d10200e100c0581c2c070644c8890b0f9002600c1c859510f002b940d100b01080d1510940310808038414058030f540203400110b14101004003d01d8900300070f02400144a0300c4660300e0030018041c001034031407a405409503150500400507902c80e41550a40c108042e030054003104401c010001d445100050200012038544000c9411001d440003c8400d80c50020000390900d1001c0104172807040e44590310071001044204015159000d04003148142c604000070341800000069020f02502c00c130080d481200e002c1000100901065000403070f2455500300d070780407080c1407103aa0b42407005030340b119071155000c00b2401d200d03000d806014600d968410700108026659544020941313800e1401101c01032503640d0203028486c60000c040c29444011118155010300d015110551032002510080c0182c0d0006102c0d00202c004202d07094 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 339092526 1250 339091276 339091289
    0x1503081e07230105060d0b041a100512010b0109051302040503011103160305010302220905010608010605120303071409180a0e10140f18010f09020a05061c02030709 72
    0x35620496450040700b00c2c01e10401c6032501e4522004030114040d4144200d51180201070a011000c8031961120b4206030401801101c10324441c8294440c0c001c80200c485000d0100071080328140c42c1018200200c0840c218040d000980c0b40c00540718082e0ba0141c1300e40211035040d60b40207000000e01600358040d11840d00300c40d41540c24052100340039030000300103610604c84100601c031143c130344950880695600384400b0350310071401810b5101004915581d030a048141c00c400086a010554800342511425800010300303035900c0404200c14240380042d2484041004041d40c5545000100900150070b4000e00100051000c605410ba41d01c0f080c04203525411400d40007502c51a04d03400c0c0c0f902814020803000c04900640700d6140c5410903502032800803100c1e40b600c0e554960f413034018204940e64024055076030f80c0d254540c0c2c1c0c0603540c401c1c0300d40c080d2007013a51004515000075005100e2911400d621150003004100a1000f0f5841d400c020141104914400580d80740c858003000c0b6036807511900f164 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 339093776 1250 339092526 339092587
    0x501172116080f040603060603051605090111010e0a0b1008100209060403080c01150b0a080103110301060f06050304120f080a0b03031e040503060612100b0118080d080a150308 77
    0x100a00700f400d0050070840381140d9050004036102c0104800342c900950f07942d082c280c43e2044461440e07000d80c02425080c0018541308a20b4180e1904150a44010f40f4020300b6980002c8110402e01800d45007003540082c00c1a6200c640d03514003918240e40d1541c1c0008034910700da0205144095a0314141198000c5401130b6003652500501c44441d80201460154940b403417458200008074401c104095458816207521500d41581c0f941e2250b650102856049540c1951f9441000c0f480700000903051001d40301c0c90362003903164903007850a0b910115840f554002400101310684161690000b181944404241c4005c41d8201c00b4401282ca54003d12008003000b8030301d01545076143c111b4401410440310700f00c0c01c840c01a1244810b00030b000b282088030f14119000f84d809807c00c0c0604e81c001088100301850300300c21400741485018021718113500100842c0e000b15510142055224035803d4002e00742010801016000c080c1c80d00c083c0741d003880020120fa101080d040c4201c884c0e0b03c1c40300b810441f5226003 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 339095026 1250 339093776 339093787
    0x90702010507030608010e030a05030606040b0a0f0e030712080d0608101a04020f07021c020d06090203211902010b04050408070b0705030103030c02120f0f01050117211608 75
    0x64007a0104503480000203140100000c5c600c80705025600e007030700c1c07500080e5190841022044510394002003200760801070030880090040088801030180d81500d54802c4403240d07100c1c200501d04081c41c0ca2880c803a0384520b80038010321510016140d10300d54030408850303448186041d542c0261003958480c4585020304135136031280b080142c2001e204601421140c08800c11840308220880c064501945900d01e0180502401400d000d2149c0c165201d0000c43c180c5110442c0d400180d802d0562201215001e41b90075112045040411171910b1131440da900c26200c0715254448400300b402000540d6540c10500180500080d000707610070080400c011303005000700d20f0b081c00d0110300d0742e02600e42102e4002d1801c0024069510070b4082d00d051b03039850350318104415056001c100a42e45400d0004400340520750401502000030000082100404000440c8661400706125842040700c1100c8200c1c1e08000d00612201c020440f0000700d40302081d04140d21520010501002241c00b80d000038140b4900042 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 339096276 1250 339095026 339095041
    0x60a06180e1608070f17062706070c0308010b07030e1e090405070303090b033709030e0307090b010219060915021801030b030d03240e190b060d05040c030209 69
    0x9000003a142e14241400c17402d03503211394000030321800d4419a25aa0405c501080e0031121f15070900780e003104240c80340f44407201502481418901d054500c4004150041c11100806402c4041d950040185100489c106400350300c0c06400019050040392151080003030724200041c2010498807500c001800292aa00d8645021a40d80f9442d000c19004282c10760380000707030290203d0480b88940f011084103400c0b421300840c4415070321030a4010380011000c03441074860071640b5100d00310045009a41d01503c000d10242032509145003031b00100c091500f40400340b0766030b036000601080107051030300e07103e1071500c50f600f0990b00610641d80c000b05a680180f44200d480070040c0c000d41150781c0d0101d40403068040f030310019022200c50351032040d0540c01007404000320a0181d4469001c40030341c0c00307810800c0045c08940084486143d00060510020907052101180c100e06050030004030b00032080007a80c5040f00012110301070502140511a108c03c005030802c050300e07098900556014101e80b03003905000d00e = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 339097526 1250 339096276 339096283
    0x40f0f020705060405100b1503040c091b03060602010e0a020910030b01030f1104090215031005100c0506150f100201110a050405120c0a1a0403080f0309060a06180e1608 74
    0x6409641c2c91044460306908000c491003603a030031f043e004015014250500d03003801138a4000600036101c6003001c0c6000600090076004140d00e1200d804869008014401d1010341240d400b0f400410441e85002908d03a8160310008a0700300040d0116141080c658031440a020b034050541c00c02400003c000000104006041c580d506101d03119404200c492480d80090104540f20a800a588810800e000e9141003a5a000842e00500104960286103844d0700218002d10b0b818840c1d2000540c40212990600000780091030700180c02403025511886400c0009000e00e07021801c151054001c07000d07001545000b544400c203c07080303c6111390344a0b06158005401ca41003441890700030901d40e10032000c26100400c1607180c40a000300112821390611014050507501c111408885030000c000c00f0000c2918103000d8041601c0c60b0f106d0035600d2a1040000b401d241d030141c60310045500307000b810320a121140c80c50402f8020b1103140050001a00c1c00c05034540404001008070b01d01219101042500021 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 339098776 1250 339097526 339097531
    0x50d0c150e060f01081603020108040311010c0207080f030c030d0b0102150a060e1501200c030f01050720070e0601030b06120103030e060a0c120207180b030706050405030606040f0f02070506 83
    0x350344400f20f6a61904030a48500305480c1010b046004103000303000660165030b4560b00540030b458103401003920828031508441d008000d00e03000d40e03c03200042140c440100021055035400d0f0010354104004951166564021401c403000526110041d510b2140d2080100080702c0b1041c68000c489424507000c01001444180150440c0488600010780745a0300801c0c0c00b2010b10042c0d59090000d5100800c0c007640e0f08202c41044c1540c018441005415601040400c4c2c0c050424000000c00d400c01003c042d0004040385d4880d81d0700f400c2c502c0080c4a10102244030000c558058220010300d03500c18004800800010100b507a01101c003180d1080d00744061154281680d10075116a0000368000041001030700450f01c5940001d40d082c0400400500c0d0354100c180d51035800d0041b80e03141a15084602400c0e5203240140f081940c0c2da1801c4444d518003001030313230700411507401d03d076260905003000b10f501d4039001403405006545a104403810700c68a81c0c441d4140d1400c803102151030710200c4c40d01c1911031409 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 339100026 1250 339098776 339098791
    0x1908040c05010302071101110106090603110307090b0a290a03141b0412140102032a030708010905180d1106150907080703020d061d090109050d0c150e06 67
    0x318003010685500a100729140150000d003400380107207102c0300444a4806001d115502552240000541ea00750b50007404060b41c032501295880700070b0003061500d81541940140605410400e0289075601c1c0c0400900580382141140c040890310342d14185c4035030002901e003507140381d800a50210740580c103504c401543c040141070000d1980791480d812860211820860120400400c41045541e000c0b411a164442c4110640e036403d0b5000140942223800032174404c11203c14100300e0f803071420008812106403080000c466429403c000000078a100014001c0b03c1c0d88a071340310081012042111044030396540c94a0880c0d03240200c14034002c001e8001001c000c02144620808900300310040d0761540c41d03940000e01002081e50350fa0b081207500c04805400a014150308002e4001d006c05240518005010420034202000c1210b1203c0c41d4420390040011031903034502030b03100c0001440880c0e00c024149162404440e2180e1310b04046a000860f44049008103103400d41e02c01001e000031605600c190300c2e = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 339101276 1250 339100026 339100043
    0x30803180d1e170c0a0210060b130b0f030f06210304060314011802070812040507050f0d05071e0b03090c0307150903080a0c0803040506010512010e060f04020402190804 74
    0x65428059500c075038081803e60146019000080a060030400642182c441c1441142c8011000b10074540868907250042070a00800090842d40394081110a4000309110030855280c80c46c8050f101c0e4071404080d003000005c50018010542c181e40d0215a800748044244212405007000000d1075902d504c06c0c0706913800310741003080b40ca0b06035a8090601e1f0403214007500c000c500d00030403002040203500481d41110054001e00480c2951603180d8606803250740708100030b10001d41040701b04114013519480e01441004901156000200003055484c121100000f08c1105145c1e5017240403032159058000380c46c0c1600200030011403074000110207449010540079100b490341c540c400b2400c80d02180e01c541c80232170340d50107040000554420040c14980c0161030f161920000302d9031403001550003a501a1101d0380301900620003890080340c24180708500400030880041100310f20382d20740e031000703000d00d9083c0c0400c0001010f54403250100ea03003080001120700c0d640e00c003a42002e090594140e5042e1a61310 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 339102526 1250 339101276 339101327
    0x6070519120c08220e01060c03030513200301110c0a0606060804020d11031e0154082b0507080c07150c091806050a030803180d 56
    0x10b0040d0b6211401c560082c0c1c1661038100c1140401400e8a191807450302901c200d03080002c2c82c1440c45a5181c0038050079a42c180c0c40e01003506005041d250060284660102030031003d20004012022980701440c00001302c0055000940010307004220044030000113290026a031840d05501081c00c01d401803040e00104401612407104036051401214002c0d04010700c0507400000c14074070b00014070880c100408a40e80d4124075041d051001107584025201c6039120810a8608808801c800660031248190b4400d24441080316080104039001d1a00c41c1002d07400841200c2c402c0b4000301300e2a035030000d24240ea22807030007058940b0100032140f0030100c0b6840c03103100303851940540181401240250f0700c4c0d92060b15140042602a4000e000446000000400c4000c1c110f81c3e50107036050030070042e15100451860304401040d40500034400d5900d1500d404c0c028003590361210079145c20b80742c00142c016166541c22882c8201c4200116030b01400e031140b0107800e010680d000940e4818580d5002e048014038 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 339103776 1250 339102526 339102563
    0x70b041d0f010806060607050109080403080403050105070311160204090807050c0a090209012a020915040f060f03060b180a1a0906010816020a0c08030417070806060603040206070519 80
    0x3a0020b0290080c0f6411070004a0111700d4814007400006010b000001a61403040d55040140c0e4010340c4212203d1030301007000c0051240c280308080d4010300e03034201404403403c0d03901c104005110740c0070307840d00c0625a21032100641d10341c3d60156002da580141130640da80058106542c0c5d0700c00715403040e0311034100c500000c95040707664000c1e00c1d0b41c07642c1038485011160032548a8804206581c10000040f9103929014000d80d5550b06440d010792000c104451200d030050081c481034813505601094124240b140400403110311074600310407a0f8005100155184114000403003401404100750905040308007444000e8089074403002051668111070310b58941c40d801442070385481111500d0202e00c686d00019911f2114a2020300c138a81c042c410ba66503682c82c0c1d91400c0305403030760340c11010107076002240c180507910a40c1244894144607100604400e4900000180e540b000100650b01600c0301102007402c64840100b03943c24190701c2010344000b1a0580700300c1e824540410303000d84510b0500504040c51 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 339105026 1250 339103776 339103801
    0x109020408061b041406160b0402010e0604061e1107030303020409060e0421180f150201110a05070f0f200a15030e0c0a0e19060501051b070b041d 64
    0x4050030b1880e180c02c00c5e1030303d060b02004500d070307a032155000101005601e074554450003910030071900c00e0500015900f4103000060100b000b880e105809a0020401880341680210031003100340180204110600c46200c0c0403994502c1010800220340704854001c4101609500a4010f403811100700700714003a91182c0000c0c19a105031009008444a42880d4083c10700104403024440414144103070f003503480342d0b40a1041d0403507520084040c40e020406001084641c07180001e480b015200078801901c10850640d05403092207104810701c240021044100280c003001e401950b034014040d060800440d0501300c0d00d248040601403a21888441d08040620300700d03800341d01703a40030300d043d51310410070003682940140600c1030ba03100c0c2c030711440003c0051980c1d03c00c1444040c03c445d607182407c44c01c0c60090001200c140407880e840440c1001d10510259a006047d11400d428945106004d482c0e049481c60800c04d0b50b07040b16105070f000042c081641c12615401c892100406600141030b070781c038032030790003032 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 339106276 1250 339105026 339105061
    0x3010302060a05071b120b090c01020304151806051b0d120c090b07050c010f08160c1406180c01020609030403061d0d020d0914010806040c020f0105010902040806 71
    0x184148140b0401c1c003500d10800182134038034418400e28060300c002c520b03c10011001544941c66441e000301020041048030a115134010046800503d0102014800030f516030145014071020182c05c5502034103a02d1041c00e002e08020490001c0010342615900b0050040c2e000795a1003034481654201038071344c00d2000a1081e00442c050380d40c03921000007114888054590410300104000b50001c01040c6007002c3c1d001008020300c160010140c2d13010340350000d0003000218560790103025620b0704202c0c0031210f080c04c0d1280380c112813800c111007495a2030012035103400f01a4800807446100c040104403883e00301d412030450000400c81c0d079050035803030049a60f1403013200d1110a903001440704000090980e0498101d245d54101400c2d0b4502025441614000042030000c0041e4032070511134110301c0d0890b1080020f09206443e6034a18102034001800b14140030b41054007450340c0d018004580d61080c03044030f100f100400f0081c4801d50351801d08201075041400b07000d00c03070b00540e000b040ca1030050304136121 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 339107526 1250 339106276 339106279
    0x70510020d080412050c0f030307080f0108060606031e040b011406040b090603060a05100f090906080d0e01030b100806030d0f0c11060d29030601060e120109081606050c03010302 78
    0x2d8041d540ca039507600a894412120401703202085c40800c290460074005207111030381141c002c0d038072031401c5d04005005c01c0000e40000c0e84240302c5030043c00310100101e11698030000540b246592900c495485800d2210440d100c03078840442d0300e050104002c01e0005080c1291000900e9816000e518020044944980d220342e51020008200920b41e908203240510340c40301008081211142d5100c0c00300c0d11450741180c0c0c0f0300c0068007054022039419001484180a0002d803030b0104403440c00d200d00140d440e80700001190501c085080c0303040b4581e20a0f0001007071898042c210501812010728050826901552401e00c44d01410303654040303a600c511429940049a55201c4039100b00c29110803001441039401c140d0403403400c00c4034404072509030145080c4651254074143c0b0a4943da01c0920b04003180b010040c3c0302c1e4101c1c2004125030390b84400741c044600d07000c484a030a0040e8400106006140d42800105000d00c085002611540000344455029000c0c020078400307507544100e270a1541c4001d01009 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 339108776 1250 339107526 339107537
    0x70602030c1b010b312403120f0f0c0303050a060b04080a032d080405012009011b080a050c0c0a0e0f09010603080307030207080d050a06180b09180709020309070510020d 74
    0x452103400e02e806c12414805914030303038205150034603d04207500d44107401c00d68070b8000001042c0000b5910803003a0120502502d8000700d00c2d100f80000420040c10795002600f015196004a850010150311280c02004211001a41c49640e54805a11000b00c028240c1c045040090410341c1c01c8031500340404031318403440254800460b4064190303504079000d0019103c0d0340d0b030f4505036122038040b0f0307000d40ac05859a10314152922341c0d0340001000c0820f0003000083c0c40c0926015a03000036191800e4600c0c00c502410541d450301c0c0114142807801c03407405400d41e807221035210006050028015807d0040302c6610210110707964680c0300c070342a5600c40c40014171104003040024040ca10030341c050080c1070301c40c0160324034208800c0c2d50f0340103803141a0380040800d55950000c00c034000d003981c42c1c10411103002c0010700060b407496002a20303d51004280000d030700480c10340c5203e448404d0088101a0011038011522810501041c9540d846d4600509000310020402d030302e001030002440060b44c2d44196a403 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 339110026 1250 339108776 339108859
    0x1b020c060f121312020a020a08030c0c060c010e0a0605010f0f0b0406121d160f1809062408060a06141002070807030818090705070602030c1b010b 64
    0xd1014100043c003200072203624101d01c1c40083c48521300d81d00c3c1e10455a0042400302d507503004106c02012154400c1c0042d902c100841c818004010500b0705603200116017094481e440840d07210701410700c48211141a01078900804200044ea030b204d14103980e040350391504070710b40781c84207003a1500042c00355107181001400108001485909241d0101c0d0155402042c64401080310f01649072400703020f40c0c026088080b010101c17010300700c2480018060000100b4075145017688203c154024004a0070340e80d87c41d00011300a2110741d401952080c040e81064118201d1282400c040c100d04500610500740119400b040c900d0f20303280608019210340128085280201c8401c20104c0c80340c0074413103402d601484100280f415410301000005501070100b4a82d40c251140d0036481e0041d00f44030441c4035002200500c041c503548032041d55002c4d4bd00460060341d07034580d040950807034010301c241c44a051074000c403110400403064000645105064a9400d000201c00417030707000c01030000d00310060305500444c5 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 339111276 1250 339110026 339110047
    0xa03080f16050d0305070201290d17130e04082d16020306060a0b04060c080412080d05070305060f060a030b0d050d17060105030a0c030b041b020c060f 66
    0x6103003101120849a140298002084001040c05281075409803c00d000c0c2c0070710706405005040e84166184000c10842410480c5051002d00c11150f0394150402803a02d03401c0ca0702d402c0402c407106500036405100216405040c2e0308681d006c0c8050740c0e0a81400c82d40090814000b0360424040e40d4803c1682c2d00717000c02156005000788081c8031001408464a0b0300754442c841c0d000040c07910703c250214203444e0000394010301d07190010181c8424010050072204100328008401642e003034800c1444c006070b511086042484182c0680e402102006681254110400c4500b0303000b001e80055004d02800300c1d40d035140c0107800305e800032074640390006801d0328212614904174004181456450600291040b50075001c01c00030b00c0f0381c140850f0540d1000c280740c90342d2030700700b620005080810b801d1201203140540000300140000307003143c0c40d290b80741c03210391700501d000342c0127203502c03003405001040001c01d580700e02960088111101801340c0211860441c4500b0700030215400e100e05c054034240392818038007 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 339112526 1250 339111276 339111293
    0x70503040f02190914041203050405150f0f0109152d03060902120613061a090708010e060f0a030f0602070c08010218060316030c050d060b180303090a03 67
    0x18800c44499000c0e44160005030340c3d00000d101e0503140c400d450b0340d0007810801988212010641d0301a2020a110200800a80c2c41b16042d005c0304034074540414142c0300d0b0324042e40f07040340500848101c0d000520403c1041903110600f42d1041d407641440d50030070390740c6070058400c41e120018001d5411000d0030782404048603800c00c0c481596440c141c0b207242030408151034003d03c82160421030300c40741c58081341d009500c0c141e40205194400440542102d0401d24400301c0032081d0400f004080b0794981c024104908180130600c0380c005400781c5040018034210000401c5108240100020b0320080c0d40440c48500b880a0004031440b800b401d010401070540c1c0b981e0303c1c0220140c80031a03955408101c2080003c1e20385128034002e004a4001585510100110003602c0c0240040c041c022002401080890042c2c0c1c022050007a041d820001100815981c0454b03040c421a400c2c00245401d0243c00692194603000422484421210b40100600d203001056264810300580035400f8240090903c00b00d9000c4 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 339113776 1250 339112526 339112531
    0x30c0e040e0c0d0c150c0507051002060712060b16060507030501060c0f1e051c0305061e01020c0910170f0a2409060f0b040506061c0b030102070c030c0617070503 71
    0x7004d460380e08a50380d210403c03226040c02d070120002071100b00f100301007090420210025210032210480300380d0310314071b00942e58000100303410104203c5542641403500035501c544081c5c069a56210b0351690605109088a00484070450707000d0301d4a000103072111710030302c5010b050310f100742c3d2101c825038440e483d61005102d4014041e10b025007030381c0501030164800c0e028070f180e15200d10046c1c41c40b040350345080b440400c0c8000c01da00c1030600f030408016069035070361804618081d100340000400000c88004078901401b104002d900003041c2014081581054500342040f1903140ea2101d075075551008042d5115404001540b25952150750350500190800c3c1c0c010b5060102c00c0041aa8807402000310800d845508205a80c0c60380d440c0f02200001800d0300400504030320503102404141080c0010648a12404482c4081d4413864100c44c01c0e2034041d80c01c00c41102c070f8024029915416141006142c80300389120885240c81c0c07003c40020310900444e80c80b9541509088104043d503500c3c58281c9465000 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 339115026 1250 339113776 339113783
    0x60b190b030606090315161106060105070f0f06050703050613020f0a051e04060c1101080403020d0f03021c05150d050c011d040905010e010507171f05060406030c0e040e0c0d 76
    0x680c042400c0034038801b0401e41c0314002c01070b510140c0c00b04c040405440c42c100140c54042a800600411001ea600107049648190703008424100030825402c1046004003a0900149400d003071205101c02507030b0580240303000f100b04407070b494400301603c5500720491040b01d010922000c014046c100e403a40c0601e001c0c01d00036a000042c0240c02c901c80122403c650f01540080010443d000400d07030a01c0045190790180250030700f419449030a1a4401030350341d0031344002813002c001c0c600340d60448981c480d80565249044400303440161125050005010345400c544504c0241d00d00c040411003860700e250f0011502b40c11a028000d0101340c9401100e00c150320400800f501c0c00d02e4280814151254070840326038a005100011b2603210b4803600a003580c42c003400440070451240c2001070340f98900e03a613840c1c101c6241c034120a0150360310152841e03d0401f542c00261b21000125000500c035815800c01041c0c210b060750342010045d0700004010440b520101c1c007903000d5205e941aa9964200656040c4c0300070301 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 339116276 1250 339115026 339115033
    0x4060b0411030a09051606081603060f03060b040b06073503070c0b010803040b04060528110705010504030f030c03020a150b090a0207080909071b060b190b0306060903 73
    0x101e2000e010180d620940761642c1680e0344803060300a1141c00e01441d038000c040070444c555903510740340b4010461213014101072940c0b20140980c4070850700a40c40781008103550001d0000c00d65a030300b4000000e005115902e80580e0030070140303100d280350150484807441d601c60f001446c2c4c442d0419000c00c80e010741345540540302e181e030301e41c682c01001c44c0405140300f4040340e034800341c0d007881030301e003001302c2140c10b90120304a03074001e2006008071003040040d0307019a1ba95151541d1900d1103500c00221010102c42000350503807200c01306020042d03001c00304003052030810089500312a5174070011207c07072081d0f01c07000e0404080460340e0000244100d100a550500900c112017116601c0d8440c030320800300c840d0311480380342d650b01001e0701103080c03824295600c9103100b1011070038103c09407240401407280c19051072080c140c2c4000103c80c180200705102104d0480c0100b909001a83d02d0040d0041403401422445001614041446154400c8200080d144010b01160564550302c0034000382c2e40200001c0d40e490b00 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 339117526 1250 339116276 339116291
    0x100204081e071a03150d110d061e060611071a0a050d060e09011a030613020604030b0f06040b040b01092610020a0e01050a0807080604110c0601150306030b04060b04 72
    0x500e824064050030b0050b0003040e90f9091001030640321721041440c05005481d085103c00c007154181540260307420060300d10031507a0f10a85411402055003882d03840180e01c107082c490360750814540c001c5040c0ea510b901c4e01c1d6410f00140e8034559446500c0d01c9070b0203250480c00e003900d1880c3e0204003d44810141800c0c200e06100100c16440290750b89904803142805141c0d007000600b400074010440d243d0101c2090021040014010903241c3c131000b44901800c00102003900d0454464000304c500440d004000b4111600f407641600f441d01c4e030b05844c50b510a901f004480c2a00d450036110301048548141c440440e5646843d0840c0c2d82c01c8080294000010341003440d40507620720901c10404800740b2242d00698070503544d0405440e007000c04104604100d0140003040c1d0040d08040341700d422482c5400c19401658a040004003d440203040f1450140b0011818800360703130002607003905031243e49421704001051100c003203003142d680c2e1002514003806803000c103020502d036900503080c00002810204d1100d = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 339118776 1250 339117526 339117539
    0x80910020f070614030c0306030f061503060c0301153b0907030e0706030e010f020403050d0915050d0513020402030f040c1d04110103060305010c020708100204081e07 73
    0x52a28002040258126800d8491044020300c041030103082581449444161103424910907400000c01c0410981341c0080811b05643c0c00304800070103a1161021039100f45403102e072070910f9038801350b1101d00900c00c2401041c1441240d00541e0f042ea0720141010341c50f03801150040321501054011800c44c801c42c265040c0c0149130107100d92600c4104901c061104201c81814811055001030441d42018903169155080f01000320f5000101d030002c0c907000c0380c3d5510900c8190700400c1c440801c014030307134400140002003140108583da10300c0a1521046285036580307440c040c8000d084940c40000503400c01081075100c04503030005800500c1482d0641581d801036010504980c01035845071028445c0c1810841000301c0441014060b104054801c80c03005240004614508c00150009110078400d001c80302c4241d01c01e50000000f160040c0c024080f03d6440c80002c0d4a0703810761701a80203d0700590985000c489400d008580440c0c014038010300002c40816101300c01e2030000345103460079000b18034001518 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 339120026 1250 339118776 339118789
    0x9090a0e1c02070905041e030306120c0303021e071703040e0907080709020f04050409020f1f0e010305060a051207080d02060a0b090f04150f060b0706050f0f060103090809 75
    0x101400e807403503511440c1010b0314040b240da203d03050050401e030030040081c102c1030750301405614964000c80c1c9a600340c94160050007484e00042c07000e540e0100c1c04000d01102107455000c8034002c0d003e0700c1a06103d011051a03c0687d1328400304a03078880441000303160b9001140d46082940901620304043d01c818009070480003d03a1000115408407009100f5a4005d00920000b820130f07030b104501d060354a01d028001405240b01d01ca20641d0749843c20b0055440344842c410a8803001441c80500c004002150001c40001c805400000b1b44c00001c1e54070340e54002c0c17003168054600180410541032a01040000318480520340756024010004005103546c0c0403c0003a1030b06103140c020b01414030f0030340818030441c0ca501180911801884042c0500d56603c00f02c034542103500200c1426040c03100105240150030140180d0200c075240100c0028890303003043c003404a0324801c010a12098807454141401d0207025103940912901880100c1c045600a6102100c100d205001c43c80c107001c1881d000681 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 339121276 1250 339120026 339120043
    0x60d05030d0203071b031409150a0c0501061d010b0a05070206070506190507050910020c030d0206060405151f09051807030e0105100306090f08040b0403050c0a0b09090a0e 75
    0x209281c02000f405001904500e1408410303d8001c0d040c032185e8000d440081900c3c0420446105040d40001c2d106402d8951800011205807103401240d07850100700b030014540103d6100c1560694a0510085011401030032604206520706c0003031202d59007020318400241e80407090141c1408010460280113840d00000380c890280110042c08440c0791407061500c8803034099400300e80e4180b6041c00c2000701a040810b844c0300715015210b45562005c40f0300181d1901e9200803023242d0520800c200c003040d00340d000501030300c2204241da060201d0703120258100c41441003290b1255101c1c410311030050440c00314542c082c41144191529400742c0d03603540302044141c5564440c840d03500c9000c8080000311a014011912841c170000000c00c404d00c1d11a10744103a880c1d05010050215803240042824003840414400905800021155685689490386500c95101d07200444035401051041c00e4a858a0107003442102d00a0520a180c101102c0800040b4080181000b0015907122501408c03054204070001 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 339122526 1250 339121276 339121297
    0x105090301180804170d09090c0905120d030e010207050a08070309090c0507062f0d150f050a060207050102060708130b0708071d0604030303051905070504090515090f060d0503 77
    0x41e40ca0703043c4440d685902c080816174901a5100140c0c00c504658083e804038121140384800082d6000490002c84251200e5030100d64001280c2e109004000030106003012031004ca600c0800008420900e154240d0040301030141154201d000c0d030b00c003c145102c005140c5240310389010413865458001440440d6411512400008c0000c5580e404216075841000c500041d103020740150b00100d0903980c9171b5003031401c070000802080440c1301d01d004480358100d4000b0468058603500e8080d10382103c44601c10052194a1050100410028840780041280c00607180180c1c054086560f030300a081c2c034070042c054049c4450941111150010604506055028040640e1395090505010b080100420300c0c041121640d0100e044800115680e020300312402c60344e2600b80441d1554444644001d214040700144182a003040e00308004c513503102c4001c0c42900e000090810003500d07614100351801d040d0003025500800281d000c182c0741400c8030301c03d95100700b00400900082c0d6040c0c2d56181150024043c0300e = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 339123776 1250 339122526 339122543
    0xb150a02010621050c0111030708190e010804050309090c1c060e0105100801122f03060106030b0d021306051801030519050a12031d0d0f02031602010509030118 70
    0x520089a40480308040d001d0840d1072160103030080d880d010740303a43c034817071961707060100004401c0d824100510503603505681200c242038880c820340c030046603019240181d660002c0c1402c0100c100660089800d5400303150000300440c1840c1080083c0318540380042c02d44410480d06000c0001040e0f00058000d8001a01c1a80840c000c0e180c400c070030544440680105108004c505001d51038154088081030464404620540020300c1d641007001c40c0c41203240350b1440c440010128400584001004a611124294111003a5aa88080c01c404a540c42c91905500c28203110240c0094a090940942e940944101c00901c0710703941c40000d80c4081c529071900c500006054010024040b0500424aa602e61840d91910b40482d5580f403d496126814008045025102035800400e02c243e000390a42880c0c801d0007600d0300e85214155a48518681103200041d607043c0c1110080c034408826554070610041e0944500401c3c0c1d4015601500411320325a059941c03980154481d156100600058501a0150 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 339125026 1250 339123776 339123779
    0x4091a0406090c050a080402190303080117030403020108070e040f020c0c0a0b0c03040302090a02090406090b03010f060501020606150d02040b120c0a050904050402030a0b04060c09060216090b150a020106 89
    0x5010680700e0319446603040b24600710b9201000e6400c5011907a640b212407401d400719640c0c03403002403c61410340082c0e4540403a60000401007542022040c1d0603114140d2220749030320076141c280c9640b03100701e0000a00003481080480e01c2c5c030f409440008030080e001840426141415181c101c100d0f04200003940e05a808000701c507c45003401c2c283e401c041c1000a0310545040150150150b8034071481c48000d0040070340d400003800e0300c0450790542d07410160040050059030390701d00126015105140800740b00754a4407a908010f1001c51081c0e030100c0c0d80c1038014040030f179036010400c4644010b012640400034400c10a2103c140a244000c201819030030b20a01d4481d1802512420144401043c1c10410001000002c50841c1c1003002d4451821045801290540d603506c0440d00300120018000c00c65034006003031004019007500310389908809070b6104840d980c1d6a372000c9070355075142407600b14880400e000034405030b1600d8001450400c4043c2c22003074005031003400c0c240194061010440143d568880 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 339126276 1250 339125026 339125029
    0xe01090b01051504030c05060304031b030903030306150905011404050d08030406150e0c070c030519050c010309030503220b2401030207110f0423090f010e060a1104091a 74
    0x40d44002080003100c03d504143c1076664502c00d801403400741038031a510220024081602c00c0660194030b400d8001101400d14007450080c14415203404100c001c41e04260002c1001090300e030710428001c1c0740e540c4030441e0341d01d090300564240341034581c0070203800300070440414a0b441d41d401801949114080d031a42d246007505200c01212201c0010f110050003040d0304002c1d002c03403001c505401c00348000105564140500d04107180806c1c41d0310007030150088402d0320000002a200203140640030380d06898007140c040c0011000c03a200444001d012a00510106086540225920781030f81c9820100901d01426511562414042141c6080c52440281c031400c0c09a0340c401c2002c400001c3c207003420750401c803c0340d40b0701881a10384c10915001e194540c807101d40c299680d400c06403115590071400c20303102c0f920b071109003805a01103c62105d82d200d111140280f0080520a81c0f91035640d6501815043d15194241c070041d0050801081d074544060001040414042c0b1400300441903401c00c969101403c0350 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 339127526 1250 339126276 339126289
    0x13060320040506030a17070b1f09020c101104080f0610080105010e0708090106090c050d0b0a0b27100e09070804080a0f020703290a050408070809040e01090b0105 71
    0x1900c5500441c141000d00c001da0320300295001240350b000400c0c41038200307503409249043c080c06d0406040703042c0640c1404840400d00100e100141c015244124100351a004038030180e01c1000c1c40d0000340d521039441540700c0542680004a00e60b005029075250070798620702140791000056075008541c004000780b101d01a822140000200704541c002c1c007844d85802d00882d410100140680284500c0ce0000f5405e543c0c20340c4800c0c09441400b9040004000f12103006206801804c5030303d09a92907c010348421b407509003e050304a1b040c00c08210310f080d000541d11449855a07400e00510b12540c1e03007030715002c3c0d81c0714a181c0b00c011850b99200c84000c40503004100c01c1500140ca05800e000b2040c09120118100c3c0f4100e40503810641814071800c1c8200a00300d2074401141c4c00949080f0364602240b484400403c15410070302c0440c1c2c09220540c40d6000e0303c0c4110f850944000b80048010014000064403100c003402030100028400078680181e100160f0039100810400c072140c3c0d440c0c4006110500c1d107403 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 339128776 1250 339127526 339127583
    0x80a03051308010608100e030c01110d060b0f1602060408070303120c0f021209030717010203090d050f04350c01021903050d0e0a050a03050306030d0e01170402130603 73
    0x1c2c8003d100072031070070b079030b0070b40310803080389131501e816203994950105080070022203d00342e00000080080220f0400c088a2941201030340c2c826881c101080001c0803c1c90906585400c8200040c41e46031402114540000450480b01242c002ea4140310000320200c1c107001d0203000f1402070700e0b84520220580e09031803c803120741c480641480f02411140c400e0b15070004419040c4040c02808956403c00c0d04000791800d0700560000701c000a4408810000441c1034000c5c5002e0090768007183c00c403011a100660b005e00074103088106801007440304005000911400c01e96161110a0039802c9006549100d194850600400c840701d902c602c07501129564100403814002c4008038642c41c0c00c208071b9070010a203201d2001d6004040307465525644007064203200021030550702908440116450780b9026141e90000c5075458800c2c01400a149001e0317002d072030b40c82c2d80c10605070348800114050070b650030751416010740300b0398008280460211000c6568411000998050601001d444420306c01075029182e90 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 339130026 1250 339128776 339128789
    0x80a030c030c050c0c040f0608010c02030c07050a0e040f170f0a1806090b07020301180312060605120103060e0a0c080c04230c0708070b040f1401060b030a0b010504080a030513 77
    0x4100300c0c4101c0c1c1d4082441051608106c0d40031507805200302000014024582007902c0c00c2d40f03820080e11000c0d8000000b0038a8410310002d03110b00c1507450003000303880416407146c06440030001c4000b034001840200c64108481c07180000183c140d0080b800c55096401540302c00c511207000142000209030000340d4840e21101650f411600b207424504001e000659500c542c58054901081d0304007155001e400022007101915442d01910200d41002491407020320742180483c1e113404004511644214200c90343c940da04201101c142c1d1a40d903c0f03000502202920306118000c43d0a44c00004520304046030003820104c1c014444590f02c0d00070002282c1d40f0300c1c1d4001082d40c044507404090f0005451196000c00300c110b034581c5440950401d44030328890758500408e4520400100300030003010880d9108114003802181c0c1c801c08000026900702c80341c9000b82440c50006100003042604103400c10242c1e94418505107013010746d910540303454009190000ca002c82c202003100000d11520310b2019005118 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 339131276 1250 339130026 339130037
    0x405040e0f0d030e070b13151e1b0b0a061806031101030c090b070803070801060201020c070509060a050301151502160303120b10030e0c01020a02011d030a080a030c030c 74
    0x5551080079a1800368807100c0c1c05058844000116901341448004000c140c440d03119a56681110003007400c20296004089500b0039103604a0490391090444911030100d50500d013071b1500c0940c1d419120148200043c03500444945548400203158010380c501480199901207002da040001802d94400c0ca544001d420714a840420030214100e84207100d031800080c2000100b940c4100b10440f401709650b041015881000100e21003000000f50056104040c241d8840b091030340c0300d0400724280e20400681c0c04440d402400c06200070310700507050030740201c4001c3c501446103503184003080c25110088504800258501c001300000745080c21004000ba8841c40503003126110055080c1c00110386000250411000195503003007030006510082c02a1002800c0c070400d400c1a0800078090308203694220054080c0401034000d550002aa8034035455058440d40300c80704000700c420344c154100f512200d0341840b0344090351010801c580003d2014040707e40d8041010f6212900c049c0c190391084c02a0410050f = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 339132526 1250 339131276 339131293
    0x607080105030d08010b030c0408030f04031a0f06100e0d06020304061a2206090905030903101b110109120206070906080f0a09021906030603060e060405030a140c0d050405040e 77
    0x644c0004014151007109810750384036100ca100b003d40900458101c40c01911001554050307000d0345030040d20817244101445c281444a02c05034814400c2d003910601000301c000d4003c10900d1503d1550f000414030103140c010b2002c5c00c5072001a1013106c2401041d501d40754000140320a004c40c500404030b84040c0d18038984284c41590000c00c40b00d98039a0140b1840b50402d40c03144600211607044a030080c0034448080c0050b01803401d1980d104e0384040d075000c3c860320440d80a441c20326040d002d034030201070f09822403139580d0010580540d100c8000340000039040d540c0b2400c103000181e064111a40d0071a6983c000c108901c0d100c0000b510f40c580b40d4120301c0c14402000108800300e104440146e50000413080701140ba00e007144040340508210444681013101d4005010a01c60751661056040342d000740000c0c4415110002e03004d40b038690589014205400801c07400d043d1500600c1e1940c43c0d20071154000e403030035a04403130701814050708a110000059001400b0001032400c2c2c000c2c075911240c110068800b50 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 339133776 1250 339132526 339132553
    0x120c010c140f0607030c0f09180902011403010f052106061c0c2306090f010f110d0504031112071e0e09030304031707211d060708010503 60
    0x40e00c81200007045403a25615401840341d042c4495600604010101c80071414803100240c080c01c0c00050a01c0010850a002c9003043c0c0701d141100c0032940d210750848a0038100c01201c002401401d00182d0600000d11907401c0080b050800442c02007628480240e00d05061008001c131803150510851000148e80108840000020030526001718044030b0411000302102c5503072006080f00c80d8003800d54400c02c000015022400d031014048130364100040c484207400602084114011106402c2d040740300d8241000f07107540a4a43c448100240742003a58064840c0340c00689003010500b03580c00025808a010401c01103444244a18810203c0c0d40d40e0351b81d1040d00c81155174000611901424440c2645c3c1902141c01020344d40018045041c0c0040031840d101c030a583d92a44141c400720005200b0840008402908614650052a00e0796030099011500c0e54240d0074074868030758064440d40d43d50384080c17018108404000d00c3c0c143c8d40000d81141d142c00c803000b4000b40016440746000750480f40301250349 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 339135026 1250 339133776 339133787
    0x303140c120a0e010c0e0a060c0510180807110f060304110f061c050f060105070c0e0901020f0307020114060a180504080c010c110607021f020706090c090902120c01 72
    0x858010081e082182e03501198a030140003144103c0300f580d4a88452607011030b030301020400f030810060381c0b2048034540c3c0b040101c400c0003d204010741260811024142c2c10f903841c0c0c0080c080490440840c6118101070344552002d83e000b10400c4032140740c01346059007603040c0845000d44001c000c484041c04c40c0b4054a5000f4440f50030381120784204502c0c01c0e0f200e599607030030054501d82c07d925a20002080401c020b000b00400d0141c489510b002200000146298841c60440380000e40c41994800058500070030710050b4103025000c1c202c195002e00000400301000c401035449003060368000b041d480344c00c00b03003200300400c054001801880b201401b4090152001c958607a07900e9075081c00120340e41d85082014007070081c403200802035400d150501190586c03041c0302e03c02a00a40091325844d840c1d10710180d03038440895419050083c041d031540713001001c3d190b01400d00c450068802003400d14090780d60506510721604842c01196640c0c00c0380040d030505003140c41c80e00034100020300011918600207441d = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 339136276 1250 339135026 339135037
    0x50c090f0105071a0108100615051911060c180328030e090106050913090c06080402120d02160602010b060405120a06060b0307030e060f040b071110090303140c 70
    0x1800310014004040105200075a0004480c0103c4c0541c1c0f561602842520307807100c88558144542407010101d0450b01c24849080703022401d446091504100d40030318654407489025260a0101b81a101d080051052110500c607440c018a620758808010b0184181481c20100180c020f5000c0c00525003404800309a00c454818000400c6040c1007041c1f0b011034800484010703154000c54130800000380c80360414050b203804c10040b40d54800d01c5003d0011282115003140340600451131100f0208006402640d80c01d402900140c0701441000242120030b01e00615400072400603440004151185021203000b6030103030003140300a02240f001362000542d030f80140d02400e44640540c00040b00c10030800c001c401d4106920450920000c2c0e03071002c0c03d0600303030012507144010070300b8103030780610010020680520818035815040c0080d01c076511078135600840101100140b00e031213440030110358010012030420700003004000c2407070740c05441d0003400d403803201240c1d20381c540030b44090003032083c0c2200c01d946 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 339137526 1250 339136276 339136279
    0x100c050d020730060f18050a06050105060c1b01140a0e03060c0a0207050411130308040e060604150c1518150501060f052d090f10050909040f24050c090f 67
    0x603881010b21181c8000384000b8660443c59082d440101007005804074010b82d1b040d019275010025a03a0b42c01c103002080c441d100b007070300d41f9810610324040705596600f410038070082c045c5049040c05400580806280d8040028000825081144101a4035041007020b0780303d0070ba40c06003400e040e03010001964a0a81e80140361040c1e0301d42480e0000d0b94026800c1e51148510200c100b9042a40d03814010420340c014001c401c00300d811440060560b041a004580440302000791540e0788070400d2030300f1251241c2d004030843c1d0301c42c214903000035010014014200440322605c4110051442440c0030620404148181610203052900400103e07405c04c1e207446080095003070481e601c0c81c4010301c4444c080c43c480142400712200c04209200079075035802034038a078082980c0015a2843c10b03020080542c0e14446550300003042048010250309102e140c1e0350b0094494220040e50070455a54114569a80d99115504000d8040c0914550b64107000343c0750068141640b0500c0c00da150300210b80b5000c0c0c00d03000d49 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 339138776 1250 339137526 339137531
    0x1e0601030b1c020d0f0b0106090f06050a050304210e0906090402030c060d1e0b1c080405010c08070b0c072307090c1b0309080c0105040b030402100c050d02073006 71
    0x1042991075148484e07000d65444801e8040c444032a1401c0a07044100780600e20025a49200108032062040c40d8407040e2000f6072200c50821807120403c80309035100800403071300d844040c2c1080079426019081403070170080a484140d807448480701440b60780140109034612410001052001613240400c5100746400180d4540380c0e9040711840410180041648816207104654401403600750141d200703043d40f050440343c80c1d00c4002411880b051803a840d0340d01070300d0b00104000c100007660003001d403c083c092007204944d00302b8140d40c607022002c20045400703442c150800607800081050307081881d040400c400400c6080c503c1918021a0394903c0c0340076400744141c1d210f20100315180541e00d5101d40f0200882c004440850a03d002402030b516880382810300e128600903020158014000d803801c0c0d4145003042410350b1b9407602042500701c002c030341c2d0340248600505140b001c074030103224030541c481e2035800424841e032610340302d00200501f078038800303001c1310b0024509074480c2403013140940d050740c0000c0003 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 339140026 1250 339138776 339138829
    0xb1806150c0a032d09050405061503010b0a08010503070f2c0403090f06020c01081518040f1101030c1205071e08160302160308040611031e0601030b 65
    0x800c600c80c00840d0909485071007206010503601ca14005a0700c05061807203450401c2450290300e016030610b9138000413900c03071041401542841d5000540c0550010035001005001e240b080d0810b134801e81155240e078500240343c11140d07402008081c0141400d60090282c1031820400c10391180c01401085807048079030781409807030880040000e1010105040b080064145450060305042842c400c10404213480c0e82e0001d503040c0046181700000c04103844c0c500c455650324883c0e81145502030000e84d4442500c4a4403081c0c0e6185410301d42c85140305500301015900d45003441c40080da03440c10810b0403d070511031507220b8598022903541491044490100c1c03941c9802e003044d9070141119800e1840780038034181280ca020fa103d0546c500a11601d060180d503220700e0207040f03050380b080d0a4580c0c02c07078000740090f0300000d2054866a80c46401440001502c08881151000f95402960750722000080390351030115001600f040c080c0c0106c02420304100c804d004002003031204020b2289298104804080d = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 339141276 1250 339140026 339140059
    0xb04080a060b0402040b1b010b030102090d030c08040b1b01060503030313060902030a020301021611090601050a050a050d0911031b011407030c0f030207061103070b0408181302040501030b1806 84
    0x540740644106e120752a15400c0030340340c456520750f00403d21400c46d8207041034500b0600381803013120072408000d004a044641240c0301550448140c8104456010003000001011500b02005e018522009001d4403030f05864040342c40d003035401c030703401491003174100700305114180403c500c0300c240c081d034401800314107082c035400000d041004142002c0d41550001501442d00c28851000c030138028030075804046a00118400e2241c101c0007140c0300c5010130b03801c1021914541c00341001c2c0101070454600b16141400405007001074485507001103403c1c0c607c0c800400124a0140315062101105c00e051588155000000815421020601d00c00720744001448100b45440b6200c140606ca40209039105800b80701e1a001395204910b1081e44001803c000380c00750552400300440f0a401d41080026035991111380300d04005600000740c1200d42c695054444a454440351081111040100f00041e147c40c6860000341c240d0302d0040586104220f41d00341c0c00b0061041c0a48a5040030080e640c000150a0000 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 339142526 1250 339141276 339141281
    0x714181c05070806220f021908011821020706050c030904021201030501050603030a0503070807030618050406060506092b0209130c060c050d0c030207090c08060a0b04080a060b04 78
    0x14007501d42d008090300441c1e010030000d9468042c43c5820340b0954100081000d86140100080005102290205041001d071900c0944842c101e00c80c5010251017507aa90540c90031150551880c9800320b07420741d6004244010007842e2420320100b50203100d441c000c1c0c030f40001c0d26803000c0e000300c50500002064000e602d0804006551800801034002c5686614050f5000780300b080074070080321355600384000603095040103c1520b01c02d480d151511404d5480b02c101c1550300308ac00409240425990345000101600400142500011400380001700d07400d142c240a002d0300d0789604082d01455040298100e42d84031101000004c0907d904080050340210030101d000126118020b0b51101d004e60901004000c40c021807840a84a528400c3da0035684020603515a182007001074419040303000141e2015000d0711152541034402e10544000a80741c1684804480d2911000c82c0061041c1041040a041c40e04588003e004141140d60800303191202d8295900c85072030004100c90b840f904511040e44958 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 339143776 1250 339142526 339142579
    0x14100306090c0801210c092304061a15071502121006081302060d0c0207080f0d0e090112031101020c150f0a0902090a1109090a05071418 60
    0x107041881a060000750007480c5003002e00840320f40003220101003407401d044501c85500b280d4054503140d1a6032410303c0840051031003000ca1090074655040c01e0840790511400319100e00c0c45803000092440c0c240c0140c070054249130403040c1c01255642c03020b11147e0a010240c4040e01d500221514441c3d0200540348068060500c0d616050840c110031302a804801003581829120181d03500486540c07560000e14049804140180d0031840c108215650050309411003030080c1503e00458940030740d00d01040745020a000c502403010f4001079078900c1070300d600481400031803004684085d0345505290482c82c00c3d011109005062014400c0c100d0b1703c9010a4042d141c40034022415541c06160100c1e00a01074401180d61556051201c0c001840c940d40c288281c0d03111503000740245290786d5403c440d1078010302c0541b14228200c2d400380150b08859481141d028462004520042403d0230701d520090f0201030907070200c1c03213a02000d005503c0f5500b03481484002d030100455000d48507040c45001c0c2c40c0c618044 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 339145026 1250 339143776 339143789
    0x180504020a1202300d03051003120c1b09060f0803030c0c0f03030a2304122712060c050a020a0f110613060206180c0405060f0307080606010e0a14100306 67
    0x1035131046142c048026803101c2d034450050040d51548000004100c040b18011108074810041c1404140701103100860007162945560601c2074503045151500c3c0c600070350b200d0603040f4030580c4120601c100c1d5054043c0800414216660355221405e0106031503d03404010282c464140c40412a02c82501d002c02c110380744040800b007600d681e82852800080034108880f265071100c16800051403502c0112505c45104941119907000d440c0030842d0101c40600200d010282c090441c000c0da4141c140c00040200e004000b4041d0021503045c4c0c9140030343c00c2e2042c450030b45091010901445001c140c0200f4420046070b408a1200700b0700b40f80e072400c1201940c440000941003400894101e2034509501024400d071007658003211102d80c0c602e0101c038880051400001c003a0b07009141000d005041c13035005940c2010005100109180b00300740440d15105250b40990010390022081c01441e58012001407070036441a12080c00803414040044038845445400500a01c2d030020343c1c2d50b0040c071130350009000e400c0 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 339146276 1250 339145026 339145069
    0x207020603010303081611191401020a02210a0c12050d110304030905061c1e0c05030106121107020906030f070f0f05040e120f041d01180504020a1202 66
    0x84a08000706a002c0488119805e1006c406c11203504a014107140d46201ca503220080c0704020841c1002160200204412911562074a0940c0661340e820b0000d0102c2442d1940104084005040c0c40c1713a41407204040c8200280c0c04011071078049901440181e0f15503001800c03e40300c640c161904070f80602c41d404003054054900000440c9410380c0e0401180114000d0355161600da49410401565115506c4028021526460160340200181e00460501e81c80201c50309044410740d80658180ca0600072104009400040140320702c54000402d0700521000c8042000700700c1c14184ca0040c24414210042e00c80e45c00070001910a56042160324880c484007000e80303110390340d54103508440713810038001c1903030864107508085624180b91082241d241c215100a1480c1440e00b0602074aaa0014050b041c0381c40c0100004140030341300d103001c9040780001c09070178075041d8944400015060001440c00464600749410b10002d81e0701d500140040e1410101b500c180b0101c2480040e518080c60b0100042988 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 339147526 1250 339146276 339146279
    0x60d0f020a060905091e0a090f02060c01090b250503150a03050d1214060d02240910020d0206150105070b0a09030f08070807050703210b03010f0b0a0513020702060301 73
    0x26444600182143d1080e1040e034401d440c2d843e60500c070903c100c80301902084a50000407c104d42c15004010000e0142e104c0714480c46064001c126a179021218020090f0b4541c851241000000d20a00d903008000c4010b0496048881401500c981d003011003040c1007190100100c0c002e41d03609940103800701801030100030300c241e691404540742d400e80c2c0e01080c041031070542000384000640c0100103801760410107101883e036401d01080400207681c10180e8006030506e0722424040f20b01d4840072a005e00f00302300039440c1c0c1404403c2003003a240c09072a690854100150400ca9250001901e40e00002807004070151b10a0100040310341d0700400e00054066081002030003403103040c541c00f00b490140203656004200e000c00c50240c5540341c0540310100001c1101d00014030880c403c6014145052080ca0800135100c0ca42038551030040b01c0c226484103040d51403c0c003813403e1038244241c0c507441042d80c07424400c1607032400018406c5545403107401c0c0603a429403000c00040402d941126000c03076005001c15104d5 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 339148776 1250 339147526 339147539
    0xe060a120608030f0d0c0306050310050103050c01140a0818010906020d050114030d0c03030b060d0b030d021216150501063209041d070b0c1c08060d0f020a 68
    0x24540003080020526001c00031590304000f1040702c0c980849628850314101902040400514400302004101655100c02003400d940520400e0520161301c000414a035045040a904154010034070074107000344540c161040c40c082d1419140c80301040e041c107140c5641c0e8100c2139060346200700e440c02c01d69481c0145500c100304869019114030395000f9410401682c0301c0c00302090344201c40c1000c0781e0541c0b00c084610100e921684414500602c00d1030301082da05590004600143c0010762410402901c0c0d1005200d507040421094400d000709100030111102100e10340c1c03240b0b114801c0c03c5140341c08120b041340c0900210003da6548040a00320810003503958100080001a003030341d1181e4145440c1d8014400c0c1003403001e4150300b4114809040345031401c0c04082000920300d469444003285118106940c05500903c00b1400038180103081c0c0b90384511024589003040100905081e2201a985c0301e82440340c1e00442542d0b0040c01943c600416000d681009140e010b09654000c1d8400c401c00e1011440 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 339150026 1250 339148776 339148787
    0x90803130611040602120c01020403060609050910050f18071203020105190e120a0c0b01030b06030d1115190623010203091503060d0804030b0601091d070c030e060a 72
    0x10600600781000300407000c030b620071224403a610480700180c0c01442c03180c82001101c030040c910035845000041c6040d980395a01420780e100355010030861a42c2c2c0f42042080c400500c00610b481600700c01c00c10103460507520b410060800a4840088128085d42200507100d00f080380b10041e08000042c944184214034000303010b043c08803062882d480c8c0008901458800501404041213030040c0984040c400480c20009030390401038a84042050b1840004003041071708821901a41c0102000c1c810352900030141840e081c8800b840a08000748150910200b400228210000454100102c280c1d03071502c013000d12440e026070b20f107142900e18000300000c42541001118426080203080f00d014400244010b988138002e003da0075402c94403420113110440440b4004650010780202501800c01c11915150501e400070380045801c03e0494090010325a0004040c0303006200e02044058240000c840d90714a0b20700c00307040303001403001c40e916580405004044601c4a014050714184d11445040d800814 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 339151276 1250 339150026 339150061
    0x51504020f0712050301030f060513080a020703020901051512040807050304060f083303030d0e0a0b06030327040f0e061006180303050d060b030124030b1f03090803 72
    0x30740f030f003160700c0f00007821340141d0517241207a4100d02d03032840707061082c0c03280320142500410103803d003c9400f050f000042e10b444003505c80140e0b0b070f500a11030f050851050000088060300308a1068503002c408075601d004d07080c01c40b039000f114010310050a480314a0031401d640194003006005001c04a0301003182684950500105a00b82cad5454421340c89802402500f00381384048000b030140f14078155016402d0302d0000600d15a4090200c914101c01c0e040550210341c410b180002580c0c1115026038184003101131003035008141280607500d4540ca1900a501c2c1c1010102c51001a55050080d0f071540c2e0744617440706105022000060200580e91000d5941b604e10072500006508081e61011a036144100d008480510030000421078040c2140c809480603007022880300c1c200c41e01c030880400c807064134074050740c02032040400c15169426440040c400140c20107454204040c50140c54401e559038002d105503940585000b10080d800d00068120047c248800014012000001c144001d020440d1401c81 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 339152526 1250 339151276 339151283
    0x703080a0b06030403031806111c0b030303060904080d022b09050c060903010204030507060f53041101020708061009020c030d05070c06050603030a12051504020f07 72
    0x954980d00c1414a03000c44002019007a0800300500c0000d0020780a40c0c081111702001a0300301118030216520041079400c40307954454181804200d044901400c0300c09181c28005105e001d124020761000425a00d00000f0302c41c2d44030b202200040b8091140c19421500ca1004150f420b55a0741007017030048102011206400c072503000d40036004260045184079001d0080c2d4440060890120b0640400c40180c21290348140d0555013048000700080c41081810b0040801e600d076151b01d151440400740c035020346142e21140704c110030b081c3c00c0780070105c1c80540c1d0902c0c4403505403c0352284030b48101c00d04514466070403603074054180051005220071141400b249881c01d0342124a0540c44554980d200c10f0252440105448003c6061201e921283c02801c8100c10036011030b801c01c810560480161081940c254012607c20303192030041c02040d00a00794021401d0340194a40501d90800500603144040d030041107550701c00108555540648003a40c0d0450002c0c0150b4503040f0302c6d840d200075680002c4084 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 339153776 1250 339152526 339152537
    0x19020f130e0f04030e1c0b060306010e01030c0e0a060905150411091509010c0f080a02150f060409020103020f07060f0f11030708100b07051509030405030c131503080703 74
    0x303400d0820071100c610400b100410000300b500d41e5642610300501980c8440c1d44a1482c1c0003010b0300780e81844c1c000c40841c0c00384a00c8451410088181420508103070040850801d0160060002c00c141400000440d5071100d0342e408244e03104031090004054940000c14583d00b0002409030002285105e41e01c07030001200e00704031500101c4908403081c86080c1086402951131382c001c510070b040d4440a861035070707418145070504100540e01c030740500341e400f001120b0b44078003c5026210b45604100c4c01d01648910341300c1030140d00b040307240032a210100426103031049888080e42011a48030f9010344280c1c0c054208984e0301c412191505c800544280000c80d00d50914000c0c40c001d4644c1075006060114060141e1140765481e10301c000c0398065002807a440f403819500030000388160002c40181201070065014049000c499a0310409020010b440c0481c00c1d0b0040c0028406594041800e00030038100703d888040c8801c484081030094405e000c45104038001101f000024010140d00800040d031203590340 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 339155026 1250 339153776 339153779
    0x2010c05090f060f040806072601030b1326042408010308030a0605031b19080304054c020115030212150702031306090e0f19020f13 58
    0x1121036009000900703900c260549070401c15424801c00400c11184104011480c1a07144c00c80589005820780f04a03000a035492032294001049840101d0640c0040c8000311081d4555215004a0306019180340b900703611850f00441003062888000c88030704d80d01e000302209500640c50300302c40b58000d486801351400300500340b007520901c11400c5070342e013000310344416240b40d09540712007100340c0004080303c10013aa161008155658104030741d80d00210859175048102c00e40c6024069607042070403403103055095504040c405500040300350b078140ca00c144d4103001420b07035801140d070b1441c0b0148003c00e1001408000d11b0903140b0860f40c402465041080c07426001030900074200d003213402d00a050044401c001e901400107151840303c0d0f04445480c8400c03a070490310780c00c032000344c08070042d0348bc040507a0001503404004011224030b58001c2100e800c0c03103003440d8680018110741c008001d003401c240c00444400a0b604e9160a21105154001074104544680e100130745540b4580c81100c9078000c0382c208200 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 339156276 1250 339155026 339155051
    0x303110d08160309030203130f032001020c0f0f0411030f1006091a0d140105030d0c0807020603040606030b070c05060a0204180911060d0b09010b0708040608100b07080a0201 76
    0x401038040c02d82154400c200b1400100200d00900313090004800314001000b1212402080c41c4051010300881e864280e075461031413a1402c0410074090807000e00000b840c1c540002c40c0e0700071411000c6003009440ca0510483d00744001171504041c2ca1510303502030300d00802009070002d081c0141d40305151940500d8402d44030384141c0000221244540d10010750300b6a0140250a9410041c0d44401f1031201d0301820911030f079100b6400d5030018040c41c040b42d00c01c00300400c442d140030840f101c910340e404d04200003002290344a90f030003441403100280c00740754008040b0b41000f0040d80020002d542021042040e0b08040500600d49510202c09848900c41c103004114141e2462080b18115000f20900080040d15032503070304060030888000b640c100d0309001c040269511644001e01c3d0300340c00c00314000b99002d81c900c00c00c5101d180607006aa00301d1402d0110100082c0c2401c22142980d119040803d00e6035282c440040e60707030301184c02c4003000e1580494080c0801c205c40000d042400d4040d0000d2148040c1c690 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 339157526 1250 339156276 339156287
    0xe03070b0a0204050306070e040906050f0618060f0904050309030d05030f010905010f0302010f030b090703061a04060917070504021207021504020105040902090402090a150f08040803160c0209010303110d 89
    0xe04c903070580108011449180c0107012083c02c3e0500500007040c1d903070164072140c044613000c031049040c6070004d0341040440d290440d018100366024003030611040c10a80007040d004d51110b12000c0c003501d458408101807040c10003d41d1015603004037152001c0d150120010710710f4100350f400602c0c0714083301c004101c1c0142409164181c90000302c2d4140040c2c031f1900110707084581c0910401c18959034095100c03007501c5009450740f0900490b200032600900d88002800e6040500c907800039008000c0c40f0600c02603601c800782804031011107040111015511800c2e03414484594403c1d42d00500c001040101907000304416441140c00c8d80039603518070900c184010340707a0802c59000b4001030040105000601c2030740c2c0036248170039010700010b003001000700c0401d080d100c082d002041e881a403014021611580a1980200101176152280d41420310395100001400003510f0141050201d0740350301c02c81485078040d81000c1e03400822590704c1d96501c4c1030191070750243c031b441922180104566564900e0159 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 339158776 1250 339157526 339157529
    0x30d030b011b03050a050304110904240501080a030c17120a0507050304030f081b0412060b0607110607060b0d12030e160509040305070b070e10090b22090e03070b0a0204 74
    0x142c41391450174001a80444031640000e2044400000c00c1001240710346407001c0191187d1700c01c50a000100c050481c400400c2070000c0c41a07086607003448018031404c100070a103120007035854186201c0081d41d80c50081c81d035845808250151500101e0040e03004030729010340a00406a41c2d00411950b1100001200c035403004030340c050301080300c500000b02001e10401000f030303002c003084084040121040040d040c10350b2060f4025101c040300701c0140001c0c0301c001c0c8621182c03401c0c2181c03c14070f08440c1ea80d464245480c0341d031100b4403498020a0800502c42d00c4e420125000200810014000a0a01d060030707106200c001e00b40700003440e10780484102800080d120190000040d1700041c03086c80c01c1c0c204642160010412010400c060000c100020070007004030b8000c0c240c0381c8507074a148000c2814088c250001030807050401c21724a40070061880c0440c00c4a070780b403417224a41c1003001c0d5800c1100080030b040c4e6003c40c5156181003203203c1c0c05803011010b403030114440c601c4881662100c041c0501607001d0f9 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 339160026 1250 339158776 339158783
    0x4110f030c01081929010201051b0f1b01020a09060207060509040207060f020c0f01151203110a080c0106050f04060305030301061d090a09030e1909090f02030d030b011b 74
    0x1982501d40107601645489a00010552407581d281e55403810440aa80442489800079a05604d4492a41034200381441c1003410a20080120b49400310000e5040400641c0c980303c1228001110014400c4010403540801040c403508103159406024086c000e6204601c4c000000b140c0031804125280b0206000b0100c03000342e56560305004005003000000e6000500c103c071541d94420301d0310012111400900344401801002d00b1150300010300e05801d44640c14004c1c800d0301481e960500031107628081507110690103250a4040c0014001d8003460640b0098001e0000e42c80400d243c8100700054015030107503042a1528203424001c042808142c0d60341380002440c0750000e20052200a1007485180f0816412883d203084154102021802401c0c007030701c10a02081c1c480712150207158022404515100c010744003641c07401c40200000c1c00c2d031b120600560b00e040b42c03159660000d0203800c1e10141c00c090740040030344203c40324402c0058002e01114190301d0229182014804003001e4080c05030490541 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 339161276 1250 339160026 339160033
    0x109120f03050c1b010b2e0e0d060203060121020a091403101e09050303060901140a05040b0307050a080607030e0f07030b180a03020a060510031109070c0b090604110f03 74
    0x103d0751390440740b0b07040f2600c29010765940140498513950040310440d9043c0071414000381480102e42d52425901440481090000070a503071021354407402c80c801003080d0071000060300c0f5203071280102c41011031030042441403101c00c0105101030b4455801082a41801c2d2269003104c0da80d04440b400c800e840140b115451f0300424a00d8840da1400e8018080310489802c030480c0d0030004915500403107043c01c82c01da6041d03201000300412403d0503668180980700410203800320310000e0b40001c00340c8029005581c0070b662100d19000301d946080146130b004e010b0040040e012181c46003080d55640e50215140300010703080481d50307150b8079808a240941100008007810790a4190303100c468507410054244244109540d0000c141c3d050180400d081461099003c0c044041c0380e41084070a458016100601c00142524200009081c40001488002050f2100c564950b215182980c1180c0c107101c0c00303442c080d240401c11404000115940c0e1266124a4408220481c2303001402002e03c0080d01050b010350 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 339162526 1250 339161276 339161287
    0xc0801032a060314010b030402220209041d0c090603071e0f0b12071803021212130611011a090603010605040f1e0203071b050f0109120f03050c 63
    0x41c0c1200802084400020350288241d080c4a01212040700700d03403001d400039548940003801d4180d0034424030300410410143c1c600394201600040c0d0302c1c921b245a14000c3c1030041e410402c2001310381d0152038003400018000c007c001017420313044001c078060041940c072500803aa84500a0700d03282d21540e004150250040418604040000d0116010400410303482c018403100010a54000d8802c1c6015021101c86503450f5502d50154044c80d420207001081400340d100044000c15600d601010100c94040700c20082100000000606003401440c0d60010f0020001e9181c204801114902044a145a07104005d08003559031260803160f000182d049000d51800322030314603280c460341142c1c0001004000007181503030795000900700ca80d02c0c00e0903035426480d130301c618081d0f071000e08000000303d0720902c0541c514900300300004c00501488400005e001036070403100c001d00804102001583d968600208035038040741c00c04042106508035070000203602c2c1d41020010501c03e00465019408100d1600c0c20070 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 339163776 1250 339162526 339162533
    0xe1c060f0603110d0606030c090603210516060207020d0f0b150609010305090c0301060807050a14060301120c0e2403151b0d1b0207060c0b150a0902070312050603010c080103 76
    0x98900400507076105d0303100c40d0040301090b40d480c0e11a005180d483c000280e900d10358038024139040d00204506080102240300a81c080e40c03c0b0003100c480300000200d5580442e15071400600900801c40040d40001300010030f202042198604440c41c24042c41000841c1e03910800d0b0034404450389500d5039041070061160318842d50098010a070032a00000a80b06403900020120b42140c0b49070340116000c0d4405c1d407003000b06041140d11107000e032025134145401594080f0101d800c62206220301d290080e94028504140030803c035008025209071041e00d41c1d1420003045440c030b1602c0746407d01c1c0340340c404100100c2d40362500250303d80c009180920740301429501c1e854040d200080c20441e2a003258020485142c1003040e40c4076070340050f00d586c000c04801007a0301d00c0081c80c0c01c065400c1383d07061119851440340440c407001d0149520686041d150b01003180f42d40049031203912261300c03080003640017007449010580c1224180566082144c0200160b64541080600fa15004100440030440041c01071020 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 339165026 1250 339163776 339163789
    0x70c08010b0a2108040302091015050405060f160c060201050402010e0d02220e01022722051b040902070219151407140303010e01080c011b030e1c060f060311 69
    0x4140135054041c1410390760340206140e100d044a511400b1400040e090009281266000319840d00918115090074181800f0800c2da02c1500d082e120724081c08103031840e114200c41ca08001503940b000c15540403541d1500d002c0e01030001520102c2c04074030401900d0000e420300c0300d80015103c4d0010700131442c075401e0350700f000c03282c0c0c4107032240803001c60f00c1e0030150040c0b000034001810800e050002c0410384190111244080454400206100380f008400e81c0e0381400c8503101d0380d002c840822400241075102c90706182401104030525028000300032030300003445a016801b0b0305001c3d00954900814403018083d80d99481c1c0c1c02c2c01081000d0340395007410030025101c3d000d210081501140490b1610341641c9520961856440344a1380765400000140000343c8500340f0744e401055000c0c020a00109940000380108180e104c9091846030700c500a80e040c144a40d0a00b04061400b03002c4241030307209200201082c0610b030758261103580c28455003d0f01f100d25440b42600302ea40104c4411562403880d01000310 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 339166276 1250 339165026 339165089
    0x50d0203070f0b0a110c0a05060604050606120705130609080c12190807061a030d0201061208030618070e0a0e040b0a0e03070602120f01080a150e1002070c08010b0a 72
    0x4c0315034490302c2003101801c4400920100ca0503800400042841d0b14003d4503080004203400d010b1410b2005110b1603451303040540302d51010040100c14140d640e14800c8845000b00c02c0f611104001c1040c000a071182c000c040c8809a03001b510940f6250203440c410b006200282c0840c0001030f600c2084c0c20514a401e89200ca40b040e03104002640c60305505807074a10949540c0903440c99080b20b0126540f820f890108424442d0035000d000034011203152219800b40c000040c0c2019169680000000f4455500c10050000200040d070054807242040c2000800b8140041049401089101808944056440d031441e00c907940c0b000005c0e410340d46401841c00034200448000e81544014841440056901d0014003900c0d020115100000c0c5040c011112480906130302c00f0107580c11445150000c9484040c910106d40325021010036130500e0050003501d400d8064601c42c00c0a0b1000ca140c508005505224204480c3e80724001d101100004082200c460894460324190b60800300c02205240070042c1d0095 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 339167526 1250 339166276 339166291
    0x101b0b13020a0305010c02060f0c07060f110c0a0c0807030b0a0f020c15040303180b0f06030705150318190f0201120f020d05180c010804020d05031303050d0203070f0b 73
    0x40203000603901045000003190411500ba0b5104c2104d01200e03a81000700f10341c000c1001c174601203542072814600c40380c7e00c1600d0300a003030703d5180d80e100c00041840e90060104a2403803000603a490020000701070f160980e508044442400b0401c0c009940c886c00200d100c280c030303000300710840a500e54840040091070f600c0c00b2280469020b00c4004520402403111034401e5451118501d50f9183c01e01c0e0040449140e003450090300c1c900100b00310081403400400b00c2d840340210074407040d030307440d03100000749000da80d0791000d5480009190201d01a02090b00a0342c02030034500540e90013501d461131501d0f190210500301d032012034072a000f0f48000c80e102c002110b01160040c1480000c4a599445c00f00c156140ca102d008501a00041c45d081048500d11071300398000d140000700750b08408490300d07041d100c00400c40c1080c10860719202140540d0b464200c41082298080200e966800040e03016001d0395200d0f1105441500070481c0f8410f03c240003008130740600e0b92151444030400c039242e0f0341c0003050501034400f4 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 339168776 1250 339167526 339167551
    0x105150105043b090606060a0503060103151a041403030304120516080406090503160501080c0904020d06080604032d110c0901081006060302091305040512030f06101b0b 74
    0x2811807104081c09280001d100311844075140c5004000135284c624003812040c000e00007046651490b035840360583c0e4210409180200d03122030301c5010600000c41c1d9070481e030b10700102c070640401c400e00808010700440c1c14956406d20b5112141c0205912400212006820710160181050f142c900c40d034010180d450100b040e0341003511060b16101381c190810341004022440d40002800b052408001249100c40340d0706d01d1070500c50400b03000030500800a011000e1152010501d0b000541d06c0d0740644100b905c04034800c00070ba56458541a940300015601070700418015280011800d003084852820f240448142c02c5a0b200845011594000c4054a401c103600524603800343d50354890600c0c500030a8428024000940302848a0007100d41945c8090149841040065600e484000e00150015051803000506d555903003002d6017090907a07841800360450000422941d24400e080d180c0c041c950588169052400805003034030510420640b2103041030070030f0460b2000500090300160301c42d2598804 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 339170026 1250 339168776 339168839
    0x3050706140708090a0507210807050109020a0e010b040e2e0501031d070302040b0d12080a0b0d0f140c0303072d02010c06020c0a0f080309010515010504 67
    0x8140c21500c1589003510201051400d006000c0da111842641210b500000703015441c5403a070340d040c6c0d1118584038607215140307480702c0a00789600d600081d000c1541c002c5030041d178440d00340c0791860082c400c414049205021001e804102c0740900990581614a6151203501d01800c0c003641c0d4000d504000e100f0040f0040780004448034a4407108400c0c000d41fa0580c1280d1100d00b00307c00501500e42103090b09001500d03003041031081850000c1e50000b04c91701504c00140b03114506001c61041c0303290204c09412101c00285001c032050b40958043d100f00882c0070100318500e00507007082440c4240020140841030704140080c0403d03082901100901c20503803c607801079260078042400c64205060a40e01c4441c680d10813051103007030301c080c0c038040800c0344080c031013100266002070416210104083c0c40c03076901054565141c0c000308810540140c00004001c14000d03103140645903540100d5194500d5401c0002243e1a07200c194142c1c0c03003181e4141c48050526081410564134a800b5005001d50141426034 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 339171276 1250 339170026 339170033
    0x1202061611040207080316050a090b0d06170d03180206040308031324060801051b0a032702030d080411060a0905040e060402091308071103010b032a04050603030403030804030507 78
    0xc08000b44141e21761503c2e4904140d5080b20381c00040d00c2e407014044100028240c065002080c6001c0d50100107070b841d12010500034142c010b003102e40161001e44000c0058150066002442d0a08420140d134244520942c0540002458052410007504094240b00c1400017520440285910aa00c4030348135181c012151030700d104c0422842a01e54840020901c40f0b40034070268050b000c0941101e400034041401d1184196220704040200d40344005008540d42c604980310340c200c05290400541ca031070400f0040021440a101c603028200d00c2417191200360f48a26009004551107a42c0103405002030710401402d00c03041da40118043c10030072030440070229031a9503503c0303058410150039005240c41d00d8544107005442c0c40c0a0080c180100100c000c2a000691910444034100d070b1090b081140c0100d2500820701419180c03012551501601051415456a0060f01700d0a81604090300d03498035400300901085030300c213a400c4d6400d5041001b050003c0381c041d00d040798009101e4034007546800200c1c1c5 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 339172526 1250 339171276 339171281
    0x70e01050c0601030803010f08030f0304120c53091c08040806070915030f09021002060a0507051804200304050c030606040509031b07050a080c0406120206161104 71
    0x70000c5903041c00106c014802c80c04200c0c2902c029040700c0c40110300d402c1c407022962429000c0140010a500d91100d004103019105020440400e035200741d180c070140310440007003041d0300756040340c10380f4a502222030070080d501d08410219200240391070140890b41e0352030700c00c0b1003540203000c0550030140104480c0d14140c00d500d02107110b1400780c6401c5403964200360816007401c5014107103c007009040d00d828402003080c4aa01c03280c03415141030010780110714075068000b4000c035540103903020711444003c151a0b9008104580318880805041159640d07800c01074605000301d9200240f4000c5209112030341d802c1c984e00c4540d050000340607441e1280c100040700c40c1150f1003120212030681240d440d4441c0c904080044603000743d0121000d01140c03401d850160382e02e00038000d88a120400da0356079a118400148945d1025160103400302c03444540350726413240d45254107030f00a40501d1400c0400903500241c0f500c003506055005203c0c515141030002c03c62054100b03060103407000c07003d103039191079559900d1 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 339173776 1250 339172526 339172529
    0x3080601182d050118090f060b27091e040c0f0b0703021209130510260606030c010801290a09080c01080402060a1d03070e1815070e01050c0601 63
    0x140800d940c2c5a4201c1e814a8145080c0e21103410b0041032009849408503961008003544c18002000400b00344540d0201c0140025a002400c40200010350f00165001015162007920b0440286059080c0c140c09000c41c0b004202c4c1c2030b000021103562020030340c41c01000a65006801802a2640d00362245802281803c5030340c0403130001c410004da041c0c101a0140070048072a01c1c00a82d0b1030130440c0d00804900d081228140480c81181e1b01d50024911031510035000e00a09641c40750719285401030712441038204050805c1010902c26200014164600040c0c4d40e800924180d4440006903e415003514001742c000c28840f80200842d800d180c80440283c0280148100955607090864640000d4504143e003551003d0f0410076000c08000141e2103c0301112680340051a0114903039110204243c180320702c042d6200c0d03150003120b1002420082400a881c0103900034003401e42d101510601880e91a8115511003030103e00030703000901458003a01004403903101c18100585454110702c05175040c031209 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 339175026 1250 339173776 339173819
    0x90f0709020705010e24011e2d06030b130905030708070c0b0a0c1a1b1602040e0304030512031501030c140304032304060210050705070f0b0708060603040308060118 72
    0x6d0025a500152040ca90b60300600d081ca91a00c6207a205244410944541c1d00550007980c1041c646243c801400300701e9880300401c428014041203448000007000b40c4590f02c8100d2048100c030008a021040c6442124610b540c000c00461819007190344450040c0c0007424162204108584001002c082440080505041c0303691011840a41b40c0307051038429501540c000c081425000c1005121078043d52141455074102c901d1586600c2c030b201c0345245507100104029081820407a202079042c000001600949104105503007501225854018050200702c6036001030b0115412000701a500a602c82e50500d582880c1c001804c0b90302e001c0450040d032040c0d03400c60014900340807a1119100380040d1504120051004c1840d041ca010350003503481d06c41903091040c0e69580c00100e41c1260144003120221903000c00700c1415980c40f406d022541c4501159203401040b10300d00002e00c945070440450f449294191141200c9880304801102c2d0582c7c2910740ca8080300c800d4402088542c2c00e01d01c0d03003041811 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 339176276 1250 339175026 339175063
    0x50f0d1a04022d0417010c17040320160f050a1d0a020f04091404030e1c0311030c0f150c090d0605091002040f080c040c090515071a010e090f0709020705010e 69
    0x1582c020300c0f0030700801d804d0008d95000300500000a502c07024807000d084060038590b44c881e28440740d0900340344141d4641d40e40704800b0b9800045440c600d40e01181194400c48889215039034070040040c2070421440c654044907a5070b800078821394101ea019248510701608d110f03017020b840d45c441d41d0845010f19801c0703000360102c6003001b08240e40480c0100d2283d409a0b50185042d40d22102e401c001615680c006041c072540c01e4041c0205002003065525001a040c03c0752561040c684807d070f200d60a5a20502600c1099000145622213100484040c0040039020201d024010707200d40b801040094045800390103848130070700055103a400a0400b4201c0c01c0c2d5842806413500342020f24084107104920b0060703080410040e0709a803c031186a08440381515850842c84050307400403907500c01c80c5402020b091000041540c4035507100b4100e4160b952003900c0c80215110651040c1d5258003c0c0301031842544240414410704146401516800f4464000458800c0070b00402904096031440b0506400c0c4 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 339177526 1250 339176276 339176291
    0xe031c0e0604210c02031903020f060c0310060203160b0403260603010b030c0a0e0712090c0e0a14070f050f0d050a05132001050f0d1a04022d041701 65
    0xf03c42e51460301c840991400c10540c0340006a02280e1140c40d0602c40c004110b43c41e0340034800340350080c04a020a00040f906171004c1d490280b2824855402c142c4160101c0c0f030340c0800116901e80000112a440300400d05200c40800503656100c0004c800104124200941000802c5007030902400001001800c04000b0802d440c5c03807802d2608444800711a684240d218144407060341d111651484207603241e162078a541942c521109507408840d46074400011441d00e07000e8401d000c5010140310580e1b140340340d082d5417502c0e60200070050f2a6517845410040f0031200c0460307240d50144108034000700b050f040060914906400c00c0ea215081303040030100c0d00303881c0c0c406c0000327594440c130406030b05c40e8081c0f240c184001010b4591580208004810006403203002c191002280c3c05101075400c0707002d0500055641e4207011501c40081c240d80c22088030850410481015103161174000d55080020b1114965244004008a009050b0000c6e840d10f4241030708100108400c00409490740040104400201c1c47e213 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 339178776 1250 339177526 339177563
    0xf0c020a0b060f0f270703020304060b010801060503150109081b0901120f030819020d1b032304020609030a0302030a1403040812150405090c0111010e031c0e0604 71
    0x840008003490311030300e400300c00030b03101d40c4d00c0440007007203400185c6900c2200c2802c045800700418640c0240c42c0c06141c1c1000308402c031030341500118887e0780304a409101100404005541165003801582c000c1075003440040c00008030000359002c4654149042c55070b40e55600112400c101c00340704d4030760400550307404440d55814407140707043c0100803016000900b0003454541810400240000804000012010844c010010140c0c102c030260612811543c80b800c1c031000c0001011819040d0488046031070307211502502034400d91128601e125882a00d0a452031850403948030000c004a078452011300c2030302c00c1601c040006035081c500c40d0b00103543e00d1041a00c05480641610015111301004004000000784604191900620603010420305911902da095a25500303011841e50003a1410040080c6000005040403105000380c03030b001206a592101e0394242d480c245260500703607004002002000c8008076015001076404107001400041008145061940555055408003070b843c0c001041c4 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 339180026 1250 339178776 339178793
    0xc090a051b04090f05011a1209070e1602010b1f0c0206070b090102040e10030c030b0a0e010e012c0d0e0303132603030702060c18060f030403180305060a0c030f0c020a 73
    0x1f42039804030020406100610050291107480c44d000ca00d2006580411464141001204060940e000d04401d280c5400c1d02542d0300c3e0124911000019820103025500d41d01f07007500d048003010030310f0381800e20100c15820166007044100000300d0700b02504000c11004602101c904500400c02e607400541d5a40c50300031030000ca02400740807091800104902000040c0760480c0c038404995208000708101e5940f420210002c207200030f00032645502b8000c1c015070948066000980e40424102221101c081c0c110343d0096865291810516681c055901110740074003c050000300a90b0084c112460300c82c0d6285600501c40d92580441c41c003400c200c01000007410070303142182078451900011821490203500081da94030000d4105860b101000517090841e48441c1441800ca17003020b060075540d50054000130206a108403010303800a04051a800d218200c044920811283c20600820907500e0306a000401004084c5040c0b05240e5901c00290385060b0500900c0c52000d402d80182c000c031026420003040 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 339181276 1250 339180026 339180029
    0x160e0307060c110406080a0b0601030f090b010b07060e0304170607030207120f02030d0903050d2d0e070f03030e18060109060302090a0509040b0a0e0c090a051b04090f0501 75
    0x46604680410720155510015001449420400e2280c3c070701c8540340420001d100030b4008148070300480d4145c600b0700c080024001e000d030f9800c0e602000a4900400704404a50b5882c130028100c441d020010007546801c113000d458400d014400005076440d1104a0914542c0a91300c449411040b0b0b0180c081c103140f007406241d031700c038010703003801c0d854102d059503685420180a6a52030038480c40d048001007080c4200b090710401e0031a44001c00440483c0d040140ca246c01c4600d40c2d000180c00c1c140802c065401001018500c10002600ca40035840c00719400400741c10b200100b0a02031141100000d0b065a030002e10705e00560182d200c1c1e4004034000800d1165080c0e420032035006440e05042480041d9900407601012500240340050325251007400254604015a001541c09400d0106000038881001003241c050403c64070101700151301240000d88450f44807810981c00080f040004600b0803840d00004c0d800072000c1c42e40c2d1130f4804545420401d541098000c42100d40e44c1e0500c000901501e03208150 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 339182526 1250 339181276 339181279
    0x1b100b01030908040501080907030b090c030709090305040308031b0706050a0c0903030e1c05010c081008150103080c0c030f0d0e03070f050d0309170d090608061302160506160e 77
    0x71041110743c4502c400303440b96200707850421900000040c1b1445081c41550050365000580306d0f9681840b100107a990035449000d0f41c400d014486000901d80201d104120009034140c44140c10140307151a50300060f04003c00001c101603d903000507404481d100002c103501c2e0702c04e0900041d14145116403030120780b03140281009028010f1000d002117600003000d00210380003102c50000c1100381140000d109202414010701035820302445001640c2c0000103948907075048030303c0d908020303619034400380d41d280041d00e8804590780c04030050000c1400c3da00202540000f800842d40d1690604002c07a1070302c1000c925141c00b5420503001c4c03402c101e900816903105940d0460080005505080b102d803081001482600d1140d90211100c20425001e5200b000c024103140102e40d042c5c201d201072503500c0703001c95084000020304280001c96070a020b007041034001c0c500075041003228020595500001c1d40f001d110940b25051040000e00061410080e041c441d443d1846084440728141102805c105840000746 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 339183776 1250 339182526 339182531
    0x1052b05010902120c0c01020c0105010320010206041e0809060a0e010e03071404091b030b0703110a0507020d050c1512010e0412030c0c120c15050705120603031b100b0103 75
    0x12111321003140a40e504108503003859540c5880996207240280f05807a410a1203508040002091001c0c2d241c0130801c10401e40e01a802e0325220700012078640c10200c50082a031445041002004002161901c008500c14804103103410210000903015401103503210001a40704408483c165038000344192420302c6c19001005041d0030f2120ba0902c01c40110400d0707000e5560358001c0e405100809115580300d884a5404040a40c0c99040881407100202d40741d90100c1d05084042c0040e001150455000303151995810703042031242ea08002c81c80c94008400d50f0940b207003184c001e4132903450800000e454001220380682e1a4041a030009850a0590054240b400014104030109541d044c90020030104c03882c0c006581c07401d84e5001d44141074000c030060100340f06035209000040e04030344042011801001340c001d00500b131440200c117035803080f5120b10002d80107218003807040314007070503003604503400506880c01e000942d081c01440c40342e501a511000d52200982c0021100540714500505d103003032805 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 339185026 1250 339183776 339183787
    0xe0705031002072604080f030301030b0403051b030c011e05040c05130f020a111005100513022701090e010b03010b0a030209030115050f06130b0901052b05010902 71
    0x2944a52079000041041c0760005000340821a4498060b030200450240100b868141c90210142d541c00501510341e040c8600705615086600000a8a040703135031000c0e201c01c150b07449617030484807038000006180f000890010301504803c8240080c00c2c0d0000f00700c0000900c2c50b10048000310300c004801400e081c040c035203018440031072041e14414081d6801038402c0c0070201201030282009101c40151200018030106003d078265901100002144400b50101c480104c43c0c88034200444100307a0301642c3c3c12400313043c20022424000380441d00b0383d030f010b0801801e02040c0328000c4000703600114501107039100c04045100c02c1d07030454070300e00281c11900c980c11410342c10000c50000d90710060090610000011070402c4106110b5011149403007406002170098590040b248102da00a034003449104864810340d0000b40c3c00c002d4241c40d28880d111000303090862501e0014090743e405500b200d810040200022200c521a5000145805404030003e2041121001d0008100d92040e00b0685c0240d004010 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 339186276 1250 339185026 339185029
    0xe0c0603040c061b0605040501060905180a11060c070305060103030923010e060910030501141005090607140609070e0a020a1e03150e04050606031f05070c0c08010f0e0705 75
    0x3182e041d2801070501e80110502544098041c04c0e0190008001600b0003040204004044d00440101d40c00d4000c18071141e103072420311100b40d5942401045490307200208201c08900070a41300a104c0c3e6019200c40c2c90b208811260354140344041e002a101c40c0c1c401c0e40100205540500450b00900d0403418104a690558200791020218804d1050421010142201c403a130b69950441e00350300401028103a21041e80e00c0c0203030181c00c0900c00c600c01391a45031541640780c00e100d68000e084126958405241c0120101008000e801104064415240c040041442d0040400c00280100c10030001480b903d41342040190700c4103401001600824018800300c41712540140c0c1e011054400c0341c1c461f9102e103071100000c074014103100072240f0301c03000c604800241070a598080107003c1c602030000e0392100c0d0344040c1410b0382c4000c1c1c8407e041e10460518120319010380558070031600300032245040e969800072034448454544480c0c001800740d941d503003040d60034000e03148100e40d040c04089002e1300c0c0580c605130 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 339187526 1250 339186276 339186293
    0x21209011506050702210115080c0604030201081302090106050712021f050702010e060106050909060d020a03080a0e0303120a050610080a0e100c080601020709111602030309040c030e0c060304 84
    0x2040b04103200010411204550311303022100801804006100b07403011412080c14041c1c800d0700c0b05d5004070070900002089020010800b00c4070548080e00d407500c0e2514580c01100d54010017401ca4010a40c02c001001c0142e41c0c02404174000c1100355269522118281405208a80c0c110484010b40d44904081c2056207000c540b91040307002c5403480014140d4038410164054480300322042c466001c1c250001c580389400c03002802a079101900c8d01c000c103554240510240044010000e980000240010000142501c1c02002558100d140490710400d41d140070a00d1a00620381928481800004010054006200e06035205904450301d154172186440302422046015050740b030265101d0041013082502000042048400341e60300300100324078030307800402c11041a41c0e00340c014054400005105007540c003981d42201404c9042c2e614020000041c45020207034520200c3e05808203109c0f8818564551082c070642c40001d0704d022400c0b040d2442c04d682841480d003001482000188184404101c448 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 339188776 1250 339187526 339187529
    0x70207090207031b0803180f0c060a1103070309150516020103150e01030b0a050f04031b03031112040b010b27030304050d11010e060720010306180212090115 69
    0xa100140e58108500b81201c81c104020342012030000c4d160307201d00c1000f01e004011403203500072141002c2e0540100c100d450310364101081c02d01082d80020007841c41890040c0003480341b4000c500345003e000c40c00104250940c0c00c248020740104200c0700c1e080040c030050444000ca2003040c1e05d042d618003076140c0f00074542071f0f210f64030281c1010f40c0d81a00350785c02d958040340c01000e405841030200c095a03480c03038aa000c89074211103240c0101d0800c2c000c02c000e5008490f1131405140e01d503c400340c0100c031220341f02906883c207031001e40c1015111100020310b103200750020a08881c00d1080b5840628090518640120040c1d00040c2640f600300180c000c1031404050441d280580c07408496202028800080d10b9401180c00060740480205c1020b01084043c600380061000c00383c80d42c1310300d140e40c1e00400117540074150b40507194100c41501c0804454909403031144411050400080c1c090b102d014102a4907444014102c0d420740c0043c86149d0827100600035680140c51700000d002c05481d0704030a110203400d030f = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 339190026 1250 339188776 339188789
    0x20f070f02131404110a06020709050c0f0703030e012403060b030a1a07021c08010e060d050f0f120405061603141201050907022b03140403031409010203070207 70
    0x140c20380c032411503a4074442c0107070400c80030b6001e0104001d40f0000050000040d2070444040e240848000c49a0810400b000d0850344160068065646019601e5018182c01400000703201020019000302101000150940034020340c1c001400c11a00c039511401c55a00410454070719540001d900f00d08481d401d58902926401100410100108000303e46040f66824001302144241c112090440f0b0143ca9111b11800580e0b0844d20312590480704c10358455440300001000400500042c001408002c03c1c4c02d400080181c0804106116030b101e407030038500c884003014000e420228019102d50010041818080341c50700c89a4a0149000e0026149104800400001050304030580f414503000781a0040310503a4550801d588031200c410a4403d80000d0140c0d600c40c01d60103020401d0b442c070010310240c81405140c900c407011500c200f901d050219904410500300b6458920b850006016050020702403440b036180891000540c155900c42880024102c003516031041c4200a401a4002070b4001114403 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 339191276 1250 339190026 339190043
    0xc0f02100b060d0e0f01020d09021302040803070303020c0a0203060f0a060e090304030f020310050a050412020a030c0b09030904290111060606091201020c0703050115030c0b0327060a0f020f07 84
    0x26004c074141400c8500c0790819040d4400f049049420b100d603041030000e544200d68030b2174595540ca10030403c81c090b50280001d00d40c424861040000d0082d8010301140e07030684100c840115071075001901d000021203422800c01070341d0b0113024481e0000c0c081c00014082c01184182103248c003a8040742d59008500c4083c2030700380162200340942d1001d000d801003141c4000002c0c800c5240803101e40e1301501c0291411200d5420b02d00c0b000c02d00301e00c042940100d06500d981c4002494015403a9002000c0b0050400c2d000b5000801042800c2d60701d80c030400481c860101c1e00c491620841d040d1440c1095900d032040da0500c1826420174140101c0402d00c0741c1d010104448258a07003400c0030100b02078840400d102201d562000522203882400061080c00300c910030310007030040060300b030400d003030038400c0d480020490341c40240248803c0030040c014544c00860145240568201c141d5448050040894440130640200d0144088182a405a14148e880c01d000a501c0c1804040c0c42000c3c0340310321500a00b8a81c0c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 339192526 1250 339191276 339191291
    0x507080d06050604031b060e06070204050c160609050f06091c0302040b04140301060f05060a080c1216080106020111031303020a0605160809010b03060402220c0f02100b060d 76
    0x3030041e48124054007015001d580c54588a1a0080c4159061104e01e40301172100f5100190031031282c0c00040e10340802601c0e040c04d000d12a42484040c0c10003400350410014140401c442d42000c0712103001c407480c05040041180900c9060043c1404480c0b481043c080d0040c004100302c5100004260f80701710329010090030b8002c5080c000303c0080c0182d4225544515002400042135040d2407107510310303040202c00800420340e07508410074010160b44522a0801c80500100400b14001c001d41688103092039415491320441c2560311103d49000c0b11210841007961400f05000707688616081d0240209000030880700c0b40c003000a42c52400300411918194550120200805200f0f0050700320b00c0e94001000c0c080e500342000784400c416404d41040f00068000300020b0840384d0140070f001c04501000d009402c41792195000d00820101659141c041a10590a45040c030b20380341c440c040031481d0990b40d00c2c084201840000382407846c1030490000c014101145256946ea5442c121010720214010020b00007 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 339193776 1250 339192526 339192547
    0x30a1e0303060f12060e0601180e0c1c0b0f0601090e1e0f060310020f030a0c05130803030105100c05070623131e031203150939050708 59
    0xc1c02c80342c11052004900740310025400302c040d20702803495445100f0512a034074941031074503600c1702e003489000c2d51000c0c120011070a1760b40c55400003068043c1c000079100c4803041c804c0402c900c1c0038141e0201d1040b2510a0710101806260a0543d42011340c82c1c5002c4400c0c1013103030009107140820702413001400600001301c2d400c0421021030181329151040010303158500312084e2030401d8811104070780130307004c2c01d00ea50100e01418401c80b0551000341000d6400d54641c2e1821030000c4c1100710f06082446010030140a0040080703070140300401c920b400443c0e4942c104801e003e00401201c2d40607050140100c015400135030301050381d00c10340740d5a1030010700d89100d610018091894800381c03004007e400240d22080302281c418a40240ea1a20550303000d08030007821542e20144e018480a002140c14400000301c045c8a500030300c0070780200c402580c08240c0c440d111102250ba22200240225140811045440705208044003441c01404141c5060202c07442010300107104010004046417400904600f00 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 339195026 1250 339193776 339193781
    0x31120b0c07020d05010c0801080708030d0c020a0c1e17060f0705130801270c0b0304050a02040f0510080102090a090e100509060406050c03310501020a09090b030a1e0303 74
    0x141d0303002003940502d00180e041c00d90080c003610044100050b207150011800190000b0900203c6403d00004e5141c110b01210040087c00150300e00d0045004071096000480c51000000014141d521000500c03182d10b001080380c0451560b01c098030400415000e03400703120b80071400552042080c0680c0d01c07035548000c4200c1c0e191181200c00c02c040300400768082501c4205600802829048131240340070003041080b0003c410040d018000e00d50544104107012820980e4003840c0c1041c0300313104890a41d201e543c00241903071945084503443c01d03940d004102010404c400c1c1c1000821144008510f0800000302054070440e0034001c114400352a50003000c00848100000c00c0906503100040001d4101488819224042550150340d41c07030600c00414610b0b051002224052407001c3d0f080f020f0a800081402d0503900003255140d41a203480f612a00403134000c1c0000d20040480f541d0f07141c4003a09212144040b41c01c1003030b12074000d034000e001100c00a1030241c0f1844d502014031460000c00d11072858214007 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 339196276 1250 339195026 339195037
    0x5190b18011404060e2211040f2901051812060103051c080f0615190f1731150b0906010219022431120b0c 47
    0x4045040c00005404008a0300075100c80001c48050240c4caa0701c582030601c0c100c1c00c0e20510740c000d10800703070104203030284a0841949481004040d14862507100010b0484005084217115551902d20b1000302142900d20b0440340e480304006070482481180009006020f03080503000d188031241c945210a68504194298403010300040f20459a160315246071281c00d280c03901c0c14001d000405500c1064010a195481040072501c04202556840708015817040c03400888808070408110490b400300741d0b41c051030594a00c988645200b404074200090801c9602001720034015041c01c1400011a0942c0b10208160441b40708101c0e5042c10016042400d506010b00600c1c58007031465840c1035422036005414102e1049481d40403940c0d81400590704e5000c0c83c6c4c1005094603050000d08010314240c09032003201071810740ca228003910000007c10780c40d404080420362100c07120b00c00b50b02003200c203801d51142d0740682d00c521228030307e0b000803100d03000040000145040407100c00203883d900003030103645 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 339197526 1250 339196276 339196309
    0x9010b030f070608101a03060409060e06070801060203040315090c0f1503180201020d12020d091a01060906120c050712080609010e06030c010c0611040303090906050405190b 76
    0x1c503529040c1c22400d903a104940f05003408980c402d000038204441d0010148101c84000000404440c92204040800d60006042e15401682c4058041c00b080030361203498049603085000700000d0a2800d409454050140d020200b10762040005100140c04a08251a0421005000300350202d10f40742c6401030031142c0e006017640854020001845e103016604aa040304c900352420408510701c43c141010b080c20590000c3e01680c0300c0100000c19034802d40310b030b9400019448006048c01c40c503002d10425208113072016920b8600003402400c9004413504150b0040016081c14140b00e450200c0c09041110a8502004c0343c50791540344005450080003111002070740100100c0d424903074800050000842a5a410700900c03202c00045030000d0b540244034000d020040040c90160712200044461b8070700f5000403034105850b6140090540d4190700030703101a501c00c1d00c0f2400d9085c100860542102c0155202078410341c10041440b15201c8000003d215a000c1d03603030040703680e803201c43c045904801c8154184 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 339198776 1250 339197526 339197533
    0x62d03030c030d0c030b013f0e060c04030f0210020a120507140c03100b0d080309011409010c050d090809030d03020a020d08060a051210020c01020406030c0f1709010b03 74
    0x1c540351011000b0000603001010401412240307040440c221800e003054540400d881a607818800b0704c008000036025040e5150f1b010700081402a04010b07450540c2c44215a50307240c3c02131032105e0b001400710380d41c018054040d83d070401b4515251200e40c540b408030042d0180c0b1210f400007403c14402e1000300081ca40100c1007007948080e000c0001d05c00d5001d90400e07500d03628280800c511021001c5414103c1d074100070000d08040e841000d407032009101601e1403680c032803401e81490b00004e0308940910310909031303c0300003e80000000d090030042d500041c48010700e07925190241030415084429940741d980717920b80c0060201d40e0fa16020f2681c2c072480d01c001c0e5042c4903c901164604c1c2d8140c0040004074640c0e82911342820300c4400903500f01109580c0140c0c0106081400d02050410a049400032100d030411520500d41d8687c651040380e01000d07110710300382d40005080c84850b42502408402ca45a0b14190902200c1a44014000c0e5070710f200c1c0b054220084404113840040c25000000b2100c40141607 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 339200026 1250 339198776 339198787
    0x5090601020a06051e0604020703120f09050a060b091006050406050a030605091315060803030a0207020d0c140a05090c0d0c02120406021e010504030c0f030306030807080306130203062d0303 83
    0x50955581015170107003500c4c56501c005002c07802c1038001e407070300207034545c132070500c010316012102c00030f409020420b0150554138054900466410006141050300450700081c805211000348034011000918502c1020f8880300d041044030380c01422942221414a042915640c9400044001d010340364012a4003000c0780080c80800040a0341400403940324000c2c0701c680d040d52070f80c0c03a0103540c072078416080c0c03c0d0030a1000030179119060300140315440c0700520a9031540280d035509003600409812401800d03541e520000014144100550003800f8200d6181d0068a0042d4926111b48920301304104190b07111070042e0b261074003c100110301ca0307840c10007950f2141d4a5000c0256a2206041d02140c000c40d03242c001031401d44103108182c06940c050391800e00451950729480100140400c046080540d501c000102060030074001c0c01c1171300d00c20140c09a0f07a00b0018200b1442e074080e0130501c0355441c410000d10206503958054044e2280780600c400c5801030b0921200c454100802c490309800d03000c00141d = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 339201276 1250 339200026 339200041
    0xc0308070314160e0936120d060503011a040902040e03160209180601030308090f061320010504050409171909061103032e030308011d1005090601020a0605 68
    0x5540c550212035510759069130344ca00c04100010740d0507501c14007940340741e241c0502c20449031240b000390f18049009490300e1002e101e1030140740c480709260b600941e42c0e02040100304450a401030a00421007200248002c243c800100c3ea00e51008581c15442255920784000464480d40c2200b07075103103a4101900d0702c0b542600c40390041e2100020040f8402c402c1403001600c80600195865482d11003100200240da0a603501507070a040058240c510500c04c4408a50782c000f400c1180f00d1207200841119215004c1c14905812601c4880e241040c5404440584451a0741c0c00703010344044482c103c4c5d01042010fa1803c00808600b17000003203103030707400d40021005980e04800b140c00340504010b6a44081e40c541e40c0000b1600a107289400c06c0c941c0e081000031500004480103001c442441e02c9031000902410110ba40241e00c1080d03004a001c521584d00401a109015070350070b404071040c0440325540c0c07410810140c084880750245600c905208000305441d03034401c0100ca0300c0c41c1e0b4840e81c1003001d4105180c = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 339202526 1250 339201276 339201301
    0x20d030221010f0f05030307122601080307060c0305071e05071b14150703050310080f100e030f120720070311040c021b12010c0e03010c0507030c0308070314 69
    0x13403464001d2651078002400e043c000121241940c02070841403040c0e095050446519040d12046000011205100c0d8a00005564100d00070504a0000c56641d0038a15142c002c0c0c0d0340342c40c050b800781440c00081043c00c0350409000ca00c03400c64201c801c500790010321030586480c061500040d0942000d841901d5020180a48260984440390007004000710f0881c10050b01c0c00e004c3d580d25118400034071424001a01940145d40c00100300c012441c40300d40c44044061038402030b980c4c00e0000f64011010009042c00034820b411403e1aa00e02551400c840e1414918041c4100c07060a640c82c0d1303c110004031524811901040700e10014030706240150500e200807a62458035000030364211219800100d80d52078240300b0300214032040c0e0054481c9040b40f5400501280140c2c003460380252100410019846086c0f080c0610b4400c141c80b00e0001c01c200805143c00c41301081b003082e0034080100502004030380c001d18003450a50345803410000b6aa0f503410104d02910003203c6030440104400103002c80d008450 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 339203776 1250 339202526 339202529
    0xf070e010e010f261f030309030318050405070507230d11030c070b0c060906061819050705130e010f0b0a05040b0f041401080c0306100e060414010f0201050106020d030221010f 77
    0x42060044000010165844a007003a00c00103000ca441071104000180c003517072f148001000d03500b0054854503620303408070701501e100301c0e44100020300004060007000188200f400383d038651015010007142100040c141c0e20203e0318180b07810300440d8140a1400003080045402444200058450382c40e51980000b5040c0c02034051102d4078024040000e1022000040c09882060020301d00202040e0345040103c00f41400b074207580c4a50400c10104003105041d000f4140101540c0e5280d5075140c55030347d094420404d8a4201f103040b01080310041200c5046841c1c403605441d030201e1419500e400c004000d98051240b50b110b5001d00301c002c103885025144400c098012105030143c0105840e4125004542444003210b070f4100e9200c050020520b6810050140360409034282000d0754520310190000f401070700a50700403040c081100501c040b66507405003601c910101c02c1e0000340001d50406001030340721414410381c00b0805501041092000d603424080e141c101101540c041842c0d40c44039400203d4030410f = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 339205026 1250 339203776 339203791
    0x30906091401020703030c020102011b051305011707050c19081201080a030906050d061d150108040f0209060a0e07020606240304020405101802030f070e010e010f26 72
    0x14650001000c0d07284603524030346060164007425089080d95001d41c0c1d4003a20038800d074115942c03000c00b080400980c1e80030707201800707940c0c0715561a895120701c982002c03005600410704001c00700100000d50a501000250462010b003031080d222200e41c1e0f15180381285420840301e0f00400903040e1000e0000140c000e105d40310000c00c0c03c201a0780c03101002ca507503c0d00b61800400080384040200325540c403e10190101404001d80851569a1850196074450104002ca01900d166905001c0c8032184c40b400880c82c0c540a00301202c60389441d07142c0c60700c0c6040c6161301901481440000400507030f204a03640d406003a481140c4480b600300600000d503685c508030755403030280000c007000d80e05446103209520001d5131105501440e5039207560074040602409810500304c0b00182d580461055580146074648420740a0300503100c0c41c1c40b0760706d1003408070080c00355070071b00c40034400251807a41e1183c148400002c0a007004a00d04035140070441d070412034000300c1070000c1200500c0e00c0103c9150301945000d85030 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 339206276 1250 339205026 339205037
    0x1510060f020a031805040624020d12020f040512030d0501050102061303111207050a150501050a03111201020307020106031704080312100803120612150112020303070609030906 77
    0x488210556410280d5940440560b015401040c0042e20880c4100103902621075200107150361040460181c40d0903801001ca0503c000b1424a107400e00314800f0310000c6441c2c0700820760000d8040c0081e1008070030301d441c281115000941c40350862041070444000f454050030000010048803650794603074004503180b100c21424100000340943c80000c00c0d034011041036080c10300201060f503095803924540d00a44080380644081071110322440c0000d00452402580a00000791661814207100f407683c04621351843e141a0050250342ca03003840410036a90300906080c00b0b514240300003200440c0d00d0040c2d00d803641c000800c0180315507041d000082200d00c40c210703115000c0c51030070981345980200d0190b564194800e00c086524803662b148901d800c251010007a2000350307155203503981103030b1111801403000c0100c03405004403400c010004100604011003d0300c0305585145103074454078410711640f00b41c0400110300ca01903503018401c50340c02d0350b03010604104680040c64040e249031014801c07070300400c8 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 339207526 1250 339206276 339206279
    0x1a060f030a0201020606010e0406120507060801060201060305071208130f180e03030714120906190b0f0613091a01110a0f0f03052710050705030322051510 68
    0x380000c0380d0781841ea050300a08804e94a80f8011121450381d401e916904c242c507480000340310b02d41c59401142c0a402080036104817130400c00d000d40140010b030b01000c21689010800c101241c4e01168071010340e01c1c03010240000c0005030070403041034000c40c01c0301e4400499400340080e410100b013481e401200c04441000c003070761526085500c01c0f282110b00401c005e03081000081c4000e4480d0790008186250b00601c03501780601c04e0228040382e14221403002c042c0e1300003014045100781c5501c0c2000c510300720740024055008503001058080c030303010110740d000d0440411801c20f1030701d910f07814401130405010100041c0c04c030f15200d4402c4c14074a1440c10702150002005402c0000d020500320042d80d000708048a080a071560f40444407251003100f91f04004091010082c841d01c00e2243c4400340707228820000ca16065501002443c000d95410ba41c280082084808001b07031010007560b42c007822420381001c550314244c5004011940c001da00414600420020f0070340c110b6803580043c080c04204e6186040c89 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 339208633 1107 339207526 339207529
    0x9030a08161103030a140c0a02031912290d021f030902040c0e0306101503020f090a0b1312030503010b030709091a01030f05070e19031a060f 62
    0x3294031500048080c0402d82c440176005804147e08500c0e200002c400a541c0348107205d02141c4c1d5030817100401c6802030180003000d5020781d0404040c41010b507500d12021031040640e00211500220550503900307400c01f04803c0d0b64940e13000d0145408005450a04040300c60032050ba04200754698040300700586480c040c4130004c0c81d468845041d4921503400300350505400601000c801c50000300104412011f03103c03040708294490400580c1c902007028042c41c3c0303118004510350443c0005800196123841c6c3c3c001011a02030710301c2c1101d5003036115401e10001428600d0080c0c0080c0c0248014001e0300741440c01141c0003261070910742e250640d13408684003500c9420b03501c8641803d22803021103455816014074103901c0c1040604101c14903140c18083c14000400302854026580c0850b012803110040c912032025640140545541010540450502d607108460580c098080c401c202d0555 = true := by decide +kernel

theorem cover : BRFrame.Cov 339028776 339208633 := by
  have h0 := BRFrame.cov_init 339028776
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339028776 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339028776 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339028776 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339028776 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339028776 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339028776 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339028776 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339028776 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339028776 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339028776 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339028776 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339028776 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339028776 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339028776 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339028776 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339028776 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339028776 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339028776 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339028776 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339028776 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339028776 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339028776 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339028776 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339028776 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339028776 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339028776 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339028776 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339028776 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339028776 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339028776 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339028776 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339028776 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339028776 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339028776 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339028776 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339028776 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339028776 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339028776 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339028776 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339028776 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339028776 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339028776 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339028776 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339028776 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339028776 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339028776 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339028776 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339028776 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339028776 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339028776 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339028776 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339028776 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339028776 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339028776 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339028776 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339028776 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339028776 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339028776 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339028776 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339028776 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339028776 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339028776 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339028776 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339028776 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339028776 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339028776 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339028776 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339028776 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339028776 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339028776 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339028776 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339028776 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339028776 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339028776 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339028776 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339028776 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339028776 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339028776 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339028776 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339028776 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339028776 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339028776 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339028776 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339028776 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339028776 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339028776 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339028776 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339028776 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339028776 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339028776 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339028776 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339028776 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339028776 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339028776 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339028776 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339028776 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339028776 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339028776 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339028776 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339028776 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339028776 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339028776 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339028776 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339028776 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339028776 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339028776 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339028776 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339028776 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339028776 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339028776 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339028776 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339028776 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339028776 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339028776 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339028776 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339028776 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339028776 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339028776 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339028776 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339028776 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339028776 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339028776 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339028776 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339028776 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339028776 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339028776 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339028776 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339028776 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339028776 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339028776 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339028776 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339028776 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339028776 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339028776 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339028776 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339028776 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339028776 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339028776 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339028776 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339028776 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339028776 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339028776 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339028776 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339028776 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 339028776 ≤ n) (h2 : n < 339208633) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
