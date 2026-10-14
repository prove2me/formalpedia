-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3309
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:16:44.120619+00:00
-- url     : https://prove2.me/submissions/d5980ec7-9647-4809-93c4-c8626823e4a3

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 594964028 ≤ n < 595143884 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 594965278 1250 594964028 594964067
    0x105030c040e1f230609301b060d09030e030a0f0501060f15180b0403140f0f1903020a15050712020a0c030309050a0b191a0d1e02040c 59
    0x540c1d5203c00f210a4104134401a040052074a40f4207182c07610b0401031100c55030040200c0348212024203020816121207801300000780326002c0c4105561420040e12a00c0011030089441741c11600003c14003502829032840d01c1103807200b101c1810180100322861940d40d01030200d4407100a2424010300303048035070a058445502c4c21138046220120079840405031525100a45661b85018204668a510441603172581c42201000403c114403080010001136014050403146c410010325600d0500d44060140401075000010090082c00080380084000c050100307a402ca0009a007020383c10420f404a00600c901d500c60190700078070415502c6140074000c6640c658210f101410050310807880b5100c81040030404164296000138402c1e00703c0c152181c4114142c5410384581c2d500e6401c008001d42c5c48240c0728010580507100d25000f407040c081c3c09a5502d910032020b131545404a00b030030401c18401342000da00c0c0c1644602c038146440c58080301c6075024108100540072a10000d22207000358441d101c050 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 594966528 1250 594965278 594965341
    0x40e03131a04060806091b041502072301140d150e060d0b13060605060f0705120702240712030c120b09070806011407050105060a09020c0601050105030c040e 69
    0x2180303504182c0342940e0345600c07514420b07140c03401008240c04004000c2000000085000715503650300074054001400c240308c40001b801005100a42003910f5900f101c01e103207154044589107601c40850780a502d660a09209600403086040c42455100e45c01510064504220400c0c02d5121814050b0003158244041051562290782c1044448008402c02501140c850b801107591200b0b40c4081c0c00c5200d2051a0018600f175541001c112160070603608110401d00120741c40c1c0512030248104c0c400c01c0c02005115203481e079a50b0008407050200c40300b02103c3d54240c0c0d5038804204606089503010707904486101e4009403604030081c0038003400c02e503100018000e4220f4510010081c0100301b0f00c0000280f441400c0c3d50350800031a0b411400a080780e04202842d440031080d01c0c2c1001c003d111030740c000e20000c500f0b4135005090081c0d401c03840d40010000c0388100903040c3c0d00c3c0c402040c1107054030ba0074a02a0707603d841c1c2c2e4400b4905030181e604101e001000c1141032000c401c415907190f80d4401e481d075040384140c = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 594967778 1250 594966528 594966569
    0xa021b120d0c030e100b01270e010e090d05072307060e01030b03070b0d02070c0305010902091303080f042402090a0801110a030c031404111810060509040e0313 70
    0x25150101512002a44020480c0c4803030040c44e00810207191043c545810204184030034507208030410502c0841c100c20030706c2c0509c40304e01c40600e03041c05408602c0400c041c90400c40781ca07980e11110b41c1d41c1142005404941e40b0200400444821130103c0c004035500103e00390b06081580b0360440380304035004500220600712265009000c2e00e07200c000d00134043c0907602d2a04020309070700d9004110040515600300515030010b495070460b00301039402071000141451046c0306204c5030031400303400748100c00c00350a03041002035440f003101d59012a440071240340c1500c1c0c03071800b94a0304600005003c0c00c240020500006810340d42d000d020140c2d811904424a00c1d03071070307007042d00f00c840f041c151081031503003001072074a240d00030340000c1300c01200b61900081100c152003244a24000c1920122074a0308415040341c820b150040040071600d03a80b003102005c0b03041000b01c508000c0709910482040c04008190320f242e980e0b541e03000000c0ba4000d602569680e60900000d028001a513010b0b6001c01250015035020 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 594969028 1250 594967778 594967781
    0x9010b030c010305010b070807050102160c08060f0609041101022b091403072601090c03051005060a150c0b1003020a0f0819051e03030a0f050f0a021b120d0c03 70
    0x484d186d0108a600e024800c1e252810964000c1030156059902003040c40c1e080707400761004d07080441c01a590141150b040c9404281090b0000e03245401c1d68540505000c030b07943d210007040d42c01039400801c2d1021b140310303000140c0c1044c2c0000b1012103410a10440a1080b50030740401c1d4094481c5c90303035200c003400d480b10f40c84442c00071225130158040d48901002e110754232a181c06444401c0e42d800c4140e40511800e600d942c00e40d02000d00031180c40d01821070030010403004100000040150840a00451400c00c0120718008981d11441211030030b4403412226650080c4004c002c0c85400c4410a189841c00b81480b00c000c08041c4800c9001d213140c031500181031103008415105603204c90025000000e00b4001443c1552904003040e1180d000301711854000d03442040d115144411b24201450301d030b1402141c55000c03550203030030145441d03040c075081261031b00e24070701c409a01120092005845001c000d5290449005031030b980b00440c030540b0a026903528402c0e012300515101410284401d502e811022030 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 594970278 1250 594969028 594969031
    0x10503160309050a0c0f09050109020a0c03030c200a02030705030609060f060f04050906010e1018051b0703052a1b12030d0902030c0a030314030604110309010b030c010305 75
    0x1205464000110319424801c0c0c10203020940107008a03101c800e49a141c1000d00d038015805003050200c408010000b40d14140109070041458240460803d0241d00c0003500b000c203100e0004003019907400741c06281a0007024420380500300b442550409440035142180d4a00b05034405910900c10044005000d14002034000d1203040460042d0050b5259094007007002140a060070b81d00110f5011024080e031640c1c0b180503c41c001c4140142255458828458250308000e41045240c0b065100d0500027818032401c440320300d000c2840000742583c0e98a44c00d0580c5407118800407400580040c04805240d48080a412010f89405015140180306151030011070741140c40560036030841488035200c00654081d03d5900310700a41090701e00c40340c0780e00c80ea0840d800781d261180c02c0d0f0303a1a0754a40a40c1410803c20702c0c10001a240a0607440c116103000d0100182c0b83c19011510344000002080e41c0c44542040f22400c0b110707018141ca07800c1c04600e04d0301a02d03d4583c003500920441d60000034540c0700b4010307107 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 594971528 1250 594970278 594970291
    0xf05010518130c022407320a0c06050709030b060105030a15120c0510020303013f060b240f12070f0215010609051210050c0d0b010503 59
    0x2103181c80000c021054859010380d8029a1001801e151503100040d140a00146003e0941c05003600816007960706242144401c0350303241c104c0e8401c041001e0f41e50000c1c007445207001c41d145181301d01b41f00300320107032410384110060900080010030b0000314950464001e00394140314180521943d520010100c4100e0020f01c005401e858101c0003240047d40030358001c5400a08002e8042079075004400c070804488000c1d48807145040200301480d05000340000000f018240c01c4604410b00351040b50000d642e400180074080d5002000e002100c20300d50140401011007402c070414240211040310340140404220340199042400e010f0307407c4440c6007903d0b00e541e4200b18007840106121b441010f840c1e03981c01c450241c048104040100c4040701c080e003068180b00700502c0d5254107400c0d9041d6402402d005040480c0c606414040c001401aa40c00c100d2035025a901074a20fa880d0302c003241d80d07080c981500c0981c01101c0030f1400090040134210000109590303400840c0900c450a44980111410f1008030b504 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 594972778 1250 594971528 594971537
    0x807020c0d0213021e0310050405090a0210020a0f0b1b07020102070b130f080606010e0a120219090e2823030408060106080712050606071704080a0c030c0f0501 70
    0x1c040051030000f00520720039500030b0f0010705042c0250700440e07041810f00948080d01001108000500e940340c144031000d004196003d00440c2010401e03a9070750011040002e10450200c4204815548200407a92050b0303003188000400d050a414184280c50b8103583c4025151422710143d046400c04104940c10b035a410ba00806150f4a005070b0401075411400030207440c0748841100051444c120404607020380b511030050a1142000030001d080c10b015000118019600e0701c004106508401d0745c083c00c0503805075841280c564400107210340d0710840c2e4005d20703e41072401c805c01c0d40034540004c4480c1c0a042c3c3c406181810b595650320340d4a800d140d1240144040781d007425851800300c030091252a80c44000088904154448084a04149098001d20001025001040710007541f001000c2003d00003400c2c108440c1c1005400300721240b040400180681c2c01c50014000d40402000c100e400802c0ca88050764596140d5251001c0c40010f1740c0303c01e0303648441d5010082210350300e0110030011200140c66 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 594974028 1250 594972778 594972799
    0x150902040b0604060507030305071407050c030c09040c0b0c03070602030a0903090e011a16021203030a0f02040b220906060905030f1c140412060e0f01090305090f0418030f0807020c 79
    0x60440140c0401480c2b01c04000d80c55130003c3d504405900035000151140c030252190300b0320801030502c1c002c51010603c2c0314811580511020501480c458001e546000d021507075903c8a14110314510b1094420003060b05100008210101103140e000301070300752181e640d030600141d42e092400448a4207004040d64001081502c07100070001000408000100840368608840d145d00015455031001202000c280c000108002020106104041404e400c040c400c504007414159000780d240544c901111100b0810090300038152030104810300145103402d0b080c001e460302c400f0010540403a911900740240300b044009000701f00c0200d100101d80d040e0098010708031030600011110780482c9482d20400c02c0040102140f045800f60003114001d005002c08500d0080c0c082c0d12614202c070f0780c80f00c0c00300340c1d240054460029900c0313001c23507900510841d2520459042d0000090003400d0483e400c011244108401c00100741d00102854840e000316141c0c0ca0899441d5402640c60b8165030161070351044c1c0400 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 594975278 1250 594974028 594974033
    0x2012f07330506102a020904050304061206080c130b12010204060e03010209100c0c03150b0a0602031314133b100518240a11090f010507150902040b0604060507 70
    0x4170a154906008031401d9008079075801040e440f030000d0301c085d075403030f003000a0a0094680002c00d0801141075178400b04411894446115201e02525000c6807003419020480e040c3d020080d0411160010010196103001086480b140d00030b40c0580300c0c820105070302103c4d94040345010b10a4640441c07001d024041c4141c00d0300c8013250483c640300350441c1c001404900100106240406004018284c01d0002814032040402c014003074170144e02c60411580104810400d1811181d400001c640000d80c00e0400c504122000401e081e076068140ca00941ca040350030130054000742014021440305004010603846040c1c40320700400d81c95008585240d000441d00000c24003158081d5034841d802d0341c0307110f9110104207230032810072003422401000709080040c0290942c94421140750000c02c1151304100300001a42d260040c3d01035208094490440c517143eaa010381d0045040700c142c59488003418101082da0344241c4024903e25006a0080f0300d80324001c14503052030411034083c0c9060b900d91a04042c0540d = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 594976528 1250 594975278 594975317
    0x6030c09180f0e030a09050a0e041e021309110901050415120219080313080309031f060306021c0c05030c0706050403090b0a090602012f0733050610 65
    0x1081d01c200c00d00d83d216865140c450042c0040c02480ea10ba603141150b00b03141c5403c200100d03081d500420020249174050000140545000760a240743c2c0e020161294400c900001d007001248100c504242400c0c21407080411152700d001078891181200e4048081e600c5005002c00c03140c88034a4a0341b155610342c41031080e0f644503403010a40328070042040d01ca940d044170002c502c0f4a41903102001030351011032107505101c640107401c0051303c3d9482c029400c004c0844000b0b80d642d2500150103100284084003044941c42e550003030b201864010900390350b208550365a070b0070452642e070060707400545004c0201200314403903801c6a000ba1a204540341c140384494585174010312003c2c004405100c00700100003001c44150024000c1d03440d658803100d03401882d122002c0c0c2501c10340403200d4803040354031050425441c3c042c1c0c0c0c4060b20310840071500d5164020b80c58850001040510b02140348005543c255203003808800d90900700e00d200e0070061001d0388410b401d000403440310030314440120304045580d0480c201c00 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 594977778 1250 594976528 594976541
    0xf031201060c080c010612050618120904020d0c0c02030f07030b2403070305010b0a050d230f030d06170a030c021504030b0c0c0f06070804061e0f0606030c0918 70
    0x5480f003640382c070b040c10383c045003160066440b0f890241001107008003070100521005510100742c01052a030742c4c00b80c08030541c5442035036109400c00140441e0340380d110389035a4180c402285000e039003007081d40030b2610003410340b80c1c00c1e0000724481d100c3c8000401d003140000c10940e04884d07202c50280c005840d154408140403284c8140e4000400d95015048101c0c1d50070020f5034011800744000190b03240340d40051040c03c0350300b50419800361044503014030014007880e0038001e0720000d19059020710101e1100150401c1140310050907244800300c1c107030551101d50340c080c00840301001c0341480201030418402d0b482d4850400e0250104014903140740c00740c2841c0c40b040ca000b014010000d494503440703a640d4000041e050350b080f4080d0f240410040c1c42200c0420020094181c2e0200074a182d2409100003010b003180104028035043d161500003c078242c07060075101903008500001c5c0220464104240014016803140c0300001e8142280d0541c1980a00d110740c05442040c03240407440707032800f1041d0018110 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 594979028 1250 594977778 594977783
    0x20d031a06070c0501090f0302010e060c0307141501090b1c08040f0b0301150804021e0f2e031e05090309190e01082b020715020f0f031201060c 63
    0x40815228180d03544070402001018450100680e11030f0900f4001001c01405400040071042d00042c04d10140c3c1e000700b4108081c880455659030b407521090340140c114000c80300010160684010311400c04180800c2c0c59007501441040f403901030307176a82c2c0c0030400d0300c8041030241c0d004200344240f855154101c0060780030341401914105c0c44c0aa50b240d0414111610364031030400a5130101c01803042445802d9042002c90301403030252514101500090450800300d944a070303141120110041c52503c40504000c00c0b410024403012004060b8400464424298070305c904011007980341c4441007134042d101e60400031030103910070343d0041a01414440100f102400c0a411444140000805641c46d8003c4a1100d50b04a182c2501c1c40e14040310900064010307005410706030003412480207101d01c9044240780e43c0b46406144441c01e414a00d06a00b031840320340154544903e844804020070782c0014001d541e14907180121009506c004840544900034036005d169159822001003000b0340c45107a40c80c0d813060 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 594980278 1250 594979028 594979061
    0xd120f17060108010e1312121b05040506030901090606090c1e092603030703290105160222051e01030b04030e0316030b100e09100f0207050a060b0307080d020d03 71
    0x1d040e80f00d02d4004000c0c20140740008080c1108e024014409000b014035100c130786501c50504000d5120060f01900580c014503000c3e200100014010f030340d0942040b49141d4120108009d81502d40001e007000e8507185078500049814400004480d802e5105079940d224199507541e40703403a060a201aa03000491050a40d560074141003281401c01d09000442c06041a92800140030f445065200003181d40030103c1c0405113010a050b60f42c41e608002201e08003140f4070b00d1030f00c27a0b040c54800104d0b9440c1d201202c4031612040901d42c41d46803803c2d0702c0540108030b01e602c1c0c0d0003c8007032200d880500160034040100030584100206000074000c1012041c07415004003922034800c0b8644070300e001d01085c3d90059170901a110280078003400c40c591284058414020514564603155103804d9540028014040806036140c2c84d070308141c0401e0741640c2c41c05900c07009880b07c04a003400c02102a200d5041002c0c480d0040c8480001c2c06400020802d4051100717401800c0019664003080e80184401c114060b2802c = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 594981528 1250 594980278 594980311
    0x50d020309010207020f2d0d0c1508011a0901050703050f070b0103022d090709080d02010501140d1a0c0f12090f0d090905070c060207140c040614040b0d120f17060108010e 75
    0x2c005140b00400b81107200d440503494944481c004bc49020103910a580000caa032946203984044241181c00c500c03020b0812560305d046902d000c4840c0d100b04000c456031410041000c00070810942d541a040302d0003260201d444041101f240d107100c19243c02000358840c048e0400414034101503020700d9200b9040d08140500643c1d580803141060340c0c403410b5400507551400180210250381456018601003900c4040c242007080c2e0b501403a00100e134a01003100e204400c0001d02d0303405564120f80e18561f41e01c0c0081d8444044030040c0b48034000c1071b5920314540c00756030b07511995001c0005440784815410342c0c3d00d03e9001d01e000c2050b0001e03d40035150758200b009a101c09000b2601c00d0001f4a056841503008040c10310032601202e05003500358803400c0c4614200401045800c400300040c0700003200485000505d4112900041c02981200000070b2503110394081c2d001000303401222500301c410454441e040020411349440f51810740031207000303004c51207c10062011544400b02141c3c41a00d490341103495 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 594982778 1250 594981528 594981533
    0x1e0a05040515070218190603030f20030c030901020c0303072301060e0c0405010305060f030723120313090203010803030f090102090d05010606120603050606010f050d020309010207020f2d0d 83
    0x1448480d28100174030303040300302840509900868010000c1000480401038a402c550f0000c20040c401040d403420816018045000c02c0c606000da0707100d401285003107ea5605e02401c0d0251690400715a8074058020143d0303090990074007004841c2c02d5036000f04541040a010701c41164203d03810340e0360b6540c0d90b50b078180c0880da01c8a04030003203000300e441410003520b0b9841c18000405560008208078011044590343c4070840d2000185402079a1800c250150501c81c81c03149407080352440c07002d1035800346090380703400915880800200b000e480200c0f400c0d0a41c03500c90b420f00c0180e01c000c0c800c1c1202a07000304005070b03000305500d1016801080c0d110015140c800440002100003406980940f0b15075900c02040010340c1d00308a00c401148810441402060315546401d41c46400084c005030620503840b03086038580380709800306e80390400da000007103449003040f502c03c9000707420100040303000e010454082600c5144c4203d8510101c0881c28018100f10030b140b554041001c10511780c142c2082030922306100 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 594984028 1250 594982778 594982789
    0xc03090d050708072310080c09043207090f0303230304050d0801050414040f1b0b13060e060319060b0703032301080604080a0c08040b1e0a050405150702 67
    0x80c660480355900201d5041800d0104441c0d41d41700512070980c1328802c0344219040701e01c00b6403110000e080c1544800041009c2400b901c0e0034000040d100800159503900440d1956580d990030490301300c1c421007540c52801c00c0d249600980910701c1c100c16240801c2001078401c540b0103020552000d10f483d00c2d03003a07c0d00e841400d46c00580b0100c0b0550846500581c00c25804042cbc07600400f000ca50a115400c0c034409039035201c04014101400d0001709503280024001403095280c0c8070070018041c030b1191580da5a1401c902c0e04074011552070050390b0306000440384d21800d28000501e000403c200d2540d200c00d001c4022048200b681406850f854803000140154840040c005450103a140401e5240800e00e20800518030318a0300f500400440c4018409180700194240c0c0c4103a00142042d641c00d512481540d2009090f40014512035000801098003100000500300d104001d00e03007032425440090b500800d42c01170744c10b20000280d040c003007000b4a280c00d11280381c081200600240c40e11026070041407 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 594985278 1250 594984028 594984043
    0x5041a070201060906080a020906030d0909020904020c0a03020d0816171f1e050901030c0e0c0d06060f020f2a0f090a0b01080f0402010f030b032a01140c03090d050708 73
    0x1d42904886402402e40c127100d040598441011006000d0700c4541a5005e4400c0146009040304143c0c08110b00703000c4d854a41c120750038055000100c40e44609186002552030402800100001d10541c000c54035800303d18020820f04600ea490302886400700f01c41c99562646d0040068070031450031038003415501c003240d9201c800703004000c11030507221001400c0c140f440c2c0342613070015019002600040003c100d088007600155010301d403110480b0344a0034802e4180d800740c00e0703501070060320b40300340003034699086408024481100e03000d480c040d07207007140c0644c0c032a01c40c02000d503004e690b441c00c040d03041700d40c0c60200b10400c0401404255844a03c4011a400e60022100030a9890340c03192512440d617040707c0840d610040801079007101e45010703400240741e0760211041c0014562941049492590284900c00384e030b6a00d10a00b001c0c00c405202501611b60a410285011550008101008001c618200c0d4400031012009501d00742136181481003e5000b83c0068649002d00180403561b88801d201c900d = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 594986528 1250 594985278 594985289
    0x1b16030303020a18081209060403060204080c0103060504022a0a1704060e030703030e04020d0605060c07060f0c0506010b1b030c0304031a041505090106170319020105041a070201060906 81
    0x50b03d500c0d2404028006191501400381d5501d08404200a28800001d22000340354441107485d8407111004003081580c021a0402043c05e80049004901801d00141804030904240c0e41400029a00d030184000c0703104032540301d04103090681d00303282000107900f9441405c808120403114002d070540c03542d000801801710042e421010004007080b00c5540580700c005c202900f10040e041c268a075650250001110309402400b07103401003045041940103600003401401e0240c5095914014400826241d15443c06880007003100100802d40107885121049046079011000340300590074100200030300c3c0c100c80120400644c8940307001c1c00d09007052001d4a8840043d070002e517140c07070942c6440b91600a607004140400744000080101151414440500241c03264000140b99110070302a507014080d01c0d04032002c9110303010341490030401c000004010803001d61502803d080078402e0101d0a84005030303009002c02c0c0c40c040540b007200200090741c1c4e812188500002500e650b4601801080d6031166120 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 594987778 1250 594986528 594986531
    0xf03020c1309140f0303070810091d10050603070501270608041e08030720010501081e0c060909130204050f040615050a090b01020703050601170706030504081b16030303 74
    0xc8200860400c1c81015031101c034000d882c514890448117a56800014601c8040120700e001103010f0500100c8054007610f428041400006108984c0156040c0700340d03a106940c0c07003076042404c4141028800c0500401c0d0050141000030f160400454030307800c4400d00750200321200c40441c0901543d0409a200806058541c1405d5280c1030400b50341d10804055190307513a0003004001d40000712020201c95000c201801c12950400c1404103c00d6841c0c00602d88101942c0b80000129036a40c0001d1298540c0c890a1140d41164107850b030900c4d01c0b0608580c0340e9401c080b0074800306482e454103400f4142d00001030944da0315800300381d400041c107031070f41078881134490b06200d030521084c44403500031078103080320076074055000b030f440e240118013421942c2c402c1803001c03a503405203641305a200707202200c011a0401e01f16602d95840d440c42c1d152516a413400d40200b48680100003032154083d0107a188640d40044c1ca26060005404900f040c2221000340644d1a00440d50700c6806000c0d20190400030310b0181c0d60 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 594989028 1250 594987778 594987791
    0x5091003180b1803070b280c110c0102150f0403050f0403030906110f060601080628150c171e070302060402032503060c02120a0216120308040f03020c13 67
    0x1594103c1c1040b582c01001c02e4000300101c1e000304d0300c6454030a4003c3c00030000200c2c10184220160200200224060055800d083e0710441da19032200200d21042d1256080d40c2e40e490f0b4030801665a8069410075155aa60460005454140588030154401d00a04002c0d1814000215110240c3e0042e042140071400c41c000500c02c03654444a00d00181c1184d00050034482484100b0a56039100107150070f04102900703001560540b00c0714680c0a44a100101ca50a030f004030945100c035601d558090b00d01001a4200c408d610184900140007469400c44202241001481101d101d070742d11414000203101d83c0300d000b200c03440048400600740180a603000e0b1005041600c109410540350070600c1c1c402010b00b0755200e03040d824070380c1c46000303c0340e00c110000380600035140306078181b200d80655006a4600482c843d94200e40104400000252500160340095120b00e03642e5441d1010080144c0094255800500000c48005030211594020300494403051a25400100c1480c0d908040b051581d33105c1d113 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 594990278 1250 594989028 594989041
    0x20418020a03050708010e13030e0409031d0d03090b03040305041d071106062101060515190f0c0210091e0906090c020a02010f03110d05040506060306060105091003180b 74
    0x450f9a4008034103241a103940c0d45031103619801e020000d0040c0b071601d400e0181410415000d105800300b903078806441030106034102d040c09404140c00244046e50324040c01500c0c5854644010348158040d03058460306440c9040504282035900300510031014400c0412001c212a1400500390340c10501d03a00340c40900303160003100146940030b4000109803c1d440803061002640d14a03203161b40c0002010010300d07020502010603405001c0560102e034102981074106030502d8101d0000305099110700800102d180181a0204d81e082c00c84991540001d0302c01110a0061810300392501c09421700d8504000c1c5e081d2103030071b1225071100300c3c42020a180741d0600100101e6410b4000c1750018114480e0400102d854001e0181d1166441400217040001010010400f80d019600418141c4000c0c180340f13490380600c1c501040103003400e45090782c40b403042d100014003503d0005686446914180c0d26241441103180510140100005400080c140c423503403044034004044161081e400d000d261140210309101 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 594991528 1250 594990278 594990281
    0xf0301180b040b0a0902180a1d24011407050105010923010e0114240a031d0706050c030d180b060d0803190b0612010503060601090305060f060301020418020a03 70
    0xc541c06008038204540f07452a82d50701003003c03003210004500565503005980104558002d2080c910760720400e500700c003080e0101d942100c1074601982140020b071548031407002e2062100c1010349008200126810002c3c254410100604220b0201c00520709021440d5609820b4844c00d0300550400d55880ca14100030b6410659a00309010314903d140310035504000306810101d0701401114035481060542c0c541300e44554901c1d00d0648203c0300240d000481c0c1c0040b0613030541c4506018000a030038040030030003004075401c1c00440d080c2c8901c010840d103460040b003614540c04c01c2e440c1d5041404144505003501c002801590f420038111110360245001d90b10b03094010000c080c1040b80540c00300001d03040091081402c40b5000210030301c80900000894105038042c2a1010f0003540000c40403618440180c80140310605850b8101c09880b01c0e0380c3d0300c100444a042c070920010f000d5912147c08141da03042d07649040b5410800c0079001600d02625003441300c03803e24000c036601c0d0300d030f5500049850301e45501d03 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 594992778 1250 594991528 594991541
    0xb12100c1803050721021302180604050d1b1203050c0d090e01170106030c0e04021e0117040507030f0308010e010e0712050a290f0f0109030f05030f030118 68
    0x2824440801c0d082d03886550b03603000140104c80d800384003403041c0060b0f814042a0607900d264003c001408580340c0c030a8000c040e4102409a0b20400300703460110300d04c2e00d0101c00b55404d0b01c501500517401000c642d1200c0c0012003090140d80341078248254003003095110611801199030094888581d12408400224506860302d040d8070b0070004907040c14428880c460406a0448032902035950084d060901814018040e65200030800410380000103404103880ca41c0511850080340c5c10f41080010307165441c4e144912202e29800903001003d16103205000003400c582082c0602c00f106e1a450b120341d201c0a140484002c1980825021401040001c0c1c000c1040c0c0e0242c20b4800c0c1500d0710f03041c299400340095a000303007072810f11900e801c0000c0302085240d0202040c0c0c222401100c903078034101401c5d45d0328603c60050850040c64080307041c40300c0c0d040c40000c3d50704003241a07550301a16899519468601001480221214041003008800c201000e8018501030030008000d05045010080c0c09800c4403403 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 594994028 1250 594992778 594992807
    0x10c02150f070918140f0105040e12090112090b01120507060e0d0b04110901030804051005040b034606060c20060403020a12020103150f06030b12100c 66
    0x380300200004154001680030440b101c000c040c2e2804c9040c0139041000d403000445401c4c442c82d5503400c0100c9106100070013812500181d404018003107035043c5c5d06498030841039442c11128420013550044c0d5201e402c110004030100c0390005200d800716600e2000f002800c0e80b21030508580c01c4010400d0010501500300100340600b0301284030303e1888041246410103400c05049080a08002014080d14403508144204000c008980a607100c3c0340140040c0c2150181a015440d00c808201815014800b15015100d800d200b560a580e60035014842000e40409000c84114082d10b0540040c0d6062803174449a1680c3d10491052185003260101121400c1d48940200480a9104404218660341907895003440d020b100b40403680a00c0401c42610032680b00a4001c0210000021801c080b4401280f581e80f00360380c107019000c407a140700c45a50007140201c049440601000b0401ca601982c840400c425010380060710740c07030207090210300f0200d41c03241c1511002d03103a8101c0040d841d80b05210040c0042e = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 594995278 1250 594994028 594994051
    0x614060616030f030e06040c09050a11090d060b060d0b03010c0302070809121e030d0f110f130e0c12180a061107061b020606030c09040605040311010c0215 68
    0x104a15610060064410010341800000f00843d0700c21071194100c0001c10b9070040c11241c41d0700f403e02d01a03a07060a98820125034074a480c0110b0303506511401051100446060036a0810782440e003080080b1000c81d0040340c0c02036944080062039190f4101030403600300500400074411070b02505144c25642e00c400882d0425204100e448002410002500c2e0150410b48070229514100c03000c00c0e00e041c210b030400310100d0b54025101c3c1c41d1100000b0050107180e81c520001d1020403208003101051701c0101d680039600d400280984001c4100110181c00c0d5201062540692250786580400a620050711034001d40c80001510186508100d805147c000103c0c2c84035801c12805000000d440764010b010080c1040d440780c2070b8130122080101561181a00322004020000710310000c1c600915060740d014000d8018080056000c2c50003040c1c5603020310b00030300006c45075519079031f0f60001458001e00490034003401095083c0082c1d4244119009a552a0020b0080800420501d00102d00c01043c00d507820 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 594996528 1250 594995278 594995287
    0xc020601150503090708120301060f02060f040602070f02030303090a110a06050304030c0614131208060916090b190908060105090c0306011e08010807120c030605181b01140310181806140606 83
    0x2d02d0b0002c0033b10f40c421340004c80181c07640100d25201c040c40412420280d490310011040c01040c0c400810800d4810340714400c400340d044d0b644000c2c40050f0129108034000b0900a100140210380036419210714640718220004544115994036103200c60140d59041c50109080d010008105040058580c4d008a60901d59124a0303e01d00050000c20010500202c0405407000c9044060080c00207401900c981200551502174440c030308600d02040d41381c0d91340007131044000007072081408075041c1e05944e000b0300038030038641d0b2b1060340c2d24455201800003810070900c8480e1010400c00340c420000e0f00071141c1c0c0d81d1001540b6103d20749240002d00d030000c9001c0701c1241e00c0540000d103002c0b8078004403070b40700102241c9913450000444104201c01072003034950280f601248140282240051541c1c40240c03202c104841001c95101500d0004859070f11410b4014a0244503a51311604c0c0120034201100700801c00d9242601200304c1c4000c00350084401a0301c0f003900301c42d0006109000c0740c1c060429039905090 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 594997778 1250 594996528 594996541
    0x303090e16050903030d0212100e0f07030b181e0106051813090816020312310504021803120909011809060603080d0c020601150503090708120301060f0206 68
    0x10703249540d41001e102e00000c568140b03071410300c00c0d00da0b4001082401c540700c000e486005038003518100d072203000c208510351000c1418990090002d01460300500603001035070b201e030000c0c0c004064804a0b203034018040301303041c004031403d10034661044c04002005004820f4484a8011464042e005074007400014805d000c0c9078441208600b01d40c040072030710361240f90303811b400050041440400140a101d0700103013000203081c0010101a106200344c007164004030f02e669152009024501c2246501c06102044402016040242418427440076a880e051250390307400050490b40410065511a101c00e15581c94138981400303111000700703206814502c0c0c42010710010f4440c80701400f428602c9500070000030700018540d400b83c001c032680031804000a0f5181e0504840e160000a580f451131414103a12818041c0b000c00d030241290466101c0864662000200751392a404c001c080c40000e202d038441c0000c200c0301c20401d9142010300071201554035410084024100204044218150b40c0510b041c05003 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 594999028 1250 594997778 594997801
    0xc090d12030c14070b04081b0312070c0b0f150319030305090727020f0703050304021003200711041a031009030207060e0616050304061101231e0106090303090e 70
    0x402a602140c1c2c04480c6e070780c624012160b4040c9403603c4e01300c0940d04000950907203000005003494001c2c0c401c00d060f02c0c0e8820b00211540c110701076004009584a00c00710310200028000310b908000151201c580a0713a101d00801c0c0340844401e030348050040c03068906001d040d0140300b843c0e00300320140d02034a619402d2410007001079a8405042c18a80d4100060740414841541039865001000e120141d03107030201d00340200640c00640303041e4481c42962407a410314034040c2c07080c030b520000701004000c40007189400e22a00e035003100005442001c40c810804150755940e2050076810003034032001c0b060300c055290a2624003060f02581c20303440c5107000b411201094000a00e081215441e28142c0d00b800110800b14105000b0034881400d1200000b850804012002c030107002038070401d94034401e420522184007801d0710700d0348441010170040d100c1d40820720b8104900b13a40d0302c4580c1d01c09880d00f041000321710800501003644024005040020709104165101c00090010a49402c0e0303450b90f4100741c5400322 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 595000278 1250 594999028 594999037
    0x4140a0806070f0216030b1005040b011418040f0501081e06041101050720031212010308090604033302090907111c0e0f0603040c030303050c090d12030c14 68
    0x4240003c84080b20065032003004010031410080c03180044443d601c1c9440c44071040150380c02040c4003c01e02d40414075040620a2a1410005035654582214010521440c982c40003c0d12410500044c0c5142c005841d40e004004a06003a1440000c542d1b1412101c0e506140340c040445102c240039034108032414000248140e00a50081d280d028864108001a6035034441c696000784544e0170340048200071f00c0c040366190708041e13059090712009125110846210b21038590800380c507034024801031002c03880801c0544520390740a8100d6181c59101d40320f41040d5a1200401200f000c004402119800c03509032141e59030760202c0c0415818a101c480c005880340e60010101c4040092000041d142c54900704400402490442c0c07208100c2d10300518014040781d01c0e000e419008240000a6508a00389502100d1086411a43ca403c185055940072409800082c0a9144a820605c2800307c290385007074801c0f03403541c451003000b0a000d452803000b5060300c2407504800c1c1440280f031410b5010702c3da0102200c = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 595001528 1250 595000278 595000291
    0x409030c060506041b0c0c150507081309110c0c04061203080a090b100e250c033e06061507140a08030414030c0721060504030504140a0806 61
    0x4580c0d07542e0503011500030304900c071081c205c0044110b00904110b810070040c8003602e02918140d07400b0f0341c6403042c94071180030f00400840041c1d010031428000c508600081d150301c09180d8032508140c6c0e540c3d8111400e80d1000c0c440d2682c1120006540e4409640c1040100021101590180803032407409400d28a031f04046103002d000d02003041e00250183c40c09078442840c456222502d845c030703428180d0740002e0b140c0c124042e04481c81c030003101080352040d0180001d107074800100c117414081c8bc03040074125018218040101c09020b040d0180d04030b0203294840c03081209000c000406140e580d4906010102070b842d10544400e5040081480300684658140254031101c0c1d10740166140e01d00d240c104400481504161f07071601650b02202c04006081000714011400741c1555108241c0c40c900701d5842e446031040303440085c1d11030070041002198103542d5500031111070610300043c461075150792003500e500310f60071400550009411310548043d040c041031520001d41b0084116810700c91480e0350340a019122 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 595002778 1250 595001528 595001531
    0x3031018092315011e0e13025a0306010623070c05010e19030b18011e0f02070302120c0c0d06020c0105060418140c040606020304030c050409030c06 65
    0x4410502d90800c9001101d03240100c84410640c0d461a940341440303281d070240c0100701e40d4030f0300010b18502e0581c003103801008881d688401036521a0708200d400c603407a4230303400d031060700030201ca00341c548040c60046041140407510940403050780da064184020302c02e0103000c5482c00301501c141d1a4400003041c40c152007050901e40341c03a90842d0340101c40d000441404000c00600000c3e1001040350b091100011a1020389070540824600410848080852003801079001c80c02181000481c0c1451805a003005155079030b54803860403221160300795210001c200340c0d40c80082070b04400095417485039031281d01c1c13103840450511000c0c1d03030020b40b503c02c80c102c40500030102080c0b03100040401e009070101200014011281c00615141010194200f0402d03d0b0b015441c2c04000f6810f0b0a0502502415845c1105464281d0403599500100d0b0440c95000f41150b10035001c5240e41c1e5100c510454010305440d40096840340d245140800c04800c142d00001c0c003c90405686100103900040c3d01300c64680e20000 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 595004028 1250 595002778 595002833
    0x1503151e07030b0a1409071704060b06131203080108030a022a0a08060415020f1605070e13020312090906060a121802100905060a110106080303101809 66
    0x30304a0243c281400c015a11002599000458256107138081103100c409486900981c0e641c050143e900a000c0c2c41c1000c102040c0c58000307000500381d81c0c000b00c2401d80081c01c0d5400c8c4a0341d0301031421407103d00e4000d111130000300c01202c0140354125403198010036400b8000c0d4079001c0c851500a4459007901002d40c40c6c0f81b08403404502541401406010804c0090842c521203966031622079981d01066600b0f07201082d03111441c10320403406008440ba60064903207240c2c9440058000c1c00c00601d070240c02511503003e0780c440410030320a244191030040c02018070341d01a545080c010182444095204d0810a1404001c3d040180d103c00b20126840b24003115000c1d100c2c070070f9105c02da03030350405000083d01841c03800340808042d200350280030f40500d00a80b00c480210f4820502a16440000d001d442d03803002007401141c1a0701e201d0500c0d803440b124200000b041d000c0d9241800f0f840d603042640e12001007480031106206042d248040054a8410b00b0014031502c00c0503101c180c0c1030001840703d4407041d0400007 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 595005278 1250 595004028 595004041
    0x6032d030702060c030306190f0302100519080106020c04061202010c03120212010f05010e090a1104080109050c190e06090406110c010f11070218100308031503151e 72
    0xc00d490010790064495642d900b03d040c0340d15120350080b94690702c503524280d025080c0000c0e0405550a907084202540c100600b0b44e020054002d0b006001c80080050400071540e5410034030802d6034507c8041c2e00c0b40b98042d4102030020742482000d000b40c60050f031400d0b100f0006140200c0300c9481050302820001c0e50703107105040807502884200d954403151800010105618a0010030a03412070704440303a0494060f441d400112230301e40381c09520b00e90205640b0041b40b1815036582c00b64200030403131001e540c9041d9580c0d003a40e094400640c401d031110340100c1c07040c51850030f01510002520321200c220340c0300d1606015901120707030350280c43d180c000c000c10700c006810000d5a500c0100c1a405904100d42c480c04c0138008107010340080c01fa4807c1040c24102148608110803041d10305441d0b00420240040841051080340b1450051000c0000a1821000000328080700c000710b0182d010401d81c2820101c00c0c0c414540380c100380c2d01003030401e8a00c2c002004450305e400070380c89502c9461805d100940e80c0703851 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 595006528 1250 595005278 595005283
    0x2010605041e0c0e0603131e12121b2a050715030b0d0f0615060e060c01110301120b100b0306060304020f13021c061505130905010b030105030606032d 66
    0x1315660007607000410302c4500c4c46ca407206e00301c42501c02d01040102410600c8000c906600602008184480c0d400d80707a80540d000c1d482000c44d00010140029240181c00d901400300c0c40e91480a50200da800350004100f20b84001e000c01030304da41c515003954555000c0e960107954030950f10801400c4030320300c1e1040101a03c01e82000703020000003041c460714145d181c2041c1854a20001c0100c03805440c120040c2080400105088200d0f82c85403103c4031040c44c07140074861f003a408075031701620300d5594450b5a2042c08c00d21016502900c0c25529040400b00f4528044015880160a81d00c1003d68103070704100b0000e20b0070880303a010341c1c00d5450079226195440407038005680d20305040c0e400001c1070303054030401c05a80d0181004d03410607007002c2c1180b201325500c84110340e9140104820000300c1d10761614414090001002c005d014000440c180c5962101158111002a0006c0404250000041065160410144d50841c038124060607900d02103103200b00f1329020440000c2c1448800c1e01400c031000805 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 595007778 1250 595006528 595006547
    0xc030b0a06050a0603020405030d03090203121b0111041a030903070602071a0408250506010b071a07030204030b0f0f0402130902030111040602060108030c150604020403051c02010605041e0c 83
    0x500303d0400c0310788a000140c003a400030b0040c01d002e0b1143c1844013480b140311340100c0c0d62082c0c02138094403a00050f003418402d558001c5108000300301041c5118030000409110340d620904081c5091900c0c4c03410102883c6102080d001c00b420001824070600200802c04000c0f500d00542c80240180d4640c00c600c0d10b40401b0100c1c03d4014101d5510200300010700140d40010410894020380c440c04000c0d102500c0500c21756894030140240c0d20400041c0b215800503401042100c1c0144840450314903103059420b100c10f8100d40410000340c01060800400004405540e0017400704401a102464140b0580e02008c800920192103460582c84180d2100384c0ca61107101000c1c0c0140091101e401110301c009050341c0644500e40040c420b42000050110010040e41d0001042c00c028000300541e08800c01840800a40071640c415403c03c000400070788100410a801046c1000540192040142c0a030071142c00f83c0c003c50141b800c02078045040382807404c2d02c54010110050001d0410328031001220180c04 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 595009028 1250 595007778 595007789
    0x5151b090d060e210412020f0303040e07090305070605040e0604150f0308090f01090501020d030b041e050f0601030b010e090405011d07090e0a030c0f1401020a030c0207090204030c030b0a06 83
    0xd0114840850240403c050b03010101e0754080304c507106681d00c040c0c2818442da1094500003401006840014a00a00c0b4514403c034018100c03030030305481303489802c46800f05840070000315181402c104200401170100400404180c00d09500745898100c03140849400100342a119680d50b0810349200640a50a2030140a1058108207519120300c1d0806103036100b07900c1c8c588544c100c1d800c1d0003965841440244181d0f41c040e405407410000d80c2d442034018100c54920a54020b40b11010a0411178402c3c410300f60380500321102007011305003c0c0044481040c050549410142000d00c10013250740c0100d107102008805640840c225911410315900600b820b100d100028240a101c95288180010b107040c240d441e929010000000c0242c9103543d9400302c2c500003000310b40c174201401e0200c2d10386000318a12a00903480c4202c0c04500c014660b00b203911086071400820b940d4024100c070300e40d04100420180140110851034241152640e1b948490541703c02859102c0c80360019803041e0042d08080018078 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 595010278 1250 595009028 595009031
    0x3060f0607050109051207060e06010522020f0d0c0807020c01050406050f040503160303021915050403050c0607050c0c09042d150605040b1c0b06030a0c030506010305151b090d06 78
    0xd20819001031031f40c4900310503144181082d40e898000e1a011680740c0c103c1780000d241128402c00e2a401d0900004072700d001503444c50703081c014000301c0c4401400410211400c200002604015081c006c2c1407550054a0001194045410204681d0b0000c0407a01a5052410015103565120324640c065100700d4100c2ca03050b02910740340725000043c03484901d003030b01d10980959035405500c1842d940442203586000d044507070314007401c410115642c0d01031030304140280380c05881e00c4508400186010426141000000e100060b1407030528024400070307140d810102d405681605040c3c454101c3c240c1002c00c801c010b81c04003440700f440202c4c82c501e4407858542c0711409040f8003452140c154000d020500c9018003480c2003480740e2000b85070910030b00c81050340744050442219020b031200d0110300d01c02004150584110328881c0c0c003040c2d0381c8011000a61280c001419103604500d00213090903564002d000000180320305015010055440307070131000e40e082c9007550701d0340c07844800201842d42074403000d08030a = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 595011528 1250 595010278 595010293
    0x140735092107081f1d120f04270606030e03120a150303020609011506051801050d020d0203040c0801020c03190915051201080c1c020604090c08180303060f060705010905 74
    0x15000b03a010060100c600e5042003048003024205c8101c1c0001c40c840c034606036000070012442c003500950280c840d400d00701c9155410951942c10041140d03155042c014141100100f000d001c140d498002c100180c1040d01e010b03c0301c103003181c0080b589c0b4000c50b01c0340c00303000042c032000410140c950341c80b20303040303201800085480d642c0c0c904002c4c0d00d034101502c000e0754070b5003003400e20801586480c00c0030f000c0341d4169607400e150038500390302030214501282c40581004010004048034030118005010441d0b43c10200684d40e040c140b52103481500503511652659006000c09c03100d01d1000300c00c2ea1502c0007928100f10042031004030850301e950481d0030440025060b00405e00f1403503449005040d10807070510050000d079807194885a139680c2c03812001d0303034454514100780ba80449181461141e0a101800282c02c01c1d445004450a99210320740e0780c40045c1402041003000480e104440c0794012074007024501c0c50802002141100c0d0241c244c02d070190000003640d00030030600358403015001350400c041c1c880c00d = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 595012778 1250 595011528 595011553
    0xb0415090e0a05120706240b070c082a040b09011818030f0f0c050639190e030c1005160c050a09021914073509210708 52
    0x40d4000d24000d446c400c1c80e01250109190a401e00d10941480b5180c404010b40e02c1c0055060613580300d800c3c01c8400802c51a00041c106c030007081004403004401c03507142090b40078540e255141c1265086003501ca039040c40130082c0f007501c3e0606114107442d000000703030800d41030a8000c000600b45450203e44c00717009a200308002d240c1c3c00042d0500d440e003265540700000c481c0490480300c41030148005007140e08040b02142007406070a0440c1c3e107080701844600d400103543c00036400001c4200108045840c400180c400002001200d00403c3c0c40785800c010b000b00001d80c01107903030b40543c02159405181602c080c08000350284007560a000e0b010800d00003070581902c1c100d0aa00c0b41807040902a07a880c840200301050a0b0007903819240f01c07522906040c8420350400c0744c0582001080e1800e0850412038040170a8109540416684030640c00404656103008403600d11088640400c000000c140901001c82c1d80d9403440c03500070114201c81140d1a0030a01c0314509140f1039511a0f107280c42000d484180 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 595014028 1250 595012778 595012813
    0x50c0d03090c0b0304050c060c0a0804090212060303040b0a0c06140a0b0f1c02040506010e09010e060a050105070f0308070915091502070305070e1f180b0415090e0a05 73
    0x8882e110311481c202c050340d50603000105010544000f45660400c40740e8001c01d04001001c1c10340c4030740381c104541451400c0d48840ea07240e4041c5e040819001c0d000107401203800d440280e40d5822010640045181074940511492503000d00c02c680c1f010000703600c0c00706050004940140081644401d0641030904201d00103400403c8072000450003548030361103101c06860011482d030440800b041c0151040a0300e9070801c0000e0000424a034180f298803c48110991035850069004e001030b0f108910740c81c1409010030a2440345a84054100b190403c0550000340c801b034990380e91b07503a0500781040561640c00301910110768076000000c0b185880b1201100702d5034494082c030200c03110540b01e00d40c022511901242c40e55a540000f404a601c1010104586041101042d5105070310150640b49048810702d0303103030380c6c0f40c00f41e02c8a080c900b030461004180e0101c80c0305071314000d43e00305c50800580c0000440e80482c01890f100e244c125554030f003a10070100d101802400c050030b5101c02510400f030900d002500 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 595015278 1250 595014028 595014041
    0xb10020c0102211606090b040b04061107080724020c0c1903050c0607030e09040b04030f08010e0a0b030a020307030b10090203102c0c0a020f0309060a0e01050c0d03 72
    0x90041c4501e101c0c0303054120600e0000840701540c0d043c1a0321305071041e24207100c000124141103500035a034040d00000310309882d50b418045d504c945808030071070a150902d44103580c9a00c0002d200724908026941c0041c1c940d038120b0781ca85e0b030b100340d521810011484045d452146802c6030340541030300000b029200c9031400300e0a43c1c1c80c94070450300c2c0c9003d810041000001210b044c00010407651041c60055070501d80311b0088c1201500c6490000c000c0355031030000c82c0d140e28042d1011904d050300e140c10701080540043d0480d00c0c0e02c0071391400d54420740c50900c2c108044a0081d0021180c513039a240001000d44007841580b02c0c850300982103400c0c155403454079003074a10013200c2160140388800008104c01900c0e0084078000c11001c00514292818100e103110170806992000346030a10506c0c041408100311018948170704a50240b4586640c85030101a080c0030b1104030100190300304014901542c6d40c2c007400e0b910100c242c0c3c83d19050002c1100c00594040c4584418160a071081c10203021103a40d06400c941c = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 595016528 1250 595015278 595015303
    0x10c02120d0210110d0203100308070c0504061d0103031803051c08061203041a0910020105150105071a07030603080d02030103030207170a0f050c15031012050a0303020d0b1002 77
    0x40340500590300c0f42c00304494050745603283d010000c1141c0d440807036894024640040000c1c0d421040c00c1d58030365854240e44d0041c98100d5061131a544100300d00d00c0c00e4807402004282a03030050707105204074101c1940c0c1031130502004040c410800a80c121850040c10f0035400f555101c021904940c00c003c0c00314003001c9000c114000041c6086c0d0000d032183c01c00191502910302d18100441c20982404070228801244644041400a040c007190b070481e42c0341c0c4882810038103140c0002403181856141c80311900d44041c1c1c141e0602c4010844440061303d05140300094100d40001c42c500354803807070400c9014042607070003c3c041003000700d01c07070045440711740c000c1d4100c034487d400f181c1035290f4030506100c03040384507518003000740c1100000801144066002c001070604c80c00a4491500040000803211750004280100c03a81c4044100300322034500f500200040e013120755800e05007a10682e2110f07030310110b056005003090380104283d031070042c43d600540d052507001000381c0c40c0c1c140c0c43c480c0256500da4007000d6 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 595017778 1250 595016528 595016533
    0x21030504260c010e0a150507060f0c03050109050114040207020d060c0f020d180b0c010b100903020a05090903040302060c0f0601121a060a171002040303032405130b010c02120d02 78
    0x1115031541c0100042007101c0310107170448040601d0b00c0c0c0c0082051001000442c18400c3c01c0101c540040d03175a1040c600d006444150014000f041004000c00f100c0c3d05800c8030303524914210050103d0788000c9203428240c50308990259850308a4404540b013500000c0740105810300340b40a031800c2c160052810b03840039400e6030803103110b40310300b0408465000181c0394401c0b01c079500900c244501040c80b40107004084449001207401103079503012400c0c002c2512002800586110014404c41c07034004020b00081004032081d40d542c0c201900340d01d440c0d1181d44002841035a00240e0101803071750600640c8966034180d01503410641e91282c01e098203a8003084110f40342c8101c12040a2010f065003410790251502402c565007140c02c00801c2d03041c5040307058410049119840d0f4110380050240000d10203144255004244085409405401c4252200035201e140030551414030031a00c418038809007484007180e021078011001e20060303d01c01001107010390081492101b680f00c1501c0010800c1d4020002e908 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 595019028 1250 595017778 595017793
    0x31e160f1a0c030a0902030307020901080d180b030f060a120f0204051f0e060604030b01140a08030406080c0711211c020319030b030a05070303030507092103050426 72
    0x8180203409000c80d104400302000f4000320704003a906602540c086072025017160b01d42032845c1c000440f0398209034801c0c44254800001c0382e600c00e9110606814175042c00390100e107803c0c00c041c44141d207800001c3c50340c1c03141c6020b500090300c0c507038400c2031100040200248403a100c0b05030b41402c003500980403e082e40a60700b030001103002010034000e0592000300d88598440c280c2c0c18075110085095024010030b0f03001c1e0080c000800420100d0b0030907802401d60710006414030003207405004104050340d00440598000b48005c01c0000c1d00601d11903800480c664015036140c103d0302c3e0041861b440d989556401034100c000c80411030f88070ad10004000c5030010101c03006d402c0000c00608150060545002c0160030500c82c181c1100c40560084255005604003c106440d00101007881c100d4082c0c015100d59001c13003020000e060b094410107412042904d0000e8600b0700708201030126084c45003641080700007032003036039050511440a44002e88110403a2003891100b000612001108003030007440180036058 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 595020278 1250 595019028 595019063
    0x1e01020105240d061b1d04060308031504060317030615040f0e100305010507080115020d09030305180a090b12010c020d05130f0f030317060102031e160f 67
    0x2035020302a02e510361842440c040ca210a0024064a0040441d001c0f40c1391a800000c580c0302162241c1c0e1240103544183c8400400200400c000703200420444c011480c041e414000702c6c0d405000c403070384010b842241071000c01c001340c0460018403c5a101074003d61040260003c3c00f18048000d5004401c11260300500181403420500c1c00d100b10b100381345100341451410401c1400c0c07661450b81c811141d481001c249a43c1c0e4031840d00b5a20700f01c4103d00000c4410005001e4054500c070882d08062880c0b00800749000c94080c040d08103103060101405004d0081180b2507640c2c42100300440c416805400da41203e40c2c0d800c0100050403504201610900a0f2000059003107014860442d5841d0700c0d500518071382007085010707202d941c80742403289000380141c000810507200740911034000380418450301c2940e516505006100031880305403030500e00c8002d414040c55a0340001074452107a4103100f102e441300c0d81d8841c454918403500e5520303240f00480040000500591600b4460054060f00101002e0210741c1c = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 595021528 1250 595020278 595020301
    0xc0c09050f161d24030c041a0a080612010e010f061809050d140d0e0c10031b050a09120507030606050105030f15010504050d060902120d0504090b040b1e01020105 71
    0x201540510310400608003202e49041541e1440701d51010f2050f5114851135261181260f000725017a444013003000a042060140340300c202c07501c6d40700c00c034035035420100c01c448002d14211001c1c0032030303110390030061403d0310500c0c0a5012000c07484462000704001c2c00d0800661010b00260f229880e05401450382d036400640590142480791a804005000e461310303040401d4a280c00348107400c0c5036540c001d20020010170b6091003103000f642000070003080446140400c011040070111542c00406051404440e4a0882c1d0301e4100203403c0c0da801d1180c1c9a000c90203048915032116405081050000442d04050100114460054034080ca8040c05210789440064600340f0054845100c042000c03c00141c0c8a6030088600c007000005251040c030349656800020340b41c6807402800d40e01c066039940c00400310f11b000707034000581c007050f00c0c05030101714403680c0d01406902541c03003699031040d03e4040140141e503807548001c043d650000d00000d080d14003a011240c5501410300c605000d51701c0e144c0400c0b1020f070035 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 595022778 1250 595021528 595021547
    0x313080f1b04020a09050a0909022d040903030b0307030c081501052214011d0106090602031204110607031d0901050a06051e2d0c0a02010c0c09050f16 66
    0x40060700408154007105000082d40310518100030403c1040020030281c0c3c2d070700120700080c4244800801d0b00c0c0ca40d4010410443e042110f1000344070760701c205100380350a18407040d80c004c5408450004045010b0300341500a13024030389029501d030007051b0700401041703454604001a1001c900c05c84101c0b481c0440b4502135414203009141e8003c010004140d104030010002c8481604e1500001c110104000c480f158005002e030000d0700d21040398400c188a10180003900b0780184100e00e48000300381d1030207a002c2c0d2070b8420015903981d0003510800007030521007450140044408042d107071503901e2045040c010113590380c08444641444901c91081114988403036042c0c1038800003040701422034580b0805941c15840111061800c11002c407031206030840420191000f00c0ac00d2203800300d01050300036a0440c81030503c04501c000c0900b40444400403000203214609641e0a0800558000982c20640301000031076110001a80c03d180402607441c4105907410302801041e0301e01c200c1d180c1201e2050354410403 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 595024028 1250 595022778 595022803
    0x90608060301050603210f0a03020a0224070c14030d0b09100e0109022208030a030e07180209030f100903030c02030901020a0303110904060906261005180313080f 71
    0x4840c01c00e080d012150f00300d040003d80840307030034541080140840304d9504464902400310b98003050310b1350034533014441703a062015200d01d0141d15010b280f0300b00503418000740c400d0040001041520040240300b004007078108071541c045076200c520006070300004e0580c5002d018014810b01c004694005280d248100c01d5500f801c00b08240c0783c1c00c180785140290084442e40440c0250107810307081004420410002410700e080155985040c90a4045d055802d008244500f41d032020382c041210600e050703400c03402840c0c15100543d441010000003450580c0302e880f40780d42809041b03240ca000c06901c2e1321440e4214440d84061107403404541c030503031302c13400f41d100c150b07025030001044840028401da210b034041c000d001110b1410054000040340444003103810442d102903440c03200380b103070803100030702001c80001058404c1030651241d101070b9200c0800d40c0b800910305440301c000c41d14554038007003690382078601c12044030744429419201a501000920408040f0b0042d810048803000700070890382c28000 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 595025278 1250 595024028 595024033
    0x61b04060806100c020d050705040528020a0e0a0f080105180d0c062c01060b0f0d050703060b07110f010e01200a02060c060106020705040c080402010c0204060e07090608060301050603 80
    0x81c0d82c0024001c0100300104104200848000080016941c3d04100b5403203d0194004103107032408c1c82c003880104c07040604124025011480454030307200c1da8100d07110045a0078100961610b011301807d40e003451458040c00c2d40029008000f02d155213a214060080342e110310b0082c800b40d00d0301046011006080f4180c41a241c01a00303504640c18001c44210381d038a4032413840003e0704250000020200421020b010000325090705c000c18040009001d810050f16491114504d000c501b106a04903034404d10313003a0b07907290ba100c0000079201c5000e03620141c001d280d02c1d1010356440d451032030300c402d116105003c01403103403100344003892240d441400b000003c1c1e070042e124400c041b0a0881000c4030902c2102d244199803042201d8240142c48400c054040304100b18002c000075410b02002038180b08658100d01e025501e000248a80d5550000c80b168100b5020700304640d14040390b00100d0301410207504441040e004c01002e03c280164400e42d0312080354030550311540c03141c4840d4205420799070107582c555410f5 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 595026528 1250 595025278 595025281
    0xb010e041d030408030c16060c0f08090a1202100306060e12100c020616050703020303010e091615090e0103050304031212051f0503010504030f14090402030108061b040608 75
    0x24103081c0d208a1404000e845440e140042440c00345185900070382020049800216000188440c1045514038403829000000c41050401e24001c03c0b19140c070801905140c51090140107004c0c0c00d00032505598400b5104501090310fa03c021131500c0d4450501b240503190380c18610150a00c070340b140ca001d9417030740d0703640a42c85007600003041540c0c0c0b41248011050b008490341c0c10812071107881101181000741d000341c02540381c056800044426000b8504061050800c080c8000a50102c03c0300d06580303244010341a181c6a80910314502400035003800e000441c148404113560803291a4021060040d507030b01004e694503494a0b401004080c400100030340d00500c4140f002409000c80d02c0780713001e603c1c03901c100c07195003040441041c1d481c00d440445000144880448046052150000190100350700910060820b550014007040d8541c81c26001c003c402800076007200d03008000c03100c000314003c00a64903940c4030380c03030f0307644803078040e1a603000650340d0f01c03801c000d03a0f003c60060390304171403e40d12440329a = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 595027778 1250 595026528 595026557
    0x801050907051207080102040e180a030f08100509090a0c0f0501020c10020c06120a051605030f0c0f040f050a27020f16060b10030b0f0d020a1706190b01 67
    0x140e0450f010b94860041200118201c282440500300030b20b99030000c440d15081500094240d84d522440d10865074020402100200ea005500525a00024a052021951001d10b01c0c3d59840454000990006800b4240081c1c2c440010744908400d000303080c5021826910f50011030410400c0c03041ca400b50300101c05403007591624038800c14062881340141c0f80004500b10004400c1d521034400003e05c02400000d205495500b0f2003116801024050100401601c02e200505603005c01014460382195600004014002d043c007075440390b9007540d140e1a15591680c18203122850b041c040c4a0144a040c50006202880781d501103036813502d40641c0c050500200c0d0700905c0070754041a40000d0302e200421040400480d441c4c44d2501030f90050700c0020301038501a08002d0200341c913010010805003020584201e80d900c41e513180c00700300c2c0300300e500210144652020440444055002036915045a060b083c021400402c40c2d620951001c0400c0d05507003606081501107803165004280003405100e0325425 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 595029028 1250 595027778 595027789
    0x903011415040e0715120b0103050114120c03011107030e030d0504061b020303040605030103111504050f010c020907020705150c031803010906060305100e01140a1508160f080105090705 81
    0x18401900819031304455207540c0e05584e40d986805103c400181c14441e002c1c41041c4501c901c0c0e0900e002440c00b4000c1d9454101c5483c10301c110305512501c11501c0ca846103001c4003080055403440607019009000758481c043e0004080d80000b8419004149030f0b444e00e0300f19250100b00044105040d480300d030b05190600404a07003101c4480d42c4109241c201344650030160b602040034bc0001c2c09656079650341d035030541c901045251303080310001d4047c0464040d41750350b81886105950942c0c5081d23480e0703298002548012202d5420b0240044e4000302d560060010969002c02d840040d104207036440100e41c80f100e8131070340b41d5200d2502a001030350001e11400d00102c2e20440d40d60f683c2e0100900100c0c0e40c1d050354031000104c880e958003c68580c0c2c0981c201c020194103e0088440707159038a0001c00c400348400f044000c20302c400400400007150f0b11448104402d950b044044003818803c81100e4221107a50f11424010103075010750080c0c9038401c240080c01d1103050203218841c40340003000e80000c925003400c1c0038 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 595030278 1250 595029028 595029041
    0xc030a08030705250f03030e0c031f020d0504080301030201080f0f22290a020906040b160b0106030c18030210120609020a03050604060b04030b130c05090705090301141504 75
    0x31403401003100c4e042c3c01102181c42c0454001e0150140403021a01480d0241c2111005080000207800c0b240003403000d83e40100d00200d140c1c016010603501c801000e2440c9c00240f04404214a400340362030700f80700c02d00c1244009117042e24800c1c0c80707188294480e64862180150b0480b8902c501008400024008011410f01104400803110821203002d03266950b00b6003100048000b000318002c22243d6483c060280c11015800003e902c00c2189000c125401041051141e4020000c3e40b9500140218140b0307991440349020b01e8010303002c0c0401d561200d50003005400c4040ca20b900040c55900040242a04240703840c013281d82c001d184d040001415407040d9030864441c00c0000b03038141e4820b0700003210324250004007a56035095900080c00d02c2e14504100c1142e02a4100c0074803c00309100602c00a041041042d420000207a0102d81d0b5403440d2418a1440105810440c0c002c6184c00500507029040805412f50b610701714004e0052046c115180140048103d40d9411110941d5600e00e1450030194040c1 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 595031528 1250 595030278 595030297
    0x4060e070512010e0705061e0c030f27040216030f031b030b0a0b04060e06031f120b1e070327030e09070201290f041d0c030a08030705 59
    0x454180d0364550006107a1800e550500245944540c40060119420300029024140483e1140c1c01d081e1500c081f040568015803000c3d4024100049031810034070304000340c90140c2981001c050f950790000310041d120040324400c98034800705038a802600c03440c00b03000f17a4000c5801242c2d0100500040e450403121902c91402d02c505040c1d44210007032044280c5800c4003942000742e14003041c0c41c1c443c0000d12200c5440c66102c0c1010b1b00003440300780070050303000e1040283d170001220b00c140c132519030940a005181c0c850040000000808500082c00700000020000d0b5a000d0401c1300003503503500442c01490003c0c542c81c0400010000c0010380100d0080e03002c0c12011441000c1c13221900b00301c100c0508c20350345460041d004100301420160461810603100e640c840900e100a224510b00d0380703015607026040070801c02076800c0b2078451442c151200d6500080202d001803051240300211b41540840c010300c00046c00c0030b4000d411044000782000958141c1032584485014a10380e01c001044400d90000d00c0003 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 595032778 1250 595031528 595031533
    0x20d06050703090f051b01020c06120405030c0703111f0c0308070909050f0109150303020a1203020f1207030b060702090414010b0607110a0609030b070309060f0906140601140304060e 80
    0xc80c4041101c903041c2c400d03514450380003032644806d0b01858441c4102d0340d41e400e90455000c03e4040d01e46854010a03139614a00040d0308908548880c41c045055008540e603c0c40c0c684a282c0000082c40f4040645030364551040e03500e495540d00b0722500ca4241496208940081401c64140100080c402e203220b0340d0100b194038261111688030b44501003510300540d0b21880ca4a4040e0044c082000a8032480c03480c46603036800d406a241c85c55401039101c020b001c8016111100d501101000386009804690000c00007000c096501c00f00010a041c1c02441506c1210010b032810050340c110781001400c0352102e6800400d1204603694540c0c40c0d00003078200d181c0303000c005d540360240b408103601c5100c09495198030610301030940e00005e4046c03042000450b80310200f0000403a2040011030700ca0980f80b074000702c1615001c555044141000300240c042910b0f02455240780940000911003d98003450700008002c10781075060703d90000441e104c0600c68076888002004001007030000d00c4603440010610300e203205 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 595034028 1250 595032778 595032791
    0x9151f03030201091703040209040f080f0a11070605041404110c010c0207031e0b130201030b0a060c2105030c0a090f06030506040f06230a15020a0308090703020d06050703 75
    0x120121214140d50044001d42c1d11340104404106000e01503205420080d0004c03400c1d85015000a24107110190024000a0035081e801040c0720100084600d40000000002e43c2c0e07c0003190010405040c0031003500540c043c4a4000c20228403400c00c5808450b03006199180010090041100402905070010850301081243e8042e2030f10a000f060202c40b400d401900361240307541401c1c011405050404c01c10740348400c41c183c00158586090355088440c24485100c0240c842c030059009140c03c22a840e484580700400107005c603400104030901a00c540200b40315100c0c07500a0788842000d0380609800300c2c01c1030000132003140c040c81c06801411081c0c60000c0c002a680c0f02c0d008820b1545410620000386c582c002c204550400e4042c214540e0703403483c010004285000340c480554050030340d801504070407403c6081d40719507031600d40300b02900c07038100710a40c80380c46504080d507184613040c0b049001c200d54800241c003481c00800d10404882d0003525400000b00e580c1c1c0d030500100700c000c102c001410390345c40 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 595035278 1250 595034028 595034071
    0x105040807060e010f111002030a24080f160e1b1303110f1005090a08010e0f0609071503091a070e090a020a090504050417070303021305090915 63
    0x180340081c60740b603e6120303201855900040c8016440403016090000c21a520701c105a00010200034101c2c1410005850b502c034084614054025000305600344281c0380c4650800400340c4140d502114155802c0307400020800d03200c59200d200006d61101c10030008841000460310140442e039000207a50a142e1100c008008858480e402c01e02c10000c03000340c0b43c8828401c00c16540140341410104a9480d0104451440080c124803104a02d901c1003110124058080c0d4454000f5100030b01144c80083c06044102c0d86440d03a43c40090900e0011841010041010174802061000c1030b1580c403103a41c140904d0504003a000380c080f08500300d5080000300080c010040d03042e02000d018014580c2c581c0c9040d1400ca04010103405e001d09a440c10910420049807600c0d0044400402c0b1003040d50701080595490a040307a050040d00180000c5045c00190b0f0002c01d40d00d640148030070041c1e00c5c452900c1c1502d0f0800d00a4401d0301301d42a801c10303404a000f0102007a0707541c00c0c2036403020501c03480201c1d555480d07 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 595036528 1250 595035278 595035283
    0x2130c09064e0903021e06060f1f08040c0905010302061204051c051b010b0d14010b0d151b0c1e050319030515010c0f030c0204020f0405010210050603100b01050408 72
    0x200c0c0c0b81003080e51105064101076041c000303061841d1020713420112044141e5035803500d507980603000e2403040c00500c030380c184a80c48540d4011001650034800b20958003000f03c015010000482e01110652480d610103d0492050b1040c24180d035006040740c1d0a00d501d00e2071461050703001a02c00c3e80d4911403801d00f15040000c1c803c400380d9201072075859503140c251680140810002082054929904090a26542d0703204d40c400360101541203000c40c50041c2c1d20601ca28010f00d10058036540000150300184140200038455240c078900441041100c00303660f03002c09110001c0c94210600080c2491520b0b070100fa030b07043c000c0800b00c10001003492400042d0f641e071450b641c413080703500d04450749400542d120150103118140d030044c070051415460342000300008002101307030b24004040c41000000c540506100751149a1000c0d409801195641d45801907405290450b10840d40148074207071080310307400780c1c50254600a20005c0c000b003149180d811140c8003d4066456043d04204042c080003403000401c = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 595037778 1250 595036528 595036667
    0x92107030c03021824060712020a0311060f04020f0613031209290307110604030903020a09151a09041d12030103080d021602130c0906 59
    0x1540507034100034514414084240c04c40503c860300000b400041090502c2810b02e040b414007240d070344001401010350001a0580070396807002d000350165140d0038503840d4000030360001603400b94550303000c0ea80d800ca02c248c0e035505040f11804a603200d082c000c140141089484003080301c5008018900b000000b401c9840410381d154001c1d14108030315642c1d242c44a400c00c0b12030b40901154802e0103c9494160002e21044501203585880300200000080155200b114111130446080c0242d80c130608113410020052071b0703035000036440b510b0107180000e0b103043c880c40749a040c050303054503d40c0c4061801c0f1f180840820054803060709000104280f035130b1035889206000444413152035501702c034020300a1451901104601b12140000c0400061000c00c1c2403030b055454022200e10301503030701d41076040e40100c0846000c0e0000d4105205204441c10803034141c014011002e030b199200b010701941d03000d040b114a607840c00801c9100e558800c03c502240780700441c000d18400562200c11a01d1000d03185408061103 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 595039028 1250 595037778 595037783
    0x1050906010509090a081206010219080901021c120e010213120c0b28022404051005060112020705160f0305010c02030304020a090c0c14070e01080a0809210703 70
    0x4400e0040c49245031103640d0f2900003039503c0041104503055500c00705988140c180350700004040100141c01c507803080050864480f40e603210455500d407140b0b04820260004042203015004ac020b0740001903070140098080f000803960b582c0307840d0038000b00800042450000b9081155002c021032199441d14485c40c03002030402e508810002901e1303080000361190641c00c0145411401c120b29028074401003d40158840312003055914071005002c240d207001d1030020704401c04510700300c280c21002c8807100f230503103d00d005e40145c40c000640510007108070b440443d40c00d80403845040803d1111807081c0c2c05043c415100c1d030300321500c1940504100304200482d91002c1c0310400310010500030000c003070103403850504150009604500f841da0003c0c1495246000e25030501d40e0b81c1e07101190040c4640c010001e1680c000d120490901e0700030154940741c005a010f0004401001300000901c2540012072082e00c1d03400506460412070101c0401072596001010b0030201d820300204440b4891090201100862 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 595040278 1250 595039028 595039033
    0x605031b0a0f090b09030601170a21030b040b010813030908030c0f1501031104180609030518010806031c050c070b1305040209090105010e13020408010501140907021005040311010509 80
    0x24200c80009003e501240c20410503000140210812500c001a41c541503400d080149240841050001d91820070108000742c00014a41c18500c60805176000301310607991969410710031580f0300000c2c030050703c0e6054a41c90005070030308002400c85000404502500e840f0703180c9840720356951440d080c5160852a0b0404050b00400c2e5a18034200d41002001c0308082074032010350303180d0324549501080605c250541401140c44444c00000134001c81480301d00154400010050010325090090590300202c003214a000c2080300c11140560161a0303544c81448014003c040122111041c01110048522508240001407060050580342446101c018000001c2d14a80340c20f110818180c10b03850581c4070701e0007280304103c0200741d602d80800f4641904d100782032050543e2842130106103079481d21031102c04550b00c042000b241907a0706401980c1250701c50070b10380c12003c07140c10130400c5841050b6000c00143e0301c003200004040c5070a82219a100e03019050405080c0320b440740144c00e40d90111000703040b42c0c = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 595041528 1250 595040278 595040297
    0x6091815011e05180d02130b1203040305033906040b160507060e07091a09150a060e1915020d0f05090d02060c1f11030601090605031b0a 60
    0x256882040800c0d951440a800e0858202007000030303000d4030a00321351601010482c1c448400e01e4a030b040b407500040d039015140e44088211110b00d10010107041c030f80c980c81254401c40580340144000203072410303660040051442c10440c003050001811012082e94816040700001074444401a04210a44400e510181c841407030689441950598018030a46031400c0a80401d00d403a0341c0700701520521540068002016a0400344852130081190300085205040c681c0381d1500c41e6940001c070400c0075007651480410303104c018454100c1c20750003070a0382d0440e2aa80c800c001d200d228044075064040090700226400c0b070454650328451304580c201200d4542582200403401c1c0d410003403d8000b014600d0b142c3c03c0c100390548010300c20300c180490f880c45652442c12041c1036503115012a007540b2510400c80320711000f0441c0d055190b00c08800f440084511303003511000c40500c130400322445008165250360301c260078140d041d01c07a42c10140ca0a000c11901c0f10755860942c0d0707000001d11012155840b0000308 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 595042778 1250 595041528 595041571
    0xf07060b151c1a0409150e010207060b04021615110a0e0108070206010b2205100e03073312050f010f050a21080c03040605030601030b1e060918 63
    0x1e04031041e0001c10000e183ca040c0c1c81880790240c0003010044022600810090243d05103140300c0082c1c02c1c102c18140740380c49031005030f041056004110081c41490148078080000341000121f0064655808506407801500000210710624808803021022000121503001c06a030001c6c2e80c00022903200480c0c540001d1404070360708a1702056000035035100402c0310b503040c40311b81515030094003080d4800d1001c0d801e40c500d441464192407400341402500750302004012000c020496082038039900d000c0d0184070343c045100000500600501860030154201034040d0180c240aa03103c260079000402c002111555909007aa001700e9000d2450100700c00101d5040120b000078a5035958480b41c80341c03401400c100405054042d41a8400341c411521645222150410030141d2080d090444114080013401154094200b0060b40c002d94080e0303403c1000341a00e03400d2258150540d200701078000307008020801c0a00d842001001520000703030490600000c501720b861003043d0207690030829940395450b0180c0 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 595044028 1250 595042778 595042807
    0x8070b0301050418051510080f010f0507021605010c0303092010030c080a18020a170c0607111908071701050705070f0f0c0e0c0a20030f07060b15 64
    0x7442c1040803ea91041c4d0941d180e0756a01044090880c2d01e00032800080c2c0801c1a4103140d0008241000035134140c4408828401c0c000e060240032211914500303000b103070003144000b8910324403008050360703400100c0c1000c1c0152013148012000314201038403000304200082c0100c0808543c96922100040300342c038a03804011a91045801031000c1501e4010900e060581c80170b51182c103d821030100144041d1006007a0707800f00d0b04080b0280d00288071440016140c1541034105015054100540b80b01107030903820400548140e10015040500900044442d803074480000d080c02034446a0100d066075031070310700307501700315165002035240011109960030003402070085581c401ca02e480e02524142e4507039100c004550720000040c058200c640d5601c82003041c0301d42c50318054002c1110300720710340c60030784800480c551141d2080340008020032600e4000c0c400048440300c1088141d0045e5042540061205010740c101035070aa03941034a90030000115120749074600c2070610303030508265441074904c0314040c = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 595045278 1250 595044028 595044041
    0x8120d111c02071a150d0f02090c12060d020109060807030f06060f0e0a0b03070c050c0310061e0f060518060d0506191206020c2a0102100614040207030908070b03010504 74
    0x403542401804010811700104848010b8000444034000e0007031882c1044103202c0c1e03030a41d0094008002d0030900a031042c40c40007a00b80b1600c04d15201400766612800d0100714000410300078003081f5204000d1200500039442c095100080d40b80001d0014141290300e01942c7ca903511800c0424010040404025800007800a102c02c0a83c0c3d040d031464603000304500740d444004c20309810080d0104070113017000028404180341340c8000f0100c40ba410491f1300f00d140100114440c0a5a5402072030059654100040d11201200c28031140c5110f0b05152540c01e580a900010f0034030300074071090310001c00c95071f1a88050003211000b5100021545030203014010796041c140c4402c1c2d810010f000d0f04201c1e000d100c0b8040300392554880700162320b803140886050700e8034103000351000a90000348900407001c01401090981c3d91800d90842d8104170000d0a900200d0380540180360f288a511580441c0a0502e03400a1004920a281c2501030a5541003903d0a01c032458000c030101940000040010303141502840 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 595046528 1250 595045278 595045313
    0x703060c0f021902060f0d05090303181501090b030709050c12060312070201030b04090807050a0605070e0306010314030f190f03021602040914010f02120108120d111c0207 75
    0x81c0214004010f6106101d08070000c0248600000182c0f103555151520039541c040100e004c0501640c1040b81000e0384942049130450402003c0fa242d01010180c001007003400d80c40b03003182c900e405908100f0400b02400c10807504c650141302d8120009034012040c03254511400d180032540792141403a090b2898164409092640b0941c404c9441c440031a103400c045a608139424203002428210b0100442c0c080d0100b000f0103001c0380300114860b810b00001141b13145000d1f2288404000e81d60b903c03101034030155245440c03660903600800050000881c6a210b40c501e248a2030100c3e41011441508030806620202c0302d85540d40f40c8032b000312a119009020103020510f641000e60420204042d4031400d8485c038080a4800d90301c8400010502c202946111403040710303040240100d034241803420002c0c0d8050b0a21000d0b501d081000065090404640301852000110506141107402c44050015080c1404ca408881c041006428043c003903801004402803201c010241c0c9420441c00c0c05141d90052a826 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 595047778 1250 595046528 595046533
    0x901060b0c03121003030206070f03060f1205070e1003080c101506180b180a0b040b120a02030903030c0d020c01050f240a170106090614031b0102060a18050703060c0f02 74
    0x9100190300414289c0c1e100f40b07145010f05035003000c0902100078041c0d6034800101c2028052021801600c07801034400c28a0007038045800e481c1da00c0d28a0f5001c0c2808403804020f0030342009041c00001c8100c0000c03c4681c82d003504840f8880c090700803031400c03540a24450070b4600e0000404204554011111001007445050140504c5140654000f0503104000307042e44c44218944c41c030901036603803118450180420080c2c840d225030300e1b50100f003010703803041140740d600c40040000a0214030590003201d1180b01c4440203141180c84107142851942c01903034450709010b80a014022500d2002d224080c0301e0800d114400c0550309054410b802c000c415000d400c00c00307140c60b0403220103e4507a83d07040070403140444040c109218040c82c1e030500412a039006541032908000c000a0b600719080c0502121100407019100c0d44108400c4010400aa822005015030020305c0003802054446d0300c07140c041240310003801e880d03801c5a80c0e030714104022504104c40d60b545c0d400e40b01400340e40c8000e003103020f05801d000 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 595049028 1250 595047778 595047811
    0x1814090609070e0c0d09060518190605180d0203072001080c1c140a0e060f220213050a1a030c1201060e040c0305060a1103040b0901060b0c0312 63
    0x4010b52580e1182c040c1c1c83c2d20b200160041204600842e0880742d00301c45c14102001191014680f420140c0000d848812000307242c02181e402c03411010550f119144001480344c2c050303034000d0350b503080a058000d1400b640b800e04a03040c0ca40c0030006114029200300a40c0c040d40c0d0316940c03860151518564480c0d00b00f0303404ea90869101c80c7ea40c00030f20094002c0c1e0401040c3d5110031451281401d106255543c0c12031241c24403001c1c2010030514505d190141012034800d1200344003040e4050b5681d44101c803c2d20101214030302041d8214950201c032000b603111110039010103500c0307801041c215415000d0611410b6940c0301000b8507081c20303104070f514450f10851400d05074a68500001e03510046a00d0242c451142d419510042510940c4500300400650004409a14043c20a41c580d1042848140d880780a42400603210810354858400c10368a0390303800c24115103032511b0b41d02d0150401408d0040a65941c1c0d00407800a20300d00c064000c1010b004011139440c5144020b42c602e054010f080314440f11038040 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 595050278 1250 595049028 595049041
    0x9090109060b09210f07030c0501140313020105070b010e0f0c0c100509010207020916090803040b030c0a030b0a0b04030606080d081801140115020c120712060618140906 74
    0x400c0f10b003892400c4918074100b400e0b4507003500210070712000b0111644981030380070044000c0802c4001c1124015820400b0701d41d502c00040d1a00304c41b00b400c031180c4540400c00103103007400b03840101d0041401854040e0408041fa5200700b001c81083c3c0224402034241c504001020300fa152440d41d1001c05120843e0605182501c11651250115204425591658001140c070002581a200c1141d00107144145600b00100c848030019000c503007880002e1141c0301c011859180006c02c031021994011106860f5035a981c900c0315494100c40b02c01c104160f144d0003009003560311502610090b028003030300c080c3c0d1039141d1301c2c200e012115550311a01c0d00b60068890100c145e904102050361060150851400c566603000c00d0500400e890340d950001d584010b400030413080d803080d001c400b021030580c0843d41680078400412401c10071241601c0f52507132008405122241c1001d06d04a00030740b0909005c10130a0315090a03c40140e000c2900c2000c00d40c1c0c5503401031002002c0e03094290440700100140078242000c0 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 595051528 1250 595050278 595050299
    0x1d0d030906050912011409060906070f0f0201021c05011811030112020d0b0a02030f0a090b06060a0201060503030403120906090b092b0302010905010e160911070c0b0909010906 77
    0x41c400c040c01d0100200f0b41d209140c69004820003584407840c0200a6030708101c0910b0401d4a0545240340e41303106000000300c0300c0c3e8000070703d07500884039a260707040000300d0318008807240d04c5d0f1110110115502800311000c40701c071480d0049504ac04020001c517696040c500002c46120460102d06101410820311201c041c500c00100d03030548402c020101c02074400c60000c1500c802c26400c0080070040d9500801c4080c50f460f40c040c6000b8420b00c5000c0505d5180c0415041c103955245c0d201034144030800022520034941075008000c010464000171030309a9640300000c0c216042680181c0c1d0450500f511101c0071076000b25604081c08060030041081c0d806c290100500e4050443c61501502c02c007101c0034003042c2c285465000585612808090030110391400a0113001521012507103503081c000060151700d000b041140d2103c00ca26002c22410b850f00d6412805807000c00d030485d1070a141001008003007546806000003402c0c03001407050b07440c0550300c1800801c4105a1010700e0491078001d040c000c2d080c50 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 595052778 1250 595051528 595051547
    0xc010315050405040204060305030a1205450a0c0503010e070e01090e150a14060603061e12030408031305010f090509072010110304050606120304090c1d0d03 69
    0x70b80e0300164a654a101017002440650400f03040c0c0c0c4404110464801ea02c40300441924500107400d01c03a58a41102400303103404c2004841c0240652a1001c0701c8554461021800e41d040c1c0d40700d58507999050300d640d24202980108207940004003601c0070700040c00e0074001c0b00c0d5001c0081e4010261640f412405500b10001800303030780b060b05e40b160441200d50900308400c0da4060031742510380880e41002801400202500081100c2d4101c0d84000134000c0d00e0172806aa1184101600700700e00709a0411b01350742800c030403440e041da0190900000018090040001d8405003500718002d551381c0a03000842c40026016602041c1040b11400728810002d6202c5080411144d06543c80201d0b519249070a41e000d4180196003909000402d45482c035424001411044880c0e02e1007042008182c081e41d0000c030351004443c0070309580d020501103240f504006003544140c0d409442600c0c03c003a140c41d40c001c00d0312381c1c100880d03001130040f40441407a1100c0c100c07030303600c42c1d00121003400b01100c065a0107414101d2 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 595054028 1250 595052778 595052789
    0x1803080105270c030621030904090c0e040602091201060b0a03021c0f0c0e0901050612092a09010602160e09030702030a0f050d050c03120a1811030c010315 68
    0x2286035105240c1c00c40d00b40a20884001d80210758540540811943d403c11a44680315141070018070b101d103441c44250b0f00002c2d8076500694a03000e00300050102901480c502103803003055400d4002241d05110303000a005520469016030340f1440e00d000c02c0006e441c60802d01c4101d134074000d0308000d10b2214804880780c010f01d138140941c44140c55901400d81864203a960a5498148250581c504600f5400b140c10040c0649500b50511741c071005201c07000d2005d0066a40188040000c080c2c10083e60a441e907000744510100d03402c1240d42c0308090340712494a82036405404000117850403034541072003d80d0143c00903200402c1c001d02c0b20314071910701c100644035920100b601e060204880e4036080c4115a031964020301114400101490710000a103590312040d281401110b0f12b0107060b900c00c40849010b104034200550400d400304040380004c210182451680584d18031580690080d490304087c031f828020460302c502c6960560901d8140030010a0b00707810035140201030700340d0504c02e1242005684 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 595055278 1250 595054028 595054039
    0x10b0406030e16050d11042c0c060706020d09050a030305161b15060b0c031804060810020a0207031a0921180a0518180106030c050603040c0918061803080105 69
    0x45c40d400d02022401e030a11407a0b4020381810300c2c2072000c078403104003202e010610580701c00795845018101c54803200d0114003140d00480070045c002c00700301e4540151031188005200010484025a00e051400d0300003081200401d880300e04100b0344000540702d0850f807100501b8094001c1408600003580100034031402001095825510000d82005600c09006482ca00060329a1400c0c4860042e5a03034000030070382001d20050080320342c0341d0700b418011003046a40b042d004194000500c03140b100030b900131035100411803041040000c0424910300000d10914840234460340039003040840c0d28201304a00d0300c0681000c10b00c9101002403a880c0040360715601d051243c0d003602104240000b0151b2000744d1080d1b5004107a9010400b20185010405008003400c410109100056441107401d81c3c00510002d04201c1c400c840801490422000445d0300910403030f46c00c001a6105c010800440e001c103451000314071280051602007000030702c45c141c81d219047d840586001c54594009004280502a039800f90 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 595056528 1250 595055278 595055299
    0x80601051b01110c0a050705040b030a230a030306050102011406010909020f2106030d08070909020a0c0c090203060a09050103020904030f02031c0c140a09060810050306010b0406030e1605 82
    0x1600294441d10300f84808020386942c0c0c1c10420f01e600c1c1e4034080c0c0d40c0192198010900001844e203001c4c4103c6550410241c003030710050225459004038892000001038804401000000451201f440042c407031074400c0c0c43c0051000c4c1800002030840c1c0450500c03003213821b00d0784284805aa00b100d03680d000c903a806038015075102240c6000d81050301030b51204160401e800e04034030100500c42421144540001d60440c0c1d09400c0c81c010440c0c0210082c0d03041c2e80481c5a190003808545084e4004011485840c24010206519956404c1e59440d103613103e0345c106640807040c006c8616060304120020304a0349400c0c0941d50560300000c542e070340040c000409200074504a4090f190003842a0b03960750101c3c0c803030a00c411450075028005006254115000110000209100e420f90501910400600c0380d039030b2808641008400e842800d030192a0400354200701c0c00005182c0c1d01000303064080c1c00300f007407299140d86c40c024020701076409001d65103030190020300101d50311140e19104941260340441e5056080c = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 595057778 1250 595056528 595056577
    0x2060103060c0c080403060906140f0a020a031409070f0602070302030c0904111801030c06030e030921070b0c120405011e14030a090311070f030f0501110310140108060105 75
    0x81c60f40103200402070301c400301c0c000090100356840101104c0c0502000d2080498803070103000e03001000c46600c6040706d0380f1000b00d8201d10581e030250030300c509a4180052894050405450b40030030485844101d548030140c01d01c83e108000304000000c01c6030f07000414089042d03500207500d400c0c81a150780e02690301000064240440c14180c1e00300340030701910130a0b42900442a00e0039580003404151208000000000340c940e2103440740c44406540310002d141020b2524041085410414135140385400e8219200000100148099001441e200081c0307030366030354800007807800c2086e00300c0c62a035005010b01042140c0d0b604490f041e0b040c008180009100c03202d080b40207603070350842e040b511401d00c403010040044440403640412030702e40c044d4440c011002603020205030790320b800340910090400200c2080000892800300700241e94494030000c281c1c041d001410049680080740d0b0840650702502080091010410403030380f19141c207291000903864a540081c00c46c2c41680ea4008242d042ca843c407052 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 595059028 1250 595057778 595057787
    0xc030305041a07050a08070804022209020619030e0a0203120d0f06061d0f130e0a02180f0f22050f070303210504020a031220060a0507080702060103060c 67
    0x1249400b042d40044182022600100b1607003000045002081d002404221114042d0300f929100e298000c0c004d200d50259007600104c085c149110706d10446895554040040c3d90700d60141c1101150034440308000e1791000f8000741603d0501c89400ca450b009058050050380b00072903405000300c404c1144a541d102c00700850401032140f0380480b2542498408013080c1c0d281e02c40604510711110311202054600700c90304100084250b01e20207503018100300d14804420880d034021802d0340011200b41d0f000e288aa4003c1250742881c84003140304540d42104211010801108450b00420080c40d40401480c2000140b00102451200c071241d82e861074440200b085020000e4291404140080c0c800c0c41d9a241f601404000d05108610030710b10b0409110130007040c651203014410340e00117000491540c034580303903c401c2ea03081e00180f40070840c0701d91070780c00008042c031620a80310013100c0090420780b070096049003c4a0001e0401c0c800c0000010030f010303020f58005020390540390401000035500c65007600544 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 595060278 1250 595059028 595059053
    0x611030702010c23070303030501270e0a0803040f020307060c030c0b0c0d020a0806030c0f130c2d02010b060304331107021315030f1e0b06040e010c0c03030504 70
    0x44d004401c11180d00000500441d111007200d1181d00d0a22550f600c17607400000b00c5000c9800d121407404c02c1c003410401039800d9049502107910100544d10700c005113031940003c80c3c3c02141d040e110100034003c00f40031401c04100341d40050a0714a03002c00c00106a9400070700381d00030861b01402c41c0c407448002c21803c1c0c02c0034044507034201c0602d4086540d0bd510f100040c144a204445052007401070350812204e81c1407502d6a04e45003940200359500c43c1c00d444d5442402002e29034800001c104046048105880c024200300b25040e2403006030094240501d103009082d2042840000d004150510a100024a64441840d04003030110200c07540501641c058400c03904034243e90345200e03070815460144044034100205941c600035071741005003104059602081c2d07a1180241512510006810800f00d81c480320300040381031041500000040c030a0301030b20300c56070340361006494600d4840c05114080c5818800c280c0042010270082c004074800d0300010300120500540901455255400902000403510810 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 595061528 1250 595060278 595060313
    0x9170918150a0e0118021303080c0a1514071b0804140f03010204060f050f12040c0617042004060e09060717090a030c03021903030509070611030702010c 67
    0x15950300d000ca01840c1401800740d4840d015070101c40001c1003985403007010314180c6600f0130f03011044004182c400002948038500110300e03d08070a07004030018490400500185058030010300000c185030070120f0540c2c0038040c2c0909050f00e00118100100c2c015104541e21610034102151142001c03824a0701ea06521800180014800207020411041d540d40341c81d030421041d01c010340ca580052003410700304c0c0701700d000d49030109510700702c1050210b00c03603402041640152440f4034100803100b0312100004d202502c0480350f20703901e458240312442e400300031501110035022000c10b650506807170b20340c035080e40701c0f07035220b440c140d451485181174403560007500090020303464903007003850141c1c803594440701c094560070300242442e40c410403071040c0005443e001b80b5140380680b90806042c2d074184c1325440e150b9011825802000b5080f41b4950708100c0400d501c0c0d0190b28040b82130b01e007106c881420808203030843d80500c00c05d090072000c0e503040081560341c969420b0034240815000f41c2410718080103440c800 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 595062778 1250 595061528 595061569
    0x1e06040f06170c01020f03090f011e02010506040c030207020a0b160b01030b0702061f06080a090624080a080d051b0f070c0509010b0a1d06070303140a091709 69
    0xa18520140b0003000c40c0e884403001d9440880c4400300481e200c0c21100e0406403654024083c04c82d4600d801c6070501071000d0141007010b000c0e180c0c440c1c86036601f40b00080703007070150f50364200b048080c1c2018000c40e0b03840c0000386011454121658001800031000d030150a1038480b021605a0f10480c0081451030045d810241c243d08640c0d6a18001160740000c44003200107000c2c041c0818030072082003000c00074001c4c0c00d101310030006041200c04c8810440040643c42c40b1621092a0390100b5500e03c1480780703800050b46440050381d6001400348480d8000d620042680d41702c40f1000000c01e005000f50703804815500c1c40882d05d9200c0c0508900010800d2007513802001c000200c54002450a06c020030703009104040503894070742d41e8020000444000d104001d000c040400459007114803480045100d0a04d4070503903c511140d01000c9200791300040c601f200400d5a038030b440b022a104440f0010344c000a0781e0130901c80b4041035914070f24400041d054201c4c00000c0490455040e680b661811000d009642c04d8 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 595064028 1250 595062778 595062791
    0x60e0f0a0b0604110702060d020f0906070614061012021810090608011d0a0b1201050c040e01080111041205010605040c0c11100806100e03190302070b031e06040f 71
    0x14984aa014250b0b61a8400d07840e11010010101d40300c0300383c401054008020f0760405c05004100310195008414400c00306c40204018130544d95010702405c10107014000010340300710a010004244880135101c40d210b0074400d40c0340309103554480107602c01c05221810141c0c0f140d82840003064207074640c1c0d82465220a112500c01d003602d9002c600c080840794a5030b5290f4840e40d890710307440b0200203003a5881005c0c2c03c2080008040381d2981d0042044d1003005850307845c0d03083c5501002400c4910944081c6044180081c041101a0300085068050400e090007080315401c3e920794000980b045100d40200000d0114012051010a40c4007100520b000380040c06100000c04009080c041c5407038003110103001001010b85c1c28140103000e410341444644442d4499100c00e8100098584201104001c01503c0840281d05403400d015820311075003100005921049180b8000c5d0804440d9003158120700d0080c01003040903092403540c448034540c170843c401000c0c1c868030b001c0f501412006031003c0b2102d04241 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 595065278 1250 595064028 595064033
    0x1210230a0209100507170a0c17030a0c080915070c14010518010207032309060f0a030c0f080c071a1623030105060a020123090d050301050d060e0f0a 65
    0x1c0003018190b1048a030100c00507003d0300141c0f428020a0409003c000340c80c2e100302011521000100445500c034100050000e0841d80c820000d500c491201e54008c0c0004414441a04030500506900d0301182c14034180c0c0c1d04d000d011255981c2030301403404450305900404108464000c0c4040e000554020070a0360144152402d0340303002c1c10040da4410781d41d071344400c09600d50380f1061081c1e9405940c1a1344500180740d49988248190070b404400750500742081142400c2c03aa03c080080083c4404403428648030b805840d0060102c40c0346611402c140628000001001a40702842c90351220094a106031189524100030005210152040c030501d514603040c1b202e01038503401c1c1c4c1c072030700c00003507484652103121854101010b002d0f07000706024100c0d050005028514240001e00518102840006100365000c2400445280d13001c505003142d400c11014060414005e201c0c0d54803101c0749040452555250a0103d0001c0714800070150456a480f106ca540700f20040c07080c014818000c1c1c0c111400c443d00c2c0d0 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 595066528 1250 595065278 595065281
    0x603041a011401020709060e0711010b040612021c0b0103060e030904050705070204110f041721031005030a02130510080709060806090705060712052a0105061210230a 73
    0xb1190342c1c054410941c0c0000d035410140216802e54004101403541034031250400c0c0c0e0840d94102208900f5500d40c00805981d440700e11a40d0018152072004026101090041c403000742160014020b0122020303200c1e0b40404c8180c50541c6c1140d5121100040e80e1380f2921605003140904c1000a03400b40c2040240a1041c0d40a0060804180201d4003004448a8060b6a0940703200718980300d00e030341c038090008006100070303001c1141c68900002d051304c4c0010503441c05d52802003081520614603050100520004110b20b040004c0030780300942c0203020300c6071260005056001c5107041528203d0302c407400200358204a080c20700c02440c481080700c9a090302c941e05007003d4015801888150310641000036012a00068098215400a800b047c80c00703d580d240c0000710310f0740201000c24810204908142c0740740008421086000c0710502072021104240d40c2d600b5600c01410040c0b14000c42c500d200e011082c0400e0ba01000d03410320b280018170303401140d5011084100c511001800300003180c00c100440f044c9 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 595067778 1250 595066528 595066559
    0x120c021504081b0901050d03030204090f1d0102040305120304110d03030e1b060f071406091506090709052b06050402010201060b03070507061509020d06090b0607110603041a01 77
    0x4206643c03107060500e8072140070420800010340e000862000401c035a0916400d80b8010a0080c50054601501d9184800036103843c496059003036903841151034000c4056040d440e03031003080781c002585050f117152150b5544520a10740c41019000000c0400c00300440c0c3c01ea0300500700d802900000c1000c0d0203080c0500101121565412940104205401c04e10b0100b06545880c05c03000700424100b0710040342880040d04400380843c0c0a010108042c04100c00800c02140b140141e80c0040450b40002d50340001e08010140c05c90f07014191000901c03820303503000302110045c3c5106840e54001d070031034800c082000305125103516040d984443d00820620425401480c8514000c2c2c000b4010760f941c1d508814050b20045480c90000b810502903080054901e402410b0905400c91700216030a0b15000448100d07844001c0000715560b80700c0c0c040011144501850708051812110941020312035180c8407910400c942c2e41e684035000c000005402c0155074204407004041d0700c1210b4103590385440d95100c2c2c9105 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 595069028 1250 595067778 595067789
    0x10e2e09060b070218060f031b1806012709020417150103031704020121050403020d0f2a0f0f0605131208060a1a2212120c021504 57
    0x1c02402144105650b01200c010950141c110010841d4000ea4100000d1000e400e0542c800200e8049000a40d01044801590050381040c071205c0710a0800b00301030091540064084811020304000050307800c841c4480f00d0804d404000122054202101c3d0b80e0b10f1a95007090255905c0403130045101d4101c0d2104841e10304d001d03000c0321031510320410228040042440000c0005d0b40ea4034000030307145120100c240e00248103040100ca4000300c0c8408000a00030707003941c031042030b581d4010403082c0341e4100000d41000190341001070b20308016400040000050503189841000c400070303140c4640ca110141c0c200520303000302407142641c205103804018086c0c0d4420035207526007040c0200d082c08140103800741c04554800e401c514020910744094070490001450603038404800c540006141e40c4141d02510803200c41001240e403182440755050051303626414003031701458516018000302d024656030251882e006444821f0b80001110200c550020120000307403c0041054441d040d0300d2088007030016200d = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 595070278 1250 595069028 595069031
    0xe0303012603090904151503200a050a05010c031808070e0703020f03060907050c060c090301140f0a0e0703060609050109060611060f070215041424010e2e09 69
    0x89030100030b03601e000d40d111859200307050101003000100208002402040c0d5610080340d21000828801751b24846036000355481e5011000800d44502c005100c060320030801c07603035031088a05040100c1d10300442c0c2c2c041c9034140599220b801042c980198800082403038030300000e10b0314503200d80409403680035511908162844441c04030b15218024003c1e034094001c140c5440f03003507950382410401181c00181540050000400c9091505507060050304d210707402e0100860303980c0b41140d003491f0840c1c0da00b400c0814040030703080501c40c0094400c402c90790042108400030034210f83d0802c031705040c44c0b041c0d0b0008000c54271f820000264441c007a0007860484905180c10042c4540e6001c0542c0d4201308140780c0c0c202a00480005041e4003405590190462a10720494020316141d043c500d000c50802d80d01551225515454909028400c20031198841004402c030303000c0141c001c0700d081a168040c0502c003540c0046400140c40b5074020000042d074403901400c0c0901d9070000341484500d120203409a0800c0d01d = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 595071528 1250 595070278 595070339
    0x31505070203030c0d021605010216050613150e1e010603030306140d203f1908090a030b0604050a0b0a121401050c1209010c0e060a030e030301 63
    0x1030380044152440340004500740d620f85042c42491300d0095004c1028120084059003801c404500c0c01d2004d0300501c007200ca8000019034403410154508a4010714549600940403065400204c0b03404c0709a440c0140e948010540c2c0c40c00709812402c01128114168800324601e480a00024054003c5011280a62400c000644e01c0703003a80e030407031280c0700ba20681080e42c100841f80001c02542c0807000c50003a2640b0042001310980004608417414003606641010380d016084515003a15040d1314202002d40d2071001d4844c41952054071410310144450040d540b5001c1201800620030840e84c2c01c3d01d0042c0401d220030345074503080525034400e80703006000302c2c509400214001c60501c03624002c0031004044850880c50b1034000c010080300040c0444940440b2201030b030203000b0074003801380921344485031541c590151031081d22a4401c028080640c607810400314a80c216084407051044410585166036181c45421055004e089d030ba000c0d0704150b120010002030020101c0745141c1e00c0560400d81034494 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 595072778 1250 595071528 595071541
    0x40204120b040b160f0f02011e1a090402090f070903020301110a0f020724020106030f0b040227061507050a0c060207060201020403081207021014100905040f0204020d0e0106031505 79
    0x134201c9240889021410010003015500d0086029880d0b00c2200e1001040000c804401e83da40307020b440036200601340e1541d0713680c2e43c15035a1444c0208000c0090340d8101746840d054001408000010700042d240302c0200022814082c0b0600d110300165402030002d0001d032800b01165040380c0c3c400380380d1400007408100c180c982e161001c03d00b101243d028040c050034a801581d09195003003170109420080d59038a8078008001110f14000214142c05054681c06502d054018040031040e10b0701c0e08002d400d00103c64039041c5842000c80d580080c4e060314035058075847d82249200c54860300e04090f14030310808421800304141100890f084d20390720f6080c0e9200b00d503503110030303801d034091400010004482803144044541040003025808141c80c070465102098440d8220100c4041c40c00606880750780740200b011441031070943c1401805241e00800040c030301501e48812841c46481e00910a503000524016090703074a4001ca014000580d000f0443c45a0701d1410005410301090000806070400e40005c0c503 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 595074028 1250 595072778 595072801
    0x3061802150711120c0d1a0c0301060f08041e1103011a09060d0305071b050109150c030815040608010614010201060608010303050702040207080c10110a090311040204120b040b 77
    0xb080f6403055286420000c050200043c040740e400c50390701140b05a4690300c04c0c55681c050400b441d2405688100e007220401c00c000c5000010081c41c043e8040c408000411075143d01030094903a22403a890040045e41715864501005811050f6001403007000000380b10a02c04420541a0411400c4008004801000ca521040d01c1007070381c000303a4445aa00300003030300c9003001c041c0584514030900c1c050b407601c02c03d5580c0d610300d140e81405c101040901014180b20650300010440040c00c0c081460b51900d00e803070b250080c00040b495800034104580c03940440c042c41c0c0d090104540e9124004d00034444546c0b82c0804074003c10080c030a651048290140c2801c040d401842040c060750003a5544c0031090f82035031400c2d219580000c0c000c076001a405c00c20800818a0344016040311440030003d4056410403026840560b00d007041081c80101c41040741e111000d411401c0ea8040300c0e400b06061103a4080c000019000740502d42c4400c0341d0b01e0715042c01004000c0700d041000c0c401c07072103031070f03500c005c0d03191060b626a = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 595075278 1250 595074028 595074037
    0x31201060f1106190b2403011a031b0d0f1e050109020301030c120302030903190b0a14070c030c0c090c090b0906030c16120207050a08060f0711070306180215 69
    0x100c0e8040745030101221482541003101c5c40d031000b60510750741468417040c0189444000c0c1200e0080302001c801030081d504440000240a807004049605604040b40302d004035142909402d001c400000980032070102c02c40c2c100340c00703469500b00700b006050620512031104000740c0e10500d06403481d1100114401c8818820340f07050b01d070001001d4000504140161045002d442416000e61005124108480ea001c00502d1740d0028202203c1c1e082108500e4807441902024060f449080d0500b440c80c201c00744c030400015841003092a081d815500700341415585031001c4200a081c600b42030201145d0b10b540b039081504c006075250380702e4699550700d00300140e0b5030040f1546030350300400802c042003100c0740305000707041c001000360307160070301520190780e01900c640015401d4005a0001c8a0800061404007010001400543e02410b0540f40c40c41d1110300242004000c00140b0075051a00392515504000b220080d40c0d011030100000444000d028245215038602240705820346030785552540919403e55 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 595076528 1250 595075278 595075291
    0xe0106050d17130b1602010905010e03060402010810030203030c0304050a0501090e06010e1201090b0115020f070b031810050610051c0f18061e0e071502031201060f1106 74
    0x40d24030440003030b02e200f035010145054560304454030120b1200e0031a4010010722404407100300d840d011600c0058040c2c42075911860501000880c48070311030b203020444517441582441c003540543c0c0d401c1c0d000c440d00a000e80010750141310215560820300000402801510402c98440d41d003203542d80011500c011680c041e43d00b444a80b400131900070350044082c549012002800700080324061040a0700b1200c907008141e0302002c03250010003849803401d4600c10050554030190108600904225550300860320921400d1a000000100320104841c081c580b410110340a44920301c0900c0c00e400c020b03180a0b11058840d10104200e0560240100d044445810a56030601c100800c0e4000840080070307000802c101243d2510f10849901c480000c0c1c3d5070941d4403e410000d101c07400b210065403410724001120580ca86880540a04608005061401c44407007410030381c1820002d810403403c60040802c40d040c1c44200388008103400350400008101d0403242e035110040b0031040c0710b00903a2614160f0380c2 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 595077778 1250 595076528 595076543
    0x207060c1704170f120f0f09070e071b0807060b06031003150e0115060e090103030f0e040b04022a010c080f15030d05090909011a190806040c180203151e10030e0106050d 74
    0x10042b00300d04040302d82d400030442c200100f012500d4008564450742240c021a1050b10006000303041080710301c9000e2200405440d010b0440c900401c0450100c0700d00c0c00041c10450b00a11103001c0e007010380e00204402c180c20002888880120407006a8492183c000d0102140043c2100c040e5400c000d0019812a078055813028031200c1c0140c2d040e84e010044050381500301d5241c01c0d408806444070300040003080784d0383c92510a49840040000c500c0c1d0800c0d0f1080459905003c5c00004007030707221080d00c0d00320594203141c01c07171a16842501903401c418458060f40501800ac0300c403600a402402510105100f0b0340e1940084c0c1e18100368070300302d4004880000701424101c3ca001ca4900b07000e40720780e0700c041d0502d032000603454132544803602c1d0620403107080716046d18240003070291128111031403413840184001942076081c200340c00c035402184200d086018002c0440391008482400110003103038400035054484850008070020007600005c13002c2c0c0259800c1041c0018241090702e07504a81c260070681 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 595079028 1250 595077778 595077793
    0x7050c010f032a0e032509020c1b18010803190c170a090e010b0a17040b040303050c04031e02030c030718050901020c100207060c1704170f120f0f09 65
    0x8400d1807483e451030b0344104100b034090365851580c40400409042c001c0c3e0306030880d090a220180c444204506411116080f401800380b0f403544000040d13000e4100761230f90011510322112102141d01d0382008003c155956408000000300b001e40400140080030917692140b0601005e16000d441b25406143d00600c40502202c009444003040d6010748841001442c040041998844107140e0034031007a040741d200c1c4800019190001504070f900c00a4208522420004502d03050b00c40d85201900140080d0a2649680000b814603504000320740195501c440880d608082c403035421124040c070307000300300e01920170300d8003265a52034005842e4003107403c0c036030740444003130030700e482c0b18001d01005010307084259001d22285403524014014403502003090140141c030b4942034103105c0107542001d400d8106210f00011560f02c807a42e015101540a600410140c0003902d040c010414244a14044007420b81c5011448180445941200038018400910201110345512a200b00b00341000e43e03035118141c0c400b40 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 595080278 1250 595079028 595079081
    0x1080c070b0603010b2e17150301090f1b080106080a02040b1903051023071803060606030e060a0506100813321609020906090607050c010f03 62
    0x1c1d00e5640c00b80d00035001055109210001c01c0800c800e07929004020410600c425040c42c0c1c1c98100112031140741d24002c00360303141c0308200710f8102201502c401080940c95102c1744683e142500803001c3d65501c08a26600502c0c24104201c0d00048082c4181c81d04560781c000140e2000b0502445040c0c4654002034040204a5800c0000401d00400140c2d0001003040d034980700040ca0b070780007000860041e00035190304085a0a880200c40c00d80d15503150340c2068030702e0485128000c144440d8001d03031904101031409004070f2846c0d03409205910040401e41030060124425a0540004004c0c0401e40c0850b0019183c04101c2d0701900c1080303a85036000003001c1e040034000391103907558076042019440382224202060301c840300c501d2021044140c95000d244000c2140c4100b501c004009a42c040d03000e17011b0640c0e40c2c5694080e16189100f600400750300072030000e1309032703880030304079035800b00c00610a90b605c03100c07460503a8480200426035070200d040e43e16000112406806160040c0c01d56034104c041c1000c121 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 595081528 1250 595080278 595080293
    0xa06080d0212180a050604090c0215220201170c0a031d0a0b0408040806070c140f0a03050a0513170c03031206060d0b060703020a1b120b150d0606080c01080c07 70
    0x1030300400e90001c142140043c45c5e0316000c0060000c1d103014100400c50440d00d90029152000d46400f40b00f5000804081201c8024286140045030700b1038801400309000c1400103c91031080c10b0869115840311906100d040080c00b0020104051561018404030001d465551754445480569058035000056820300080180d00800e80c045c0c4111401c900382074460a003a442c00c0c0e01141c1000106d09851904000d20207040c02c100650441ca00040c001d0605081c013a40c9c86010245c4000c0c24000c000c01d0090407240148280c0c1d000318211500c0c0c412040c2e4904c00c0000f14511004495018020104403025604000c800c0b40d40102c0003502c0320031551150828000e142d4803019580840303d030b4450401d1016500e28005010701806a070040203284264104510081511607004c0002c0d10508000c010b100c00c0080c0202c503061f001413a11100d41c5c0c410300d15021395907200001039031180002c0e50340000c01419601000542e2034800c01c541900c024100152200401600c10300c0200c9070074030810000a510 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 595082778 1250 595081528 595081567
    0x9090f0601090906021209010c1d01120e01060504181b0509220215090f090610030e07030209191a0607060c03112706030c0304030c050304030b0a06080d0212 69
    0x1828011b01c0d0200030181940002e109032580300299460341c0e0300002480e4403003400c3d91403441c840361132101d000c0d0603c00a490900c003101103940d52911480b0601a00e2400e40c070220081c0030280050040c1a596503000500320101d40e402c0300c1000e030344078404200c0451000c03224152003000c0c240ea529034580a0301c01d81e000e0303401c21031480086022014ce00042e1a03030104410540110700c00e4589a01001d8200b003146070032054030900030b02d400001c01c0700ba07a49046400001603900d04002941c171206030101810040b5036000650040c000300305000046015611030134404c004103070704015452050a8014121201c1308601d0380c04001801081c0105540da401500d8a06040c2000500b070800d0345c40742002c6801c008000345c1100840e1084103070b050403500f80c0071003054040b1040740ca180341c5541e400320f050001410240400c8019a90700040002c100102c401660304018020842c1c034015075001c0282c5190b02402c2050f000d252000d100c00c90000440900e4601100782c1c9a0038080f0085070542001030 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 595084028 1250 595082778 595082783
    0x806010b070c08191509030806060d110c0f0609010b090621060a061e030c030b04081606061419060f020309150a030c0c050a02011b021201050609090f06010909 70
    0x10700b07aa00040390b01e401c100311910000040c0c0390360b043c01c0d03950410951180c070f01030744082070600f004a8000007990066503103a121100300c881c951180d458503440802007221240d000007126001408803110080001c0114107400782400304c179000d0392042e00140c243c03500c407425960003c0399080803030018a00076943e52507c0402c04140380c64030146011f4545056400d40d18580050b0b40c4031410f1008030600c00d0110f40001c440c3e60b85500c0030b4910395811040d10024400030786200b02e620b01107410000440116074280c05110b0b07100003a0390441c24401c00404407886403c401c025030342205074a500340051000c1c184d44100510801c110710f080c90aaa45080c06c2610700d0031800100079190040d0340d41180d94524003524001642c560f0010311001d81210311200c0e0010610200e4604640000c9000480119031a030a1a1904000826502001000c801140025400007e50ac50308083e07100c150b0005101e070034211006001516400c0c841c648a8040492030314964006400501240a1a41000c6252071 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 595085278 1250 595084028 595084043
    0x406050a0e040b1905071e050a05031f03020a060810051203120603010b0613170307050a17090d050102031005011b02010311090307030b071107060e130609181502040806010b07 77
    0x2c0c002130b000710480b03404483e550041804601e1014803450510000740001c1140d092651070406107103009046070000074001c440003c030800412510301c60340480c5000a42d4041d0088007419100c800240c40e00208541030010f0b503800e104002558a0701c0d04811010000c0701019510b03003009820728000ad084001c20b03a80d0550b4940144c8c8006803600c4005010003c2c884031544038107802c140461500654240000c8081e51040c81a8008034001140355480e140c0c0c0324030500b02c0480800501c1c0c200340a56400c0552000c4000741c1c1c5e1050141c19001141300741d6240d50140002501e400c019210340a80b018030216000b500901c80c1c1c0154020344c089004281200100e81c2000706080005e0b03c1c002c815082218500c0180d402e00606c140c11041000c1031529501c0070740b42c500e0809800604079480104018414800135020790000311241d8810130140182c007405100c3c0c0a0b8010b95a10410806142119032900b0b48500e83c1e00d0789910320a55082d10101005001381d0703464034403040c410340c02014041d42c0300d0 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 595086528 1250 595085278 595085311
    0x110703051b0c03120702090907060516030932010c0b06060706020c010203070c031b26130b1804050f0c0a140301081506121c05040302090a0204050406050a0e040b 71
    0xd0b035080009045221032141c4c05036071112544184510320401034034130b401c10382c0034110500403072f170708001520300b8450600a485012251303414200d44200c0654800300310212108083c5459800306490000102c0c0c1c88107040750424040001151940c60340031002e00f802c403908020480c07500d000c0005041a40c0201ca0250528004440c80e900326841502d800000c5240c1c100030008142e0403841c07140307285006550280040301c81e42c40f803030380148080046c80381c43c05110b1104d0085980303d5056072070114440b482c110785d80340c403000074441e25031008440103e0042ea00e00548058900340c0076181c450103600c5080402501d07541d007810400e4000180e80b000f40850b08403e07849419812000d10300801035640104a805000c81c10664054005400107004141d94040d2400000001901c2e11001d0000d41d4442e02a560443e4100d403540a40d0300000c1d4001c50040c00d1203020005900500262502110b080000030350b10070400c0552602031042584048030640001c0101c4c49840c2e0f080c0d4403c01e440ba211f00c40 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 595087778 1250 595086528 595086553
    0x3260a150902180901050108070206061011161a0a050d02070f020d06050f0a0b06031602031b01021c1b03090611280306061d0a0b040e010801110703051b 67
    0xa0f83c2101e4440c01004883c01d984160381e2074480308260042c4000c0c01d200410f4200f0910003500c907100104403901460784210390001c05c5100f00d8024018468400c19551086540114081e1512803032250044c0c1001541130f40142607240703000c036015039070207465480c900941300348054007a4002031000e03282c4100030f245840140e1034001b051030045202d510005003910782400e5000c101e040150901640d00d2030906520901c0c0c030340000303c030b410420305c4000000400c9602c070100c5c694441c5000b0302040540d0010206c0e284c02c0c054000c0c110b0b08034082402e48011072881000c80858580030b283d920b51882d0740310341482035070280d445500c1440c00798a000c11540f03d000e01880c0301d54002c8581c840c0545590004802c5000d1098020305000120b18060007018a0210001e1504401c40a5031510000061f010036203030f80ca2000c640001c001c1440390b5520b8a507120b4452801d11400d202c0c001e4a5400e019410a0070b0300884112142e680d03154407418200038007540c0d00d40003204001c2040c1d07010b200f8480950310 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 595089028 1250 595087778 595087781
    0xf27050408040e0705030103240e0102180f240d18030915210209010c051c0909020a120209030c040e0706090b04050306010e0619030803010303260a1509 67
    0xc40d074094100c0c5681c0d1450494a140680d200900c40b00800c03c0c24001440050444407524406407940800b0305024000700712004000c1425180b640025803000070010f290b00b02084448281400807100701130b03140000e8051050711400c80003052803250444d9100d44604e03550780082c2607000d50042d80010784241131503003505001c00400040d004210107240c1008416012410000c0c00060344c070307203074115600908001c94440c61800b0428445c64002ca141d80660744200c0d1000c0503141c00500315900c1504071102c1441c030224001024000501c00c00000c00c8566071402220034440c201e07651120388032180708060780207400c0b0305005940740c0582d01c1c0d0300f5001e9880b030059002e410018405001c05078a4040d02421042071903000e03e00401e804d1008101c035550214140d41140c2e51849282a10360b51080091600800310303040d0004549480c00110034001d41c0c50103541620721a488120145029254503030541c1840c001c022061110140042c4116a1940140e1062a02c5d14524040380f6100c1040d40d0 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 595090278 1250 595089028 595089031
    0x1805030c0312090307050705012109140d080705040e3301030e010b03030d1a030d020a02130504210203130e06130c050a0509190b130905010f2705 64
    0xe01540007007111556080c4411070640c10070480d03001076240800a0342c84a460740c0c154443d950602c0160303d811404542c0c04031961861811188003044010098503000c01e20040c140c00141491003429079109040340034019030b07401200d180d02c401d420f107841c0c007483c194040001007801c40500801868460341481c0440342c1c00310850072105608400302ca1400040c11039451446101e2a60305200c8826001e4074040101c1b01c42104650002c03030246521000f0a1032407140e1820a50944030301d601001015a001c100782010764400c1b9001d1419640345180c0c1c5007a102c0641e4054500e4507078189150740390a040f1088028000340d4010f03241023038850518540843c210358049964840c0c0907003086964a08210181c0c000c010b810701c04c1142c0d1648100040207409601040000e00000050140d02e980d075a092803da0318201035030b023500c80b5031100a068656081403400c400249245580803a1704600c0e406424180c0310003005040c5040c3c81d024040d480d0010020803085114007185005450020902546 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 595091528 1250 595090278 595090297
    0x30606070f14160f0311030307140601141e010507110406060e03060f070f140d02030408250203060604020f1201030c030b010f0605030114060d2901091404180503 71
    0x120032042c07402000c508140c404191008040e02d182c0c010300203105071091003c15660440807144c0210381c103c0c00700345940700740c10380508040b900501709901000300003503541c103036031641c40c1410380700b14801c1c280041c910200c045090040c51011214246500c0342d406060154051401c2d030201500c2c0f0404542140c09036001400040c006040000340b606007002604d800c10a40e01905107603141c600c01c01003e00d4482001e410400002c031302501c06041a00301914220059200115500d0802e85071140d11340e800b00500000d1401c646050b4006280504855040d075500a00600f62030391710b41041100035805102c400341d00107001c3c4010451500c902d140607019510407881080345d14114108080040360507804a0b4401040150a01440d5480415241124a080d900d201e404286e10f00045281c012418506001480c0c40c01680c0490308100305c03d100c0354040d2505c000e501008400440300c52145000701c40c92259142d58591907418650321002d13201c140400a0700320180c42d60360315800c56014102c032 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 595092778 1250 595091528 595091543
    0x1050a02151815240a0306050702011a0d0c030206090d05061303140307020703032d0e150c03030105090a0e06040807020a0906060c12050d0e070f29030606070f 70
    0x10034505020400000d40401e0500c2810116032901340c00151001402948088034600f018100038025214005514055940f1044c01d110510b89044001c0c000e080c01c000c0c40c92409008a80c00645060940c020301c0740d240c004101d40400d40c01c580902060b584200203a640110190301c10750049903041c454180541d491a40c5144450300341d040003025440c41d4070401080410401c03c3c1b02e5496000101c8408903541400c250b550030158045008108803806413011841c030341e2820540c02c03994081c040e030300c006000700c2d0081040035604100d240300e801402401325a81d8410001403240e490315803582c2d130740001d545001280559003410613908204090b20102c0b0b550b000403851504620307141440d200600083c090802085280140052035514824005440318401c80340080d0002e2250302200d05442318988188450b40c130400210346d4400c0301b40304046000510000c003148485a1141e11881c005001091104605c02080710941d143d002a090f00e5000804210840010304c0b045003811965000f20503 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 595094028 1250 595092778 595092811
    0x60303020708010b010314070f030b060408210a020c09090c0d08211e06041d0c0a09060e061909050c0301050f09090d0c0f080d1b0c080901050a0215 65
    0x400b2820f50310398560081c189402c0c540b6101c000320041030f000da8031100707516040343c890f42c40c80310940051800c8100103400000006000c02e030403e000600c080e4880075a620100c0300030100c50507030050702400c0c40ea140141c00030141490030b0b2a00c4900150480a402c05481004524500244920409581c2240c0e0316901080c02c440381d034804001c00781f00e0701803040451140c0c50410700444068400110b100326549000c00880c80c0e544031680b007149a041c490090103844400b03010855500c1e980d041505105080b0307010b000c02d580c03006008900c2101c2500038859000c1e2690070030040c02d1040500c0e4112005028640010103100764064030380517980b403031401c0d40d60754140400d0180350030440312403c1c0101040e00c00e00203a08000140c2c0341c20074015251074000b0300114501250140481c00000d0405400862030911003c141c0c0c0c403091141550401307500e40165a0001550b440c92064405402450f080c489108030354010b000529120482d44152241d504003060844a4003a0070750f4078a0742000c2000 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 595095278 1250 595094028 595094039
    0x60d1104050a03061d0d02072c040606080c040b0f0f010c06020a030203041a090a0206180a0b0306010f09080d030213210309050105090906040c1e02030c06010e0925090603030207 78
    0x205c0e40030350310115003c1d181020074003001941e2030755a441820b64a49074000c10f0b10606a141c4400c06240300b1a80b003507881400e085c01e091020f00440d008160f01c5000f05040c41c40549001e1241281681024002c021950765290421052100305426141805107006000c0b00081d5988010284442c40c0d80b00180c0700d09141c241078107142050800d0100314450b000c2445088100011100c401e2541114501d540e44950104800c20441c0105551b40005031414040f8000700306030081c501c076110a985402a8650062084800c8141c900c2216210717041151148031300c038400d4004215100805511030310f466540e02040d0900c134042c005055001030400348140416901030001c0c0001e120900e04281001c4182c070000d08803080207002c2e6803007140d0b44e01c1035442240c02074070710091452000000700510740c0300200281d141c3d841450b071070720103004200020843c806071031540c5000742d00366030042101c0c9030304440080300e03040d1b2251600d408014100d800030300c140007400b42e207002e544030341d0140109503c0c22 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 595096528 1250 595095278 595095311
    0x150f0a08160605040602031c060506040b031f0b0403031b120c03030f27020301061509090c03060b0706020a3509010e19080d021201080f0c060d1104050a0306 69
    0x160403810803c2410801000a258004140c808100405400064401c1c0040c0c0340c2c4010703e51944000d402c188007040008007a2500c2001c0c5100b0400510109103043c11061480003418280c05065200e090501090000c60720405182014541060078a5094101a21070350344420001c041c0780b0005024141f0307a01007581c503001d0760708038200400060240400008000508489415169940c003104480714015075900350064401440490701f07201110000d4280140900d44038090840c05600782038144002074800c3c4920b10480d5203c0303640d64100211503480d0000fa61042c202ca004001e08850810058074050307031950000301d0000b401d4114160280c9400350345e00c1c4010241d83d00c0d6450102c580c001e119020504090b910300c40c001c0f21001101c1860440c0c000d000317030700405001e2440480d0b681c1e8644004c01e1001d0599105100701d0b00e0948104801070b6951202c80071440c2c12140070310903113290504c3d6400134100d541c000e0031754a003415259004204022520382c02914059224200c0071034100c0c10 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 595097778 1250 595096528 595096573
    0x70804090c0e0f0a0b07061b02071e0308040504020d20090310050903030f0702070b0a0c0611070c0b0a140c071a0712050a090801020705070806060d0506150f0a08 71
    0x10fa5440c62580d04550004160010702c0c41107850710080015001c080243d903510020b01000c100080e00d03400c0003180c0d0000e40e10041400744000200d020000000010944084081180c0c0d001c0ca020386880c1c1880d00340f0000c0d40208004001041d2916880c4454500310709081c00c2c0d01031049405a18bc5499000701490716107440d200a80039490501884121440401140e501c001d20726070f009455110300030300b24600002984040e00b17540780402c00b40042c60348000703610500c0740524402c0c480d2200e01003070300300070340300307010b4010300d860001c180402c40000e5801c00341ca12903005040c0302d090314a800b4240f0031175500101070801c840c0c1104006118036928519181000440030043c1400d1101c85d5444e02d0120440b01000c00c10710101041c8101c1d890b00c10080369014015450081d5101d544a01e006983c512290042c0021070040380006070ba2400c2c0780c500c560b02d0301e801c04020089901c414040400d950f9030465120f42254483c00341c0b400310f4503810380450080440b9402080e9600c0d112950395107100300d = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 595099028 1250 595097778 595097807
    0xd0504060f1812090509010e070201050705250204020f070804080f1c11011b12050f100e2a0408060708160e0f040e030d060b041203080705070804090c 66
    0x1d4140410301448280c80302c0010140d000002c0c80105507940c1081e51319882c45d074881a80f001480002189040c40c80024a001b00e11503002030000342c89401e02901d40b4041c0c01c0e00c0039403c40103074480180005408030340038546400076000502d001d084401d003d0702a4048803060312401ba0000f010000316100300403100250382d5500142600b503180c450881640e4984140d0b0800f0006102c4055903100c07000e5203c01c1e420401051002c0d02c140c80042c0c0505000c00a0b00403802c654540320020b02d200594030002c1344078608015420417040d0030b0181c495410030b07014060b038401d0300800510410a82c2016030700300c46401c94000c080e44032440c060b440d03468940c1c020195002c10001328240081d1a49140d01200e540d181401c0407100141070707001082d80c081d8051290b5a006041144804041c00084014480d48214071024003495450b40c21000c024482c034481c40c200da0304030b01c1c80540441d128a00094000b07c240c42c0c034138585801e5031070380c903a80c1d0450341000d0700007503443d904c8251050f0044801c1c41c40c1407 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 595100278 1250 595099028 595099031
    0x30406141003140106050d0305451210020705030d110c2a092206050105030d08040b01140303070f06020a0f03140106110c06070b06010905030a0c05130b060d0504060f 73
    0x5003030070045807244580d000001c0c144040403030f8800940d81c8000c1c20280c00d0010032b142040301458003403051071400681e020860048000d040c0d0309030b83d05005403401c00c1c214486008018448050040720700035440104255401c0c0400e00c00c010210b4458010219003480b4101b40399102c80c1b51000780d50a0250401c04c0f600000b000e00000194001c00304a00f502c80901200e0080301540c80708031603074010f400c0328070110403000c0390004c07441040420b50019045c0c0301c1c142c0c102d8500c50003d080541f480542682c01405194010b00104000036102450383c01400001d02a203040205981d5060181ca04800007200c0594010030b00080300d0f0b81c8080d00401482c1c2a00c0c0030722102d50002e603800c4404006004400803c544051a5980a10100400c011807000600500e540d1441c900380310242c240140d0300c41c0c0c0040e1041d40005030524000590158454001410a809c1880c100411030b011088008000312152244489010b0342c0e00e0902501e10106407030b4012505103400c0c0782010840f25001d8040f910305 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 595101528 1250 595100278 595100291
    0x702010c180306020d06080d0315173003090708010b040207080a0806012601050901061e1116060f02011d150c0705010501030807060c050a0f050304061410031401 71
    0x2401c8501d5000112034100c00f005a8a24504c0146030152076581c110000e9442042c0f4040d10a6030700d0361141350340c0d800c034040c00160a6103600e401031050015000701495036000403814059002d07441e000107000820302e241107400c1e82e0a01c0c5000c0e40754001302c6842025801c003000c01c029460013070003001d510300e41c2243e08600d0555a680c4451507409034480c00760411403e400010b0700c0e6400743e044200c82514400f66040c1c2c0d0b420034502c012600380240150303030180c6407113000001d0080c0103040c08070000a01e010140244180f460040311256041000071041340b0500e034034494407141d540022009003a142d5112403041c0b4080701c0103401c2d5a0b08444034090b440c00200e61598403800400d0858400c96400400d0b1116221160002030b28010380401a0242d443d1400000c100850200105070040c4541001c0c00084a9680240d486004007800a000301d00c1d480c124240061060000355801407052000043c80010f481d0b41c40804202156828201c200c0e00c2c00038000e1000c000d08008000c3d091304c2c020300c6038 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 595102778 1250 595101528 595101557
    0x2a1e061b160b012c040312020a140d020a090506041a0703030b0907030504020418030f1b0203070b0304020102070f050f09040503220f05090c09010c02030a0501050c09090609040c0317130e0702010c 86
    0x102c003030b92000d20110780d130211b0a11900c0c1d20403014520001c03c23460480740c43e00c41c0e6465840037540031090840c00b00d0022480040c0c0e40c20060160b40c104c48440c02c005140081c100e48203039031507000440440401d607684d00d8090155482e01c401d24050402030b40d000619207818410f000807074a500d030070700d400c6c00c0d101150240001c0d484682c0a11260b40d41c6460119a148018038103615035010000a516025412010a4084800f405180304034001d80c2200c81850fa26509660440114080c55030440300710f949000c010309003030b03001640141c8a4001c0741d142c1856244218594607245503c40903c000003071042001000c45403a2601401c02101e803010740c0e00700800381d606503210303c01c50107040c0f0000c2038402082d0341d002e000700480d80350800000d001510340410540c10f0b541c0700c401c0480c0715118030b1700441c038242001204607118507800106900914116200c0b60401131243c009039100d181c7c10020141511a6460a00c0052003440814082803d2045020f401e40f0450740d0b02d88100324181d24082ca0 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 595104028 1250 595102778 595102787
    0x50105151e160c08030d0617120306010e04020c0705010e0102010b0f0f030703080a08010819030f03091707032a0209010b2a1e061b160b012c0403 64
    0x1400708500c4455503031249900400ca40c02800d00e000075109040560740004c2c030480100c01070140360306034081040510f0300c90b87c80800010658140070320720b522254440807401d64003030055401034030505041c1c1441c6908000a0140d90103041040040d8100400400c699600001010f20000c800d000174042102e00001040070455a00301c1144114071210510a05843c24040240603507040008541d584450080c05448403000380b05610040c8031b613002074200c130100c202151020780d034542e460301c8030041c483c4812409080c100384190b607201c07500700d0200080440140200380c0c03184684c03907a0003d902c0a2101307004000d402910514238a1754541a440107070303201c0c05031071306407080c1a0381c040c0c446a03030312405c1340707241e00042d5201c0c0341e41c0b40080c10202c00013002170351a2251030803070417400c00311b0000e030070301502d4043c00d444c1d126022241b05090034405003100d0180c50f80014040d1654151f000303648030001e81860a0340314603400000c1070f060960b200c840018604452420840007281401e05660050 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 595105278 1250 595104028 595104067
    0x180501051e0915040e010501022a1f1d090c1209160303030501081c021911041506090b07121d0a03050c1003060803090f13090605010515 60
    0x1020411500a56aa007240c44000c1c2c03411400302074010840200c0d20b2405000320b030700c1805199850320300d043c0002659880001c41c84d0140c07510f4030203a4510b490b10329160031040c100c485e0099020620910300c88140280207010700c5202829500c0c045030003c503003206a4100a54001c1ca806107040c0380404c4a2512410112160300e80c840c404450103603900c801c00da061034803044030050040c00c00400001130603410b40082c1c0c1030f81c04a0301a6083c074075401c2d4010b04a510045405c00c0540c0111040c404c1601d40200c2c00c0300c0725400b0b5011a04080d400f000060100c0e00803040c080389110380d0750705c01c1c800650b21082c080013510080c0e425910300709103503e5000400140d18540c0f410040b2043c0c3c030300b1144418421180120300701401d1402d03100d450380344c00c980b1081c1582c41a270080110252540b8540c0c403030f006680403076044101561401444005020804030010344258000c604400700090029a502c80d56440310700031100002c0359410a002c12080d52103142034440d01740340c2405240105c200200c4030a = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 595106528 1250 595105278 595105297
    0x10f110f031c0b031522061b0503040201080610180f0f060207030816060b03030a09060f052a03130b07110a0b09130b03030c1609090506130c050a090c18050105 70
    0x404d01d994550a10384008145014650610040003501004210207900208c4a00300402a8005200e8007444100c0711400b003220080d002410030000b251880c10072a50544c603207a900c0c80c00c004181d05080350086003840310303880312210f44140b00b01040034000d9208441c01420f000e20142c100103144d52038410b40b6008841c105180320a074207982c0c408000780d0781e110755a0040f01a0039680c8400e4002d00c0544500207510605010404422900c140c45220b00c0450351010301d0748000c0c0460303592580744c071002d840303c6661000c903078803040190701014001d0144407401007140044403a901c1c00c40c1c0c540320b107016080e5010301e4000e5031844803d010001c030303810035030b801c0800c107a40e001e90445156001401070810b003400d20fa0113000020b00e8100032a400300303949040c80300c0c0f82c40c4901c603981d9520541c1c0484e8040c1d40c0191040c1c1202000c118078102e480b0903180c0545c0200b4003558801d80b1940054024402030703210440540d07540d034905c0c26072500012200002d218002e601e1020741c4c41e0400107002441400c909 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 595107778 1250 595106528 595106563
    0x3030601020319051b25270e0a0b10050109030308070804020315100302090f0403091505040801060e0a0c02010c02030904110d051005090123010f110f031c0b03 70
    0x1400d4010303c10816500d003481c241c4c050340f800c00c12034605ca0303407078400482c40c0c250b100004070085282d48080024810464042516540c078000e08000d04400d01400c0305c42c01c1c941036441e0054001501010002d03030000a0003009401e17020b08008603203404c200e005500c09414029005010070219401c00c4010b507201c02c00381400ea130720ba903c030301c00282070220042c0c0f00c140c460103820500c800d00640b080d045e0203480c4290fa807010903407502d0b600f540d050001143c006000400b544024010140c0c80001e050004680e4107040d0300303186c0c0b101565803c0d0b6003e9006000501281c200708070900303100c0d0003001442084c0380000c0100f00700310301c0e000b516441001c3e20640107545408030110526904004c0382c1381680c8d40102080745080443c0c2d6944860346910495100710043c0300003098595082c0c14040351014405101d0220b402590010f48a0072103401d46402482806041181c42003402c1c042800d00c450100080e5540e41c80310f5503105003c0d5500400400d81925009200000781c400080412261088489 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 595109028 1250 595107778 595107817
    0x2d0f0114040b0405100507080a0c09050325030c060c0210050903060114010c1b060e093601050a05160e0604090e19060b03152203030612050f010b03030306010203 71
    0x400e5032400d403a421942170854030300001c01c40065448280540112028442801084080413040710030383e60501480740d06800444c141d4404945034040350b2080c001c00041e1000c42030342e0f0b45031180d00301d105070701c2000420140d00d1030300c0c110725045104444c1e900b40b509045052510307040200750b0302d080c14000c2c116405078903d0a003050b81e000d0f401c0245059848040e190048400d6440442481d44030300c05d6001082c4040581007103031500f4a1036a00c14644152282c00031a14200c503611207a40144180300c1404184a054804020a00415215000034000443c1c0707801c00380c0d0340000303903200084400708012108034090383c10741d81e4600700c83c2110703413486005c905941c8041685003000d9051600621007808031059008028441c1c0012613003400480035a207a50002150982c0000400c40320100040e070a40a140d102c4070000055a40c0c542c0079140000e110f90700d84180441100c0350b030500381ca081e80400d0110501b502c0c00d0180d0b400c00c0c0c5050f0040c500350b051070300010b9a0b0340114a44003144815600 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 595110278 1250 595109028 595109033
    0x1b010801271d0f01060e01091b03150b0301060e0f060910080613141801020412030f1e11010608070806040b1308031314010603030f050703022d0f0114040b04 69
    0x303a80c80703015580c0c2c0b041d40c503101c002c0d03040c00707000388601d104404080700d40000005400106106d00c01c580458080300e2020380c424404200c00428a1b152800b1310300c20a03000c0841c1061803400031318080d01c43c94544c25820780b444010803012104000c04c139881590108000021500d4903e18507070030081c00d042c51800350300d5400024221061f42403940018501d084818508200c10b1031045004900500b42c41042e4180c483c000c1c5d0030b030b00c00e0340241070203070300d1010465000911400342c92080c0f0300140303010368010000780d2010300c1245003100c4080000c1c0d006070f10464002c0b000e220781e000400042d0020300400e49440031054496a00600c0035210281240003d0003800000c840008450350040300c9943c2c0307180900484410846250007640c800705403280c0c5094610b0144600810380b030b01911161801c1040e408112010350182404404601034208990003400e8210f284981c11001005031200505502103900c1c5008a0440744200b20f030b04202c0700d004001006151141c109800c81c7d080b106a60f90390 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 595111528 1250 595110278 595110311
    0x11407060b090a02030403140406080103110607060c020705040e0f0d03150e0c12010509090a0b220c03021002070609152622030914030a02031b01080127 67
    0x89841c54002c1ca0641c108510312403154000c40c413492113a250070040101c1e003581800c045c02140103020204120744014004902500024001d480008000c1407501280380d42e00c07002d44154440481c05680854030511040c50240104040c80100d070307005008018601d203c0700d507144550050790080c140c0d510185582414048014400b901001010788240e00f0241c000360041c0d44141034413019092800b0000c544c40c0b83c01841c40c6e00401d1018001d1081c27080031303100c9402c0c0b41c401500c1c11004030b120341d824501000507040c3d0300343e405010f01d000f50070345450750044c400780b845015410400c54000e0401440303041d800000d0501900c0c0050044040790401c040103455040e5441800d50118410700510380b90a101c1c40381c242c1c410284035000116064400900000030700c1c0030200140070426a420030708c0074000340b11035980340e00c0009084030000c0c001c0d81c021074203105010b000310700c0c050f000c000701740b000303503085202240140050320040c80d50113a044011026100c080146c120865210f9040d0801c103040c2 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 595112778 1250 595111528 595111541
    0x1150509070c0f050a06051023010e12060a0516120e0102090901090209150f0706051b1b06061e010c06060e0108151308031f0305010603121d01140706 66
    0x3186800380a0403e900f0070f6591190750500850314142010b00048501408d403844008880104006003601c074000300051180c80c01158885041005c00c5a842481d541c1c6e101590f4142c0c803000001d0040c40c140140c1500658400600c0ea205d56054201148121544454003c14010100800245040f400300c5a10f02910070300020a0b404801a030011072070603056801001205c50490302d08180013007060381100c50707010381054401c03412003c0c80460042441500415840031003603100e441c1d40c00e0b100007a008182c001c1103800d48100e026980b2800b8045080040c50b07084002143c850002900480c840030495540f03004060420013450500b1042003082d8020401818140c0c079041c40542c1c4803d400f0f903864030306c449200d12400041c00400c40b02190601e1805541c0c1d00501101d02d540c0e105113422110000a9600300c0080c026050f0000114a0a11400700514401d007503144060310b14030f20050145200a0750340d6030140d601d40140c2c540e6a000640d00310b804181548550702e8014505140340245071 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 595114028 1250 595112778 595112783
    0xd0810031704090c0806061e0c01020a031407110703030c050309030609160b0f09060c03070819080106020c0310150504090c2c061c1a010806060301150509070c 70
    0x7121400d4000c500c0080010300256605200c04001c60740004004451903d01920403e412003010003616640c0411000308100044c0c001085902d0240d182d000c0c2400ca0f88551840c0000a584915045502c001c4d0222a80c02c56118640340c43d010b8810040c40d91584030510000b03040c041c030f00d0301d00c00404c5020b00554030743c4a8010107407211f82c07038209035498461540c00d0080544801442000c9001054803007524215a600000c1a0070308100c0070901c003c59109042e60700c0240700a00c50a80001c0f11040240001c41944801e0200280d0803003002e401c3d54410b810000070340d0484101c010154400140204800b841c04601041a41094903c0d1030b5800e2103421450b046420043e4460600010401420840c0d051180c0320440c10303000e20000d815450138200080ba1a4541c1000c10340302d00d0410310b501070050880c50701002000a5035182d110800000c0d10b4201159003100040000c0703201401841d0380020150b00038010b100c44011240540b0400340581071144407102c001c652090300c00c40a41c0038066 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 595115278 1250 595114028 595114043
    0x12060c0304112106091222080607030207050c04140a090215040e090f0f10020c070504060e0a0605060a05090411090901030b0a0501141f0315090603030e040b01020d081003 75
    0x140b41a214010703050309010540c400c1c03180c800801c5400400040d540710000d1203041b01d90034400b454110100d540d000c1001c01d118044c0224001c42c01c0d800901245000b00266100140da900c007a250050402d040e2084140c401d1386405454404c0e000901d0f0b4041c2c0c80480c240001039a02100d20005420b181c05c20b0800621030408600446c2008400d0041d80c0911145000c42c1c0031503850b00c52076507556420f49000c180707036001114000c94140103078001d0b140c1c5c0c501d140300742e800e519245d1000c80d00b140c1c01c580c40f0b44108141c0d5010300499120a10030480034107810341e60f0f14505449424060000d21840c20264080c55907084030400d1320303181c441a120300c100000c0c4046590f580d00c2c1003027050000709580c0d8070440c41c40c001c0001441003038000c074141a144060110f01c2c2e0646c44c4520004401c1c4841d08000a240d200c3c0200649140c001110002400708410006145803c5003001040c115441031001d00a9182007108240b9030380000361021540d840b4900f0303d10aa0700d4010401d10080b99074401000e44 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 595116528 1250 595115278 595115299
    0x2a091503090a050118030e0d020a180b030a031e0206011a09120a0b01081209030709050a0921091706010b0f0708121909030906050d090f060609050612060c030411 71
    0x910840754101742e014082c0e80ea00201c80c00540410004030f1100c40001d501c0666400c0030070142c001c4042c1c803080850b1100c00040e04000b901c01280c2003c0003c141100043c80c1d804201a0f0221072040c04203040c0d2542c401011950b040c4003548142c0d8403c0c140c9d022003410041400b40c905c1e9681110800402840016504501400d280ca08165482802250903c3c040d14011401e00000a01a5441c40b50020700820f00c00786088a44001420302410843d1000d4072100840c0114a04003d1060580c41c405480640d440145030300804000c00d0350080c08401074084070180c2030500001d0010305650070403032150799462081c410081c1d544200100100210404580d0380c030480c044481301442203201400e1b42da11001803031070b620126810004010041075180c41c041c45410300c1030b0064140480400710003e8040c02d69101c1e607000d0300182200f100d0ba0b5032100b0040c485401a40185078220005a0b000c4030201c440642054a8010040c0521004d0002000050a01c150102d501c1ca00003000b03040003500 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 595117778 1250 595116528 595116551
    0x17191806030b041e1d120a030c140c07061206051e19080a0c060f0c2d05010518030a020307120509060706020d0509060907030215040e2a091503090a0501 67
    0x41c02c00f40683d0704403171080000e00340c2c03c0140810070445032414a0056403a002461030194000c0c14204255070400500c4140c0f2030010940100404e40d092815004040280c42c03c24010400031400a41c1400b1a082c594100030503103c00300524032034241484102c8240101d9804101a00c0c7c031040348000c04144008002017090000c180401101d02580d011005d1b16203c01043e55a01c01180c10800003507940f0003078a0200322500c003c0702c2840c0c03481c459904180c100240e03c007000340c0d100001741d803165035910a1013008041541c0410707080305500d0103103042104010000e9120301518a0140c2260000c0c007444142501c2a42100c1da2650010711654440b0150f0400c000250003c2c03124072000ba01e0304010928090b40090300500c0350543d50004c3c03034040d00759400e1000c05d0b04010b0300f9801c1400280808a44226004410b0344113004000071507000074060a03000300706108104d0390321325801c0f041100c1401a100e420451450700310588940c2e940340c407800009494003c170b0030000750843d46800030780c101 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 595119028 1250 595117778 595117781
    0x1203041811030c1207081003060504030905040c0203040914090706110c04020d02071e20130603030c0312060e220506040309050f040519110717191806030b041e 70
    0x258014136409a1502d945c4008090b195170380151503100300d00001c504100005a499040715501610915141040b180d485004c42c0985603a06a4000503810215042c098102c492041e12009100791301c89082504099071610344039459030003104200031901d0408002e0f200208003000f1540d8029100310f5031032005840c0c40b00250000903044642d03003290396460100f03501040d0007144c13480e0005206080c03c070700700b200f01c4050050902542c1d0131503114420954002054810040114082e881d604c041181510f401004106900107000070700303117001c0d8180b01c00d43c00414282e0380400c03c00420000000008800c059164080500815038031510080004140c2d000d4200300440d07406032040b11000080d0350800c01a41c1d421a4904418003800d203003104201c2e1031b03820008020305101c840e10329000c0551103c00c105610404052a03424001410800c0304010000b0078803642503500d032444440f4440103d08080c0c07072551140700109900d0760f008040a0796594441c00c4000110b004201c030b841d030014181e10 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 595120278 1250 595119028 595119037
    0xf141e2b03020318030c130506030a06020706050402150a051911160f05040608030d050606090310021809160c020a09060f050a09060b03181009030503060f1203041811030c 75
    0x4036800e0922007441300e0a0020300880106002004920300ea00c61058190042400920607545480b4907144103002c6215403000f0075441b4050500801d040c6420f00500c00343e00203000307803034044001c200104170404d40d101042d5044e01019040d90040c84036164003c5400d80c0c2c400c20940c001d4020340d6101e04100d01038024100031100841d808c1c2030701940c2ea80800c401c4030340511848902c0d40007008810607480070380d0311403644140e000340080c0c100241680402d28040700000b00d440820b5001540d86c010152540042484140c100c500e01c3c124602040300c1401c0b041c90340e03905001c1c440d00704080411036403103641100140c554400200142940d0314800380510025118560003918881c4010078080300901500050f00c00c03c031001455502d482140590315440000442e03000c0c020705141851a140b85d0181d010254060340d1107544070305045040007500d0003407020144c4a172401c504540803414000c000e4600311503d41542c1003522040c8481030010301154041c4042c5004e0010411002d03804070b00141 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 595121528 1250 595120278 595120297
    0x6120207031709151b0a210617060f0c09100309021f080a14060907020a050307030324180e0312090a0b0c0a080103140a0209010f141e2b030203 63
    0x20410750b118010785c0070808016001d5801d910304100074810085000b070301841d0415498507620542406201920422035035140c101e0010304021034040552040d00300000c030340000b04461100194200000e201180f8820740c401d940c002d002901c05540040e00030f901c100180364010b00a007004c0d00c0c10f01011861070502c01c00c40310100e841100801d40b1102c0c0c2d40300310007418802e820612100d0b1035450400ca001e0400070000811881850b07444400034506002406a15100780c0b00070841020942c41e10024407901269121901e001c0344040001000854080040711260100040c41c505800380d61401e500c2403c003820803100c5800c0a02a620100060740440240103c04440540d12030700c041c441d081c46a4501300303001401203401800403071090b000c0c018070303c3d0898084544005480c0e02081c3e4240d000d0b844540704944103201000b40c00800d561052913280e0858030707840301078070351500c004110b5403140199000b00341c03400b600c115414002c03456240551a18030308210841141c42c0003136407540b114201 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 595122778 1250 595121528 595121563
    0x501320306100311040303030504140f01020d05011e090f0f1103060102150f04020f1f200a200a080a0503190e010512090c15041401020706120207031709 67
    0xb480094800e100304503100040f42c03030051074207203981c40c00c130040c09000d8016507440009000c0301075000410010000400481c500160b10340464201032802c80c2c81c160b102c052071000d1002481048030111881d030041d0390703a41d8400a0032680045920004001c0b0000541ca094501008104250401d40103903200716826801c071000c00030442d82e91131440f80c060b25801d01c980c16070000314005207085000f0000848029001c1c45a1103503401d1245501d0010003001300c041a030404828140711902e462022072900103c0040068440950300d1a042c5482c0007401b0007803403040803031348601d80e0b2200c0c440401441c41100315080d501c0030b810710a442c0c0c1c0c80010b801c80095807040383c584019004101c00f0007100016141c40c2c0c24041c0f100444801000000c11080d0700303004000740c902581c0e4513800e64410b81031309a0450790700d40e414111105011581c28903018195845080e0070002a0ba1005007200e25400001c000340e1114090700c0c0079078018610503400000851018104102a100016125501e0002046 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 595124028 1250 595122778 595122799
    0x3050705210a0c05010f1805061f170f0f07061107030209040b060a09060f0f0b160813030b240a060e010c0512040e0108100c090501320306 61
    0x199118a051524281c00e09220601040e03241074000d5103a011402c0c0034000104441d0b4159540500f01d41036100c0c55010100c1a0040e8402c0c0442001000e5110f02c2c0364411b52283c50300e20300c0c041c06102c003903c0b07600c2803408110605121505c090055449003040300c003c41348010005141681c8608803801074900040b081c2a80e00c0c0c01c9a0f00242100440750007629000003522217846101c0074003801440503401038206140000c07408030a109180007009400e42043c000d9040220b009600340ca0b40c0c3c080300c0303600410300948414400d000c604505c41079001c0c0030301d540c8081206010030983c25070b0f440039003074040c1c0720204030070100400320710003a2000007040106030389014410407400d00351078001c100c000388010517000c0c803950081c02c8400503940a0070842d50081651101080168459000403800802c0703d001000b04440420000b540100c02c40300500106a500c0d4004200c408d1510896042109403001401c001d43d02c841c4545001c0503407101d0103c07a400e41036405815031701c1a15a5070041c1817102 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 595125278 1250 595124028 595124053
    0x80601120c08150f0a030506160305090c0d02011404060c11040504030909050c0405030303180d020a110103020a0908030310030506090c01050f0c0304080a150c0f172203050705 77
    0x200352000701d241c9465400e2192208091020f00d109006149a003042c00415480e82aa0341c01800000441c4103100500080c13030a840c41c1d080484000300c082007818142402d00030580400f0406500184040c1c0300442c1e400c038a800101d800c0581203a6004828034001004540d955001c04568202c074015988410400745d003000303010807540102c03405800a80400001d00072400144c20003604803e040803c0e40c141500d580010b8110b603c2a10014852006a1000c02000e003040c000700d2004401030003e0002c841c9203440c0c00f0304105102206504140c0d0010b404111355005a01d000042c180b5038080720b4882c6400d0400700c85604450100b03030b03042d119040010704407081c0060034480404069407094104009050113178002d80064024503000e00080c08041403070700c002c008500c0b41c1802a0f07002da01c101207030000c840031542c1c545c8600c410040d0f03010109078165000680381100074049a132404040e03840798840d25a075030010f001105505078085030a01407550050103028034901510030303550240c0149 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 595126528 1250 595125278 595125281
    0xc0603040c210818220504111c0b041a0f040512041203121404081201060804021f0c020303190311042106060302180106120e0327040c08060112 63
    0x600c8000c1103840700300281510743c03580c0041410040e03c050104030900454416170a1a400c881c0c40c5440365a0b51101084103014615a078000011401d0f506410711042c8400814511030800c2406081881090041000c1100f0681903e00d21600d403e294005424156443e07202c48405a40c1600c0c6807080c5102100ca4884070b40c00c5408423200e201200f10b25111030755090340c003d80315400c0341c840c2c0c1d55194000c1c810101100c0ca414459441b80300d119070340c0c000d108407a000c40001a0000f40070000384104000041e1510b820b402c0f11007550152248011050410031594080c3d65a0002e401d4080480c800754490b403440c4800045a078161014001040142d84000043c0124458800b81d5089542900340c680c0b1a20700c0c185c07442d40103440225800741c81c0c0c2c010070004140c40c00d400c245401540c004102c2e459005440c1910352082c0703a0184032515034920010b40d40d0003114106072154081c80d03640114109500802d800b541320140050006119185014055500403190140402c1041074684a00c4099 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 595127778 1250 595126528 595126589
    0x30f0105010f1701180222080d02060907030212010b040f020307020f1903140c0d02070306050105060a0c150b0411070201030c0512310c08011a0604090902030c0603040c 74
    0x607598400500da01e800503200213401000c040303102065082007200b80802660841021f100c021010b800030161030510190302d0134100e11007102c2150440818801c0940010030341c41c046a40448201d001c000080403028010701e19140c090350b00c0341c980f5440b0b030059222900558441c0441d5001c2d5801c82520911440d02d400d0420715604000a00e04403800000780a121614600d543c0d14048908050710301c45124900301203941b1007805030340880320800c1008650b026160250400750745080c10801300c400058002040701d01e00400d580e038580d03115094401c041d03010b030710360580060090220003003100c148141c55010746000d070b00007820a446000601c1c000d80440c4d11030111606141c03d07507558064103021440c030300c240000301400b51219202180310210704454a9502400c0b0250501d46069525403c544400a0b07040d201c503601906d1b82d0a9070740c1c0109450031580c003000702003000c0c0c545200083c02c1041070041598003c2d40441030006210718400920f0039281c090408151103044002c511960010 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 595129028 1250 595127778 595127807
    0xa051c1512031b05031b25180c0e030304030c1a040e0a0b04061d0f01081b0d02150705070317030c0a110c04020d02130f0506070b100b030f0105010f 65
    0x21070403074160341c4003144140b810f00c0c54010001d40303051201d50f60140861043c000c204442950050703030318100352250380e2141c05003910510390800c015841c0c9104042c1d00c030074456641c134405503030320700e00e0340031602415251408a03401010341743e8a64892500049624290191501c0f00030034a0f4032466810080040380c05451900e00d800c0004e940c1d80022030061300f480b002064000384c07254030008041c00002c0e0006407100e10070300c0500441c90515034a0b480740700140c1c09a9115445155655110124203035a003403503001c15500c6100010240c004200011250307104001c5d085000240c44042c008041248401c0e80d10445034035040030310744929407038240010340d0200e03000d000c10000000301b01d020707440f82582422401c01f550036140b83c100014080b6009000340e0213400b50009001440090800469406440d009031040d544a08000114441d40503210004000d500803030040740c884503a24524500501d2084505544c0e4604001001d600c00028071616012031480c00740c5000c8140075180071400b203407 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 595130278 1250 595129028 595129037
    0x30806330a351504090303020304020306060a03240e0a050307020109060807120b01030e06040302060604060605040803071211030a0f0306060e030a020907260f07020601060806060a051c151203 84
    0x20154420b1900d000c1c400740901114040c104141c550589640c0650041e0302d01070f03200140c59142c540181801e10a0007030400c3d00c50402d0315018070010b0750b6031104440502c40c4100c802141c4e03819070708400c02882e4044041c00c07641b05590005040100010061030418400c1c0d9030009116540c3c003050300c3c0b040007071343e030000440c80300d0b0303450542000f6550024400d008145804540003244946450901e88251015070058100c2800c100310317801c003030080303200415051400514184c41c240da03950300ca000b8144000c1c086001000c00e002c2e164030800c40000f03084800d10649907502e80700040a0300808651402030086400e01c100000d003035000c1c1100c80302410014020300b080820355803c21044280080121090000344582400004108120740d54060071000d101012810417041a01040c41c0040020f811540030100520260798461140b607000740041e11900c2e1100f040660560790342c0a004850014440e034144485104e0405802440c11080c40c0e03424105040d071030340004030103c0128540a800708 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 595131528 1250 595130278 595130357
    0x1110a14090f060d1a010e150705070e07180902180d021504031406060603090709110d02070503030f0c041a030a0204030804080d02011503030806330a 66
    0x8110000100340d03580c00104810940103682e0000303a05500410031141c142c6a455540240340310010000c40c1c010308090810111a10241d00000e004d8040514541a1001e0220745141000020000c040140528072038010452500780c100a1291643d11401004003d40d8100005c40814900c03c94051003e014042c0c180d6402c0c0700309001c40120803590481c1c20590403001e0311101480840507001071840b40c1022030148019011291400c00c01134003080c400c0c1c0c0d0400510182d00710016190f0101c0b0807041000c1402c41c103ca185814600a4050981c10b032400080c803a010440c01000840c401c10160740c3c0080c4d581c40e0301d11460100e003d28003070600b4800c5189081c078072408090000d5a840550b00e40090b2a023a01c0342d40300811504582d01ca0030b125880076200c00525502805080d00c90302c09e00c142c4000817880c60714014400000544014000c070704000303117051082084102c003a9403000071041c2d03800354003040c0500a01c2d5130092030307041c3c000b9510012040b002c0d03007613810925609040b000311141c0c0 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 595132778 1250 595131528 595131557
    0xc0b010905060604091a1e12060c19050403060c05120f09060c090310020d06180e0c130f0509061e041104150806040302070e0c070b0a0b04060801061701110a 69
    0x400e60003a060b8502c0d2910907140c640796031001e9244240c0c0c0403802204511041c07d80501006400c22040d00034190004010064905000c000b960309628080c8889080c145800c60203807200d101c0e941000e41071380c0c28041c128100640010007801000fa6000c008420790742c0e03010130404c2ca2230083e04c0d000740542040021503d000b80d2503000e8040d060005055032084000c050051f800c03a48507480d850909a00e90030100304402e0042d60440101c00d2220003801013a112941c01e64595145468007031188101203100c10040c1404d40c0301110242c40305804110303d0814108859550104441c2c0884034802e040e6049440b14000c503050b40102d5000d41ca40041920360002c000103001c000c0320b00c4140d51320003e000103c4030700c108200c500583c0650050480e040c1411054080710364020401507a1100c10044000001d503505c40b2941d200c401d000300000ea101403140064064050380d80710404035800d002000c00d0308190881081e45c0500b08000811a10b030400075a600340d030180b00046c4d40890030103d600e144 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 595134028 1250 595132778 595132781
    0xc020d03022104060903020c0a060e010c080d1e060602030a201501030c080c040908120705040b1215040e0a0b09120c010b030f01020f0720030109030c0b01090506060409 74
    0xc050121021030b0019074402e58450b01c801d041214140c5000b610340040c1024180c040c0b04100101506841200426041901c0a8040b00b00c024402c0d040140003103001c014083c0c0003080e144200021107081c0b100c1141003012340003504614065120503880c04000140050000040b110303596000e4541d440c201c3c1d1080074414060b81d00d0740f1012024002e402444000400d01d8580602851007a02080901400d240100d8a03081c1c2403818140100d2030450f01c00c0c08030b0b560000381c400d666094003001640d81d03108001110f007401260f0000700f4140003c244400c03900107a0010501c580c0d0444c0701c14440c00400b20401c0251500010b012540350420464a008a444850402d9000d171400c011215014140081998680e0040d080501165074032201c2c04881d20b4280404c1610030034800095060a0182ca045001f03071091910090a07403c0c07038002e601c2c030300000b00490ba0405000070b008222071301050902074148001c0510444070400842d00215911050b0311031a8080c09001e41028205030400c1903910 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 595135278 1250 595134028 595134037
    0x2c06010234030206070309030c05030303010e010b0c120c01060509150d020904080c07060306051002010c120209040b1207170307050606010804110901060f020714060304060c0903052e0c020d0302 85
    0x1c1081c99001c804809602c030200101500303403007a43d80c000f03030b90700d542803080d48a806a0030842c4650410001004101e0700c0c080d04605480009002680c0d80040c0281c0600d003503140d08a804044d24041204a01da00b010340c81007044410a6401001c182c2d5000450450015100382d40c0350310070007002150001d41000303c1c50030b9020b07203d42106460017416014080c40d203801036008400098940c2401d0041d410401544403c00030240001e02c041c0c0032141c809850480d988103a81d900039800f2400da1140e5903150402050010040d11684104220490180d00c41c1c4036809a40314201d481e05a14100e0900042110201600a8051b090079103940c001168003100140c402d503540c080014034009076a0f110001c140c000c0610b0340398a0040c5a000602a007002102e138801c200b80d40142d0a03190721034503030310200c03a84070340d000c3c5001865040300d03d015200c18200f0341001e080c0d8801c24806011100307001080d10300035040c003640c4000c40c14a020010068070500410b00740143c0042100c3e1203828040c0e000382 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 595136528 1250 595135278 595135363
    0x5250c17030301080a0b060307090204080d030615082809050606010e010f05032805090606011b0f1202010e1c0e0604270b030d021005060103060501020d08102c060102 73
    0x1610007954030165034059801371740011602d070304007041c8561029098440c00d801086e540c030710580c0000340f04a020b00442c000520741e0fa086603000301c0300c42c4001c841c5c03001c8030b01a4041c54010015902c8030b00b0050307500c04007117804a01241c004070b80c0444641c001c1c1c032003242d02003a940d141d604c1d65580d80701185d940c3e40313011130502102001d00303007010a4507014001c59101c0d0f15104001d002910701100010510928020b4586048031144c4059000c14004010942d0039500141962000741c3c040004900401081002c03e185009800c401e414612051214032780301e100c259204071803d42d45108005951045118040c0313401c111130300b220030860505002c5c26065501c50350004410320b4120100e81000e403a20041070051304200342d03680b46080c2620070340350402001c5c40c080142c1c5081000203595000ca42c40340d00c007031040324400a0f024140207841d46014000900c00c02d403416019490031580c01c0d003441c8a46000c075060000040340f5501c0000c4400d05000d07117007088500c0f610707a140740118a59803003035403 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 595137778 1250 595136528 595136533
    0xf0120030f0a180602071101030b010302130b030c0c060906150316090b030a1e060e011a1c060c05040503101a100e180906010605030c090105250c17030301080a0b0603 73
    0x98013091040c400f50003e540a11445845404a04001000c480190503903034181072042c00100c98988050a410341074414000d4016500d86a58142c0035035800384006100440c450001003000340d400100d00b10b1700443c00d183c2c940058142c001c00f0180c0342c0014031a200341c8180a4001080b800c92141c10419418501601380c5244455030b45490f80c2484500c60550302102007076051008102d014440d1074600c549000003001291007001ca4907420040041c401ca101f424030b40c40170102c8076240300f030701d00da400e500180070486030f80c140b100507120360402e104051180c052048069040c2059010740300140d844101f448a03985022003c00040f03154800d250010002881c6500300c0c4d42d00c4580c07075004500504145180c00d40b801c115010301e0000143c000000b00407041c0103100d00d045400003954100b038000d09041c3c2d102c21800400745045403083c510400000c46800d0301c0000d005000040c0800c1c2c9442030100020f2580c12504903a680c8002e2140000742e038810911b110100d41d04000d202d8120720001c06 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 595139028 1250 595137778 595137821
    0x604020f0117040b010f05030109020604050910180f0515030627101a060c0303070c0809040507080f0601090623040b19020c0a03020904020d020f030f0120030f0a 71
    0x4070844010480707040700d0b02184d82006000890400150200034442100207200b0005981d000c0b4400b4052445180c1c020f08400e0003068090129100c101c0213132410a03140d03c40c1104580048000c0c0c0162402110344c03c0c40c2401003004c0820b11400c0c504882005402014a51280d5030318a0074007108080b400001d000110020160210a00c01d00000035924a408134400104920f403d41c9002080c1030035116240070880140c0400c4048180d07548644130342000c0901c80154142401248261141254003d140004010100d0380000c2c019008880c01d242a250542c0d4240c015580354200b8016400480c1540380e1232602050300f000b00d88840340c0280c102908050766028030008641202d0f485d08030701c0381017000b0311170015410441e14080e0f0b08210b03951441945150042042000c014001900617410784c0c801e48259120001e001002100c0035007101e1802800c1c02407103000300030396098034441c0c0c107040003460313160b04010302070b20b0082d048403000743c103261200d140c40c100404031844034010a664004 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 595140278 1250 595139028 595139057
    0x13050607080619090b03070603270c030803130c0506030637060207091a091f05061c1d0d050711030a210f05160302070f09020a08010909050604020f01 66
    0x30380f40c00180508000429155550170805081c5542070300f0500030980f40c408070602c02244021915406d200300442d4030a210414140342c0003025154101901c020000424052410100e5402509050041440304545510350042046500c4203646c50f59005c036011a5a1003801e000c00f0218030548a0300180b504051540484251482c00f507a20000158000c0082081500000e0080d480726058001301100141c011300d0001d501c95401900311560340500d041c60b6101313680d04415000c0940002011301e51070b1840095800300002c00010081a558104001020b03581186264a0a130354413180240810400101c0112100d80001c2c005503005048800c18070100e44040c0f1102814500540c41400f40b105000038203001d2402600582c03080203d4000c010500d15400360640f100d2072082da000300c04610f100c0c14200e10b010000c1e0050494070306410b600041c0310440e03900034420040c6948409c449a80da600c1c81800300c9038800310240881d080300380041c00525005281ca00c1204050401004422061 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 595141528 1250 595140278 595140319
    0xa1818020a060305011e030f03050a052a0708060103150b0a030b09010c030b09090a0b1506210c07030c060203070504030b131103070b0717040506071a130506070806 72
    0x10382c0300c040070135507450040c490941c40503e2140d4000380301000805261966503480d030903104600020301000f40105109420910410031a15410101c59558260202d00501c010242d484241600d0042c4500d010024100001041c030034122a00041c4000344c0c60282a4800040e04018210f990f026a01c00f40100c00038561011190280c1e0a1400000d000f407940c00d03015045421019400e03100f9114002008420600060106044da5004a5902054860100407102e0f0303600c07510701c0c507842400800c064560800c0300c0c98a40c50109402c0d2003a00c0c584501800fa400744c803070f04501800190418010300003041480d002950010040d00d0302030301d803da0742e4840d0011424240c4040d20750840064400d428030151410485990100700c014100f824a40f5641c985140300c0c0c0d0000800075000010100040c3c8000c0c000d440040c80050141540c80403240341c02c080e0003603002c06204c80d040c0403801040050506005483c03106d80c3c04402030005e0f8980c0c4000360b8190000608c1c06030b10141d007074000000351030310 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 595142778 1250 595141528 595141549
    0x40b030901060306050a020403020627221d0303150d020a030317070207151d06030f090d02012319110705060f06102d09060e0a181802 59
    0x800c000000c0090651074a803064a1004d08100c011500500007070000d07a80b04030850f040c944010780110f20000d00b101074411450010240700b54054034a52001a054088103003c10000d80c00140811030980103007014145040c543d100c040c7c031a0f0041c800a03003a80344c011241d541150005103642c140002035400104d6a00582d08200c0003c0c4030100341c401a52b50140784650811480d00107401002c7c1800b4151a40c882a035650800304640c141ca00480c40300703582420741001d07070090701c210b032b81e494070103d405019030b000e4031090124828282d442001c0f0784180709070cc07402104c1041c0c0105000e69100003051002014200a0b5080c0f22082180c400a1162184000d800f8441801c6a11280d9900301142003240007800130a0414109080250640d6a0700510884081909007040e0341030001120401480c1d481040062004184001078440d03500003426100700e0741c0301d030703104000030811800380800c040c1688201c45108104000c070080c080103a0300054044d0100f403520500d19072098001800e00d600 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 595143884 1106 595142778 595142791
    0x150c021e13021b0f010b0609090403200d03060801090c03021011010203071e0e0307060807050708130302090c18040f0209060c07060f1103091302040b03 67
    0x7112258801c40e0112044219183c410351404070f807038154801040c030b0540c0b1800306003000e40300c41402a00001c0201404c5181440800400e100f85414090320407414070210080130820006500c1000c800c0c0400340c401030644400707c0c40701400b00d0350660851036490f410541041c010440b500104801c4a50544a1070110f4030801c030200c802c2c079616080a0415400001840314883e40300c03208511101ca144281c50342c001111106035038024103034002d95011f0b0885501003010502402126500c004c00717080552408281c0c1c3e0381d10149511240f41e014540c01104401d105508001e0080f5500112182c9140d2903c0f0941c02d03410003602803001c1c0544070386c0d210340040203c0302990301580d07500da40107062213899600b8908840d07241c0d09c0600031100000c040040c14040c0d40d1180da80d14071003540301000741d480c0078445400c0c4007425142c202c64840c0c0d15002c11001618000c52801140300d040d = true := by decide +kernel

theorem cover : BRFrame.Cov 594964028 595143884 := by
  have h0 := BRFrame.cov_init 594964028
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594964028 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594964028 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594964028 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594964028 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594964028 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594964028 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594964028 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594964028 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594964028 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594964028 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594964028 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594964028 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594964028 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594964028 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594964028 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594964028 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594964028 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594964028 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594964028 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594964028 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594964028 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594964028 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594964028 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594964028 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594964028 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594964028 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594964028 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594964028 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594964028 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594964028 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594964028 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594964028 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594964028 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594964028 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594964028 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594964028 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594964028 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594964028 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594964028 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594964028 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594964028 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594964028 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594964028 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594964028 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594964028 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594964028 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594964028 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594964028 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594964028 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594964028 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594964028 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594964028 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594964028 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594964028 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594964028 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594964028 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594964028 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594964028 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594964028 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594964028 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594964028 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594964028 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594964028 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594964028 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594964028 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594964028 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594964028 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594964028 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594964028 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594964028 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594964028 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594964028 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594964028 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594964028 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594964028 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594964028 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594964028 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594964028 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594964028 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594964028 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594964028 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594964028 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594964028 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594964028 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594964028 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594964028 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594964028 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594964028 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594964028 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594964028 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594964028 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594964028 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594964028 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594964028 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594964028 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594964028 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594964028 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594964028 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594964028 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594964028 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594964028 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594964028 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594964028 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594964028 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594964028 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594964028 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594964028 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594964028 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594964028 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594964028 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594964028 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594964028 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594964028 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594964028 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594964028 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594964028 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594964028 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594964028 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594964028 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594964028 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594964028 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594964028 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594964028 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594964028 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594964028 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594964028 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594964028 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594964028 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594964028 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594964028 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594964028 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594964028 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594964028 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594964028 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594964028 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594964028 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594964028 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594964028 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594964028 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594964028 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594964028 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594964028 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594964028 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594964028 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 594964028 ≤ n) (h2 : n < 595143884) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
