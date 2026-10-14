-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3140
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:46:58.999197+00:00
-- url     : https://prove2.me/submissions/b8293da2-2b33-4156-9896-82a5494a3a45

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 564568345 ≤ n < 564748201 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 564569595 1250 564568345 564568363
    0x3010b0a080a0902060403110a05040204080d030b030c0a060809011b0f0c020102010f11210c0307050703180306061403120d0c1b0b060a09020304031e05070b010b130503010e 76
    0x200070780d440c0015510101640107100b2164010a125034850f41c034103113100c084001d81d0300b5500c140020780700082c55260620032a41100d5450000d0078413500f01c5407040e40103268900c2e495415010b4a401d580c03c035a1556011700203401d071034179404147e0500c6c4d0400b5003101c0c140034105001f5031074280103884098000703071001c68403100c9140031103084200340300403800340818011040303089007028100c210480008024110640b124001082065010040d003503010000742c9200714440010804100d500d4410701c020040349000b41403680300440440e00c4140300000d140d0041c1c17032103030382c070202840020510100c1001c4286d0840003000003100b8a401d0390410710888280401d526924201e103051180561180011038001803141862070b1154100b42c40d03c480112045480340c064224003003600403007071003500d00554040d0f5418240060760004900040042c120f0303d014000180b1600300044d40303150714503018002095200c2e440d1a20400761400014403038004d548240d0421545c50500200007842c549 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 564570845 1250 564569595 564569597
    0x1b05010c080f07050d0e011106100302210f010213060309030f031d0a08040614130e0a0605030d020a1209050d080d110a0c02033c0c2d030303010b0a 65
    0xa0740c0d02103840b604040384940ca20060490080c120820705040d0090550003000c1400c0e00c600d01e0301f000002c0403030f845000454406800c5d81c001c000a101600700500103400300803072841d0b80b8102401c28103415251502c01007911b503550f900080d411080480c0782c0c014500030005828180070709081caa801038007507099004440100343e692290f500c03000000e84c0114602050f102d0558440141038200600550711074003a9001040307010152031403014002046070803141d080090307000110300f40409030350721000c0684040e00711616200040783c2d0f544c0520818130403d88035002000015020301d42100d900c1940d03000c0f5028404641c07020402030715880001200740343d00909140e07030f40c0700e0b08070700c1801000c5141102d0108035011841500858001500342c500600807803c5600403034210020f942410b0030588004140b0450743c0d50280029a1540e078080c0c41c4070203c0941d03070503610000c04180200408d81e0b800040c0c1400c0c03211018070708245124050708243c00e8004e0341c555030410001902c54401c02400e44c0c = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 564572095 1250 564570845 564570847
    0x106090905041101083c0106050310171501060503040611090d060e0f03040602100e0a020a050904020103060306020f09090c030907031403090a0905220b010501050f0d05010803071b05010c08 83
    0x6d0710003401013000600d10713048404103a061281d403010702031140c0406240142082030100045441405003095a1041059000c0d40e41030908281c1c6044a2600e0151420910b00c5040303824101249940304070381c0a40001c4c0d40b0b25841c1e240c0b07401d22800380d40b24115143c0f01e1030010441a0b0031b5844241c0704040faa90014070100301d100c4c1c12140c152a140300e10070703950341d240004138000c159658003103140f10004801c12170030301030608042400c646500d00954004ccd4001c81d040000c100c603003041464076038014014100025190b50329240c41090760321030a50301c000c1ca030002841c03084902c3c11021081c0c20040039840c8504504d4000c10995644070140005818480c040c400707440c0001c400c004448030b06602030054007071a659600d00e81d01070401a1040308000d800c0e40d2560940381283d024104559400c02c0411030f06901c1c0100548a65108400011809500300304584481b03102d4043e5034024140d01009590301c031841c0c14030540c0d1410503807a4074100ca1085034104096a840300311104080c0c1c020102c1 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 564573345 1250 564572095 564572101
    0x5010315030c060f0206091b04090305090a290301050906120703150203160e0915120118060b0d050c152206080105032805190605010609090504110108 66
    0x44501015541c4010441c840c1c000000c5820f5602c5403102405603915021640d5540307610146c982c031000aa04400b4001c00600740300c40315480e1a8200b800702500908090780380c0078400f00443c0c41c1c0c2002d60059030001c890009500c4101c4420849201c0d12501074030200e0a41d4180f2000944849001d40f4042c03090080c5912610080380c140281c2d0019540607814940551503891800d0103074108459101d281150382c1041001140240d544003002351005120800c7c035540c21004103025514110307105d41029482014002480003407090140c1c078901e922112804000030320340707002a50301c46004c0307d014a01400002c0002100014000022178040307c00d17012884010805c24014010038074454960f18000d5440c0110560b80105801600e4160342c900d081ca07a00d6905059440194103802c0c00078620302c83d609803908030a10110f038001449502952030b02201a00c90282085600900382da0381952040100700300740d00301c2c1c2c052005140d0040117100c14501500c03401c0000300303c18943c505001c111000 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 564574595 1250 564573345 564573371
    0x204081b06040e1e06180a0e12220801200a0c2406060e063001150801060306031a1e0a0903080a02040e0103260412111009050103 57
    0x240d402800903040f5410103403070b200038200e6903d11108980340407003039280003094160501150205030561096014492522840d00030402440e900000b50b42034050300504c00c803205c01d844001d0111605070b02004900c80304981d201c1084401a82c40503142ea85090890a100b22086c14416800e040e4820f805880700c6400764103503404200b968008040003107501030251507080c0618800040d96012104014071038486006a40301409941d40507070240051001d80315001d486641503420f03d62041e900c41080700000a40e20300c00500307130420110f95246080390207482c0d41c0260303000d004101e54541842001c0c0f564490050809407204986050703152040001c048160901a052411724032440352440303840d110068800500059804400140029000c0b641c150003a00035141510040002c07030706180d10790ba031410358a04002050302c200100d0581880302051840d4007a0001300043d0210300d203450345512f01680765500032454a03100750101c411540e00c5541c4035543c1000e40d202800c1c002103032415441 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 564575845 1250 564574595 564574597
    0xf03160b03040c0506040609030b1302060f09030c0409030509180403050703030209060c07060203090301060f0e0105060714030d200715051009060311040b0312070605151207180204081b06 82
    0x1000e170304024006400100f007540500b5103011a4000c440c80899901c0390038000681c4c142c2c2c010007950041c0148509903541d03600c14014180144010300310b41c10000c0800204090314001c10301134010600c0861444c60b00c0c213092181c61354010702c030f02518005140035540900b40b40140e0034060201640803810341c070f00d81c030750304111401080590110348440383d8604000b0350301d50140c0d1010b4042d50030520002000c020300d0800605032103005d003c1c40456800e0330280b004035040802c080e03030300340425154100740d038100b8801170076440000f12000c0740c2e402c0c040c0c04101052500180d4900e94201c1044490f0200d5824829a10b00114183c030104030b50311032141c0d030034441c0e42581001c4075043c5040c0000081168880100c90002c1d402c0d1418844000380c0f904054442e008850b0054144504110b18030010300c450340034961000c3e00081d54010016000c02061441142d00a02d403115400312509000400903a5800014903003901400c1d0f00e068201030505403030710b0040070b02c000c070b0b0610b209407000744c1d5031050 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 564577095 1250 564575845 564575849
    0xc01171911031006110705010203090607062c070608073240090b010c061404051204050307030b0423061f050a210804060309020f03160b03040c 63
    0x108500d03140c2c00c00c0c0c0614000c994040c0704d0308002c5202d0413400c510f002d0000c02c030a0121360f070503006582404042e20611140780d0003420308507003251f590013100b0055034501c0c1c0429245003100c40b0300120000e032148158a855010740061091146210130491900d9005410440200304461b4042d003111800e00d60301410703d280811060034100c04100c0304048003110035120207140e1803017406c0c8121380d40144800001001c40b0380d807058145900c9000e200042d107a4105008030b0006142003404a072107a02d41c14103c0d07a0310300c03603112807120b004180014800b0400021245c42108940c05180c9031174400080c3e900c0b9241d1200800c561003c2c00040d040c49034460406081d50300040c00728104000180d225500c2d810100c514170244101d03502101290bc0d441c4070708405943c000b419030880d0904040300080b080181d000e50340910808005413400180c0c40ca03000e00700422013518040780d0700701648104800001d05404541c026440515500c01541031001030030304880844030306550720b44a900303243c88a07400d29 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 564578345 1250 564577095 564577121
    0x902010e13090204050f0f0c031506040906030506060406050a05040c030213060c0201110f03030601030209041e061a1305060c0f060c0d0c05090307060f03060f170c011719 75
    0x10000744003410303201c0d08801000ea200f00e03420081d594805104a215003000c0d0303079585403680d2000c00610001718600c0296000800c00d11440a441d204500080c800e41c0650003418040740c4403501001040001c00017240c0021048400344141404e04d0f011400301c2140b446143c1c441c036198030040601074043d5045030f80c500b2103040070f101042d464110151000040310300480c0050319a070105855600041800542d80c8000c001035851038403a41d004601940050720a20740c03060391480c5100c10030380070781c0342c03071504556a0a01280312450207902911030480750400d0100703000704000380c0d020208102041415180c04648054803405c5035a041c030f02e404070307449651b400d9115503814459103a10138400380000b00070b850414090040144012583c84c0107031010b49030103a000040034041203014115881e01d40b080c3d440c002541c0d039a504160700c22a40c241d4460001d00c4000354242c400f000301481504030a81c03082c248040a084802a04140c945009003090810124016889004482c64020b54140011 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 564579595 1250 564578345 564578359
    0x902030a021333170607080c0c03210a0c050904020a0c022e0504080c0f03010e0106060e031606120905030909070f0206090d0c02040e070909080706061d0a0902010e 72
    0xa09460001d9200c42124030403c6840c001e080050b100c0e110b42c5020003000c090300003414094548880940e40340c070015000b01d000c00014044610862030400140900aa0707208020480c10f0700207582d5880108c015020301011030070421050030790341d00102194040c46065078010307070707907184414102c0d0114100c04c07009500c410035038402207544407001c0044840c0c40c134043c802c0e03520ba0f24400040d034003446a0703c20031220b504030009002103450f200301d40748905200500045804800800c0e403d0850301d00c0d4201902081c80b42c10801902e08040280303900c60026002072071502d50070103074090285a01c0800d51902203444018003010040c0500c00d581561a01030503000b80c0d4182170401401f91400f80746810014420200003981e40350000621580030006502c9502140d034954007884084c0051900c48082446608000107030403074a40b01d02d0f10310500601103a605ca0b00145051803c4d0f0301660301000045104080a1049001e81034516400c00151107002855508a00c0165820340c001410b1a510010b = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 564580845 1250 564579595 564579641
    0x110f040212040c1e03060216060f0e07090c17181209010e0a032006070507030b0709060905090123041d01060801050c190c0b0412120902030a0213 64
    0x80c042003030740d00940c441d80d070760f03403a103500d6656490411150000e0304040c04140c0c0c100b080802d207654000d14903120205610100740503a503d602090f104a5000742d440c040d81c8103001100400b0500400014100c100f2092240f030240c0c05005100302100054500b0410002010070000b11101d02c2030f00d84000d5103c1500c0607000e0505084925410142900b070105a070082c50000d02e140140d82101134941c0100c032900a1907003520507204018103641c1c00341d00b00c2405c006540100c1d0381080888015442104554034502d00000001c1000155910880c103000c104d460501407641c4040078a03040d21403440c0e00714000720003d48085450482010003681051500e690385002042c5283c140541e0f515540c001e0102039070303481d9031908035072084800c084210701c01e1140030400140420921122031440c604a00082d08540b1148030002041d1411100300c3d11955914410a030814003225010343e01c003d0401104c001500842d032070303140c4910004c1c410745032a42c50281c0300081e9070100c2c1c9107140d485003c802c821 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 564582095 1250 564580845 564580867
    0x30c021c0905121c030c0c050601080f1509060f04020a17060901060609080303060906061b0114010608010803070b091218030615011211070f12090803040b07110f0402 73
    0x41c207502806001e100c0040c1c0402d03505000003840451041c401000440250300404120001c140c200b000e2000c004001c680c00d4082501002980d010b041500068022480d14071515890108a2422001203014100c1080f40b110404205d01350b0000c9400c04103400e0b943c4d144001180441d660b048441181c0040c0c80361884110b000410512440d0000000c000c003d03160f850680f80d030500c40c8940c0645034001c1000642a00b0708400054104401401e41c0e410101580c581a95180d81400e80604980d510400030098103006500140100b010f814801c1c0194104201301e600d0303200340d40c07002d070070988040049206a081040b42072081040d000c11561254207007802011400400c10304540300f441138101061102191841e03400b42400c05854200440005c421050b0291215407044101c25200303200000c04145200f6843c3e524074803d45280714a11444007014040100320b401001e05075200703100600180c0b010384221035246d60440315070490182c87c100000d154140041070940c1042c008102c031185c02e = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 564583345 1250 564582095 564582107
    0xc0807020d06051e2809050601080a03140915030402010e0907110715091e080111030402181b0d15091407020a0c03020108060f0a0e0106030f14010303030c021c 70
    0x1407005420954481920081031491410300340c42c1200e40480507454a40005e1030000e10100728089010085001001c0303031219070410400341e00c4888590842c00fa00001c02d644190800c030740b04401c00c900d070f05004a00001c05c0c11401010071002d5517080000c041400d580c042c2d40d0750b100f80d0000400c00b014034540b2090060180d203005112410a114250700410880042e02419542464940c2d400d0015490000c0d038040c1181040003450601d0100f1001048012007030140ca02c0d0303120f45041c080d690303080610611038540990383c0c1c0920080380140500203200c03074910101c2a401e41c954034040c1c03a8180e002c01340c2c0c010b01c905080119940d5109034001140c98a9070016040705035858104030b29541d80d05000e0b40c031100e0684d8001c00200d21540103100541c02180c1e02e0340c0210300035098011020000b40894034008407608217806012260004000d220b9040c06034400310024a0b9090001001d121002d0040c0391040c08001c003810786800c202103295100b00065039410100c0420940d1904103194081c10b0 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 564584595 1250 564583345 564583351
    0x12020f030105070e032b0e19151b0b0c25060e01060e01030b010b03191503020a0506091f020a081909152001020c16090605150304030c0807020d0605 65
    0x6d001e03041d1001140ca045241c40c2c94104203501c0800110160319400300c866810f01034005a01160801960081400c8d00842c8406410342c20184400e0840c0e0203c003030300c004051900040030006140010001955020310503420960784440240c85208000c0140881d03078001034071410039841c900d001000e00a042e04681c0360460315074000c0004585992411202240034000a044030214a00411600c01c0042c011540714081c1114a401114804990015035809104002080c140700c003041c000e500d4080741910080204551091900704200003041905250340c5845010183d550045c1030202d009029207202c2c940c0c44a4101e50380d030300c84500e185145111181036400950726400210b56102a07544410301000c00381c0724a440d158400803140700c0b0000c000100c8460707540a0144100d50b18040001960720040101c80300015818030323204504039191580f0042c4222101c01c222898040b031032007141e40154240c509550307580f00b14100806140f1034078a0094214020f82c1000d01403020035801140 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 564585845 1250 564584595 564584599
    0x201020d023402240403020a180f0612030e130c090e0a050106050d0b1504090e010f2a1701090606020d0e031902010c08030406061505040b0412020f030105070e 70
    0x2121068400c0529080040b000029041059454580a0350f0380e2030828414071030400750350701c0c5420b0b2070f0713408116003c0c62a40890039030f0140341071140035400503004200038601204000c0080d2071030000e542c0c03204608890058148000403103a0102600d541003200341c1000741c860240701c0c4034010a4014200141c510505002c1c0243d0000f10351188180d00401d030486545664036801c207100091480c004003042016203a118000e44c0346030008000501c0070380018107a8800000705155104601c0f800d44803081c56112a030351803d941c1d0601c07412004d501c84410000c40803170181a16040f4000e4844481e8100c3d804441e40d21100001070071a074035000baa00783c50003503003590741040a456050b1030809088242c154035410a9011a8001d02060384880280340140b40c054040080707600c84031040e902c00d45054546984801c400e000070482c22400403040e030740614019180c1450115019294080c40c094903140660000211087d556014006028440c0080c02001341d800e104c0f20140c002003c2c180c400d4 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 564587095 1250 564585845 564585907
    0x17030307020f070f05090a0b030105070f030e0703171c0501030606050f18040b090a0b100303030605010f0504030312020c030d0b2d240c010b030c09041a070201020d02 73
    0x14500c03140203c1d08404031200c0e12490741c60942403038100484188001d01055801d9a01d03400701b107182d5070074040d1a01560f000d0b100c010f4100d040a100070269882c08080002e59800350700c040000070503505c416444425042501d903103a18251201c40d0b90001c00c041210040c40c285030010062040b65400441161404c485000c0712401840500c0200700481d040c2e00540307100b50340050b000c10340d1038121942c4134101a0507180102c0060b41c2e004400a401d648000364600c6000d001d0041580501c10350307000e06000d003850300080c40c0c1030030b0050091040340001401c201480c400c50700c0051085d0140d9400100c1081030701d44503030400d60740c00000c00554803101e226687c0380142c403603601c08140c80307c410041842c01d2500c15400c2141030007004a1902c0f07404502d0b914841d001d5900d81d030100054141e105082c0d0021400707483c840c0415241812042800d8403030840a800d110004001900d00101d1036900700c0c0184607980ea554084c1d00901620030002a60350002410700e60201030000450042031a00c0010 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 564588345 1250 564587095 564587113
    0x60c030f010608070507020f0102031623011407050a0c15020d05010609050d0f020a0306020301290a0f23030903090a1406090d241b17010b0a0203041703030702 70
    0x100c4010000b44c40c4000031660030070240d0b001d42819541003103a900d040c01141d2800d0000507440b01000148003041e83d5480c8002c40382103081d05c409142d42070002250000340b05400c10054510176440d0090244c0060203800540310320224005e1404d21562030300110a100d9600303d800741d2101941c4440880c110703903450030740042034141c06080020300b034540240004903c0b8403c0d59900084840a080c140c0e8085101e00c0000001a41c0303000540c0a0141d00c06002c030180704403042800c44180102d92503220840901c02e40b02c5140d800340c107003c21040309180c1440c6180c00a122101014002581008031003000410030006010020007480b040c542a0303a100e0086540300b03820503114180c600c0d240d512132010081240903240800c00312150300e0062001c1c1c4a1001a00d03030300b04500a0b1801c3c414843c913165180240d8180179960041018040c60510403c001040e01e409130b0134160500540301c1810b00800e100303150600c04c205940151201b03091010b090a0702d50403040d03a80d001114044018403400020b = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 564589595 1250 564588345 564588347
    0x20a0804060b0d05061b0f0d060f0b030c0d0506060702031b100504030b070302130f0608150910091e05090105041b0b040b160b040f1b050a26060c030f0106 68
    0x70050710107130414040c1c0040d48030036015121480030480c05001856090208154005a0200900e850b0400b5000003e000341b03000c2000400721400d6204104c2c1000034820080401c0c40f1300200e841210030900002841d1350f40900103059030240a0700650184603039415140008149180c3c21107100085400710400d078640001240c0522030313400000c01031046180824202402900603181c03000f405030a10300f2141c2c4071400e003403200203a0390000000601500034064800b50903001640d03d0001134a5980d0b0514100c2014044158648604400a9039804404180345a84100c110f00c4103100c00b01442241070012000d40600006e540644182002d4101c2c0012016501d007a003003212a00b40050f0305042c5800c8241e40c054005400c44001c0700036414090b0b000a0a003000b07940b180c0d00c1074200100c10141411b01c01407000d051010107840c1742103158140281e41d5107000d0607040700c000c00e00c098050f00c2c41c007038403101714082c03504040e105102e4941401180384c0c00070003441c420440e6401c2000241c0c0d072000 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 564590845 1250 564589595 564589609
    0x7030318112d12070302060c01060f060903030e010c060216060204050414040506010e150604061707050a170c0708040f0305010b010302131203020a0507060906090e0402011b0510020a0804060b 84
    0x1451042c21803a1040481d0521078805840d03042c542040da44929602d1700403c00e1984140e00300301469558500601110703005a84280c050811072138040b540900710b40d03025042031050310340a81440014644001000b040d82c04440040d24101d0958000085034a44035001e0340250086602c6281090503181d900e0100e03003e040c1c8078540080c010580c59180c04024203422402908000c00030341000c0ba078410075118040204001d200700e54402251000b44084006010b1010745008200442008100750047d8800b9103038003917210b02e0442080a481c2d075080c01407240304070b02000380402030101d80010440301c060500804c49008000034000815102c00440c200d10800244405402a80005104110441049450440c8680111a61180c803030702c60701c2c40d110581e80141c0001f001c1034030912001e548074202c04000e0003000b540c08528103040d0700203810314810045503580c44200035070b03035824001c041000c21250900d0100031991901801c2c070041144004480907119242001c44911032030400038 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 564592095 1250 564590845 564590899
    0x61106041a1003020607111f021b060705070303080720120a021e06090d031e02030c0708120103020a08030a02060c0309011d060f16050306060703031811 67
    0x1801180c404070441d04001c5280e0005000d80b030b08050365500c08001078030303900010b2601d10700982d000740d8140900e00401c146250079000002029404c1e41100c842c1c1a0006142500600c40803026488040400041085030059880103070051151503800010b06800082160061440b641e07800c84262004205c20752880a40342d41c1c00003940941055505c0390101c070050002081c042c4181c0e08841c00e100005181d40305031240d8905290070003014020854010051110383c1c50540c00c3c01d000707040c0202d940d501801212403800000c10340000000761076091000c00c481010b41e004140a03121203030341c000c12000300824003040780a034184d58004148401c3c00030588165074280c1d4010600d40da100924204d0380e40014106921941d21040e609035885800d241128100c0f840c80020a414940b00c070143c2c8a4103005800801e0100440e120035014540c000700b2030398440400c0e140140d0322101c1b894101c000301074400d098210703064007c1e00f0004212102c0494a190f84e011070340e10252141c811070100b00c00100c6 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 564593345 1250 564592095 564592103
    0x308040e01080d050a030b04060512060105041b020a290408030702071d0406111306020f10140f07020715020c040b09060a031103030d0c0c0b01090b06031f15050406110604 75
    0xc0c0304208103103200e81c10101c0d0061020317101280f4107544ac4085080e18003e0b001c0042d80d034000600503c95404c05104118080d954440300c030303d010380320341d4001c0c0d1103074541c0301d0240018244046c000b003004140c030744603000044401391000700392909051201107500705840c0c510060049000000d07284010094a820031241c034506400386840356600c83c1c00401e080004104102000d00c03885400070f0007500d00800520198020f8110940700300d134507908102145108461442c507219050541308244221540c2c01624043c0f03c58803511007100627880d142540c0d206080410031412003515496021170301c850340c00e0003980c05024090320f0340104040444105d50003a0030042c032030001c0001c90070401c2c100f6203106010302079034907080c80c3d14808000e99281c00e00002c0866107144582c82000b000c45500341c010400030804000c01001607001641922003e44168002580742e01d0954240b070718145020020814000344000003401c18401030001c0c0c01c18407401000c103260364903d040d80400880e15500c51540 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 564594595 1250 564593345 564593347
    0x1020c030f0403351803010f0218040510030312111303110a270b0907021e031801081806100923132f040506030d0c030f0311040308040e01080d05 64
    0x95130010300c04e5000300c00d0215900c602001102815242840750099100c2035140240e03440055010410440144820b100e002c0c6107080100b010300c1000c4421401905d9040c9031405141c00d1a1070380001601031024000d500c05400107202c0d000048245400c0c0c1128071512090394403429500030040311a0b900d100380f50014000f104444204110540d40030070421005200042422194011951081040b18040c0142c3d010315000004981103a0404000c0c2c10090001c0d0b24240c0a44d001131404400e154410741840300050108402242d000d050300031110115044405074074052903501c0340c0c2d04543c41a0000c961a00c00705200c402d40c64940e46204d000c0049007030707a4548a045010803808081d510070b41c0d161014107202d0911a0500140301030403602100801550f051080c204021581d0181c4102e200e540103408424030270790011000008650182000303010180925415400350a0140090350a620006004000c2244040c0500b042e0303910f146407403159a0701c900003103940349041c90500f030104030 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 564595845 1250 564594595 564594683
    0x12105071502101401080610030804140a0518040b0703020703090302060a0c17040602010f0204030b071101060b0408060a0e07030b1f0905040f12020105010b09040e01020c030f0403 79
    0x401c100414516001841180c8003043d8802d0b80d030049443d050000c0008102c54001000750b5182000416000001d21444410191441c0d6400040e80325511407107200701d00c2c80c2d80e02c01080c0d940400081c018400540200c0e40588500c5201c8181e002c00c4501325040790804022400c1c0303511910a4445d520b074142c5401110b07506540070005c0b9074100304d4682041202d0f0010520014980309440304d20241c60051a50b181c3d424404080d09442c4191a00a1000d00c14402080403850092109030000d049003807040041c4109401c0c14090801c1d500058508800080c0004600c10005071035482030729400c5042281141c000659511200c040c4000b5000d0742008004c2080724550380c14500c0b110b10094008940c040c3d48000c039900350341003101e05441c3c2c94103581200e014400e1103610814883c2c2503200800c40f560500b030a82c41c0d540a10b44107280120b0b40c0e9005000840025030480b07602d03001c0c1200f01c035291520300a9402090340140000c83d52052822a26855100031078400700200e81c1c1480e079800110 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 564597095 1250 564595845 564595859
    0x5130804080606100302160f050127050d020a080d020a030e030c07090b03070602070308032505030a151a0706020d090c05030d0207080c06090d0f06020d0e1b0d0203070e01090501210507 81
    0x41c250275140795584e49141c1d060343c40c040f51088821302304040501d1070b0980505206013010041550f000a5421009820000440ca081210306d0181030610041e2103101c1c83d0000c4005100d007401ca140e0512000620880c40d880008131301048803004403050044100390005c0c540c9901c042c0c481c10015030302424081c070024100c1c001841e4170403090b10541e4501000d11180e803085403120b00e91240841c00000900020100d540980c68110701c020102e00c4826240440d40842150300003d0588203802c00311380c200411030550111051403044110500c421145c500341034241001d10302c5140d102c0c0c403030341c0f0740e03440918000310b011000ca50310500a0032240c1c1026007844010b521000360380d0352200880814000050403440d10758112401110700503200e401030360420003142c105962600f41c95103c001554151028000141106081a15510294441440440d16203040c6401c40b8a45080080000c980f400260340840c0c12918010002c140111021350020000c1041c0301c80a026908002003d000344 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 564598345 1250 564597095 564597113
    0x1f062a0507121e0f1a090a0201230d051609030503040306020f0d0e0d0318020f100e06030a0b09100b16240609050f060a090513080408060610030216 65
    0x440c000c00f010043e590b114480a12001004801111407440003101c450030300801c20001d10f94099507216102c10703401c00c01040b5a80f41c2c517500b4001d0401045c0307159a409102c02804140b00010003842c007a40f84c0c450180320b103000c0c2c00c0450740202c1d111320070480e555102c0d1080204108681d0000040c0d450507046491340c9010b940a9450840801410400000050b242d4410703c0c2040036a18090581040c0540c0001c0030b03074180c3d0100340711710010402001c2c0540d4641905000c82001103c0c001031040651000760340c038204000c1c5642e884a0003000304211880140c1040a045c042140d40741d8942d900c10000c0c05542c031190160411091081c49039104010011403840c1d130441c0940b207205000c00e42c01c1ca84052280d07010340e50300c0655817a02070400030701403140121600840317040b00c1c5004c9450f00401080900c4554450002100d0f160401b09038500072405100384019004601d907951151160380070f42c0d49420542e003617400b031000f485525605a01c64401c0c1ca1401300c0c0e00a0a1102e030406448030050 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 564599595 1250 564598345 564598379
    0x201140a020f16080f0c0c040f110d0510090606021509150408071505010b0d18050d0c03260f0a270c120b10060c0305070b1f062a0507 59
    0x3030a0004c00000405e4008440986862482a0000e000e101001824042503410280b200c040075030134500c80541c4e013a01c03c2c080d2030901c6540180042ca56855441340c02000385075034442841030f8a0b010b4003182040e404540880030040ca01c01020080d01d440181660f114003407030002d07143c03008810108000031078200c0140180d5005084903a08000c03c0300003d81115002ea2204015a00000743c50581c0700386030069006503c00d2041e44801880e55071681c079150420881301004001c0b02d65110001c242c043c401c402e5149018005404019580d41510340e180001903d201c4030320800340c40024445175141c041c0700301e5440030b41403502c0c95030030001107001216145034045130100180032011407441d010142002805000b131030201c0007400d000307074411620040c42d000441040b00000481c0b01280e000811202c4c6a82d0001c002c1c0500e550b104004040940010154080400b807550000340716603002e43c4072039140c40c0c080010b402442000b4981284003024420052254000c56003c204030f06086001c1c1e00 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 564600845 1250 564599595 564599603
    0x80601090b0a0201090c0f0501090b1c05091203040b07090905070909020309191110020604030e0d020d0f0302010b030c0d0c172e051803070f1b060201140a020f16 71
    0x40d501901b99249040f500c815006401c1426490340200070569006800b9402008044086464214081700c048a251811040c2380d00f20381e01c0701c2c081180350000700120b18000c0340f0114081d0700e038101841c000040000980e5900d0029084047c0820400710724410035004101585544030380078604442d0f180603400c0209415440d0080101540c0321680400e10040980e11510300c001c1807114600c03c105400e140703810840e007107522071020800041d402c01c501103803028080341c2d016284061032000440030113002500a0100d804010312004054054101c40f4890300d046040c2c61103500642c0c10f105940034030400203803207006002d00c02c1262820408004050752031080581d428000310004018015580c0c98400500440c4c65070400c0411049100b602d80103041e000c41e0810441030a17040f113942e401640700240c0b1050619a42c2d40070005c1c00c002c00c040c0b0020003a0081c11450b980c00c0041d00800318924601c4500c41c108001982d080001c3c8201c40c02500030f0613100f803e111010000040210072400c00312 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 564602095 1250 564600845 564600851
    0xb0906030c040f150305062e1703090a141f020a0602030604141312020106060f11071a07050c030609030a080702070308460c0819030c0f080601090b0a0201 68
    0x1841130540c0e49000610700800c020120740c100450409032080d04294451096000307003411151512004440d41c0896000406050303140107100c210710700314410401c119038420b03281c0000285a8122008040407400129041020b0240003c100300a00480014400040e0442c2030101c0009500d507000d1900031380050310001e428102010041800340c0c0581c3c10201d020580b550f1101008001581441d10300c01c3c0c1d00c0203004031032809802616801802000c030007400604201400b042000300071100040c001007004000d030407411007000120303500568095501d0301400c00340f622141400241c150051100c00011071410184000c100c07850900a05900c04500800d540040402c030600c0c09000300c221b04242c1d1071440c14004c8000301f540e904624a204100c1c0300c900f4217071080800d082d0b81e845120b1160078040c1450703000c0c2c03a0415843c800d00501e142c0051403040c45000d00c07503041d0310031030001c4100d41340d020826000e1081a140d00302c00700d6110340024050341040c02880030343c801810800100380004 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 564603345 1250 564602095 564602111
    0x4050409080c0d17161205040501020d05041202010c031e020906040e0f160206041709010e06042306030f070521041103120a0504120516090b01030b0906030c040f 71
    0xb9900304466100703c5000a5403200c6001466060844215007007245017501801298140c2c402408042d2260f070500703003480e540d1001405010080d01111100240244100210b01c1c180c60050070003080414001c005601c1c200c14010014020b215500d449801100d06425a888084a14010754420090f80d9000281440300090489075413040380d0044841416080721458194440780424901080410031075000300103100102c2d044038942c0020b5408500001d0b0f0b604030400040c1c403d4840c10345d4441d0081c40000e0300044207080c284080c2410702440d601404100c118a080280724042560a180c2009014000c1030301d00c3e01900003000002a050f101486101c110b9000c0c10403040119415912403a081c514a0314178a01402002c80e0712011f1003500382001488080141203000f68001c0080d249004a601c90a120040002e03d80300030040003443e10090f01c582c07660b40581140800940860b06103008003040b441c20b41d2011303110742c20241c01071510205150412024024418a842c041c40c2d6500d0300b = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 564604595 1250 564603345 564603367
    0xb0c0c040c0908031c050c2110210b0a020c030f1326120307091413060315050705160602210106030e06060307031e080c07170f120405040908 62
    0x3801c0142c50710fa0401c0a000440814141546c20080210f84110700030007450003980810726545031040c40070b8001e5100307540c0300b0303504000e40346c510307045124450304a03041e00c1c103040c800084c00c4071118424901c2e24219240c00c0c0302c0f10140d0060142c842ca0070f410a00401461280c52000b0304406407400800580c03c640c1e0341d2908402c102d9200030700c1c0101040114110a200c810070040e040c26030459400351440c1f0704050000c1251035a40182c9220382040d800703640c0030749d0750300a6241c03002e4800c85041010a540b132901540e0200380d01c1c00c00744154248000280038a00440036205405e910890010025541d0340d04c42c2c000390710070f220191303401c100510155202c05510982d64040c11081e18005850903032041070030702e80b14000307010903ca64080030040c000601848000d80740030011015100f11100380c0d1503d0386442c050384038000024400d0010011790b030103c0c1482860400c81c10025900041c9000307002d203846112002c55040c10400401c41041903007407030b80c00400360700e0292403403034181824900 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 564605845 1250 564604595 564604597
    0xf0702010f0c0e010e030a0206030606070f0605070309050f0a0c0e0702190326010305210f0310141008150a030203060a0c090503160302010804060902100908070b0c0c040c090803 78
    0x14080001a881503c0603007030350300008420400c8200b1001860305d0b103515400038040c0e01c40104064082c803004241d40c41007151030741050300c0341c5a200000303012914000d8001001007072445810388052007601d4009030f01c1c000c00315152146982202c051b140e21814051401102240500058110702c9620b41e01d01000c03048002074400d941c404d5907101c140c00d51581d060301400800117211002c00c894040100b000680025810706140c682840f00b1004807802010701449008905151018550020030814843c001c1a560030640d410b0b007041405030081007052160320003001c0452404070300c240b0042010382c1d20200d007015030b151000305050307000c1c1c0e2607501090400d04191a004106503c551407c807019410840e581c001d028140e0003005140c84c002d0250222031500e200103414080e400c4086414042c140d089014241c0c1c014121020303480c00040d001f0506070442c462030754940913411002c101d040c0c0c41c40803200c0008080001b081050311180402000b000c0070b081c49002c0c05005030307000400c090184 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 564607095 1250 564605845 564605861
    0x313020d2102060718090507021e010203040302012306041505040c020c1e0907050306060f040311010f090807030b0a09050d0c0606210f05010b090901020c0709140f0702010f 76
    0x100300181c400d42521020b440d2030740c06000c0c0d906001da0354601c040d80d030701200c03a00c000b04d405d0800d0118094032504401c1c6d0421201404000740700606110b20004140150000e500a5103e98000c01c2820840b05030300c900007a030680351075082d0a4501c013041c1c0f145030a4214516400c01e0320308940d20700780c1d10400a01250b889910030000340e007004074008814500f41580d006c045540111408591892400081c2540380c010841c20911902101094550311240c084d161150f407000412662a501c9061015003189c05c0b281042c002000040030b80100e91080200c8422071360020001e000362401c581e03540760102d100500044143d6a5a4200404100104580c2407021040c0d12402c801c8150703420700d5820340c2c0041c0c021008a4030030300ca200d14448100d6402c00013a07a0001c840c4103904041d4500140541031039410143d00c498000248252068103500a0501c00003260072035240b590384401c2038080d10206071003040c1d82c102507000900700c40b185407070703841c1d100210b8800054400301d00d01002c0c0454001b0 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 564608345 1250 564607095 564607133
    0x19091a040519150e0a0506070b04140c060403060e061005100e180f01063209030a0609061e290a0906030516080c220e030304060b03070f03080313020d 66
    0x11074861441c0e00b40545c1c08030160070160381803450401d8544522402507405400202402c20b40724901a4240302400f004044440062806070344644c0d81c109400070b00a040d003504401d01a84001c140c9801c410b08a00c001c03940301410803610701c07a070030109450704004400c0701c9803c02a03041c203401404111240c03842c802d100d0401ca82c04070f54100000100400381e5080610f5988058100d25840808035201c80e410703043da4003007040ea0b2444800b01081c1800e03000c4000030541401c00c0c0e0140300308082d030341090b03000101070056010404104090708003a00c1042104181211060303406030100391114140060800c006800f9007a06691900b5080841310290300a071004d4001b90160504d101c03507030340d0706c0000740b4010000f001d00e2001d5100007020801c8228a0480110301c0361503e49082ca040c0c0c000d1481002c14405894503443d113800c0c5440a007500b04803403031180c010343e0004920b042980040c4000d40c0d41141515096603144030550242ea84d11072070a03640050311482c080700065080e8413003486401c1c0 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 564609595 1250 564608345 564608357
    0xc07050901090f0c0215011511010c11120a2708030a02010e1506031509010e030a110c01020d020607030b0301290a090b03030a1206080319091a04051915 67
    0x3200e1540b001c94600180310300854122216254104070904060341c11b48c1d040c118121a00030000c1d0058482840c440c51a101950a21541d8119981c10003a40b4040c50740d14410b40307100c4250f0080c410340301d1140241c0040404d40e1500c501400f903440b0348098845042100403042c0080d152002c80307241d50052080c6000603074440360200d94414050100c1c500d01c004020007800c40d4104040000e4032078a40c0e00200840988003000985c202c202508450022040c00c000e0703941d50450300c240142024684410301001788520450040c89520015003d8140000b070b41c0a000c41c3c0d2254070303084019200b5491090303410341d2107094498803034401c8a402c00064504000c003458038925031003807103200b80031503000b20021450004811036540f00401190000d540c20b161454504101c0070003040280b0054000c0c0000d44004101d1203480510380390010800d0040f0344540d6941903403010640558060f070b6141a104441c248010001820564010a55168140c541000c29138564007000501000e105820001074a = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 564610845 1250 564609595 564609611
    0xa3f03030b0a0308070201080402010e04020a0201060609050306041211031c09030806090907060c080d0e1e030903211c0b0f0d0230060c04030c051c0201050c0705090109 74
    0x40c152280c06185282603600410280c50743d102c6401500400c2c50103070500002000090840e0310900c10002a80c000500842d00c48100101c000d000f440355025500201e2101d81011030640340014415202d5980300c0005002094140c500702c07400000b48081e142280b0083c0018a40c0d0341655890074281e61b1403410000d8094a2418014040500030b0031031406903001070705000340a030001c51035101741d911504126040300d0491402000500c10358181114907403410506003249440420780c8203104000d61504507002c094603030441e843c4d101d0b0782c51040d41075228001c10b5103404441e101c100f2108070f0600800e810400551400c02a012039159048034140da00c4410190a15140241050602041e103220084603c1035000c600850115003150301c03200894400c10450ba140c041074240d060450300146c998600f010000341c4540c0e0072030700046405082585001c070303850030185101040b070303d0807001c0d0400b0000d07503400540d02540018103000890049600109242d100e011100d4000e11104400080c000 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 564612095 1250 564610845 564610847
    0x4050d0309080f1b0d0c0614070515011707150c030c0602183a06020405100c03090e092e021c1427030d1407110c0a3f03 53
    0x10408003880f51151000c40c1162000c62486c002c05400d0710b146040c1180c442c041305024130080e02071000b000744544104c010042e0302c41110980a41280c4501c800190510501c50751142c0323aa03c18060680d11010041c1c0561003107110715100142c95019003003207040340f841910344609a0b40610822400001100301c2d010b01030800598107070465240c0250025000302040b598014000d1180030010090200145c9070b041c8001a41120003c0100802c0c20440d003034900c07400b4040014102045d404500c07000c00015042d60444819841104148050a50a2156001d00092017122820740c8031030a0065400a08000d052004290304403e20b202e100f029400c0c0d051500075140b011200200f1152030744107200c80240402c1102c0c181c50b0180c40c0706100f0002d6804014914090b01c101c0d124214102041c00e80d0381282c2c00742c440d015000f13584c1c0f0710603e1900584029070342e1400700e01c40b6411003032408040103c3c0c400302400f01991040b003902514107402e1045c00112100421508044566100100000b05 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 564613345 1250 564612095 564612133
    0x3010311150301060509010e030c040e0706080903030105010c0f03350907060c170903010501091a0f031905010902061210090504020d03051c0e03040f060e0604050d0309080f 76
    0x580303400314075403440d0b06014004005e409850580c905200c100510a991039409218500c00c03200301a10802062001c140d82c0c960700e0016118030310105080c007001c62100313480401220f0690f41c0684520a5084443e41c800b41c0780003501400341c0030004000c440e18244a036040780342e25000d99040310400d07202040b0028440300300d0090801e41980d031100e03004004030f070f070421108803401e50000d215034001c0c0e090840da24483c1c8a101d09140e8154039050000c101540c07103078442c00501407048200310030a03800c8001d0248010210024560661040024007401c03a84006ea49550b540301e2000811200c0300b0b5400314400303411800904900d60b008800b00f022040302e416006000f0408844284624105600030a21006c00c80308054104040014607810001480e079000d948505202420403901c4103001015440f0340090240301010b0706070b00c0c000106944903e8174480ca4540081215103480d00d40410008041c1e4640000c40a000890a0015040005001c07990044c42d80c400a4112010f84115018031 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 564614595 1250 564613345 564613369
    0x6030803070216030209010501080405100507090617150f0402070203120a030b010815060a2a020103050c040e060d2414060a030f0308060102120c0123040f03081b03010311 75
    0x183c0e082201040016035a90520541118028204001c3c0c80d101c0f030030001d0425410382c0c4004559401d001c24801000c0c0d001d030851007120f60300e65441c60360312540f011107038000700c0c00e40f00031b1064103109201e0380301890300395401c0c004000024401482c0c401c680c2e010900b840329266804e4100303000496051318050301402201c465490910300805540b40105106c1c0e5903082d40b202050040e000804e19158040c0620011464200c00040159143c0394010b0113400c4902e40c490101d00207404c1034082406003240005640036200341411166840d500c080501c1030502d00c1e800181c55058007200815918000c0313005032890807040210100b0f061040b807124030742c285009454076005903665030003000030869420085074440da2502c1c250755151207a0300100d282000305559621002c0d000904808061015400501c006038880c01610202e00d01c0c4a20802012080b20003810103e281d0701c2d03c100092042458950120400040c1c00c240300100c2e6018480e41c100b60022550f01440b0b0100d042203181078142815 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 564615845 1250 564614595 564614623
    0x2d050109060303021218090c0a09090e1011041208041401080f0c16020a0602070602011b02071505041d181606030b0d02093d27060308030702 62
    0x62a69400030369a080b0680c0180e43e101012602c2c00c0128540001b0080c1084d00620808003400d00e84020304240c0e0051036510045418880001000d82250141c00350501c60318000d000060950920710300070300340c03254410044410401003c074840384003030b00d8030046500426010317880e03e0905042d040340912416617281800300e02c00030001e5001040002e20340c440851a24140c840814042c4012501c21484000790300010780e083c0450300d5580051a102100c0e041d0b402032000300f00b0340e440f07456180314040d01100140c001c20818410240c04500c10414894186403880c503183d6550394a03009000264140c402d007502d2107050180050038903c8a400403d0400d010741450032040c0b035003c0d0000405e100c0c0800b41916068801180d41e19078401401154000e0710780d92462400c2c0903500006030f808003d600c180c44000100c0c0404002d1910b0310701c50000d03041d081404940c10801d801c42c0e00902c43d40c0a81c1290310004441c4481c0840380540c83c01580b159140c03e4580c00c2000c0042e00700040703081011 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 564617095 1250 564615845 564615851
    0x515190b030723120f160e040206031f03060f0e0c0904021201140a0b0913171e07050a02040c030b03060f250e01020d050a080a0c032d050109 62
    0x100d60341c00300b41e8604a4002d1803a1448400c002029000481001090319920102003c1d07400c2001002150b1004031041e600c1c00d0b00c4481c0c09171008101c02c07000034011158903100f8140050010309120f4011608000085548003014242584102501100e03400459140b80c0303946030441c0d400a00d0141000780604600602464500740340810110352000b00060311034940850285201c400070b620950f0711461405114500b072510010000c00703040324423451805619101c0c00904400400c00f803c00c0b049500181120496002003c40c9906410400819900030010241c481d00900448010034982d48200c0240080254600401c021590a0013910080c1810301c0654440c42d0350210341258000900c0c0790000342c84d103840c106181c0c00c07900c0303075440850880c0c401d10504049030403200c01c104038042642140c940d0a000f41003200e090190200c0007021682001c04514070320081d130401c91440055190008103800044411080e42085d20b0740d80890020600d02400142e020b40940c501400e03503020b0174 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 564618345 1250 564617095 564617111
    0x1e03060510140f011b0c0314060f0a090501110301060f02070504050c090d0510020c03120106030c120e0a020910051311090d06060302040903030f0513030f1209051519 73
    0x8400700611202c1d510320424100d007400a85a01550800015408180c2c4800240c0303003a20b4210351310200c601080e00c80511041d0a401c4540300096010b00c5840510751b0260152600500745016099000c01191503540342d40404d00c060100c240618000c100943d00d00100d511240006403d00a10303400c424051810315042001c0c0a0071071080742c5800d042550080c62000903818160b042c1441c400311285445d0000508444110001020705160014020a544903982e181c40a504a07902210700038082030680041d004c242009520203034580c1c41c01416510300c0c182950000c0c0b55610120350b100d0780b00051071418044c608000142146d20f0018440410140c12070120001447c0529099184588858407040702080000d4016a0080d40d016100f030000f0380286c600a40074100c02c00340050a18900390001e10b0707201c03e0040701420740350151075146040c0c210704804c8544100344219454250b80700e5030075200042003000030340d41c210307410401c0d102e03d424901c41d10a40346004101a5195508005c25 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 564619595 1250 564618345 564618359
    0xa05031905090c010c0516080109030f030c1209112e05040b0301140a0801020c030d0c0e0f0108071107030f0b010506030f070804020d050f0d0905120606191e03060510 73
    0x40d43c6a888800d0910503020075440c44d00914000d144519041d8160108034000381c605015000664818400d8440380e50788000804e04404a401446002001943c201345a0041c04e20941c04195041e005d505803103c80b40225001c41c01201144140070068050010703040085140340f003509001e80a5444c00610300ba2402c121001e140c001801040c001046802c003144c403540d5500300c00300003002d07044004c0d900e9041680c03c4540b030b41c0141110702856802c111450601e03d20825085070000002403151218401a4004440f04080200540d05105045006080185082100c00300135441890544515a00ea161000240c4030607403160707015850610501000072521003007940c0c01226417806422969a87c000030302c00200c00e4501520500894540d92074603040460454846249512410b41c0326a40344180300c11003251621034111908000c0224403180b03400203800002030303940f420058690f52115000300714000e00310904000075016030820410401c15000c1c10340c3c001c8100c40e03003154251034001 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 564620845 1250 564619595 564619603
    0xb100605090f0d0507090504110103110a030b0f040905030316050903030706090c09140601030e1908131523030106080402060a031515030b063105060a0503190509 71
    0x3079500c03502d942090078440b034a68a0107441c0d03564101e012580c00f1561004500c000340000e0760152801000013648906550090044001364005030840a16014610300308030020581d844003a60300c400d98101080c0d10740d445004d4901c00c1802030028603138070704204c0055640380c190081e41c5001d0220a001010090382c020083c1c912594002c100416178024525004c100c804660f080501714070301d40074030b00184007030b1169140e224075130a032002c00c0b402d1091855180c0e030b09010300c6001c2035501c032440c400d400240b808026203000c1c01c00c0280c3d104c5060701c451903490202c0200508400180e0340c0c258141e45543d03204c82c2e500300d03c0304482c0b02c1451035042034402070135540700410107401003800140c0096624445c0c0c1c043d011006280d45080405600c45190b00d403401402c0c598140002d04003000d08040e854524104e5102d807009086071960100e4948049071101e102283d900b00040c00a00c000500c0e0704ca55004010895256840d5640c1c2d2800312142014034a40c00008012030345000100489518001 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 564622095 1250 564620845 564620857
    0xf060909230a12080103020102010e0a0213022b050f0f061305060117070305071205010f0e07090f06030f1d0703030806120106030c030203061608060409111009030b100605 75
    0x1900c58200c07421003003001c42c0380010b00301004000d40c01060019010581c042580f0703040c0ca02c03d070700034061b500588550b02d41e98500010065404008403480380030449041d4000d242c0d1070038404400c1d1a11612031605005220070010301000c0680340d40420400401c1d09890300d51020060a83c0a2181000d10104207040242288000900e51394004108541e01401d0059040c04c4c0e0116070310070600d441c050003805081e0a541c11300214101c1c49485101881c640900e5061b0b690300d48611030100d113060304921003000c01400550078004a100003182e9180c2d41d140c600c01500494401003030810800035031404454111161001d00c0840080e50b1814020200381c040c03c8a805143c01d41d85074458030001901c8000b00008410f181d0f2a040e000402c1003c5080300400320381c02181904c03140c0d52008070514410415079071030b50008038040f0024003946402d40c046000c65000d03400e0829400605008213002a00b4003420b900030a48018003001084005449c46038060003159110000514115010706580036107 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 564623345 1250 564622095 564622133
    0x604050706050a03020f030907080607020a021807050c100204050a05060c06071404080709050a0e0705010c1b180915020c07050d050307081b0d030507120e150106030f060909 76
    0x5010805a20a4040c1c44080070755900c40c070387c1e906095001c0350703a40101d481a0788042c040c420004a00c40e001140c40c030101c54026001c0c0d09259142080d001f4900001400c803418060140041510700c041005400403503010b2038401640d59080804000124081b030740100e01c11a410030083d90551030206050f500041142800c0400400c840b18440c00380c0596041440c40303100d48000069240b00e603810440c0100c400900c1000116840c104040d1106001d0140d203020071100c090460016500000901001089aa0038202e0030345900c100c08011000f00c40340c450154603a13001c03805000d4425158040c200d4032a004501d0581c46415643e1122200e100c0c65105000a1508c08240705051080f00c42455112207819550501140c1100202100e07903c4c03005c0c548250b80d0917031b0b005406807160700e00400b1a80c41d000c0c0c1c81c00d40f400020024154502c6405a0340c0500072049034211044070016000c3c1030161000714400703107211106d07400c460440d400701c01045c0c10f02410201081388480c080e5010202 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 564624595 1250 564623345 564623347
    0xf260a0f1a06220912030204030b0c04080705060a0203070f140f210a0504081002040f120f0b0405031201060519090b04060516050a15050a0509060a24030602030711060405070605 78
    0x100a0b042d0000c03c5504c10251203d41c11060901c01280c1c564010400c1c0c1c4d204c0c07140c03150356455040c605103503400380d801803041ca507200c446c051110303243c01c1028001040c42071040301c0c5084001e980b11640c0560515080310200543c9030a100c241e88184501001a0101c2c0000c00d461002d403102684031480840c00c3d4500c0d801d0004034240303520710442c1280c3c0a001c1410803034107126540700e120710007580103204400c0d004840300c00c0030640b100885202070109400603400c4078a405161520010007030090003c030b8141c4010403440b40d18405230200c1c5402007400c1d444e02525008190300d614640f000034404a4108502d0b94000e0002400f0310003564280d0700b40d40340c104c0d195000b00660a50041c8803180180580c4282c048081c00c02031500c0c03d40b00034003001c501c240320365226918410f0130f50301c00b59240d00c425001640000e0305032040390b01882085110100100014942842058480400341c00a0301c0590f0004200032180381c0100204501005480080505243c01e03190181c9460f03481c00b90400f0004 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 564625845 1250 564624595 564624649
    0xc09050f1f03050304140301060510140f040302130c0305161b0c0f121e021008090c040f0b12070605070303020307021c0302070b0c040f260a0f1a06 65
    0x7040344440d9016692000850b95038681354009400f40d4258440f03d28403039800c20101046c10b0510560303140c000145074446c1c100c3c143c10300c3e00d81845600701840203442c0380400c0c000007001d80c3d2040100b038600308a09100185071191a14000c0548500405841880c0c480008010300700d580222907001d0302074540d036410098109864040700e100b400b5444800e161072049404560f0803054984111510310072200f040c200390030b440c0c0086011284000196005e4104030903080350600074601181d01032010790030356841e102140300180c00c4680c09070386d61110035911510300300c0b40d00b8000b54001c400c0130040b004255462503c41e000f0407502c90540d00404254010020800701030003001641000c030f031503500c1203802481001c0300030025000003400b034540c013031740101240204600c001102c090713440608041c03080350300b04419405140b030382c240081c8020f030710392400124518050041ca9080ea100e85a500030443e103074104494035860254001811001c1030040c4044c030780e50041c007162955056226120409 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 564627095 1250 564625845 564625891
    0x10030519020d0b0d0507140414010909060b1017010506071205070515010b03070f0311030c07050a02030d0903120e130e01090209070206010609120c0e041713030c09050f 74
    0x80e044078407500702c088100c2407401c100c00415088147d80d81d003031b08191030380350316000c00094440c0400c4001504400900600c07039002c5581120750740902444012038041250804220030300364005200d000150044040d524520001018034014241192800d0814a0640b102e900240304c0c08410340074003030005000c100308041400050005500300d81c52200640c2d403165410700503841210b1003c00144107540e4141802d01074403410610300c81c0115040e0442d80c3d0702c1108441c55008501c01d4405105a030302c26801070394100142045415542c1d1280541461441c016041080a0719641c051006456045d0103540340c00c41c11003e880d0b21024081900316624403024010107003840c002e03400c100c00c04108040c0325000110342e4102d8500340d45e00c0407426940c0e180d10716010749501d0010031941070400100030302e0900c0040b6a8105000380801081d44651625146840d800f1001420805e0f030909401c00621243c0d00f000d40003000c404105100614000840c035460400041841000e00c020704003060040e = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 564628345 1250 564627095 564627101
    0x1107050a1815090c050a110d1d041d0309010e0d030206150604031e020108010906030209130305040b0a1d0906011b030509030102070605091c0c032a0308040210030519020d 75
    0xd109103407013001401ca0300e407002003403a03008620180100b2030120b074040442c0c8000070a00d1900210f50303641340d074021305000090104e95100c1d4801d0f0303200340c5840f24100c0d03c045401e4044a6000d00340000d50755905414000342c0103c10010046102d502c4920340701c1c0200380c01041903940900420040d254030054032001036010b000703c5d0030280400aa070203880c421410480800780803035000f41c03038800740c1b41c2c1d0b2a04000c0c1625402d000003500f1485800124041c062152204800c040c400c0c1400c1c4e041c1515202c3e0881c0c0343d0000b603503110001d900e02c0e0703e888c0b5018000010070841036040c0c07840b22807894400000b0344104400b00030042c1481d4025031f0304060601c0f450035208100d00050083d0b582e001e260902c00084c18003030740c1d0742115000d1745c0c0e5215841418080f88100d9981c00d41c076a6460b02025031000d0382d050300b20200b10071240c3e80a50302e19218454000000504510076181c1c9241e0303041a0040c40441c08040e01e094045c54649010b000d1542680c0c501c040a4103198080035984403041143c040103 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 564629595 1250 564628345 564628349
    0x1051809010b18010503070602150c0706140a0b1203040b1602040b0d0b011d10140102010b09181902010215041a0a09120804030e0609010c080309060106021b0d030318121107050a1815 80
    0x51882e4003406203054254020f4241140112103543c18045550470302d039242d214900c0b8100d02c0f9901001440007907100c65013601c540c0c82c00207000080126403400421060780810108071945104103005101981c0c414040100507030841800402518120009071440051401029441905c65034448920fa00c00d4011301d6005101511030803540c186070140708984003a02107160000d01641000702200745040f54400c0006405078018450b0042c0030702000716004004d08240c8041070b0400041c010041c0306010103001d02a03403100080c800320281004024066284400001c0082c1c900501000c25400803103d064420203e034010364511180e00141e80c04009200d00400b02080402000f00c1400040b800034100d4440d40c00391000807401c0303401c41c07807120400b8002e581d010410b150382102083c480e501c400d81d003040d118081895200b0719212110154411000300c000560113401c10302910b40140035190040405aa0190600781441c414507180e4400340405010141d842e180d08030751250b1050080c2c0 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 564630845 1250 564629595 564629621
    0x1f050603090f07090510051903110a08070308091f090506180306100302090705031e0a090602030f06010e03160306020a050f1c1401051809010b18010503070602150c0706 74
    0x300a50f1303a02c4c100e07001d400212a500ea150710310010000c1c840c100034241d01d84e1480700e00051001d05055035142e6030b410030003002c03241d080072145c000810b907240100300c0703000558052a0700e0b03a00c8041880c00c012000b018a4081d50540e8000b500316010103400c1100803050710402c8070404d031680c2d20407103441403500d0400f00300d036454070841d000c0c01071042c0341c0040c100030b0301c0c001c0c0c0d000100c0b0380d102901030b03802e407100b600c82421001d103006503980321303c074000c030b800c0d0300039000d0140410920340c03c3e100c1c00140e800690b9441341c10500801403090365030708201c211000510542c050310350f080010201c00e801d07084611000d05810b0b00020f0201341175104404460079040d41d50303141ca807a0110070b0f011021291f20303104000c120500c0c3c10007211b00462003c0d46503040701c80c01042d90312034201130110b00c03429020192404405640f5290412500e981d03816810b00303c032104101c20704140d80352004051500040303500440c1550080800c100b14408030740310445e03110107e048125074440040c54050010841000118 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 564632095 1250 564630845 564630853
    0x60e120c03012a0302130b09030a02130b1201051603150509040f14010213030212071a180f010905011407050601320306011a0d050c0307081f050603090f 67
    0x11401d0301c4002c3e4240c01c905240d83c0c29802c1000f0815000c03486031b800c0025440401c01c0e410001e0342c03038071001460400406016240818581e502141143d140c00d8510300c680c2c0d0700c8520402c111700b0000380b800b560351400c0c40203001e40d05003040114140c010940703000e410182c840624118400e507185a0300d005000c007410401c158078107424001512808908100e41c00001160840c243c1a01402039a0b046038a42d42150001c41c515401c111403001d001c0500700d01c602913100d0004180d0741c0c3c0510501d02c6141c1203c8240d90301c42b5803d140d06440201503120b4441c6254a40050869900220740410b865080c00c01804000700442ca5245502a01e0300083c01803041c41d0000c50340382a5212701c01c00001c2d030401c0103141a1529002c086c0ca00182245440e0590b02001c0104009410032180e5144c00c42e59045044c901406c0351452402e50b0b80484030100f1a1500000b4406c502c4c0d8000d401a81c0300c03100500e101c1800072109500d003a180000e00c00c41d48600e0b004000700700f11050074441700003035a841314110303 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 564633345 1250 564632095 564632111
    0x3040501022110170c0d05011a010302041a03040f080a02070f050907121d1912080907030201050a0e18100501090612020c0f0f1f0204060e120c0301 65
    0x502079800a02d403401403880e05444071036403004061220b405100c40369240044103041a46401400034500c10900300ca1003000404200c58940800c08443c681c0100f002040c0e00c40b0f00c1d89010403181002c00064100f40c8104400c01c1004030701051505208050500c2c0340e03176a260340c14540c0242d8071810300030b0048040003500b00d0072035070001140c804545d4401102d1184a65030030410540342c80c00c640250200c0d242c1c801945614000b58006101038451003e074aa041e140030404a29020382d80d0a148840035208009d0001d0000e5100b0241c0342200c14a4406000d280180340940c03103140510000303052000105140b409540102d00081d240e03c0e000c0c140119085186108035890002551a402d20107015500419a0b500c681a641c050301c060361110106e100300d0b100d03020000c1d03100c200c0711400e602410000c0c414001c000d11050b0340c8010185c0c000c1001003800d0303092960084070030b1102c0082d02d104004c2000078903001745551030000411610f4140d1942c03203c1065080c00c03007112a0302d605500c2d040079 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 564634595 1250 564633345 564633353
    0xc0907051201151b171b120f070b0c0d02070807060606032f07050321100e06040b13060f380703021606030e010c021b0d050a02060304 59
    0x60045000915950701890b66616580a0703100041a40d03640010480a49425441254480c40300700c0b6100d255290003413861842003000a80001010500c040000c40c08001240010010404090800950149401642004d184841c825180000c040c502100d00103001c007000f00c0c0595004040030301d4250341d40c1040c1d2800801c01c1e880700300200d58251a040700032034035a01c288240f841c00441260070748090100c402c410f4249401011441d80c020b00300300b00f0700300000c3c01031020380702c41529aa0403041c41d14080003034002c0514020b03d01041010384410800502103064412038000e9010f41380054181380345004a0701c10281092642401c41c280003000a030b01c080e0b001401c048a191000311458050031205001000c1f08628140303907a004070302001c0c0132029611000302301041c03080c011108002c00040d0a0102012141d0244010a554140211050301c0c00c4c064807810280a00c0944490702800c00d4842c1c02d0600580054060500c0741001700c1080410411000c18a8008000703c0c0c423440c4c10700d0 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 564635845 1250 564634595 564634597
    0x10e0709020c060f060a0b131e050a1502030423150306030c0603060303040501082e0f06020a0b0f0613150302240306010e0109030f14011109060301050d050c090705 72
    0xd0004401d204800c001844c81005860700c0c0d004002c01031041c040540b03010003840054001c000145620f42261000045a0030f101d8240910714011184520a45141208014041390305178003404840d10250b40150340c00d0b03070210840b016916402c29444082ca5502080da0300030702d990031002d8020000201000c400c7c41660060340c0b10364011000c50b0f0700c99162005202c1280025902240c00d0760081c03000340900e60045d90307116407000860240210a1504200380071090901c07000c1c50b003204662082c1480858609c154480151070540018403010004d903540e03001e00c1100420107003a629040c804502503580d001c00e1a14084c0c0241000e010351802602644ea00300b05903c01284036808015000c1c004100027040d04c84900448403101d4215074642c0b0054480440e003110b49410460607840c044002031682d0740004401e401508100382100040314000e085034003022a021008100348412446a41d80da0100c0381514400da07016a1104040d00d003041c501030b2a4a129070b8400c05000170400030640c404 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 564637095 1250 564635845 564635857
    0x1a060309010501031b0f03021002210711060f030a05060f030a210207060504090203040609020d050c09071803030509030102071a0a0b010e060d05041103010608010b120706021c02010e070902 83
    0x501840360440440c0c0500c0c0aaa040307100703030805d80e050011300700023518011b410100240f2050041c0c85040c0b200d042d898034900c0700700140c0011040c2c00703d8000240880c296100b21071b00019680340340341410096440d1868040240144145071301c07480000c0090f02d8074514001c0c460b60240c03c48030a6111440c080e030410181c546520b070003e2220103004003003031001580804682d016244d891a05003001d0f80003019500061046d54800d031907030107010050321281c003641c5c100b034010ba015101c0180c040040104a0001500303110420001e00d200040a011850490302200e40c541491031766900c01b4404240a40250000941000d03504500c034041200c180d004070f84504282001006010a114019115503c015810641118061221095039401503208540250081002640318807601c4002400c3d1411900040001c0c1d4481c451000d003401c1556031000120141406003041c941404402582e803041e42102000c0c0038401e9580d94600f5000f9400030121008031805d4402c00f0b61904d15540180d4040 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 564638345 1250 564637095 564637103
    0xb061b0105060d02010c0312110d060e100e0c1b06011202100503010b03150103020702040608160806150114040f08030301030309060f1d18012d120201031a06030901050103 75
    0x1800160b220b1414907803205440d0b60507190706015050a407400c91b40b10031003031006c03070000781c1e0b844a4212028600340680905c040d5408007040303090509030180c00a0310080c040b4985032140540c140401c88200e0040c560100000460644803400e800e000b18592518051000d520f004070b00001c54141d0354106544000c0e402602d060300d24402d1440212500d00c0244280d400d038280910100700305140401c5260b00c403040514000d4106110f940015003261190350100d901503204820030040c04146003156001055070402030003c82c07811114005c0380c2c07030200d51b06504119104d9540c0180d106a401650080c0c00303401d4940102d903469580c9555a94028001a00443c0001d01d0000e0400d200701c3d02003002c2c2c2560395a100b048251114420b021464101c413650f44802c0360010300c42c06044001409008040307024681c801a002408400e800b40c003d141040b01d00142000c0601c400741110444103a003a5081c43c2c00200424071030260300f40c4200152109900c17a03000014020301c5036054000c14103072806 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 564639595 1250 564638345 564638351
    0x100908041410020a030309030e0301020a090801051b0d0c0306080d030b01080f09151801110426030f0903010f0e10050a0c090314010f0c0c03020c03070612020c010b061b01 75
    0x34a010802c1850025078800010790001c100840064425004001428860704010005a0401000a007a604201e00034400a01580410040d800007401455000f207604500c8254408400310b0303c81541c42502902c2070781588900d060712481e40f180c0d00c148010548039051768244440860000d014001a808140c0000c03001c80105022018001c10a405880c0d88802802c0d04000c010340b61084180040640d140c0b205c6d50502249040400e01131422510044100b20307070746500304103c26514800000380880590003030303e07000c1b00880c00001150180c105e403241f060348803405140040c5c058104890f07030040c003d003041e800300006030740003c85131003d903000801030106903110b007141c20840b4a03030a130070400101c1301c7c10304001054104143c26a400c1013000007046513080c0f4215201942c8400c403030b04001a032180c28490516a06100d02d609030442140030b0147c8070b02c0d00038001c3c0306601c42e0701040c1441d5800500c4080c810000d501411039140040c00c51915001c032401c4042406900f92078064943d42 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 564640845 1250 564639595 564639629
    0x20a0803060310111819060318060501080a030210140601110f0111030613090506070f020106080a0507030201110f060c0a020307020a03060f0f021215010228110f130b010210090804 79
    0x241c0441c061184001031040511b0107454450214085d2500d421030003500c010b00c04611010910600600b0701030704002c4010a071400b07003464005c0c9001941c00c04284064944100c00503170184038040c0729007004007481d0442401c8842d0f541281400d41155020342c4070b602c0c2610110541803820043d500c035107811140960000034191010f01681d4040c800104284c102e0760000d907005000c0d008140e802c80d1144000034006031622001d42c80c2c00e8000006903010350082c14100304544c0d00c840342c8110b0000907005044800007202c00240d84900140800c5066071011400364035840c82001500c4600f600204010360150741c0b410400014080004020002418034410b40c1d2501028022600103400c441c0000309681e0740c20f0b449080408981c2240d82c118000c07103100409600a210451030b01440664043c00307400794a243c00c03982001c0300c58400e80034222181800d50070b0366415a801e80c00d505a600301084070f03244000102e0030301e400340301900710300c2e032030030100c4814007902c2005003041c0c0300c0c502c0040c1040742c = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 564642095 1250 564640845 564640849
    0x2071113140103150213090609111305010509060f0a11010e0a08180406030c060f030b0a0806060d0804120303150b28020c0603070825020a08030603101118 68
    0x1800080c1e050740c6200c04000410014150303110000d00a4103048005084c0320003c40b001188140d80d0b0320185666480d00401d0001c0c032481d2082c02c03e1030000f00d1490340b42025220004001d103c1600c40c082c14444081600d20316a03d5000849613803403d80380c00d156481001d8207014003402042420248290b02c0c004103070f02080c4000441c1446690061003082c14490400408090300340f510b09920381041e1503020010000e880d190820015100b1521129600ca469000080803a00e07101c464a01c0f40324084010440c0510105002d0b070890000d03180142c0800c1c20f8100f4000f0381c451a40004140500324805078141031381b5910800c980300700701030041c010b25aa207103040301b14028030007140c6100e200f609410b1802540c840030071140b0112801607841541200c800160940c10071545540404c0400d002c01040480c00084640c20040140d6900d41106207004020b603600520403004101c8400000801d10b190741c1008032140e00c202c04002441240e00e550302680b03c0d6046280d0030fa40901888040300c04038 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 564643345 1250 564642095 564642101
    0x6030f190203071b060e01061206150302010f050702010c1407030209100f0b0d06031205091206010b09040207050f070b041502011107060203062103130503030711040b01110102071113 80
    0x1401150340c2c0320428401c16064071042c0c036180700100c0e201c0780c0d203410364648011b003802500300809018184119550740ba04004003601c440350741b03200c50920000401c1c00141e030008124540a1001d181250321841036200582d1140c45411015220796000d2114400f058800a07080e02901d200381c41c0c0c2c20151301c0f42c68000145200c103020304000b44000c01e800b81301d1038000d00080c062418040b940803601c0359a0b0386852807040d40071803245001500001d000c0080d070a110710944110141d00000700480d43c904a2896400d001e07641c0100d12440c1c00082c48410b02c0f104000c1a44940c807c03000f990030960342d42400b500d281e40030703100305148004182c140c41c8a00d80103100d552000da03621002245400d8440c1d0359000290b000500a580c80240008125910b00c826000203c48030452402156641e1981203508502000307a840144070b80c0c401c2003541c0c009109020030350f14600c800c0d64085440e03201100180c81c0842620340380b0340c4640c4049400c06c00c3c4102c410b441807c94034256001108075180410340020703 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 564644595 1250 564643345 564643351
    0x90f050c0f0103270201021014010911031501050f0c0f030c0606010c080d0518030a090608010b0412060504050307050616030c090e150f060a11070e040b15040b06030f190203 76
    0x80f140071080050481410f13a41c0355103209205205583c0d40000740003200f0100d882003151000f58108001c01030185e8102880350780500d040800c00c2a0440c544040c0c0000e204120355125410880c010031880a0080e01000b61060402c2c1c08040d2800401050700060340c03034111403106080d5101c0c1c0b801007916075000e0241a40c089030032000d81d0345440c0e0380c0d00c0c1c894058500074201c40342042d0b4840c24050350b04400c1c80a02100c030041d0b40c58403082c528040c07008103103440681040035001c804000070071078003101c490030300c01c0c15a0003c00818035980c0e40c2800c80c1075020b10039000c0d105000e42010094100381c01d4486001c4a00c1d942c4080082c20103103541141d8020b5503005000c11681d80401045096400c0940c0401c0680014202209180218040b0b010380d000400c50b40c2c0851800291800042024007091025010b045114851407415803200420f041c000303071500000507001584c00303040d500c0d1908015040f00d0050f010b81e50720306000880205180c011165025860880f441740d8044164600032240 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 564645845 1250 564644595 564644621
    0x132909011a04151e08040516080c0d080d090b1603140609090f030f1309090201090e100504050115080703090305180f030a03030e07171f090f050c0f0103 67
    0x42032604003010342c0d0a0702c010f20354180a100150a82c032581c080307992140c10079801c859079215440c1c2000c0c5003203450800c0c0030b40c1500c0030000001b81031050010000b00c50110010461b14a0059100307418000d03603611076501c2004c0d10702d09041000050112104a8601450219080d480c1c64a40302a04400322441e08405501001c5000d002c10418504207201c0b0b81c002400e8815100c51501c14004203156a01400001c61207102c0882d43c40850040d4001034001400301e01024401a20f40768002428004c03180140941201c504020411000f5400c69070b601402004d0000c05c201d5840b13880042e079018004001400240703c0d00001b940c400e12034022162542d601d529414107103c120240d4410361407004003a241c20001e0b21501400580d010403064560600a032400540f01681e2000c65040100039003100060120418070fa83c1c03501400158034003101c144140e91200c03920701103c0030b130242070b070317401d0190011030950400424000042001c4c50b048208841c0f9400c043c0349800150159044088500 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 564647095 1250 564645845 564645847
    0x15030709030803060f0405010e06040c0e0f1011060703320f06030c040906092a09020306040b030d030f180503090909030910080105150c0309132909011a 67
    0x10314024040d582010008110303176800f0050501040884401342e101c900e4584805003402103909052282c000c0f03070102c03403074003941d4640c0341790114800e103c880905a00421a110884070307860b01c00e440100542d05103005440060500c1c170401000b070b05040690030300c800310301c0102042d050381b1810118448000c124440920b940e070b10300d407003484240061038583c060158000110095556216042d11184583c03800503e6200c1e0f800c09400c4a2034001481d00c0031589901c5130100610481c4881d01201c01100015030f0360303030b60100458003900402c808150113100c1d5080001301c071034040c0c10274038281b42002000c11480c50310604082e0200d841484c090b1064100300700903d06800c1c5001580c1c3d000c0080310481e4604140350000c0381c2000c00140032800003402e214014402490050b088103024842207c405080c8082d207a001d0341c40340314040160f442140d100041d04140070258020030000d06506107202c11840342c40350003c101d0030b12210042c0c800d000240010032400315020700c2d1101c2c034200c0240751f = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 564648345 1250 564647095 564647099
    0x100306080d0309031209031e031e020a23030708070815060d0605091608130803010608040201090b0d0209090901060b030412030609050a02040602100e062208120615030709 75
    0x35802000f8044040c0c4c100074400307510991512981c0138650f240ba10030303956040d03d612484c400507a0503240607250340405041c480210b24000c0910010701c01d59803010030050380c0315202e00066442c075802100c440243c0d40fa04002003960030404010314400d000684903940c2d41c0ea80c00404035034800c81200c4044056140042100460401070050b012100c0603c0340081e90544503400200c01c03c0e0300f142d0345401c03c0241c80c041002c099021901c2600601b41040c1000907040a035511112030005000b41c004000302440042c1c01c1da8807501a10b0010704011400d1a40c4040b4040f111010394401c441f41c03401440860082002c0c0301052155104580b10341c002d15040d500c4950341c1010003e64542c4010030140c0302c05c00815070620038401c550168814010059031145000300181c1024041071142c0182c61900941d1840c0d12400f0403043d40c04811607502000511240c0b409001c8009551000b45c0455130200344d40e00440480c3d52507030b008070320841d82c1c00c0c1c019400145d145041d1100302c072076200240b020801 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 564649595 1250 564648345 564648347
    0x90210090e071101061a0a0f020118080306130c030b10020f030a030e070f0806010504050708130209090a0b0406061d220213050f0a0b0301060819020a081902100306080d 74
    0x2048a02009000130404584e03802d4a80d44081e06c8041009552a002421240603500300d600301140e01c005000074499041d9010365650200013a0350090321042e40000021400c2e61441c18983c14075181201c00c02c00d2107881440100201003810340700380203c0c2049200c500300c82c00001d0f40b05251207071500540c0703008550a0b08a001e80140070650f1410f1164180200f60704019502d80c40140c03401038010602c641c9410304003c15203501030300c1c6a00b4040c0c9a4180100700c030301000d202c4581034040c0e5006120392207450005182440c0c8007409807010454805120070840150490070440344160700180740c0000d03404c441071400c0c40c1640c500d12003015413641c6100740b403115249202e80360b00041419000e0b01440d1000410703a613044441880d0500310314100108c902da58859589120010f0b402084440d04060b04d955680d0341d142c2c9a1078801c516421700a0856a90b1a801f1010f003d030349065401e070034028840c2c07102c0070700c82a400b03d21a80100703c401c80c40502c40d101b688110780400f00148010303a50040 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 564650845 1250 564649595 564649607
    0xe1b040b060f2a060f0f0c25030203130308070506011e06030509100903050a1107050f1302070606080607080c090916090308040b0a090b0c031b030403060f090210090e07 74
    0x1601a510701060030f40c1c0812800501405204004101240d44a403030b0071207500000b040e00400c03807800100280031242088943d0807810501080135110b0404503c841c2c10140e145000740d01e11313591541c1000b0f2021007003111000140003e54804c2c41110300c41c0e42c803a284807804100858000c00b1100da95003041042500c81c2d000280c00c1580385049c4c501d54040181040306894694509030b000c00c400294402013241d1218160640c0d20280380500481402c00c0000780811a071001498411003120f1500c2140c4903841d4100c03040d003a444081000395a42c0e81c0c0f0016240c140845410300814803000c00105010410400c07510004401070061a0660724450300d904107480d20070301070041080d80300f000300020710b03410002d00c00ba1040c840510307110680b0450040003207032540c0080d41d00020522403040030b40c400000351030f09200304003000724064481180c0700b031941c0503e910141405082c040580c00044a5a0004460b603000703846007460b034828060141c0d031400082c03060f481c00240d0903001510040c4222 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 564652095 1250 564650845 564650887
    0xf0303020c030703050301050315161215060804051207120f0e030f01240b0d0b030f06010f090b030607080403031805060405070602010c14040501120e1b040b060f 71
    0x10400504180c1c500c11074901c0c2d500800011008120000014041c13450204182c01c0c0d211658010b18400389003000041d8515208030500000b408149208401301c01060b402024155a2503050030503210340c0c8800c010800b04058909503114012080b4410540740600100c42041d90460a500d0080d682c8074070850b60025031940c0a020000d15541001031940e0034004040081d801c3e400100300b09081a00c0a10200b855100c401030100c840002082072121f02002d80780344407040c4030300180f0804110046400c0c5050880a010513000e20000410101c00d590f107000192030081004118007040750051550300c030400d8407210f01150680c000200000d00c82d2b00040c02102003541800c101c11026600c151911406880845032034014403410f10002d0703824070400800d4103651404400349008010025901e00c5103020362810056000504485902a03410584103803200340112980c0140301e00004500d40c1b078110440f417245042c4101c8507120b203002401d0780d0800e901003441528242c0481640e541002d446 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 564653345 1250 564652095 564652097
    0x804020d0209090606040b01050a0c1b030b040b0a1a0303070611040b16050f060714090a0f06020a02030d0f0906180902071208010e13140f031c06050402030103030503040f03 76
    0x200684480c2d000d540a54a080001e09203810004200300a07104403100c1075040100c1070044201c5103900200d46c45281e0b4004103940245e0014218000c6010b80703581001d040c4058000c140303c10029803840007440760b0090902001f1060310001180a405140c1c8805a4143d0040c05960b001c41c80c4c1c0d60000c1d00c51003001e2005840c180da510807060194000100c095070aa0700c48100e00c0c207010382803117080110b0552401411403458141c0002d80500d501c204441c10958000c00ca00044d9110307a2018000742000a09c0ca0021681d81c00000f9500c0e4070f1240e003203000c1d0040090040c2481c0c02482d003080a00000e4545091890404404030b4842c01060340e1882e003010080e80010b44c00c501031009042541c000c8510f008210102200604202d50603030018800410035401c1103105460300d0640341405a02184148484d640251054a003140929049035640000210b0280340400b4007012031f1b0580c1c03404410302ca40d5540300c00300001c81c0802d1102401140d800c20000e000680d040880342503451003 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 564654595 1250 564653345 564653359
    0x120806010e041d06060901150c08090d0f11040504030207121b260703030207030609030e030f03040f08060105030d0309081c05100e13060507092d06110d080402 70
    0x42c0c143ca1400c42c034603801a01d42182c1da0000e0405200440e40010251000103031549040c001c0c001c00420010010100440c100002c003c120450086441610009080d161000018140700f000c954107110300301c0701c0201c88003010000341031030f0140b203100c0d50300340e00585909450516001d03d480300e1414100c83c4501c51100c122440705804804002920341104032403005c9201c98401d00060326079070300a0380c03541e1244008000103640000c4010030783e944410045140e0b03e8510b820341d01c0f00d14520005901d4001c20600702c0d013280d000006002101d241c45d1864081c03550b500d001c281c03951001c3c0201078240e0000e05080309030b107000f90401300d0000c1c460b041991074440e440300c401d18194605941c061800e41c449003802400000941064060541c103204c1d043c5500b84030707410045545001c0d000410064a41c000a404203000c0c0310140c00600022146400d42071400d0740190403550440e00c0820000704c8148040340b440d1044100c0700c0d900740e03200018006c1903003003c02900c84e0100200101c1e0b000d42 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 564655845 1250 564654595 564654617
    0x4020f1e090c0315010212070620032a070302250b03070e030c06160609062003180a0c18110d14010503160e040609050a26030412080601 60
    0xc610145610464841041c0c0340c4031300308002d5015a582d1380e07101050440d031260280c00910640381c000c42d030107154040380010b0700c2030700d90040f18132080d021010301105840100c200544000d02030b100d52602e1b800810064105407a00b85101c005004040c1c0203401a800703050920303d02000aa06070110240103135103000740c190740b07101c1200a40c3c0f0442d034003030020740c0020481e042c5040402c56039610540c00ca401d0360a0007036807103040007040c4030b41c000a402c041e1101e5001342405082d0b40406440c030b080c640803003009280301d070754101680c1c010b0b20008507041c003200c9440402c85011546040540c0e200d2821010b40e0300e081c1d110141d5090300d0104582c520784e00c018040070444020011320f0000d03800080444c0200d40200e40c03006003081640814042d401503150046010803064480c425103024000041e041c0d02c03203080443c02004540300080040c402c9503036480078444a1030010003020300045103202c100805420b00f50081c0020385d0001d083c0c055008e01e44100c140144402644102c040c54101e04040b = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 564657095 1250 564655845 564655849
    0x414041104080d0807050a050f1809070504030308090a030e12010b0901060e13150b0a0c05010c0c0b15101b0b10081006080a02040902010216080c01110604020f1e 71
    0x1074840da002c16035950002c0b84540001c2d80080207140c0c005168104241004050580a803107445423400d01b103402100090381107400c0003ca48940076000c8080c0482a0518002c0780c0030b07010b40d0203400203a000c191900700003010428001811024158169902140d0000c0c00d01030068054a4040301c020765504d408400c0055150340d503209000b02825650813071281e4031441403194840740501c00700ea219041000c0d1301c5030100c6200d181001c80340d00304d10540da515406101141d40c94000c000043c855420301d0541440d4903802409411010b011b02502002522000004080408034104030341c0c00c01050103803400b00c58025458008104c030b0003c400a120201c80c0d80c1d803800c0c4401141c0c142c91003207500000740440c2d40300708a4000740f120051400c00c10b5900306a26107a4807500608002d2143ea140c0103a9011a482400240e502d07001c01c4d100c1c02c9809440f01e8400c0c3d100c024496030207002409ea842080e5003100c001640a000c0d60b006001c00b100d24521700c01740003280441e05803c2c1149044a0021b0390301d6 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 564658345 1250 564657095 564657097
    0xd02030703060303030f09020d11040207150207020406080d02070b1e0325020a020f04020a0302090603010b0c0c010e060715241409160806041506050c06010e0c04140411 74
    0xe03404564000032020709529000d0215824040c548090504d000704150041e207603025040d8070140c000c0e10501044840d000040c1c041d100755070002b01185034090b10f40322246c600c0d40103400c140740708640610242d034952031a01d170784001381501d50005900c00070041009651241c003d20009140480620300101c80d00c0c4549840d074000d950f0801418030040a035a20034a08120b100ca43c05185d1002d440c503010180c00203018001c1000c2483d108590000d04480b107a406503044a80082d0041c0c0019202d6030f4a602c03000c42034100c07400005c1306000302c455a540035071041440c0004402d005114a0800d0860348404503840b60303015841200301c3e034484419100c01294030303042c118188220000031f9618203000b1042c103540100e130401c1d400341800c84144a200c1d4081901016141c10f03514144005941d8000010050901c550814540b505110804070325a5070041c0103180c031195120881c0c0a42e640d9607100200300004486448031360205000034800707441e03198240c04441c9802003001c180b82004031920051 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 564659595 1250 564658345 564658351
    0x405040c050912030412081b0604050f01050a050f13021302180307080c030c060304030314040b0103030e010905130209060717090a060201020f0301030f05101401141f0804080d0203 79
    0x20400c081000e401d60f1405080d00c0d90b80c00840ca02541c00c041c9003a0056030b8600081c0c400811100011a4a10201d00ba007103d000259800c3c1003210090b007018100a610354001e8410f034140b55080400251049040b805401d016103180002c0d80340365669410301403907031110b010081364006809031182c254100c2034005448060059100040480b114000b0103107000e11640c00b9850039000910442107940c1c0c04164500142410741d80955240d9940c030741200240032500f11548965000d80612007400480c8132114142d030b200b500c0780b401503d00d210043d5110300c0c05216255101d01444803071440e9074404d40181188101c0a080541040c500380d460341007880c4090481c03a089000031464580c2c40c9002d02c0400c0040031340740003c6140100f1000010340ae8441404050019210a80f180c42040800c12103841c1c103040c560b004010701109009042c0403410288501c0400103a41c0c0c600d20f805107041d44142c0340000c0001105074200c1c60701101a55441c40041080c3c403004410b0241201c00046030005501c = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 564660845 1250 564659595 564659597
    0x5090d050609030c160b030406023007200a0201030c02100f0905010b0a030b0f060a2402010c0f170c04080d03021c05160e031903030b0307060816030507050405040c 72
    0xa00c0d5410104000d240850ba80028080d08010603030801004c90b046c3c0c00c490f04507030000c01c050b0365010300d00802e01892280c000300546010841e00300d41c500e51441d050250007510303290707034a40080d040081400e070720182200c209826070700080c0c1942c00540c041e03070010031004000d006541050b0000010b580407250707a120700c01403050f11065500100803081c85041c10034070782107c1c01d803a00380c00c5445240907914014540c0c80c0d0241c00c000440d80564a14180d980148021356040e8111a588039080c013201d105000044055800c149115000600a4a140c00d4907804c41e55402480d14010900c4c408070007000c0c01e8450554030802022402900910001c491520300c0c0c0c03400f40e42c0d000f103181c65400c1c202105024000040c90801842040b0045010801c442c140906d01a206100307108002828500c0c4cc0401c08404a4816011030800d501500414800300040b405d030f8a005a6528003034a40c40000c41c1c1d0042140450201950880d0182c9c0c00395400840c01e00c1c5c03039800c0c0364540c40482c1c1100c0c07070210400 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 564662095 1250 564660845 564660847
    0x7060c080c0408060a1e06081507030501060206160903120c0b010509190f14010b04080d0f0c060b0315100302010801090510050d1e08040e071805040f0f0c0806011403090d05090d05060903 82
    0x200c203a2786440c000980103880b0b0b140c00c00042d071400340000d46841c000741c04141140660307141071080c50b102d40f00140203543c20080030501c828092401070714070042e41400b202c1c682d11090000405140c100d01c540d10541d40e00042d225903c1c0441201c400404500480c40764681d50381c0d0004038202d940044c085d0207081c00c280e1140d42c0e50704214140b8074080c40f8018034030802540c11248141c41c3d80c00101460710651110020030614120400a4108402c00c06180c0070320f041402005003051420600c0e0084a0007070300d41601690300c03250f5101c00d40b5004c80e01001080450b803020060cd0801980e4082e09030f00600c08000c0b281d09140b807420500c0d4103010282c85071400820240202001482c01940040803401d000c010100a503a88900801803407064501c00c582d203810702800c0104680180801189002c0b0400c0007144a0300701032708034001996200c0c0007808009011002490540880e8000c3d41000010850b032046100110380790340c0840d0780150044485c2d8a400c0c006541000a5805850910095 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 564663345 1250 564662095 564662113
    0xe09010807060528030b030613080d020a031b09090609090803010311011407050d113903191205120a0203070e06121b0f030c091507060c080c0408060a1e0608 69
    0x740c0340c813501600701d000c09d0709451846c0c00084e9210381210b07a401d05019000d40c80e00c0121030242c00a010801c1c43c40343c0400300d10150380307c09501c2401041500c0c0083c01c1080416200c0300c3d01c03412200d0742240107103001c1c1308200600103e0080c004106200754140740000001500701951211500f000e1004c075000d500074220301031001d4000054642c154450030040c0380c0b040345821701c3c42d031421000e00103c003941c20038062500e0540c2c070400e00c0c50746410043c08071903030b00c006071940d8035110000480544a8131602c40d07203500c010307214404035400203104880300f40c01519503626040c02580094480342c10301482804001058482c907000e07100ca011824283c120b01d1074126030b0700303c0102020080f4010607008010244041100d502030b6030708840783c0c090b42600c600d240e030042405141c110f905440038610104100c0f00304207460300445201a0b007550f6094090f154220b034024680194018241c40d50031010010b03c44d040c0c20741c00144545200310540400000d640d000108454003a046050250014815 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 564664595 1250 564663345 564663349
    0xf07060809010b10080f090c03031c060504020913020f1b0a05070b0a12051009060b1801020115050108100504020f07020427030f050f0a0507030e09010807060528030b 73
    0x900c0c40516000d80d8580b03205130082034010300311200103100f030950050140120394480c1007000f0202c4050b00c0501140d5a4400e108603482161041f00030b80c13046c2d0380c200138000c1020708150080e203c0d540d401800901c407503170300c003403201c0b010b504040103a582c403810070300220000076400e1244030f0305c004802006e44610b00701da080c074904008854010301000701c420030100100035030000d04004422620000000c050711080d1032202d000c885980259144c40c109200401e030307544400002d09680d10149840301c8004082c0e030069080e85d0101c118030b0743c01040000200040c1d4080c2850a40c480c440c036007035145058072400020100d8100c5076000240c0100443d020342103007014810080603004600303148000383e044090034194a2200c03c2d0007000c00105a40c003468060184c0f05585014541540c0181c4408010400800a8000c00020707000502d25800640c018100348110a041c0e9031002c010740803035410701b6001d9401d5880703607008001d240070b5120620301d02c80340d001c1c1012146802e594085841c840c0801 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 564665845 1250 564664595 564664601
    0x80c010e2a0405010f090911060a350a0b01020a02040c081504050405070302011407060227060c100e0313080105151005090108040f120c051b0102030f09030f0706080901 74
    0x98018002e030301c1c1c00700600c80f24102c84800c80403691030030000310713030002c1d140f802001001008141030f030000008156400c010ba000703100c1c001400001c101d0310841c10089441c000c244c101030280e049410b440100815403444640e005500c4100c010300444400300400e9000c201103807180da40110002d05036a0501c8100c0040640408441004550078812402d241d12005d40314102e5100081c1400b0384009140483c00007002510038a0b500320034119103a6010300307142407441d4002072200c01d541800009aa49524003c010750b40c04000c41e40c000e05020302c3e0740b1a201c0080c030480700c0942d560301c0140044040301003c03104c140080c2c144100042845e06080035048090480188014800d103941c004402489034001e0503155009000d00c1c121000e500e035800c041d201c1981180025168241e10030000c04155017000007490120700c07c004803035209d8411000b07030905442d070345042c0740103800401010049400180c080c2410440c001c050b110310b50a0314030b0140c9002c10541c0710001082140b0104054040c4c284 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 564667095 1250 564665845 564665923
    0x90e0403110714130c020114010e040b0604020a020d0c03020c0a08030904060b07030c120c0b010303271a0702040f05071d03030319180b011e0f050d080c010e 69
    0x100c41e0701e070f103003034000001d120b440c000c0461400c540d5645080c0e24054400d400c0580b2890314002443c0b09540c40300705030710100c1c908440c265003411003940810010704003403007120074042c1145c0c050890708801078021900703211226020f4045220398540c2e070206940340c03010380c0e00070050308000310703502c0408005100503100c50394820b238031840c0c00380600e07804207400025041c1580e60058032039210300c1701408203031080c203501d42c070103098950a1b078008410036070400d12040c21220310003001c00380740c1a020200c0c0c0e034940709400b6040b010501601c0160003200d4200142c00603a1004002141d118a0300e1030400c111441100c52a0000e9a980c440013002d1040709000b003420b010640c0654a14039120005040000d2160880d2022503902c894605091108690203011654025441e81c1e403541d56520440320800c0401e08814051311014000801c404031103c0d4504655015000f07244400850700c840c4240c1d0030600b0308010f19500c400000d02d1968060100e400d607402c50800404200c2c44d260140d01590f0140 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 564668345 1250 564667095 564667109
    0x30203060a02130e07170703020c01020f0307030b0a140411160506071e0806010e06310815040803041a0708011a030709031b09060e01080d020d170601090e04031107 72
    0x40001d100001d80e000b5491041b1100c907941c00c17034160322400e030110002d20880e80861b1903544041030b04040d10a001c0010b600500b01541e085c01121f40740d00812025030900d00c02d40600041c82500950303113013416001101aa101900c2c214140341c203c2c0141c00c1c40342000d5108a886030003201c00c01107440e030025070100c6000c58044446400401104020b0441a40a0101c0d03040c403021080007021565044122001c2141140c2200f51140741c1c069880140c400511607001240070048010a4031030300007507540d0514041c0701c14000c90b5240d940f41c51780154009401aa6403001000001d4640e40a00d0780c0c00c2d0081c1d0680e40c400006601d408619104800140b0302148088020003e0010030707544000b1038000d0b41e07008084211300c1406a400201d4540704d5a2002d0349440c10719130f00041300031500d1000e9040b02d49540668810280400040341c80c0c0c1c0c454100000400c41505010818402285070a41d01004c181003250b15552100091480103904440c201c000529514449900f220184005030040000c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 564669595 1250 564668345 564668369
    0x2001080906090a060b0a2301110102120c0a09050604060909050c0a0c030e03010e010e010615020606031f090609052407050d020d0b090414011a150310030203060a0213 73
    0x10510303a460b200c03c40c0250103401c1a8440c1c480803016907800070b03188024040d060b07070f100108954910108031140d001c0c0000d80801d800f500c2c0c14001c1c00041c000c0b04c00c85000f100d00806244c0d030b2462042415003114050f1010440c0443d0f0110b540e0b20740e10028405011f851712400c8501e450001c440301600d00080c1aa29a5101400742480321904040260441540741c1400e4050790200b80c08607005104941d0aa04c480d820f10b65428603080c0d06620407030907900e4071b401c0401c0c01414680c0983ea1404180c0c3d0303d03074140c0c0c070050340155001c075038500090090b080403401098024a0b0303240d0034181c0c1c070751100179038540d00258054070100250a1800c140c0224054625401d0b260488000e0254040e01c88030720000c0c6e0b00001c56941d01c00c00c0e43d0002c1c4820000602c6035042c0d080505001848000b503640c100c1641d0f01e821070b0107120008030220946444d50082240b010741c40c42c42d140c81490342003c0c04010002c21004e502100696050180c1481042102d90050311000f0240007800508400d9101113503200e4 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 564670845 1250 564669595 564669601
    0x50d06030f1b05150d020a03092307090c081612060306020301050f040506030309210d0e01090e0603030405010e01120f0b1503010302060726030c0301060e01030b130c0302072001080906 81
    0xd60b60054540501740d05c040141c42d130350724080517006004980380003403841c0c02104100c514000f4100c05104036a0305007007122561a1100c1d030100443d0680158107001c00c0340d400c0005c3c420402c50700141d40d0911246012010800707030000400a0360a00c3c0c000700c4400f0340100043c8114284071007120010482124207020741d01f418004242c0300d116030349019014209003c901424404a158050500c00850f401c80e205511410001400d000714480414002030038020700081c10114241d4250180300300602542c5071501d02030054a07035000c01e0102605001207050031555541151055016500c0300d0311010404030000c004100392011101402d0302d05040c144014800340c1c440f001039840250348007244d603403201c0e01d500050003d01703845030400c0d0000c0c00000412400d120742c031340514101d80a644032003940e031400300015010303554030340180f68001100500d404201040ad030014801a00e25040041c078085058031081180180d10154858003009414504d42039640300400b254020804d00181101d42 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 564672095 1250 564670845 564670879
    0x3120215061918090206040b0301060f1e05092b02011e0804260403030c03020601211502090d060b0a060302070b1f0518071404080706050d06030f1b05 66
    0x102c0074040c0308640e0080702000010160160300000711540c004002586846d940c41da8802244d0090041c02e000a070352422000000d4043c041c038800314407000404a0860310b030b01800312441e07002094480d0340a0008031011010304100408902001d074018090b0101050f2400054040510074025032802040c141400844c16446208103801ca5804400644020503441009142243c200c805034841d100c0024000708041c0c00116440c419031098003a035142f60f9032070780a0030072200c858110340c81c00d1090100b0640025401d1403410034124107102d005050403940c5010039215a00082d0840341f807036540301d02808074500070009200810392460190326042c800e0341c55081e407c001500c80313040710b110601040c3e00c00c810320b01e0040243c400035008104013502c0d641d00c001400707426150500440c806040c50b640d0030f83c00b03c0448060340c40100082c50014a080e0b411551680701c0c1030340e0490030f640c4403400300006000594880c400741c000d0080c0c031481042c42002100355800c550185c0c1c800c0d004511184191 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 564673345 1250 564672095 564672139
    0x1020601060f050c1212014212151e12030f0e030d0503011401080f130204140916061805010f031e0608100e03070b100312021506 57
    0x450098034110783c40e1804002e0081c6030504000c10160b80140201b2442e100841c6c0c104281e0481d110782000201c541e581190022070f04051551340700c0400e00300c401c4a100b80703094540802ca0070040e45868540b9900200140c0112100000c0500c0c0280f0b09003420020508014540c6502d90040400f0b0000d41d454101c1034001104441b00050600801c2c100d5403000c60300841074034858005c0502514460809580000c10603030090007041481b400502d28200654800d21800b03100d107100b000010305548954103c490080e501000c100e07401503d840c00051301c0c10121149178061215403008041540e110941d00c0034580c500d4200e42c00700111403010310b6441c21105814ad003260340a0a1101480007203000881c0a408100807034140f0f6805950780011100c020703400070781118506130a40d440d0007040341c910307005c1e100d40c5840c0303002d1540148011000308a00c4d002c81c0d500044118090690303070750750340c0e0f40c0040c1c4000d0b1a1244007581212220103090f0760380f000e00581c012000c80d405143c01440200d12408 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 564674595 1250 564673345 564673367
    0xc0c011d0111120406020a02120109120806060714030a0e03190605041403070c030b060f06090910170105060405180312101701020903010b0919050c09060a0305040201020c0102060106 80
    0x4110364808540031000d000c3c450041125001c0b070b10745945645400c000b954a41d40980b04030b0160500c171310f4440d140e07401841190401c940c844090300781c141d540d98080794803402c050241c591040c410800d1000160412002e80084462007000d1900c0c2c503008100503101c80c0440f0b00080c06604590a200c84650641c054490b08a07803000000030241c551b800d1440c00c41d042c2594584175031000044560601950442860440744140404440c643d00c60092004845400c4003054100105124a0880d440c000a00c2c580c04040004a2000243d50300e147d158209103c098804440e503441092083c0727030034103014403544000300d001e0031428800c1c1c050302160799124000b0103249806050380850070200421031624005e200c03103203492151100c400303139030f500079031007100c010344250710303082c8886080d05100c50003a12502c048000015481440c4103d44081d040051100d8004241000140e003a0f076103000160001c00c20541d0006100d103400d03c006464081100d00c1035040d035100700c00410100d5070007091208 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 564675845 1250 564674595 564674597
    0xf0301060501093f0b070509010c06020714070303090311040b13020714060109020a080f06010f0c060209060d060825120c03080705030a08130b010e19050c0c0c011d01 73
    0x150500c46a0000d44c89602c5602c2141d40c0d40d00d0031040e02c01866041501050320b903014548040f02c0340c641038025141c502c92038440601203510505503801080c8103902618842e40284042070000c500c4c91884c506000c10b940044000c02c010103402c4c002e21880e000000030016059034200f01500602002130000c0000700300c40012150000780302020000c0b500d0f201f01d01640c0c01003c40e42c441d6100c5140b10043c1d00100b00d9800004c0741e55000913500760956505501038101a1502408a20340c010215003848111100781c60540d020082080b09481d03030310042c0301c0e01e640c200b000654142003255035820590501d0100350700030405141040d00039040300102d012244110b458010420592410110001c490703400606005004280603060020210092901f8106075480d50819500e44052150501c1804005007030900d4000c0140108103924004540120242005181450a0442407021f0b9070040b900030700d000c040031407031114034102041000d10503403007401c0005102e081c5031081004800408030881c = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 564677095 1250 564675845 564675869
    0xc0c0902090d150e0601091d070b03010501050a090e04080d060605070b06040c09030501020706060302120601082d010f09060609020c03030a05060105160506071403090318030309030a0606050f030106050109 90
    0x6800d03101ea640081403c40e50310040d0303100780d80c3d20706000b030040c00c2303a859041041d10b081180e0f41141c170300400e00344240c5800d00700090540e4208401151356030054507250081c071030314440200c0c0d41401080818861740c843c3c40e60741e83e5041203e01c40016035607580d00820900c00f003840201c2c0055029007255a1041c001e0300c0c009400c0400103070171140200c0700d03440035106500c00a15071042c41aaa088001507038001e503240002c2c0720032011800c0c2d64480900c122a0f0f15045140900030121101c0d40d2070402d1122880b5607440d58480d84039244c00c4a00d42804560f00341d550312030800421405010745001004000c01c1141000048001ca075103c0c07000429250300d4580c0c46000405a0780684191841c100c0e81560751080c2028624080343d85e4001074605a010a6040110340c6071031100004892180031010007071030a0410f9508561a52a41c600300a81c0c1030006100303a4200e070b103007084500c442a005580c00300d00640f801050041e106042c00c0c1450180e410000e05101903600700392240308490a501d021 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 564678345 1250 564677095 564677123
    0xb04050d05030c0304020d0c050d0809120312070c11090a0203150301020f0d11070807050303040c1406041401020c10091e08120304080d020a0906171501120608030301060c0c0902090d 80
    0x209000c603402e42003147e1146c4a00d40ac80c044c8110f080c054165203405071029803110301d224048c190b4a0080d00e2840d0303009618000051485031190306240e49552281510300d00880030000001c00c1c80204640c41c0703e800780c2c04002c0001000201004007042e00c42540214a05100c0d0344003030301c07075110744441c51120f0703a00e800014108618a00444006a411a400e1398a4000c249801d51300d9500545040e1050200e0810100740c101c0c4841f5680d42d0040d000b2310840c5807614154400c045c004a048142d0f06601800c04059250307200c01280c124491001d58442149500f410a0140b40034603020b0405c40716a88004207020000e00041c3c100c2e4100c1c1100c0e00c0d15101d50311807030548820b00c200d030032442071207002249011000381c200780c410090300c00d03e4550700c42116a0000712075901c4411501d4104820986882e421154025020842c06210603480071a40545074007440d0301e1743d8002c1c0d01a500041d072004500c028840150400809803c461109502c0c0c1905c5200298551400031005041c211415840d = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 564679595 1250 564678345 564678353
    0x504120f0e310c0f02070e0c03131e0b10080f1b0a15090504060902030915090f06010e01031b060206010b0a030b090403030c0809120409270b04050d05030c0304020d 72
    0x42c0d0140380d00c2e004244104020fa500003040220082031810140c820002c0114406030703c840c0c0c461148040149a5007196213a08580e0900000c0080545406240350b2181c6101e41c50343c40507002150007810400407a0500f00c45451010769207504c4004550021120f9a11130800480c05540b0707040301c440c0e12118145260001424603070250b00c40a00c40d50ba0070304d5252856008114401195400c407420810f10343d8600b07908003640b100f00c0d4500500d401820308803400050454109800400c20012214070006d003048041c0750a1081c0c04c10100001440010002c000180345044521034003150150f90103890000042c1d9190418024050005004a8011104d9100e940442400070004109090b0340c1490306028005085d003010000000c0d104000188540d900051094003540300c5100c170b24a401e00c0d011445000b840030281142c01c40c911555098090f9045920003404103004025248141c2024941146809034418111381404001d2040050015454003502e500c240c05450648504c0e24500d8 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 564680845 1250 564679595 564679669
    0xe0d0201020c031906050f131506090f06091a011209030c2102070906080309012304150f020606150706061701020a090f270f0504120f0e 60
    0x1c1c1c10b42d0075104103403d80f4000c02c0850115201a80910001c11150f02e501154840406084442c1140c103100755032031200080c0f0b11589007000ba86c0c2c1140c006100c5c1d855504a00658041c1c0740a009d40e2500c8a0f801e104000041c80313050f1505d00d45c00307001e5480d804c900f000686068a0156080e520554401c2d04205140c0180c6a0040c40f5501c00c1da0000c20710269202c0d00c4410407200c443c18010302c281c510108607482e89201d5101500c00d008029410600c0803001184c004441704400c070014000d802e00458600300b1f14014201824683c7c0841c190155540401402886500d950400b150b000c0403c0c08502e40301d0001c402031400214000c01c0d80e80c842c504201010304007550001c9080c6040260003400755030706501034180d4002503561600710565a10301504114901d004010220010400c869080910346020441503848010301240960041c0d10301001c07508210f40545810380d140907041c4040da484054240c40c90038900f02040d070342140c3c3c0301040784003c000100b003600f080010912100101541 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 564682095 1250 564680845 564680863
    0x111c03021b0d0f14010c0305070314010806160c0c08011b09030809040e0a1a010f0f140402160f0b0103020f030615120309091e01270f0b04151503020a0e0d020102 71
    0x36001b0300c0391502c0101c00030014441129a00d0000386402440d00c0e5180401070040d041b69841030040046848816070409140c40501001e424003030380784c035643e00050004043d00b0062005000000c2c148140c130b61140d15094201c5e84030800c010a010080c00011003030360648034465000ea80c0080c1c4001500e64503840e0802a03100640003000c032100b81204c820030000b105040c0c5903000124282c440e50b80132940340c061030500500010710103400d20650181420b86c00307401c104c2005a01030080320f0140d00c6480c60800b00e03010640e8007600200c010f00942c14821805000c07080c0507401040305192801c00f0b00445403100303200798130410202c0043c1d4102c8408106940d164071009123070490300d050800217000d03009008440c07500303050600000010b5420070025400b50807095a16031000320301d407030601072000f010f44a00014071141d03561748000c941c0e11980700300007141006d020300f800ea55081c503202e07a81e0741c18250007805c00c044c010040b85d02040c0e4003c21034035590b80e09851500b400211440181d0800e0044d07 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 564683345 1250 564682095 564682133
    0x90c12050f0106020f16050f010507080304080c0106062109021203040e010e0901140c0c070e0711070f050a090f020f032509060c0b04111c03021b0d0f 66
    0xc101400342182040707458030704a8041d5000c6583e25950340341c1054440c0000c0324159610800c0701810003040c1004040722030560300525180d480c0012690b02c81701141c105590645501c200428441c0803030700d003445500040c01e014280840d44610310210b804070710183c0c2e44200c1829440d0b8440c0700c119103840031482141111002520f03100e907210301e0102000b010034801c00c03840900d100c000c11440d403c18840d0789800040c01e020380585507500304e448187c40e8014a420b60301072189000024182e08003030745c100e0061030150b0b034088100b2a0940041d1601c1c40c0754210903040f8135005410000d6688170b005e55002c5984078078001c104180301d41140c80090180b0070080c08903a000108010410038440545040001404559601005011002c80e204a018001c0c1c601003aa2400810007080d070782d2010b594840d2082080c60040c5142c0c0c0046400203e0b1050101c035500d50710740b1034104058050042203e02c0d01c10b290f03040000000580000d01403201e901000e018001105c0c9450309020034590000c00d08500 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 564684595 1250 564683345 564683351
    0xb1c020d0e072c09030301051e060a0807120531050307050303100f030b1305010b1e01020721030c0305480618161806050306010807090c12 61
    0x9030b062542805140040032003d10044090407038800d10071505a20700403102c00000f14113507800c01c0e0070300501140c03000800504c44032540c1c0e00c0e985035490000411041c81c0a80ea240f44509200c00040e03c0b0349104400e0100b15410281000300f03800080e5001070340703284000c1026074440d076010048440c030800c000001d00103000c000754010520000100540c018804d40000c003008555908a500071000c03e07002c014181714224000c60802d82c01d504a20340220301813000000c880000c180041c0866001d110b00203000210849402420740e01070103903000500300d000802c44803000c00c0c0703a00c07114200c1481c401020301001d1100407051611401c10340390304c070003020103070094090b010000328140042102034080c0b0018071024242c0c40d04d890503014074440918802819541c940c01003100e0141110000581c281c8104034184698440c5400404018a22100c101801d002c41505410070f8610507080300c1c0c00384c0c1c0702200422040d980045e0040480c0d00e078071000242111091400c17a1b4900b60042000c002d281 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 564685845 1250 564684595 564684599
    0x3051b040b031005180c030414030c07030212010c021510030c0e060f1e0f0f10050c0613052e0219080a0b0f0409050f03071b0b1c020d0e07 61
    0x840c90082d40528125091800482d644000300035089440d08414028400001d0100c0c8240520801468003d8814002d0070029610700c000180345030405243c20009a000c41c100f04150b00304442c05046d00807950380207014801c03c180c0060b50710101900c10340e00054001000480149502c5922800341d540107510912407540c2d0248012480010340e071462140303e4002030025945815103603e03e28003464449501c5425410f0300b0014040c078501c10b66074202c4594842c424003a0354081107010358031115103c00b44c480c0351844070387d4507103440100343da9100b00020301004040b40001030300080c0052103001180c007090902010540741105880b01c102c24a0020401507440181c800d000d0a215082d580d03404006e41c1c0e884240c4094540101c5040e400480404541c50b640c20241c10402e0b1845c0180116042d0100081e40140745a0201c80e00f81ca0002020441d02c00c0c100311982c0c001c000b800c09542c010b040920181800d045099403071441d0780c0042c1e0024030141c0719080c0ba0410720840d109001580d000139 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 564687095 1250 564685845 564685859
    0x20301021b070e150103050601030e06091e070305030913060806042121020714060708160203070230060a0c0e010c0c0e09120c07031202190303051b04 66
    0x10003101c00301481405120340204903000201045481041440e01c000c0421110034015001001d020301032504041d02c81f010194130140801034240a038031484010299040503640344075003407014a12058554209280c01c0010400000c10380303080d5142294040c1015100080d418002d0245a1210800d401460100000d0202d548040542c1c590700d100300780f12a02c00c210084900b1a50040c013840320010000e100c0a84410690290440341c3c4592110440b941100c4540d914012040b02c8520015111504000514406088544604c940c81c0011030416245500150100e454120704d01100303c00d41005101800c06090902c1084036000c0595155042025001e00034105060700c1d2400b040c190b00101845511584132543c13503541140d441019141049852041081c0203880c520b039520444071150345a520b080000c02031003a82e10010b194040c80d5150100148040784040700954224501c280e40c016031549081caa4140d040c503000410369a40c0040004c820001d00c0660000780300420b010400c1 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 564688345 1250 564687095 564687127
    0x40612061d0a05100c03050601140d0905030c070f0e011a090a030807030201050f070c0b131704060903030f030b1315212003031c020f2101050603100501120902030102 73
    0x44880e5135400d001441890300158195031041d9031041c00501c0d90000441c2c4002654050b1503230021007072000c0350544441e2030351451500020720390125900900c5042119410031440c11004017140c0816103a00d40c904124841c6204140000440181c800a2501407994401d0311002c0a50792018100b42c4500f010704000b4000c005c00c40e01c034041c83c02500702203180d55006420300003649610144000c0c240e0b491200c681006c10311048115544a0340580001c880700e4480d0103040075213815520040041d113542030080c1611034586203501450721f4659444510703290801c0049100d241040040780402d041c0c100140614103680c004900007030710300003181c0301c030034074011a141d4507001e00c98480c0781403003414513103240d1545a0200355246c1e00400102100007660019103100f642010001801d1440805e00e20005600522144c2c00e1b880600c9084000181380c408030030301402083d5401410b51808404410300c4103034602400d4180481c203000c80c410401550440021a54084d00035900c43c1e852a01d03108071 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 564689595 1250 564688345 564688363
    0x20f0c011401171018060903050a090f060503040210090f060e0a08070b12130f0b1e0402031b03070b070c030506070c030c02040b03031303030509010e040612061d0a05 73
    0x140d81c03041000014880c5040c1d044071840810800941400c800c1080307508014406110420040f007150300201001c10201c4c802e00960b6130294542584d80d489001c4005e000307402c030b900004641c1061103c140625540107042d01d074003d9040d10701c17900e40e50340a002900d4201040d440b01c0a483d00c81000400c3c840d0340081c5c00c2840c40f030213448001c80907860b0030060f0f80300c1c0014015452410010300c060314801484242c0250443c910071081c450704005d03501d13081490180e2007410703a0221519801d1110800303182da0480c4107410000316002c403504055000030b407240c026801a0210300000f5040c0e44c00d0b0f0b501404100003d094402c8001d07550105490170060301d008034403080d6414060100054103580c043c00c50b40304d007170340d05a07520780403605039900f0040103101154030150544000e002c461122440b40007110007450107500d90765128060707038000402071440111001d020305d0a00000f00603400c2511040200194803420100d04045001da50340042060784031051594883c9040d58001d201000c150600 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 564690845 1250 564689595 564689621
    0x201051b060c130b04080c01050708070501110307080702010b01090e0a1107050f150c0304170d02180a06170a0b01050c2b0c08030a090305190e092d0901020f0c01 71
    0x3d083d03560040c15600d4081c0d4460112150003c1884510940c031030001803003001e11a440c502e0510030282c44050842d0305510201c94421000424011142d800c05010b41c0e1043c100d10003400b070b109007000024080c580c0b07445050707030f102000c8010031614507803504140140120b844986840f0700f51400c2459450040c200c0b48038035801083e2210a40107600784d421031003480750300d80107840c644595a56100c0c1525100701741d07000c0e0740300307000b0000200c0d0540010b22256031640d011000c00441038040284a2030350360300900070700ca11640b0010010200320070380d82d40f0550182000501306204d10042c2c905200d00021012680103104000030310907590148200c41c1c81d040240702d40390403452541504c0750200a6809492854144000340030081a5003010701c020f486840d203135082020710b803c42c140d0052444c1034880440d50170400c902c10303818040150382e0310028400c00d0021040040c0038007000a0f03890f5021264000c040703800142d212900f5012039100c80b030407180c8a650399034103500c554020071406d40701d04 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 564692095 1250 564690845 564690877
    0xa0506060a080c0d0f080405101101060e0915060f1503190c1734030e0a0c23100e040e120d0c11030f090102060907120201051b060c 58
    0x407a90703101c0000d1000c800500900113107107480d40754030340190240d524842102ea00c1d00c1000085102c0d00ca50300002111329094480d580b2400f04000d606003520740c2904600131210500080001c01c01c00003170f5401140c42e000c09916034070b4891001051f88501e540c4181e80d045610a0000c0c502001008010f43c850041400c2c8400c5a040c11108203007a0398100c0c02e81400121401e10a031180e82c090242c00f504000b03404546040e8150320703000000c07131118405000c84e00d0440b20028038141c81e054001e07483c60001103c080d0000700025035440041510900a104580905107000c00305083c6140d56190081c0d00200340303039030710f250b6914000d024914040005004030304000c4041749a84001a2010011484046260a000a1408050040521800d88401c010145900c810380f001c091004003000c102490b021a529110980064136145001e070110415034442c60b01005481c205000600300a982480c00955441c0c1211005402111404950029020b000180003003018550010070400f11101185 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 564693345 1250 564692095 564692099
    0x60509030d1d130b0406082104121112030d0c14070b0a0b031207060203090705090412050708070510050601111f2c0102040303090506270102010e0a0506060a 69
    0x40300d190380c0040c61842d0401c50150280c01e540342c110f102045022001c400050610210000102074501c40d0b4403e50150708441c201088a420050b03081c0e010703a1007120542c4c43c0500c1c0144201c0310301c42001003d450500e44c0c0d001440b09603176400010504200d400304598a4207442a1b851006005c018290400715001c00741301e80c0008186810b5681c403640010a0355280d82d100c50031038014022081c1c50b184e05028601c500000305c0035400242045a000d02c0c0e0041e101c2c40c2c0b0101d0589440340c0c5412552040e0100301c20032001410042501c0741800e4180b0b0310329207032031803454040c1c254000e448008055000300c0c01c0d1180400b002e548440d103e030600f40d0b01c8003a4000c1415070b05840b41002e1000d502c15001d8404078410b290800d03001008014110501c669606007411000e44103010441d40308809079400050030401d040d445030001010b001c048030f003145845503900305203656641c0341d5008400100480711410705a03000f94003882c000203000b02a50340d51f018900c0c00c00d48540341154854442ca400e4000 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 564694595 1250 564693345 564693347
    0x1518032906010c06090c0b040e1501030510060e0a180903020d030b060d1107051c0e010e13050a060302060a020a06050f09060708280b041b020c0415030c060509030d 72
    0x3903a405000d0607100c01c03a420486072211030281014440c25240080505800682e0b0300403c40180300400701c07032440210f030341081c1d00004e000c003031408101030400d400d040500080440201554040742c0c0d80b401d0207401040c028010031410401944101e450400000a01c0710501d1140c011003102c61095094034402c8070900c4081e01242c0160003a03d0b0080d600b444a000c81d80025840802c41c04c2e1114a501c0c00c100070f40c1d54a5141c940410440c4d104680142c035001c0c1259041424200c05000908007011071141f07501c08501580c200480c122042d40d290b00120380c585100368041d0740615000340c0819034a4626580103580c580b903a0a04440032454140011006000114664011003801018141d81d1f150040e04a8058102a113407a860074500c915148020b0fa0900c1d00d1000c1400004000c5000d402c2002084101c43c0401f41e410010006400e110880503404a41c0d20384043c4200d0300040c0d0307038000d4a4010851129904020801c02e181c2d5800b084030754000e0050000315000f1000c4070100d01c20428 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 564695845 1250 564694595 564694673
    0xb0a09140901092a1203030903020601060806030319050904060324060e0703020a02030d05090c1002030a0e061b03070f140d080424050f01170106050a151803 69
    0x2c0c000d07004010300f841c45041101148030800c128000c40704c0c0203a6040e1920b9400324000414402100441c0e0b0350300d803000030140c0604c0680d00502d40c505245000345011400b09031241314031340c03030307040c405000c05c545c0180c1c14001c1081e00c60401000e401000020340f6071400c1c0e02aa5030b04000710011000c03040980d01c0c88281409902c0c03e844800d2600d52840c2c442040540c081d400400d0b206041d40024001c01c582c40700c15110700c5104804590090481b06002c0061015140c070107210388045401c1004561007481d00900e04030315000e000d8484546d00d0044425171100d000d0142d40c0748100d4000003030034006100c03c5079411780d20280a40c2e00d1009148102d91074540e600324800181012444035000a030124840c401541c2541d50f0983e20020500c1910320544110348003215045021049074005008020703015030007401c22b02c64200200049030421001941010387d512a40b00c19481240aa1910070702c50100ba06c482c1d0200d080d00720416483c1e1915001208150602c07481044d0b01c03404c1d007960940c40403 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 564697095 1250 564695845 564695861
    0x61d090f0c010203070636020907030b030a0308040302030405030a030216050a060906030b1c0b1b0310030b0a09060c1e0503010b07060b0307150c060f200d0b0a09140901 74
    0x10700210302d058034940e00c080c0504008468803046501100224800c581400020140120101d07030a8038147d0b050300c1004003030390780038203003d04140c07400f0310314500c1340c400140d0000b145400d4100440e603540c5030f10741240346100d9038001503054015030f5a42020542c00203840f500004503000c40340c0800d82c4600034441d00724070521038800001d00b0018100f000c64040e6200c03010385138010309002244503000003080442c0354883c00481e08011024108003100002040082c0d205090702d50307580c03460400940c4043e2010300ca0202806a5441c100030491200321607004494003a4002c0d402e000032984568040c040864111009043c4c0705801000e03002c262080c03084034103030380c013080b01071741032070002d48900d030080a14410700c0790107109010f0081001c04010f0740c003495071713100c6a440d00c0410603580b60a00a880c03008204203003160a1200540c8060001c07001c030165061004a007030344640c00c400250300504103100d25141c0100044602041510f80758019401c4031010144850341a2240e1420f1030883d0703495 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 564698345 1250 564697095 564697097
    0x20702120a0201051c09080f070b1b0901030c030f053108030106050a05070512041e050a03060c09091a04050f09100b03030f040f151103120604061d090f0c01 69
    0x81000c1701001c500689000340d9044030003c0001c1d07050b00307613540103040c0e4844420f0040120700800c03040c04010148003040c3d8010301101004000500c41030380c840440c0555180b00e410b01d520340109014080c4a54070240029260300d806008608104104200781c801440060760540d6801e030501200403802c0d0841c0f2015540031f8819071035680f9180d0f00700c0b42070b00705411480c20008200704c000c0c08a02c08006a40c450900400c405950300d00c0c003508036041d256021100340b10360192440820450b50744a00301c00889400041c007050345160010115402050340d005100b442c2d2820780c204001d044003101c000140601034800700001d8850040103090824119084034a5601c0315482c041c204d80260882d02c001c003409801c80b42000555141800e05800c00d0b00f20504210b0f690004001c80f05030350341c1a0704030b60117500f044190141e80007034040e180d225001071201c903c65504085195502c5d180e001d04010a50307010784c3c2c020019403007000c104410098800a80300d03c18425079010380344020070444024141 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 564699595 1250 564698345 564698347
    0xc05070519020a051002060f090705150f040e070801060e040b0d02010f0908030c010e010c0f0906051c050109050a062c1806090d0305070302090a03021e030d03020702120a020105 78
    0x805000880c1414a01d00100c2e000710620000280544a05243da801e598058000c0c1106140911540e100108000c3c50866540d00001d01003000d511118058401c1c4401c035901640c3d5107146116407440382c42654400d46c0341684010030442c04030f5010000c141070b1403440c0d8400340e2007400902040141e409041d000c1c6c0d84826269006801507000c1c0072490b08903035060908000c00c86e0303500003180c2907801c01001d681c0140d4643c4802807a00c5001c3c4920200d41700142010341125400c250700801c0601940100002c5c0f1400041c00980b0755400d1199149418002d40280905d686584410010300b000341c0303d44140d03034103115021400b82503a060301d654a503907000c04a6000c115113007074100800170240c80c420411510081c101804c960610105120b001d01200800201c02a40c10007021160000c100c5402c041c0b0600104816a54a070b81420441c0c2d0121050f0500c81d540c0392030801324402040609500d0710940103111101501600034101441c0201d030800709890f80070304019101c00603204002d0000c1d40c = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 564700845 1250 564699595 564699613
    0x3020c040b09150d14010c0e152b11071506051c150c17010617010302010c0812010f050f0d0803130c17010204090b042903030d050a0c030c050705 64
    0x2103220078a002504000c0c2800c01e0f8800c2178807900b145c40004800c0a0981e5194880c5010041e00203c07002d460010545a50001070b98040c03c0440134000d41c1070380e410620701400d111f034414508072407400107540001d03420001071018102d140d031540d2290900b294040142456812030301c20a10504080380c070003403d9131602c901c01425884121514500c100c0300f001e00401c5801840b0b050b03110309081900707284c8a00803014283e034017040100c60141d2000f41003041f4820410304006090341541d04490782801e2500e10010b25243c450b0142c000c0300c0f007000c0002003e030000160000d94a03481811101c054800d107210701d200c281800404070fa228005002c0703080c2000170502207042135480310021400382d40312420040d05e81d00305150760100014110540c1c2e4002c60301313000c0a49584200340803000201c40400c020210316080c00c81354001d00c01a103050440c9401c280e02d580e1400c0c41141c45034070041104000303030318110103414000d1030103440c101d00003840c000c60440842c0c050022901410341010082c40540 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 564702095 1250 564700845 564700861
    0xa0602191106070b0a06050f0d11060a090e130201090801021204140c0a0b120f01050904030309050705120f0c0d03091a0412110f060910030209030307120c03020c040b09 74
    0x480340c40c01c0d80c100707070204242c0011491030640ca030f00800344403201007070061400301003009003944190b0743c80c0b045129807940d000094603895200340b10141a281c0340d031503640440d0182c8200415901004d2480f2040003002a960030b1048621030301c6100b603e5400d0102d45a0a00508034051032003484424507201c00828041020100482928240300048510982c031107404140481400d83c402d0312505804203410242c12100c103139042e40280718444542d4250f140c00001210098040d00260605548100c1042445402d21003070000d02005007001420103061400d55a071102118210502d500801d0a040e07424940b010701c1105058040d500c408056080800c04c28201080140315412590204070028624000341041c0c148140a5155100d0140d902000d011000300d40c0560284206030030850268035542e80d48240030014118a070041e2503fa107407022900d588980c0b603000d410003002140040c203c1d0340c01850007070005c0c4030794251040c2811311800e02040e114a40e40c1940d00c001c42a001803106 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 564703345 1250 564702095 564702113
    0xc0405010509130c120f140712140106271505160b0c0316020a050d0c0311070305030309100c0f050a03021b030a23090927010b0a060219 60
    0x2d0000c08800403901800207440840707003074000040200c2c1d0280740285c9000d0700c0c1d20621080b040849800c0c0321010044001041040b4014541c04c28411800ca00c042030b030700b0542c401e144054075401c80c0101035840c0c8002030012000e02034042d10404805d1007012030040700305445021520081c90f9540f4082114130b01b03440c1a0840440c2802d550200090403001c19000c20743e950199440108182e0340f402e0001c02c058884140001d00b80566200c200e8901c001380001a80d0b0307507070188603d0414030803206403030100d41c082054002500780380705d8440c0200030b12102000440c004d1480344101c41e000c2c002604030500395403d6034034003c003048005d283c403400c07980504000d06136a1128503005140166244841490320040070710056191700c0441c840d410560800e820000c0d050b1030700e062104c3c4200070640c1c1401485441100e038051052100071880490401c45003d541512004082040c50012410540200402d9025a2244000100000340c0700c1c0041001088a03403d00e40800b20001a0f407101608 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 564704595 1250 564703345 564703357
    0xd0c140d080307030c0e030c0a090e0106051e03011d03041203030f090c0e010605071e05011d030a0323150112060b030603210301142d0a09050c04050105 67
    0xa0312920020000305001d00070740c480d07041071302c0018401c6401180200359400500b100c500a60010075050040d580d030080140850f000641301050014070400c40da405484035501c010307000014082040d0311b60071107401c028403480c400e4000f000a410008840707456060a45900758190f00108414003845811a500c1c10301903029041c04900e0030a081f4015003151041a81900c203002269014000d0080d400c0003980186001c0c0303030042c14100581c60322541064001d252030340d14001180b0100402c6804e401c04a0300321044403006444c801002c010036101d501250501000910f0f0001503425084081c100d4080d440b0100004106681c1c2c0c5400c1c00101c0050050310381c10712504445141014403980100400350080313100d119224180741091500d022620410180d5003070b059003201c50070400642c2643d0456903203090b1542c00c0d51501002c141ca500c506850003400e404012100d142002e100b03502d109042a040d140381007015501d090030030807202e00780c0e803041d450310b4100010010356201c1c20241c90 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 564705845 1250 564704595 564704599
    0x17010605060a081509010602030306010f0206241813050712030807050307140328020406050a0f05090901090614100e04240e07020f070503060402040f090b10140d0c14 73
    0x3d07180360058001101784000341e1200c40140e00010410115503808000800c0c011f80e030380000c00c15828100c4510040c541c08403401c1340d8150f035000103490309580380030301011030740c04140c4c502c042804e03c00d2411910f00c460a03020759861191000009103440701110700030446425948560440d15806411291540040d00482c20860551040780e008100900110300604403030919071817002100007111a01500580176440c0b0900c140000c111091b0010100c40d4008150f00e0090042e5402072025159406070041c3c80f6080000c2600109000c0031990054080d699514440326010070717401d040040d1801c0b07052181000031003442d0000f0090805400038040b8090310440560820034000c080c0403905150350240580125950030301070155010700c20b040c066101e210180c1083c1d42020301181e925400a84024003036551030303400390100600c550021502d01c0c3d100c0300c222924103094a000d10390304001d0041e402d5000020300380088926105510f6000d45511100d07000039141b03489900c618000908604503 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 564707095 1250 564705845 564705871
    0x14090d031b0633080c09071809021b0318060306030c130f051f0b030a02160606050a050109030213020306030109020603040f0b0604020f27040e0717010605060a08 71
    0x940062102d0103683c0e0300360f440011030381c0c940d000c10b00840c4414118410803d008000030a090101a0001c03410f02c90701c5030251a643e031039403a80541221080d0503184400c80c40302e4200b00c00704000d0483d40082943c103e92051100c04000781007130075a1644502005a9100c000c040d800c180282049405103600c41401000d4402d280840d1010071110803600c41007502455a031280f06100311003901c0382c0e0f40c10034848a00310003008840c1c401042c90310780b00d018000000381c012000500d0911590110703800c802e09000170054100d610301e4498040d10140c092284070707042015002c0340c907520928041088a0b00208003960203207014818a00035440908099010354a901c54600961a00c00c0118001d43c40b4541e0b501c0100e015040c040c3c803401d03015000c00c4c883c45c010041420005111019580440c3c99401300428401301114101900441060705581042c1084000d40011401060740021102e8441d0004864028811450b0032034840b405544e074050024011616040c0c40b555031190301c200071500b04 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 564708345 1250 564707095 564707147
    0x501210e010c09090f060305102a11060921031f08060f150d120903061b0e030109020d030c110d060b040b0d0209011715090601030314090d03 62
    0x500b59940340c038004000ca01d0f54070080211030442d01c6a007100c007910043c03c0020038195a10907803558080e0340d19040c2152100a0782c01c94407200003160320412142c0365a1062150501009008207a943c0c000580e5805010000389a0710fa010501e800c09040f0141ca001da240c00c54000c0d034241340c1000d0075400501104000c00040703080141d103001e018007004030080200c2d1034100e44900754884020300c00d4100400d40e010100355500c825410844080d4403600c1c072200d1044001007100c2c0f2445680c4040d004500300120048580d000010419580316240d40306070a07404202d040c18240c80ca110002500140390b1142c01c80072038131828411254902c200707180d41030b08008070002840b034061003100751802030341d070720308480e041c5030905c1844061001554041c0c00300321103800081d03032841c1c1440358410303d071282000c607144d4941c1801090545912000280003900748080116900c9200f40001c0b00410b04480c0c0310b54030b0160b214192030504000921480200d101940d044400d03500c1e01140b5170304e03940d1690003 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 564709595 1250 564708345 564708371
    0x1090c030e031b0d03060303140a032309070501020303010e01032a06180909020f1c02120a02010e0a0b09060a0302040506030a0507080c16141c050a1701050121 70
    0x400d119200d00755002a00c110540b00d42e818032422007903000503d80386c03203c2000001c0c1c00c000340064203418132404903102c030094001a001b518035442c004c034170006030081d142d2424100c1030b81c660041012400310703500661110016a40e0344000c2c001c12007000e1000c001080010862005176030b09100f00c2500c038420420b98038210114a401d1f42064011030301500701502c41c0c80c288103400000f0500d1600078005501e0b0358001c140d0190014030a140034411484440921000b1900b112402d5036010702105001802403c90780d44880c21550101d0000700a617a0668580c50070f040d41d802640e20b90404146000340490400800758000c1c0217084c180754003407000090a036221005103202d0b14194401080340e10304a8802020340b4001001550040c401713100010040c0c1880000c508040c3d40111001e000000c940e113103514043e0960300214998040c1245012400e5100d4050310310000f040d01c5804c880b07006507401d100c0ca003000b4011030b40080c0703910b00b0181c0351401444000c041c0d819901000515400041c2c0 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 564710845 1250 564709595 564709597
    0x80d1b020f0f1305090c100e01030906021e07020f01050f030109051914071206081207080909070504180c0c260c0304060e09040305030f04110603040b041109090601090c030e03 77
    0x1010510f0b9990303410070440c0600051101c1c041903a001c0311100f0616005400c0a0030300011011110304040d0f95048400c01c00c04180c2c100c900e0642e81c07600103649600c08500f81d010960003010200d0003240e4042d14044a54080c9060300c0c500c551a800f018103582c20440380b02e00810009040050340040c20301075462182c481d11500f40007465120325a8214a0030a0003d00303d0389040d5000710301c031403030000200160304006c1000b002900b440c0e50360340d03510442400d00380b0341e901881c2400c5034401900e8080c000740c180c0090080c012140310043d1074404000b0015084100c2c2c13001c116200128070078419003000075801d1101213840c40c001c2c10000300605e41d00f4034001c3c0b0325002107103015038a40c00000c06001c402c1e04400807011510040728180b0300c5207065030f0f0081c11800080d042e2400c906e084408202005110720886050100182a264480c5090704101e20003c505403130136103210403020310080450409902e01403044603100d008002a92078054000024007007003001c00101941c9180b2041d25600c140 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 564712095 1250 564710845 564710869
    0x60b0708071e0b0c071109060a09420603090f060207020d050a0c080708030c10050c041203020d081312050d020405150a020f3408060f01080d1b020f0f 66
    0x130301c4c02d403a22428a046e801c0340414200151183c2c0e404010803000380d6440c0381c0c800030342d0b01400340419944092172684686c0d03d4408411003407907030304040401e103a05040c001400c0b1b1201e6050300109081e0b42e00b8080d000c482c0b5000c80904031100c0c90046902141e0a5001001c1d164409407640d04915030030345846003003040c1d40da022a440a03020744104942c05041101401910030180954a85040a410190307203920002800c1708464481d000224440d00020644000740b40e0754a040d002d184d96460025103c08901c601c440c0030802c28000b00303805c40d60f9109015181e0307a102c1580c92441084c2041501d40d03030031440c480c800e629000c010100d5151680401020350304091508582c4512561001904184443d90f1014580e48035004002412088880401080c0b808803401d400780c02e106222151b00d640d031130f0440c0c44c4621420040c005241c0300c0d0b441081c100e420340419200c3c40c3c001900e08482c0111200c0c2004070355081043c211000d03180c020504100100300800d40e04400d0080b00119030500084 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 564713345 1250 564712095 564712111
    0x5150a030b0d02180f071b0b070c0807060f050c0403030e0f040608100b09060324040c0b030c0c010e03030c1210050307170708070501050d0f0e0610030204060b0708071e0b 75
    0xd091141740ca03c000025504910507041803003081030810202459028030b9180540812140c20120b40b080780500e03a801c0419410150080c3e603040c076824504081c00c1d4038a2400342c4c031442d101c000f400c1024010b050b18142da070301d951080f2240e40c1c0f440170850400c06847c09564050303a20b140025021004000031540300710800f00204d5203c20b40401c21024010040005000e07822240d40074020f40b464840016100403444062484e94599007491500120350342c1064940340b0001081c410038405440203400401c0d614802409465091502941c890109a85000181c1d106012042500100d545030350342c400c5200c11020801c0782d40d000000e10303204050740803032032400403040e110500143c140690005440b03040020100e813494480002d146124680d02780121f180e440000041480003500901e020407842c400700d48041c01e2031840c0c18013070b19a52004078402c82c500140001c407001041c0a441105070040245801e01141c4e450709145010390640c40c400440145140c42c1c0000e045480705409143c1d4 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 564714595 1250 564713345 564713389
    0x6130e01052d01111b2706010c0312020d0b1f0503011827171908070512090c120705090106050c070e0705070209010501020318040b1809150105150a030b0d02 69
    0x170107014212541c51400141c40c00134040c00c0b00410b8840c6a0140c1114003803a050601469a050483c1c000c803210407511003980c0000340c2545421029005070300082d600316007806118070084c4802042c40050034081001c80c0c8244010044501024002c030361800c1c941c040070500410041c2c40c400542c03010100001003403d0b550018051000301280b40300910b6044841c2481c00c1b000840800303450120140490130841d00c41d002912191240080c0c6180051a200411080c100100c219444921044980380926543c03009042d0704c200000700281101c8020300391080a034203001e001c5a29500017440405188105800000c03c0102c03550014400c000c995140c64590001d44100b1010b031006a0000c0e045510038026000c1c54070300d00c60701415441003100d0028680c1140c0740442d0481d0192078050b0900e0200000704985200d010031100c2c91940a8415100582e80780c00c1040105085c03600d1030000d11105001e1690528080d07803041c82590070040c10b034800c141c0303d40d00280380c24030f840401803e0114 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 564715845 1250 564714595 564714643
    0x30507090e03040e0a0b0f030613060c0906090e04020d0b070201020d0b0909060601030b210109050f0622061508011b0813021e06130e01052d0111 64
    0x22051060341107401a50010350f1800e860405140110038001d40252003d03035440c0d8131100e00d940d90400b90480400f001c1e064501c149006002d1544150f50b500c01526000c0c00c0c2036100e454181f2480310001a00c3c0701c1e8450160791810700d00310301506c000003041280c0188070f000b10300001c90f078401c0006105550320b070700160350b907913015000f00b064540740350405004001802c2440785c4050049400c6038480820320f000680002c2c20000680184080c05001200444100900c0030300f0a06410049015018201f00ca581c4040071f9a840d640c1ca03401c4810f040a01030006615803c00380100452200c40d02a620114074841030040f9000454501c4d0311824650b035403552451920100c0341f2100310181e600e03042c0128645018a0a0b207200d94032004020f01c25075988403211401c204402c1070a070211b0003d0161520780061034181c3c000e039607650044098045a40000042600c1c200d00001007207503c000c0086002100241c02001d69500780d0401c5041c041c840700c40130050b138420007144603002007140400204803 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 564717095 1250 564715845 564715859
    0x80c0f0c06090f0607050d02030a0b060a170c0414190e0c0a1701061e0c06020f0c100e0c0904140d05041404020f0f030408130b030a0606030c020a061802030304030507 73
    0x141154200c0c00844e00010104401c1d035030014141e5000c1010035201580e03903503540324424000d20000c04ca1561242d0003152124240394803100c1c140e09001002090303c0103072500c2c0c61030b5486005a125400c241d00f40c7c0310603070403242440030110800b541e8151400c0015622032248550b07582040b510100051004164070f1102940002c40401c0705600b206124510b5040600040c0100c02c0700400004208450300300c0e02140707100f04143e8449a402103821501c500c08048035044580c01042c4400c0b031449509000c41d40e03078403684a0b810030403c1510090500301d44100078460b0070400144140c80410540c0d0141c0c0380720009109040f1100095910150f03034a00f050541541000d4500c1014001c07403040c4140031302e440303550b02250711b071441d2000c60a4680d03072603203414030b500c2c03103040130705040015070741000950010f200c400f450060952030800d12035140c9079030040b0100c4010a05c0d01d03005901201e00b00380403501d180c1c04000d1404074003003800381c040701c0c540100e80b0f954481d074021101e81e0700012040061b1 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 564718345 1250 564717095 564717103
    0xf0a03050403120504050a02120708070b0901020111030108101e0911270c0c010209060c0102070b0a18020f012a0501050f0106020607050f04030f0b100b130303080c0f0c0609 76
    0x3480c50f441084a410f0075180c00307030355242000000b402030104511900042c0d0040120b1401040301800b112205034403540c20800d5a0400308c91a809076003001026103126500b281602e0580700860014150891404003c034042d00412070845000042180341c801c5d15841400b641c07207401e00907c1c0000c600c40d6440284002c1802e070106484440b8440410103d82035420102140c106110840c030383e49500002551038020301c04c58201943c0032000003813005c04403074190060004540250110802662081d03581c00507645480500c0c8910045e10fa00300340149000100034441940c180b4201030882e10203107110b4400254000424442400084048100b140134040c007580256400c510105039490000b010359214030180c40a002c0c01404074030002910100c1080d94001c42d044600c0c600514090304144109000949082504410b000404542d00421500f107403043c4041d41414043d581c80c50300c00b1225504040c0c120200b003001009168034041d0700b5000740025400c20809403080741000c1c40458a0 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 564719595 1250 564718345 564718367
    0x4030f0e0f032505040504050d110303060603010b130504060b070b0109140609041a10060f181a0d05010b19030c1e0e0a090f0b0d0206040b0702060f0a03050403 70
    0x201d07030080c0000554580740400c2d2080112040400141d0f806840024501e00180742d0300004d03040740c074100c01c200a200c0001000c0e9100b0302151184c004126100c48120b03100e00c011201e19070000010401080f0042072500109450140209041c0159032548002810395505506c103a01c4c0303c0c4040313900000d2107170140c003030342c01030100707440400c03106162440c54090110014803951152100c800000d007800348100004012152010422a83d4508014100129590390040c4800603090706100c0c54110701a610046040c2820072030402110324060541050140d651030b2000030203002d0044000460050044501034024101c2084c1c5400501c202400004a04140d4104060030070366000002608402d1a112103610200c01100b03842c64442d007a5042c0002c0c140560b0440741001c40080c00c8155540300e8000841481c4051120401200400000e0300040c00060352115080008000103200103004050f0345101034841820704e40703c120301c4ca0064102000390300219461b00304000c100f640c40440c00613 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 564720845 1250 564719595 564719599
    0x1611130c020c1c0c030308130821060324220807060c0f0c111206040b010509100501050414030a08040806060a062618100e0c030105042d02040504030f0e 67
    0x301e001a036441d41c0720708440b144806011f010b1188003203030120822903075036814640c1020704540e40b8140c5040e0b685848100a01d0038010888a401081052038007050500c2000340e0840014564100c190443c100e09001503c80d1a5900010000380f03040d202c1030079841c10490044030190b483e00003e08080707007565203505484080190310b00c0701c5a00142c000030400750280e004100b1640e08031480c00414141d607280002860b1501c140801c010070001920300341c2c2c2c16076206486c1d8010540b2800c0100c03003004914011b0310b0110702e040c84140104500483d080041143c010112a0002400e880380f1601e80c2c026000090b01d500203800300001070419090040003090b542c039004818404503000320450348012560080c030074040001040e881481c541c1040500506481510740da105c101000030028043c045d6a0101f40c0100c03020509a49410708c40c8511558100481d0110034490b8000c69210005001351054200c0c0810a80303070168841d403040c035218034460b07201c0e56500512440d010b4803095034100380038 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 564722095 1250 564720845 564720889
    0x406080c0607031b150f110301151d0d0f05162103030f0203010801061409040b0609070c0c060909200f09060403051203160201021611130c020c 63
    0x159240c0c8503082101d0b041d50b094682030070140c5100c0000090421181d90140040602082c0d02804003000d900120510700000d200300100e0510b640c0c0c070071640c08240304415030490b9240304000140c0c02100d1002400d40c09401480102d01c201c800101c07507001049040d2092500112020700f049020009000e110031031030001e07503000f0320b401c514414000d000180b42a43c4c0d603401580c0ca08240c020b40124020b0038404000703546035a10f130b0380102d0081040f881070750124100c00d19000311505010507120300a5803c0f00314012960f40e050180b100488001c2c040204008040700c0301008601800101000303005a0765403034074000d18106c40360043d64000c02004c40040e0003012102c00070750800b000c850121058000f155210411030380011782c1805540d0000d4958000c03e010a144a5440002544920b2400c20100140d580c00c0030102d08038000c501d0042803028010b04400302160307001d0443c00e4030740002031146100945200c92a4140c0c1c0c40c1e5410a000740c0d0000c0610305441c0780005005615100101c544 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 564723345 1250 564722095 564722113
    0x3051b0f070204020408760e0105030606030c03040c09050901020d06060e011d06040302041503030219080d0b063001290a031409031309020c03030411060408070311040608 75
    0x90440c01880b41071000100d51051f0107000f007018014000154000d01a500654004840e030000d030280d144402800000320b00340f0f4201e40c41d60180c41964007800d005400390341150ba42500320045644068415030f82e808610800290150040c06000c4c40355038004005600c90100313454150560b03120f0340006050009000f000041e90742d206911110f8011a80540014021102c021541c144100e0f08042c1d00113003860014841c4003c02e9124030100c030f10075821520070b103009000c80101042350100c0206002401c001510400d001904801014940205268076122490540342d40d081041400300b001410907154154a102d22414002c1c010074900d410a1b143c16080300d0440c1468a02504aa48248000c40c007012040c0c0310740d220307a50b803544041700003000c4e08220407d1039698002c41c05003001200880d001042c03c070313400d0090340c1080414034011410360f00c40c2e07034407201841100c08100da00000b061100040d0a2410042880110300130b07461a281e800c80300c1c0900081d90b4660f003004026a01500c00 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 564724595 1250 564723345 564723433
    0x90905070f12050a1508010207200a1403010609050f090606040c0e01030e100204060801080601150503190f1d011407020a1202010e031803010c03051b0f070204020408 73
    0x96000d600450010000b9144d90b02c02004000b02100c4c045088121010580403901c071205500505031580906075064903200028448503480504448058120060030f40400a052995210100c0100c00400128500d61103007042c0081321011140d42820700490340521000400c1400100c1d00440c0a440501c02030304114000f41041d42d1024400d410582d89400d80f180309103080c4482c041407151001e09550f00caa5800d8010500f00b005c3c000c0e001c2d103001d2840005100b00186900100000d8651102411a0f4842904cc94040e0080c080310b0304d06915540f524841e5410f038428100030079268400a98400c5803502c0f05030031907014181322482c8045040c05d000d40507400299a14001c0e5010524020b00100ba210882c09401c03802d0a0030342a1001285941c10000d10810b450802e0009400800080c61022000c030141d03502600d400d000342f075105030110403000d142001071161031048181d2601c0d106840c3e011030100e030301550205940f80c20895002c03019080c031800c60b510340c80c0c144018040c26060206 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 564725845 1250 564724595 564724607
    0x30b01090e1b09030307050c09090a0210111606030c180302180c120403200a030e061b0f0c0f1e01080a06121401110a050906090102070302030d090905070f 68
    0x3034040800c40000b04940c112480048a201c00c0d005800d994442c0310780d1802c03556411480d071003c0d104950400001e051503900142c0c42240e2a0000d003840369907047c0490503190746049417148030450241941d1228041034240e0980000c040c5a84c0008204c00111402801c05000071540e10740c1000d0290200b0141e40d407080e5289142c03100318400318180d141c0c102900403910441e4240080c07240c0100070807003030540003114400c0744d46083d580d040c455034041c0d20103604c0d1040151b00a020641a0034290440c0c18100042d104421080050343c0720024200c1d607003441c111852480036060f5010f00c081c0c41b107a06001512003d010400e41d08a2240111010181000800450294100100e03240000c0a04a581c2c01c00380042c5180c0b0303440c0c544a2002e003040d0b40d804500d18201c1c074440d824030009107015010b240032611131000395541c40742840e9030401000703520380c45880721138114800c0b07000c0032026a0f0140044180304c02540c41d604451031601c003501040e52030042858007841682d00c0c0c0d924010703820903 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 564727095 1250 564725845 564725851
    0x515030c1009050a08010b01021e06070807140c030301080d050a0f260a02030717061521010e01080f011104030f24020903010b19030f05031c0c030b01090e 68
    0x540c55110030750388510440d090300850f441035510090895002a03882810740c08003050500a0f42070b01c13504414440c80d000b8043c220212601e50382e0000c0300042c0c0030f5201d51956074220038a8940a0a03100918880c02442e800401450b20103403c000010050780c50304004845000115007421420701c282c051002c2c04e203020b4a4080018003034984d25030300011b44043d60b4a065078228122081e9142481c164040094004071141400303e030400c5105558210b008403400e110380001403070701c20303224008940e40c01c284d00585809101f50b921642c9d8141c00b80d00303818001d4040d103101d9000490035850549024a03000c0c0d013201c044180d92500903000b0b011401d007402c540580750007010300c59074910586015500c161410340006245201c00c0380701c0801c144c09400410803490220000d22a03100c544041184c0c1049142030b072240c500c03006a040001401e007007070522001d8050004d0b2400c000111076041849034103500ca0001d030325500d4008403456a010310480c00418001e01c0c04103400c0303050059a00c0c1d030641c05 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 564728345 1250 564727095 564727099
    0xa11012a05132102090a060305030d09020d0f0506040b16080a0e030d060e060a17060103061817030402100509010206011a0c12120c0f090d0303180b0a0515030c 70
    0x200e5121212410b80c020004108409400b040d50b543c00c64242c2407485a124200d00c90ba401d140824821062030007024242c07078201c0f0141d460603c40c0c00c2a40000c200c007039000c0360001c09150f1040046400005c070400710a015402405640c0740a02e0f1014100400030714001c034081a90340d0310070f01c841d80044203640c001901400018800e8202d052a4914003555003691516400c2c040d01103102240707255828058941034510000c25a07d0f10303040a4181001c0070104802d40c488030041000c07030301c503422032142019043d8505640900796200c1000d0303480800d0000110100005c140011400c00c000c402c0041100ca113001418003044000003902c920042c810460b0340c0320070700d80c4014400600b000320380040000d04c0407900f06070b01c1400981100e4205454007048280340b0400140300001c00b0044075140c6508004061074030888601f003003000102002d041d01050b50f00c03080c1c8456003048070b03030580c0030901560581e0035900d03010280d0005d07514020030110140681a68044141c3c600007007018a003601 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 564729595 1250 564728345 564728347
    0x307061d0906010905030f1006080c0310020901090e090a02030613030e010806030f0d1115010b04032a03030c0b06100f03110c0a1b0b03040c090506010e04020a11012a05 74
    0x800340100d910700a560817495250081c03075000d0f08060710000d800e9000191000c42802102c1c0e560340010f465015400b00607406800c501424030310782000748d00500d54480c05042444a1648030311810048a500301c0300f201d140e9105108034402c5d450200320132039110084191222400005036001407400300710101c0c0c503042c800803201103006070ba4180400341d29468000101c2c2c0b0f4121150b400201504c000003a81c940c02d028419010410102c0c3c8100c0c0c90507240b00280003441c06e89140c2d9a04200c403242807140c0780c01803201620703e182c10308211040000314000d944405001c2c0244c00c203482902d90207007505100d520f4070340c680b00c42541c104410395140c500500700080c8030000c0c1a2003030094030618103040d03807602541c500740d010000c01501e8600c04075085001404d8480d100e202050842c442582d014112280701d41041018021540100e5440074040c90710341d100d00322103000f00d403c0c0d0700203c0134038022982400300044135110034865a40c685174554030906000e41710401c40500900d0840c000020080 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 564730845 1250 564729595 564729601
    0x603050c090f01120f02030a0b2d0d030c02091501110a0c06050d090210090f1a1b030903011e0c2a1704060216090c09060f0318050304050307061d09 65
    0x13001e6100f005104400c0a0542d503a20b410350a81c0000e02c070401e4064801d0352181c1042100c01c00e094900919014445450b19507410041c0c1049518050b002d412800c108281c0d542d02d0040c2c440b1042913010b204802c00c3c40c1d008058400025190820030030851280c0e9102c00765900200d1048040c40c2c040790000c0c01c000e60f0340c0080750302e01d034040d00ca00300021f90401110303c3e0900c0c0c510fa0211040e02191041e5035840003c540b209027007141d40000ca40b4400600c501070110344921140d9100c0c3e00624900c920842e0324050120003c2829600c405101c0008100f250240c180c12408500070511424184c1c034144144481205041c1030b101c84003600e5816541c00c003040d810030001d5a0602d1120130500407540c1c0d40f61680c40350f0081d41c5e421b00c41c400c0d0803c1072882100043c1c5500c03078059848244800e0b01d68500701400e251003143c9000103101658205901c40721a54810001c2850086006000c2d40c06035984034207240a00d1300d80826948428204000c082c580002c40300440098200c2c0074003101c81046c661 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 564732095 1250 564730845 564730877
    0x20d0b0a150b09010e060a02070e0c040305010e01271a06030c090c0a030b0103060e0f0709090f0b120d1d150a030516050307090306110f070c0603050c090f01 69
    0x88245a001035007071004901103124851100940b0f030342c503026030360485500822002d0001c00c0c020b503010000907901c040400d204081d0200c100d03e80c800304600e602c0d0300305543d86c1c55641c01d5400c104240c40d09a559824140440c001c103903241c1d00d4107545000c1166004000c1d5039403000031205995104c415400e4080030503016901840159510305006080f6221414174400c00360460380040e4901000c40d01e0302d03042c1e0100354002d0045204662041c0c1c103080995481344422b0400d014011f1040d01005203c0e0710200d02c50341d051180500764144040005900c2880b4003d1125068003d910301080f0b0344482d005561180c5e200c410704900c0312100407038883c440c00120100b02e0704109007560280d0070f0404903440c1e0300701e64980e102c17a03c81c80f1090900e90340304040140945d04c51009885000c00911983e00510108995402032030040e280c420034249414a50b45800e516504000d50454038420807250800080707a150142a030060401c801c01407400200100086080c8503090043c0d040c040719100040d142 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 564733345 1250 564732095 564732101
    0x15040203071d070e180c07030c050105090313090e030406110111030a1407031b03021b0d050325020d0c05011514030106061b14100207030206060f040207020d0b0a 71
    0x202400c00e20351000e488403010030261904101c2d40030b00043c140136101a44e030310b45005a208003400100d81c4d540c594503a002031001c564080c280c00d4040c810a88080030000d1800d01c03030644034420700340146865410682c00c012035064140e000b400d45609040014050a0b40401107404582290511441d1a0740c0c803100d46003d08507400c1c030b240c0d001e140401084014000c45c0c10595030003605545040c11a622340c0c0b004d90403101140400e1049010b0b1101c40c112103802035001304542e070440d149241c4504103600d001d0307150802804080700040c0340841401710b0502c40c01c10300c643e002c0c00320310b000c032058182d040003d543d40b070240589400c100107462100305008081d03002e4404501c090402e10310381600c6003141c9408502803420340b4001c2d031034010005a42c92007580e00701000745507a00000649000c42d1162120250071020700ca130340740207128600d00c91074481e10040c41c6007442900074201616003481003000810f10541c00714001d03801040f940300180d5030142c003212943c0e4031101c04041500c2c0c9290440007 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 564734595 1250 564733345 564733349
    0x12060b250f06050603010c0c0b01050906030f07060e2e08060d020d141c0c0605190c021e16090515030303091005010e040305120c0c10140a0204051507021813030e0306091504020307 79
    0x8fe4050007030b0109407940c1c8100000000f44080d540345c2403c0709003091401880441094074410301d1900c0010b8400d19218485860700403000406000301042c070ba400054005c00700003402c86010350380c42800b20b0028401d00c4080340c1840c49103140d45500d170071040040d0a2421208001b4911982d5800041115220f0210003049851000c02048220b54154010b982c0f107072003103102d07601550440000da01c5640c0014003101403107082c1e22840703041480c1844440248c40094500c103080b4105401d0244107450070000b941c814048a8002c01941540001a00460308103070807176802c0c40f040c0801c01020a40000445452088144400c503d650f10b0342c86c0c03201c2a0044940d142031034020070486200c0300c81181c000701442c45001207051b07555100c21001000720b204600c100ca07004a1a0900342c0060041c401c0038080c044c1c00a06860440314a900c4c481da5a0381048840c1940301610356622003e1680c000d2031402d54038000d500900290507c20384032035660701001e542c2000608203200250441d01c0911a03000 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 564735845 1250 564734595 564734623
    0x2071202010507140c010201061401090909020303040b0f030a0c05041d10031b1a0c0c0d050309060403080703120902062a0303010b03010612060b250f06050603010c0c0b0105090603 79
    0x10100001c941e91398580f01c00403403c80c010760070810041900307005014050440c0105071158180d00e4500132040d0054860b0007000ea074140800d001c00a11a4241c1005040005a40004c41d07907078507008180704202c44400380b17120204482440284110513a05042001060344d80c503a11045559803400244a070425400017803401850740072000c05660404080b03810742c0c0300b513441c441e542507040305440114011071415441a07032110811402905084200b54403860056081c2c0f860502c50b0800314010790b115500417a8800000034030681856408285411000e00141062010360341030b80000303d4501aa50340c0c06001c0d14000b03040710268401041d0b04400718203040c1525140d40c0d503a10488034a0f0400d11919020408400603098090418441d00c3c00f6588200140b9091120360b075a04041d1b50b400720503d042c0d00c503005100601003840c40c81810950b40c4514400304680c0303444400c1c1030a4501c01e141e50000d00180302d50420000782c080318030718155102980c01c0c2145640e4080024501250010190 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 564737095 1250 564735845 564735863
    0x319110f010c0302031806040f12050d0510150806090f150909030a0e0910031104060518070306090b0f090601030b1c0c06050315120f0f0304030b0105060a02071202010507 75
    0xb0050b4054015510031614108450420401101020303107a0504403402804081c00b00403550004800000e004242c0603145402810800c024011900312102030b100409150780c40001040361010780210070b103080d1900d10303000340203041441c04295180300140103500284210300000d040342110b8032041c50300b10001458044103040c801882910707648020815800284000c10f00e40784c2d4207142d140369000d04032950000b2031051071502c170a00701100422107035901a840700c0c2c00203004d0796000342490650442c403684800a060400e0041c0469441c0c0e88894190f03424200c1d0903840e40d44650700d880403104259440030721541c503103004a00900c02d04064980c043c1e88908883c01110701d213060107860070701c50740608a00079110b01c0152a00e010480d4151122041060a00c40c035040c2a100c40843c1000d10f801ca602a1b04820040c07400d0000c512642d40241d4408202042030282c1e03020043d005000588100c0d117410007200000303485500034000d400c110010140850110391065007110301264101c50340fa = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 564738345 1250 564737095 564737111
    0x40c050c0d05031608090c06040603150602010e0a200d050307170f09041a1f090f0b121b031305010e0105090c10020312010905040210020319110f01 65
    0x50910340001121803018410300c0c2104024078024011a03018408903210701500c07089a075000c4840e00b100500d01440c500130004821300380d03264100074101400c013585001c00c03205d8080100c020242c101d80e011000b1a0304001c0340044050000c00c009003516040131403150340055800c01051503009101995400190386042c2c402444800b00150100030b219111801d1100040c01000300d4034000c95a06450503201004003903802c1c54243e000000c45004030550b12440c1c441140003440000c1300034810400700c20010683c0c040709a001e880031020300409403404142c40d0a10f1520009409000000c3e0304c12115a000304034150480e848184007401d034508450f66920b0a580c0d1030386107c10a840840f20f560070b00c508400042011300940740305d01c1000005003401c01481e41042511403d1101e03003000c0d40010007488049024203d5854003805501c8004607203800c0c94414044942d91800c00002150002d001e00684114041c030103d2601d1410f2806900f0020144190b50030311412241c040041d42c603211003 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 564739595 1250 564738345 564738347
    0x9020a082809032c01080c07031407020130060807120303021308010c120605330d15051021090602040b1215030c03032221020a090c1d0609040c 63
    0x3031009135641c00c0e6910f504503100c1d090036040b46d000d4140010007081350041da01001d290303028090100c1c076005251050070582ca481980c00ca0300e10001d01501e0050114011200b4601c660041c03c006110700c0e4003c0840a140007000e24130780031400c50060030144c0004180b0750300c0c42c580c003829014241000081100094812025200d540c0e100e805586070b5092500000d4927142403829542e058051040721003914105103001c036402c1030b110701001c405a00034051424109500e11403140c058010300d4903800e40c01c0c00d01040240124005901c081000a548060086205011403040c2000c058079804279a8070064500b040c00b03409150488540c10030701082e000e0000c3c585180c542c2c05601c1c4409001da0280142050641b1100c483c0c1100e605036104114207040c070302c0d83c40c0e000442d040c40c0e64060440c082d2140c900055519030001044400100f80700d4510551411a01c0c50009256100041001420f103201c040c02503103540d211169000c20352803901e01d481d15a00121460701038010000c01402490400c = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 564740845 1250 564739595 564739667
    0xa090302220c08090a0609061d0303040b1302031905030409020a080703110918041a0415140112030c02010c08270409030207030213060b0409020a08280903 68
    0x4481c41c51030800d001c1e2030415000d40b000034020303d15071010b80301100407516084040c001100c4220742040d07071100300482a20941001d40b80c03411260015503500c2c1414140115141c40140c000c05801c102c2c140e21000503035000802640d000c4c3d59080200100c600e40c01c2480c154081d951100b04624000100200102d82c0a11041e01c1064280c03070810044d0a2800e22102d64002c620141d6040010360500c070045160300790941d68002d2182c0801c425203241d06440d0901100184c4044a8046c05082c1c0d0040c02c010a0007140c2e00c0341c105071000f030b41d9585861071080041a07010801790904c0240c2010a06591003002c44008080e04541e0603642d402400c03601c440c1d405400180b11601d1140b50350740c0c201602c0d1500a00340f0b519010b034000c109880c1180c08111410603030b5401510901d07503a41c80019444003503000f42c001030550210040c2c407220180005130034030307a006014800786505100707070f0000c09a0010300e52001c01c400c1840010f40130a1032a054a040b151140100b60012401e007071a038040007519 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 564742095 1250 564740845 564740899
    0x14100f09051b0102100b0d0602040f0513150e041e0507150201020f09010f170901020703030608010903080c0a050d06081c0810051009121a060307030809060a090302 72
    0x140403a2403491102c02166588001c0c2d048241c01a04001c3c11103050402a8000056504e00280b8440d0440c813550740c2c00c0101c2e481980000748542200700d040002c0d28220402d91803540c034051003403000013040003402c803100b030300c1b8014040760f0007402020a0501c041d88003400303032901c400c0e030454285c052a4140155031b48c0d801c1c07161000310418440d5904c56284103000b80c800303d0003103100c042e003812010001901d8081104807100d0070859541e4911851504008105001d08501400148c0c0d030b4005041c010160781c40764004041581c1040741c0040007a03403100820781c0c411000307036003262248921201103034148240c42403900e41e2403c0903030200301210007107903007601403401480140c040e40711580d0a40e0314400840b20103508000e800c0040045003000312040300c1d05242c1c1c1c03078051030a64031100410030320f44000105840070340e9003042c3c414900d480c6450094000c06c00320010300364203166682e0144144103030038441d402203074040b41030f01d0300c980203c07409409158000c002e500c54001c00903d1009a43d4a0 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 564743345 1250 564742095 564742103
    0x40f240213030506090309011b050f0a03080601030b0d030e090402120f0705090a06031a0406150821040f1707051005070323090105070521300414100f09 67
    0x4c480030814040d0000101c5015500c103131282030301d03251500c84400854102c41401d5403907002e00381d008045c3c8107041c030003d00102d2086c0c940030914105000011704680030110040c0c090000303280641d000c60b0b00010ba40b0200c42d000c03208641c45075600d00c041007100b00701082094051280d00104d00d403414010428200343c803002e4448010658500c0c0310407066409512024001038120040e0b085041044c0000650050107944e0104036003008055600c039800b8558400810758109603000d40e5180303038180601c00d03039905420300c860400d4141f411000c4c210000b03101c0c0c0c4e0500d0f00c4540110707205a4041c0010001400700404402c0c3c41c4402050181a030ba0144104600060b041e42d00480e034610826254039010301640d55a0b07091100f40c06c01512a076101041c1a1010300c1040f1070706c0591600340e40303101c80d002c40ba04102a20780c0039040d4040818a2411180d61200421103200c840e07130702d154801c10b58410f820000d00c0165000300100c49080000482eaa80012820a81d020341400320a07001802c1003442 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 564744595 1250 564743345 564743353
    0x901090c0c080a0c0318050609060c0114040b06180906071d0301020c010507091e0302010309020d050a030e0a0914061504090603031808010e060705090f0a09051b03040f2402130305 79
    0x103c0c8620350380c01103001f02030313000b00300344140c40b810f052590150107001050400001d076250349201d000c8c0b8400c1c0848003110416403000070041a400e215414083d5040c1c040d03100c40141c1450418141c440c20b00030002c4080111401240650300d1005034400308450018000b1541da048040d4203c2c00303001c0850318600031904128000864500048181c04045c813000d03441d41e507da007590300440140c0440001683e025000744003440115405024442c030191013921194510603004051060050351540141186c5107484840b50030114440c501c568845c4040340c40310074a102803001070180c4c1c000d94008080040c03030031001004254201c40744600140c17042c60350b0b6065555a03643c44d82a101702414041e80750300943c012034000c0e40920054030314400010318035040e0b07807407010106003194400d6100d20b800507112000e00494603805100e0181501c1c2c400520340c81c46c60a529400d030701500c4000d000702200060224040f2840801c2450300601125010030356541d0112401c8041c100e540f400140e4507401 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 564745845 1250 564744595 564744617
    0x30a142805060703020a030e0616180e04020f010c0b0a0e011b050a03050604180305031017031903140108030c07140d0b100801052d04020901090c0c080a0c03 69
    0x5000c10914620752040050200c3d582e0342c00100c0194005050700018962601000e9000b810284170b154482c212045162052482110707006081d000303d03540500c042c4a9100080c490069060000d640c40340e01a108076a0424110004a40c031003070b80e20004d01400c041500707200c1c851000307801841070000108024440000c2e1040d202c0300c825200c24000000c90400c1210682c0c941c001c0e000258800d038001e00005490704882030840001584040c22000103800000f003005403842014003001504140f0740b20804080704115403a603074801e0301800f1018020b00780400800501c01e4218068201008500001d956034545a00395a90014010710b0781c680100c0c8804554904440c000081d100780003480d209400e44942c44444540001518400c1030b801c20800114059809000320340c0a50050388040a01ca100c1da80d4800c1c69035031201800b050095a141400090b84d1040c554a040d61090b00c40090015104074042e52480c901000c020030b100000700703040700c00035000803601c40024069109c075405d10b6 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 564747095 1250 564745845 564745903
    0x60e27030c0d0f080714030601030b0a180b090a050702190602040503070e01080105070f0905040209010e0d1112030304110f01182d08030d020c03250614040b070806030a14 75
    0x114070075081b11045050000655030740c0301e40c005642809000d01b25a404603201c1200f08404042a43d8003041151541c0a10b41182000a202c90b408041080200031605109c82c1c002d448031980152810244c030b44482c840180045039040310001c040007011548602c1c2c0d2040390352140703e42403141030155480c1500203480c0f01c0c000e101013409030300c01c0c0d65689412810981004000e4110302040ca042115400c281d001c01e8407524200810540603006061000351440100705d01075000007101c1d040c0f03400a205200001e4017012251014040490f5005845019800101c9a5001944501d10140c52801c0700241a07207200c0000c0440d100d4420820f4807105d14116080c41c6410326100740b006640c820040d281400041e9406041691558410349246c048a40607840340280d032001002900031003000e8400c02c111f268800e40a0081c4218846c000741e180588507071301c585000a085a09020a210000c0c1003507809001d00080c003a44151886400c40c2c00c2500566030f20350f51003556948201c0c4c401001c1c090 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 564748201 1106 564747095 564747107
    0x604140c031e1e03030a1506211107150614010806130b10050c0601090603031d01021218040e060606030c0901050d060602010b04060e27030c0d0f0807 66
    0x10f4101b0042c1001201c401c4020046e6614100204000c8036401503407000d403140c1452641c1080d110111213003006010980f0f62154078040010b42c0504000c1801501061011103a0040042076201c04c14460080004140310780801d03055000921140741190079440551400340020a4000e41c03440466912202c1c40151008918049407044c03c0c29030401c071590040107084c00c24817200d40b031520054600000c03100c540030b49400c0300041c042c5070390082040014140c00c40742d0b003076130325000c01d03040050380305081c003c2d43d1166040000e03402069000040031030040c10020400307407035030300c4800c00d00403141d002c040440e05010040c803460744101c000348140402409941c0011070f000c2000d00070001103428a81200c0901100541801300c06400d99800d2400f5405e01d50a030f49000700c0002e0b1452030350003174001c000a0342c4144510410a96485521038141400e41d849a4403540c075840025079007 = true := by decide +kernel

theorem cover : BRFrame.Cov 564568345 564748201 := by
  have h0 := BRFrame.cov_init 564568345
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564568345 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564568345 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564568345 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564568345 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564568345 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564568345 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564568345 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564568345 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564568345 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564568345 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564568345 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564568345 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564568345 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564568345 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564568345 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564568345 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564568345 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564568345 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564568345 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564568345 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564568345 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564568345 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564568345 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564568345 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564568345 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564568345 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564568345 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564568345 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564568345 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564568345 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564568345 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564568345 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564568345 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564568345 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564568345 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564568345 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564568345 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564568345 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564568345 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564568345 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564568345 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564568345 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564568345 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564568345 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564568345 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564568345 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564568345 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564568345 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564568345 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564568345 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564568345 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564568345 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564568345 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564568345 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564568345 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564568345 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564568345 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564568345 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564568345 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564568345 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564568345 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564568345 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564568345 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564568345 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564568345 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564568345 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564568345 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564568345 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564568345 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564568345 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564568345 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564568345 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564568345 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564568345 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564568345 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564568345 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564568345 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564568345 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564568345 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564568345 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564568345 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564568345 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564568345 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564568345 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564568345 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564568345 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564568345 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564568345 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564568345 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564568345 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564568345 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564568345 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564568345 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564568345 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564568345 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564568345 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564568345 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564568345 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564568345 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564568345 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564568345 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564568345 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564568345 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564568345 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564568345 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564568345 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564568345 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564568345 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564568345 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564568345 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564568345 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564568345 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564568345 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564568345 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564568345 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564568345 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564568345 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564568345 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564568345 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564568345 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564568345 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564568345 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564568345 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564568345 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564568345 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564568345 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564568345 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564568345 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564568345 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564568345 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564568345 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564568345 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564568345 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564568345 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564568345 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564568345 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564568345 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564568345 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564568345 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564568345 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564568345 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564568345 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564568345 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564568345 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 564568345 ≤ n) (h2 : n < 564748201) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
