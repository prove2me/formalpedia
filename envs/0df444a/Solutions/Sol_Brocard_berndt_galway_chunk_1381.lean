-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1381
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T02:41:16.388852+00:00
-- url     : https://prove2.me/submissions/28ecf4ff-1814-4c15-9cac-873286497d3c

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 248201438 ≤ n < 248381294 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 248202688 1250 248201438 248201467
    0x70e040e0d0e03010605090c07020111030a050301060e18040c050307080f0304090221070f030c0c020d0201050904060b0c0f0d0503150105030c190c15150905100515040509010614 78
    0x116002c0e00f6645c1d8000010f100d90724456040e005031a18900c1076030f1102c2a0000500d0001e410100c14040c0d84200803800c2c490703030f001c02101e044522619201121025001c006808200c010081c01c4203082070b40305101c2402401c000203000c0301c40c118222485070f40da82d07070300340d0700c90200e06150b164580052004224280903900103020412400b85004542c4035034041c1c6400600c806d48076900011012134140b480780f81c15104528001019041011003801258000b4400368660303000241002070216002c2825191900541e02401d031a08085031030340d40c0320010360380d217154200c0007244500c00e404100654500a07000c49000e0710189001510001c84036005560301c0c2d0001e010300228000c00c05c0755480720049030302c02040d83c80540d036607076082d8200c07802d2003500010107a042c0d800951070020420145c2492030001d1084609407240850940d4509030030200d005503c0d40300f00d4005148003000941001c082008009a550131a00c00c22266200c0300100c5419040540e0313482a41810011150080e40c0c0 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 248203938 1250 248202688 248202707
    0x140d170c03060409120302070c05040501050f0f0f0418050d090b040902030c070804060f03050c0a1b050c0901080601031403031302010309060e031605060105030a1e0f050d08070e040e0d 81
    0x7a001040b084e015907111501e48030f03000c0010703001940c081001004c0101e030100150040008540500842d41050005110880240c2d0028499503920300e10f22a561105045040c40320002002004075064503407018125030035002085847d8050b10013605d01080c01949403000761410355498509140c24190854000e41c4007501079880a00140600800101d103040100040c00c00d6a45080702e003550303224040c0907184091f0050344c0070081442203000681c0d00c8030026000003210350102c507900b0014180141410b200300c5072240c2040802c0000308421500080107812240700703086c0341e1401ca0861404941300d000a40e441c0c0c0e00c040a014111016600c41d8100b02180e6002d0800018a0013104007100c1c503540c089404145c3ca000040303115024000140051801050240d0103000c00d0070465032420070b810009074501000200440b410b00c1408a000d010b015010703480011a0310070064800042c0c28107008460920014561122218141c2414080c00414002c024001c120b1000d6540b070035550801c0 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 248205188 1250 248203938 248203951
    0x150915042306070309260703060c0807030905060c070c05100c031e08150612070f0e0a0503030f1309020408030913090b06150903030d09060c080f04061116140d170c03 73
    0x1041c0d02d44261160060060380d0003188142c80014010a0210ac094a1a00c006040030103052a1105030000304401181d400e80c071100750186c1c1581d07400300d813801446119050b002142c04c40d0740c4118944d140d5030172400d005d0700d00703001e9255010310a110482003030001c00461504000510503002080ea034200d43c980c00d0300658001015a8104207900c0090404110704981210001d41148404d4620f41d400c20845421010107031810690382381080d010907030724401e000c2e0210301c132580054900c46040340b803a4408060590700200b5942c40e592800c03607a41d00d4000b404418400c1b00e0694001c0107040c103920503006002c2d403100e1b80702d400366106010013600340318030114420020350030801d90b10a0341e414401081515106c0c80e0015540545003881800c9071201e00c490300500c0504030038000501c008601c0d403648154031443c04100584140f04040702800344010300d150b40407208189404011244040801003160107040b0f801c1c2a1804ca000c031a1403410301001042181c0b07210101d0384515007240210750122 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 248206438 1250 248205188 248205239
    0x5010b04150c170304050601030c0605040305070b0a0309050a0f020f06030112030c11180a0615021011070204110c0c01020102030114040e071a070b070e150915042306070309 76
    0x2480e01481680c5603000305c0d81103456401150043c020818580c40f954042c003214903080d801c2a0543d278800e5500d60f4107000b40c002c110408903400010030300c80d4011044180d030180a5940c01402d41c070f084030b40b2940040d41244100c02e045900c02c13850410200b980e040700c400800384802034036a80c4040d140c80d01103d0094800201c5000402919211013880c403a2014410103a900307245007543d0920205c502c10307001407186198000402d0101c90b4002600440b14542132400280134059004042083c400d108009410504100070b844283c076451001d0403081d0380c58016580c010600a0049080344800d02406c02d2201c040c41000f0110f0602e9071020741c8110070f607801c9800c00790b26000d845000040100904c103d51a000803010200b0198481c001d40028450410031400c180800008441810540580510703440110740c3c1c01d40da50718107400300302da401c040507159517854541e00141030074507010061800d2410002c10996541c2840b02c00c4604850301503075041e0005090400e07051020700400515000403 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 248207688 1250 248206438 248206463
    0x2090604150e09270a0f0212150106030e010f060605030112020d0204060e060112051005010c0503090d08040801060b030402090f07050f0c01020a030b030606010807030e030d1d0105010b04150c 84
    0x5850780314045000340c8140c640d0500d043c01120341e08504c010314510900071504800b6049000030b00000031012030950440b14062928200044030f441d0195801c90072035810f00b248000294560142d202c0c440e4048418004c1c011903a6003142d80c0c0c195070a038030810000501c03c000400201038841c4061108905c001c0008490800c0b030740005c0c05840707694210071600c008034003e2084560b041000070724040620101440580307804c55400408499902c0740b6418480c07400204020080280b040b511900300040801c22065001d0404d40d5003a00b05000e03041e010b602c0c0ca1008100602c041c0284c07441168000d16103101c40d038451643d03418011000d002c3d40d0900009000d0309004c8200000500b038140c079100300040c2c42d071320814001400d40d4000d1811078000d4114406204159038403607019507004c0c0e00c40c14081303818590b40b510180343d0311400c1607c3c8001c0c4c2c0380c000700aa08002e4a0000f15032210710070002d0110341d0b01d580800000e07104510a45070300529080108104a008104a0000b1780c054644e14284 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 248208938 1250 248207688 248207717
    0x1140114010206040c05090c090d0b010501030605030d14090d120216090e031801300c0807050306041a061b06011403100b0427020307092c07050d080d0c030209060415 73
    0x4007030b041c0340112090320bc150f0040c8510b50345480b468005102c1280140070150483c080901644007100c120900e407540041c09008649611811640c000d501c0042d00d4400b00b041c1304002c0d1120041103105520342c080034000100d044840c01401309500e43c0c04c0c055032030007042c0c03219403581c5c0156001aa051040e0400f1598102070b888251400781000b040f1029401c00b41c1d41c01140c121003480c044030060014940510a619521106490340000c041e10000cd40d00c0e0010440029a00b09810301a44900005070f4100c00b2680c0204411002003010104c0d140303a601c0e01f80c42e03c000040f0492854059121030710407106002b55410607000c01002500000d8130304d039101104003404c0c1402000015010354008030703900b1420100600c03401040b03003c00400403017034520408076001e003101001400340006020707118603051060110078014000145410311588452a01103a26044400419041403400420001d0f56001e4021a0b49150300104414030b41410006208603580e54144030408000006146150 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 248210188 1250 248208938 248208949
    0x30303100605130906230103090b060f0f030303071205010503060609061e0d060207110301150b09030118050a05120310330806040c0c020d060b1201140114010206040c05090c09 77
    0x9444440e802c20013425030201001c00042c903c1c80d80794100f609d00441d03000031900c10000180c011604561046c200030000e40081c902400444c205945808000107010409410042000400c050b0030b4091100c0e030313a100d04240e1212000ca80c09500000c0020006205140490695402c10303546034080070801d4405000c200b46000440b800c44110350700242080c14011001100c00100d502140241714990000c016602080c1b41c0741f00c0d482c0e02600100d5036100e50740d401e41044c46c60820b481c0305103030114042d0038420381d01c41d00c03103506031014040d00702c41d04a055003070300c12a07200f40c206c010020345061800c11002100e0440c82500c00036500c114056540d045400c04501c0f4190b03941d5640d04080d070510341c00304011074803030340d20b00d0090000751058000181c85103040600c0c415000b40380080c00719500404680c410068403052011540707404900e03294a0641e40055051f07070341c188649141c0d51104d800690391806c05450240c90410383e00810031041c90600303c2e2690103111043c0351810501d0000100c0c1 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 248211438 1250 248210188 248210201
    0x3050f03040302090c03090a060c020c1305060909211b10050403030c0c02031506041116030207060c0201080f1b0403050c040c09031a0406020f0408010b0f0303031006051309 76
    0x1026420006041081d460104000394203d800499080e20f1400d00c062004c0e9a03040d4a0001406180c840c80603440c554000e1141e201c0e50072002e081c0803100c0b0301074920030700101012500c80c0d2103104450f003c100e5400002404080b003590101403490600c1c5400103e488540108004800c5c1c0401c44481d8510080103100b43c003034084410030702240a0526140c00740603107001c8a501402c0120998202c0c0140e0b90000340d4034481c420020311403180791a050040740203001180c52450402100052800d583c4d5080804928428000e0782640e000030b4072021f04503200380030703c00c0190008a0403400b15110304000304c0c9843e00000c1149070102c04505000b070900300c6812681c81510300b5000746c0354040d654101030264210030310039845d118840f41e080d07549510b00c8608800400004116843c001010000303140d0441d84406441410303152a6940e8800c1c59018185001165002e2441c400caa440c407818000240c07070052541a4281074164140142201d4075000b8108240c5812000b0f500001c072a0707801e1007441e = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 248212688 1250 248211438 248211463
    0x506070305071e0b0402041a01090303030e010b0d0f1109040f02041e0e0a0212060408122a0c0118200303070c08011506050f091003140709140a080709050c040305 71
    0x13400d00f4030702401044101d6011200341e45402d100b89555103041ea07805414002540c0d894100042d40100c2240d6032801400401003040d00a0016280c05050104d255003002c5030522034900100403030404402e004580700180d90007000b6074100507a61005133441e8000d241203401ca0003000b50001600d50942c000e440784440d4072501368000c04030280660030325880030640c0e00c501200504090425a450079814030a4640d21040148070380007040640c00c45004605086d0700124010385042101c0101083c0c0398049441843c0b158a018000540904074540c9400b8541d044802c2000b130350b02c4910710b440c2c45040c000400d9030501040100c2000180e50b04c0500e000380414100000e404058404c8004400010741c02610900c8414801c42420200c0d40d01211440241a5100c1c824281291820f4001e03002200b45e444020750301038100030201e82c0c41040c020403107210406404012091006110380300201f4050a0060f411282c07082c0300c1001c1c507801c400c1e00802070441c01c5260580da622518200743c1d040b00903 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 248213938 1250 248212688 248212703
    0x71d040908041514030408090d050f03040603060e2502070306020f0403050c180a0c09120302151501050f07020a03021201061805070e090403020f0304060e10030203010506070305071e 80
    0xd01082c0054050f1052808541c28080038602c180c07101c820190200900042190340002005100c98450142c1c1120300c0e68020101c1e030a821191007069201c3c0c03c00d020781c0e00040e141070701c0003071a00360040c200d6004050010b258107150800b800000858607444200006610809000200203036151004249030107c40c403480c1d0304ca0307007140b4103581030090180d14030740702d0852122166070164003034030240d42020000c0e00010325050002d00c152240f95450340315800014088440c4010715401040d86041303061580b1000c0b001d551500384407002c40c5074550020340003800a00060725420310300801420840d00052003940c0482e0f0340c0e0f00040000c4c103c1c00034001d89075103d05003080403002d04c03402c0c0c0100c0f107118941800a0300d0b0550f402440d104214442c03d2141c1d07601800328060500074003104d018001c00d44140ca544907243c2402403c91005004844c0c003c810403142500303828800c1c070a03072b4140c8400529991804a481d10101c0e4580c02c000e100b9030b041d0704403031100b4501a81d0f99401c41e201d42d101c3d808 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 248215188 1250 248213938 248213947
    0x305010204150311120403031103040302030702090c1c05090f010c0f08010909021039020306011502070b1804020d090213090c0b0a020304031e051b0603071d040908 72
    0x2403903030445001c007044042c513003070440d2180c0c4140140141c51020002e0007400b0f00c3c540e00d40c00c044020b4615280d0580c1003032000014401495404001040013900030b440006068075060351103207852150100104110040d0141c0c0780004410340c1007541c004e07120780100e540c0140303d2400300307085030b10103401e00000c07038010200a880207070848851350040078464020028580e080d00890000c51000e20510100000f0003400341c504510060540e0040001e80c1c15404485c40d12140007025400b1301209a100e4032440700002208106100c0c42c0c40403a00c0344d4058080c051424140501076001100d9081d0261074003070310015039889070701c00703000d41d62420000410540304078014443c945a1042c03040304558100300c100004502c41018540494110b011207a95418101c1c20172420b601458100804000c070010021441c3e1035102d500684081c081c3c42600c1c540100d503411a12403000b1426020b402120a10015041a0140c00b2a1494890ba002c1d0007120342c2c030100025080301d40502c805c942065001c82c = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 248216438 1250 248215188 248215199
    0x90509070c0506070c0804050d03030216140f03090f01030908070f060209131a150903070b0c12130b07480f03060504020d0206030702010b01081311150f040305010204 73
    0x300d0b0008135034200604692100d4595076030510a900400d805402444020f8080520039412208280c10381c120900800040389001f050030100c4c0300c01060244243c14000042010100c226203400f10018240500307078402c8001035001c3c1180358019144480c06018002c0420240d244034200d4a1282071300694884200c010007050741d00c107503d13500c03841e03290520070408240c0740403c06d440920200e0b91035402e0128054010028070410591030f4260281640008150351a00b000c0c0900010303807020740c2ca0f0903030700100c41d840502504402c5030160031032404c2040801288001441d03c280609001d940700c0d0015400c4110421412140703009000074a540540ca0b0444822501c5034114152028003581d40b400c2c5408000c0241c9020241c089a51140410115924003510409043e400b810560b228603020707202038000c2c40503070300d0390380400c110f100012510b00480208603402a84005c0e080320307500046041c01032042c000514850454020000c0c0c0c1100c14100d000343c4011485140090b82c0c650410 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 248217688 1250 248216438 248216443
    0x812070203191106270307050a1112060a020c0307080a0f020f03031e06040b031c0e040219030b010306050406121a0106091715010905040b1b0316090509070c05 70
    0x982c81c0c0100400003070480ba60803800316119030045450043ca520030100f000910001804083c05000c03e0303c00020480c0c100a008684850198095109214042c9080302800003c840d0241040c0c0107070030030000650440c050368042c1401c562541c007180c0c1807803416504c0d91200d074001901d03000840d002c910300b041c189a040103a4a000c050090180d03040d401c000d44000c9000d0740c02c0440170300910b03d02002071083d4440d603020114400004041f0707040821031075213010b40c0d8025201c10000041582006a0f51400d1034000c540c6400d8900f4049004005004021001845403202041c101500e60f80f00160301d40c1c5a0003608003400310328002002e680d1140c60207155011120b07514190001e56480104a00e036046840712049800b012414050400141800c40c10a40c042900140224048001081d81d806691205100d24410107141c1080d45400112205000303540f00c1090b043d103000c20005d007010790a04c0b00062070801c2c5e42042c5407001e4588001585034842120720364001f81400e400341c070038040304 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 248218938 1250 248217688 248217727
    0xa03060b0f01140406031805010c03020307021606021c030f05040507090c091a070302030d060b04090e01090f020f131a0103050f0708040b04110409050a050c0a0b0d090812070203 78
    0xf400c2401200c035004940b60b1090145220365414195640f110554aa440350186054141d10100820040c092043e000c1c000750800c0e20031038010320400f11170300340a1241c82940c100790fa00c03e4000300300d444d4212400d034003c1c0341d401e06c240c0100341d01c80d1640400c0103424022180140d11490107008040d0034500b682084408441c05142003000e001010400b1030041303241000f0300784d40405540d5681c0424207080c2c1c03030b40c4601101c4507006450b00c1400280c82114401810903101c2c601c20a000c250381401c0070314203032080004040d1154001410032001403034200e0fa6103196510181440701801c141050b81c80c100c4040e50b02e07003101100e45001030341880d0b0340340c8541903000c00c1150b1074031124140490001c2c00d90740028802400c0c040e040c0003080600c0750411588890a0009000b4820b24805250054441d13000c0f183c211824072801040c0401441c01000310f40c1903820f41c0310401d00304124040d80e00081c160701c69082d510300c541007081f42107034007804107203901c00d0103d82c00655440305000501c2a41014 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 248220188 1250 248218938 248218969
    0x110612240d0c0e130206030f0703020909040b01150c1203050702010b0418140a032102120106020a0b0a020901050a0c080c0124060201060e071d030613150608071208090a03060b 77
    0x940c0b44c940165a201300343c035004080344120f03504c1b558400d01c09030001e12420603202d5001849404010400c04d1704041c05041e0f41001d400081040c4c00820283d40202000c00014900c40c201031441140c07500c203a1090354051201d10010802e034560101007411078504e5502d048052044004043c14090811510394005088000070130300898961402850380354207504030600b0300c030880324240c8189195015145500010200e520155942d5400650344148201c0d04464804141e0001940603030544283c500d44841030f102d0605c1c0018040b4212040203138002e04480f02d840c1071001880c1c1c1034007441001104541d81042100203076041034a0003044a8a0b84204110380c1400003d00c003440c3e40c130000640029440c03d007040b01ca00140d40c5207100b140c5d40c00c01250988a081c081040ca504c801008240c018010280360f421841908803080558006009610351540080c8040010180d044015800d44c0d008403030660804c9035050004940c3c0000c0c0e8015100310b51124101d04003454a15100c001448 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 248221438 1250 248220188 248220211
    0x2030a02160602030f030c070611070201020c0f030c06070f151e05060102070501030f1e02030a0b030109020303031303090e09010903110a020a03140c0616110612240d0c0e 75
    0x42c90a03100a56a11a035241550110b4011020a10480000c429078250a80c00801808480001e00400c07400c0d0b0054070080c1d0041c8900c0a01c100c2c50305042c001980d0320701018000d000c1d280750000a01c102ca03072204104aa0f481003111540000c5001e0700c4c140102d03140c04000c04200c05010404c0c08070700d800c060001d41c07a03851900c003c2c400d841c0c2c0c0000c3c40200b100c5080c00d0110303081540d80d000c003000f041505906006092040180203151107179500851080780c010704100032400d5184181400c81e15601d40080d0598070030004960070300e44440000e003642d0722a103027502a207515036a40342d121302c0781038684048607919240c0e10020107812442d60901820804001c0842041c2900010700f494143c2c4009041a1100c18102014810502402560840250070942d40d5001c4150a015002c003000090b00c1c03c0303c80a0102003140f03814002c4840b241e0200e8680c546548901024002a02a04d056030740015410036041d4915206c1262820000d4000ca100700307405841c00c1c40d1401250310040164110b403 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 248222688 1250 248221438 248221483
    0x10180506060a0e06091909030206040b0112030e06090a03050d0206040b0121060b1c0c080c0409030c3f02010e07050604031401060b0708130801140a09030909050702030a02 75
    0xe580f000285580840119010b000503101e4401140203c1d02d1144071600142c02c1803003000615800250300d0340100e01c9002403144030713079903030000380c0d41c855204500500203080e00d582051705103000030152100031f4000345402242e680d0707961254900380c1c2010810000d43c04c02e030100024005c99200e02d50050100f4042196500c40450611401240804d801030405659400545003500d60040801c0100401c1c64042e494000a081c010686d0700c1e54031407904144140c021100250600740540d0320031076816200c0a00c401e41039a02c17500c0c1080305404005400217165904008000001115064030000d08000c10b1540007482009096800030400700249600070f0004210316204c4204031070880c2d4101c19500e040090104c0e8150141071326038003036583c029020030b0100921408a00900d0291500807010343c01541c3c82c0c81c05402d0b20b0b01b4811038a03c2e02205000210680629040f03040114402e18004009039141e0310601c0483d00c0c107a6200005900c0807400d40005ca4040180d024290342c001c6010010303 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 248223938 1250 248222688 248222699
    0x30106050117040302070f290a080c03040609050102030c07020310090203030f07050c060d0b0109120218130b100906050607172203060902040507170708070210180506060a 75
    0x240200d02401111020300c40c0c00082c2858400e106c00b1000d0910865030481165543d65200101c414686100d42401c084188581c0b404a90386c08603518841142c49502c03069481806450241c0c00060095940c030340c99980120020b0341c02e200844c40340720076200c1d00da00d51629005241c501507041400e03500c050300c2c1212a00c00341e5400807c0d50005035041c880d5960b07504080c03412034240b90345500c01d2508110f000c5070041840d06660032041c2402c034280c0c2d6100702159110b0b80c1c00384a2803118030194104030354051018030300c000481050380c001c00303480031861000c4c010f60741e4240600c000c56400b941040f007424103000841c041d010b60301c01400101d8845061a01c40c2e115040c540c0403110705600c03400b4001851580601d0380410100a1a0851048811155480c14004090710a09070b04902c11803508000400c2580a60b41c00301d80c3d20710346031510f11203a681c0c070016100c2e040080c112100f948236154940451854502035050583c00b01558168541020328143c1e1071b00d24054080340c401c0741040c03010b101 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 248225188 1250 248223938 248223947
    0x803190e150a020f0c120405010f09060905130b2d06070201120e07030c120b0c040308071101030b0a0f0e0a050c03130819020d0f020f03040b0d0e1e010b0301060501 72
    0x100074403210030060384c0759411020304146100f010180030f19400382d01080c5028051240150003212820780300c3c15001002100102d45d100b940d8050f90703000c54070a80e01400a42007243c0080040e00b10380c040060703083c08600014004400030040b402403000c030703c0141602c0c5061000b1414618105480960400e40d03d40d0000c0d2100c000d0880544941c0d036a03042c81e049a103030030440c040065400100d03080000d0f40b610030b00b26240814100c00d54450552001080c0804501c400319401c6070342125002d0b0418180355185013001b2451040d0b641050b03210ae000c40c2060380c811004100a25a04921041d010726099104203013085c001d1045000a2a00d03007080a0080b20344200c0758030891400d6508664803407485c100701d1500800014900c2c0385c0224003114040340d000165030a036519192145c0700369014000040b82c2e11545816684000e82061104000c0500100050310f0030311035010010940100240036903140c0a1840b04201e08246200068014a0000c0c49041048a01034009001d501c0c14440046c0 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 248226438 1250 248225188 248225191
    0x1060c02090402030703020a06050705060601080c04090218090901090b0c040501090e070c05030a05042102060d151208091003020f0a080a0e0a05010e191a090a0803190e15 75
    0x1c0c010300d450300c001011035400344070f10800b46500800007820b060b2035020052564120700e500301c489104410104107150b000380c12032131003051100901441d00e0700301082400a5041001401c5900d01840c0d140f510fa55150b81059106000303260000440c071803903080c59900c61308064000305911100b040180324690b8048080e0085c3c03452017128a000343c440c81400c8507a1200d00f040513055010100328140101d90241c020801c80e80f056040189900811074192a211800c09000354030081c00c000210320564150000601e48102c21a404000c03075a4814201c091100300804030307030003200028020000d20b000341c503102c1403000034a4114140303c00c503410380c5210320401c0b49080c00c2c807680c500021540c00b400d03004882c8000489068421581617490310764083e000d44d106254190040c0724940075140060f58207104690f82200310b04800003481d05645001050150401444e8003490349a4030110307000c2c400460003007030b413000050304c5201c684a00400b01c1d0314900a82526400a00c00308010040d1807034141d = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 248227688 1250 248226438 248226443
    0xd1e060e010e04080903030403081602100503072019052b0c03030908070f06060501090614300108030a020c180601031d0706090302040b09040201080c16060f0c031401060c 75
    0x1142c1d1808140002861f6000e982e000a084882c0001d0ae01e4102c41c0381301c01d8481c0c0c984242d130104508144858251180d00045400700d0008924440e0040400100b4201040509181e0b042c0c2c0e4440d082003a010540040c0c86100b5603540e4400c80d80101905c03020108128607010b40426070b00c10141d4013034001c00061844102404160725013802da000d0003418030450b00c0c5150702c01030304c800545061601001800702d40c425a4085030007050001a00707801403145600c00700c1e004044a02d003d207101602d58844811204424644000c94400b642d00c5c0e00c00e1b10030710301078408071000f5074684400c94402460507007420001c41c01412104542016485d04400068000307809080109031484840300380c1040415900c0801e81c01e118500300050340c0c58000c0180e000f6a4000e85003401b01c511003405110411a00303903070083c0011925000218201c441d200904254610117820342004096603e44074103450351240326145407035070340c4410340748103400d4030421010340c04030101501c1e29031500c41c020304488010300b0b01 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 248228938 1250 248227688 248227703
    0x50411040f141609060c0c0509130b070206060a09020336210a051e0f070302010f0e030306010f0c020301090c150206012607050402041511010b090115050d1e060e010e04 74
    0x6c4034204140008104050701010b00010254604090480c01c49003c0f0a016140302101d60b010403103852010550a204180103000500c8680c07406c80000c00940c8001c0038000783d41e1003142d15008004e02550316908554042641d0340818041e203503032504040320170366801440c1c003c03045034560710807642c01036803a03c11190070f1290f00e030210340a0480b0116003052803d500002c00054012900c1c1c0322102a00e8032a02030f6008116440021801004440d5107140801203603006000107005580300d015075101038100d0b442c2524104a6940c0400d094034001e960403140d92960240520040702c0c00c5200c1c40301c03d100c4e44000c0006515007001240200d5243d401c03101c64844c5001c40124540b82000340c480108005002155119945c82650505051110743d02c0002410f030041d50548010501500107800070041204115904e460f100c80c41c250910180c4d00b0500106000d000701c102c3c070a2240440381c10186421080c8030010002c490200c0300280c208402100444c40184910802c80303207280e501550200c074 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 248230188 1250 248228938 248228957
    0x150306040b03070602010e010c0203071a060a1701050a18110411040302061c0b061207081b0d0501210c0510091509080c04060302090604050411040f14160906 69
    0x4680540780840450790548546040014600d40c158019144104020000c001c4e400444100301e0b200e100c0e0b24000740c010b640300341901034090642850035400400051182091036a24400c46030946c0c0d10700e500d4507482e55914200000b1307400358000c005400c51102219000c010450740c5508624003d4088031307000e607039203d00400299005030111400380d90028859030315651000112603030706488172034060006040401e002c41a0506600366542e0800f2a40307901d5460303840100403160084010001d4101914000503a0081c0c0c8160703000b42843e0f554004007150645c10201c03485031001d0040d1041d011030100b0750190010410300074005090750011a010000c024800e5401c03160010070740c1118000012503640240350310307049104401100c1c07101061340d500c1c070104010001120401c1c407001e5081000500090481c2c41c05510040c1d100f803184020600c6500f428001c9400c075107031901740352102603541100c41c00550644d884140c0c072a80403090b1111410b00c801009000e0038640c4140402e014040a = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 248231438 1250 248230188 248230201
    0x60c04030827040f02040302100207150e0609040204060e040c05030c04170f0304080607080a09080306040209040608011a010e03060c07080d061a03061f090b0901030b03060f01031e021503 82
    0x1124414070140003803043c010801c5440304e040003940903120403172247c0c00d00040b594180340045858012150003450080714402c07264801e64180481070202d0b03902050400c082e0b02c01d41d0380c43c400382014224070344da1a0300700f6004505001c1101d00101c0301c801030102c18010008048504012982942e040c41301030034034212800100341c03502500c088140d0385400301040109001d003000840600c00d00c4640c2e100c0ea0252109906101180c01c010006402c1c40c108000045150510b0380007000103003406800001c00310340d1880542d007115176015a01d210001114083c24656a010b4a000c03803c29088002e01000d041c10606103155129001c03004140580c0031030400c1c1c1220055000000402c460f47c0052117440000041d01d500b5882242c0a9104509100c0440780c1d02d1108911005030f80c40079210304084c0c50400341c06000e141c02800050341055246c04440d10a40c505112040c02411540d911154550561800440c21110300e5800e01d12000050034010140e0703100c0090141d043c2c40d25050a50340c0e10b03103d = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 248232688 1250 248231438 248231497
    0x4090905030409091b09050601020604030c03110f1b0111070504050c07061104030317040308060913081603110a05150604020d140703060503010603020604090c020c120a0302060c040308 81
    0x207611503c01d403850180800140419a00a030b079500540d007060f2000c00c0e4071040c40c84100c030b405441e0940180d11440000300064051204040c08500a0602c0e242e000030310000185040c0b0300008048144d0411606a00641c80b55851045000b400f400d001c49440201007949945128902c0784521454407100450092040c90f41210041d0750803120a0005100382800f41d542e81e4081e20044000a00e0000700345105025003605500480e41a510f4112a4031008200500404003270060084451001c21b188000b0306100c0041000c4a1740e80682c419200403414060700c0c10307030300c0042111290803041380500018030129540604181e20001008581c42d402c01081c02402810382480705649001d43d600c20394040b04c0105440780c0302e545e4007441801e884405060a90714035100007500b2442c14081440b1013500d0f6084001480707a5031040303c4030703110200001003032444000c40b4420a81c110b440c0d201c05041d03042c05955403140801c05050b207428134660b81c18515102d8100d203200ca0008681103845108080b = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 248233938 1250 248232688 248232697
    0x6020a06180c030302030406020c09010e130204022104120203030c0406030c0905040c08041104180807060219080a0533030a05030a03060806061e011211040b0d0f0b03030409090503 79
    0x200300c08008868a13807901950700d9005025072005481011094003407480c0130b40410b07060380c404d0803103903105443e504601a001544540200c0c1d00035020312006200b200d04080d980007160840481a019041504000903c008600d040701c0c1150010420401c1c0207105034100e4040354604d20740002ca050010808403102403194201961040c184440c0a40c1d096111500d540039a01458680651003000c00411007124210030b40070301107140413810a8041058030028110b00780c098480585810b0b07500014007111030400e0607620100e02c0315800e204819206102e01e55100f00c41d40740207004000407800c40303014405180c251b060a800c440048156030b032024000f404001e580481203c0e00c0341c03940c8501030042e000e41e000311480c9218200000d040c51911031440c5079280b0280c8140c0c16142e030644011a1000104200501542d4130703007108003030494810009000800103401103c0d1140741c80d86416080d1881030814200040c18111080c81d0f40d50080100c1e0210b0b9064040054900341a1400c41e045008 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 248235188 1250 248233938 248233943
    0x2060412020a050625020c0f0d030c170307121a100507051e010b010e060304030305040503070b010806150321210a0905070b0301180506011e09060e03030406020a0618 73
    0x34442400030701c1e0210303450101c5c0080c00d035128034625109018100d1741c0f050700d0b204c40d41e440f1440c0365800c00345007020305440c00b900d4080d181c03100c80e6508075100c500a85030104400c5214250000030402019445450f4881aa01e480010300c4038164051441010b0300c500010680b2070f00b00040c0342044940103030100e074581503010080c7e4141c492250358001b1081c89540410000f5400c0c5000000f16610980344900c8244000344081d0454960f03460403802400020400c03101c0d403008002e0400031560340c0004034003d04581c0000d182c94940013031091480341910b03280500030b07803100342c00e02000e00c2c42c0440000341200c42c4284580320010000d0038840360120880c003a0084442c401848036080650704450107090046046441c1555100542c0000b03100900c102580d41c0c0d1000c605844c000360640000d1f0700481305140c40d002c1007518810705001d180c14080e0000c0403034030300d000820049030803001090304648110081d5044c5882c00c14065111609480c00412069551030905520100080520f02164 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 248236438 1250 248235188 248235193
    0x80406140d0f05060f19090b01140c031e030402090f07020c0a031515081b0604091107060605030606181f0308120a0501030f03030b03070e09010603150b0102060412020a05 75
    0x8444084610007040250744c03950080965100c1c00105041c000d584c0d0b00f601312000c18a19485150590420041c0405c07043e840c108804204002c1c59011200e000d08900386100002e107a0300c90500c4000010401203202010301c188080c41040f025035106015158022088180c3c0d246540d100307207080f420800030b207036000c2d07101249040201c07c1c0300c1c483d010084100c4a4503000c00c0b10200c180030b0314402941910074808158026072130a643c400780000e04820711030014120301e0905071107010000944840a060b501042c030041105800c1c41454019000140400d030094601810304e040480c00344003804418000c0d200344000452035410f00c501c03c1c01d0382124200300714062103840303242100882c1d004055082511680d00c0100c3c1008205203d40c50403a0b80c001654095507100d65020740180a030b15405a6141c041c00500103021102248190b114240f1400000303102421843d141e40c5450f40c811170f8014461429040012590f00028203940054002b60210258100c1082c201d180c124403500081c51030 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 248237688 1250 248236438 248236451
    0x18030a020106051503060f0630091603020109060c230303060a09060b090409031209060b13091a10120309050108090a02150903071a03061c080406140d 66
    0x40d5042d4008426100704a51038800d048040903418558041564401d92100304200c021358070340fa084000b041040d0040c502500190028001c0c0c80754100c0300386031050120813800401c40380e00da00f8010192152030406001c040c060568000030b0144201c0e0040c88140050112464180b01409210700f50303011080303120880142040d54129100e400980d6801c0c0201d600c00c0c00030070004054080e8a00340c41c014541c042c1400c180400304006840c16400950600120410106c0142524040c44141c40c0c0901404126640b2440030311005082d0002c200d82c1c2030349048424000542094000c83d2942000b0305141100d4948100241f54004254081582c5c04101c52025082580040c1900200c0780f00340c03518501507540414a5485038404a4025480010404018500c1003104080c2001d40700250071940c541e80c41f0080d540f206085003c88500402c408001c00c6031303600d007010280401056580c42c402c100d00d4503540d140380502560041605200c8107803580c103a90310414040d19a80d10380c2070028000c2 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 248238938 1250 248237688 248237707
    0x804090207170708030c0901090e0f04052e0b0a1d0603070e15010f021903090e0a15030311030f0301090c110102030903070204091406160807020a0f06051803 69
    0x80d03019110854184401c0202c10410741503030000d903038640b6080000d0302d01d150b5665268400580c040221581409207800b40402c400d00600c403554400c0075688542082410031342440c42c505017815100711920070402185070380f1031010100740e41d8822207034400031074460300c0c6000164506149403c56140b5a6400d40085046aa050b400e81d0003240c040c0c1c15104065181c96074940c4c82082141d00e902e050002082c0350703030103500c40c1100c10622203091068690780d0740044035000500c1d003082002e03070001c4c1e230900b07050140d06040020540c00c0091020100864614294040c3d04107400d448040c2c00c4c48290b0403e03d201c99401d00441b6025420341076001d0f903940e10340d044900100301d9008030100041e0400200800c213030701442102d000b00c90400040d4100300300d0381d0030803024000c5000112a002d00a20080c05890810002207000c0d40c031420040ca541d8074101001443c02400404040c1150301c8810140041030311030720610000d9400500104403a9561b050001d10200301c62210002480005a403504 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 248240188 1250 248238938 248238941
    0x409020a0804120207140d06110342011805030a150f051b0c010603080a0c03270b0313170d0b090405060106031806140f06010827010603080409 63
    0x1180740303d0580808420400b040c1281d98055038020901c00140c1819210b449207000f03140e040041d4813926005c0740b845a03074002c0480b00e400647e580c5a0041d50054004007040313140c2c003035900b0380032606441280440d0710f583c0f0f006444002d805103414404401c04055030403411a141c03071b000c1c10300034048805001140ca05a585c0301d0841d4501140c1d5440d081303080d0781540560050a014030410074078202000c1402003071210503480006e801046668451000000401180103403580c1c4640f500e841914948a0401426100d000c02541c94001071491117514075001400c004030682d000584940e4481c0d1b56500c95850031000c61002a044191042180d802c440381d2000030084411800c505100000703c00c0c0a20a41d1401910010881d0b00080014003055110382c1c030a81d40302100314000080200c1c5a19030100f00d400402c1f12100001e019010060b62410602290742c21603070130b10b440f0000b45000c052020118011100f600c400e5482920503258109094019001454000c0061135569554400420 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 248241438 1250 248240188 248240191
    0x810080105070c030306060315030204020c07080118050d0903030212070f1410110414060307020a0206070b010905130302030307111606020609061f090b0a0e180606190311060409020a08 81
    0xd00080c200200071402a200e409906109d07040010002461410350b42084041c1d00040009980d91180350340004610340309001e5100d151300d010360b03d050a00102e040840c181003001c8205018850107000801c00680d0004400885101c846030f01c84d103a40d5103190265800300c03401c03009883d40c28a90000240000080382c01d94030424000c80400c881ea0700200101102d024605c210a170341d0a6061428410341071030001144d108513544151029280e0b558000703207654210740700584105040724014002c000b141e02c140d40e0000300d0f40c0c103008528006503074000e50340d1100030301e030380204083c8400c00b40c41c80320104140c80100307000c5805180c04039200e100080d80c1d540d00320f0307003c0d40310320a22020603100151a450708090259104e480c1c41c4090511024001070800903424070b4000302c094900099042e038810540c1d005680c805410b14110345025100c80c0382c0000504007620415905003014041c8104659440407039030b10580ca40100700c44100042c2e881e010f541d01240b00b1500001d0024881c61340101400e = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 248242688 1250 248241438 248241443
    0x4030c0e0907060801080a020114090a0f060f020304140d050f0d180b0a050a08071e0807030f06050a06030b120106080f06090f03030f0a020c070e0a0b090c0a0810080105070c 76
    0x54490b07540e10103045905000c2803044a0403a040700320031030055442075019007842d864101c3e14516024006002c980c1194403640400100d0031701d42000c1c8105548900f560341141035910096084c03030b04141c4080010103000c050039100c0d0070f1a20a8108020040c01303d845a2980c6405a51800d0364240c0040c0c407928a07038440940144017044086400f0000c8402d6841d02202503031498202100090103840002006d03107100b09012503110400454900882202c0c4a900303d0b40e41c0c105641003554000c0c00755545c03200da010150303081030740900c66a102c44240108684141ca001700384900e100380071481841a01001868550a010020640810025240c40100c1c441030440d21207a54804031551181c12203100040a03030810400f15803400002d080ca527800c095038103801840c1c000c2111402c1e16281141d440103080c91030a404000084041c3e11075840390100581d0352001500c0c01800448840c0b00d1942c1407800e000442001c07070401c54450f4070280127400c1000c000c018606021001030004414840c04 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 248243938 1250 248242688 248242693
    0x6030804090c02030c03180d0b01150801050f0f061309060e04120507050c01030504080c1c0801080106080613030c05030f0306040c050a1b06150b0318070503100905010204030c0e09 79
    0xb0100394400001c40d1a00010300e00518200a4480341808039003031010718441d030103a42d00200e00081800540510300a007070031900d9601e0030b0b508030000f07054004140c0c40248030300b054002ea8860b035155002aaa00303a00c00322852640c032842056105841c2c0303c43c1d0090002140b50031404519480b0450300c0c14040c6001380c103070a0740300c05007810844041c45003120003443c4d0b41001c0405c03010765009403c06074101c1d1103040218141403100814602c0d051441c0354201040c1d483d240240403d607080040103015000c480000d100703103401c0440041daa6480a008841e80e10380c400100d1050522030380218680c240d000013600d50319202900181c4603070704140c0b03200c0d1140d4602860b00620340c1c0071f0001c40310054900e4541e040d80400c45440f035122390f54003120a488144c5c444103407950030030704c072124000275080000b01607403282000041b030b001c8030a20312041c881541c00780e44207000f10b580006071008000c0070500045170203544c0e840d02c0c03800f81c0110350005008440314003001c1203542544000c103200fa02039508 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 248245188 1250 248243938 248243951
    0x150f12020a050906061b01060504090b06040605030613032102040b04061403040b04120c021f17042a050616060b1807052a0d110c01080604020c0109060603080409 71
    0x811140200c107640017640040b08100c101024010180c0581001d02da00000160095403580440d06661510008a56145104080100500d001d1146101800f07042d0000d1003030380b6003403683c1460801c5440c0080c1c00d20040352016840318613074490b1080c5091980100395241d6503a01d0084005400900900000c140b004101000032140c59080d17034480d503003002c028803094540381c9585202c0134502d040e4808000986035044050303200c0d00c5a10468000701010a068000030700070003030803034025500c0150701650a106110202e100c909001542090384034400d0560408035040101010603980401c0d046040414140c1380b0900c3d045625000340e004034424000440c1000401c10320740c00700c20202c0d800740c440b040070074505881800074102c40480c8511050000d4082248c141031410701d4521207103164048003003050601d500c68004405900c0060041948232580c00c00a812140e0082c0800e000d0340d408102241c10090075000707900c08580080c004c0103060f0f02e0b0300785420107910070300502c00750724200740b0b = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 248246438 1250 248245188 248245199
    0x15070302120a0203040e04080d09080310060503041a1305100b040b0f0307030303020a05040504021303060b0306100e0408040b120601201905010e03031306060e060603040303150f12020a 81
    0x50880b02c0340c0d516075000c0d514081c2040e46401c02e00001130000e40b0091410310699600402501c100b107901d030302441c043d54403843d0249181514214a40054040040c1401440001011032202c0360604420035039600441c1d0320032103100710b043c500c0b400c058405d10130307041185001d5031540d20030180030000b554144040440001801030342d800c01010f80340c06030301c80c500400210344a5406000007103403e00d0b140b032901c0e5032031001070181c0e006200030203a80340c4841010000c2085510940c19940b00a0780a4444c0b4900030b0f680c24583d110394807942560841000003c1e0410030103404480c00390144000f41600c600c1d1100b1001d00394242100d1140c04501d080e00440401d020101a442200d00240001e040000140c003440f00103140507101100c2c19074a07540d014010f000140041d511601000c4811050021039003001c1c0140c2d41c079a8022240d00d0f85050a00c8580e44881088a41c00307601820081000403440c0060701000169501c00c0041c2c025a200206911095406294241d0f0080f00d624070001d8a0782d = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 248247688 1250 248246438 248246473
    0x120d11030c0a03110d0906150f0806040b06040f020d240807050f150a0c0c0b03040b010e091c0504090e0102030105030715032705011b05090d060b15070302 68
    0x20781d000704101c0340900422642ca4400e030440038080b0b040b00f145038141000c1660320000c1d200b001d0030466185444003445040030030501007a0000b04040380310800385a00d042c20352500e0305000703070000c0c02014011001030700907100c1c0e070810410010495811036858001806c04001043c010303080c90341048404600c5001d613410b1801d058165959400070300301071032910041016a07091007504580001d500d60301e841001e454000641220703c116152104920b0031442c0010b07610042da045084121000d00500000c24101240181540c1440804c28803175140c0744d261038580742d100d030740081e00306e100360407519121176100d000781c4111003000d0b1060200c40d424000c4ca500f81d01007401a6174069202c41c004001d4892100c1c04044144080d06000620703040c80d12003210400c02e07083c1a0340c0c8054030048420100b03c0c0c244a0b807903a104248031500984070704260001d2403441036048403446031207c034030b42e4024416580e001d824400b400910100d86c3c264010340c3d02c040c0d5000714100b41c01602605280b9411000c08 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 248248938 1250 248247688 248247691
    0x503010b01020606010f2007030317010b16030e0f030106180b0307122a060201021911060703020912060a0f060e010b030a050c0408030d061e030305030f0603030c120d1103 75
    0x58440b80c6d00b900410314120341c045e2010300d5005114600917043c49085005211103406036005c1d0351800700c904950708200c0480103041c1d002c855403500c204012082c0492051001d0100d40d814984583e06032541c8000650318040761000c154035510b49640018079100301080305110505651017030000003440c0040580b258090f210340030340b40c5402c040050000d02c01d5134446480c018541255500c0c440b9840740e10700c5c020a560007401c0982e60004054100c035601502000e02c0b40312a01d4030b45001005010000d448010181c11034003415000b060981e100e81d101000107040d40b004508071901841c003c003504001d800c0c80d44184038254980ba402061a102d02d81000f41a12070000220307103191a0515060000c01c4028130380e004100c814040441d80c000b0a200402d4010020180824141c0c00d108580c042e118100317540700c106c540325000410002e9003240c2504c0d4460030403101203115943e0900844d0442c0309001c0d09e00514090550f04a000e08202c401800e01c0c000c0c408401c01000d0018070098009100 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 248250188 1250 248248938 248248951
    0x9020906070816080d0501050f04050106201e0a1703060d1113140711010e07030f060b03010c0c060507030b0f09040f050d02030c010b030109020d0b0a091b0503010b010206 75
    0x108111501c0400c000038000e01d42c0070910800620b04030041d803541e1a068011140c00e60f203541d222001004107151076840511840800c64080007954500003000d0142da411400b0b00000c1c020000040203058000e1007281803941c0b528680200106010b5448c0391500d5410a04844c10200d031441c000c0c000c62050706592103441c01038100780d20212075407036015104005c5000f184e88240c480329643d55070f0750703603000b10315800c4811601c00c0a9400c250102803e400a60113111060341c0c900407031a00031100001d08202200d4100030f0035040a815814041c01070496080740c0e40d09582419036075020144e100f000e0740440c40c041c100400650f116070404500380c03520f241c0c0103644407100442c056a64605040003e801034410100744d0b0b042403943d0350f034904280040c07009a01580003c00c03401039803002070050404501c0c04130002c102c6900b042d800100010070350171000c2c040f406084002035000000b58081d0203826040032013424844500d403070041c0b10178001d0007003900035400c04813804542d5000045a900408 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 248251438 1250 248250188 248250199
    0x912030e030d170117190f15020702031009020f0f0301020712050304140102071113090f0318060c1502070302070b03130c060c0201080f0613090804090c08040b040b060409080c0610090209 82
    0x3610340302902c05c45080151b00b5600340e15074800402c00078031007208809544420900142e00d40c07203c2c3c0101030501c0b402c4880c0c0d03150344d4184060b04005076a158844010f400c022100d03108101d5078040800c0c020f00071a03600820b6650303a00c0c5090b210a4021000c0c52049100d0b04042008015200303200c0e09034010441c1c000c040758100078054003a03207489403403032640081a40d00000e0041490b00d990003206001c100540126214020390b40c0c2c05203402c00b0680c044c001c04e0816070100c0301c80d507030f81d180d0415525180c41350304e50740801c0c03003001c15200780319090042c150f15400a4490402d50149a1310000c03101c8101c4550743c19920000b203990040d10f0150026070140c440d1000c81d030f108207007420143c100401c0603500c11f07010000c09001e032144c0e01c650480a4005c1e601d1584540c10111500100c41c524a610710a00580500700000030324074250b11b651165001c0108203d945912001c5400780800c01da004184440205071400c2c1030000203100d1748100d02450040e400140d0310721180d000c0b03115262031700d0b4026 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 248252688 1250 248251438 248251453
    0x151017060c031b0307030b010305060f03031603090e010303182102101b030c0203060f01180903020118140c060405030c0f0d020a08030d0509010b010912030e030d170117 74
    0xd050340000d564070800c1528000f5100150b6100000d15600c01c40b120340c0031a5842c00140e0741c959161107540d501c070070103540150b0581500310000f0364900528141c03001540e4008011000c05100d55540401044042924003455841c1c3c50b0240040007015604144417842d034100094002c00da50601d400866200e0001074003000d0b6400348040c1782300c02c1c40c0440c02e109400043c00050302c0070074041000c0c14080d036a0a41f00544500c10141452809003140d6009840440140849003070003402c00c50012004000088911540c03400380c2c05440c0b81d01c90784020200c12044101408010b2101c03480308051082501c50000d40c0008100031070003140222501507001e04a1003045040c12892101550001403143c801c0510950009242c0c2d0300d9a0440740081c0c1010505580b0010303140500f50304500c500000b442100f5807900000c00012783c512489103400b590390410360906000d2000355110384800f6082c0c0d440240c004401a125a802c903840340c8400c00c142d000007404000141041442c01712840c05015203 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 248253938 1250 248252688 248252701
    0x603050f07090b070303060e0a1a0904030e09100b03040f020120030306040e07170d12060b18010314090d170103020916051c051e1e090f15101706 64
    0x64104c10004c405046d6680c3d004200303840615003491050310100d20118030390341c40081002005c1455150503000d034103840c1c14080041d0b0401e0b528038000c0360944076107006958100312a10144801d501c170403d00c00c400010b120500410990300e090b10340c001c2e241d0092828043c2c9591030410840b0001c054290070500c00f00300c443c5041d0300640e40c030240080480301455201c40080312b60885001c20201c8e5980161001600c2513009081e2000c4400d406404009061414924041134440c95161f042032940500c0302200e00d0f80030358008a02c1010403045007507280f824041031a0f5600040c9809004244203604219121420035078050680758050708021140c2c071040c9800071114a400540b07000d1007428088201c02c8138942ca181c00c113440700103401107040e00705600c1001c0f120811180344a005a041010401c0784041c1d642c0030075180080c820041815035a05004504140380000080010300516108441c21581490740324059803c03180c00c2d25030140d42d04c1c0c0905200c92081c1c0c03022030503003051000410 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 248255188 1250 248253938 248253959
    0xe0c16150b040e0a0c0b0f0703030c1e080109050603070b0f0304170a0903061b0c1412160506010603181101051309021c0204060e060904240603050f0709 67
    0x40c024968402003264580540001c081d58a4500c6048943d0700c0140c0540501501c1410712000340343d0100610310f0000690818a1a032084400c050305140d15180e000c000144141d84070070300d00710080c003641d400001301140188428001e12031401d01c0f504040c04140c0d8ad2a01040300011603500c40046483c141d1010080304003504024400d95009140c00f15414007100044000c01c14141d442d40d030154650700354039282c4c085030030900302a41500c0390402000440303034111031040410ba8212424000402081c4801c81c500f80c20480c8001000c2c901044134605c5e1103600035580c00c202d200d101510580c1e0380350101101211a09480506400c03582d59505000c10164000c199049406241640c138240211403a076201021b660710400c0036960000c0c0000b0220349200020042c402e6518040d45010300c4c00c0e000608440da0a14182e00c50703100001c12004a5a866008008007081241505421018411189441c2030944030ba00c0119007004005846020b62010f100e10078500c0342c5484004c0b6041035203c40 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 248256438 1250 248255188 248255213
    0x14040b0f0904140d02061905041506060215010812160503091c0b070f1d13061205160f030f03021f1505010203070c090908160503040e0c16 61
    0x103400c0308504400354400c1d2241c02910b84554040c884402c2d50b0030b02400032a14100704001840c0464100c8000c1c4021500d00c80182e4546111055020a1035196424101b807030803146030300c00f40418504400014000d80206d1400414081d1000c030319500d0f0784c1c400c1140d40700c824070b44005c02d1005040100c0040d4405442c0420b00741c41c040d200302c07810b04c50f0080104040341c0c0000042400c1d11021503c43c0c040100c202059680415945081188003106403c0038010204420302c2141c1140310002119960705c0d0f80d200d01048074240350007480034039640c0c003907060100c00c110025540b45c001d82c00c4c11040d01308442d0b40705084841518807813030010325544031201c640300c1c003d5045046001c0c4c000342d044001c6e000dc42074201460001c00c0042c5101c001d5054903c0350050b60300403419034106200b584045145a4003100840c1c4698002046520079460f2280251284010580b180a13100c0740714400d0200002c081c006980e81c5900384002521400c1020013680221181c0c140c2d000701c12601c079400191000d6096 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 248257688 1250 248256438 248256461
    0xf01050f070822060f023f030a050105010c1505040206070b100906060314180708070f0602100227060f0403080d0b0402070302120a0504031e060f061404 67
    0x114107090385542c40540d10f50000804841c118000e030b02c1a8000b00c610b101080040200b4144214160f840e98000394035a070a51500c500c5240f05034400c2449082089000042c424520101900c2654401040c400700e03002512400c41c01e0b40ba0000119503940200c0f550f03d00070b038010007072518641c040001180906801001203070041e50a0201d500021810301e03500b401900c0581034001440d04000501003203c0c250351204040500300309990440c118000300c00750700116610b0100000d80110100b103403600c001030380701e403034180315000d80080c052030100921070a0301c41c194252200544d0320120b1030b080c0d00800d10b841115004075200d1a0b66031a10404203c00c07000e003e4021410281d0820840300300750880c0c4d00c142c07082c6500084540d200c201a201e9003030b49500403642142010310322380b4025500e5207805216084c3c6080022038005403070051060301c0081d640506088421142d04104004c42095418100d030014240012004160382c18000c2038140d4118160000890460300200b201425014040 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 248258938 1250 248257688 248257717
    0x61809030f0f090405220605060f100c030e09010303080f0601020a1704030b100b120c1201062d020d1b0c0603050f0a06060c020f01020c0a03050609010c09050f0105 72
    0x1481044103030700c0041d01c0003140415515446001000621003555070042900408091a91900d034030a4100d004401100d030700a900002c0325919100414144040305401d1a80420741036624600e551740300c08010f501c1440b036902c0f0380780c40340d01105000200e4001e0000901060300750001680b00d440c50031110764005014412200300044903100c001d0030111806680151110001f014403c1c0b18414000c0d5400401c140c680b03001107850706a0999040c0640c1000d400a9078080b804070b00c202c0000d100f07a40c0365900183c4030300c0306565100409054032050948125a4048003501c1e883c405001e10404104919140c02400394450002c004a5410110401c440c4600c1d2826202c5404035640307060200c094400c0d500d00050034180385160089140300201000d10042c10b218003442240e0744002c0d68100240c1c15140b00c0c0500d48540300607818082d01c480e1490b00003540035000800e00c000018601d02070000d1000030030907000c0c504400c541c50203da0040c0d540055110060080c00d51048008101902d0003510 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 248260188 1250 248258938 248258947
    0x21317030d0f09140d020f03190819020c070e070513140d061a010201060803041508150d030f0f030c1b05012c010b0105032a0c010204090504060c0806180903 69
    0x6139050b000c5604030440040e44d00ca4409100319580400c5040042110880154209115000b000d403201d08110030050802200720042031101c070301c403582d4032001882c07040155240c0d184420001e948d060f441c40b50b86034010080000c03d6403640101e00f21003540f103e0307048078000f0340e0404198000b8480701041041c2c03c00500c5a02c0d801082580c8074800c03c402d1030030101301e40e207400e1200090031344505800030b0125400c01c00041000c500b80c0400e4801c0c504060500444a41d544510005401d1440c0c102c80d4002b401c82080c0000c2541c132030380d1002440825166900c0d210829801101100c145e59200008105600b044111031032030b54842080440c031600010401441b40c40c4440030008005410f105107280c09400405a44001c0c000c1c9140340000313113021800c40ca8072200a043c00046404518030b04050095400d400210540c102d0b60408a698029940d5a0b41c400c03100c4001c1c40200d43c2900c0c03081c548100c41e0445032084020300d00854005009003035103400c00c58a0b11804d000644000c0d0280710400 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 248261438 1250 248260188 248260193
    0x10e03010e010219050c060a0506030132071404171014090706020105040b01120303060b040b0703140705030f0a020f0109080a110708030f09130609021317030d0f09 72
    0x208070001c001080056242d403c085500810765184601c10820301409005881d8141d0b8001000b03a442249120046a03503103c407030209006014540c14080300501c54050081c80440c4410000601072013400c241440b80e88281c42120b032501c8080e02c039640c0e80c0082108000c0904190390440e10a440b6070305540c6807201580d05103048032071141410720004040c10800482e15014000d40000f4110f80c0028841c5140503900d01020fa4014012840c00c0d08580601d0300515201740c0c042030280c41ca41c500d181d40c032501d5032610b080f1904176540480020381c211824140c1562001d051f101e0b403581c084011800c004000403c00b02507040300301d60310304511400c003500801c02803d02032070a5040c050311446640e60002c040080196030000002416a480a0800c00c40c8038400021204101146102d4039102d550000015810f035500c04010040c460504902082c09411030740181401d0030001805803e45a65110040d5055400014030341a07401c24024210340b0307095508900c00c076480540e8001a00003031039 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 248262688 1250 248261438 248261441
    0x3120c0206040b130e090a0b07030c0e0d030203040f0902120f04080705190b0f13140703062a0f0804030507060906090f0501180b2a030405030a092c0402010e0301 71
    0x4c074503000e00000082c00c10006900c2081603140c1108204010305000c010b251110b200c0e01c48041c011008145d6030b40004500740703226444100020710001c045040561041c20000d50340d4101d03001d622402da0b0320385400a101c40162007100c81d4803078044c100f150690341d0f4500035444070300010003e0310064020003400c000500305221903c3c80000306291403a00002d0b90606180d0f0400003810302003600d11a40c2402000954018105802c550103400b40c070a20b440c040c011828864168002004242403c2210680d074250290512108500100340702c04100d5401049400560400e031b40400b0a00c058085804288100001c1c41c460b40142004504a0001c1d0b80311400c032210007005650403403100e201d03401041801e01540fa0000d4800d000d62140c0c14064407444203928018003000319803d40c01c940c2c03405007900c0e403001d00c1104001c00261901e0303191504125440c0d83c1b04201b0100028549103000c20302c528000a0460005085040d0420104070182241c00c80d2402a2040e03050140e1280c804446580c00d = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 248263938 1250 248262688 248262697
    0x111b030109140303010608010f0e13020f0a08011e02040b0301170309100e19050f040f0608010606170906070801030f1109100f090902180a14010608160903120c0206040b 74
    0x1000155502d40c94107000500d080c0041c1c100d030500740d1242760200702c510b07421070b40315800108072520829036080c14030001e1045c83c800c041d440d8000c0c484040014140c001940f0000e8800392842804051401800e00c81c03003207200314001c41c0c20000e01032006100c0348040c2400141c0104c1410100c070301c0c0182010024039000000b0818400003013140c01250658209080f8150340d003a03c01d07001026a0381080c000a1305a407481e8051406550f881d20301b200d8401032500480000c0c00050000c020f19130700d808e03004008078801c5400106402e008400309107400d40015217a407160303204c1c0d9900d0025034296960071321100d8184a05a850103040340c482c9038a5503422403101d004129441e03d40c8012480c20098034800142903011000032440c0640110250311850240d03420b8076086801c800599484140880c0141010303491060700780543d900100b4501c4c2c1040000d4020405000044900c4800a1040b6003103401404018410b4915a1844160900801840200620060401d4102925003c002d10907400 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 248265188 1250 248263938 248263973
    0x604030b1023130e07091509020403030215070c050a110112050f0105150f0a0c0f0507060c020f090403141e2d0a0806090705070203011a040507111b030109 68
    0x11420341034020300c0c082031040c60881c9110310900240e46820904e81c0c95417040e10601825513180c0b20031281468020503c50040d0107074803411510b4640b40c0c100290340d161400805448100c505004c101c0450044001340c01d90350340000201011010740c1c2e074003154141c00406141c14450301140c50b80380e0458600074244103c0c0e1a000c03007100c3d50b1501c0200318500c488201d8080b1030000800210b0300e21945102100d1220916003003601000c0d485107480c005c0d4920300722000e071090091010108181c0d41c440102c0000600031101c8480100c1f424041005440e0240c1c2e004010804084a894181c0d000728050410f074506c4000d902144504200700c100070ba8042d4180e4054240c84455003030040c04c5a810601180da400001a030610030012400340250a001e4421441885124001410548036500b1502160307800740c001e103c40031020350301c104049074040d0500c0c4150700307010009110138031030040b950034a03d14400070180c107090b0340060911300e01c1030b50070260155220988903000c034904510442c1c0309074 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 248266438 1250 248265188 248265239
    0xc0b0406150609030c12020111060403020106030b010b0316030c0509030109050f061e0109020903030409020d0e0c060315060304110d0c090f0b010c023c011d0604030b10 74
    0x1c00001d00c030340d40007080341c00540c180301c580030b018070114000d161004107454685c8a14490000700f0b00069505001c0b004440c0b03482c1c407078039040008044d419000041180e03c2048000e001d070b6243d10040d0254042200c92100d4080c4c3c0400844207103109400c480040c40990921925202c01c25020a00751070340d00c0f106840780e03402001800808241085190f41c098940760681c1c0450ba09000c50030075443c0c0600c168004181c01154410f040d0340d041c81102d00410075420110740e515100c3c002c1d00c2c0601888441003106005442e804035007420043c0489105400100e907107603010700000c0411103107800140040d0380c010300e490a03441030b5886081048800d42d01942c00990003a1400d0b52460580e680100744119650910104840c1d80e6001385456440c150304a4541c0702008000441074400c0311151628200b0031002800c1c4ca03c00318090300e40c1000d042c020380c1d601008440361048156210381d55001c90350404800c000030000700d20004441c94000458030082040d60b583d84072a150030105815800d003010 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 248267688 1250 248266438 248266451
    0x715020111300114010e03060106080402010c03050418051509010b040611010e0601060201092303090405070201140a06090e070e010509130503030a0c030e0c10030507020102090a090c0f140a0e010c0b0406 89
    0x40d83c010f0500400c644041f0010505581442030040c9003100141000717043c80700c40d40541c4101801001901c0143c107445180c141044c0d00140c01d030010700029642d280144082c058001c0240c10540d1455050f500c100804d00d150903d040d0080b1032114042c282014039550340c81d01044400c905000e040d000b080702d40e0002c00c0002c1c1c1400c00501048510414069040401c640613010305008825a0848441101c00280a607030385c507c240e016040e688002c4c1d130a10640810000013a506034040003c0d00c0c00244d0070491f001c1c0d081141540c2d90013500901840e0071802c001048a80340c42d11049a00164092400d0780d4107989551700c2e8a0b5401c00c0d40c51142c02a150008112090303403508c640c41903008960010001c40740800080307500050031034100300425468500003980e09000750111003800c000940f03a003d90581c1c40d50242c0040403000f90314800034009202c00f055440c03084000d01001541e41100303601e81034801001b40c0301c1c100d0302e0801c42c0c1807003030244d02c11000c10304410200744601e00640c000b0842 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 248268938 1250 248267688 248267729
    0x1151401030501051e010302090406030f030c03021608061b04030f06060317070327080708150a110406081509010305011d03030c04050906150c07150201113001 70
    0x7a20b074140c00413806600301c1e407031401149146903a600f8404000382070061782c0307000042c081809082d268001a18040700c2400c0071003050740c40606c0c240600d0181d403e40d804c9400811500c0b0000402d1310030200e01d680040e021030741881c40300702c41d56002c403070401c0400d1620382e49a071042580c1e905a107041d034200f40d4817441081840100110031441d12640c640d07541c901103441d507000c3d00c0701914000a0095010701074100d21071100720007410000c1c3c00d02d102201d0784542e8400c6416a200d00300e050303c0800707201c0040070a4070034030b40d80520200070204411603400c250802c4811034013400c005240d1072405151030301d042c0240d1122020280a54001d0001103240507017103140b00c0181a490000c1200f950082003000b00914258096600361203003216005029182e41d80020051100e00030000000c0070700040010f00041c000440e8412291030141e5010b04070390b00c81c0141d089030b840f650012004201044a401e00551a03507612000b5602c41c4c10061342c081c0e01c0c001d8040076a00c00d0b00300c1c1e844001d010f50300c01c0e00c = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 248270188 1250 248268938 248268941
    0x2505010c080601140309070521010b040504030c0803071b0602040608090d090b0d140a050106091d0114010c2a051207051011060709030201120c0806120115140103 71
    0x2a554200d082210450a01c54002400500382e00c0080c441d900003c03003c95640001404031f280100002000000490540000c0700d0f1550760b460180c0040c1d61812035038000c00d080500882d48956013540b03c3d507a080506489807042544024003d40412a1060207020103a046030000f0031f00b140a03d500503121810300d6005480210098034108107035000007a0044070551005c0d0301400e65824040c0d00e51114444a0b2100c05055145100e9420313080170020082c080030190712450484010baa1500c401a540e40c440d2103c40381429000b0715650940401440b10780c920456040d5544010700d00101c1c1001c3c1c60303d946903401c2607030b0582e2501c4039072031260584054084203540c1c054003045800802d1120107200040c1c0e00e40944c440c440c09514104600c600391390040c50003030b00d801c0200081d40d502d440c00304802000000340380001c030f001c940c2c4111103c5500c9100d210307100c00e580d802d403200c40f00c54803040204000007030091841c0c1d11940d00c50354074a0042c01c580c64401c2c0201911703e40901580784c030038000340 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 248271438 1250 248270188 248270201
    0xf1918150203061012020403020603150f0d03020307020d1103100c030c020d05192f1005130b0c0903030a0302040e070e0607060507030906020a170a0606090b0d02250501 74
    0x12400360052092214540c0c640c134500440c1501c40c01c0c03038004140b0fa40440d1000c0d000b96400654030400c04010000810800c0d090011443c2045038214161708003c02040380b0000000c3c4003400682c820700545005041091170b01c25014050b11200d448540c0407030000f032914060f100790754002c0c2d40343c1c45a00b00d01c84e0140104643d00d61180044e0100301d00c192030040150044244041800c0c0324866010003140c06010303a409944403c0c800c1ca2801740000c50108070710807003164000034502c038004104907511080c0c81014010350310307145005030000b8592902c030032682c4090149030011000704441d50840d85c0c104002c10114419480160f15145030003030035403030301400410b07038818860201c00c4403076561755540444072640e600c40743c00501ca4a038030000318000e0544060003045075100140419010f0340020103143c0500c8180c0c3c1038509a55146560400d0703407418401c000125114420612994001c0c50240060201e541001403c040818080c210581411400c141e5040440821101400820700444 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 248272688 1250 248271438 248271473
    0x191a0a0c080601021906050c0d0e0a15020f0315040e010203070f09051009270204030b0604150806060f01020c060d06080d020307030f050a02100509010510080601030b0f1918 76
    0x1040c50011185296072600b42d41c0e05c000304081e0356200020704141d400305c2907404079603084800300142135404600325035880403110b054584403040041e81512107070714000c0302c80504070480e2990071b41e221080c02e0422111a6500d041d070080c1c0b101b40c81d4040007001d00c0558403600503640d405400c860034030740160500005400c800e0107284034800d111a4141c0140d0104203e034860680c2407501ca5156208410008000000d0184d03030b80005400001c0c48488a003081c0522021682001449201009d6501849061145031110b801c44800150790b0320b07003442c28554004060040e11034201078200011119808030340340050481c0d079181c09002a40d000c02c9075002201260008506e45100d40c0c90240440c41b4401c0b90f00200480000c05c5a4128428000745400d2416403209000600b070481c4001d010308411600c0c0f002400fa400c10005a203080054081d0407650010200003940d16035006165120320014040030350300c0c04140d11420310140900c28846030f02d20000c1e25003403100c020302d002d2401c0312121005 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 248273938 1250 248272688 248272693
    0x150d0504230c0306041214070309090b030c01020d030f02040b04030c060201060503060c070605070e030a0c09051003020a03060c0507080304030c110d110d020103060902130f050405040302191a0a0c08060102 90
    0x642d00b140c0f000100c40d50410b4011b19002c0c03039144c203114202c4021a8841e4210349000b40421510205500003034182c01782c510f40f0105000c010407541c01e060780e44141c0324016006074010ba00b200001400307075102000c02c4800c00d2025140030b4460a4802c1c0d00d511603030040343e200c041202c00f0010b0903070a100b10300141000300d02410b4107040c503003541c0c5444d000b4010301400340c55551001c69449805405203414200c4060181d410646050501000c0c04001d031294030962800d0200141e254880300d4807003002d41ea40141140c4880f82141c4440740102880098507080c8070041001c800440c86050141d0710640c46551070355290840c500d000040e0509060f1a98041c44941d989180028100449418140c0040d071300b03000988041c0c00120090401a40400400751001900a44096107019040c040d2072042401100c543e98401c03d102c2110300c101d030040c2c016001800324640c04c001d80413984403414003445081d490340c061050307103000000c000d440d041420b56860703120a01d210b8020184545c000c1c0240003 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 248275188 1250 248273938 248273953
    0xc0b010504020702131e050c0a090b19050d0209030a0b040309090216110310050115080f09060612010209040203010b0703030e060103050d0c0201030f09050c130218150d050423 77
    0x210b1907403031442c640c0c0d20605480f00e1b09800602c4c0741452201401000103800d10842c1000a0844101e80c0b00c124141c0016065076070106444051008881d4008001d682030302020320071140c00c81e00d5800a00b0034a1129408010600f46540c04111b03e40016000b03008220090074680b501410042031684040c0b1428010b01961210030701e10b031200ca00490b08411902c2140c991140001d040003525000000c07001e00c1c0c2800801c151003020710070f03020414035403038840300340d00c0300455041041400c58140409521034170004002e414800785000c1c98110300d20025091070780540010b0240e0b0003d0700081410440418a401410340c0341c0140c260300709907207000d04620350442c1c032440d0701e07600185569000d00c245643c0400071079100f030b4018030380e101c524030040041d460f462034010b8803080c03503994041c8502c007110410401c2002501c2101c4401c00c0b218030140381700780c040741030001100c1440c2c40e943c04410144801514800c45001c1c9901c100d214a84000c0e4800940d900c0c9542e02c44d0bd0042600b0690107050b = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 248276438 1250 248275188 248275193
    0x1020a12032324010210050f0601030c08060d030315030b04080910030c0c02010503060d08040e15120c0910090c023f0705070f1d0f04020108060111010b030106060c0b0105040207 78
    0x40c02e11000c00c0040d00d1511030003c04500503440d14442945c0050307154905810040c04d048800030749401001b00347d9040c01071030f0304100107c4940c0806e8030b81c00c1e400381c02143c1c0304000030300a40c8030700d8410905000001c00305903a902c0b02078210b84225020340c2c1c291400034004c2113910305112480c1c89412070f4101040110354100000703207a00d080c0c05000703040c4140000480c416039548070140c45203540c82612035079240d44031003001c1c3d0319484c2582d403007404044200300144070b46400e10098140741c60300d00003044c1c4200f482d400c1280e001c002501414141061909c042881e078450300401064658940050801c400044846010740c04100a205a45455a0303045008030300886450142090505031440d124013590600d207090400c15884144024410039002a490450000000c2c0c0280c1061801c0b80e90340c0d55220446034080c040710028005095800050110f41c014035243c15040720040000031091a00400702e82100c10640025010a05452846081025034a4211301415096805604003a00359 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 248277688 1250 248276438 248276461
    0x7051503040b07140c07050a060e100302030a0b0d03020a0b0a051b030a020d090b190207020d020402030421020304050a1502070302010c1a070806030f01050103170901020a120323 78
    0x40c100a05244030b4801180074640305404803040d442d05101069034030503e61101969403074580c401c540c095145d01c800050980e0041041500c100400f5111003040c022121f0308600030351008028540556850701502d803151104040341030904c1c82600184952819401c00d0002c6036001041c035075815003000204103060701281c40f40390f8006c400c0e510345612610703100c5030744000c0c1c050260380150840c034010200c414041c5514115000d40070070807406c461340d401030040506911880801a40120603040311800604059004543c4540264024a40c1c0d4032141011924650f0403030380100181d002080510441c0340004018000b4125042c2e188e01c854614580a9140c119500c03020703040c482101800b806018103801e004040f150800c2600800e840d00d240c025080280c251680d50180c800c000f02503040c0c2d03005100311070681e030b0407500c4200520090200600d09038031903030505045004e080c203000002000c5003400275811400361808680000d22424004159024807152128644d10034280300f60100308 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 248278938 1250 248277688 248277691
    0xf051c05280f1101081302150304060b030706030606170114090c070c06020d030e06040302150603150a02090415060504090c03021909090e072123060907051503 70
    0x50040000800c1040392a1900024800303201902000c110b164003030401003641da5401200d0300c241c840449130340341c140b804110b0082c001c80094000b494034041c4080c8807880c00145a00c684110327000701e000b0003900040390130711590b5841840070a0b1510414041603800115041040c50715a200302001c3d858180c4170741011080041d0f090140585001040c1c0d414040d808840c03c0c580c101502d48002c590b1690025030300c1c1074001d07803140001c4c500903d4041c03104000c51180d0050f034265004001f003444501007800911000307040035606102d00a43d030040b00c0c80d103c12052140f44515001600d03004094140020b88100307413850665a5001c55050104980001c02c0c0c038262101c3e903d002505084d43c90f015402441000101c2c54034004200140c0640e41e40300814a041e11a00c48007030161a40300038240c2d40e210614094000d1403000e41245070459548842113541190040c1c078601b8600f803c600109410200b00e14022000b50069010070910010801c00d043c0103010581d521190300c02e4503110002e0780d000 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 248280188 1250 248278938 248278963
    0x504090206030402040b060f220f0e060f060c01090605060405090304030b07030203041e0503030613060501050a05210f090f150414010b030d020703050616021f020d0203010f051c05 79
    0x2510070451846890f01c01c01d5a0105102c1c2ea002c5583d00e010040f0100c09444c03d082c1200248040d28000c02c041003040c42b40411250b6140180809455030810044002682c0321f00341d400401c10f00040b0788801c1c0900840c00990f006030000034080c1003000520054810003860084254070801c010000540551003c540c44041d610380141c80f5103403807070b0150041c84218002c3e41036295800148041c03203408002035005942c104c4180e8030300b1001115040039070701c41d032141c01c0c081b41c420b02c01c06000500880041c00703200c4005140d002600041c4c41400c0900d48240c42040e1102c8c07000c01004014481000440c005100708001400307002d840c48003918424500034001404002c015403207039884a0709401002020100506540c0c50b444d000400954a24844c403081c0c1e928811580822940f8614241b1b0203000c5155038040d103c68030b003a00790110554000342465142036402c104407905d601c07130791001d1400f03000402c000c19405850301c800c12100850114104c1c04c83c40315442c610000072000610b62601c0308 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 248281438 1250 248280188 248280191
    0x10021b1b030c011b0f030302040501080a06030b0c0702180c07201c0206090a23010e0d141203130b0a051306110f120402010305090a240b03030a0306030309050409020603040204 77
    0xb00404c20b11a0a41d480700c030091403200c10500c400304154058016009950080e40d03200983d9030b5100740c1c4015903020f480007600c000d89260204102c19400002401418006003941c0e0b0000001d141c1070182038007c45020059400c003041e00b008001c144456541001503e1030f660311307440f54020004103a00d400b040b41d81100101200220110340390f8100b90b60b08049d00500303030480242c3e52a499010025030b40c50a5403000f5044152620640c00341304480810710f400b408030740d00b9030010b580d900d90400b022003d2006a00c2070365100c04070070703403494000c1d44541d0b61040d0700c0b4041c0c4100c0c90070724841c02c0f01900301d8800500b04000c0000c84102c3c80003c4c04a150403945c040303081e641d0520070700c2c098441e42d40340c00f846035030001d00c0c0e951103040c40c0e030302c11b0040d4400e907020001590313001e429030b0710340710910801000b104e242a250403a5100142514000406030080001d078000703908000382c5598000158140826180c6004000389504041001c0c003c1c08140d48c03e10030001a91300140e03540c84000d05c002e100c2c5 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 248282688 1250 248281438 248281457
    0x11d09030405040f110d050a1b020a0b07032904050a06211b0306051909050d05210103051e030a02031213020d150c020a0b06010e010210021b1b030c01 66
    0x1845e00000c00c5000b0f00100310395901002c0b0754290140404540c20742107d428660385d0403240d00c8401e03880440740001d40c082d04500341a41e403280e410034000b41c1080c003010340783d03044200035041c1d00e48440d0b007400c4044401d24100500f1014402a0b0790700800d0710303d60341d103000b100700a0030680580d03000100d54501382c1c0d4000e0303088625204088140c0f0f650b202e0010340340b070400402000540d0703000501880d0403003c0303a0041c103e0103030f00f401070314100000100203810a030300d103560060043c40500740390190a2070301e02e81800b40b041c4030b4512700c00036402a507007640f008049402c0b004034054600344812031800034500d003034a02000030b076036407003407424541d00103000e20002880c48a10800b0210b403ea801003080c40c2c3c120141c00c0c080a0300b500c000d01d00c8940c07858420b0650409000003604100240d001c103041402d5a560001550300c03510950f0380c0303810340c015010300801401d003d1004040000322110300450300354018203803d20f0711040000350342d00040040c0c12015296070000745190000401d00e85022003 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 248283938 1250 248282688 248282711
    0x30b040516080a06110702060406050c1009060c17010f0510020708190b07030203070c061a0d030f18260a0f03050913050f04030503070203090612011d0903040504 71
    0x416a10507000c400001280d08041440b040101e00d200016004400074000d041201036094540d20a07444003d610003402c1104000c8180500c01a00504808005407000d0300294001e54042d07640ca00b130211011583c44160b07440c01c1d90480d0340c01140c00ca100030f42500541c10594005800d101602607140700c2d000d00d020100761244204900805031400805070340e105003000340c891001d41460042154048003100028060758464030950b071060130183e8031041210030b980c035a41c3c010300f8102c2c0506440707544030700c61107641d455540110281da442503849450217020100c0042a60807000c1504a071001c03220820016066866040f1001c0140000340e40d0b000302d21020400c4c0760820f0244001d02d00b80c140a200000d040e0450081d2a508009844113004034000180030400c95400700c0743d04c400c0080350004503010901c51006917600c20000d00486e440c000b505400240c05400441c5038031402980503006100e0504c03805040e0150300c6040e04816507900700040019228007450140900550741c03017003540d10 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 248285188 1250 248283938 248283943
    0x804080d15080601030605010b12060f0609040911031b0f0909070e0408070c090b01020a2d140106050f010203180f061b06010501020c0f0121180314090a030b0405 71
    0x1004064280011096a0790703421050301d0320005d01c0300307840481ca00030002401041090881d2202c003803640004c6a50f5841d039041105188003200081d403c14802d010309541c0e07449030711807910340c24004c205060340440034100709071404120a4440b02c4030940301b504007440c0d03250041004400c2200f15180009a510031700600d203800081d5001600d40e05203c420301040c00854801441500d00801980c0d5080340c4cc3c401600139600810003160041e446008070340007080010702d40c000c81d00088540703698001c01a14a184101650b500d056620041d401c1501003198400d00c5442c00620301501c50101c0c00f0010030010351640140c5401d48000710518401c8842c83d641e48c82d54400c1040010070707103a10744d9001441c0c202c0b0301d00071540c0d01810f8030400001080700d6000068001903020010198108a4504001103c00010b0f04c2c2007040e0b0501c010707120f441c218045000320046521400710303040100381c65090003003042021000c440d001d10010068111644c40d030120210940340c0000d44558a511180f409a2 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 248286438 1250 248285188 248285201
    0x121c030902150301061d0d08030c0d06050411310e0703061805070807080105031b0d0203010207050a050d08090c01050304210806030d0503010b09041d030705060a0f09030804080d 78
    0x180b0400000000b082c41a0000b5030940f1140c0c0310301e00038191488013810701414039943c0c80301814422090000411940c3c048000f440350761040170300802d031265074401080680c0c0360341c80d21008407080402c829000d51545024001c03400032000c07040036006003000d0340e814206903601510034240742907030004507402d002e504101c004150001c2c94280d08000441d070100140000e44d038600002c1d45040209010314403a0790310342d0580b00010050303c42491001c40712100c0380e050304810790b0041e80c003031244000350764280b000c0d0080a00500290000703204d1403030051704003503444881e0300c1408252010301140d2640002c085120440a003005950f80d20703181070000e01c2c4a000040fa886040500c01150440b44d80059031901444040e0b04850441ca0f04450544e03560109004050305c6442c14001100d1a28254102d2484042001e164100549081c0c0e025401c55129440a40d0f0640c001028032184212621a62402500d002020040e078805694000e00b03038a8003a00144c200b0b1000f1070003036440750706070b80300c40c = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 248287688 1250 248286438 248286469
    0xb030106020d230f0c070e0f01050102030702090a02090f12030c0601150c111309050a0303050a110d0506010507050a030f2c01081b070b060312090907121514121c030902 74
    0x541b04544e94098980c0420030407640300c550602903900000300307540004251211158000d21006032941c0e03c80814000750015030340290300c01c204609883d03982c1c40d8018140c900380c581c1c0010710f035620032981a0754036105040e4007640503102c0c0842d61700d10040d807001480c04403c1d8005550780a5400d10800a0443c0310002c0d0500001d500c0d115440c002c00100107485851a0f200351130034401c43d501c080401003200d056a68000651004001c50204400300307038045135200c00141803060800c1d180d510bd00313280172040041117000c510b02540d2040d0064210070b10010260800c00d030380c26025101c50b111131005552240f039505200f0000b0100354000c840d44400803041044203a1151243c8242c10805403060064801c0741c0203004c2c0010394440e20442c0c00494110301f8010b448034815441e0790b00c040768610340010304412015941c1010290b05524221100014900800780d800c0d12000760003000303031494038541130003021750060440d01d1519489404e1828000e1032818000340c404503d0010887c2900e080005 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 248288938 1250 248287688 248287693
    0x60509032b060605091507061b0903030e10050a0813061a010e0603091207170307030603030f110d03180b0f07080114030705040509010207020301060b030106020d230f0c 74
    0x494855145000ea03461200d403904050002c1d03030760b4400030b641034400c83d40340d2900b0401c8408000c889010400007040b41c0340c0302e8000004c290684940308901d25101a42040008030216000c00a0640c4203c42c260036100442d01900c1c24500840301130040d200e07180900040c410b16100140c0c0f05415605902c00d41508458184200040c01026000c418075a01e0243c0c081943e00074001c40604206064a11600f1590001c00201400d4881c04400d50880f04003214218066800e04954008103405180a40003036140803070000d00b149001350010070992091000c001c0d502800944481c00010300311508807850500260103110b043c800b542441700400c0141c0400d80c0e010610149625134900c5600c0f5455a558905441c0d0721414a13003140550f203a4400c0c0d2645c040ea0052000c2d10781648550f0b0480d43c0c40000621f0640306a002c60700b9a40c00e50701c07204c1800c401200402000d901804007041e211110b1801c1c2246502e6003024454600406111502c100b101040000c1140c6c0741c0001c4810300981d8804 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 248290188 1250 248288938 248288977
    0x180403030203101406072a0306050a0c0507050c0f0d0206041502070f1d1312020109060c0908071203030e060a0506040f060e0604051911031608060d06050903 69
    0x20068065030082d02d24402c283c1c1c080500040a15602048a19181c03000740424600305441d19400d4668032110340311424040080080b00558810b20207202c021481550041598075000e2000c41c200e0380f00b00d081c002403100400080c03000070f101144c2c0d00140041228012954144d41c40440c05070441844000d40101c00020040303203c1410052482c1141312542c00c440000b0744410803114400d0f6a4864014500005448140031440c040c11341070307200f182c203c00f500020311261941c81941ca4082048000f50b50b40d0030300c2c40140f03d482d000b0300d6030084850405111181c5401e41041d0703200f010f4070400c500c4d2070055080c001050300ca50400524030701e41c18100d4045052060300300c8003d100580d509840b80785440001480380e022070042034122a0344400c0100140d07a480148000360600501542071081e1800d100380701d43c82907125103241c1e01040749403a51a4074205a040e0088103a00703a5076418456030504021081d42c0c0e070325459108952002c000b040300d0326a0040680f4500400700451f4100e400e0700e0b03 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 248291438 1250 248290188 248290193
    0xf01170a06150e030606060a020d031a0a09020a0e0f0a0504050406020706092a0e01050d030c0c06020c01030e01021801180518060301050a0c0f03021827180604030e1804 74
    0x1083e0340e20754004406880d01900c40c4002c0100724890682d0031402750300400e0700078140d1070095101164100850322901c01200c9110000f0340300c0c0049401120400d070b40800c235600e0b0030340e1104001149040036a440c121250000d00043d122910501c2403e00c40c684410006040010350b4041e201344541c04941841210604e1074007001c03031009511a41725406002400007010250014132100310f039000320008841b6401c05090160800b40910305405012060140100040c1e445003441c0080489901402140f0b00c4680010141d4500301d45074011a8014030075010700d036803814404c0d104030000f4280007140c8d040c3c54030309910b0030429a00656002600300c08007070f1405004280144500d004600800c001e50f9441070160440d2011103c400010307809128815000b80039500412140400e1600e10b050102c0c848001003510b240007204080c1c0e00c046100c0c00d4007080c050f000140c0c10090501c1c10148800c1e04883c0d040da00c070002400078082200c5120402d2141c2c84900300e14168901103520ba05241ca040d0 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 248292688 1250 248291438 248291447
    0xc1701030f03020d03090b0a1a1801180b09060607020109080f01050f0a15030312020c100606021905030304032001020d140105012307030201060e0a0b0109050f01170a0615 75
    0x51002e50240c018201d40b10f49140c481c0c03055580c2c480e40100352000ba500c0d404030050041c441e010b08440a071036070b0201c03880150755000c00d0000403a0b011044400c5507040081c0e02e61004102c468031114541809519500d42c0e403000b00242d80144243d41c1d0340c0d214506800103c0b882e5126070700c05401c0d4094850308081c40ca0040d001544150340c1c400100b03015444840d18070007210900001412005d01e000da003840004d2084201282591001102505040040e1310700d48c00c2a01001855407096615401044041d4040c00071107002100c0240403108591030351a071301d4692100030001800c0100304110b0000c400480c442446285000100840d1034016403981075000f0301480382d00750a83c0009400000d42c546c46000d0151050b001b51a2404282a118601600d2900400b0044003075548400e030104050b200b4144d940d1082401050100310210624009001c45405410103802a010b07030f000c3e0407a0780d070460803200c0c941800300d80ca500036a8900c0800d4004001d51340052540e503000e50301d14014650300 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 248293938 1250 248292688 248292713
    0x270b190812090306070305061302040905041a220c120503071b150c020d0b04150606030203010605030606130b030c0c06010f080c2e030204090b0307180c170103 70
    0x298001c403072440301107200c003061a000b03845025600d60721000005449030710980250707402c10805000c44586003a000c0424042e41c209420584640d56581c040000340111030380020a004880c000401c183d041940c00480210003034101040400c1d800209101008a1000040c005014032889140811282d140c4961a9400070f2000e4800402c400c00740c4203200b500d4040c0030115040d0100218000c417001c0401d490203011034a099911900c04946034005c211021607191041d846a03100307107030f404103095122080b50200d8201800301803042c001409129001011250014411903c0a40300c104104608099440c0c0341c104030045407001c0180520310b40c04002030203240a9810548000c0d03a200c0000c40140790031846440410707446211485000c1c2400b51990506c807069240e9010100040c04490380c034031211450440020f5030025081000009a100f0300c40c03020341c1140034100c080d250100319100648400c03da144080d58034801e41c18081d0046800c0029011002141c1c0640e40e03607410400000a403 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 248295188 1250 248293938 248293949
    0x80909100e1b03061011010f02040e090a03020705122b0f02061509130519021806210c041104030311061308090604080a050c040b01020304270b19 64
    0x44001280c901021000702035680b803080c184103419a82c48504009000c2400c442c00c2041c0141010a203075a114203009100001e09044405a96249844046ca020150090a5042d10f8000c0c00c488400254089000d001720743c0c040722103d501c200710300b1074642004000201c080c040540644000b540c0041049000741d02100c07501c40840f070081a600503a122641283c14001140010b07644404500e080c442c01034000707492040700d4407906000e6490034a0310001c00c80c200344020002e80d0035030862070030200340742c024040000c0c81010f07420003c020a0060540da00f008180040d4110305100c0c101c0104011040ca550040c1305200e40001d14600000c0b581c8903000540000d030000e52001d25001c0e00003900d601801929070340501c0a0b80360f485218a64008585507a0300aa04000c00079446208005050f00b060056018003d00585141044110768480da0228159002400200003100e405944c60002008041010302030240c0640e04070010660810443d0b481540d0303101084102d0301e1040e104040e07a0303 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 248296438 1250 248295188 248295209
    0x50903010203280921030b180118090201020d12180b0a050702034e0a0609060810051e09030a020705010201020708040603020a0905130b030606041503030c08090910 72
    0x5014681900762034140c51302800c10b25051780012000d4544501900c12030751185000034450100c400041c20b803640c0b200b804228401003100511a4841c90b24801e0030310a10084d042055202d50350000c2d44403c0a10f8460040c816414004c00304525a034101d540d01c0c841005802900002d146041c6600305801d4070701101803480c001c006a0000d000008640351403251445030031540784240b0038040011440340d10b09249801c0084c0501d080440742c40900710149080004813442d24207900b0340400c0358a10b901850710541440400c000d142c9002c940c0360004000d00030003081990302c40385401c4d10f91001c2d60701c40d660050f2103802c206403100d0200140100f031001d5425600005d0780ca2004a080c0c4c05004e10140013a00100300810001c0e000341c0c0140300360038450070140c880035a03c0d030002c2c5280d8003074055200704545901e401e0080385410322202da4001d070308a170308000e24451012685200c0030b250200a00b440074507441a0140030540b815500c0e03070500201760303007050700d0199040fa0201809201e1021400c = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 248297688 1250 248296438 248296501
    0x902360606120c030a0f0515030d021b0613030b0c09010927050415050420010305041104020901020f16050a080303040b041e0804030b0601230301120201050903010203 73
    0x24505002200d1080300b032034100ca046500d4000440c881d99101a00e1100030554035107009406405600031680708070b208041001100c1d012806150901e100d0001070b8007150481d80f038a11405070008030030000300000b620807603140c086002c011420480507800190070964041b0400444000e070303a00400d2829401c0ea07942c01d0540d5944880c031512004031440c400765000428403030030b0440081e4440d0341e21a0042d200c00b081401804903040803202c00780c81c02c1c1c500804400d03520624588108100d2040202880c0130406858a42c64007024a4503000e4071074801d61300061611070780d0303108100d845500200c0c5001e55803500c8020051a0110402d88034031402540100000503414902109883c41307030381c0142e2099070aa40d076580380d1004403000fa0303402128003081072120001c261b061f00540060b40c4108040b0b4002e0070544005800f110000030000428400e002c010303c042d01518098038116000420003102d82c4500d031005032094001c09910716090342c404030400002400c00882c5041c200300c9000d148406 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 248298938 1250 248297688 248297701
    0x80115050901080a06180f05100c0e0901030f020111030409050105090a2304240203040c0e04030c0809060904020d0b0a21020909030906070c18150306090236 69
    0x310100b4810041c41e0f4210031505000f01c0c40305d411803d840054a40c404510006903551f000c4441d1090809540070380c04110f14a00c14039070b900c038445528046040c40c62000088900052202d1414000200310755509041c01017164080c4c0c00702104451400d050780e840c1c54440306020004c0500f4460301c2d100d400034070b010a10305001445450b0258101641c1d090362508150303045000408090301c111018107400f02214000c290610581e103144006150240e601e0a143c10010506900ea802000746041d000d0b0512001940040804105c02c1e031101880d5181e14602000519a0080500440d0044e000080c4288001c4155001071103014048460031002c1c2d4903817002e0711b058001c0580303014540f0b4413011001d001d45462222203602428500450745005a82c101107019030704020750480304113211100a1000c404007030f441d140c00c150403760400000039a02c0d0881c141c00554403016024030703980e501e03034020340d2502e220030340392912900c00129160b0225001603030005d00540302c1c1f074202115040410301 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 248300188 1250 248298938 248298949
    0x190608040611070b0c090a0f09021c06050105161e0f030f14030a0b04020d0e010504020a060807090303050a020313080f100207150b0334050301151401020c0303030108011505 76
    0x6180d0032002d00c4c0000c0d030729901040810351105419a40c4152520300000c0d10b104010003010160852071070240e1550520008000f0404440d28211841e07820601c0038405030340d10205a03000c10100301c0c1000c114070000e0425054200c40350100c217006440500e0150300303200001c1506000c083c465a1f560302e6103a101082103c51403841c0440c0102c86408001142c444400c6801c401c840d90b500910040c40d101344000c03840211407601010304980d0351a1000c000940c43e2640214004046030b0808000c5407404800040c00548035000050520401080c104841d038400c00580e04801078a800d40c14072551903d03102c903500c0d00070308501100f40c1308003040b081e90901030b80241e0750001d500440b00035003c80c800122202628419400541512405007203603045440c40381c415600c1481481241107580001102100120b141d07046a0700036814510404070000051074003100b12012000c24031000c90301100100e0400c0108440c16505101c080000718000380107510840c0e440f11409440c05a00b90394400348032 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 248301438 1250 248300188 248300197
    0xd0c0303081b0c0606040e0c3a08070318030f0b0a061208070602030703092a06030b032127030d090f060507020105040905010803030a1401080a030509190608040611 72
    0x80301e070013010200b086030401780c001c04004042c0200340d80c00103c043d0081742e150010920003038460100d02e00368042403907800c0308804498503516080302082c091929103001d0391160240007401c22818080d40c0d0420002085030101440e403214600c01803082c24140210b07600c0090351860b03541441c2c54030000d0b100d84c4a200c4010440d52040606081407880d450300c00081d080207009100703054540b404000001c0404451602094000580381c00366540042071944000d5183c00210915141001d1646550360001d0a81c0c00c8215400d024841c503031104600110078010740c0c0b00060f400e0030000398840058560520350081082c1601254844890040102e6030140148129a61142012030500070a44201e00804107036006050031403a00d550b0300035000489000740d110306c50580011050008075041c50082054903020b400e100801541410104e944034002c509004062080001d140762143c0c0341c01181c1c1c9400304402810b140e03090303500d07031300a00070500840741142c0680c07801c0c1ca41ca84261040b802e45 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 248302688 1250 248301438 248301457
    0x9081b0c031f0f1506020319080c12040501110a0f030b030a0308010b0a02010207050709060306051305070501111c09030201180e06040203180a060218240304020d0c0303081b 76
    0x300c58210300d031802c04018040c2041d0b8440e070a449020001d4107000350b000b5400213013130950003559200c42140d25020189400e10035201000440e80501025507003c030103540426076503040440440d165481c0c0180100343c00701c500c1050100c0070611032010b582000c841c0c0942009a1000e01c0300c2c0c03a2620805480d25502c800042c0403420420050000300d0110010300f10035440b5000040c80d03d0a2034440d5880c0c00c20f1a80158402c03905e0701000d00822100707002e100c2d00b02040003c00d81a82545070368a60300c841c405d0188074100290516011300c07002040000e801c08249110320f0700020110920010040c07107550105901054512030001c0d10401171400b00f81c1260041480c052440c1c50b00c608020107540080c0c035042c400e0008a40c0c401400205001e03802c1201e2180f18010ba4646464400c02110284501d1180c41816035401880c5039020308d0700c0e424400f5170803504072541c80ea12480000e418800e2004042c081c201c0302c5d1004400c140c1c004460074002c08011001c08200c4920500041d81071250101c0b6 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 248303938 1250 248302688 248302723
    0x1201050f04111912030906111506180c070203010606020d05040504090807050322080d0509062a0d1701140d0302011d0a11120303071209081b0c03 64
    0x14002c80d660440d40c81c145100100281100440c0304000d07100101560030461040012141c08020142c016000100515a90802e0a20700707030813140c850b8031a030b00074a011303070314034224000078000c1c2e0399450002e4841300c0c1416850580d42842c0c190f40120b9005100c040f03001e580b9010b00403542d1400018034a103205c0781e40d504c0e6464107003007000f840041c003a406000c135000300091180c880003900c10f0028180402e102c042c80000004032100c0319a480c0340d10303800205950040240508003580c020120f03900000b064421070365444880403a16520161220841c2500103054800300400c440481d101d421629696140c2c0c04283e0f0b1f0440440003c2030a2191010000c803407112a46107081911100051038041c0c0000512845202c030412030310124800040c1c103e801c03800c405401c0210790501142c40c040300303985640303143c002070281c10390381e00c009010401804070705a2014804005500065000381d4001c54075502c9001642903984040c1c0c800380784500e00d02a0f8000d4004504000504104281c00b0364403 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 248305188 1250 248303938 248303941
    0x7080c0402030f1801020d0c0206060102060705040612110c01060b030106030b0109050901030b1f06090302011202071205030c250b1513330302030d080603120f0c1b1201050f 76
    0x2180f071130660100101080554081c000a640d8680900c00c00b0442d030016006018607140c54000242003000c01040c2c0350074444103010602106510404442c241c90701401c0002c1c079104120b180c081a80107066190f040c5600b00007010606c07a4050010314121001030720184101c900c0b04006540b241240c2c0105ca410840000041020400c02072420b80c200c4106014020302c0462034028208403101c6411080c04542200010021544c1c000d16900000810030000c504003125176480c80c42007444034a41b44100000440494030f06c10681c0304869030709084000c0b0a41e000000c1d4412845500790300030907202c0c8110300000a1260114040d04a0b001c0d20041058081310700c0002440014208440d01d080740082110254070308500500541c0c80c04030300b0b14100f40005245104140c50003010b5001300b0104140c980034086192000503045030a2a0096a0f03d0b48441020401442034000c20350107011511461030715210340001042c090341e010100340c81c0c88030301c07001107215103081c0ca00c155070181d01e2490100 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 248306438 1250 248305188 248305201
    0x90305060a1a0f0402070212030306011715012703060b041109030706030c0302091207050306060316030f020d1a070f02070609030627030513050a0501021c02120c07080c0402030f 78
    0xc0b5803e46030b86004000508042140d00402d104400c0d1002d40310482d400081030082d150b0300850344800203004c04d03201903c240b625107600e507015500c40621906111111000345440365400c204a82201d1032040c00013011650b0741000006420207410140c06186084640c0a00c4010803040f911340044c0500101034030b6103000f20071401800281030300420568203118482c041d41e100051900c08040880080040c242494100b50401a000c2e020b81d00c0b036445a07010002203050300040d04101e98001c2140d4164101c03034000310301c4030a081c0100400b03440f1b50001003080307240e0300322095000340034a41c0d0301d07220001507100c16a540c006502550b004621414010030004403140c2101000a08a480c1c3c0e40800c4594000b140701442c4a001c00c602082e40403030b402c1040714004c0d40840c014601207408151181c5010000303500e41400b0740c0e14480412010b0000004607000304084080414104416651600307103a401c182c075102c80d8018400540280c10700d590380c6103498025240504100f170b41c2001e8945a42 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 248307688 1250 248306438 248306449
    0x50c064308060a1a0c0d09150c0303231015050409020f090405070f110102070809090405010905070b0a090803030108032508030c2512030b0d0c06090305060a1a 70
    0xd20541e03021103c0e500104010307003000075071498014440074a0340c40301060607103d41400b03030714203810b802c10646a60800c80007002c60301110302c5056a003002c0486d05010708007180500648150040310b81001d000481c00c441003924070310312400c04000705c1d00c00191550003c60303000c000d4862482c009001070100f440030b03444a85c01000c0d1003070f44414551404201c03401040c181c0380103c40b490041004040314030102600319080801a16401000314600f480655500c04c041c02200280c0340605034600028040103400d52109101c0c81c0c2060442707607015650701000b241039101080d4180082c00d6440002030995001040d030b8143c5c3c007210051400c05188602d0980c0007644851000e1502307201d113110002040d84100214003601d180410596a001c0c01400042125890603049a481d100e48000b480881c540c8007220901006030301e00410030300c0c130080c0010790801003840041e00201615500041854001501034200d87c815004d54072030350b070342d800141c08841d00c44002450100150424030001d107450b = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 248308938 1250 248307688 248307691
    0x3050d020c2d0a031a0115091518230303070b3705010302040e06090a031d0405090a0209091504080d14040c05011107050f06030403050c064308 63
    0x14520b03201e00340215000209407009a90094550108201050340c5407585685000e014140b0b40041c0482184006001006a805846512520301000355054038452069849104911014482200f03070340d190304c202005402490094403506480c41130002e00c90502100b540c03811a0082c4440b501da55070082520264031038828101080e82c040c58810b4032000c80114164601401110300048541c1148140802c903044001c2d00c84a5034009410860701d07020008003214420741c140303080c12803110311035884240305403c0d80345140e000d420107040010b118000178240505900803542e801541e20768001e0b56271200c1c0000b44901d201140c000004010519034001003041c4042d01c240000c41101700ca0458060250940d01101c041c1c07140c01003000a5a8020308084605040801070a0003d20b004009800080c168821502170b000200000b07003854040c00079904c508a0000644800c1e143c03241c40240011013402c140d00380c0b9805900c8000541070b03400407200340048880f50401140c1c800c840c06030b402200 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 248310188 1250 248308938 248308999
    0x807031503150b0a060c17270f0301020a0309060b1f05090a0f03050a0501050c0313170408070e040c060e090402040504110303190201200901050c0102040f0b0403050d020c 75
    0x850b44016642a2504c0790650004c0000b0b564a0368040c68900e04100d991481c0c1c01180d070019418480300e0001d088000803603129440044009141c0004003010849000c0c001034640d606510100b403160307003150590090611244a0081085410f04810401c08041c1a6802401c41c005941b00210001070148009164014004002c1800c035079960104400c0d03490315810844940e00442c00c0041004024060941c0004810302120b0a42c41c06003200c0720104c201aa0141002001e0380001a41d24002022180074041030b109445040b85c0b940882034a150f4155411514211002c0c0001410f500c0351800c0004140e0090140109440315003c01000c1c000150003512049080700e85c03121141d40c200000d1104003450f4041c040c0c6450300c0700f0040d085609441208083d804020700080242c0d06000485181e10800d08100c0c1e140c8404c500c1050080c082ca800011410385d4625011030381c128402c0103081124850001c07a212a40440000c03603d80100c0100d95402007200025803444451074000900d022a = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 248311438 1250 248310188 248310191
    0x1c0801031b0306060609080d0806031f02040305030f09030709060815180607030c11060618071103040b07140109020a09180602030c0405090f010b12070306051f080703150315 76
    0x10307143c1c1c82c1c440c102d8002d54005004103203032040800501074140110b40280101342040001e614111010a4565a04500480f8961009582c007986064140c4c19100515081400c882c0c0392014200c400a0035803158007024401e2060080000b4441010700501d02a0340a0f9009416000780f4030350b622000740b601400041d15070749000703003607800c00d83d081000601c03c030044c2e034000c190501c0d04540603261940350340c0c5640c0c040d004402000380c152215644000e1080d0301e01d48002442e556900c0848000c180303290030440324000020006042c660310310142128a01500c41e041008201010752400c07180c0c0313108025000904200304102d5513a0582c01204803211810524882c4c100c1d0b5601d140817a03004484103103036110003207002c0c082403c046030082d038410215081410203504140d20f441107400b038201c0c502100442c450000750441d2194100c400280350143c68070035010f254004050502e2a0180114001151000081c0415210f4052008030f540e020425401e01800d54550070b0f000701c42c0030322101509 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 248312688 1250 248311438 248311493
    0x40201030605030607120506030c0901140619020304050103151415090a1d070201050714071b060f030522060906140f0405060c07030807200d050a021c080103 69
    0x243c03014070401e485030301c2a0355030f1026624817075481401c0301c0e006050207002c0e80c05460713001010780395034480b0f6055442402960100380c0c3c0c040c0c000b5026100c0e090381e4144e8500d003115006400e07a000005041035607000d0300c060103003030040751044181960a202c1c42103a030528205802c1c840c08d00c00d60241052070219601441d0141d540040340068985174805809000c3c01070304440061118114660401690b100901050402d038070300514078800070201b4040e41c90002081810803520043c65041c130b0351481c58a20f82c80c0d55a110207012038500016090210381864000b4401148501003c504150744040402014529403652402008011070440e070440c1d59030f0175410805907011201c1e00c04c1c08082001d074658a49443e10a0504e40040d20480f041e440920180000a80015510741c0c0a038561404014117a0507801401d80101c0240c490009805400810b00760705030711400814401380b40340c080300c6115510640d01c03094000c0070b0701d10700d0010310080d0050000a1050581009058140c40e25440c2d0 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 248313938 1250 248312688 248312699
    0x20106090612031b05060c0c01060e0a09031d01200f10091203060506181311041a031b0a200a030e04050907030605061c0606060216031203050402010306 67
    0x1221055000016040d010b5481c00302096400340a411a03140d4070340c0c104402e50300356a80c903580e07590301520f00c0c001e20001152402c0344602c00d40c0b0010042480310343d80c40060605803d0f01c0c00034404001c041d8009003c03806400d040142d2208504c0600e041a500e940800620080450101074071483d0441070f4000e08110f005070b840304001c0e0368044240000700050013015841d0506155051801c0c100c249400c00c401008180d5844080d03030342c030341d0440200d824414140d000041d4513464100c5041c010501c3c2c07100e4800d500305030030084c0007a9004244801c1140207007489101060000b01c0300220904403080340d200c4001c044001030400300c0705070308200e14141c561580c108140019442c401c8200d0b44140801e50038140d000300d03000860034040e00d007004242081400e45031520114007020f40070984600c04280207032107036034a42c45401880e40c042c4030010014a841009007400e846a40014480c070140071080358081d501c1074040300d50101ba010005068020141c010303000080c400c0c2c0c14150f850900280 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 248315188 1250 248313938 248313941
    0xf1b0806100806070807050301060c110303070605010e0105060403022d03030d050a06090221040309170c031c05030f04020d1a1807080304180213030b0919020f1002010609 75
    0x303125054001071820341060309281c80c08000900340020000c042c0b06000c030168000741120305454451030145008035090501e08502d026a0610a41510001a6080511180c1d5000713605a405005202240d80da0b203404101186c0240c2c00042e6010100d525290684008c1d01000d0b40103c0003400580da030040c2c3c4030002070075a08203024100082d0303111000c00c0080041d604c41c160181c08102011802d05042e0340042503c14004440c00195240311400f140c181400b81000d08002d0000020091444ca020035a907611010000c44180c0a44288400c540072043e0210005458150580d10309045544080c0354a502000190099030404c40c541602000316910552101207047d1100510402d0309003040142c8900c410207641020302d4001d84024445098040f04031000c41c4c18209080d4514030344043d496009110b2030030540b5403c00c56140000c00c0006007140c1130b21901448050702c07844000f550341c004080300c070320400a511441d43c0007094071601e898180c010420b0000e100014119464912400 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 248316438 1250 248315188 248315191
    0x40203130618080a11010f0e070f0b030f04150905010f020301170c0916050f1206190e010909240506030f1b01080408120a0b01090b070f1b0806 63
    0x1144108009112000d01034a4000d01c032202c03010500001c0e1500c800e850b14079040c043c0c0f070001000c0000c200480019a0000d4002c0744070300098060800c40a9192106d284d80d65a981c8103204c540c8104100c00164603200c841600d114401100070902d041d81d4503914042a42140d821008402c0d54070701d103040c081402441602e4104605001c0143c5c1c0c1d504011481e909441358100600403540041400f4001d62030711440550048000e09002031048668082900c06020300074181842c110049800e92280395464035142c0626002d4940540c940e442c0501100e070361441d40510010100e0003401049081a81c0c1e2104044e603000742003481181d0780d0800d91140d0226454031000040d601c3d6802c1c06103e00d018000d404034513080d82d00a1400210b03046030600b03614200503505040c40842e400141c28040340d0380031a003504000c0e0011000500c0c00040c0b02c2d0040c8074003840f0500292880501064032a56441210516604485088140c401c290f0b0307450400760402c02e4100c8400c41c490800079564000b000310780e = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 248317688 1250 248316438 248316451
    0x1c09080d0504030b01140d02060a02190c090b120a03050a030603060f05010e0105040e15040201020307080a0203041a040509060904060216080c1b100f022e0c050f0a050c0c040203 78
    0x981d0b461460500307116071807042e08071605140c041240d08000d070b5562000b000e020ba41c19108a130300c51180720410b0782030105044201456840c0c0404000400404a010700251910a4070800a008112080c000e4010045422015541c440802100868013030400350001c1c042c1c900d070110325292641d680509582559515080d015102c83c014001c2200407000e040c0500800e950421041c8031303440e48c0940d1408044851035601da400d00100707056901c00d0003210700050700520015525001e0100080d900d61144c4591151a03802d212040511007081048504070384004140504580b030300400c000b44650058001c4030b4095003040440d050908000d01022164043c034501d54442d58640c0b01c050a00020b103028103811301140040c400c296484807402032240840e8509142580003020b0142d1401c0780301000c41e25100c1103560b9540e0b441102040b0125002c42784d180078418510040cd0030350b4a80203500c20060406028001c00b5000c0d031003200600419680002110105040200841e08a034400d40383c0 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 248318938 1250 248317688 248317697
    0x30b09030f0705031c230a090b0f070207050108040c060806010c02030d09032d03110a08031005030d110304050d0203010605090c03060924150702040c02071a0c1c09080d 74
    0x304541c0145c20122400a00360001050180c140c0320700c4a0b94080b4250a44404500c501d84003081150314954013991280380d000035480b540d41000c0440280c8008222182c10061140030300101e02d9500c1000c0c9503006950041c0d000c1e05250514a00fa80d42c560000c00b01d41c100400b510025016950030084d4030340c5404561501d480e0a4294244040c4010340091a880049100d882100c1540444809043c43d1601403408122040c40e085000d401c141034a500130f4000c0d0808020f112a881c0171620803011070348110201d0b241400955000e6841e46080403180c4825081070108000b00d040500c003007201a480100009405d82e1210700040c1c203c0700c2600c0740780040c10007104120550030000001604412020f1580781910381000e000b0807410001f21025000d150300d000c0e0801082030250544000981c010000c0c00b51400300080299588441d03c9400302000c1e002c1021816024484115080065414007400c0c0441a00084103000b9507526910800c101a05100180c174150500c0484100325031b550381c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 248320188 1250 248318938 248318947
    0x10e1807110109080403061509050109020910020a030f030b0f0303030103060b28050607080d0509010b03190309030809010507051c0e0a0e0f04141209040c0201110301030b09030f070503 81
    0x104510384298854259030f1602c59410701007209901034508503070b4042000308100802801c1322009030750765446507400368240030010500d070540780c014100c082c13420f941490034131464180c1241d82e200600800743c0820303004040c10b04180d00c41c0d048011040e80107825810703200c000320b01003491030b80241e10554842d80d640f00f084400e8585084400c400c00080955480420300060030003c1e030703c8a52050601c100c40010f0071404009880054852000216100304824549144014041c0c06100c0b0b08038420701840300b282c060080d1f142d41020010b60136030f48699100c0c0c20b41d91000c109a110340c14a50512500388400703c001030302004800e41c110140c0c480c203048041904005008104d09600180c4070b903650708410b00c4401012900c5c10b91108940790100741075101d500b00742210741d030307a41d0010546000303403c100c0d0b640c07195020050804070300503a010425207804850480c00c8540301321044282076002c0004001056130300202541080400b802d491804000c02900040b6078000f81046450b0340011a = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 248321438 1250 248320188 248320201
    0xa0e0f01090515430804030206070912060b0d0f050a0b0903040b030a02090109050424090b030703020904150504030903030f23130915080609010606020d0509010e18 72
    0xb2004881c0f55030101c50700054100059042e101c1c003108040032008900725240c02c0000240b070000c1000218a95100100302c0b41e5180004020303000485d030030b8001d841454007250403140310741032000c201c494031a06860b20802d203a9900001e400040b000503449a140146503006c00c544c286801e07646481400148010600b84c81c240414040003000c840d0309401c144810015142c502088a07030114030b00c000140d032000020016612000070f070308036582161420303081d070111081d80300c2d0f65a102140380a600400c1580c0f11041002c0d100c00003003098050304000c1080005092400e251500544541420b0014800350440281140d4040b5030940c001070f6076840030802d040c1c22004a07203d11100b4a84242c00801e0b00c641044c007420301001d01404c001c400928020b000a003140f100028198404003401501c004500b2400005080e010b0b00f003003400b8003400b14100e03580500c991003c80b00d554001e409119134044090f02c141e0444140e0f1810b01a004041c090b4654074030310389456802202125070031600740300 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 248322688 1250 248321438 248321443
    0x108010b010f0c0b041113051504270204020f07060c030b0909010e1509010906020d02040503150403090501030b0a050402071406090a05060c0a2a050d090501080406050a0e0f010905 79
    0xb07020079002c1c0080111250041011407a0043e40107070485268503201803440d002c901c400c041d07407100321041071400c82404203e060180b4042c038a14070446052009541c0c40710218201e448a1001c5130003040e02c14510b00050030a600070301348542e06044080d080c111140c0300c1006a4640c61000b40002ea80c62400c80780a250040520741c0001000f0020803000004000050707403a41d240d202c03441403508000011301500ca09401c0f030282c1d194010010b546a00daa601c5450194003c0d0040a02c41d009030200700b1800c61a042c0303d030340b1442d00340e81d8048202d441c010040d00148044000719130094064103002c0f496480d540010010b203072041400320b00703040021200c5801c000010b4601003454010900c0480801c0f00054050303000550000b1460796803102d200281c45600c0d100001880000403000390b41d804410300d40910b500a805901a0b034140d50b0300aa08031100111801254081040c1c0800709020404580c0310a60020526000040c0075081c0042e240c6441d03000003150b102030303444516120411000703 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 248323938 1250 248322688 248322707
    0xd05090306010b12071101020f12040c05060a090e071b0b040c0f060f14091203030103030206010e06010f110a020616060b06040b1606150f17070303050f0a02150108010b01 75
    0x11075980c40d00388002a214500c101401501240c204140034030b422520080230b5044034526980030480587d074041040c14042844811a41607031089606040051142014401c50340788107103d681e10301021b402d0071a92203036094090180c904020443c501c4800300c8012000414005000341d860b80c0047c5450302d040c41a03002c494000100078030341c8460400002d80c121442c40c00368412030804c2510040114241340746400350080d440c0d4483c10039103200b04a074a000c00154180da01a43c00da88071a82c9a40b0840511141030700c1583c002410441e51166003485010400a0516060140c0700354444a07000a907042c0c110036043c0784c08504907280181044075503c900071040900b914014106468a44031044901903041e070041003000c0000240104403165010b1072580003400e0010802e96100c503950f24904c3d031540a1402141d0601c0304201d20b0341400500c5908a03075050703840d80e19105007401610269042803040c1d03001e40c82007c200207100c40550b14518064030250000044c1400700c50f0004141146 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 248325188 1250 248323938 248323949
    0x215070519030b0307090f0e0703030503180610170109140d09060e0312091203160b0711061f051f0311180d031403100f0b0903100b04020c0d0509030601 67
    0x43c2814520035030320081801003c46250040c001551603030159003001130010000010444d000320000801015041005180290b941107910640d09218070452591600e05070350b80110740e80a58000c1160010804001c1c0324040144000f1460441564820604038440000d038002600240c140300703c4242d1140c06d040040102e480e0510306007003000046600da40e2104003104048000007183d400d25152001d41f00980300012044035614800d9400343c0b41040f812a400302e508003901d10115102c0341c8200c0380c10984000300c0e0050101c94440100500e00030758404400f80c40c19085200010342540e40e0310107191020200d030071100540c07040d070074018121002c02c1c0c036002c00c500c024840e80c2050302000089400318181070307071200803000d16810241e410b51040703008590801350020402c02220758101080f03040b502100e49400a460311442140018083c44500d590540d101025450321002c99411100d520000a400146014a0004e406003490200e03403161002c10f00c0080c030840c80e400e003008190300400 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 248326438 1250 248325188 248325191
    0x2060a060308180d0f0602030a05102d21121b03050901020106090501090b13110d0b0a05030f03180604050d1b051e03100b0a050907021507051903 64
    0x5056503102c00341070040151074800343c0c1c039452000300743c2e84481c00c81d0101117400c040c0c040b01703501c01c903d04240650b004a40e8025901d00700004103507001d403c10702210075a58442922000d041c010040003942c14030805000d080300102000010300341c400865282294014070040441c401c1c1c90381000700c0c82181c00c1d0025820462818a4440009202101c14100990510300503544900c0390004034050040c0350450742d10b040c41c01000042d02103480d400102440019280110312001004030b403000c40744a80002c440c2400c00704454072401c846c80d8041c00d103c00005101c0d00d003103621280801d18240c010032070000c5a51002800c1d940d20a03000e00d49041c00f500884c2c1a40c42c2c0360a10022070f40340c1021543c020111208404036005041c1c0c9081c4a0303000e010041c0003800d01e1001e02030b100c04101c540d484024003a025840f811100031040d80120782c4104800f0b0094600185004280b169200c0000e11100031800b6001001100e045104e0315240285101d9503030741d41342c13070360700b1400c40310095540944014075 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 248327688 1250 248326438 248326451
    0x20c0c040b031b0105030a14131209050a0902250605090f0c0310050c0c0105240901050a120305120c0301061707020a030518061606060e010f050418080a08060102060a 73
    0x80a00c000030f021802c10a280540d01c0b510744c03000000c0540368092070414155180d030708110161a400b8121840c4a02071042440820f0030540156010145801401e4006128034400c1c8014503860b001880401c4c680c04a8100604459800400e04070301040100d4690303442c0c009000804004203c900c0d412858000603020080050000030340e03915134088002e00e01601e842c00100c8401303402058030071420254000740040d26140d40d1032203110795482086a40f102008400701d065040040da014140c40000c1c10034a009401c141c044403003280c0f481c43c201c0402c801000941140c100e41c41c1c3e0240290002e00010b40c9035410030001074804074048000180000c100400c00000300d60009d9240e8525405041182d40d5511062202240d50700c0c0c54141d907004600021f41114402e031810705000118044e1303208216591300d510491074804020b103c0d088101c101500305201c6840e1550040f101801540c0c2c143ca12100e003a62071840c1c581001a10001041e040010040715503014031450368440015074003003025 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 248328938 1250 248327688 248327713
    0x204030c1a1312020d060e0c04050703060621020405060403030309050c09040305030a2007051501080304030f0818090108010203040b0106140d1805150a110403030909051009020c0c040b03 82
    0x3061a00c14000b0030f94007111100155224140070041c02034102e40203016075014010201c0e81c40420100840c0a1480d00002812840c841d2150f0001d0b0f4902c8d030f483e102003e04880d14440e106202a1034003205942c03c01c800030300ba0b80c500f4000d00046100e0344020504030107030708015061202d000004d90062503200c08100000c0e0b03001003280e9201c0c41c85800090075406900d4480700e26459004c0c5a050b403d400254207043c0300700059891781c0340c40c0b090062003d5a0300d03080215100c2c0143d1000510420800648000180c003030409404150169038200900842190024080c10000e0307124030201d0358004280810702a038084410b01601090600c50118052403660b0100c510944160a0b0005d69443e980d00068132180b000c0ea0800d508501110400d100c00119500116000d5441c620304a14141130b07403001c8501203040c4c5048039010b0b08e0310032102d4038021690001e850000c0001c40000800400803600c05482d1014001004016000780426820801840115810401d8491103948010a29201c = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 248330188 1250 248328938 248328967
    0x3111801050c100c03090506060409110105280e1f0e0d0507050d08121003050307031209060905011a040e0309010f1101020304051507051c0e0a05010204030c1a 70
    0x1112002840d090365101d201140c0c00d030401c02e0b600140041c0b2400c0003044418240d05030001c480460280302583d80c41e0705c0301400c005c102d5501c0e282c001c000d80e0703800351500185d40c0507401918068078101d03d10036003e0410484c0c00d200040d010000d5001c9000d50b09010000c2c18044a4000b002851340c4e5006c5442e030031088080c000145100c03a00d0300c0f40c0c20021251040140070b212100081001500804601d0b145180044180c1c00c0328035041c05071103c100000329200c51000c00c50303040b41d4000000c3c40c904101600e003100c2c0c0c242d448482807045a207412040d000180d15108541e000c50040b0000104d807100e400820b042e81e40f10305a000e00c076a04010003440d1a040100403101c0c902c00c2404d05a00e00d5642c0e910640315031104844105655101004003c03c1c44400300307810402d0741e0b240603201c80f16610b944069406000d025441c641000c02c10f01300c0300c880c4496030b200c0860f00c090b500480c2e0509002c1d90b0740f942a0380c0550000c43e0102070000c010060f00d03031070410019030007800480c1c0c0740c01c1c000c450341c0104 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 248331438 1250 248330188 248330227
    0xa0606030b01120e01060902030c0c0f12090603060a05090a06060f021617010b120a0b06090919050705190e0c0c0a0b0a0204090c030902012c0d2109060311 68
    0x3c00b41c07580c0c0ca2210340e5003082540b00ca4014906a4015900c07803400c0d07c014a03203a00448030001d0b482c000c800b40d0b01c0025101107040e2890000710000f181c00e001d03005042c04882d400007820507401024940340424141e032940c400b40d02c94414400e0200340182401402000c40c0040070402e001d540c081c2c11a2450f20f582c0b06224819610440c0c0812140c4a6400f455405442d000d002030760840c89111030004445808076800380d01c0d030701504d50100c843c1c0b0344105000003540101c0d402030054110b50f0000380c20380c080c00d95184c40785002c1c0045a001940710170014899100002c11211080b0080e0010883e104680300a41c0e80040c00e80209801d102c00804202d0700ca0402104c0280321011590000326007052030750546001d002c207040100700c61034107030a001d8018030040100340d02080c4203170405460404c50030014003019801000c0e061040e402c4005118012038120300480703080c2007001d480c0b8103d446404880b0818a60350b5038458580745801d00141c200c0703c259440d42103102c0c04001c508461451519440c = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 248332688 1250 248331438 248331467
    0x507140705070b0310080712020a1202010c060f0914030f190302040902040b0301090b2b06022104030917030f07020f0d060b0f06040305120c150106080a0606030b01 72
    0x166110350358581103003019503903008900510740120502c819400c0d4000010280c404200c12100c901d912224041011011070500030340c40409139005215521201d800110281d2060414000c00880c0f903443c6015151504034580341180d4400b001418008190200d014415912001d1403030f180c0320014040321482840c0c0c5c01c0690b0025407202c10b03005446a81100c4c000c10750a9011900c0c0c40d00c585642c48594020704c502c0c0c066900b00303411140146000401c84503a40d0744288520014640300c911030105943c3c04005856035a42800300029285129543c0900b501c0030180c402e0503483c061502404500d1160019250780d07614422501107500000200c41100c52450301c140e850391190720014100ba444400115041001622408104903141d00904054082118482901d14160040c408640903d200150040c0e0114040c4845015a00000c10302c2003151800c0e104044850044540c0d42c4c0c00030781c4804002900c1404020b00ba8219108813809405503140900c011f00801000808441009030032 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 248333938 1250 248332688 248332727
    0x100e030d09081b21073605070e270112051005040c080f01050106140906030f1e0403050c0105060409030804030e03071a1908040804180b060d020d0f0507 67
    0x40c3d000999628018142c04c00e082001c04042607284031030151070b20302d14440caaa44d0407420f55401401103004d0803500864000c40b000b40841140303c02c4c028040d002c0a0b041e001401450350200e8640d032145c503404c80160603101001400c0c3d411001c41c840000740d05031f028008030041d0080b0900002d4022508030b05543c036200022480352201d040001c00e07101564407810641c452a040d0b0110020190080380c122410b54949200150030700002072a01e10a281070140c0c400c20800000303190b01c005641c83c5801141d40d0007107200103200700d5a03a41516030196800d80202c0c90204001210405c2401055445181a94140003003c441c0c3d5005d0700c0d2180c098001000d0240820040c8219281041803e005140120914000304100c51058259500c0801140c01d9030b01d038510000344640c0038648680c040ca0b4044105440c15252084810072082103038034150190380c81d9070109c015659010040d14004522140050341d8414804489044801003105461010300702010004447e40000d5868015155140b0 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 248335188 1250 248333938 248333983
    0x1501050609210309100309051b10030f020c0115091a060304020108150604150806061e0c0307120e040b04050f07030b0103061508040c081603020d020f100e030d0908 72
    0x250142180290b03020304c3d8002d0303540480309140a6064010b18400c40c06001640d901c0104c00d101e100e010450003e8035900205001e50b20304000348203030b10140030707002070350030050409112800503401e60315a0000200c050007440402c0c040344a19104aa10550000020070b030740508034004104603000080002e81403080c1e240000da0141603032229402c1d060401041180d6490321224a0140400c614002c02e0003d22028001201401c1600880d258011030100d00b060a0f01100070059496001e108010b84c01d0009014540000b01c0005244490781200e4803084101c1409c1c0d41400219080c0407110341c03203141480700303000d44860a461565040481ca20300032070312281d201e006a018082c1303035000706036410b40c3d441c003101c1c1e0a0340b00c0c501e03501903403050301400101e595400c42c4a545485402c41f842001140c540104018504004034a6040b44080c1181e041822004009000d00001c075071a2804141d400d1205041c1d4602808151106140390424401050810100542d10f074120300006030f10064006 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 248336438 1250 248335188 248335249
    0x70f120e0310180b090f010b041109120715020102040918030e060901030905060906040501140108070b30010602071d01170304080d0507060f14060427051501050609 72
    0x12100d03d01c9801c2180d00400c0c0c1001003000303179151170b96040d80c1950b510700b64042c141c2d0329180c043d18480901d00c401c0182080002d80403c04501a002b031042d0305882103440006030420000c1500849003241d400058459140264107002c0c3d40300d01e00400302d241c550b0005180003035000f000c1a181030130281d518030303155101c000050780100f51400d0040c00354401c070010026800c9000032000e10030361081d07000380102e00c00309040401c0e1510030b004007030103904413007010f00c01003c402c009002c481412003a050300d2048401004c0070741076403007081070201d400a00010711a0340c0d0100001002086c40c1900003c1385007228000c81400303035042c01118541c10030b0020302c1151202c10000d0318050010f2000b5211440c0c6600c0015104da8030060f021a1650306154113411a92030750f20406200207903080c10f00d1215541d407410000100900c07800d0022038000c40307040d540344507011032000315558861001007030041c0046000c10b1070b00c44164003061003a078081204145a40303a00c2c61900c1e032642c1500c0410110794020 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 248337688 1250 248336438 248336471
    0x3021c0f0809100906062105060f0402130204060c1a07050f0702040e0d0c0b0c030c0405091806130605090c010e0d0f080706021b010c1d040e03070f120e0310 69
    0x60840000c3d141c1041c0803030043c8800c0368030090884c2c42010003c890f540204a2094442280303407000b070032070b0f0071020000700e000011520702c80c0d21520080014540407540100ca80403a00030b90009000170748681401c004000d0301c044682d10b111866100700240e460080c1000703000f03201384e00c4a001762440200301d00086445e05d030400405c0c00f4034802a1544d8000400e402030080b801c0d034000341c0b42e0704090004a1800715062040300c0c041e0b1402006149030905000c00c0c45400c42002e00790340f4850700c2400301d0030382d103032018441c99008482c0c0c80a91440ca5135103003002400e4400140c041d4007560026000042c2e076030380128a41400e003005940c0a4140701c014106071f2071a0044440107000340000007202010416198001c21200380124407201c21021000c44c1c00b402c84007000c00342408201d0782071241f210449410842c46201e85c0c014400308000f05480301c4241140c000f164200c17440820024610308010390070200d066008290b1501a407010230050000344e50780350a40c26416990355402200050781d00a = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 248338938 1250 248337688 248337703
    0x20f0f03030c060405060709090204050607061d16090b09010806010303140d02030c070311061b0d020706060311031c02071e05060307020f0d0c080d0c03180c0303021c0f0809 76
    0x2e041d07a4103403400f401c10305d4644004469440c0003030f00a20740070504c600e01b4800d07170b0250350b00581000d043c44031607070701c10303004042400505d070040707014603e85038442c80104014400740c0c0382c4004100001c0d16080300c401c1699040d40110340700e120002c0c0140a45c400001d50541100d1b01881d0070404c149200d5a80d0000b880744280c0c42c515540000100403070580044001c0034594441c1e6510350043c20041d0406803075070f4041e05d0300c2080700301c0c80340b5400102c84c4d80e00c00f52203900a4180c00524107045580c46604030348580e442128000b240c0c3c0f42c480b101e850140700900108802c2c002203000c121010100030b40b210803600030303074100000032140c80d0b0f001c024074440c0001030800503254540d40e042c41c130400b039a94011200310034a14440c180401c81e03064414888101490751140085003445400c854117005805c103010990201a80e4400381100d84401c42d170707000d8865001d0507100d8803c1341075090082c24050072041e01c82e91300842030055452280d01c8000714000c201c003440d040b115900c4411191b0f041469 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 248340188 1250 248338938 248338957
    0x30c0901050c0604060e0c100e0d06060801181b0605030103030507030509040e0c0406060509010207062006010b0714150c03040609020306090f0c0301060f0e1009020310090c020a020f0f0303 83
    0x83c03102044100b00d800e91007510348116103000c0381e40251070a0100005100e0550b1804009000c00250022905025812004c03245c400d0501140c2c09454092980c00c5030345003281414528044803142040c090b020800d14a066542d00403a0348482c20110060110b00c1b06200c01020000000340c031000f85445102039400e2010024000c1c4120603403007401594400c03a84110a101e14641100042c030f079030041e01129115441070f00909106031030068156604450701d000081e200c0c084951480c002841442003601030080c8107111901e0301c140e41030080400541258409150b40144108808140d0340485c2a0740300304011360880d6281e455180c6140a080c125400075010310903802840090000400c840f04510859001c0320200060042014240d5005100e940c00c1c660781c42d10103000c0d400c10041901d43c01100135181c0c040b82a5608244d5003240c0c4221030340766005840f880c083c480000140100304a0081c0351001b01131030b410790340001d1140b25000030078a21a0381701c0211181f0907101401680e4202c1c0 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 248341438 1250 248340188 248340193
    0xc0a0e0a06090602010b01020105061c03030609020c06091204060e2715031009021c081608120601020a0c0b1c090606060818071e0302060a0c0605100803030c0901050c 73
    0x741d4031203014040404a0080302e02650031300d2204010355105104071481060001c0140007004000c1c904102200c40c1d211080c0e0815850362008900071050b40000c03d00c9420b02030040c0305900c0e01d1b000803410700d161581a0417800604000c03c0003410f6000ea1801c6100b10101c0d8a03038901d018003004070b95250b02c403c1850444005600c20814030780017040b801004c4603801e80c2503510b0b0140300500202282d002131002980b05881d005600c0d0290ba280281c25030380b601c0b840d005490000d807a0a46100f2109282c0220343c680000143c100300840d285d2410754110200780000c04924829944440c600308140c0199040c401005c504100403a492018981810700c130b80b00c0c00c004001d500e08200001d06254007030b0a0202e41d10f1001300d10100f40411110508821007030207060214109103080c002c180c1080500000f4112103030011016031f80e140020821840c81e6201e8081300241e5143c00e800740e510091849500d8001000c04202d440d501000720b03030f03009041560499441d10043c4c01607c031400383c50450b08091 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 248342688 1250 248341438 248341459
    0x30f0c0c0a0308060f300a0b010f050a23011d04020417010e0303041e06060302060c1501060809030414040f02160b0a05060a14150a0909050912030c0a0e 67
    0x542110446001d90005d444410040003d6014881345441d400303c0900550142001030310200c2026a0700c1c004039800714251070403800c5946408070103103801e801601010501d640b040016240010300240249411035113440c0002c440c10012a841d4200b4001741e06200c0d495540c80714800245c070708061810b00c0100110341759030304d41e160900000001c3c088484a58a0811501c143d042d000055a00c203a034030090300d0000700181c8101159076080404126100c40d103420b00440183d035544050044047c0000091003001c601400342c4450800c181d105c1d105001000052123007036013000c0200c0d004d46911501014018800101180c02403405660340c101107440801c032480090610348588500c00d00070854903030a0b880302d0008070101c850980342c05a00c41409801006100d2104003a403214280091128a012100541d2100254400401d680c0041c190100501032030030b551090f01d130464400340080140d15a40c1d00d62101c00c0c80081d01080751610301090310102944030307a4400c040340e0809032014030003 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 248343938 1250 248342688 248342693
    0x8130b0a05130f081e030d02030f04030e01030c360603090c06050909060f06070203010e0309010f0e0a0b03061201020706151707090c03021b060103020a060c0305030f0c0c0a 76
    0x50b50000d00030754a055040d0340d000200d0701e02d0400c10303206481d440342c00342c0325840c00740e01c002511200d02410981d0501052245411030200d610140d0700c186000c40400c922440c01d450f0041010b025040164149071500e5000c084081d8040c00c0890101e810400b9420313000b01100c06508a482c0b0450441140e100160022a078180e25400000107107100f0084a0019509c82c0c40030b680c140580040e1a40089402d0001011840c3c051120704803081d010300f8103440e02619402283c2920380c2401d0401e07690b84002501d6440c0e50f40121070310b14400302c1349460009540c00c00002400010035100d4201c05500101c0403510715514404050300d80c288460007155101514949440940b03040c684002c00101c00c141c0010b00c0c0c01020b250f4144606051000d04006d40c2131080580c001c2540d030a074501050350034050318a240c4051100154901c600c030008120b59072444c410050305464541003c0104685400008006500101581c0c0c010a0300c2008200f560b07100c12004402c0d0080b10b1040402d0f1040a100d8010b = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 248345188 1250 248343938 248343947
    0x90705120705011e0507020f1309140c060406020a0204050405010605060c0601140108090a260d06210c0306200f0a030e01060b07030e0604091416030c0c08130b0a 71
    0x1142c1c0282c803106120082c03124054940c4c0030892000307002c244200b04c2c0ca00149440d060901e8101c01c020402c030150f006111200b0200c80080ca01115100c0c104058001d80280812903810041000c80300d4500d01420000000c0d02c800102a0003802661a0804030301004429088240a0311010b003109803542c0604000b240d68400a1180c80220000400248060f5100f10100d910950030b10340180041401540c0c0d8410110051341e4166104d03050b440c02a481041c80c07402400a9520b9800101e1002c0c02c10f9a200903041c0514030a406030007024200800044490b050001100c4e00480002040765011241207039076004130000850394080001c55581980070f4101514420703020350750401103540d20900c01402c0355100d008500541ca4180042e0300068807a0350540d900f05030241415061070796950002081d1406024000c0202031003800704030049404420442c4e1045081c42c00b48000b035144000a07101c107114010207843d1000011f24006a10b2144004000401d100f1503842c3e030342c2c040841d0041 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 248346438 1250 248345188 248345203
    0x41401141c060e0d03060509060108070522080307060f02120f0705071b0311030f03040b0c010b04150618120215070b070305180a120513030602030702030403110402030f0f09070512 79
    0x4c0c0400e00d04840410141401ca00061040344103846100e15516682c2c01914650401100640d103409281803d04d26209003010f2080140441c0e03004503140c9920f864007030159064258200104ca20501140d00c18040c010781030380d005008075031040c555403200802141d040c40b4020018212201c590030710250510390b0b429a0048a000d5002c454056000404040e20b4030310118046d00300360710030700040c03000d40800380c01000760079003001c00014031a0907040401c09882c40c10106462044d1160000c0000b5a040f1440700400c2d40455040d0404c80d0800c2040783d892210110043d006211110f041981e403c558011550f00c5500326401071207034a01031300024080c2c80c0440b07041c00c81d82000240c0c05001c0348005000d001702c40d40100b4a48002c1004071040360316402142c246201c2035000c07940000810a03620007940178500d00da02940c3c0e0740e0304605015810840d1800300502540c4104100210b60845144180c3c000c0b8000d02c240c0510b807241401149400d2140d000385501607000c481c4080c00c01c00000303455 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 248347688 1250 248346438 248346463
    0x210a0506010f0824120102030708132004060b0705010c0e030a1a1f14040c110c0103051801060815220b07022a041401141c060e 56
    0x24045550365000440303680c104450000c0200360740b08003003180c09190807190054149105100080d082100c400103070910303c6921040030303596000040c40901ca500c40d050503442100f4608e150260708490340d0b45030407040e141484180d901034111a00c1c110f076a994100000038200c4000d6983c03658140d040c941d00030001b07010384c4c0b030105a0282d1820724a08000c244141c540f42c01c2a0311040c186014255680b0f81c4600030841d81580400d4802003000348900d171180c03005803040660041c0d00450160070310003151280401141403004010103204801030005289a8900081c40c01141c1c94131124001045031040d400071500550901d0804614000002550320700c0030700c920303c10314203600d6803800602005030021800d102a10361403910b4003c00d0402d4001c5802c071810b0710443e00d182c1011404c5103c103c0b000c890203000800c0e502440340b95454a8001c2010090300d6140512084d49882c100d10500a000350303241d4028241100002d41c16108803552203000c54020105010300244000c000b6201c9495a42a = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 248348938 1250 248347688 248347691
    0xf180b09010e03070b18120307140105010b09090a020c10062304050405070303110c030304030c031103060f0601030b010e0303040b1e030601080703050606130e0702120c0601031205210a 81
    0x10b0804920f800200031088805d13100e5214a840211610030100d4200b60480b50b0f0401d0b40c081c05030308014810402400d21900500349180005445c0d4106404c8d60030691015035010380c10300240d1150760720044855003142c541900181d03030742c0340d500101e810500322101c202c1c8280d2a201e000101000c985101d100c0d000440b8a42d081d8082c90541000119203055802406950040900340000390080b82440c0c0880c0c411812100101d60220010707240d580260000c40319003441c1c117010030800840820700e08507044210058252851708594062190034004c16030781c10141c540c0c40818040e4001c80020300752903030140a80b55205e03103d032883c0c012940107070011001000c50190080c8008034002c00e49003d03190581d50b10b00c5a445244084018010103000c0039400203082005000300490039042c080200100707600c0c100c0e141750001000e81484000380c14061815400c22031401d0844c1c02243c0141981d502000561111501140407104c50066807540048642d00390014600002c0445440340300f074001a00 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 248350188 1250 248348938 248348957
    0x30609040204330b2d0706051f120201020d1b02210c121f1815110c190c030b0108031e0406051c0e150a0507080603030403030f180b0901 60
    0x14500500d00c0381c03000d250000e00f0071600d20040517108207454480c490a4051060400519131120030844a0645065400110219151440c4614010790b903008060410b4290420700712074001075121240d8490010400c02c010500c90780c00e541140b0086074a035000380c0782d18003404a400c6070000d00c040742e20007405140f0403510a41800d00d08240f002c040c854480000d00f81c40b8101070900309001100c00741070662280c0f11080005100d07860510201d4190040c4007400340000380d10080400c4034402000411480400c000080070420b00242d000000403441515032034480c4c80c3e0900141c3c8401c0c40c1c10040c1003120000c00010b01e4600040604031501c034600210070700c60f5991072804420300c030314801c19012400c103110340e000340002801c080e43c5036010041c0c081400c1400d42d40b114106204040034400316164801130000c3c1c40b800344501923000301c490519444900340300700029075a0007240310041c2000315031082032004034402e550010011104031100b42c00903481e103243c0e07001a0025030002d03000540411 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 248351438 1250 248350188 248350199
    0x1e0c0c0503070303052203120206070e090603300703020f070b071101110f0102160b1303020307120e090f010504050f010b030106030e0109080a0513170303060904020433 74
    0x1602c0003102e42c5030b1251440c01079040c641501541d0450460608046108800004205c04410001c040c02d00c1b603000d0202c51421150161401c6209008940600b100d4420004d0b1a00e00052400f201d62031090a41e5040300064001c00c401480f03a501c802d1108004104002090340008104094441420650f010940c695075080e02d60701440c8400782943c2808401c000e0700754011807482006100341d1056500b070088a03600b1a007681d100e002c440700102c49109824080c801104800c90b08001008a840714080880e14000d50f07a010b014070141811086904c500c2d00903000b000d00040c43c65019110901c180380051172602298003d2150900807400c18001490542c2d90343c90441c10303541003034080350941e420860100c0060504c90064903181d96103c40a8001c07904c80009814a03808690340c460707803656070b1004500c03111001d5006c5140c035203400c03030701c0d81c4451070105c180c99000d40300391032811310b40d03a690000034003410400c0d821444402403c54117001708903082c0050081c2d45d0115514200195640 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 248352688 1250 248351438 248351443
    0x10b03100b0913030e1e01030614030a060c09120b041401050f0c0c0f0106090218031207080f090405070c0302010c0e010e0904061e150f21031e0c0c0503 67
    0x1107100d41d0b0300441c100c00044100c0040d2030311440c400d000c5d01e0700c541d402503200b0200d01c449081c3c401c1d59541103141c10b502c808030341e4075004020161a030312503800e0000c417407a004a941c442035440e0050a03030340c032281900c91180c42000500b008207075164107901700f10102e0400c0c51029005880075104034414844011109405002d03a5000740d00d1004400a0350350380ca20400c549400864120350701d0301401604e005418401d0141c240605016100182d6811004528008a003001c0c1001030281d0090301c98031070003400070400d8600c15500894803da55886d9003901201600c140404a54003d10f05400e022100c0d40c045480e00419129070020481c02c1d41d901003c1d241c02c0740d40e030710382400102030703410052072803c0c007401c0590880d11550001c03d00440b000d894490403d19200c1268490340c1da403240c0340340da00544c00d0080003400c504031800f40e00b03420408040321004903081d818540c4406131a00b501054450320303c1e5000144c20b03040f9680c040207131100080c541805c0240a80780b80300071140102d5145000f = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 248353938 1250 248352688 248352701
    0x1209190b0409060f120b09010e010603110f0d0b0a09030905060304122d0315050406030b091b0f0d030c0204180b0c0a050712110d050c06090607051605100905010b0310 73
    0x304651407030b4071760b00b07640e62000f900e0010240b030b48035500c801101c1c2007040c00340200c60255204044c42c0045400c82010f011650000304d020500c1614104035020206034028030b4190003007c07038100441c0d01c400904040d101280705600654111000104110a21189102d091b0f4004540d9031000c0350309814509502e2100c0303001030f6000151045606201109000341c2c13020340e1290120740d03010b000325500e1000030b049404640c41954891030110402000801c05e2100211540d105d42400f00194214000320700c100c282000990300441140e9030020a0601420f460400603a0080c001d118010035401c440094003030050302101c2c020a013001040900e0f4600c3c3c10f0316407005e07e0360b54082c102451901e5000481182011030418410310710baa0344507004041c001803d0304c10290b100c1940c2c800940b030b261803510a0041c000c070100d401c490203000040354040201c45585210040729101c40202d07040081c02c04241c1c201c01c01030f01e071401044070f0030000190000c070a441030490036681800700342c0c0b03090401d6400 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 248355188 1250 248353938 248353949
    0x130308010b13051201061d0420180106030f0f090203060f0c1c05180a05071e0807080c0901060f08130305070222110a021209190b0409060f 61
    0x10400148051010400a00000414001c4100103156103030042030302042d15409000e210394448100303004224004c0704d180710047c6c100c03040700c00e03070728143d1a00c1802261159505003080d14000e40046190780b15000d0140c0e41040c400342c01c9003941e403281c003d0010409c0301c40b04030003541040d200942e030b00a030b031241c61551030b00034001c0c0c901c643d00c1c010b815104070802000c400803904140803007900600b8494400c1b40312817002000050301c1c20105414150480c26512100495005075074400000d5000304144040b19180e03605080000f41040f8900c60800803030b00141014031644000255041c0300188041600c0d100344c0b0801074590701c411080f98031480414180e0041030158002c01c502d414049071104140d802403a185040c81415800161040e0803030860f0402282c1b01d03098640706102510880d02d01016006603203150200110004c0d441e207071a0940100110310110381c132003076074441c0c3e02c405040401c04190090105e031503d4103c0c032141c1042c09441c1d1241d00e8440d01140a09030354050805481 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 248356438 1250 248355188 248355197
    0x5100807151205060d05060405100b0409020d170d0e1501080120090d081813020c100906060b070c0303020c0301020405061c0b120d080f070917030c07030602040503061303 75
    0x100310b000980103840b01401c441d8100c10041140c8020403000e010460081d48160b014003201100150b0180030743d80c013184110f00c102e01d0081060f0041c0c0d101c00010ba00141c2c451024205841102c8d80c0c5040b0340074503003034803030031504000d4500032016000c500c241500345003048201040c3d80b071b06140d5080300d040c0170a54483c0250100340031010403075200a045101d0004180451a03101c0d07a4070204290407019517101e414070656038082c1140b801a802c40303d042c4a048003141030070400d540302940d82c0324034030750f120300740703a0320f96082d0248001500100040c011120306156512000e140c218103203442d5101c1078005000d14401c50409150600861302240e000034081410b00e141c0d2000e0103050300001034086a0a581c42650913025100c49500d810505c1c070300c03009854000f09840340a002c8190050034401c40c0d0b4940010020120713009001c060503900d440e07140c40b40310500c0da244513140d4400c0e500c0086151080c01d00020030401c2c90740041040d00c405606503000742d15011262848a841e0410080204 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 248357688 1250 248356438 248356457
    0x5120a051c08040b0a09060c08250f0507050703021002061602010c080103080307110607020f100915050c07060504050a020f1c080a051e1305010504080a031b02040510080715 76
    0x500d141080c145c110143e00701c0090b00301030a9440390300b00c03021941244082110340e0200512001028040754000c0040d01413440070380300800b00101852100c0114500f4440041001014008100104009180d000e42203800c611118800a59500d07822140c14042000000740d06004901c1801001300078112601c4112940e401d583d20042d01c1e0300002c0c009010000c00d6030000b28000300c2002014012207032074007d44044448483c045003804e0302d41641003000e6052000490004000340321850720003003100c200180c039032659106565544200f4a024003258145410311041c42408540328103514800c451407a07140c0c1d0f070034045c40500e0f07600784082009016401c42041c0400c00460040091343d1491500515007038450104c148a03020102c0145005040845d2007080081c00340001c10191200f42815803c040c41c085040b0398609103498014208800c12103140514207001200602c410350060050103d450719642141781040f485c816500a842141000030f45007140c0381040000c0035459803251a503 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 248358938 1250 248357688 248357693
    0x80103060507300509010606050304061d10050604050105010921020f030d02030304050c0a12060b030304050405180706050c07052101020307020f07210b1005120a051c0804 75
    0x3014002d003614140070080c00440010818000e0310b000c40c81c484003150011800840f00d040458a0050201400d82e14184040c017459401200341c0b94010392004001c90000c10f440c228006210170400381301c40d00d00c0780e8640380c96011030f5034003c1e82c482d4105a5081140d44c1c1e07100011902c16a923485220480d800014a080300820025003402e4141d001400001441c600c1d4000f0038a8144010203030401a0008401e110410a00f40141081060115040c0040d0341c1400c502c2456010030540084c87c0350307680c00c1b4000d201d0b1401d009840c01088003c100308103500c0c043d8440c2c2d81c420000e4249501034080e1002c0420601d015130300b690910800c1d2401080d01038205014009007845204000841070010170f44004500000d00046100b00d50300c6e030144c580c000061701072528001c480c0e044442c9081c41d642d9070303d00c00d400d05000c43d540a5001510203206440d04143c9501c042c40c070340c200b03640244d0702d604010301c600000986001454840c10485000c40b030028031803070b0000c4132350391041c0000700c505022501 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 248360188 1250 248358938 248358941
    0x12060105071403040602150f0402030304050108070e040908120f0408030c07030203040b0d0b030d0908280c080c0321070f0215160312090302071e0b0c01060e090304030308010306 78
    0x81061003210009410030044800b1032458000b9486140144d000001808501c030585054a8200e881c4802442003810716600081d00d83c0076a00926042058940003d00014490901c998203180e000d0002c010706815400d048070158070600e0030740801c2180c03e012032081481c5994140c0701d2904040c1c102d0031a107039100701e02c1c407690091405408511081c031007c03070160302d428001c1040140144000642060500c14182032034144044e0106000c50103c04015603c3c0c08188035958280d2002450a50302d2080340d142c004c8291014040c101980200020508140005484800c0c0f0070803412a0120484264001c0743c013060100103115520061082c000010f160509694909100034468071001e03040b50708441c59034018401c0300f103d5028003d0940107044d00207022200c3c06136a00c405020040c02501c020395200001d210300c0750450030a5006510340d12594070014082c0a5100041c1e680f4424a041a0301900050261501c2d56955001040407660004100c5c0c044a604d0b458002940e0728580300c000 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 248361438 1250 248360188 248360197
    0xd020c011b0804090e0c0a0b03060f0a030f2f0a1205070b030c21040206160c08010f05060f0409020a09020706180b04030e01110a0b10030507151412060105 68
    0x4120705850740505001612140180014040300c180000e40b004000611034507140100013181d0094040351018003043d0511000c0b01d90050080c0c1d299520700e05400c001c00c84103580e40d8405051340041c00860b504100342150341c0c044613070322901246a1401c030440d07201c001480d09181c09a0007028000200490144075400c0404607019005546000f9030340c0311100c3c0c49134070450307012800c10b4001134003180d5a5800f100c00d0420302c03030307c941e03c43c001d14041d80450300c9031203001010f0880311040c040d06020407006000500c06405450001e01081c11590082070182c1002e4410520444803419141d4041c101882003580d015001004082c0280c0b4110411009500221040e035003a0340b01d200c10510301440c0c0b94824545482204003d8081c0b405044c01459042c0c1250454100b0580300f0fa4050400e2001070403c40c180e1700320400749255111000f1811822096a00050050203801400542d0b5903d030280070550007995110049107502294035040580b0821400070340c46041400420801d51281c409032 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 248362688 1250 248361438 248361467
    0x40303140c0303090703050d0c0c12061b050a030b031207031202040302060a050d0f050c1801110123071110020c0a06060306060501030e010e06010b031e0c030f07020d020c01 76
    0x451401d070901904034103640c401c80d400c20455006070b108204002c41003091011940f1145400b698038046541c91305d03800030043c81a1180100041804001d000207903212600000c184c0d41074140e0014685005000e60700304502a41c003091801c142001d19080200c1d00b001905c25902d2650301d01086a90140d40f052100110700700c5013a82400040700503281c100040540051507140c964848200782c014100b50b84079003144000e098144001d2000f005211000c0e1510103200c00c20800244411a00495903a8a0940050030315802c0903000e802072903c607500316041c4c185001180e2030030b40d1010025540d5405056400210b40c1c071510004480b030034598050a0b03030000c544295510000c4d9030316908c05407070043c1c10030f4408035594a0100b0081d80c04d4070a0313a2003910f0140080c0406028600813944a00c0144100440c0500010008d400030500c1c80c1450702c150007481d5400380c40d040008104003650002c40700600c101e001000410455400015000703040300032580140f40f4092140011198100b102849 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 248363938 1250 248362688 248362727
    0x3200102011803201203160f09090218090a020c0c1503010608060a08150603060601030b06120402240a02162601020c07060c02030c011812110a0905060109060212040303 74
    0x24502c80d4130342071100c9111101c012a4660f120704103a0444001d03801081220010300ca61409080100b54014032410200d0f1503004005840b0230405000c004100c1a5010480c2c1c44101c134400c108040f0810303030103001c1e500c0e15402260040c085040500008656060481c0802c1d041400100071390ba21507841d4560214000c0d08000c422076652951a1510b104d03010302d00303070220401041195030b0408000d216031180c000d280500c41480c0c40e101059662103069641c03d03281c4c0c00d0200203000d41d101c1c45d00c0307a8038158200b644051500581000c1020340c0c1c00540c00c440041c02108a10018401c540380841c0598941d0714808c07544102d8400141e85644d40d05009410554091003d1181d030841484172100800003a00c030740128400c144101410080d000049606105032994014000c0a1050800040d03402c080c1800f000d0000c0c6080545146030040541907019201a0001c40e280c40b1a13004603010750000e803910a1090746840c402e03611051550505040e0040074801000824400d100ba0526400440c90 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 248365188 1250 248363938 248363987
    0x21f02030702190605061009060f030209060c0a08030118020304021503070309051b090c0406170907080102030109090b09060108060c070c0509100303090b1903020a120603200102011803 81
    0x403681507031062403d00344d9801d9951010462182070261500c0140030700c500d00340d40c2c41414140c0140200034403580c000c0c10158081500051a00e5042c00c031030110b07000d84d007100d80d43c0c01d59241081c003581c000d02030205000d07a94030030034410300070500a9074083c0c1d60042c4041039036900e01d04502010b81001740340004051300d41240744d0110364180991043d0b800c110762000710b404202024040714040240440b40461000c000400003079a01483e02c101c03c0c42c1d0500c010320b803034071005001441c1c0344ca55000b60500394030010001a032184a90f100c0b410310b0b07100d404c403480c4940e030b450206a10b642c024440e40704181c010303100080c4041c4444004190300340c410303c1000d060984501c0400c84180c02103507400d0b81ca076005002441459007040005004050605070079203001c1030040304c0c4840d42100034103002416000304049070034034014485841a10620706082208503900d080904142d50a514044081030601d10b100000d544180900c50603448551803072054860259800c4502c1402c4c00080d107144a8000b1 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 248366438 1250 248365188 248365213
    0x10302030c2a07060c020d0201080702070b120f09030c07031203021318050c1602090a061508060f011713020a03050625090e0708040804050d061b021f02030702 70
    0x100004040b2003403107602465410003404645410f16030707040035080c0600d201c00c03840169a0381516101455081ca070518680c1c50300c1d00c05911700a90b5800103000c2150109500c5810b07000d58071440e108640152900348151140d0089a86900c145120495550800982400450351614140c43c01001c1442d00520700b9156a9811803800b0071904107000c0c0240d4000d9041b4035100500402d500507500003096440c0000252f0748880b407107000000240684038840c000b80c5051195401040205645401e80c0c200114050001304046811104588121103003e0020b5507940304840600410034400682e8a5544595503091104004036401b207a001d0b04041000c400203005002d0503006010f084102c0c018691500714084411039150182010414800c8080100c0818440081e0308240c09084c070100c00e40711418410300034840c41d040a5041030700d109204007000f5036503210450300c851002c420716900c1c8484108a0312018008504514120310208101000b2016401160801d0f100e0044481454020 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 248367688 1250 248366438 248366467
    0x102070f081e1908090405061f0804050307020a091b08070e1203071403070b0121060e0c10020c0901090e07180906110d0b0f01050307030e07031b06020706050711010302030c 76
    0x45404c54841c2400b052500490800e4000d10381c020500f11030141d94490010001079420001e141d035a01040404c0c80400d0911030240200e40d000c1e50040c0003000c0043d00c070301e14140640005140391100100f0407070314244140c40740f1040c90198003d07540700c0300b0302d4800e8020011280d140d14460442030100704188000a0002e8a12449081c0e801c400703952110000c0c2044406402c1c140e1000707070303241d02207201d40303000c01e0341007a0b01d00c1490fa01000024914298052003403403c02c08126140e0841c95a5403620700141d0001012115464101d0309104260b8844181c071054402003060342c0c0341648400c80c244220b200080b820f10001c00100c400140000554032190f043d119142054080a80b0029800300c1d00c403840d0090a0301840180c0740e0407154420b0100080c00da00c402444c03501015501d04000041e00c400303000410046800c400d14507040e0808a801820f5000b482c420345015120740d890008660703010b84103075006135420402c91203103419020019406984028442c684401c41044075000700c0045 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 248368938 1250 248367688 248367733
    0x4020f190f0e06090108010204030503030f07030207060e030301140f0d02010f050708160c1203091403070302060309060f090f03040308131203030903030b04140c0702040e030304050c0102070f081e 86
    0x107035002e1101d041c20f50030b0008101068201d00c405034010001400450300000880c0c3d04480101941106680d804600320024000e00d1002071034281802c4240c9480301c8000060750599030b0150300c2c1401000c01104111203e070100c1a0303a50080810714001000d0740c021041810310a840f405c00d9483d001160343da514103a4400046140040b000408440c240a0311000c114090040381d81c00d1210b20341c039620041e02c042c1891003210305a0b000d4001b070340c0742e640b414090342c402194090304042c0c5a00304150000d485060488a0000c030441d80700c005942104002500303014120079601442c502800c5448004150b40014280c24a40d03408100006000910b00200c0b03141c14003942e00024420003c0c64000d040d50008080c3c44d104505040021344030140c941241d40d00200c4180000e07603100400d10109014001c0b2204841660001008010038040089030540103a5004d81c20380d00026114124102e030071625008040c0c2d01e602103103108c80e6010301101c3e0020004140000c0380d01c1400c18a52a0413618031 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 248370188 1250 248368938 248368949
    0x20105130f0303080a14060d020a05030d03050f0a0501050a060f0e1002151f09020c010b190e0108191401060302060d02040602010e0f0c0603102309070804020f190f 72
    0xd0001001031591004d95960441a9500103000c003681c18003221182880240016101e0746181807120219520074515a00911019040d200c18070888000940141811140d00101100c00c000040008040e4415141611001019551414200320341181c170b000301d036403558050002c034900e00030842d03031040c00c0c90a801c10382d9401820404980011b03801e95010240c40007403160440c40c050042da0300c42c100b8040648415880050b190500301410b5800360518030b071025084041c00a403844d181c1c00c0e00c070110003a240352004600741d503660396131015030b40c20742c84100041e542c0d08a0307100c000040c544000c04042c40341210010884a8403500040c1c840d5001000c0c845515500203020420185c081c0a100c00601028024007201d024060210761175038012081984107072000400a000e2501410390b000c05044980c0340201c0f904428040704142c0d450b607050085c8502038180002d200b5a00c1690303a2481643d015228000c45202c10081c00a440c51002d001461380001910100c0c0742c4c40440c511400500 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 248371438 1250 248370188 248370209
    0x3020105190e1f1b0b0712150b190e06030402010804050a20130501030c03060e120307020d0e0f1813020306090a060c05040806150d08160302010501061b080702010513 73
    0xc000d14000e000311000c525615042c13503001e40f004010031188051035501c000b07241006550541850103100c001c10740c2e02d450b001851881040400c0152000b0702400707800c440c03894100a00104010150b4510114003141e59001c14200b0000e8019403181082c690460b00c101d04407446503106949801800504504d4003112402c0001000c0315440c20249151184140201c204125415503c5411aa160502000e0139070780c1c8401d1031011860301040040c2490072886c480341e480e81801880291602c195601d5040000e41c5054a00c00500d8840301c900d0032a00000c00c07458903101868040485204010000301c0507504118050002d62030510026200c0c080c0311000e40709980070b44c580b400440f03903086034502c2045014801400304540008490360070640700118548150916800a8042050044002d258a4000c100c0c082441624240d41c1c0312184a60001d100680c5c03203841c1122040200e0a880d100d4810265810000c510742c600203251250062506516040340701c0c580d007400541c19030012801d00d = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 248372688 1250 248371438 248371489
    0xc030c0b0c03030c0a0c051b0f0a0303021b0303070b0103030905030d03110a031508010204032d0b0c0c012003040b160f03021c0912030f050402060901110c120f0f010603020105190e 79
    0x28a46181109c100c0e8004482e142c814904644000303580740f0021540b16422640d00084071160b56082050340c890552010101309590385034174006084103854410b0b0f9009110b291040d0100e28024050140c0400d10b00380581e041608280084019090300712100b00d02c0044da076800308444500380020b0000e10301668940600b0f08a00c180340141001404242507840742d40d200c5800056075009c11980c002c81e061218613100d1000d442014014940c2811001d010f0b4550707a180c134401e541b0700015501c6140100302e05105a031384d00242c0011400c81440039000100e0104540311524021b1340944812010055041070500040044034200c4c1c45000c4141c0b400b180400c0800c0031254180a4032000d400c4400081c08a400d040d80412598092405001c1c1809840d24068614a10400c078912402c0c00c02061140a105891812602c82001d04114032180c024400d184052034414040e540440713606031f44152420500419480400d843c1c00d08082c204803071002040c540742d85030414030300e00d0490401a540c24 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 248373938 1250 248372688 248372743
    0x7030609020c0c030708030310030b0a020c190b0a0c0207051003020c03031f080a11210a0318060207121115070305120a0b0f0f060706090c030c0b0c03030c0a0c05 71
    0x300003160f0701c100d03a47d070300c00c1003088440a244100f40e001c480e40040d5640990303d459030150041d00803024018080d204d80c0140d441c8200d0403104100c000c0b4064480c00010b511441520420b80b600d64483c8030259008803410849801c040f620f00881440c40d140044c1800c030394484050440d801901ea0590544082c0743c1001010481c0c0c0c90ae400811908005014205281d034840e140c1c0031113103075040c1c841c010580c0943c0302d8588490130042c1c0c1412003802d662f040012860007600c109190080b55216800c1041c000c1082400001d18805442c0680c1420040d00300a9840c4803040d146012201c0d0011140090812206104400f074005e06200740c071090380302c0300c1104168605c040c004258141141c100044210720303403140801c65006500541e9191905811040490b0b840c1c4601c0d400100910316104401e0305000c40c40e501c06c01568803507018003542e16520f0b400701000b4001da0440322500d80041004c20340e426003c0005042c8040b0909003801c0d0003440e42c6446080c80d2240c19552500041c10380b01003007 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 248375188 1250 248373938 248373943
    0x90a060806011e08070f18020f0a030e01061202031e0a1202030706050f01030809040f110c0a150b1e18010806090106081b010c080d02072405040f020907030609020c0c03 74
    0x81d01c074540051000c01d00d03282c01c0039031b0b68500780b2554001010b82428031411f0704903601111520b00c0015030040e628010752000600400780b40f440d89400c2e500e06007001c00e05064458841400ba030f0024020844161290311291021407003030941c44203841016005000112440400010814a5005180c4403011400c3c607606880000300a09803000c0d640e00144005513481d4280c580d5044241d800040609408002a004003100e85101c0028079021410f81509000050604c070018810042c036074121038094034601c00d075444403042e543e00408900f085003500b180035000075801d560040c003005442084c510301004159080c6c0111060344c1102d801c01c80000024007440d40241501e01c001d2403e545804074407200c1140c50341d072150400c900050f016040c070850000346c5240c2170a00e00d0465451210345000e407100c4608200c20b1040300040d0b84c0000503d0103c1c440c0e180b140f0f4201c4040000c60840d5400c02504100c014112401e06a840b000440c1c0c0403590302c042c024600c2200014140201044d00305031 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 248376438 1250 248375188 248375249
    0xb060d14070315120f05100f0209041a0d0f05070504090f11030c150912010608160f050901060509061201140a050a0b0d09020a090e060a0609090b06090a06080601 71
    0xe030b00b1154071608000760b1401c158490002c079004110560081781350b00e405401c000c030f915407802c501410050100441040c03540145125202101c003001107000000c400c2090710b4600681b203500601b4151030f40f01050318003030341d09183c1d4404d01c1681c020b2034903000050220b489140c01912000c210303501e040200a040c401803001940c0850080521000310710011700103030a100c000840540012a070540540c40380000718004401c210020302200b51520b68403617503480c8400c03482c5000c0d910b105000405001400700c00040e154090003200d101e17803d0050503101035000f10b00c0207070000b00400041e0902900c0303270300c00790203002400c003d4039041d8900c0003008180449600150f120f00b4003604100062440c44080b501c00307800d01400402e400030b20303000203110f00880e9401280154148600045200c2c0013180740c0388a8030341d80c042080f0991301c45903500101c8040b400010500c42c00400400e081d40340c64090306a106812000104000e03840361406801c0450a921071010148840e4010343d07940c20492501 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 248377688 1250 248376438 248376461
    0x1b18040308150102150c0c0c03030304060e01060e09030a0e0627150a080f04050708120a031503030c030315080a150b010503040201020703080a020102130803090a0b03070e040b060d140703 82
    0x4200e402d1007041c030070140440142c0003003510a800501d041f00d102c400d02c462040c0400c01802e49450780f0305400c0110241907035242d00360b00c651074040c0100d904101502c8040c083c000c810019070404240790340c169851100e01100603031202c01400701360607041c200c91442852203a01040b002c0800309000c207000508042c0b094000011b842071241401e040c2d84022056403000940c4036404d81511a82083c508010098005038810702a00b81c2600a800100d4010020181c02d9581040803203a0010540c0380c1f070049000050010354003d1940e00030074820740080030400034200b00502030581e203440e11490259008001c0b107015020107188030f041c00381885040d40010081c2046860761030f00c1c2d03000030744640c0c45000c020008030340825030501044c401d6060320f54100824242e82809a102c1c040c0e295039070070800d007240c80380e1100d94000c030704000240d050f24092580f9844404081682008220280000d01c054640005043c0036403000c040113070152908180480b00349405030704003100b0060680311006d049 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 248378938 1250 248377688 248377693
    0x8010506010e0d020f0405040b2512021b07080a020103060504020f0a110c09071706031c031e090b010e0906160f12060b040f080f1b18040308150102 65
    0x4110890342c01c5076080d4240310080307441d1605402e1500c001007244c00c0e250010340e002032070131080108020030000e00700c0c0240c1c11003814000c0d01c2a00d10001694400540c240d01c0001c00c012198440006960090700c0b00c0e00c40716a4a1849416240e0b035149003846035840401c2a501c40d00107401596014400c075070140170251400c1d403501c41d03659000d1100348100c405142c03c0061850081440c440c0500002e042920010011910b0341000b080040040080d01c9000300e01c1007404010440c0b0f40740c0000c01503d280070242ea046d09103c80300800380c0080010207424103000414072440c4071006620300c900380010303200354031181d10740d4180f800080400c03500422a07103a0340e00c001e09104840e1648180c540000c1c6541c900b03d81c3c0001207040440e2102c0710741032010350b03d03820100007048205411000d00180c0d11403801912a41d9965001d40303613954600c1d8088000c0d500142d15a122000c20940c0035a410503000d4007080b4480811328040d071910604990540c0060546014010b4544410442e000c40710b0b401d100 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 248380188 1250 248378938 248378941
    0x60905030a080735040501030e1c03051306110307022806020904060302120109060b0a1d070504030b0903070c050114181c060b031501030503030a05040c0e01140a080105 74
    0x15075450510072010080c0c1400700524500c1404d2146148880c680807076850740380d541d090448468405504140603075400300342802c0303207044a4000003030114240b107500c1c021a03a030101c8000c0c00b5030060030040c1031104000d1120b400341020500314001c807480544a10007095907403404141c000e0510002551240102080a00301082c07041840c15400300241c0143c1d0040c0e40362518000100285410362000350840c03021140c07800189419840355400c1070148005224481518081010200700d03400b8810400644034108240a04040140c690160040c146249099101e450720690001c00f11050071027544002900d5040200111255005203000c0c02c01c81c900c1c032610054814180504500300c0c00c01da1980c0d030780381c10560781d641107082c14011594001d50301c12001d0502401800741d40c503205010340b041104440c104c0041c518010304072500040a10700750740b1101c54039809004050800e4074400040031001c038041c412002103900030240300c2c18981d004282c83e0280003004000380e000b1080c0340d14120 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 248381294 1106 248380188 248380193
    0x10207032103060e101202030c04090c140105040b030106051e03150f120c060a090801140609090c0114070302031911070b04081002180d0b01060905030a 67
    0x5405101d400e495545003c0c04138070550300c40c500d00c82c00f030104005201080310034072007803803004040d40c1400909000080942c0c0400c1c1081e90f08111220701004a000c0f21070100b040081c013800c1075800c0a141042040749400140703d2032050020000d05049040204030f003102481544040f85130702c905008010711b0318156080c58850189803108001c0400d450103106005051440100510b14001030005024194009000309028010611300c0410098030070f004c0c0d4100a00003d450314280e1400104100034040701512500403508249900c2480d40d9009425464000322000d81a98504691408901d036206001501080c1d002c8801c901e01802c0d03120300ca070031018a224080b111080c1e12071650011a100d27502c1108400d60010340380d481e100c61107801501403044c5815555104017100c1011414001100404540d02c001c9000184991608041e1440252a042c0d00400141c1200c1d03 = true := by decide +kernel

theorem cover : BRFrame.Cov 248201438 248381294 := by
  have h0 := BRFrame.cov_init 248201438
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248201438 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248201438 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248201438 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248201438 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248201438 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248201438 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248201438 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248201438 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248201438 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248201438 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248201438 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248201438 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248201438 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248201438 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248201438 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248201438 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248201438 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248201438 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248201438 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248201438 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248201438 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248201438 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248201438 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248201438 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248201438 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248201438 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248201438 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248201438 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248201438 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248201438 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248201438 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248201438 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248201438 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248201438 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248201438 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248201438 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248201438 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248201438 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248201438 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248201438 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248201438 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248201438 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248201438 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248201438 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248201438 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248201438 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248201438 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248201438 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248201438 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248201438 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248201438 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248201438 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248201438 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248201438 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248201438 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248201438 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248201438 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248201438 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248201438 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248201438 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248201438 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248201438 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248201438 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248201438 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248201438 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248201438 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248201438 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248201438 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248201438 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248201438 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248201438 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248201438 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248201438 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248201438 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248201438 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248201438 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248201438 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248201438 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248201438 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248201438 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248201438 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248201438 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248201438 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248201438 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248201438 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248201438 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248201438 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248201438 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248201438 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248201438 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248201438 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248201438 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248201438 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248201438 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248201438 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248201438 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248201438 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248201438 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248201438 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248201438 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248201438 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248201438 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248201438 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248201438 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248201438 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248201438 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248201438 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248201438 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248201438 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248201438 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248201438 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248201438 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248201438 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248201438 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248201438 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248201438 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248201438 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248201438 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248201438 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248201438 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248201438 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248201438 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248201438 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248201438 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248201438 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248201438 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248201438 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248201438 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248201438 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248201438 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248201438 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248201438 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248201438 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248201438 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248201438 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248201438 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248201438 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248201438 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248201438 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248201438 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248201438 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248201438 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248201438 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248201438 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 248201438 ≤ n) (h2 : n < 248381294) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
