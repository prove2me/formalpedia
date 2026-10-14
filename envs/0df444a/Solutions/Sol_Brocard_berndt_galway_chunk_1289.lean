-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1289
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T02:11:35.488404+00:00
-- url     : https://prove2.me/submissions/445399db-085b-4258-bb52-97aa85390020

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 231654676 ≤ n < 231834532 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 231655926 1250 231654676 231654719
    0x506060f0f090f090106050f101803050706031b020102090901182a140a020d0302070f020d0b1005240c07180b1005071a0705160c0801060e10 62
    0x1c40418a0002408025040702c0d007000c0c04030340c0410302080c1402400b400000d44000c8443c1c901003120f000c04103030348000c404503031810040c6156130f6410a01600c841c030301c040c58119042d140115202d1901501520b0a56000705000180070700b820400c3e0b00c188296444aa03004104131000d9280c1208002c10144a400710320706550f44106100310782c5107600308108042442c00403148103640300074020f4150144070381d01e031750443e07001c1080b0303d800c07035002c00c402c1c82ca01254100146c07221548c0c245110000c2d13000c400290451600c00000003030260400f001c501c85c110107800f10200a445c0d01c01c0c090021a5034142c4202c014502032203885410200000e01101e000103412944001d07903400800b080042115084400bd039a503624038000f40c00c0500c2d080ca4511030604005103044116500c900c0000703040c214030000020880041203000c2e00c56001c59400300074040004c44c2c20040d80c1491030240610380b04101070b07586000d9000030041e00316001c061260940b0000403030340d0351605941c04040c005c00110315 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 231657176 1250 231655926 231655939
    0x50a17070b180c060403111305100b031e0a0213050a0501050909060d050d0906110d050d0903020a1b1706010308070201050703020c03100218030705550b03040506060f 73
    0x180c0f6941c80303010181006500803400145610341000500050124513915049a13500340420440355805100f45031048880d20241c0d1556075660310450a41012010112072a8061030b0042c40038029154002d01480d01420003950007140c0d455003004040c1c0a01d1040340c0c04180c00307100c0c10182d49440a40710754006005003500100405a5594908100810881c0b0022654500060004590101c804511281e4003801003503078111500c00030304039010784224040e0b1240c032003180004040c801e02c42500d82030343c001e0f91803000f28525a400503d103102d601451401e8150b1072004c00c500307000010020b048a4100200e645089480c0d001156580c0c071000c402c1e81035200b405e203400e1381501d0801441008015228005884080c0042c40e8080b03941600b00a80c03082c4d000d05414880390ba02c00c211510962000d91135605002041c4804001d591080358918181241d9417444d16000200c1d54000f00c081c510410b0403ca07000e03280c00c2d10180501045c0d0740a00140d005000180041c10700a40c002d06018008244 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 231658426 1250 231657176 231657193
    0xf0609010e10030204080f06040201090e0c1908011403070b040605071e0807020f0d0b0c180d05030c1c0c1211010f0e061003080f09040b0d050a17070b18 67
    0x100e14821802030b41100000e1340080d040080140030b000c100070184001000c0c0010741400c2d00001c18000da00d000d80081d03c400b02012400228014044415001e4111459210a0a400805088580c091040745200921007510701910303e0301240302015101603042c291308041c14030108541d16044078400700c44041142d85048100c1c3c800d5000341d2501803046a101d0307640c50f480d2050024900642442c0f60059940c0d03400340f07001590070701d48691f01c00300701c010642d15102c820b1f0b098a1070300d040a8040d0341010a00c2281410f21401200601c40d203015202141d413285500c240c40d1201a2078420400700041043c401d1380002407810222520121451a100515081c90748015084609480d820110070360744003803c0c00501000d10946600602e00c0d52644010b0b46035440c0c1004900c5440350f100079010000969020580c0eaa174890102220b0152070746901c0d60041c81c0647d6500208642a20800e18480004481c0c8542408564840b51b00c081d1100ca41c0e00c4190f42250501b00714819203405010720f40070b = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 231659676 1250 231658426 231658429
    0x9030703150504110a03030e01030b27090f0606030304030303021c0f0902030d03050106050706090203071203090905060913020d0c032001080c031312090816060f0207050f0609010e 79
    0x900c0c44210110007400241d40c00c051606048212000c24007030300030600901d0420219400c51a00b100d880740a00b00440c130b1000900014600a46d46400d241700d00300c02c010a85039021404030885d204003103000032200b085100201003662032000b21180b0358160f100700400d00029119402a100e14600c0300c054200d03080c00c10550905898011201210b4540e64a503400c0030f51030101310034000400d49003002c20840d410b100c8002c0261155100180582d51102d10300011510100071540c0245144c08c05024007071241e1078010309108981c0705490a0306c1c24840070400341d282c0240c07458011300400e11070840200c160341c2030002725488140207640321388000038008007080c020740451b0081c40d01c9180d5800c3c2800300300b001400e00000034114000c00e80050080181324580a01040a03054102000c00d4a102203403500304c500c18500d0308080e0302c0d4004c110074500182d403078200040540c0c02c1511a0300e035804034071030704995680040c468186c2c4030385180142c0e1800d081100090a03102010300d00751175010100030 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 231660926 1250 231659676 231659693
    0x1b0729120a0207050d0305040c14030319080618070c030f110616031401030804030b100810020912060702060f1b0c060106180b0f03132a17100209030703 67
    0x107070310210700c81d00010f03034008000c03003481030014002079400c0c20005030405403a400600b03113a5000e0301144001c0d10b9984800c0d0340d01003003aa4403640da10400c148240070300da180104200c1c0705030389450003606d106040940521508110724482c0019aa07036014600154904940000004000e80140a0707a610303031089000083c00080d2040b07002040900344040500c4005040700e0400c07141d000048900c500610014822100300c4080341d810260340b04160300c03101c0120325107404551140349188603100102c8000c02c042e801408010030100e80300d4000c0d510001070340d515000d04594140058100b2030001301000403000c2c80c40e412401c1d0310110807043c24402a001c0d0035a00440d4142019031018004024050380100c05041c43c4440ca00031110851500703424070b0980c02000030410044101000240c64442000f800c4002c15421008181c50b0500d040d444a0b6208400340321052a0b203922000461543c0351412042000400c4400030607003000c85507003620003900f2620407160b00d802074481c0000400d1211 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 231662176 1250 231660926 231660931
    0x18081207020604080609060402211b030102121005030c0609061603111002190201360b0c0309061b1806040f080303090105160507020405060d08030703021b072912 71
    0xc2d1b0040103942072034010011441c1031185130105004000c041180c0301400403808219110a0556042030740049000007806401102081c0c021074110703808111200e01409120402c0765411341c20350f240046800d09010043c456040f0b615040841004041d40011040180950041c000d20b4503924403800c0074621400e01c808000700b03d000d02c0c0c0200c1c030022084800d01c844044044940000c004181c114803205d14004000380a1733403118840030341c40c03440d035414842d0794a020650100c0240e55500c0e2078038203103a00d40c1050719072400c40d1045800140d070f96502c25841c1c9004a10000340f05003480400740007200d500550106003504040140400110704040c01c200c04003401c03152024503201d1a02507509400c481c070040025001180b910744400c14282c204e0121845140c042e507000c00c442da9640b0100c1d44500583c0780003007203140d00004206d4030b19815409041070f0704030400c0c1c01e507211384034010950307440c0f4090065180400014007407a0458403520320300840070703180b8040bc50906440705a1250704078000c = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 231663426 1250 231662176 231662191
    0xb060c01021312020108060d08250303150605091311070303020301060215060904060f1508030406030b01050301050a12030c0f0501050609090610060f03020405030601030f03180812070206040806 85
    0x80b0340c0b003030307541d2030340803441c0150141c29801e4940070200c0e00000c1261070040c11a07401540c0e03154895080c130448000b110b0a100304140d03044030206900e90071454030b03001c0010540000b450802c0d56407840c842c0c9010074081b0f40035543c0303960030020640d00b08801c00d0000f04000842e140d40e216810700c6a08010080c144050181d00c0040e00da62400d08003a05100d00c0c40e2070014003140d44401c203e140c0d900c00544c00d40140c0c118400055002c6003031011002003640c412044030b009800000010034880000080c0190303a480e42e41400a0f10900700151041d0100b80581075001100100a000960032141540103581c0680390144103401c154075044820041000181d641b65110300420845040c03c842c001d8024450380000c041c14a03007800441110803440c020b9208114400c09481a400c3c07003901070b04d0241400074280c40382541d5038a41480611203402303048000c918951f0884ca0070900e4821100b040b192444003a10342100f610b911081d00d03030f00003a03003281d200c0000e20012071880020031245105014 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 231664676 1250 231663426 231663431
    0x90f021e040e06030708060f0709080303090604050d05070c0b0703200c0901060f020604021905060f030f060a08150a020f0301060e130c020c01080a09060e0d140708070f05010b060c01 80
    0x100642e070459428014030603030282c0e00450003002510302c00a10780d0360114210fa03264010392510b560440d10712045038020905d611010007800000e0b40c0100e007076401140314a00705c841a408480d8140c0b85805400e82c0070f0807000b0744030340800030105c8074002011940e10074984101811620301d21400b010145136a503500c00d900c05c40c0410a41e0402909007405002e25007002d009000008a00940d94900100001e016102000c40d003441442100003903030181000a11a54559540885206c0769400480c0c031070070801081000f01c1d6990914110880617548000060a00034110003500310f01c403034015041c41d81440d401c0180544200c0f000000e03501070700f0503a41d0003225120f03000030010408550342c0100c07801c41c07500740d03001e102680014003000205000e081509070b56840c0401c4600070404e1182c05088181010444c0300b030760101107440010fa886584849148005140f4001e03050700607588001d221300800c00c035140104480032a2661410f00c100000309520300d509000c1511608410682c075100c0c1e4 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 231665926 1250 231664676 231664679
    0x40609050607110423070302302811070302010b0406140d0809030a03030b100c120804020f0411030105010e120c040203040804030f08040603050a15090f021e04 70
    0x1540016520000d060844000d402c01086482e0680105061070941d03100301c0c0e03a0800183c1e400c071030421040c0b051411401d10316840c03510030006000795102400500302a035500022420038201a1507640142c100c40424420b90340d29110b00031950940290310141060b601c5191040c90b105a0140c54122002c00ca649038840403075140203030a446000900038030450510302e00340182004900c561001e190112000800c1500e03606104039503106c0c3c4904250507000e540c2504042c035400d07070041c0d807101e1410747d070004103445008003c481459031124002c3c401c80d0316100781c10009110341c0940c0d030000e00090512100480c82d0780094100e030126540801d002c0d0003c00104841d60f003201402c2901c520070368040d441a0482501c140c0c48010503540144205d03404400315080c88011810380b40030750341c081c6414501110134281412140c100740300341400a410240065100f04050041450300000007203001c5205040c5400701000d404c19100c10303581140e090000040c1222003101c0c490030203981002e5640d486 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 231667176 1250 231665926 231665939
    0x1317340f150305131e14010603020108061504050f131401150905010516030c0510021911061612110705010614030604030e0a0f03120207080c0307171006030804 70
    0x1100c0729a400d42414540020014013101e42c004441000e036101810106601d2502c54180e40d00c407000c480a488001c2d0314032030907640c0300c05510103029a4001d880340401c41d651042082412034000d080200d81c40300034441040700d418842c13154511070348002c00b2070306100c160320481d200b116914000040200c156000410500ca043d40322801c08084a150a00c8214109400600f86204840c61002809000c44444080c540f040040021480d4000140c5441181071135203003010750807c101c42e00d141403100141040e4607000e00390744000c1e4109003014181c40d0341d03854400c0c80c0ea2007040b2544800d002c81c004036500070031880c0c400c2a100114498055071620114145582140c10035000714060144d4411011541da07400568240e115130f2502d403031241c240072440800c10f1315206078018a071130049114080100041a044900109241d50842c0c102a03504c411256130f402c2105280d40d0582c0041d0401d0150440410110905204050488214084001c006011980558000d0301d101a0100341440381 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 231668426 1250 231667176 231667199
    0x1c0c051201050406050106020c060a080907031a0106080708150108090a2a0e0f0c0a0302070b0103030801051810060e01090e0403020d020615030318190b1317340f 71
    0x500424030003804027a0f034040218106101e10149442840701c100d0000d58507100800c00407000d10780c8200303860b84410301c50f0401c070700000d400c0c003031680410034a400040c1814810b06a5901c94000701204420724540c2c0340054512a201a024200500803207080d000801e090115840d0a103405504160509004060706052214245c1001c0325003034040040c0619100d030400c425400c4180e0801056540b0a1188182c00900c99200c0090038a42410000802d25800c0701c0c403a03040341d0055980c40d03042c060010b10b8141c0a034040b07454895642d142d100900901e4803584802c586110181004000703280c0342c100c1e415100104583c1140180d00010031700d2445a4140041b54026181c2d89280e1503101150000940b24099940c6100910302c0d140d1404041e50340b140c511404010b036015002c0c0da6540c0358100b40441d5807015800300038006070130301d000500c211413079401012002c007180034008020b40c0d441200882600c602e4010383c1040c0440603044050101340c00207008000710034016000a142181c103110 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 231669676 1250 231668426 231668429
    0xc020a080d0207060c0809040506030a29070c030906030203070504082b021b130f02030921040b0f070f020604090e010c0c030c0204050403020f0708011a030106051c0c0512010504060501 81
    0x1017020151505c00041e0300c0000380d52200070700710b402140a54812010038600700408030058171407821381d0520380c403000d604214002154003000d00c001090b036418405464003419018005d000484440c07007040308a1080e405940c02410a152240c42d06d5907640be014034090032505001a0074420442e404600300149844080c1d04030140040c0080e85003800c0410780340900c0590a80c02207401840007c284c0803da030051104405240c02103450742011008140d554001c03c3c4041d19841e9a280d14422403806801958219800f041109182510340c15000b05207030850041100d0040750400d207c4016516a0083c002811b900d5100048403400c888401d402e54810704007142c203018190010a0101e58009503400c10356805650100b62138940e450100d03c5d191149a03240c085003e10310001c103104c5070640021035049035004000020141200030103080344c8080c8500baa20400e540f240d8040c8820b01e180d8500010700901001d94a40d54442c08200c48a10040d4170f500c1d6179644908010400056108030360 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 231670926 1250 231669676 231669689
    0x506130603122f061902042601110c0610050405041533030506010b0a02030a0f090b070809030f070513091b0f03031101050601140a0c020a080d0207 65
    0x1110301d1864503081a84240341c500c00c010482c1081003e000100b102c8440c3c000d403459695601c4214500d0800a41c441d00141c4084070300c0300ca00b2181c0c0791070252500036102503422070211b980300510002c8000c000b0076100400200b8654881500c1c01c02590304002070481d8000100107002035103003a50b054102080150000c61056141806000c0400c8440c030b001403280380c030140e00241100141ca245030182c01000101685401603c04494a9443c0291480c04603071164003128003907600c4400d02f000c03a000740184803006910600c4900045403050002e000c8140b940d0610104454861000040b03c3d400100180d50105c8001a010311304e040c00c00a4008810094001d000325500701000601101750340c0008014460325004200103100b00d400c00700182c54a154900ba0182d6502c1d560740100761003601c015408181c3c0b194600b6103494060050034800c00c016504c1e0180c5429400c220107242d00000424420490300d00080c40050f191000c0e400068001940200841003420710005d03d025115004a03 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 231672176 1250 231670926 231670931
    0x160e09010e03030c0d2d180b04030e0d08040806250e12011112090105100b04030b0411190f140607020906031c0e0307050a0501081f18050613 62
    0x511000040240e9130426144d030300300340d81d40c10180b60309009008148108455000c25500080c950103010303105943d070a101700c400f0700101200400301c0c3c05408201d5000f42070018010000790010341b14403011078055200501c00000400036031101c20081e01310b508544201d60080d414024090f941c42e10306030840400242224400e49294001800e89120810030750103581c0310b20107030310604c400390000703c6100a410051525800c4120601d0341e89181600c00d00c00b03d501c0c04022480189110519409403040c101c001480c15245030348145140f14018410340d00303001075007007801c041d6540c1d0040c110f05030030b006551034800d4102229402803080d10f0b0b01c001401e0701b07480507040543d02e4100070b551145404030740b144e101c0d40c1c401e00460b086c0741c1d42000e8002c01100c1250ba140200e908100c0e00d090b01d00303050b0112210507480b5070510490500d20300466003c84d51002c0090f00340000c002d064000c90800040c403088241d65558205007a0204520751200c0e25191000c004050505a220300164001507209 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 231673426 1250 231672176 231672191
    0x2090d081b100e1e010612030e040f020a08040305030702240403020f03160f050f0706180b0a0c020f01030b06160b150d032a0f02010807020f0c1c05160e0901 69
    0x701d07034540d200c0d40280c44081c0b0120613044034003001e6000b480140f0340d1001e00c1001210f81c0c44c0050548102207050703403241e840c009410030940e43c0d51080e2011b80300c00d40c82d4070000d80c8176a2416185500010804030031840f5201f0782030384811200035051203001c91340e08100002c0c18a49000307170412607044440c600ca42c2c014003502c40c0780c150802e80720035130301d07009a0015406841c41c180343d420800d20441c0030300c85202c0c1c3c7c24000303000c1d9841a02002c580944c030f00309400d4a51070b500c613030701c140c4100b030202400600c651010b4005890803410141c0181c00506001070034481020118181c0c2e0041c1328881c0d01c80c1c281c2e0404400744400418401d40c0700304000728890f0b040d900b04c1c0018a94404885010341086905202503080011142421400c81c070001300e8041c02000516040b01c400c184010700301c1c00582c6c02c00200e5a614000110702c0004d44001000c0c00316039074003400380080201032a03030640c03550748808548404180b040c001001c401000c4081709411038102120302400210160000c041c40c1c2c0b40100 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 231674676 1250 231673426 231673451
    0x6030f110405240103090c0b04050a0f0e071b0b040b060a0806040203060739020103060e0613020c070506190806060a080a0b0109091506030f060b03060402090d081b10 73
    0x740b2110814003000c480307104001c04004038010041c6c480000c1c006064501e0101e00c01007141c02520454004940d40d062541d00c42c1c15a00d124070f480c1c4103003034520001701c01044804c1c0c002c04224010500c0c003a000c1c066182d00f40c4420040d400d058500f600e0200346402401018104001440060036030400104031508095003c07d603078500c02171003541004071098600388064404400200705500c224540000c884071030100b40c3c4641d9908104a01181ca0700d10009403c040c5162030600c102d030000c100e540742d80d0b8440700080117544030350741480140c00783c940c01060319502c00c40600640c0008049488010144e5640a081c03503501401c0d8611420090100044a90340300c46040ea200400060104a21504400513200c0150316040310324054200b5800e03201d01c0c030015000504541555074107208985101c00d64404440280c02442d80c0c2801c04c00c0040c480741440d40042481d4680036003031902003907940c1c4580aa40d04400352100e000c0d00c1d410318100202108001c9604c20031072022040148a50000 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 231675926 1250 231674676 231674701
    0xa0903020d020d020901080327220f060f090c020307050d0320040e04210903020409080f03240402090112050601090b0c2503050c0607140106030f110405 67
    0x44001d01c600540c850072802c5495400e81a60803941c0607004910558491025a0300d079040000780c20300307241040c008941c4404201101c0e40e52404080d01440450222003019442540c011203058842c42e00c52000c041c0841e21840f4001c0103084030300b4000c00031070038078150405a0f90b2200c0359a045610078012540070410200c0c141d2078081c1142000101c9103556203020441605c00c1c00105842c3c400898000340340044500301a11071413003404d0460b1040c1c2c2a8002011414960b22190002341c0c0e000340920042c2402c0d405440114040d11881d403c00360000040c120750b601c1259110b00781816101c101e80e04000700c444285042d6802c0f1419410041c640c00000c0061035004002c101303281c1c82c2d0000c2101c50f406035207900d02800f2049042070391114607602541c1c2d40c4600d1f44ea145420b403002d60400d078551400c0700041c0256640040034004c82c1c1107680401849403c5000c00352440d010041864178103042c01d2164200440c4201c1e82250202d0300c80c1485254a2101402c00b0300035400e110802c0078441290 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 231677176 1250 231675926 231675929
    0x14010302060a121503200a15230403050106050306090c010e041802030d0f090f0b0d0c140409050f0c03040c21020406080703140a080322080703031e020a09 68
    0x1d140c800f110046025080c0064680b0721109030004203624404001c2c8058a08504c418400544c04081180e41c040b00b4070646801620130035074540c00303c00e61280c209105403a650503411081d4108900e90b4000b030341802c6160b01c03690040f10242e42d80c8000b04094201800b4060340006640040c142c410000800a00f01d510b88003521440b969503003042591100071161130b0010740b50040d04980140d0350180003c3c08a6004003102c1c030106041c00d400203500d548448982080c1c400100282c3c0c02c00703010700400d4001d07100d22209030003440003040e41c1c4000302011401900050440c3c10000c0f50901341202c240c40c841002a01842840ca800c00401001c52030000c40303401244c002062054189020b8a42c0c2d402d18002042d00a501c1801c2543c0060300c4030b0005110016607004200c04014110225003042c1e541803c014024800c0005100064182202d800303140c1a0700a11070300c080003e00903940d440d0071a400040b04402003569001c6142000690b400001520340600c2002c40c68400c4888021349800c559 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 231678426 1250 231677176 231677197
    0x15150305010b122205101a060705030f0a0e060d050a110c1c0306050d05030403060b010314040611090a0b0316020d0c170d020c100b0301020703170a09050609030d1401030206 76
    0xf10728007090803400c4e0350002e00c00280c0100689410f0218804144007030b151101c0044240b201e2210b400c006403400d201250111035002c0000d5240003130014140019400c070300c2c110000e212420081c9071464489100901c2d103032120110010b201c2c506600d02c4c6003210307580c0d030684220312828086034048000c00101d05003180420703504a039400d4000c1c031044010341401d0708203641000000380341c1006c002001010740300380c9200300814011050060f0045003142c0740710f1241e860741814000807501080007580310114000d0340788805441c1c102c0c460007040c0107101540c4000b8189400008100810f2114199413078509807520203088603800c6000010f01c01a45400d01800340a40c00042c0810102d0000843d000b00e00380c90f90641d2200f441c0340c0781c2500d409010151913020346c1401c0b900d40d178514040c4200c0d0140c03581a00c6043c114091003071284001d9900400b040001c1e0342d140a1320010440401406108182000042d5a00d8015411402c1940c05400d0a1050a80290300500069642e04240c030b120810 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 231679676 1250 231678426 231678451
    0x15050d06020d0b0402042601020f040e101a0c0f151503071e15050f030114040e0a050601050a0618060c02060706020c0307020414040201020a080306010315150305010b12 74
    0x120041441c01403007406400d5031300920009001030b084541c412401d50088800c03100260440740c1d01030f818240d1040400c0c6c0601201d00701310900400c405240503580141c003241404c0b00140d196901041071602004030000843c42c04074600340429801c0050109902065014000741100e100300030b8514080035100c4180d1813211010300d00d5948081120000408500104a20f09106824400c040840c00e000e19048200004802c03441240210200c6100040c00c0070040d207540e20b801c021034801d81c40d04200a40c0a0346640d04140c0f000d03400c00c02542214003a01c007030f0819501d020701700400189c840d88410300b4080d0010b540900c41400d504004100c58031800c200a100b907184c400100148249038000b01400d1002c074034804c00e0400000a00307400d5200340d5042104500c006221074100c1d5003210002d00627409508404009420007002d150010018100401c1046c4400070403c0402015080f100008580c9a00f2411445d41401920b00400c24180f8071483e04070f000c003c0c00e80042c4014200300701e001 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 231680926 1250 231679676 231679687
    0x201030506042c0c01110304030201080a110c011e151e050a06090501030606110616051e03090d08040f29011401020c0307060c0f06020d020307020a0615050d0602 71
    0x126a500710a1040c010405404031401a0000c1d20643c9168802d1008242c811050321180c42d500550107000c50720b081000444c1820300d5a4011640510010b02d81c0c0c44550b12205003508011008000d04070f502c141c3d40004c0351503c0500440c40440f07410b00340041085041c1070b20002030f01947c40618080c0c42008503218121018900d100507014581e902041d04001c400c0c0c8009580c030780c0300741e42d1001d07101d0981c1c040c42003554500f821210f880074107441c2c21366a00040c021806400d8005600202e42001e0b0800c1401d0500d0a0360001404140100340c0c190500f0001c1001112402844900312861260901084030b0030240c846040e0074149020051082da210358203038980300050400140e03a81c00c078080e150440d6031910f01130304861801c040214054486c00f11a01c803103180105000301907501d070350b444100c0009240c955030914108003006aa41c6582000300d140820305074001180700300c106030000d10001c0c1d150314290003191011303a48251819402c0d80280320f941d907402e11186101c0c0d0001001760316403 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 231682176 1250 231680926 231680929
    0x30e093114060f0709080604170a110318010801050409051f02070c0906061b03050316090801090b011e0605090402400603140c0f0d0c0503041101050c0a0201030506 72
    0x1445160100c03825110b04010802c24a40048083d8494510303036541128682e0340700e20311350b500c0b5000e40d802840c0810300305248232014112005052008081d10b004c481985001c0c40b01e0741141e002a62000c0409480440c030b00c03440d40c00015090040100381c50410003030300e07541c490a4030340b84540101810b80120860f016030044c0c4c0f6030160f40d40180c021a01c02c10302035031040501c00030301241c4101c03c017003843c4e030110725144a00301800080031501900d82c0b03072031a0788103401d8112082c2c1903000d0206121050401056840c024070402904912440d2191195414480f200250850149844504c050000420b01080e640101a90355114058501680301c2521156404811000d000081d0182d80801c1807a05c4107000e00071580001f42d40202c00383d450340e44940302182590800d030022625001d10001080602c0980d00040c20141414200141420740d8582e284094828030565640001c40100c244424800d441c16000d040900c00d0900b14a0031140300c240b00d8a4001690f0003905156803200080e03480d = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 231683426 1250 231682176 231682193
    0xd0201020a0b1e01080d08040320100506211002070309051003060e070908061305030f03100302040f180213020c01091a0709050d15020904020304030e0931 68
    0x14590140c007031082d510b40950100c04071042d001c1085098a1103000018401c4004505408444d1850761010040d0344ea94130143c03580480840c004080200300c6440d03c501300300c18007207120390700c07401800420765040410410298081d404c00c89405141b00411f0034407405030000e14496100c00403480075846000f282001d843d611000e5025540060070031107500851641a482034040d5814200c10f0b2700e081e05c2d170318401c64a81c422070003020019400700012030360360031b502c0811400151080044925000780d01c00d0b00c0304150000e46801c500c0000c040780a02c1180340c940517000e10716007960000c00445007029840d80c000c0121800290240c94080100c000c071200e160120b41e101107441c03000388a041c04d00d02e4007120310741c81c3e03c524050002c0000d01080019125002d40b0301101c800524028000c1c0c10340c1c4070142215a00303450440100c0d8204001d00c0503454900140d403103203000e0340325000c0c0341c0421401c1c0b21750756200502c8608128a20b42c0e004401d04c6100b82a10b10300344094000508419091401000 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 231684676 1250 231683426 231683443
    0x1a100803030114130606080f100b040509040503190903110d0b0a0c030902090c12101203050a0512040f1415010b070201030b0303041403070e060607021e093d050d020102 74
    0x84242c01c0c1500461071b01c0d00701e0b600c603001c0c460395210300b4040d59644401a0306204071740030303880354030030100410019032401f401d480390041e00070f01c01d43e0711300040c14000018501d030350f82d90500400c41c940d20401c280020700740311030510342040c1c510a1048400781d552003a400001001d200c1519510b130700121190740300742c0c4241240d0b40d0141c452aa6400c000650452503008448a4020452080001413086d226104000c0440d680032840b04130039041e5980545e119000160800c0c1041800e1002c0c1100d9038150b62a24069405511700341c0214070542460817605c409440e00724640d50082100c21944c640c5030300b003981120406c8000301c0d2940240d200407000740c07400c0000154548400314001c0ba10090001e4583c2d00010100d04442c40783e9070f100c02d4800340600031241180d01c200107000c40c001504040d091001c0c503c0b4481b010340a50180c900024a000100361070310803400d00784100d42107030107080004c50740200c0c0241c0b00d00c0c0360a00340c07090b024076806241c2c014603014117188602c450459008000030407 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 231685926 1250 231684676 231684709
    0x50702070312020c0a0810110c0d0305131203020a0f020610030b0901060e0a0c030c0c081c0204050909100612080301092003010314060a0c1205040203030c01091a100803030114 77
    0x100e1a9900c0000c955161440320441060342d141c948e00b80005d5505d40100ca032414804009802c000144881c150700403c001040390310000c0181c60020002400304900020f03410352524010389407805124020310110038484031005642c0f01c0c400b402100c12544002c6411a58824007504480d42c40f00708040c094051548a00c03004400e2609002003030306e0355086888607110350b6a040184000c0c2c10021100e61b01c41131b0014201038400c00580c02021400b00d03081c012207501e07460241c60540c0e0388012515200c42162000001d0f0000c030b8104501040d140540700080040d0302107065114100d8a03120014841131189680484d81c682804102d440100614122005208003c0c0e441e582c1d40c1c103201410440d100180d0b100350003002c0006190b40c40901c1051178480c016a14507100300d03202d02e0701c00c00400300980280d03070520090143d0890201d00340107080050b481403d000c1591b4500d422000d0a4100203003024075100d0040c4410721280304c000003601c0c112204015856032030681d90001c07803044980041d488 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 231687176 1250 231685926 231685939
    0xc040606110c101d150316030b040c0f030203040c030c0617090303190b030a0c14040f060602190f1506170c01021b01050d0911010206010801050702070312020c 70
    0x61494000c81030888410041007610500031190041010303091a0740c0c800000b044da02d0781d110b03404502c2c1001d00c40a02c100500100000c03c028041c440380381e0000c4640307508117840c0341c4002d00720769803502451500e141c05071000c0c4010101c40c1c8010301351441c21007403a01095030120009082c0806810320304010358019501c4419203403900b00050112241d1607011f405042510080b904200c00041264490000142d0100a100c03800c1503c40150284109080c1c1c54861003804901103040e624424004245050407220301c498807400380b02c20740780507410120425242000c1048116001b088400c15805041044d045200c014502100701000703c0d140075060041d1450a100d49140755481503080d03a0f8021160749507014181907680d918102d9811080c010f03040481c20030740320751400b002810360620504106060030550481901121129001940d50301d001d0a0141045d50301401440d000d003890304d00910040c0b0b070042003c0c0d03030f507103141c48000c0038080240062030380c81c1d100303000c0c0c02c07801e0a008181 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 231688426 1250 231687176 231687179
    0x71b080705060105091e011a0d060602030408070906140d151e0605041a0909011e2021070c0506040311010e0a02091501051c060305060f13020405090c0406 68
    0x110b0340c1d1042405882c1c041c0c507070980440d0340650321412000c1c801810305448150780c0c1c20312021f8914a561017481d409920b40c24440707034030750305403500400001d040b10fa4000c580310703031030441d0710780c4cd1080c41e40c000e00942c1c0c40e04905000b1140e44001212000b401601d88080130420303850048600c03610305d0b6215202515120b0b804d1141c03400c51400012800c0d00c0e00c0244141d81d1600200811502c0000d2010a960701c1001c0400450409c40b80b4541d0004619000046180c0d4030555403020f030071507005941403c1d94444511140d045c0462095202c10b4032140305908041c0324958481c1d00c0030401d0503000a92040c41c0015034041e1048050101c00380d130080c01c2d109241000e29015207102e0702204403030240e50801e0120103c96000142201c21150020710b016084d84840b5815801000a120702d1410001e04000e0010340507809442c5005520a04200044080ca5401d00c01d05040010b000d20018580d00000d101014021040d1032856036012280044e10f038480120341881c00e6290944c3c81d80140c1007490 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 231689676 1250 231688426 231688433
    0x606101e05130e01050d0222060b040f090605010504061419030b03070b030714030402032b0f020601050a23090c0901120509072306030123040e06071b0807 68
    0x280600442e580c40e02d141e400e446003904402c0100034020550070031410616440545481c48200888040504c0c010518000890b000300550b031460304054080440028208081880d0808480041030030400c1000070908210000306148a04c4c400c14041042c10307503000001c4d061207412240ca4008514415007000304800f406800340040c01030700d510074001c0c1c0800180c800c0907070044a11662090b40e40208080065203503011a400140060b81c242c440c05003401116003409400d00e11060b502848104d00130182c00d402819041d0412070a01190040e1004002d15151801c000069400889a82d8280310381240c521052080c9201e80c1c0da0302c807152400b8040c61035049801028001002e9903200718107a969403218050360746c1941e80060650002c40c00700410700c1e08910b0101d07981ca8420405200c031400100080968100fa00220360090104950004550080e14103142980c816941070101c3e0340c04802003919040000c02c1181031042d50340c4c0145c08200c000000030300c00c07648107803125100c1c103c504 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 231690926 1250 231689676 231689687
    0x60803031501030c1103090d081b15070e03150403120c0e0f06070c030206090109031a100e10150c1b140d050714060d0c0809100c020606101e 62
    0x881c82400310740b81a4200c8052841102c002082c00c0160004502d0160500140885410040c0c000d9590311020320103c00100041c0001d01100c1d000c020040c040510303400795660b6212005480b01c0c06016001511100315100480c0e84503800d007802c681c0402c141d440703060940c5e404069126400c5001c4c980038201084541083c00c141e071414013135640301030b40c21f0b03c0001d0043ca44a5405e0140840f5410001000107207085001841c0c00d042c10b07d4049030203952603032400b001e0b4042842c81e0702141000c004001086e00301d0780b000d03c014078070140031003400c0c180140c5c980000409402a00040c1003140a50713808140550881d2072090792041d21012014521400b602851400380625079414650a0f2582900d1030314800d000d8082d90031030040c1c020145846800c102e035102082040b60040810701580a042074a40300d00c0008076240e4452540526040201c541041d01c1010002c90386031503e00c241964950018003d0b42c440c1c0141c0d103a480d0500301090550b91b140464846415523110101011006603121 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 231692176 1250 231690926 231690961
    0x703170f04030206010602011a0609030a020d0b0a0b040504030c151b030603110d02060a260a0b040b03030c030a0804050c271e1611070f05010e03010209010c0206070606080303 77
    0x83c0d081c0c4200d640c0340c0404a080e00c034151412441030940c91007481c0716252250003030401c004005c04584900750203902140c8404516003050790800580401c2081c1a0042d000302c180c0d5120031a4200081d2a01c0d54010300b181d42c44000c058045200c1c00107200c0d84035800c1d0b03c0542c4400802501c1200241c032240010090011070208a034000006103454140b8246603a00000e15031707000304003508128017074004880b003e880344026142e0040840030b000000710340b5035989000f00050079001c41c90010840900c8161000507584c50700079030040140c1c1300050400300a0364141c00360352519521b02c0e16142809880d042d150190154004165102000c0c07010b81e413101d000e40d088030242d00c035070180c3e03800001d002c6141a901004602e450424002101101000541c1950148606080440c6001c180744d040ca0411143c00c01d4a0403040e404042c412580c100c604240160001c500a518203847d00740028844000703401c009005c2c80c80810307041d040200070781204000d0401542105d44a141c00701948c203181c20300 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 231693426 1250 231692176 231692183
    0x309070b03090a200a1a19031d1f0b06071406010305070f05060d02030a021303030906090e01030206070f170c01050f06040c09051009030b010801050103020a12170703170f04 76
    0x303113101e41109484184001000000c040c400c40c0da140022201d0f0000201010307600d8003404110040c1e0000340d202880b00e1042d8035940001c1e0b81d024006076140d456100c070b06005003035484075644440012516010011040c0a01004501741c03e070b00021a01d103003d0410700520248850074100200fa00014101e412030f80180c003102d50f80c9564100d22780d5026080c1c0506500603d040024900442d201e40045801c104031030700051410705035114090b1201190b4004500007003940204100643c2c0c401d0081c00070f42890500300c40603514650014081c0e00c100400180002800e070302070001c1c0300c0710a140c120415032034078565a0f2182c1400c0700303900030101220000706982c55100455642d080034410020310000c1d81e1540406541010200042200d00c4130402082101d00170010000555490f91580209070036000410154118070401c40c8188075078000c410280d00440400008c81c910390f81640c0c140030400405640d51000e070508890441e0900c5420368045482c806008101c0501008070340b00e18003 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 231694676 1250 231693426 231693443
    0x11814030105070531120c1502030c0c2809050109110c0a0308061504060e03010608030a0c06090204061208030403030e030a0e0f0d061803030e061306020309070b03090a 74
    0x1030b0f6980c1030380e55000c1c040c401c11294244100045000044c0d500c140300614211420340d0125907a41d16980d044c0304142e40c00c0b100c1440c046401c2082c5096049003004188140c0051403c03c0d00c4a040250f0300c22007440c400e40305043c0d80113042620250100c05a5125021650118480d030325080400301800003881aa1150b524010307402c1a05448802a5101005001d0142400b0001514120394100d005040c080e40400d0220034400c01e40c0e40d02008100a0030303240c07580303160595480105400c56110b5440840650420001030f02c005500603103611540360702c00ca000503030001c940041030081060b9000841c1030102e0454034030500403e07c028620a521039682400041d004000310b07a1203000c0c180c490000b040300060a0306141c644844e42980340f04004c0d0201c06101c12603124441500c111401100644501508040078154075005049010300100002c00450800504c4803070101980303c8050000c035800b101250079801c00b0311241008202e4910415100d06250400701d8a071003a52200b03d0b820360 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 231695926 1250 231694676 231694681
    0x90503030406080606340b0c040510080901060315090b060d020f040207030507150507020f03030c0a11190c0f0812040603020318060405100c03020c06070e011814030105 74
    0x5800001c481c241c0301c0ca950b5402c00c540750303030b0305000443e0807199980c006111340850483c10840b644107450107407080040c001041940c40d0800c0040801c01512100780511304010510640d181c0d4868400b100302c251401e20400d07940d801c400c9005028541006041681c251f0851401c406640c002814240c01440406030944403182000210307101c0e0107000b0b4004803920f4014082c0d00d080d5025180f040c0c041e08040d4500010380d9900880e26503001c001414055542e010f000850b60304019918a2400340c00055255080500510b401d0f409891112000c01000301181004107606010700c0b890081d40031030420341d03001203280507001007000e4000e60064803c0d865000858050024805070100c1c0984020342c600341c28104110003039407004000f400701c1003000e00010391104040000d06d200e070b802070703002d08450803403c40070034103a8010484000c101401402910340c1c0010204943ea0041701a042000902d40f0f90300060b156444050350040c4054108500051040c0011148400a0f90110f000f0402030703 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 231697176 1250 231695926 231695929
    0xc0f06020105160201180305030604021b1c3e010507020c010e030c0a230a0b0304021005030103020f010c1407060302041e0f0608190606030906051605090d0c0e01060903030905 77
    0x3a070b00425a51186da104410700804680544025500804040c2c000f5213030080014040c45074805000042c00c00c0d42c00126035901d01c507295681c50241010519140d8240000c071082460dd420500c4520390310198400c1020181e048510480c031200900b100c0244042c0c940980d001e034440345040d040324089041c0e032540383c1f000c2c035000c40e84a0a100c00101208095824070344800e298481020510120940a041001c034954a0740c2a18006104510807a035507441d1078414400503000d01908181030000c18001400107030b1f50000c07540010802840c009510241900b403584200c0000c12030302207540106d080c0810f201d68150014829181c4501071442140c40780030855011403103620a41213084440041844071510072801590003101803000203008415005141048440583c01200400d41d68448142000388034000e05a0002c0c02c5440d0310707003440e0040000362261081070413041c42800182ca50740d0800c0300103031529000c0c080d5a9000042d940c0c454001400c00c0d0704500003030740800e042260002d2507 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 231698426 1250 231697176 231697181
    0x60f180d06020903060105011e0509030a051608070e060a090203061305150102060606040b0901050705100c08040618031d041b09080601150509040c02010207051b0a0b120609040c0f06020105160201 86
    0x90427600511301c5461541c1c0c440440d201d40020888a0303050150503a620b002c10341c204680d048088294180703003039503803801e954140b4240c82c2da482a115115000100100c0d6500c810008080300c144200c052703a240da5020000309160011725104081521f000180700340ca2080b81201c1a02030404c0c0c0894840d07889840801c038050284d407142507450801004841c0e41944640d000d4040e80c3d1040044946040c0402d28080958404400090025152500700f10a00089001c0c80e080340544407910b403580f001540f801405000d80b0821951401c17414261032075243c032160f005000d040d600016251100c0102e03100102011780d00d03c580a413a00c62034002062408030150072413a01d071219100d8a203003613007030014800a0424a85c040d42955402d0100b44013140c014032403141010304d082000c1c81c11584c040c040240c2000d5941041c42007280038015880045407030f80320700350041000ca400603625941e500c0c4c0940d550795035402100f450201440c0008e18581c054208500801d010070706905100325100d0700720308 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 231699676 1250 231698426 231698447
    0x51005030606330a0806281e0509010f15050a0c030c1713030201120606050301051207270b09040305070b0a0f020a02030702090f0402060f180d0602090306010501 71
    0x24000030440100621011803040010503d0f0042031008042d5402090984950001002c040114810340c0801800303140100c00440e0740d0100025207422444418040c0700c081415014400c54040030085240850005140f11001080010403001e080d60319407014400500d081d10546007203c002c2500008520300400075561054020780c0c1e00280400d59440407507400030100c5040c0d55100c0c010500302d044840c1a0028001c2110441c420071060b403451000400c948441d00f9408030043c81d008003401855880340899046400072524081d603041c1030b2000c5820711074980d1141100003803c5000c101c55207018184201c556a1581040002da1203000c144280000c00b06c81c024006a41000b9580c000f582e042402a08001041c030001142c1c1c0f0390000d004201da06c417224090150b03001080c00c608510b05050000e500c5480c90f41120340a003015404a012402800c50b0503108101c08039030244401e00a107419000e03403100800c40b40c00c030100750a1002c020750066255900a00850001103003950140b4070911 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 231700926 1250 231699676 231699679
    0x1505040b030a1802040504030c031413140609220e070e0718030c0f0302121912020115090f050a0606050306010521071701080109030c080901020c0a09051005030606 72
    0x51071555400355a200030060041ca010305112203003448000f5803200d03c1640d2180303100b911141d480c1201410007420902d1002d170300c40c050070f600304240c1c03100c07120b940629000c545034201184502143d0a000070741c40e0055103001b54029084062860040030717014481681245e264104014850640118944811107809442240c00002004c1080d0a214006500e0050300000020f5003250b2039903190b0344401030326400000007298003078040c000d40c60006041c4010200c50b500901454018580c4141c191190f440c0103009a41c1c41c042c1141e043e8002c3d003010880350080b4425a150549030403d01c00242a0f0070400030001d46004005100035481d4403402d4140c895503203400341595900d40046640780c0c013400009146085681005401e002000c0005000380c00e107888605d024a40000310020034170050b400014640e041440c5200441e4010b58262059030301b110745a682c032900d40780141d14120084002c0c42d0898041c800000c0e12403d5a072126006d0402920031580305a030b00d00400d40d64810598610f03 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 231702176 1250 231700926 231700949
    0x1050a060315030807030c211206050a17030c2505060903060c03150904060207120903030530040606050411250203150a0509120a0503040b060f0d030306150504 70
    0x140f0110b19840c0c060200d142c805d10303180440000a685010304244a610507804220040c0b1348218a02d400c90000d8004600620040142525200009803900c1c52440f07208a1720305840e484020f402c3e0184100c0d803640d0402e5041700c28498042d4000e130806007000021081224034614007107454980001106d60b5101c00030020160344d00c1c0c00740465101c0c0d00180c070840030100c050f4140c05a0381c4588840520990042d1001070300e600207410078070302000c002200703c0c0c100440c02e4014000030b03400c00d05546a000b210110b02e0305a00032a0880b0018014045900d00720142d00c00803c0308008950b04910250b036001e0324148620f500114000c0d0407030041c5104a202c1c01001c0c02d82003180c50041401000c581d0004080354410711139070076681c811fa00c007929110282900c071000c01049080400c400209260589000da05d4201c0000c0c4c0280136000c090701c001c240c81600e40108000c1d544001070064001802080055210000d00d80030303000700414030690640340080d030303500100a4004d07420b46003154034440a1 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 231703426 1250 231702176 231702179
    0x3060a0c020d0810120b180a0201081501030b0405040506060102070b03060a05040905120f070b070503010e07080a09080c100608030301030f080a020718061d0415110f070b01050a060315 81
    0x54415450040c1071851003414010001515001a06202003546c09041190301d907003041202d00000c040c1002070200e060b800182e0329001030741d214a03c99400307981014030120120401004030044c004407090181d100d030500c030600040c09008110640900d509030201c490a56896192110500045440c00c0d030104405004000c58241030300800c612a01c80c50541d0b400c0c612051004010b07811204e4494040e5401185101c10071440a01c1c26070421050700300141035601d010201ca5090000400724400c0040c0342c001300b03040300c03502d070450303060660b00a1042d0740302c0c1c9215040343c0c2d44174005040d900d54241409400902607101004480c16a500411042ea03038840d1512490f10561010b585441184214140050b10340d502525a80650046000205215203084e800d80e03415001003038541c180102c180240400a000d5000301880c02c0480b05001ca03040a00b4410074000c0c0c01040c52100080100146410822100030038441c103862017200c01d4000d940e100d072400c80c104c6125030701503407501584000 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 231704676 1250 231703426 231703453
    0x60305090604330f0207030f020114071407020a08011a040b0a06080916120623040204050604020403060504050106030b09060403210603230106050409050a060c050c160503060a0c02 79
    0x598007000c4140000c594041400300360604913151095120b400079404641c2c2c01c109903010b00070f42d44548452000f40002004000b0b040c0305d0020240609042c00700d6800c0301e80040b440042074580b0160002c0c204100b080c1d9404a01d400303403000a40061681180d1a210b0f445854280f150068113140501190000c0d800c10b04140c030342400141143c038003882510b10f8240003c1c8054260005010940718240454041e484c00400751480124100c5021102110007800d1003404040076511030780450340410703140c0f111404240244100d410180c80a4100f8040006100d815000310089a2140c1c4080c4059501d0f08a132039182d990645000700019100768080b40b50807400d651903600e8510700440021401d03540e50365a07945298480415014409411030720100840078410340c401000e0980e0300b409842c0c1076581d603544484100000800c50740d9680313a1202214450030944e92a000880c0c210f6101e02041100807010b80074034440c1d144a031180d81d0004550748210b0040004103001c82d0028040c2c0301a084 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 231705926 1250 231704676 231704723
    0x2120114030712060c05090d0c030c06050c03220918020a06090b0304030c050106051f20030409020c070515070507060c0c0e06030f0d03020a14120103150e06040c060305090604 77
    0x417000303081003000e200da0794155460940c41c802c003900c2030f904800064610301e00020f090105610040c24441d051003012242c520100c122422401c4400c03200d045040030000000c00c2a2080d040310200d180f0b0641100e04442901d640220420b000729265030303116030b90710f008840d8514103000300720070941d06001042c00a03001d440e482107800c2c4110000315030251900c0224a5881c41003200c440c3c1840b5401011482540005403901d50710341c265666039100d8285982c42e40e50b44102e1250903a01940040e0301d044600c010301c03020028010061100740114040c5d00601080e400245043d90f9034001c900d000909140500d1001440c0d80d440b5918003a42c47c44c0c5801c3d1507078860300070119509405641100c1c07415040c2841000b90120315a1801a101c24001000400c0030481c00c0b00c034200200104500100304012000490440364092130400b40780d20318240610140c01c4441c0000e081d4850542071104001c040940001511210f90742080b00e5940c80795a186d9441081c0d82c050001505d0740803140d018046207 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 231707176 1250 231705926 231705941
    0x81509010603080a03020d0e0d0e0d03120f0b09070306030f020f0d14030a0e061c47040203060d03110102070506041b050303130b16060212011403071206 67
    0x12000010515602c1e124031016a0090910704c0c0000e500241c188030040d21841256444a20b0000403c0c441c10300c444040c080701b402c1703070000307224440001081c2d0030035100b001480c2c1e200b24581000d00c80c0c0300350803444202070520010041e00c1203500400003490030b8802d10800007260b8006011480b208143c4e020b120508518698403904040b8031b844c9039002c42d40340f114040e100d002c4400110350b9804481402880d08035164a09841140d00b04200d01c01548a0700001660302c2e404100087e61180002c03031540d4440000d5006440c564100040103851038449481c40d141851001c2c0303103d220390010040000701d00c000c9030308035402550031440c0da021138841c50254040c0001e030f0000516045031521703a1450540215001c80c0c0311080f07407a00f6104401c811051100420086d0000c41c140f04c22402004481e400034011903614280c040340d40d030900110040500100c6800c18411541e0344482e041a001940003400f645101d445080b44400301c5017400220b1400300c40c401c0d480300d90300d101942d0f01c4101030000e0 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 231708426 1250 231707176 231707191
    0x101d0705040c03020919092708181504060201060e01060c030807271706101e0306050106030e070b0906070201120f05090f06060a05010f080a41010815 66
    0x3400198521b40f15040b2010001c140f007000404154508072121095078201840c2c3d0506046892600359402041c6100da00c1d074540c441e481c41d80703d01c045000c820124140142907a4030002d080100c24103014030100500c00e030707000c0c6c0e07009000d016140d02c0354102045007032141e000020950040c100200e40f0400006810030140c0c98400314a02e240912034161502d09500ca807480c07030907500e041040c0340054140220510b040005400d091502000c1491318501501c225001211406d5044107801d07010300c035510185a101d00c0c01c20a958407140300500800c0d403840c1c0280c03244903042000ca64403514805484440c0001040d007860000c3d0365004480c41e08039040003c2140c0c0e15211850b02090f15400b070140b0072130840d070040c10403a00380d1000da46070280181c00c440c01030660b41c00034041a644040d4003800003401381021141c9448807501c480c01001400380c0c2c0d04071044070fa084803001d000c0c1c41112100550380009600c0fa21900c10034942c2b058007027032044181179485000079018203400031480d954030014 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 231709676 1250 231708426 231708431
    0xd0b0406090c0807060908010501090c170c0d0504080304050d0e13020901020102130305010c020706140706091a0702061005030115121b090921022d010e101d0705040c03 74
    0x6968621034034060080d0003060101d2841038047c44525400d1041c9401000c1d440c038140019116030350054542d40d4031000700c241c039022800006030314030312840c1160024144a00c041040d0301d030605105803a50001d540403a00390141c40303540c601061144c0c41c40035041400600c0142c0002d1140c10100095202c0039002e4151354080c0320b0703c0d100525920030840118022000425a80e900510081c2448415040030083c0401c00407030502255007082542e440341c0d4014070000d190b540c00d040c410175407036149034008091060041040191580407890501542803560350181783e6895504050980c1c405904410114009074000c0004c88504980500e46900640b8507900084006441041c0d941040e049400142d8071052510104001031102c8030683ea2248004c80c90024039580003501e030152170f0a2000b05804001038501c20034800384e65081250b00201c0204540600e00051649648c1129017500c42e20b460114458145042d001103132800a01d00009400c02a062070f042000400d0100100c0d0704259 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 231710926 1250 231709676 231709679
    0x15070305010f09230907030f060e0c060f1804020d150501020f010c05091011030705031206040b0d0f110a170c01030203010509180304030c062007080c012111070b060d0b0406090c 78
    0x44044526003c8d00380a0b400c04034035060380610080c60201c040500b180118400c04c00841d2286a800030307100c0e4154014800910204d111000801030b004008090003598039145040c4694800e410b030441c21030f0760a030255140c1c543c40c03060541c200e880c02c800e01800705030b040003040030034075200b011100d07040203901b481036410700182c01c0145190405036040312142d0000460741c0c2500c0e4048546980710000303d809100c20031004022540080c8401c074010303c0c1031030304c0032010b04000030030080820784000900300312512566408c682140f4070b010612140c0034000d01d0010201540b02c1c6c022207069a101400d001360036210002080001c44a42d690392541c1c0c00180004000280c800b820350005000135615140d4a907400d41c402410006049410b810300c0d8002d0034100601000411403c0d110402400c0c2050015484903111081c03c460141420520f1305d041c080e4144c0c880d485000d00811030040302c0c5011580d5814080c8140820114000380280512500050025104e41c00410000d031003100d0340d42581d0b = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 231712176 1250 231710926 231710933
    0x90906060c060702060f0f060d3f0305062b061e0501031407080d050a020c0d05010c080a15030206090418080301090e070e0105100215070305010f0923090703 69
    0x802030781c50b00b0058101009000400c1510a801b640151380210782c44600d042010004552503030041d00104401c0d52031000680a0f60050607207005006013460005000460741c00c0d03005031000c4003600d0404286044040351039400c0980c43c1e80213845192072114401d11000211003a44050901c04584c1a6103a8099524005480040326214502c078a804181c550541c600702d04842e07009030609089902c556402c0000400002d600164403240d401c10305c0d654903c0e10422401c1900000e4a15000034001404d032040210540c0400081135040e40d551545132035100b207501c02d503643d1180c00c0c500348044250074005403419000600502e4002800041c45070f0111300f5888402c0e25a02d0f00b03566030070010004200404060041e240d00e0245803010308142d90403c803414104603c10301456004074044801082c096000300540c0b111200101800d017140d28110100a0142100b405400c002004200300011410094001c4c081c04180c000e2141840301e00c8000b100c80c811078007c290840500c292040040070 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 231713426 1250 231712176 231712183
    0x203060a0f0b090907020a02030606100e09160306080316060506010903060c031407022e02070b010b040303020705060921123408040e100e0106230f090906060c 70
    0x2d00801c81a59140c1c20348404222884100814840c03d64000021360300050340c2c04250581e200c2c4003201c7c042c0f401c0103500d201319604d003c241d43e29a00002027005104600348070a40e840349120349070354280704154455451549a0041ca0340302620001c0310500c4900041c002c2c2c1041c2c3e400401850002c10007550398a0341001c0e200520305050100307a07a0046180d950042d05040c6522000354001010505c1107003101826040030301c129121031650391081904815020340441d03c40580002a441555842d070f4051303140c5a00c03070710007240548501c060004841c00c10748140c911410307000340078450b50011602048214191a81d010b0503034056101e4030814100501e010f03000940c200c0c030310405550400c0e01c0c04c036510f03078012a03440301c01104c0d500c3d141c000030322510072a02a03888140b039805c5c494a032034050100850307407038111441e83c03a400c4001003645039000f91101d01c01c1d0300ea440750641c4803050b07900030409403080c000209801d640420055a0604103503c1203504900c01503e141e203004800c1c16403d04 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 231714676 1250 231713426 231713429
    0x303030e010f0615080f1911090a06110705010c0b06100c0203010c0f14090306010b0a020c0901060c021e060f1c092f060d0f0905160f0f030203030d0203060a0f 70
    0x7003858811054220564440b2840b03510803600c02420307021f8100310212086403640b180601036081d440d4040c035994204031401f558400340001d0305914000351240009402400f0f00003210100e48034066002071950700c03039425924001d410502c061000d456440074400c2541400f1000c9007804610740c0e10100589091052100c4043c05540d5501010000d0900810034a202c1106c61034080c030038040640d10350f401040c02d6046035412035005546030300c10f80e0241d040c0b0b10f0740c0d0b0849500c244800000103001e03130000350f6040894401c03180c40d0341c0303000540b850b03100c90304498038113a40100c1c05102c0b03240310360220301c02810840f0951404070340c4e81645c0041c01056803c03558048440b40100f00d100c60501c2500794506144400a00c50030f1b41000c11080868a180242c040f0007021030b450301030301020600c440e8400709020341c010341503840034052200d03940c07550491032051074a2502c16840026030b0aa01407045c90540e43e00501940c5030044103c2c4584c0690000b401c0117500800d103541c002044100c9020440 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 231715926 1250 231714676 231714689
    0x10e090c31061d0105030601180b07140a0f02091305060a0903141801030506130e01050709060903150e03220302040f06050913050c040e060a150b040303030e010f06 72
    0x2031035014900040d01049405500860612400243c41d0b58802d6100c1250b411409003172a20a440360b0b10744004a0361441042c101400c4940700b40008201d10000342c00619445000d04540043c40002c040250303501c56140c4030150003510702451520040c6010100107030044a041c400c0b40034000039889135810800e0503103d5026240e69403150b10205604640354001528482010500b030941e4402501039001440f0062810113982e0750014406030355100343c032103251801107400c00a00080100c154001d02c0181e9000c404030380c030820001090342c46000880300707803580701e2004400701d04c1c0d0200031030180c2184d8402c0b11040c001809024180c6080c11500000040e840c4602010306180d401444111044080d0001559040001c1030005071035015001ea08807441c24080e040c215054104642016002420b0691050400701507032a414030024036907014805e40802048500350b0844d5040c0b01400700d210b0710b6071949081c4410808240a0760014035200395000002c00d50880c0503000c041201e04a40204 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 231717176 1250 231715926 231715987
    0x20c01060f0e19291203030115030504020a030b150108090f0d0c0f0b09030a120507050a0c0501090803071205010503010218010f030912050406020c0405010803041403070b0d050403080a0506010e090c 87
    0x1301ea91a0001c01c001c010904070016600e194100405107849140a402c850203054807003001c40c08540b98402080d0065800a41c0c2a096081450480d40085e06c51290f40b070020710040302042c80074402041e000c40c0c0012a10080c483d00c400500c05481c2c822144034180c907003109002c2e1040225841002c1e083c403400d00d9801544d40d4aa10810141400000410712008a031502003044401504003040780c4406a503414000030310070729443c1050160080c0d5400424400001c018410183d0f0081c9450032541c10a050501080e07884005140c01c0b406803040c080c8141e080108a090994040c52609800b41418640800c185040d500c800c100c13148400c1581001460003d0104074407a07041c0020380e19610700310303014080c551405503295520b000d035000344529460740b42c4000b810303039504000000c01444092941c81d00c071803500111000910040320290081601c0e00d0000740d6000c4948110f40c4a00030503100c40e40c1050001c0c0a0000b241c030300070320741e80300b010003008a1450b0244081003000f801a070008207 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 231718426 1250 231717176 231717251
    0x4020705151305060402011b15061427190501032f13020c011e020903060108061014150304050109350313020a0306020c01060f0e19 58
    0x426180e08004007000c2840c190080c20340300043e400310ba0360703811035024605040d100703500032614401c940700080d000780400710394400741140c070403160084822241c4411354554011f4941c418000d03400c00c2540c28903400c11504140284540d80c2668440d0803c840b003101264035807103022000d04460342a0800c1c0c48140080b9a00d120403401d9030034582c210030112078802c030200b0844020860300849180f075070500d9074000ca160194041d00f5800b400d04907141c01d80c0301c00107410720140b04000350311942c2c25078081d0044c5400850040340028002e4000c02c204515140310500c3d04200c10110319a07049020340c415000303030900c3c4440c44c0800180d070045008100005110400c0d15000c08514655180d001d03808a0107c80c0e0194191401c0746d540304000c02007502c3e5941e6444414400451015590003980f008040c4804000d005085e0302408010049030000c008160b00c44002821504e140d100e40d107103103510503000599005101034500c41040c0503680118214200400c0801803800705184800b212200b90712 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 231719676 1250 231718426 231718453
    0xf07061b020a150b131a040c0905031005010b04030321050a0e0c010e010c02040e0c03030316091e12020d021c05120340080a02060601020c0108060d0f0204020705 71
    0x900c502001004108002c056082404a8100c3c0c04035102c004541ba41c0d1617581045500d4500c0700c1d81c035010000d03c2000802c50b1444054422502030103850b003c0e00c50030000b8281c0101c0303445014141c441c2e9500741800d103031039230380d040310100d01c040c40c1030480d0303c0d4400e07070300c0d0b8155404d02a40e4007840c06c111021034805400d207219850f08041c0c7c00018100300d108280c3c44160b036004aa141d42c4942c040d200443c1300e0045419161409031500302d600e4040c4000030402c0707048981c0c60600400018503581d501081999030b2010001c0f6013003000e00f80300c000b10744541000100420200c0c440312a02c0602400100c820390340005800d2002140d005025038926608082002014401024540044008075066043c071000c00e01c00c13107003581603076000c0b00a81c880c000c0f500307400280084100e0030f140300d03003030070901b200d2820351f9040c2c01110340400940b0540c00803031a15030000c0f400b44524401a51b03104210f0351402c0c2000320005a440041d10300c40b030540c91030340c050b807194001807a0f400c0c0a48000e1112021028 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 231720926 1250 231719676 231719693
    0x801030f0f1a07110d091e0506031602060709080606010f020f010f021b1f0905071802180102030309060708070e150405090609010b0a0c080d0c02010b03160b0f07061b020a 75
    0x154004c0d554010882c078440d0203030002c615070203035100d51155012807510f580504800c06401d80100e588100d002c810020349860420311102c40342d03001e80c2503074020384550009941360091400303400019000040056219403081c1c1d0b400441c18004e1040768080d5402491140c00c440380051942c04042d00010341d0607048241614900402c079207200105000c0c0038201e4204e9404511040c3d5042c0d140d101c3c0482000d01204100300f03000360101c0840c83c00071110740b0300040029400011580c0318000440c488054941c004030503640708100e001d01070a01507842d16001c1b01c1c4032070020b08590511050014903003a0b619040000c5948080140701070795158102001c1121161008041600c141c2008005000b52249903007a5100001c0380d0030000500c0342c02d86000d42c51800b4010300074403440d14140b4800a030590540083e0486d803015825140c140c0000320104280c0c120f50301034a048490200304031444a4606401802d0b4140208800146510340e003041c0d03a10381580149150050b0311581e03107a0180070703c0d036 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 231722176 1250 231720926 231720947
    0x6010504152c06041e05060a03020306041109060315040e0304031a06040b030312060109090e0303040b160e01081003050703150e0114070c060b030f01020a03110304030801030f0f1a07 80
    0x10b06000b00c2d082d60800000d29070f48520f02075454034401404502003072415194400000d40b42c0140900e80f1650b03505002002500216410742c41a0304000314001f80e400b50000b01c8205042c064056403a540d5400500a20a00f90841013604142c3e503210b040326200381880504051403003042481018215640d0300c0c515041c2c003401407449245007083e14121598000200c580044c44008040700079600c550040c0c4004480380e0081c41c1c2d00d411b04803c3c40c0750b20004401188500e2023a03101840ba501d0f60615076000400358140107000c1181c041d07881071198007030360170030364840c01c541039110880e512030b0788180c00c090303840e07204407000e180042220f24000194024461450500402000b1042c850000080ca0b104042e00c1c1c03005121507081d44d08248108d070340108411034406022190704040c0404458000d5200119940001e0303d03008130010102401000c40e8040d80e0142d48144036642140c0710300041191803a4203c8084c00b444180304005188001b0440e00103600c010701603c43d1900590140c0010443e = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 231723426 1250 231722176 231722237
    0x106090b030c0f01020a031808070603320612010f090602030412020309220b04090c08070608060d03030b01050c0601030c03030905060a120b010509060f0405011806080402010302030601050415 84
    0x1c2c90f101626640068060030098241c548a10101c00e500f0003c1860700e441c4e00840094080c01c6030105a003a01354200c50103150058650050b9030810001074950108032140e100d001410744e9010507414a024042c00300301080c100000160389200c0007040046405803001107403420b40100400040c408032140d01080001e0f980003442c41c0145110002d00c4190300042c0b100796005240c01700401c9100c444c3c1c0315594995000c0e108202e0940c0500303007005008070784c3c451058540b08800340407440e607100300d10180c052000502811170784d00c12994160040c028031074a450401100b03004014903040100200c41c0250300030300c1c540782110304500b0020040c4007250400c0703009010400c100400c1560100d600c0c5084070b04088005031908281004075605e2181d801425030083c0b010035800151202d0324002c0048440980f81d40b0f011100750752313101f0101d000c00e1060002107094000090b006d54000e070007c6a00c10723014507206240c20f4852460100e0740101840002c0068400c6100c00c0040110340c1c10502d04444 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 231724676 1250 231723426 231723439
    0x91807060504122d06050a06050103060602070b0f0702090420010c05060f06010e03070e15030a03080a0f02120f04061508190203011b08150103051005061b0106090b030c 74
    0x104003500005500046009040070781440e6800f652044500c0d4070600d40c0407408040008100508101002d01407d9980988039803500d04009aa58000d120700c1003151559000340910a10388490680d00e60048083c50414040800400005075078504040b80b00d94411101c1050325030038861040380720484180924180003030100481301243e40080d4180e44a5040c090389641d5503075050048441000d00c880140d014448e040b008980c1081c01c51419214003c0380080203004089103007056500d6040c5000034002c02d900b04003060400b04d00ea040703150505014000503103411014030034220f40500c1283c039070801d0350020003030204005940c019001d90002009007950894107003003c0030380340d80141c250045203021400074442107450a4000f0080000b844104c00e2016081210142500c1000c075040352680001d070441d0152903019102d414042c03404416418101c50510301400b070750b40e021214845c1d110b629084010641f103400d00800d40a0003a2800c00708207260040107152910044d0301c02107202d4034 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 231725926 1250 231724676 231724679
    0x180506010902130b070213050c0d0e03090105250804030809090711030f0d091e0302160e06010804020303070f1b0506031b0703090e0403020d08090303090a03050c0705091807060504 79
    0x4154804a0081c0d4004c14201a5902c51503c000b9940c00b031400d080300c42d03807810042049025090302c1c000d040940071903c0140724507524890303040d480388507940c000c5005c1381003800541d80001d200022960302c0c0300486200b1411141c680c1302c1a6964105d54000c55614000180700a00d504004600b01d801c0340300d604002900620420300b107500c82c05683d24401c041d0501003445203400f2095000215010b41105040319002d40c07614030040346c14203d44058000d8802c1c0c4913900258007034041240122026142c4007030f10382e180e107801180c50440160091340e0512081c41200045540e094407000c0e0980f11305041181c60200e1103170031210149550055114480074810490000d450704031502ea00b5180d00441682c8945038603050f2403207607080d0002c00340790720054100400c047c0c0019100300310540a4541c881d20b50381303112034641d03244400c076001c015580080d80000c0000b4010000303028034a020342c060362003058552010440244084417844c40c04403d860611408540504c07104001d001c0c24948580f41c617 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 231727176 1250 231725926 231725947
    0x515061305040203092118010527011e0305010609170303040f031103030705030a27240c0201021305010c0308010303110307020604120b15130519180506010902 70
    0x319030510a079409103800100180490500344100c2d0120740c0001c51039444c411038020400050b40281000380c840b652441095501907000b0401d540901070011400c0c0060b0200c1b180f400a004203040d42c4506120000361881c2d04210801a49076000f8a01c1d41d001905600d0b0540090241105a0041218040c02c0030740c0c2d200088048101d03680141c0095000e01508100d00d0111500d840341079515805000100500c2021540701005500426030302d0000c1c4810348009440940480121524a070300200700400d200c0099400d040c051112070001e5503100c201d400614803102600c04000c000302c0140d5000a0001e24040002c0610000d00303070030318014440344055a0090005101800050140001101e6002064808000700c807500755000d00703a00e07121a900d404c105505885170200310b445642d03050024501c1d00494808800e21580105801410b030b0b140c0394968018000034000d41100901c551606030181500c5c003035005aaa40c2c854918080c1150b41491400d0cc80103802080b081801045100400c = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 231728426 1250 231727176 231727207
    0x30c0e0d030503090a080c06070201060902041d15040e0d12060b0306090a02090607080301060305090a21120504050a0209071404140d320109050a06150b03040501051506 74
    0x2050707050a0a564a0715441e1120385400c00420000f070220600044498185102140b41401212a9002801a161104d00d80003d034003d600810301c0d900800036008420021020105070085140088206c40000500c00304045d100a041c0081c500d074425000084203684c0003400d101c0034801564100116401c1200d200440d1201800b5188a49803550100745401c04aa04460750b510000b44155a10301852034445403940091052001007403400740000c00c0c045010030fa880c00c8642c0801d02902c4031b040401642d4440c2c40504084082140294681022001a10405e40100c1c011030007044071a8240c41004400b80004100000300324001c204500301c11010b200390b0782590650324043da510300c4100040b6082030390441001d80003a00f4500c410300b811041c41c01c0340c003100c0e6600e03230444c1039248081441400d0740c3d0320000042c1250b1001880b0404240d4a6002d00c1403112044209021941c0e203000e000740d20382080d2825561070b591041445209446004403495111003551080d0914030340c6628180c9 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 231729676 1250 231728426 231728449
    0x11030f16060e01091e050406080d02060703230f01090b0604140112090b130201020c060901051b0f030a020c0a0e0c0901111c03020c010c03090b0103110607080703050a030c0e 76
    0x9120b080c00b000d8250340e001c0c1004802a121050340c03014400040d44c03000402100f10f00ca1039001d03e00d400c03404961900d0110b80050b190030070350002c113802e484081c0128000d102e20021541c0c081110030b0803500d100200845a4020f4017140ea6402495052000c0710301200c0101d407040707200f18800c100c2080441071364507000ca00000242005c0940900c0d505086000d81030041004040754100c0e0308101a41070000021310b03049000380d00701d615940b1500c05011149c031030398008501240c01440f02c3d90030381c440014811708030707030424085d644442c02c5070014070f03e10f80019243c83c001d60401c80d064401802c00c68108002805c0011110314035090140501003a4031a40844a04120740030501c00c01c0c500c01000b1400c2811020a4005c103c03040c00c0c1001402900200e49008031035081c4114110760741d21901801c584903400440c0718060b6469580c41c004880000504150055401d01400010955010180100e60700a440e21542c0b4600990020221003c02140b442070041c008039640b03441d240e681e40c0302e1 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 231730926 1250 231729676 231729689
    0x50d05120103200d030206070905062106030102040b0313030e03030a080c0304111011071d060d1104050a02034515090307140606030a080a030b0405010311030f16 71
    0x103e030f0f030034101c030040b5800954030071a507003218180003079608069000895520071003c0d5a03410041d15191402c000e031031700c1001c1c42c503680c0d884e1940b055201000d24059640d04410700500051426076581d1082e4244e41007120400d0314410000900342c24503801400c00c1888100c1180a10300c2c107001c1c5c450103040c00c100a4501c159810002c00002c081181201c4048040351300201441c0c20526403d02c000c1503080141c014448600400313400066000b10240301741504c02c005d0001c401960703620004e00011621014058407194010288034240d034566100b41c600841402030b0140e034a240c070b00404108008013441004841006071b0400d000c15654035503000900d45501e140101c6595940d030316600c0c040640710800c43e034840720070500040510000c0186412481888007403100a403107698075884030f40c1280c07443d030981c10040180b00010386c010010143c0711b84600307000802c0c0e202000840c04a80090b00103c6001c401110414124501040350040c8007031803030024102c80f0044840074003030802d14030541 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 231732176 1250 231730926 231730943
    0x3060b0406030b12070806062b1b0e0c070c05030303072304030b0903030a06080f030f030709090c0905041802180709180603031d01050a0f0e040e010504050d05120103 73
    0x2020703901c04c1d0922002c10500d1003210100740c0c448000c43d868000c291202446070344000004028414507111b01101d4032000743e00b01401c14034a840b802d54000c281401d424000558000114000d6480c0840f540079520605816072104000e250042c1e03003423580d4002610a0b8010700401141c1980000c0c5084030400c0980e0b140c81c00300030810100e00c50b0189420051054010100b0084030344d40010103984103c903140000c2c0415591542403507280d80300300d070807007505400400040d810300003008000c54006a0303615000d49419a607030f2115044031014071803a00000d501d0502048145031601554101d12074540071050300810590016140345c000c49103280e00e10700c0000000d04214001e60040008050041c20720704c0c004c0001400e00000c0c000c9000813000309041074001007460b5104900c00f004064180c5880e4580841c50400b95405c003140041d03c03080021424030007030076846034003411000300000c00000c1a43d00b85071070070508040c0f1104030310082003030900c400c82e10b50b03044c10003850450350001c1d401f = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 231733426 1250 231732176 231732191
    0x12150f010f1401031e060b071509150504020307120308060301050916030201031e090f0b3106110409140105060c030406080c070c0f06110d080a230108071503060b040603 74
    0x3c3c2050282d10720504005c40f80b80c0540040c00440040c010f200451290a2103440300c80320307514150480c0d0003150043c0c5600086074165200d90b0082c1c0c03280750002d000508440c049641d80d200c580044104810450018440e034040c03081505013400f0300c41e00400e00c1c8014017542c91901d0300126210400d840060304054850009101c0c041440810005441c1031241c14810105103062055000d4000700d0122644000100000d5039244604005e20300704190702000c04941d501c0b251140c2480c84203c50503600a50b440c0082d8a40c00310308001030000b01103442c40841e4100424070144501c031016840207020fa030042004000740c10010040b00c0968009040c00345c4140c0b5110a060313014021a0300040440145070008100d082d4460b1002080301c605990359131409066052890700c0316008035440c4041071260300401e000d0411a00502c0e42403550036402c84016160303074600c054a071030030303070050441da0400c0f4024028100d14078103c01c0108498141406860300e082c0485005129600c036600c00c140d44c524a = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 231734676 1250 231733426 231733451
    0xb0306060d170a050c10060308070f020303190809010606030905151009020d0f0605060a080a020a0c0203060a050f01080609101a032a040902061812150f010f140103 72
    0x148112441c40002d0310b0b200d6182d100068000e5100b011003190510600d11a00c2c00707003c25000b42e4013a40e41c400719441c1810981d603940881000c000740300300c0e8103000038030540c13213122a000d200100d80e0342c803955080c1050810310002400c5460b150003000402d81080d0214003c100001650100020a075100000340c0c0d5030b000300c0881c00200c0d038210404441c000280415007040c00e81010004901c0400e00308040c66982003000254030600c1c61420201e11401c0001c0c1038003d80d5806081e0b0b039040b0741030117812820142d00003410702400721840494541d50b4400d100301c81384d0054030ba6001d4203581e80244485d04140504a030358140c4918000326840d154002c00301d008601100c802405503016088552074000043e0082c0459041c25290303034451040c000510492130f06020342c856454019110f10b1400c42110340407125240c58440382b07030300700001c4c06a07800800d4042000c010541d43c02c400b444610b0510b007540319507500041e840322400c845000e03402e010203010484404c0740c0c4071003401d0010315201c2610 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 231735926 1250 231734676 231734693
    0x607020f12030306040c08012103020f0313090606080105031b0114030103030f030c050a050403060f0b06040e0403020706020a02010e0d0f0209011e051c03050a03060e130201030b040b0306060d 84
    0x1040541c0141e400d4540c86454040040510700926040b1010b211030612070900321801c00c130034400c40200c44403030803508005210340c0003030014041c040e1040da00e058143e10010361a584c03000d01a0061030041180030040c0d508103100f003801501051030302c1c0c0601d514000c006580c0310342155100101c00341c000180c8080c1d0b030249100c00b00700a0401d01c105d0300ca681d6400d0142180c00d003204d0542c0403900f0440481141031040c0300312841e0072090345482d81024195151317000113282d00035588009950b60310010407150307034100c0984000c20340402600e02502c0d081c41c0c000d040809a074000d205561081c00c2d4200141c0c1c00c0850a42c0b020019182202c4502441c10300003c1507562180c003a412282e43d00c00030844c86465801109a00d103411030404000780e8a1042c0940d50200c0108040454282e04031366000901c00d83c0106441403281c80c0c041000c2d0b45491580a00403020388861000b607000b20242400c658041c007440d0045d04017100e0801c152403e83d1b004c02e0300d48600030a024420242034121904004041 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 231737176 1250 231735926 231735949
    0x10e060c011e020307080f19020711030618100501050f06090f1003020c07050105130303080601020f011802011b0b01050103110708160201090f0b0904020a120e061503010605060702060702 82
    0x4041044000b40014200e0080d8000e44482000503c00c0c800a880121569150b9000ea40d20300307031001d10002041a80002500140c038202d514929040450089540800145000302d80c81e2441030303048200000c05914008100a80001084c00c00004011603a9441a080038004050310b103540d84154020006003040140c40a01380e00520400d000c0c0c015691582c0136003540c0d40e0f80811140c589440304010f40d130b00e00070b03024114110071140c0000c0c0f000902c50000c090300980180115080c030400c2200b12030070344240b0056805441d19840f224015903900c0302042c2c656503008030103059034000329202c903a121101401031906042e180c0311800ca10040c85821100403d42155005844000714074020050702041201640014181a80840c100c041c4103402c0702281d409284052030700700039005100182d0000c494400030b024040341c21160a2a0314012090f810071800042c0800d1310340003846400048003070804074000da00d0144140495111141114101c03901114074075200e00962000580000300c4 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 231738426 1250 231737176 231737201
    0x20f0d02120711041a0f010e1507031e0809010f0219031a1201020301080705060309030a03110417161509140f10020a050f010504031b02010c1b08010b0d02010e060c01 73
    0x2070005c03280c550f0b0202c9813070b074104440866070001102030040046410060b52042c503603000c281c848a994141c4540801002914403a08003042d0b11000078520f41040c0c031043c800440802c1d0f03114104900220203200e642d5035580800800c50500090030203e80580110a032900241075135080134144404204038442c010f85402085500c14840346440315010390802c3c410f480c654884c403071000c034051070700600b80c0384a00070700c03002503091180f03151048015043c030b0903188103004010000803030310391851590125940080300c000d005028480700d51505051440c0e2181d85c42c150691074292440307500c400b1200440d030180e60044c0b404042c90001411000d00340412592010a007808151102d801084100416014405a851030503d0308201d03401c2c3ea0301120000c000901c151054001c840c0c0200078a950140185040001c00070156181425040d801c41103411629550b081041903210901a043c130303c50040c0c501c0314220200783e0010f00140300d103000750f86c4a064045042c24924200b58840d0410005 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 231739676 1250 231738426 231738431
    0x11070b0313050f06010302010c08030a0e10050609070e131104050a09050f150a0b0a031d0616053f0403031a040218060a0203131401020f0d0212071104 66
    0x8004001e802841d5020300101d580e4000d203201d03480400404035109040340c5d01a1148114213109036034524450344000d000070380d8150b031200300000b189010805444020f41e029400929814440304202c11400001c2502080004508030f081d2280c03108801740c13500e840c00c054007240c40c06000d80d040c4800d01594000540010311103000042c6404150046030040410030311840c01600d03602190201c10300744550260308441c440600f0005101028001c0000b20178604c3c0000d51079518109a5001d0362141858000a500500500c528682944c02034000b40620b400c01da813a020b010303040170b000c09140d4565100c00b41c2542044040b84c0159408016a890384400c40c0c80861a040c83c018004000c1000c10aa81070100d804040c0da60626200f00c8009a60032035007448442400b5040041603482892440d00311302003071003194143c00c0710b0b1610710080c043c5608014407501c2c07640002032810803900000080d0740d1040c06a00400f03074007c01d005c0d1810203400c0c00c1c1a41c2e03210701e040c04800c4051382040107401c9403 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 231740926 1250 231739676 231739681
    0x2070e0c0318061003020d0602040504021c06050f0906090403110d09141c1203150305010b03010f0612031107030c0e061026150a03080a0f02071511070b03 68
    0x52915000310300c00c078640420a88005499090207584020458507005010240d50381030006d440c00c2c070302181107503100300405450b007500c540c0490141d80000204007a43d824040c01c2100606a0340100c0c0d0150106407403802c0c0300d206010000b40c0c0c0302e2000d41418002c41148020030140340c41010245401e020000403100540048030f030042c00380c3c00360300c100740c46140302961111191400c051107002c1c00000c00501c031034540d0315403100c09880f407202c9030410074195209c20710480600040c8540c401180100d000003400c10152090ad825580006400c0902c140740540a006201000e041810915098a01080f00400360016545042101e0b00050441d0b001081c1c00035010103440c034514441c035025907903403a0021050005803034009003e2a0140e00c880345200607600c8140c1c085003d5401300780c2030030808000310700b4030200e501e910b070503007054a85080024202c0035440e00a41004905511440200352143c5030000543c442d081a02180080000349a41d0075406081000f090380507110b000001c4e0fa490 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 231742176 1250 231740926 231740941
    0x90325030305010b09012c1309021509030d050d0f02031303110f03091e13020405210d03050406091407090e0c0a170304030c0e0612011b0f02070e 64
    0x80400081240000e080c100046000f000d8181560003042d01038482240500000e168044680380c2c072229004908840703910b407080c42e070b82c4001d184030b4403d4116000484560900500403020121441034900d07050411035100700f503d002401c501c0c280c1140c1b40460f00c0700780c48000308001d01601201c50242c14000700501002c0354000704007024440c400d1f1180485104061842d984421140301d442d03d1030f400034400491541800f0070b03000000c58642480c111b00300300201c00141100311948507046e40c2a400300f0148000d0420141841d041c40d41200b078200050165049241e80c0c042c0041214101501c560103e000c208864000e50700340760b405100c178a1500140880b1039591001807081500300ba0604107000f2200300d01003014020000041d10501c501d50510f03010b5894407803403981a404c035110801000020500317841a510240c65002142d024030b080240c20050360384144030b10007625914100c9080541c02035440c507540800d03881c0c28004e0710848012020307414025241c0c01403550080200401408 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 231743426 1250 231742176 231742237
    0x50f060d06080718090209011703040b280c0804120c03020d0609050c0105090117100e0702060613180f0c1d090f010e0a0f1104020f13050102010b010e090903 69
    0x250740034841001e01314120b0762800e00950b4107074800030350080f50340720040c407201c003202c07028504030182c08003240d03e45a525000070204d80e000c8110451000d111445a1840701c45050611250a11524101f0a100c509803a240702c1c5e4811481080d03401040c01118800b0421050400001150001c007100e60301c800500307000024150004046406001c0c400348110950700580642c0d100050603914034582d0b034008025254103003c0517010380c4003400c0000d00025580924410a8841d0600e0303030162100741800814885940b80001c003540090f4203018161007040e113280c2200b03401da5003001c1c45609861250a01c10950325144c0c100800202071210454219000807405a0054420310121603521449801c054203ca05001d17417622180c00001481003c6000212484641c902854500e0f03072082030314000800700e0340301e100c42414001000c55091000f00740310080200a11082c002400746180301400200f51000d10440301e4450000d0b0000300e41205403c20070340c2c5060861007110510400b090055011 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 231744676 1250 231743426 231743429
    0x50a050a0e0711070513140604020c0307021c02030106230307142e030606080f040b01030308180105070905040f060b030c07060609090308090f07080607050315150c0c03070b04050f060d060807 84
    0x316001d0200170484a041232b10888e003014820030080c40c00d2140e40d0f402c10414031102803005900e0584010b034900942c0e000e120341c00060210000d07800c024a06441c0d854010510054043e2007504025002c0160701c20007a000c0e00e07407000484540b000c60468000507440c1800c001074420015421b070305042d0310641c140e40f040b0240c4243d82c803130000343d545080c3c0d141d0940100b10380c0286003100c21001000040d001d6000d0b1904181c038240c040d050280d0700b10700c25003114000c488005c00142441c0341002141410710809e501a80700f50014003c0c60306122103600b0074030000c0d10f4010441c50002e40c000a01019511075000781886400500580c1d04a0400030110081560a2101800b800b03090164080d00054500304841d02c0314090002d9a4408005a510342c1006264501541104950940540c0d034000c0380710389600040704c0181c903482e010680310329101000300d115020b51300003581172041e107a403201030340e04888085030340c0035900ba582804103c040c001c1004a88100b030904001044501000c00c0c0d050 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 231745926 1250 231744676 231744701
    0x1103010807050303071e26030a0f0c080f060103020c03030903130806040b01060302071103031c0513030e0409050f0604061b09031509032007050a050a0e0711070513 72
    0x180d4481d02c1d602015228460040020854650b50b068031440e80300078915140c1007401080c0101d11084011082e5060a911500c2c1a540c0ca1002007005401d20035880350344a84c030000c4004201d90000c52034080c00d80d0301d000d00090314010300031000580f140c1c86601203a00f840f1024003a80c1d2641010055660b0f41d170045402d80f1000750403144007040980c00041d101b03202c2d070303003081c041c403100c0c1d103403000503002980b1481050300c149c99010003407001da480400060260a00708030060b01c9100d410341c0c18008444014001c0088131003055140e0001c20340c00100c0c90303600501200c000402c078405203044c600e00071010605001e10300850b02004240141765001d028940300140004095800c0240d003101e801d90240001440d4000360100302c0325039002c550010b815188030382400d01071a0000109c01c0d051a084040303004484d8029a82440f0b2070405045040003404107444a00e0228200743e400056028003c041e0020000b010420391a420000c01002004000c003518241040c945140301ba800ba142d901c000c032 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 231747176 1250 231745926 231745933
    0xd0b0619031a092508120705070b0d060e0103031808010605100302030901060923011d18071a0706060506030721090804060f0f1e0507020a031709091b16080d11030108 73
    0x4100b11b90b91a040722161903102d0040c200503818071307401c90855000030020807819955040040b50f6010f10300c4034507010314000d44444c00d0040d500c084020300c1110381c0e00150b9103a410064204005c4d201d03660581c14010160a005d44ca0341d4844200314010011540840a450308003d0106005040303d0303c00386041041503c0084103a0b2120341000a600981104030f0b0440c50440002d05210044440c2841e603080d0750050b680f84a0b0768000c52904801c05084402900e00009100f804005480c41600000c09043d03806a095241000d03000d0a82a02c440000441d07210001d10303445500001c0c1d201c040010b61140042d0786982c0c50360310040c5003d040d00300e45408110f5400e075600c01c503401001c01344001c419003681d1110340107000b1822142c54001290807030700f010324408003000040784004102016041c2c018030685410b07400c1e041100400010309070701030b1501c0e0a502817440a0300c04086900303140351500615058425854003030454440c1ca20b0301a10fa42c64078040700350741451a00158125031703d00048 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 231748426 1250 231747176 231747193
    0x60a230625150606021c050c0708071514040e04050a08030f1503060610050c1005041104062102061806070f140304230409020d0b0619031a092508 64
    0x14202110f0850048801503445085a0701180d4488440100d001e5024608035041020900c21189080925080550b103a003044100b4400058485a1036990041c61b18160100f91400a100541031159008014203030403041e00203002e00c18200160750805030b014101940d60303d1704205500c00041c0c240d07600940050012200c41c0e042c40c1c0040c1150045000800007602c44c8020701041e521030740840c2140c0e085010740584110300500500c03907107120ba80203030481113007400ca8808100072100950801070320b440b0302490200b0304051034886204107540c10b4900c266580f82c41003c0c14900000c00c0440d43d4404400103c100401c515502d08801035482018041c440600344120303d42c61b0b0003076000d510014406d134103000403844184048039401070000b90000800c007400382c01148104522100a484002c07140c01444040c7c280404000601240d8aa94a802c0d50070356940c0400c0c2209020503403042c1d0500c0e030108040a0082c00241c030105044034442c00b6400a1088034100f1541911540701c1501640c0c11 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 231749676 1250 231748426 231748463
    0x20414120f031c1808031501030e0109050a02040c0810150e0402030411030610050310180525090603122105090a0b0112030f0804050c04020d060806060a230625 70
    0x280d0b02c1c074203034414240c504503915400800c0c101402e0300040788c109a02e9044140c0d00c00428801c0c40301007030188000d00885402401030005958206040d00c04011800f070400c4078040550300b8503030560740c03603c0b80030800c082c00340411521006503000c1d05a0280c400070502082102e0304001803d0801b09400740d8900703560b464128595442188a030942540018244084e00e00b0154041580d80f1148070492541501c1c64440ca46003400c508461022040010141400500720000c8240141485603050202c20304550310b10881002c1508050103101c0007501000a203110200161080300401c0c0c4204841d240c0001e0195940070407010030768902d0600070020446840b04141d0845507609621078040d1045168412201480c0050042c0c81a0007100c01344da0055443d13000415a808404102246d094142000142409030151036507200e9042054104114001500310b04a0903080190b0310145120b40e0000c14841e104a483c030188294000c0f01200200410407810744010380240c800303034042d5a0044 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 231750926 1250 231749676 231749711
    0xe01090b0901060905040b0307031505060112060f0504020715050405070f0b040b0301140a080a03050316080708010b09040b06070609060b06041d06120607020d080a020414120f031c 79
    0x74140061213aa03c2800729040c5600071002c01c00001c2c040384c410541d640c81b031000880189625080254454082c01910340e4001710020011181180411080d031810040d8603510003d480b4850207540c01046080c24010724011080300e000703c0000c180503600c0c0c9494881c2c0c8940c20b0f4050300b2082e074070b1a080401c0028815040c1c80c03c1e00c0304030707400a15590030410110140240b416015520440c1c41d4004121018284800092140300f92116601d07814060030780007250340074902c0e100400a00004101d0542e500c45491411070302c091038841d503030300055800306014110211600341c02000005110341040b07400c0d48201b0409002c0d41040201c1521001009201d1255208181c80d00008008401d210601d4400d015040040200080c0009002d074181c6814000122000005a004070412800d00c075008521541d218185203011480c1504003280600e100c0410000385004440c1886500c0400c90700300160f15054580c00c04580d2501003042011205070001d140850380c1ca400c2c0b41890040400e0301 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 231752176 1250 231750926 231750929
    0x4021005120411040b0319020a060305130b0a0605190e0c030408070b0601090e040f0501050105120a030e12030c0d0f020304030b070e01030b12100b03060f0402190b040e01090b0901 79
    0x407040300c065803640c2e01d5918142c04044180765002e5940c0690701883c1d50200944000c0104d404481c070b000c112640104240c000c1280e1291003403500385000c000c1414206800e405016078099060100c940300d0384031440043c52284c1140e908813021b040504409070540c001e440441300040404c3d035041d5981801290503010544004100304400e1041200086000c035043d5801001031525941d22561080300e007030381c000c0035a4282c68009040e4801e00030302c0b41c00e00886025041c282c0d080031041d05541c01d034a55604414002a040019000d0500166030710b8650b440b488083c80c80072030380c82e030f40e81004040d100e45e80d090603040402c1c03424a407401010f001000742c4040701d400119a200c10354030010700755207501e5944040e604041e82c40d810242141d03034407110701200420204c0200351005003820040120340a900c0840c0c420b92114003080f40d4000501c283c558007a030306a68a02c64948143c1407170388042030682101c1e080006c041804240c0d415008010360407114441f400f07024400301001805601c0c00302707 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 231753426 1250 231752176 231752197
    0x3090405150f010f030b040207110907020c01091509150216080c09010b030c0d1d150c0901030e0f01091a0f0702100b030a02030708010203040b0105090906190605031504021005 77
    0xa040b4005003580075120081e50548503050114284c0080c40010b8200d034000c5030100e805041c00320428050342081a440c9038415900d00042041e4001200080c002c03070040c0c49222058000007100f44041849500994000d001507141a503041c091540040d403200415902290521401e507400600541e000400302c003450070203001802c45900302850142c00b60b000410581c00e80008004118511149205505480e03078000303042043c105200201c0d034200b1040c035050210303915680092080703450421080b12400042420f000801c0d0301c03104a01c6003054444002201e240d480c041c101424411440002c1c1401c40420050200540c3c82007902007074801c0544400c80168444503114040303800961010b648030400804a664401c0154002032030603c0329000948a80d40100a00080041c1c0340401805800102c540011f1442d1208950395a030310000c0440d1440460b0302c3c14140000c1d12581300314041d140103000d45540701010b50350180c1040c01910124041c40b1795001c0500002e1050003a01c4c6038855 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 231754676 1250 231753426 231753439
    0x90f010e0604051003080a0f0e060c150916080607020d1b020103240b0c06090c18060d080408030309100b010c03051b06131509020603010e0a0b120309040515 69
    0x1501c0040c80010040100300d0506011000700100c0030450010281c004001d0070b40c0c0360300c0c041d041280020085070080300c100d8040d940c14806010a104040b030484aa940c148071400800e40c0d803040d01c285010110140710610820111020a400740d01140c0d0600c5004a5001c40703150f04c2001d44101c8895072401040190b190a40140c0d400661282e000754008904a103400742c04082c0e1a0240050050b4540c090b01340c00b500061040300c1c20034213000059007d83c110300502105a40c410100340716404408561507441c0501d4000717840b5981e01a014206950414901a01e07203840d42d03891543c0ea4015501f18201d171003840f50b0003001c0b220038003807034400c400306946150034036001b9501038609410a43c6585203000708a05086541041045494443c0c5000b036a04c0403214210300300003006000c4141c5210207c0d080607100c40151700c5500469044030700382c06443d80c155940c800820f0084c034602d580075600c4504229409905800000070388201c0302c1c02c9030100030988a46d506581c00b28102e030b260b181c000a = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 231755926 1250 231754676 231754681
    0x60305070e22060314010605010905090c0714120a03060e15060f0f1b0706080903030f06011b0203070608010609050901051c03021504030503070306081902100c05060a020306090f010e 80
    0x808a82541d0400b608410b4045041912541d6102040c0011800307410b00b03a40d1102c0800480d0f902a0040c00202400ea41d00c1c02c040c02c0c51158100507200d2441301a000b841741040e03003100b0f8481041504142c60442000a86036000c00d40d00401034509440b810507603120041c04542d113102101c02485500c10003c1c0031600e403250352607100c1256000303039031250b128100601140d21500184000d90800060390b00c06400e000c0d044c41809400300401921842c0c1aa0040c000c0103010429010101d0304014242000d0025150108040c02112404100250503002c1c441c0001109500114101d050711550b40f40d020300e035a150414020600030911906074031202240c400f00d0417100303018503104064060320554043d9508c5040d5806205002d540c00c0780003400000801902603031520413080a010001c018045500c002c070f101c40e000040c4030130007a03ca15503030403070306299502444100c01030381c1e4080c05940311880d0180500000750001c03640a4010300034080000d40035101c50fa1818141c441c080100703110340c2c = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 231757176 1250 231755926 231755959
    0xe0f15120718140a0b150f04060e0a1805070e060703050702151b0a12030204151202210a0b010305040503033606040c0801060b16062004060305070e 65
    0x1034046020110443d6443e0303c038181e15601c06003801d200303115400c4040313814501c0105208400c0500700001e0051501030149500813040882201c0480e066072605e491118899000510020125800510428001c9150070b2030326200d038010b6071040c0d94a845850f1190844028810907216035600100060782c1000325800500d440624000f1a40c06a12103034200b450540c5913815a00c01041000881e5108109900800110360f400e44000c960302c0c50700b07506140c41c005031203030402000c0581100b48400050100000181503040d03a15003c151000400b410710f0512600c401024141e44e03040006003418810403055000c3c0c003925003d564098004c500e5584c5e440101c0210f00020f4010803205200040500c080900048407195030310b8144010f44010306107071030844001c04680c0d010784071513414aa41040a0804201a08d0003500041d900300520181c51803e6401485810202204903100205034420840ca14002d04284d03003140d03c0421954039104c4c020380b20590203545040e88407005600001c0c21 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 231758426 1250 231757176 231757199
    0x12090503100f020706060602070906050613030f0201020c061809010e07141b01050f010501031404050c0607050102280906031b0f03021e13090605060a0302070c0e0f151207 75
    0xb00b818610040c280207265a0f02002d407034155008200582c412001440305112600c60030000340b00840c3c03040e2805c0c0c0c114500c880039403000d00c0b020305008114112007040da4024004041c28020081c083c5039500044d01c0110601c1100c44e04942c0035400790b00010600c1000c401d4003a026190503100c40f20460b92a8020040e03642c0440c40c03240c1142e04407480058080800d00405000c0d03242e00d10505040e60500340014101c60340f60304800392164140040c84085500482c15621490b030540380c00b0340e15060790070001d0180c41041e5404560300c00300d407074543c5161054030001841d601c5560710441c00d40e589160072400c0c0ea900802c42a0f00c08a80c11190307803640c0c06506040030360307400e60030054240f80c251298105036101700d000401102c8000500c2c42205d86030031380c1e203c1c00b504849904000b17950429003c07400ca40034000d1490b051590004020302413003402c07a83c03c0f0081000d0107214040745403601c0d2000303c0c1401a101c94121201c1c909241055203495000081c0290105c0000d012462400801005 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 231759676 1250 231758426 231758441
    0x4050d0503040806090709050603032803020403020306040c17161e0e070c291902070b04030e010201060e090307020d03030e012906040308040b0d1d0a1209050310 71
    0x1a14031042000040e559010302c4007a1203855200003030030a60745021f0b47c05061714030040c030841c443c5d0070400000c1d038145d40d0040e9034072140d100da2034001d881c0000b04000750000c1c422600080c0d0302d80b24141c03c000c01c010503d140c00b0302303441004102440700a900c118050b0346003450100e5804061020390140190314140312800e070340d084482c502e101119500c0b039079902c01d8a0165442c80000318501401c0b410700c0104d84a1801c0340c40b04040d91050402c44010036144110040c001159802c039058000c0a0509941c040d0756005801402c8250a4105440c002d400011100507250240d402d008000441c007290545143c89030a441000c0c5141904039420495240d514000850901d83d84030400c586009091081100850205078011507080502810740101519241c1e0148103d40410062000407a03800980301100c2c1d40541c03c42d183c003102d400b640042c080c01a004e030041c20b2108000000d5160004030000c45074080c10a10b90210201e4108076000c4805001c0d240d016441034003c100c29540702e600c03581 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 231760926 1250 231759676 231759683
    0x20a0608040303091a151e041802060a050d0e060105060304020f010201090c26060709030f030c050a0b0114010e061b0c060406050301240e1c0209160905030f0304050d 73
    0x16160605170f0b200e004a82564110070042410041081450003a03621058201c9004580e0b0744140a0b4041024440f8880d00004078061500c0390b16264074200400e420920381640280080d4542664080080c0070390040c03120009103030309042d0720410010022907014140c800c003074085e40c0703195110b40a0048003240300302290b045650b09c64004011a4007014014094400c1e50f030703503c2c12024401c041070381e00c0307500404980c59500082e007842079694200c91020100c0f90b00c5811a88030071268102907a03440e42c0700740e010304a405071071000d200304540340f40103506072001d44502418801214004440d58000340b250941c10035070400000301185000400690540700480403540c9140451010a21580040d481207010440101c010302250454014040c04441001d80c455031101004c3c0c001800700e603407031052a014203440c0600c1c1c00520302c00311403941c003e80c01505800040c10720700c14800e01103c061030401c0c0064642c1c0004103c41c0703400b05607c60940c0014000310308050820082054200c90008203c = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 231762176 1250 231760926 231760931
    0x708072d050733050d0e070509040320030c030d06120309170705030307060b010306052e0512040309030b13020a180204030b0a0203011509060519110a0f020a050d020a0608040303 78
    0x8410704400e2a0f81d051800b1035a0f504e030b00c171601c1d48484c0381a507240041090f00c54020540920032611040850342e0301680500e40500c0041d02c0c04400c001c2a003c11100480e180800079100e005054000700912450750f90b004200480c6980d0303d40050701041c100d100400080740300364100105408001940007240703c0a050700c020a545000117031075035103d014200c80b481c2e194281181690703010f1007040010917080d00c4030036100a0300f0440e404d24a09885040302544a0301441e180310b04d02c21030540312440b80c100302a0541d800c6c64100500300c00c10701d2000301e48011411000a20349440324500c0a11281c0c0501165041800c04921040c5d41500c28982e0442560078030000001c1040e88110500400d40c0703400060781ca5041036104409040c1d02c2c42464144103806000300300c5607030301c00b04444050301e13038080e000b80d400d041d0b4108640c1b80b03081a1000c0302500c2081d0304041446291040046814403c032109200305581d101031284508440c58080e45c00040360008000b042e01900489901500c6803400 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 231763426 1250 231762176 231762239
    0x50a020d2003070b180c03060703020708090a1e060f050a030b0609041103010305010f020f0304020f01111f06150c080c1501030c0303110109110f060708072d0507 71
    0xc140ba5800c070340d00a5541d02a600c0602940d00c070490181403050102d2406425562181c00110744e83d014003410041c20154001540700034044e094003514403001d0001c1815100c69914442d03805008500c201c22110002c6c2400c0c00a41140243c01032082d003022502c0305402d1020600041e0003c0444800b5181c101c0d1081180b400596918455007400000c81c420f802d0700c0c0e5045040c01c50031507056910f40c450813441088500d480c00c400009595005174129155030301d0320380003001245c40030800c1800b04801d10031611017404a403074240a241c426000f8120030400103a031411060811865048001c010461110600012507400801042c0e40850392007103035400c0b04006030580900134240d009a07140d03054540e09104240e801a07212042c1c0c40001c0c028010f420903034490485400000b100f5034031070b030b44903148202191031b00002d83d02007c1d080710700030307403211620305045507a10300c051442074031180780191108d9038a04c0c800100b00c210b50884010080d840c1002500b40c40180581043c0800c698201c05 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 231764676 1250 231763426 231763487
    0x30228080607020115060c051f0920100c08072603010609170c090105060a02070503011b09080f030f03150402070507081002040b030c03180703050f0c01050a020d 71
    0x81e0380c0155196400054001c0190642d07a02e8540a6004030041086048180010400004500700003c140d007a44040a02509079284000c100c049001030810620704201441c0c02c1003003100d0312900c4800d07100001c50415140e021500700d00120070050440605001c6500420b42d04581441c1800f401c1c3c0261441d9001c581903000d99802c260300c10307800180c1030507041c00f0b5025061046501c100c140c00c018054a40340c00001000500d05000743c5003d0b01000c6030014041d80308202a8000f004068000c104002c500011240c1000407084490f012a000c07080000350b2000024400310000380b0f40c805107040c60b8a203110303540540d1000d840c0369041401041090380a64841c0b009000640c8214010400307107207080c0e03000741840c101440b181291403060008001a894440859901c180b801e40480c4d500da441841b1094849140b5071111101e200f00d003800703c00c0000000b000009200844226010344070308a00444443c40f07102c20890058000d01d04814100380100b0203400f40c80c10094010328684c201d00d2 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 231765926 1250 231764676 231764683
    0x11010903090b180307121a13060e01020409090b090d21023009060a18021504030f1b1203120b0a030204050c0909060616081312060504110a03022808 65
    0x4010700984403240d4100300030483e1f940b4003001c810303204440744c0500c1d14100d04038600c26021108003400c001d48694601860040a40c110b5003d8010701e5010440c00702c01d0708110340c6202007254501c0f001d11031340d02c1d803040d5580554041c034100e44200510715012020142854041e4001d016012007a0702c0006005d6000c003483c1c1c0214032a101c030440c141c1c20619110307207214a042006860346c040240361000031980015502c4610743c1054050780d502c103100d102607450314024400d070382c0080c000e03904902449040040c0c0c40b6110b0700100d1b0720100362444c15102c00c41440e2458010000902060722160041d010014a40080506001c020811500999690082000c2d540c1c110b61101ca01c041c00a8814401e25200d00e90380d402c100e042e034280381411059041c1400003d008840034020b01c10100b54207005c242c015007100007400c842d50052071104100e00c2c00101a000c15141183c502d035946c2c180c00c4e120f0074422040c0e4105c0340c00400d100d4a109030701c150324040c00c2803801c44200d410340b04040840c240c0c4040 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 231767176 1250 231765926 231765929
    0xb0f06040501051b191b05030d140409050c090a09151502150c2101030807111c031d1207030204050702010b0618030c1f0e04060302090f01030311010903090b180307 72
    0x11800d00444003a945007103c01c011009107401c170074981b4481c0500840d14005514011000c45080104c40c51188400c158014020b950120300b13a9420801004131840c000c40c0602081813083c0d07104400b85484031051411380303030740d410b035240940c1041ca001c00c5402d104840d54429900103005851962510158018042100302e4a00303610310030000f91002c42000c001d0705101c3e4142200013204c0030b0350465407114410322400d08042d1002c150050002d141d07547e491005045805100d00364105280145006001c00500420000000c400300520515609200444a011b501c503200a40b40ea03d045500b044000d29019103c07404665032003c0100040e220076000b01405001e0403450121600302000f01884e1140105040b030060300300c01860354042604208011580380d8900f040640451402c02082c0117005079400603500240480a000c0824403640c4c40790305a80c00382d0b842401e0003010012250aa940c400c40080018501030380821510f0b070802c0140c16030356a02c1050149940030400045d18000c1035 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 231768426 1250 231767176 231767203
    0x213090209041b050a0501080f18030309011401050418060509010f141515030a0506010c08030a050a0e030c070b1e07080d0e06100b0310081009060b0f06040501051b 72
    0x11a244030820f804001020000e21044414003061030400000030302104001d8032000701c40800101003079041054190300c01c40f07c00740104a94030391a1517101c5038040d01c0d1480d50180a075480600108003400d00b1302070214500b88181400406c1c9480742d44060040400514100140d541c03094018000070003805040030f840103008004080d0300f02407803c01103450000d003600f80301c3c0a44070035800b0b945080c1001d6075405200768500190aa841303c005948074200810300034017580002040210281041e8029402071451000c10400f8410308409582d60748181000500141d22801c002c0082e80200c07030081c8089200d030001d400e40b159140820400640246404840014010840302e190b12014410402e000b11890000c241c40e0510101d401c10240b181d005a90b0740c0c0c0000000103000010499516004210100865078a100c50300a540b008190401048801034201038450780c49151001d03210982100c0204040d18081ca0f1000545a9030b120481304500c9140304034014144c074070280014440c1c00d24 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 231769676 1250 231768426 231768443
    0xc0c060c0c040b03030307090b0d0b0409030c03030c09030305190e031009050d0c12030b010c02032a0904080f0a020a050109050a0b0c130905060d0c030f0b0f13021309020904 76
    0x3400c04002c1501c8100020b280250300500c200030180f6407007003d03a401c131a247c034034484c2c0d150b4241982d24094400e881507660010308102c10107040680c0000501680c50080c2c0d0100101b02880c0d10858200c2c405100250010340b05000d885540b194030284e84501d84142d0401c40120000440880d0a00c241a5500904c185d640c81482e0140300d002d11070314041203070529094501080c1c80d42d411700c40001c1140a102015580c00007041c039640640c0d10841c0c0d0b140c000301101e01381202c13100b14101100441d17482c0f5052400d000100500303814080e94450082c3d40c0b1507840b6040c11500300300120341c0e0300200e034200218071030418410003080c800e105220703807076003e03a004c0e03c082140d5062078030114202918400c2840e02c10002c42250021150f414000d86410000124503070b100d81c0001420000b41714809080c9500c9007100008000c808100d410485228110700104c580d5240c10000003038408580004200c481c42c0b403000f00500d81000e140c00c42851102d000150b608282c0c0101c1e844400442d81100e0450 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 231770926 1250 231769676 231769693
    0x6160c0803030411010504061e090e090c040b121902010203040b04080304091b02100b0f0a260d1706010207090f02072003030f18040c05070c0f0b030106050c0c060c 72
    0x84904114541c0204c213003441d0f0703d0b09180c440020310700740d40e000c00400c02102c050240f014041c81440100003d1100d10002d0322103041c058179458540285420207031007245810741d4084917050190309050810601e40c080c0c41d8005101c1e1032550710320f0407148200e04600080001091007070405000e4000780c1440c4c00155100c0b4104825a400c841851180c4804503581111b207440290740082c174100c0310502040301040116000000c80c4410500d0100350364454200c03800031641c0078840152a4250814000c000041d4009003841d81e1034005028a403c0028201c080c162084c50075800d03580c1e0003d0041c4125004195a81000c03400c90303005c3c8042042a0b07400150311400e01282880708088015400f8240f4024400040061b9903441040c00b00442c6180208216800525450320444103843c050424007555030788020086c07030b03548558022183e50a0307920000c100135403c980e4800580b031004007a46d2440c0d08000d0b09507070075041200100180d00c150b40c4400519100c1c000903040b80c9441600611808 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 231772176 1250 231770926 231770933
    0x1302100504140904080a0e03010603020a08030a031a0603060114070f1109060a060801050d06020409050a1e020702060409020d0b0a0f08010f020909150a0308030f1014010e06160c08030304 82
    0x104a800400c0d12543c2c0000512001c158a134040720b1070780c1194109480c0f01d001e45008207001d004150b2010703501540c0c01e8000508550044000d0020500e155070402c10006001a002d584110204416800450a100041d415400b5140052031200d1a200540c1450702554940f950755005d50340484166410a403040b001e82494194035401c80c2c400c0320302c113000f0790404c40003c03c0090140b0980f80328090424a40c001e0000c030380d040318007900e640842442a45018680c0e90080c200c8040881c880241c14840c5101c01e082c50320a80e040b03658001c21360b070700d0980b81440004c042c0d0403409421158079500e40043e0400d55440011000400c082c441e10400545401103850031071f814000d0855070180100551380442d62485405540090441c01a5035200c8201020500c42400d83d040200b810070000184540c401002100c18800c14103a40c00c1240c4c1c0341c842c40c0001c0c1200518181d180811100c1d982d01d15940341020180048586040060502e400c0796118816500700c0c0d40d12801241d0800414041803 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 231773426 1250 231772176 231772199
    0x918060608010b0c0a1e0c080c0a060513090b0f300102070c05100207080610050a0b0909060405040501020d2408010507080a0f110a02010c03051f030206031302100504 73
    0x1040c3c248071660500003600003503601c07820511402810032511200d80e5440011210304041c0250304a0903143c121501c0c1c280c41543d03a8484520944a460950000902c11381718104030713503000d110303000c03032030859440c0890903030242050b0f107001544102da010f00302b41c00e602c0707001d040752822211240046c00044201030902e002c404a20b950301c50360f40108903081c0400d8078441000c040710300c03d44181c803030b170a00103100b2428203055420a451502820381070000991807046183c1c1600c008450a074481551981480d0180c49004d80d55500300000d440002d101d880c1c254485030303006024500140ca0150f010024070106c0c4c05ca800c010b00691145509180d220441018400252107080004c01090600240180c00f481004080201d059251000b149007140d241d0042120040100713039080c0c5400c81c0d00d4010303018000c3c1c4406040020302c0d201c001051030036000c1c1175410384103404082031030071800c42d001d011309540001c2200c0349070191001040010307100c83e0342c0d99044080d60360360305403a1820503000c41030 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 231774676 1250 231773426 231773429
    0xd1b090e250c031403060a121505010303080114030a330204150909050f040f060212042307061b021216081c020d2d03020a0e01110a060c091806060801 66
    0x401440030f00810039551034016468054440100c1414000300302c3d45030070450004020040d00080780ac010001041580140d005416250b800c1d040b6a09030328035105050b540c4599840c040c20b512090070001c19a400009004030301c004d00030010303c00b142000c4a00714184c3e8081d90207001c68410025400d4000e90344000c0c000054203152a00b44a642404046002800c1000d07001030003030307850440301d01c0c100082d80e411602e144000c3c4064910302d103058109560020108041e050300310919135820080c0d040081034001c1a90790702e45034224103080b4031840c10031003124403000f02d0b04855482d2050800704410410310418441c1c131024800036a08103c040c0f4280114035400c04036040010b00066055500896500001d034040e1900d0446e655288600c402154202c8699040c9282140245e8071040ea054008001da80a81c2d2100c4543c0302e16900110f452505803515144a6000004044c0c0083c03000e03008641504100c1ca03207810501d8490100c000701d5012802d03480c440d80e585400070013981c4e030008900350 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 231775926 1250 231774676 231774707
    0xe03010b01031b0e220504060e010507090303120603060f06031202120409020904090f0b04020f03120306040905030c06090708070605030c0910051b030d1b090e250c03 73
    0x2040d6004031000b488040c0c240f0614051024402e01604607840e9100280c0600e6240c3c500303625559508030790080140015602036a025041c1a684858070f40c05004245c01501a03640302c031512441c5850480358540c8546030300781019190100000030546500500f4211100f01600061152540c505641c600507032001c40740c1590010b1640c034545868000036102101c561000c003507030f51122440060020500d41000910441c011004c078818881340100d40c5200364420340d42c00c0141d000f95402c06668800e00381e040d03031250004000180d0642443d41211141502c9141103904010001c2101c40c1444004c0b1158100350748980700c104036144c005c0000b0001010b040c180310349181000c2d1807144052040703070314280c0a24003459440e03002602c40e100b02d940740004080141601a02c0001c090b4503a403045003010700b210705000c8407400c1605842d010344000300d00c54440d102a07600e0011140d000b01c0008240c109075010f9041001801e00c1c1f80022242011060307516840d06211614000d03100c0c080813030700c1c1c5 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 231777176 1250 231775926 231775931
    0x10020c06060906041401060507081e070c050a15120b091602070b16080c0f030a05040801050603030421031e1707020a02010906111f02090307091407110f0d0e03010b0103 74
    0xa56206440300741160547c0c90745e01d4226520142400c203c01c00307100761a03014001741c40d183c0111104510f21000350105500c0f46151440b0280d90350204501c034616070040c80a0010624110496280036415000d228040d84601107000d400758800a078803160100d90b0340d04903d40c0340c0c0c0d00c250040e41c1800084082c2c14031440701c50038090541004100b200e001c1c080104040c3c80066811003080c0200305511a400b0110201e030346d40c081404000303000d60043e00c50700c0701641c2800e010410301e15020051b6001e5903c000c500d00e0100244100d001e254a0b5010381c240c1c24440d03064146428198035014000800850752103806c901012603201c0464450010802021500483c2902006030382c0702d51756030101c44141c50b003004440c00031052a030415116111400c9502d02440c403000100ea12074010740151003044094034185a9079401050640d05503440e00e031011700b8460002110b003400750701100c0410030000c0440720704104c0e0303100e62480c0076120000340c0045064514501d00f40d00d030900030103514400a2805 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 231778426 1250 231777176 231777191
    0xd06080a050c130c09150c06060b0c0129040902060f0d0b0109090c020706050f04121103070b1206060a21050a0615081b09100507050723010f0210020c0606090604 71
    0x21701c010100c0c02050802240800107440251040c1448005d0a81084041040342d80e5001200065445449808815428090410840c40e9504507000c11002800c0b604600020020b08220081c05440800c81e4010014400500b10a030b6410141230322645011002510882e4040050151001d5500c54804142040004c20b803c0758046800b9044410504141c0c1c0c40341081403004c85240102d420140d06404450343c18824051003c5d00c441a034001a0140c5003003a0700c8008030016445029096915034103101c01141d2103062910060014485616040c40000d9440128030019021000800b000c5500c2f0014000c0341541031081200500c0080702d5510225501c2e80c002d07100d048010124042d41c250100b0408c00d030345640080740d009010050101d62442c1490340c0c0607115401018058880d403288081c00700d200c0c40661303d0348841c1c0c2000c0350340074624800340f03004582e00c0410805003811801260b41d00d02500c2094006011100211406000c042c0382c284103200e0002001848140b00d941040b07407 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 231779676 1250 231778426 231778451
    0xf03040f031b1e03051603090515340f030c050606030d0e0d020409020d0c080c01021209121f09051014010512070305160e28020d06080a050c13 63
    0xb0f800c0200160a9004031406071a41401d0341d150080d0b0011070380540e24581250101940079182c40c05441049844040014440c1e54020f1540180b1019102c05007039010311406800c0003400c640601406903101c4d6862b4506569000001d8410180031408102407214850030040288a80f5034480e00a4000300050509a1402402940712038411401081400005070039501c594012149081c0c010b0400100540c1914004440d290b031071041e10034500036400c285200f90310100b05800500c1c4e0481110b07046c0002041003101d1031a4282d4501524840d4036195a441c100354074001e9039109a0200c00219058030341450790912800285510015150000c90100205058402ca040d00c5090701c0512081390942d80013031401919400c0604240f268166601503400c6030301d03038130b801c0d105214401c102d1030300d0341c20b00c441803150281010718080ca0350081351040e0b825150302a020580d55210042280c5548030034850400c1c03066170056609800c480144130440c2445c20300e2815031300d4000f204210031614041e = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 231780926 1250 231779676 231779693
    0x30318080405040f020403050a1a01080c151803060109061403010b06040e0405030f070c090e03030708041401180b060411030c1207030e101b0f020613080f03040f031b 73
    0x40303070b2007544c1e609200243c840f11907040d0b03406507a01c20708851406000307050a10707950079145008038130f03103442000100e0b4103200401c0f0524041030150443c069034004d0a20a400340d0031101d002807140c00300740039203100303554104130203402000340c0000041c1031800d140050410420200d070380f0f4026810654160003984603d012179086510503001206c00340c803030789030260a41c0702d07003c423403040e0b05d01c01f00700c2030103002000c0c11500458140060030072003c1d10124a044d10f07030108030b40c1440841d061303000150200300b076088600f80051100b170000a1070881424076085d24650000140c401c40c904038100310160500744242d42c28100c000728420706600d8000e05030740c110b101d14a074101c00c030f071a12004201000c0c043d07040b20103965a40420765841d1510040440000c100c0c00ea428002c8007c42c0001c085164040c1c0c03a0300500f15501c3d030241046584405201c800352140c807078122103100f02048190811003a200c051802984201074074400501d81e810014103002000034100003402c00703500d1000c002030000 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 231782176 1250 231780926 231780929
    0x209043312080a030216111003090503071101090f0e0f06060403080706150905010306021908070f0810030f080c0d0912060c0e060f0405090916060c050f07060c0303180804 75
    0x140a0380d82e5103e0894045003e40a1901001d0041480075510301c20485804001e00030f0080a4940d0380c80c11420391004c4040d074513444400341c410b400030000000410b421340c1c096611140103040030b11140d950344c40920242c40c0290710140503014130000707011241015150a6410060403a4881e0505055894060031485298001494a5698001e900e000d00c8400842001420001c800304120340e528140350300a90320066070786559458040f00750b102075001c0c800c02802100c869503140b501c4122203030b040c0c400402c06000c03500b1030540000c001000031202c500c110100d500c03422003291542e518125080c0780044480e0400c0600800807024044107031241104080c29401c0f08020440440e402401e4030054403292a10740c000e40c001410005510b06d501c001c10480d5800d40b0041040c2d41c034041b416450f4868a5164910704051540c101300701c2c0d200f008055010390185003551200c18213502001e00d041095030043c0007180748410303080c06064040c07151001290565417076090500e61642c40d5003891285 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 231783426 1250 231782176 231782183
    0x601061709010f0504290c0315010201180f03140a080703020a0e03010e0106140a0b090d15051014060715050a0207050115031b0b0301120201030209043312 68
    0x903000814190003500b0a0805000010b81002213003030500300b108140c1c0810310040c1d101c05030750a0f425810415600c0a0f48504680400c03241142c442d00300e40080da42000d600e071411592580f855890205031200c2e40701c1c3c020300c00c0301e43c280d11107017510b000b070309100e0f203a00d450210f000180a2550b1240d044401660321100506c1d006a0341c0d55980c0058a2815911042c035030107611385800110b04840560140084d070350344400c0001c40705800c00821002c40b0f100d01600c200c24405000300410f07400d0a824800c055032242c11010300c2454107000007000c039101151800300841c0070007410026004070007100d459120b41aa0740600c0c00003c2e03144d6484542080c00303030741c104940e0341d00080d10444c0309506a07914282d01070000e1006a4065480c40101d03070180c0016640c14240309084243d0007200d03000c80c1c0413160154042411686010102130040c801c00000303030305040e020054080d0954442c45000c50024403100d0805c2c2d01d05036404400702e034a80120140d900358410150034070002c4003025a28199551 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 231784676 1250 231783426 231783467
    0x30702010c02040608061806090a03020a06050406020702120a0201032304020d081306030b0405100e04031409060406030f0c0305091f0f05010605041502210c0708190b0603060106 78
    0x1c00d202040040c405580a207849001c0d090a010300d40d00c400c1560351821802d002210301c1a158546455118810824000c0240e1b1002a24000240b681d8101d01d43c054007510b0018200074107a00401c203a400300344202a01500118514400c540c2c041c0729803080d040445d5101c40b0922281c1c2061115400013401c0a881945003150300c00401c00c906080713407411485000152032682d6102809009441c0342e4100a201e2030403e000500036204414001080716501d190010172501c954500307640c08039201c0b01962070b400b8200501c83c62a12004004c200a00181da00041d55802401710f20f0225035080d80c88000b007604101c1171040800c00001c400380a40b80204011409072000c005c0600101014400700004604000000844031b40003000342c0704031004117507803000c00282024101d840d2542c855a90300300c00c01040b020f100040c1c0d1140a04a1601c80c8002c4841640d100d042d810300e00890300848007101d0440200010030081800a0103400010a50040903103504148010f8142e182d00070841a0400c7c = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 231785926 1250 231784676 231784697
    0x30f020d0204020c0a0204183c0b010603050a0b03070b0918160809010618050403030905150a0e070503030406030203090703120507030306150c06180501241703070201 73
    0x6a499140d01641603000307108643e01c3c8024400702c0e4480c052400c040c1c0c441e83c0380581d80032007400324010740d1f0741d4258030616018404408180d400c0da1100c461000700741d0991078079640300400541e100900c0c901e034007034100e8420641c54680b004040e140d009003940007a5040c0f0050400c01e840004000056075403402c01c6c1a141e40103400420041c001c0100310811030380300c0d10107002801e5030301110801400515030329032100c4d0396100c00d440e003a2021446401e48a12000e0744007040a5a2540440c0e0064131030314012401d40c10301e40394245402c13198820a280645410306210910b10f4601ca11802d40022401602e80245448006601c0740030302d1045d070091640000000305031400c1441b2100165900440e6000300f600e582c3e03c0202a0b401c403480072001300340381040216039100d4040c400000b0711401c1c0d42d42070701c0c0c503195640d605c013800710301c010948006501054034000800030300440d0500142084424604400090b01c06607600c0c03142d10551401900f214007a041e08400300032552030f59020f00340000001e = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 231787176 1250 231785926 231785929
    0x920150a050d02040308041a03040c030209060f0d11040b030d0e060313170403023c120706021f020403051504050a02040e03090109050a080a0b1e01151d0901030f02 72
    0x14842c00507110700c06840041c0c088100003400001c0c0080d40e250321702c1950441c43d084c0b0110300c1840241c40280c502c601891040005241c42c0d0300156101c003000d401406c000c4403000c0403c44215007404104c490700310351121585036050174404c10810400031001054402d494500181c440c00320003400d107014000002c0028040c04c04d0401503000d19034000400f0512003580e070b8031080d45401c1400100c0c032500401c1c24080c1d40ca010050102003c951002d071205070b02c250390f50410503151086c3c2c03505030094241b03980105000340621010008104903009400c400c0c10a08840f0300343c3c841c042c90b08002604c1448140041030340061a40b45074158120001056140da0800c1441d150385600700035803240c200349900004500204c040c000c625000c1e200c00d2249502c034420443c103070314940100e0809034000700007400460040c10080f50800d4440380f150340098844041900f40300026008040b0700c442d103408080e0315650040c81e5410046880c0880010340c0003020001d1643c60040c8409000648220329410a5 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 231788426 1250 231787176 231787187
    0x19050a02213115030c0302031006030f1b090e0903040803041e0305030a05090f03010e1b040f0501120302120322030e0a170c0103090503090108100b0d0920150a 70
    0x50803603180614003850341c0d850344101c07548030906450002070400c02d01c00c9105001c0d0090313274000c1c0740340848001514140103049008002d40000500c06c2910303211404c07107400520b4003414446859603980100a4144010313032000e2030010300342d1140c07507008200401c40820080207850640d598482c90920720b1007440610940c401d07664102501d980800502500c0c040c1e00000200746000c0e00f996105603222805e4101401c8641100a0b150300c0d4020321044829242d031030110035800030005000041d0380380b812080c5401c56034260030003420280c44001c1001815010440300b00c00d00c0e50003801900d5031510b01d221310010745a00c2100e281000d002141c1004160007a155000140070280050410070341e12449503007010701a0344034800a01444140181070f521138005c03040f003143c0240c011490300c0c004500443d0340c1345005020000f4418081d001080d281c110000425084880c5000807960828900b40700807144c0504908520420407c151541d203926403a001940200c04014080e8450106a00681c2c0 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 231789676 1250 231788426 231788497
    0x60f13020301080610060e01080604020d0e03030f010302031504050a02360a0c0302040602060f1017010b0102060f1302090a06080a050f0c010302030105012319050a0221 74
    0x9560300110010400306000a00d541c481e00e81c11018690b030329658107058418144c1c280c640c0f4000b996601c0001e010342010f4000700001b1300d68900004104d11100d4059055400c00c0d910305415a444800402c10751400300400440c0803062050030090707050076a1403555031180040020b00500101110f50700002102e295a26402030560841003c400c0441c0100010b82088a0b407018592408000f1481c0511900c00c0c0d6040e104507800400c1c461710395440320300c04554010031054a500c8002400714051800c00300e0580c0d64140c080000c619407040d0303400603003081002000540c401861400f002802c104e01c1c900c0d801c299805403501310040d21000400c8010b801141c01082c490b2052001410800c140010004a01c00301041660b0303512641e140114140c0c0b2080c822240021032104840d42d0302a5940e40e40074000072881001031400d586c50844220b600d2001c00764074042100840c0d0464038070b806001e0782c102101c481c40f00c0880490758100c82840e038083c0d002c0340100310702c04400c000f1440c42c614101c0389 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 231790926 1250 231789676 231789709
    0x7090b0d08030a0b030f0d0f030209121204030b060f10050a03090c0f060909050c07021002010b0a03030302043311071e0317040503031204020d060603080301140d0b060f 74
    0xa9032841e03da02010f01506114003254024802c00e020110705510104000501c020183c0d90442c1c4081040c3d400c40103908034120302ca51040442c0b000c8111070004101203103403e4604500745480e107256081c90000050020030322406804c6501282000740e40e00c0c02d0310b031813409c01400c2c26900c9100c04141200140080320340105000300c60407012440c258201e020404442c165a11118880d4582c000790707043d10800e95002030500c0061107081c0061620881c0c694041001d4400010100f11210008451284547c4164040f03075000405104003040700016498003130300e22a8515403281100c01145c0507002070508030040248881020000c104140059401060a100128450785030035040e540192402d1000b1600102e245080c80344000640b401c0d47d0885400030301842c1444c00209151130522030041040343c1c0060b4200015000419510840001d5400b61700080c0e01ea6050000c600740f41d00018a40601ca58041e04004d000501c45441641d4824400d441c240070f4000003c0102d46030b44910407280 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 231792176 1250 231790926 231790943
    0x30c051b07080f07051e010c0b0a02031501080411041a090a0509010608060103080a0807050c06071d01140f0f1209010b04140105010c060c02030408190c061107090b0d 73
    0x461800c58009014401d41d01d5407425a003902405000d42c0303944190901c9906c1d0000501c441402d039510328100742466890060400300c11000381da0751040704481040b00c108524590106c207226031007140142c1d91080040030b00303184000d401c261301c403460b10030398010480c0d11030b507240d8110b81c4440003a6102550784a8010381003005501b41a0341010150004035504030681d80303002c00001c0d09040008006040b241c00c082094a030050001d801c4405a40003041c2005000081102e52800c0008102e180c0c42000a541c03070a0f140b00d00b02403920012051402c00c0c034100036180c1c0e00324060b044005e04880c00d4006039208940d17506440c0080c100c640c06407840a10462034808108002d004064000c0d4882410464041080100c0d0050302080381c0d80038040d550024554003807050014140d035205040701007407801109d040c5956101784a140c5080e480c02114815103500d0000e04000e0554205409061541803039031200d156920f1080c2d50309102d204207180191280490409130301c1d010300644a20b900030002 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 231793426 1250 231792176 231792217
    0x30d200a02060406110702010801030303020a023d060f05010e0f030703080309010c031a1017090304170a0503250b0114090f04020f10050f0a0306061b0503040501030c05 74
    0x180d00c0b260215404d996003820003c02440303c8102030226444607505865912040e420340d242100207400c8195044150322401710401d041044045148826400310601802c520842c130345d9140360300a4032004000d06909102080c0007a0346c85580b400280d8500b868007a410049490020300790300349000c8040e400d0300980d00301006100d07840c001103105140c900c009221040d0064003c50440e00e043c0417a2008100c24005a0241c0c81c148100705000311484c685040c1c1942c0007a07024003a100180e400030310503070000800300450600d80013805d0784801c01901030084044642c07500380c2c592003503052a01ca81410307900c4131041d0f010315003010903003160003410141a660b155011070010003034039100a031094814800080601890300051032240c1c1e80030b040c8025980010341405050306006200005000c030a00c40d51480d40300c1c49029004090782076601042c01440c2140140400e44c109100502d90a118424600800c0000080b1022203900f864001000b00c0398800403602809440800c0003215101c410 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 231794676 1250 231793426 231793447
    0x206070e0102120a0804050d050f0d02031815070906031104031704150504060801140d06050705070807080d061a0f031b07050a0302011104080601121b0303020105160809030d20 77
    0x1180c9111b1849030085402c005881c1e01d0595440c01802d00e01201030200b0828840fa840da00d40103103400103001c4001c0112100748040103401c1800707031103104103000f40080800200b1540711160358000e080c00d0408000302020b9424580300351040b4080034028200340000300200910b2201250001c1a1000e0310b600d581c2496200201a41e00c039208010020307003002c00215405014540064454400401c18100c003242c941d903810142c80e008089006000041c0540381c04900c41c2001040351922074502d0654840141c24410211041c9402000600013100000c01080780098121449032072014040d54480c0e8860801c03d8420280e02c40c40544110f022070001d0030894001800074500c2d02c00c1d00207002c000005140a1210700079446014415071101004010000e01a00381444d594052020303005503561103080710b10000c2c541c0d03000f01c00503075540c81084000c0d60000c50b440b00f10015803804900398108280d425a9a000782880107080315990b8800c040c3c803000402c44128080740c8144801e843d03070030940 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 231795926 1250 231794676 231794687
    0xc081504060c11030a030e070527010b0a081801090f0819050306010f050c0a08040e09010c020109020d030f020c030d020304290f03040813090902040b030d0206070e0102120a 76
    0x440c119101030400320301d001c07698000da0480c800c100c0350500a40c2003840e42d40c0128081c14100300500018000c40c2c030041001c0d124200c0480c400c40c425451a80c1d0900011111010300405070300c040c0c2ca240081c080c0390141d0b90b1207904582c02c1207002c00c900100d08d5444203600d0040480a00081c80c50503510403a504122104020b040f10300034003403480303010410700740045c0d81d54402151410b00085000b055900d09501030005440103902032000c40744130744255980e01d02160301542181102c58048010800349007424018140000d00c00d10080c40707492000d070b0100b041d0300d00011008050244411091a0192082140031308451008049400030009000065240d030b1003406a9500045224a180c2c0b0484103c1840e44000c00c1d44d041c1185130070001c495020241d00050822660b80c0c0d02004049081012958404044c042068001581038060b00c1084101c40c030300c01195000b5004542c85c43c42494001c02c615511212904000120302c800c0e10040b0700b080421140002910404240018280e0740507 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 231797176 1250 231795926 231795931
    0x60504050d050f340305060118060f1e060e011409031015051008010803120603160303030209270f0a0b060c1e061b070c0803070b0712021806070c0815 66
    0x5032035118070b0f1903c401d21401300c0e03101c5000107865948104c0041244200e1810448160007507003600141558585a60030745c00210380e0b00c135403880040f100b40c0390412440d0b5407002c0018140303824601c0584c61f441d0006040500440c49807485004041603030000303614184980c1c510602c20003400c0020750f0303801c1c5440007101c0b102d004540c01181016442034400d8000d440d4241070b200d510000f0b5003445460f44406808460091615426019108482060110040a8002540c0300741c4016840f020503000b0302c5203040c00750b40c0400c034048422100360f80b00422960110b400c2545403944a1469461151b1403010703004100315075030030403000121142e07103800208070700c50720454000a6020303203030760040000d030386d504140e4101c1074410304208081c0031014040300500c0d415200380c1080c220300703580d16820340c215004a0003e881841e50301080104581d40001f40f06071200b4944001c40c00c004001c0b00703030303ca6a440074070742d240034030b800041910620030104921801071081c50100d031a83e00f40d045110000500c00d = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 231798426 1250 231797176 231797233
    0x16030c110402040b0d050a0902030a1202010b0603150904052d01060e04082209020309030a031119140f04060203070501180b070813050106080f1204060504050d050f 72
    0x884980c08901e014003c0341e0484058103aa40d082c102c52818590082c0b1000d080f03005065611100400180c4041c4518041d03680105006034081034025400303425200c61a081611924081041028001c0210045ca0101c4820380b83e100d80b958a61800c035245c240c15104412600440e15003540109981c02c001342c0c4203e0155000f03012550350b0304415044002d09844c0100050028400d40c00313061f0030366505914440c1c000c840b8040e040d6540003114203d03030043d103039000b190b080010343c14001c60305030082d481380300c00c1c80c42001d01d02a2520b081d00d008920b81765084040011b00700b0404401c3d00c200069400381300f980c84200365520750b0fa48000c0d60b40c0c0c0c440c07a0100c0e00c075400e056440180c000b1140c01800c0158000c4031600869a031100125002c0b0300040c1200c52940d42c2a01c5100401c409100700006454490010030fa01803d0501143c940301c0d051841d548000020417082c0120b030f5025066404840d01568503641c443c2e01807611508026802880800b43e2040e50441d4400700b41001401d08030404 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 231799676 1250 231798426 231798443
    0x12032007050c0303130e0403050f0318010c020706020d0f030f021315050301151103160b011a13060f0908030a1d0f031f090512030105010201060605031005010f0516030c 74
    0x10b00c00103142e100d001d0803820031400500180300b000010011001598494440d00c1c0040c83c000c1d0a204020854105035420f0441101d0140740014a80d424800c5c1c50300b0f0030140c0001c041651130208000c2d5a0703602402071030108480040b080952070700a030400302c80c84044150075901c980c10108540000707003080c89145c01034111111141c3c2d07058061004c89060703079001030111007010960030050b5401410442e0a41203440100b151800c5103170811201c00401d4410b0b08400055458844514003034503e1045090000104100d036460810703041d6941c3d0300b2208ca604054540d145105030a480c0c102583d405541540400200c01ca0a42c0e400101c2103486500c3c10081c2c2040800c031410b008220398040106074041e84964007040ca41c0307444580c40c1c400d00940e4130b1b0106294140f0341d40c03d0700780110301603200c1041c000440140404d41e02802442c0c050915464603e0451a11101a2003448401d10501781404140840444158403400c103c6001034404113031907001414501c0c0040142e1800481628102c5 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 231800926 1250 231799676 231799693
    0x14030c0105060a0303050403031b020418110301020a0909091b140301060902070203032a03070303060509070806031c1e0806100504050f0405060d140f010608070b03041203200705 78
    0x10f0701d10000b40507240c2540d03034641454110380c1e003503038074801299107000078078002e800000040e03545001e07192180242d003105030319040c140c1c038051125a221008861181e4010310000c03085030703440410784c02218152840400d4000e414241040700c00710049101d030007a041f4090106640d05040c201207140d11007a8020840d059a6540081c01c0317002d8410001d6068000300400081d9003107002141c1d40150f0070f072042c4e0340d2414450041a26641c04107904502184d1030f44c0040055141c03034110f0700d501c0603907814000074900d442400291900b07009604a003000954401160130701d40300b00f1247e0140c0302904407142d1021b2041d00050202c6a088800511030030700c41181c8094240305006a030100c490107000c1500311820a0104400b414004100c035402010902001d404100c0385000c0d4140482140041d20841444203201401d4a590ba0003086166014410810281481c0811260b00580242c2c00a0b040c08484070210040c1c200340a808545103e42c1a0b041e10b8175a9000c020194584147c085841b2036 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 231802176 1250 231800926 231800929
    0x61902150603160b0c10020d0f061706040f030509060313051e1902060f03010b070c0e0702100504030302130f060908070503280605100e010504020702090703020a0c14030c010506 78
    0x409551030301d0403500a441e18104500301e40b04c0090241e600301d150039500c2c0070070300c804440220303005224002d81042d2100b48a40b0a0b1900f8812000a00840720203812070080ca030402981c0c03400e01034002030001e10503107a03e04c03d05d8400c00682e41c603403200400c61540c0e0709000d80020412018010f0a5615000300004c4a0100d16020744907040000c0100c0a000310041182e2010341c060354200c410780c2c200d40304001c0d02c07451052000085020b07020b091035264541c3d1090a11186503441c6801c8002c91408007424000040d8000410404c500b41c1d1503c04a07155a4500e01280a80034403007886803860800e1030b01140800f00c1340c00b654141c0d4055504c141044c0ea41c2c858455072040e40380b0402e03400d50080702044200d0184060383d08105a0354013440c1024001c1540c9032411100f003181c0b55030034a0708020341448036001400c0402d004040440e070541c24030030103800041403c80003604003424954000b803003200980c05030000301d401c0358002003055604403545074415182d6100000c2c1a10a500e000000b8045 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 231803426 1250 231802176 231802183
    0x19021216080402030d11070509160f050f0f090a0e13030315051c0602071208061f021009020406050312130603270305310504020307120902061902150603 67
    0x20ba60018001d107524146000151148041c00600d41068061103034013155949403556418004c2030071141c1c02d8181c111740300000342020003107000c40c000c10404020410809400800b600c0510122402003642d92038803c0000b0f04d404850b910501003c0e00010401c01c0c902440b001d811049030181e01c0030304c40002130703500240c03903001c030303030080aa11007641198001c000040940c0f40c2c2d4043d104040c018a408826220b500140400140c01c0c80041c20301c9081000390f06101c07001046841e0340000c80002d030400c0c458080c2d142e00c0e00da07403c2410141c0c1c4000301030a55980d5000100105006802d03981155444640d0000550140740900102c0700150350002c0d405200740300d8180031a0400038100c462000b003040c082d03076110020b441941002800d00250031300d4841170030729540320301054401c1004403180005070407088520350700481c440c40c0f0601c100900242c20110700000c00c0d0454600040e46000da01c0010f002e03000d4110300130b8035030b65000ba905078803540004051910300040c080d0681a07664880406a4 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 231804676 1250 231803426 231803431
    0x2030f10050a0b090303091f0905100f0c020d0b09100518060402010c3f03060503120c1005010929060a030e0a0f0305031501091505031902121608 64
    0x8000381840b00030454020500054065200000c00340c0f07240400c41d40c00501c00d5010b58090540005042890641c2c468004007140b00420055400411184042c5005402e0321b04440003078061200075180c4000711354401c440c041c41c5660018040940703003044400c81d40e0703846600303c1c3c0483c0d05103040d010030040f0b072075514401d441e9180ca00081031280e40b141d00443d40356483c0b000071100b002c410142071700c10051000c08141d502ca803c92000e01a043e05002c20400c0c0f14290520380e05051925205102a4401203441b45005e03042114840d601d1042c4400f140c503040300e05d5540c0d0101454000003088054842e00013003000c6000c501c41076910b29584d03030010540700c031140d0000c0e4420b00070855107400c58041d070002400c141d140130680d408101540c40b4006004504902140014000010007401c00c00095801880300000c0c6051320100c1e040200c080550200e141e201802d221700480011003010700f401c034900408451540564580c0e00c46102100e92007015258041403c003200701c0d1921052180344950f2 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 231805926 1250 231804676 231804679
    0x210d02070302090a0903140d0b3d02070b03090c0103060e0f04030c081b01090b130b010302040504050304180921050904050406201b061e060105190302030f1005 70
    0x14003500c1e410800f4004015100301103040c0081300e0004004009100702a2414855141d408219222500c00304410544441c40380b00e01c5036210018003464448404c041c00c0307100b5494ad1800340f400b4490300c059140c80c3c01603200c40c0c00100b0020030030200880103e103442ea19402a01c0620610351201c1c80c074030442004460404009116600181c0440d01c20316800034801d00400e00341d4a4800c5000c0b60344000c50f000c3c07070781c500540e4642d1040804c114040b5070315a4850a410001c9218181d140e8411101c6401880007903c6551203c01040a000082c8215070060182c4000e51200002140c00100a480a081d003501c07100d03086814440d030a030305115501090007213903888510f440c0024080200501015200340d6a2513504c402d444550158045030b0396049803038550075522031308600b0b1810014203400d242c1d0f03002c5802079004d1140440003021a00501010b130313880100103540395401226507000d8000140a4980e80e9581410280e0b00741c0e005502415128504451694502c8856041207400e841501d = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 231807176 1250 231805926 231805939
    0x1803131401090b0d110d0903051201080304062709090f031d09010504020703030b060f0d1109060912190f0308070201050403050d0b0607172a0712020f210d02070302 72
    0x41324201e0f0340159002158868014105041801c0c0303c402c0342c045050403404200009001145180c40010f0180101510b6006500c4c081c01c0c840700a00d6161108600a080180c210b0b49500410201c0042e8000d400e9000c01017094070010300300a0010600d02d0010780100310100d800c0300b56100a40c81c40a5800000352101c00c881e46400140402940880d800390209a52204004207aa40d0390000f8a045c03a0307080032203500c50007800080801c9812041100c00c665004000710019502d649069400004c0c0c11034003a44d004030360013040c41c20201c1000c400300d203907540310100ba0f08120480000e0f031001c6004e90b8481101d41e89295003030b422a4400c0d100071300850014400c1b510382c100c084c2c110700b2850401500790303420502d07160f031000561003003018038910710724021072030240b41c80f00e080324003014911000142d070a00150150709600d4401501a09200f50100c1c400b049c15900ea400c071440c81950042d04900c0046090315810b880b0750b0444050b0301890140755007104031280f00142d96002e880c0c000700300 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 231808426 1250 231807176 231807187
    0x110906070f170a020d0c140607050301062d0804080403050703060c090608370f060905130b040b0a061508090105180714010c12020a1b030f0b1803131401090b 69
    0x6440503128850126031f00c003000100c0700342c0307000d0501000703002ea80191241030b202d50400e040034007044c900f50b0017086402032141c28410a0f400c03200d11100400e005040c410465107840c10300c000b80f071080750409071092240c6a0000200300d007903489124200b5403641d0315003085451380760440c2c1d441000e07126020151040b000c0c40000880d520f807501d007072600c50342074115914104003108054504411052040a40c5e0303000c10030150301c0c3c034050103034030984005c4064840011a50341031005c0c0b5001d0800340403160020f0024139407000390b41c4040060030307110420070841082d000c03008008003c200c603003190550070800400e074030080488805181e100c021003d8000c0c20304004208240343c4101c4e55050400c10003034860b0021880600c0c2043c100c0c2e083c6c1e80074209031403160414001545031b071460350000d0003600004101044c00c91144107101c80d4040983c5550717403510b0100b0b0041032100ca4640e10a0301000a45454911507680c00d841200c149100b0b40c084482814010b640c0e8079113610801181c450100701 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 231809676 1250 231808426 231808453
    0xc030619080a1b06021b01050c0d09030c0e0624090d08030402030f0111070807020301060b070804030605060312190215090a020306090105060d02013507110d12110906070f170a02 78
    0x142c0c401c001b00107144c400c0c00d0014203c00c241c94000500420800b16110101c00c1c01800640401c00340549084200c602090910b140418810110010321070003440a014028010720058011240e03840740040508106030420b05098146600503a400c07846031142034900485000706014405040545030b04040c1080c070320f912000302a07400603404070f9240d5038030307440030400c9456a0040c10344240140c80b010f88942c25032600e034003210000b81c83c06c0c1c42070340100c00e1901c1601904007180c4a8400311201c58891500840003a440d05401c0d48903060348100ca00c04010b0a4440000c00445440c0200e0072103040d80c4404c240c0340e088032000d4a1281d000b016441c503100c0954002c2c4011f40402c0840f11111207600b540c0514548020009815401c43d03118902c280611940d0000504030741401d0407001d01800c2400b0000646544140e40c0c3d403803511b50300c4808044481841a060314a1031001405180c0d58804078944499540300310401100c0044801018480c0000480d00351541304c201034000300345075400d400 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 231810926 1250 231809676 231809713
    0x3020d0518040501080c18090706030e011d0c0411030c03220f030c031d09010e060607080d0506012c090406091a0403020d0c0b0c030619080a1b0602 65
    0x808514880c4000c1c00208a80d4a070b51180e203009103100809030101c20107041c1040511000000d00360416071031501072114003c804030b680022074806080000f50061040721240c003400303500b003094501d801da058039601c0900c03000c81d2844000d0000c035010061010a402082d00ca4081030360402c071401c03401e20001e2120680c400c03848441192801d01100e13540d902c0ea0742c2e010300d001c000c0c00031800603580741c0400e000c040c1c0061104064040304a204003182c1782100101c0c80707040c814842e0200d000c070b945e80411919140d100c111600c0c40c0e00680901d0395000700c800e01c4800b8200594059000406140303840601000d0509410044032a001803a8041d02408081240f4031001400075500e40b036554a03030b94009074022041c000c150b0109a501e09151510382406400c00010003110003d2201890102e8006030490200551040317111a00c25200e481d00c00c041903e000900001d43c90450110501041800000800d07480e481d102e032000d8038100d03000c00d0784452208098030558000d41d000e0102d0055180a54 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 231812176 1250 231810926 231810937
    0x801060516081b030403030903060b09090c010c0624030c090912030207030306051818010203100501080411090405100e0109080a03051f06090611030403170d02070b0c0408150403020d05 81
    0xa03c03c09101c1c80380e01c8102815944150701c12404914a85020010449540030b0300c0d1104001710303407024a62801c40410740e100c0350750340c001c18100314071103510004200082e842400030107200c1c80000c0c9000d03503c490b4049180120300040d0780c0801125800102489603000c3c04480950240c440e00320446100e50560103504020b50842c14151560000310b0592a8071100420702101c0d004415060b040010382c40000c20a0880e031286180d004000300008132000090242c01c898080c40c2a45450340c0d40e042c8a5603d0301c2160036103a02400200c2484240f207400244a800000c41c282d0420540810300340143c200c82441c040204070315020b1085405047c0030b5844031398408071701c2d0300e0800d0603200e400d10101c400704150040030116402c0e0409104060f4001ca038001c907525080c0085240900715100c43c0c17480800a00710000f1040c0020b01d1800302c038040d4042d103c4c10f560003c0d000e00c00781401413501e100c0d0b4101d40640b81c294803e1075410300c4150b2161066602858164001e030400402a103000c844a9214 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 231813426 1250 231812176 231812197
    0x3010902030c1509090411040c03090b18070305010203130318060f0f032a090515041205030705010219080703150b090a120c050a0510121a0301091101080106051608 72
    0x10304c07105040d903c0706141503200d0f503c203a10407a100e104080c100000c88800a85c02c00c109442c1462100000e1107401c0c80c0d41d00100c404400200000441319891704e440000d40009205500100c2481554011000d00980b01b40c1300381c6414507044004103060b000102076105000c000760110005142450107854854595102803030045248550782c0d5442c170101c2e180e00c10000d9200d0310f14000e40c0c900d40c0e200c00c8070800f800045945440d8088003e0820045000e50701803940c1c0702402c201c61000f0800104200c500c91603000009546500c40d1603054050300d5085400d03900400d140d140040c10162091142e40801c244561180010700e050403143d0039285c020300410303031304840311010200d8080c80305141780310410b119003010442e03e0f003041e090140b01400b1b0780c031050103190200400b01040f90007003660341000f507041c103002400c102251022442001d0b040708035a0194038008007a4103121124810a1040c0c20030380724807081d40d03a1018215100c1c410f004211944052850444001518110040800051 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 231814676 1250 231813426 231813469
    0x607030506040608191e03090905060604030b0408070203060f040201081f12061b02010207120509010309020a03030c0201020c0109080712020d17040f05091b07060e0111071103010902030c 82
    0x1102c9071013502e80301c9490608414089684a03201c10840d41d641c0410b4080b220145541c03481d0050394010300000c5c0c1350b005030524140c8030400503180d600d801c0241c80080d5001201401281000e091180c807580c0000d4080c0c0c080c1c056040010b4402e540d40501341e000e2130317040c0d544a003195035000385500c44c0c4011102821100600c00c1000a82c0c203121880211a40c1c001c2d030300028401d0080e51070030010400318411205590040c0062004148180c0399942a6021410516607507019440121300415034064000d5116014480200c00d066110302c1e0f100807180700f07808868541004100544a50b0901d11403011542d102c4602405490140342d140c19080340301800d5818514030b503a40b0308900131142c04600c04440e9003c1010040d44000040407801480c1c29a80410242051007841440987c0b07084445d19036a0001104020020141d000307034030200c0d040c0001c10400000d06000c1d81c09910203881982c54000201c040300ca0fa00d41886030402c4aa8020300500300941c40c0c0d000d01824071025100052000c6 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 231815926 1250 231814676 231814679
    0x10e061503041a160207141f26070f2f15070e1302041406251203140903030402040b030f16030b1510050c160b0903071706070305060406 60
    0x140440e5008088014683d150f0a0988000903d00400d5602c41d0415102654131021140c071801d64230101c03a028142d10a080da40e1111003036900c55a0040020752481560308006501581d04100600a01190396240f40c503900307010003200d143c0444804000041e00521164107400f000020341d04400701003c0c00d0f06c104040075407003881c3c1e64408641240202d030b6985624207103032400c900544036018140c1d40450410b41041198031000c46070028260090f02c001410355000e980b0745d99166450044143e1a807c100c1162070550103911419442c040401e0614105034006030078520824070591004000b103085a42e290200809003066108030382e094001c00e480840c4aa40c2404060501038403500006206440d510f490900480010084407580d40d80801c4c0b040302e9518410039041516040c5419521260000051424084814220102c40d02408400110300103c0d0f4041c00f0481c3c1c04600b6200c00590352400fa6403c9a0f06141c084001c0e000351000909441c081c1e809690030103805030002a019 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 231817176 1250 231815926 231815963
    0x7090f0807050307080307050312040305040305060a0b120d1409010903021f1214340c020a090207020d24050712060f1203050c1507110105010e06150304 67
    0x1825150441251a0005036050266050800205005260010086103425540d464142c0c41c6d006504040c80700d07100101c0814240b5201d042654044c0d500007054071203034107000d90150000c101d0400035901524090340c4240000c0000301e410361482e01c03141c45051103500da19885c4181c56000c400c540e418028107840100c05070b107031078012030075294221240032403c120007140a040011100b1184102c00e091210901004013000e00a603049071118035a00c81ca5052202610811070803807140c90600215145038060182d401800d65a03014025030f842d00400d0703194040c2d00142d1007040303000780d0080c100041c03003c0010910109543c071400b500c15490822810b0807a00c0d03081c0c2d60165501c100090302c2c2e81041000c0c0b12648211801000c03010544801980b40042c4440410600c40014003800400b2074856a580020b014030950350490041d44811072509041c06403900d01d141803202585c0d0301e0900049480b01180070389501401e401480c2000743d90382c1c1480c40c2d800f60f0000704203c40108056006d007a90 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 231818426 1250 231817176 231817199
    0x1c0b130f03020601080c0402041409060111010f0605091e010b03040602090303040e040b06180a090c050907050a09150c080903010b09250206040f060203071b03030f110a12050709 78
    0x405100e07902400c20f079490550050700e030802c80c01040c0d00c80c03441004208203850304014210640c2900365203038001c1da91800c0050344d15035000340c100000b0b5400e207400c0b80b074010f01c55807203007080d80c41c00c1b68004003d499484c100550092501d05403c03900c5000c42c01441000c500102655000303118917000344c07034943c030323000407905541207036101c400310300c59200a00080110003c803c0740c0c041d0098984608181e2918680c81c50080081d0184185a1361461000140800041600c000d440080c6c48452203041c0030900400550008181000058040c180031815259103c1394032400141d80d80d0750308213020b45440d400482d9200512031071381503507902c0d9100620740310240d041344a18001d00351003400044078940040800813881d542e0045401c00301c2084002020b80b01c00340c40c482d80003d0010b03140ea17100b50003a5006480c2c00740741603440f804060520700705503250308400c14403c0100010f014906e001c1080c007040d400f0304281d00c80441c45080c407803203032036000713510041d41f021003483c0401742c07150f584512882 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 231819676 1250 231818426 231818453
    0xf021c0c1406070c150513140f0904030c02150408010c030b0f010903020d0b060312030103080c07050a0b0306010f0203090d050a0212150c09010215150f1c0b13 70
    0x9004000a404200140d10200501000181581c40742c2c07402440d541c0300c9213076072020300030701300f0990052010881551040042e00d16140d403174510306d00d0050302d49a100b003c42c030b01c489245214103c4501c02000380d0600080d52401540c0c0342d1120403001d9201da080213064100c003040c14642e91010300001882d480c1c00d000e800b60704035003901c0c00685810484140032a541e902c030000303810f00c045d0b040d08000503141c00e030f40d1101d010307005500858103444090010342404000e1a000c04044030120010003031000a40c000c1c0f0342c01050030b0440c1d242c680d44005100d100c0825115030400141e0602c002030175135000303100303181c03c012407481901e140514010000b00040c200050075240d591142e0024000c42c20096688440a04000014500030f0b21036801401d0208000308505413000003c160500b031a4000c00800c00340d101031100d51071030342c504941c0650f041c496542e140ca11a00443c4100e0845040c6818030900000001c10b240940c01ea682e02e401c410340c0c03030142002401e00c0b4043c2da0070000c152030039110300 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 231820926 1250 231819676 231819683
    0xd0501030f0525060c0c0806010621060b180a0905130b0a1116030c080a1e0f0e0d030e10020307050d02061003110f190503010f11070f021c 61
    0x22488001c60401c2460028141c0d40303c80305424203601d0880052211010b24200c2c0c072189001d400c1071800c0e00c0d02940d0b80300b103a4820741d568800c010003c2400c0380c10940070500410070648100d080812007100704107950741ca20810039400e81c100202515450030074001000300da405400178444070380c0e40a40b40110b41c4226000300c007001e8036147c008104583d0b02d41950b00508660414400d0003403000350f910082c410ba18040e1203500c24031071002e003094001c5400c0841141c1000303130503445160861024051200806480461192980e100c014032030003507083d119900d00c0b542c0d070101503420310320a11030304281198080d411300204071840c1c3c000d90782c3c48034109101e42070b0f6400346413034001503d0032038503044113408000d003036400c80020020880207002c1c0350007c44c2d4200c54a560041011400b00350303080e01d800c16085e048020b90340d0340c05850030340340d9002040301c40a41c020010f00901c0081c4400b1a2901040f0420b0018108108030105025088180c3c100c0d00003402d0b140700409060102c000c130050214200d = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 231822176 1250 231820926 231820943
    0x703180603060617010e1503120d020901030b040c09090510080f03071a0906040609080d020a0c0b0c070206090d02120a03020c03010c11151017101d030418020d050103 73
    0x500070603130f10140100e13061010841038401e65040c41065418217400814507032000d40841c900300346559081003401405c1c4060090541c0e02c0d0480070603000031750b01c016042d90119050020005080c10988214045004155030f00d800c0c050421981c00c0c0a4080509550100400d07001c01040b042414086042e0220802d0019aa1020540b034140da0850000100e000c560503424100f0202c01c02c007040c0303254010761120001800c3d9846141c5040540540780441c4a400d1003c500c2c50199030308415061401405200c13000d140396a010000741351440340000c020740288013440707000054281001000c00d440d100802120310502c800f090145003540d1f00b1826401a484407101a8490500b0b00c9480e409048230326002c1400e40c5041151580c40b44441c281c1c00a200425001a17064249010300e44090b1904481a003011401c00000b50303603860203e0002c808441c40c024050344840014420989014800b8024501b80340c039110a409191204150300280e09400b00f140113003109032071003424040d51281c01c02 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 231823426 1250 231822176 231822179
    0x480201060f060c02040f113f190c02031606020f2a030a050f090a08060702030d06080d1403090a060f05150904030516020105070f030509030d03060b0403020402070318060306 76
    0x10071041c0c0d41502801040c00b85050078688040c45010700f101d124241e00810701540c0c180c09803030030208010035a20083e5011030014402000600800540d00410080d02c9c04c141000c028004c10003158215690744000da0300c1000100700001c5240c416a4503180240001810103490180d1030706158408601103496a5510a41550110203051100380881e4500001c50a100e40f0340e070040e0a070f20403801c0826441101041014040d40c0704846040645402002da030460304103d000039550760401d401c9851240d09001020a42140009020513200505d6031500d14000c1c120440b0340407640042c02000b0b0314080d500006022175034a01071682c1d1003500c5900056585485004507010082c2c8900e1584141d801e40d00303020220358808146e44580c0026540340c20780190741e10043c0c03464820b90390700420071a19000d44e031013859088400f07000c0d100c90680a440b45090904400c5048817503070f000e041601030081c0824009401c1960140507102e2103800c20010102400c014074018030200d40c40707540020b884000 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 231824676 1250 231823426 231823429
    0xe03030106050c1606080c0306120a03030c0e010c0209010608040311010216020f061c0c0c0b0a02091009080d0e0a0302120105040c090b06030f090c1201480201060f060c02 75
    0x101646a811800036200e80742031905c0140030000240091100340004400304601d82e8484000000700245038085511b0414240341c09009007130002d60001c01300b420100d04100035402200d501780d0040e4004c10b54007040e805c0500550b03006401610a80400009910183d1030260901c001c1c40c42c0405250001c400d04503510402a9020600c5d2443d80151010300c0050911540c1d114500180e280a0201081c030a40c0f958080300d80e80000300c00648107050540c1440010310044e8024800041e091b1011021200ba282c426641120180f02e1481e02d50300284081e00742c43d1148803401806500201741d4007517a903a03a00007900c120704c400110304007039540310240802c1002c1c03018280020a400394050121607280b41c00502d55010081410012141c40c00000e21a50703020300c448004548020204060720002102c10307030013000380f10f007242c2080940c0e0001c05810642501100c000c00b211886041589103151055032201240403000400d640d00e54001003000410301071a14040d00103139030b460411240900 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 231825926 1250 231824676 231824683
    0x120b0702010615080423030313050c0406030b09010e0712080d1401030503030f09121e0f04030f0b010608151908030c160518130c0302041a010f020c010f0f030e03030106050c 76
    0x7820000b407060b4600421b00c42c1d80403003900c0c0d02c50f002c80ca50800c030f00b81394103042d400e0000c58442c40e075106240280103c100b0001400c001d0142075000000c01c4040c52030031210355100040d000d4180c1c440c8203400c42c800001c210400400d250781d0810008a18580d4406d08070203c030800ba00100c55070380010040010350b00c10524a540d00480d8403008203000540315031240b036240704010010401c0e048122140c41c0b4180c05030212001d101040d00c2e103580d941e07540d050560100c05038080464180c0603603400040c1d034034880d01e0720758013a0800c000501e55800c040402c100e50004210328041641c0c0030a500002ca012091014054060510004d0181440030600604206619400081c0f1600c15480d84401407020131024503801484440301810341d600509018948903410b0744025071041c242018209845400d2000044031042a283e0780c1307007040308160980c0c8400c0040300240c0010b40020070760040903c11504032101501c2405d002641e00c41000b211030465000342c12803c00300e2400030b001d080e0002c082 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 231827176 1250 231825926 231825953
    0x613020306090c061903060b07030c0b0108060f0123130b010306210303020c120d060317030411150d0204030b07080c030405100b0f061801030b0a120b07020106150804 73
    0xb10301801820b83c481c00001e429008a01042031003a6146619060701c41c0294400c0c1c019210101c0c240c1d85580651900524481148100f00c42e100c00d0000000741501c0000741c111b004080c9407048600076800c241d050611380c103a500d80002c500e1490315402c02c1d070707407255140440030030a483d07000704a44800b840090300389c4526902012813240c002169503502c102482d500c0d200c0ca5450326001d41d40d01c815500302c0745000d4401032104401000000c9500d401202a84200112481882c0c0100c1551501c0d1601d0400c0c0400c440242c0903c200c13060007400361030490070f014070f2200480070301400c01512005907400c0b600160001c444101d038120a0203200d0360050152a4070881400c0d1084c0b4510302591481e48405c6e181d0b22800005441c1d58002ca159135684062484d00c010160049072145a019090311501807000901d5011030b2601d407000c0c0003420321954680c01d56403a03140a00f08641999a11070101000500c103004556940c8000b00d00303034580b900302c07140e034500650702c2007142e04003401d2190480481 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 231828426 1250 231827176 231827191
    0xc030605041a1804050114090d0315030816080417060402040f0e0d140f1c0b1212070206040f0b0a0809061302060c010905010f0603061526010204080613020306 70
    0x20594100c0b40c1d42c1c0d48a541d840d03402e0100030394500d0340e1900d03c2c205001d824803128400200d00c80305c08100c04880002140301801c0000c1c5ea080c001c0c44001141040c4400d2a40070181072101e0405c400107a0824803030b00e21445500c20350003149003503035600082c1500c00d0383c3d000000480d08071006000130740c80c1c0341c018096000203a540400a00ca500c025140c0c0d240503150200040c0310362006410850041070050b00c1c1d900b0290000c0ca951072a0030120340c4c03502031511598203000d600d0303d0704d56191030400034010407107291a00000d08020398200038120140c3c000c818101d07405001000041461104010881c009051428840b43c4443d00040d0140c0350700c01c0102400b0242e0702c03000420000100b8000a04800c5405603046542c0300c80b101b04180c09030044120242840d03090540740722018005500180890780900420007079200d03d402000040c070b003688144003030710380d074095403943c00240c0004c10340007030001000051038540d6036210706082c000c3c11110f032a03c960300006d8000a40c00d06010301540400d1 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 231829676 1250 231828426 231828461
    0x210c04080105090607081306020423030d11120f0903010c171b120a02160b01050a0b130611190807110907091e1e030203070f0f03030e0a090c03060504 66
    0x24101700c01050294000c100c03002c24100c00300e2203801e2025a50444001d041028072044a046204c1d00150b007916030322511a000384103412002c04010711405200260080d80400341114094003112350510b40c01403076400142080030820340f90a5642482060070401e0382e0780312342600c07483c0c6104003000620000d0003520710f401801004051511101c04941a00e00c2113180243e5030348418160740c0c02030140e030342c001e95545140d800c2d000c2400f03e030858040c1203442c1104c2c140c51058642040b00c245000d10305580b8425500c0520501034103000b1951040380c1c0c01500100d45201c212645980c0f02a860103e0603a5a2040011802c040c07101840b0040c4805a0a9800d61410300305500e0042280074544200030810394214500340303144000c50741c0540101a400142d4200b003895180d42004540140300c102c0c803038030a42d20300245000c940070700441107420031000c8a0480e813a507182514050041c00c50180c5c840080d1101045407a264406c1c00300251045c1d41c0065441d04201c00d00c0100c410340c2c220192003c2 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 231830926 1250 231829676 231829681
    0x105010e010b1c02090d0f020f0609030a0204090f020d061a100203030406090201180305100e060601080c160c180f27060e0706110c0109030c030602210c040801050906 73
    0xd002004503050080f01c515606154221540100d000b03016080c0c12550020001c080141400402032051101c14000c841d01c1c0701c074071109030400071103120329181290160030840c3e8600143c40c0c0740e0300000196018140640c642c0301a0b6001440c41031035507500700c448903543e017800c01e0407618a510303403504044241d9a4410410712520b02a42d40e0000a100a10325900d40250100310f901c5440490000494044d1460046072640b60403921a00304048803403450340781481d6014050000030f140340c05105c1c107071945000c903111074400b54000d44c004014005041c00501603e00000c04d103030101030040603000644c1d0300102c2c0581c4044240c5100c0d17449444094105400c034142d00603000495009918650034444c500456840e044c005000c0c9000010941d00070740e41d000601a4121464050310311805056404040001e4015911074900740405050310040c49030901c0002e849600a28140759040481c40d001c4600b03080c074080e100300071240b650510801150401403a070f424010243c0118400c00500f0452 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 231832176 1250 231830926 231830939
    0x60702012708030414190302100c0f230c220f140f011809050d11160605040810061401030c14040e161e030b011107080706020105010e01 60
    0x100c40a44800704003014425014004411420a10020710114064030f44441c2d941c406000030681c00d600007401002c803054000e8400021807012400e8a40c0142109500480f044c03040312065051402100d800010810a0002c5421007904c0c80c4240b00010700b425003a0700da00f9856051101e44280c0c10300404c2c20756441413007080350046503030f800c1f0315140c000940c06100c0c0001e080580b1000034045e5020312080b051045414074008124169150000c0d0003a01c0d2400f0200740003102c900f00c00c06011034101030344011f044c500c103100c203484404450341200c1c402c044004038140343c52966400078010030350000e0100300c002414000d01304400c2e4000e4041103554645400241400721b0401c1150400d541c4904016219000d41c0021315100c00c10b0800d5501c0e0f613103070781200400705000ea803550450050b4031156001c039803090000709044000f07804010302d00e0426680540140c0004102c450600507000141d0400307460400000c4000c1800b04010081c1c14a0031002a007142c00c180c00107145400d40d0070050002 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 231833426 1250 231832176 231832187
    0x21309111e010210180615061103040b0403030f030e010e01060608060301140f1e2802030112020d051c030203060a14090106050d0f06030f0201021005060a1403010917041406070201 79
    0x80804214001c1941d0030718203240000e01317202e0070009007034074a0700c1d11082024031102000c4064034603d480f43e40411281e100c45503628080d910400452040811061002a2081500200e0b03245c0a060104049886003e6242510000004c030440c0e603540305010040c0b10f0780211610740200b0300390003c01c40001014001000500003d016030070b0002d4000220303000049a809c0041040d14134801c5060318104641658461070914058150550a030400f21528240c03500c00c480c100c515024902c4100480c903420310040044890050381c23280a140300c441c07041a008180200d100e460381c0e40c0145c2d60714101c1c040018030462234000102d00c000d056210090754665040280c10345285013085501d622118082101524620000c3d025640c1409000010001c103c009601c640e4800d0302603e135041601240034080300c3d0b0840710181c1c09990b03003600f04086c0d81c080070040801040513001042c07801554581a6041181004e041148103001604005002103e44105000f280440300c8910340151034000820 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 231834532 1106 231833426 231833443
    0x1d0414010815010b030115020a06020c1501170a0f080d1a0306090c24070c0326030403020d030203071707031a090402030a0f021309111e0102 62
    0x31403103200c2e81c0d50341641c070002d03600350441e80b034500564805407200743c806040d030103180c4200d0040f40c5a8002041140f404400400d210310344042d00d02c03503008050f070003c110f81c0e5011803204009900850110100741d00b00002d811001090b007005021031040c29008664039280c0710380401505103981d0141c40b54030048082e900e40d55a200344042d111f0400c1820140e110307020440c1e280380000d0101c0990104440e0441b61406d0034084c0ea608c501c034105030740003612174014079242d81403d4035041c941c9000450590f1005401c506260340c01a696038400c01e080820f0640210016400c1031154145110004038031032881c0c06424000780c06001840000300a1700c4200c2c1c540d1026070541032010042e030050742d010700104a800b0f090b0315031070801403039010103c0e40310340403400140c89007501d0b00848211600a502e5040c10264810130030402003014040c50040ca6010307414884241c1c0c004ca03a204 = true := by decide +kernel

theorem cover : BRFrame.Cov 231654676 231834532 := by
  have h0 := BRFrame.cov_init 231654676
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231654676 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231654676 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231654676 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231654676 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231654676 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231654676 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231654676 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231654676 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231654676 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231654676 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231654676 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231654676 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231654676 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231654676 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231654676 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231654676 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231654676 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231654676 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231654676 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231654676 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231654676 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231654676 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231654676 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231654676 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231654676 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231654676 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231654676 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231654676 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231654676 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231654676 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231654676 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231654676 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231654676 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231654676 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231654676 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231654676 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231654676 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231654676 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231654676 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231654676 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231654676 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231654676 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231654676 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231654676 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231654676 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231654676 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231654676 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231654676 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231654676 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231654676 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231654676 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231654676 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231654676 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231654676 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231654676 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231654676 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231654676 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231654676 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231654676 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231654676 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231654676 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231654676 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231654676 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231654676 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231654676 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231654676 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231654676 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231654676 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231654676 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231654676 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231654676 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231654676 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231654676 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231654676 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231654676 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231654676 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231654676 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231654676 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231654676 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231654676 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231654676 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231654676 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231654676 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231654676 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231654676 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231654676 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231654676 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231654676 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231654676 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231654676 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231654676 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231654676 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231654676 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231654676 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231654676 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231654676 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231654676 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231654676 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231654676 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231654676 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231654676 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231654676 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231654676 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231654676 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231654676 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231654676 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231654676 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231654676 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231654676 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231654676 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231654676 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231654676 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231654676 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231654676 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231654676 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231654676 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231654676 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231654676 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231654676 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231654676 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231654676 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231654676 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231654676 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231654676 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231654676 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231654676 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231654676 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231654676 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231654676 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231654676 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231654676 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231654676 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231654676 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231654676 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231654676 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231654676 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231654676 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231654676 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231654676 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231654676 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231654676 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231654676 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231654676 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231654676 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 231654676 ≤ n) (h2 : n < 231834532) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
