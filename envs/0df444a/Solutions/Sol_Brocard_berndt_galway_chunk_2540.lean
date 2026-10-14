-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2540
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:00:54.998565+00:00
-- url     : https://prove2.me/submissions/7110359e-3561-42e9-846a-4c3839dea3b2

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 456654676 ≤ n < 456834532 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 456655926 1250 456654676 456654689
    0x411160602120f160f1205180109030c02360403020a0b2a0414010c05072d1508010e0601030b030115090f02090307051002070306090804090506030607022a03031201 72
    0x403001c0030072041100e0115000b00d6030030108240d0001404070306c00700e4000d66407020180035101f4a00c21000c00f594290b85541c00d00350b020134403d43e0f09d9001c1d82454a600150000a94580d403001e01041c440301c5225603500421000030401c400118003058401c0c40300410003500722181300711070300780003010038094043e203084ca03810540240380d400d180d03103808401ea0f0100c0751707074040010744140d00d0001900c01d4880080200c841d8000ca9201040300741e941801e4060301e100c804d1304445034030301c8441e01000261840d0094032a801440d05912207055201c81524199520b0780645c3c0d145455100059000e0800b150406901d0750038507002841c1c3e0041d4005280854420110602150f0031070008101284154070700650135420140c824011b600700480300c00c00c1d083c1c1d07034411148419620703124207048801000e012600d44500140070082118540622500702d2800c901402031030501e41006591240805180d1184520703281c003020740241210080403000c20040c0a0300da8a000003c0311001c002402d0050a = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 456657176 1250 456655926 456655951
    0x160605040b071709031602030c060a02010e0714090103020f01050c010c021f0902031914070b040f0b1c0b0a030501020f210708040201180b0a030902010206060411160602120f 76
    0x241075203202d1580d03407030113801424060351800d08084400312011009403801d90300351140d00181000c03a00c4010041402c10001e6000161030340140210070300300030295000e055040c0c031418801c2e496507120300c280750459504441000004840c400141e4960158103c0d5070b80a510b080c000400385500441c0140c081422441c4c4842c5030f620b0001c000c0d00f150600c9402940582c02000a82215607005a030442c1190240d2105408000803900d40c0c1d1034880c00d508041d40c1c01f8008038081082084441d20354000e032120b035030040e041c0101800020000d2568a000c1560f050326000d00304803903203c0b440140050340d001002559150940c90041c8020350040e0b1244030250a000500e20240601c0c21800780520940c0d0b503514804d8840b9001154200d1503052801c1b4200c0802cbd01c001540e41d00d1074024030741015540c4000c01c940004d40000390600c640240818011400c0405030040505140c0807a00003074190a40d10035540c225088c240700038083c4100c07071020980c031041030020360381c59500349903c07410001415 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 456658426 1250 456657176 456657197
    0xc0e01020c12070902090d0b040c060813050c190f030602032505070837021b0f04020d1808040801061212050304110a0b280e0105160605040b07 63
    0x520a03840e42da040c11082d2074014860921031225203800900380020700810343d0300403054544812041d4802510221410002510101700c9644c110720903560145004025140d008050f4981301d450355924030440e48910400d141e0b26281a001da100c0001810f98407201e044456217925046000394410b8400d0013100603124188175071034084181e5161003450315502c0c0360034031916598981c5070750009070f01d11900907000700310b035003403070260023013501ca80700306841020f04206000102900340101c0d9250480082e000c0a002001030b00d44401509608400b0341c1c0047c4d8511050b00c0d903600802c0e18041d8140358076115400003040c845404c01802c10b854844008100d82c40c0c0c2c034100e10310104500840103200400c011502c10156004202075a031081c020302e0340170341d1860208005003643c1d0140c2c01600c000200400c40113010708120301c44c0038800e62481494820a0040c080c05450708001c44c0398507041100004888001001038003042c643d03e940400c0038852414286800a214a0215001400030f9854104c = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 456659676 1250 456658426 456658429
    0xf05060a06140a0e06030709060e010e150c03040b0a27050904020105093c09040203030d0c110d0207032001120507140c0c0f180109020d060503010c0e01020c 69
    0x8411045446544802d00b242c0d400c281d240d00640c0080900c1814400301d0003800a4035225200194410340da140e44400c044c07030501c040501002c2901c2910760400100741101e40e55070300c2d1003003064400740d8001580d50322900c850055502d1031203103800c490110180130690310042c1c3d40215895034036003078400e20003110341414152403c444900e0700c9041d03404030001c0301160155004e2401019000703c00b07841c018070a036064100c4180d0b00c0d001440681c407001c402d21341c6240d140c602c044c00740e0a10301c2203034030308100e00301034000a40e02d008000314405015500e01071203000a00502c01c490520400c14280e8a904102d0f4101a454010030702c0281e54454030003034810b010340101c0301c0c1c5401d01c8105071035504c00c912000300f00b60b00608005000b0300a00c10862032488480c03054001601400008200030f008808025050200004514114071700688901c01c440050800c1096168151400364a0040e112000c00203201c020b081d0316803006406500c1d02d8030903884aa070214482c051000c0a800303c4032109400b40 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 456660926 1250 456659676 456659689
    0x816050706080f010909020619020606040b060a0905040e010b0a0e27030307030e120d091e0f06020d1b0305090c1002030a0e04060e09070e010803031e070908030309010f0506 76
    0x10f411108100034a8010300c20f0003040d40c060724190303002400c034a00700a04802050603101941c8402c5016074000001c0001070300e00341c0244440140e050700e00d941071112040020744000c045000e103e206649480c0032a05070314003503220191101c2c00614064184d41d80c1c200c03071880003c0581d0821081d00f41c0801000580c1840603100c0705d2045141d00440c510740d42d406040f00109204115040c4600a04061260007080c40c0d01070a4284240440098401b006160070405041c280b000c0000d01c0241d401c1003c080391155400000d00c075005440035956403038020043c1d008021032803040034840002e120510b003140e456440fa601c160b070720104480d03081c10074908003c08410b04400c2280168801c00600316510b00c140c1d0242a980c80c05000412416220320641010307190845070200c05500400c010003c100c0c042841c58010f00c01440550718504000c11210001c156000c91481046401c1c004141128890b80d6980000d0151200340c2c1d45a0400401050213000640410f040341c1e805c181c00f181084c581807 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 456662176 1250 456660926 456660931
    0x72106052e120f03020f06070302130509060913080c070e061002120d0c0201021606091203060b0f090102030904050c0307030c08061305090307080403080a1407111309081605070608 79
    0x26800200786110b6a40d5150400c0210b00d41103085000b500c0710304440f02c9042002a00480061700e0140e115038030640464030f412403d60045105641d05414040d26444000c10309030004c40100c03034040d4079a25410941e00c14807841d050b01d001c0e44030b40100062041c52101c151405a40c0403210030440c4c07181e00004030781d0b450000000c4548802c003003042d0f450344403059214228011a600002d0f003004840322000f400900d850005440c42da03250007040b802c00c100c0b0003d8114403040c0d400d040200e2410300c1342c0c0038424003d015140510707900c0010901c1d61607000f003042c4d6005d00da008000340a103180440825030107030415211000840c0c2002404000075000c0c000a500c20440a841c0418085110b80a40080c0001030081031003030004100790404680004000c10145001c2c0c41d09569036040c043d0000e08550810150b600103a0040c880000010040240b07102602001c03101c0302188000940700c80002c1c501010014602c407400650441c0c0c810921011700d840c207006006640560f0360724882940c0b00e8004 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 456663426 1250 456662176 456662189
    0x13120507210c0803030a1103070e0d030909051513090803060613081207030206070e0d060902010201060b070b0a05310503070215030a0617072106052e 66
    0x40020311041107403401e03140c079a0100700180d107a61200d9499003046091141c000309200d400000400c0310030140750080380d0303401d030b13024001d0f0f403451a1641009000301150100d013071060364409035485c00d0501c140503075809003010040c10426410121503880140181c1444e4074010500c00c061403503018018864040b54a030000f0390030f45142d40e11410000d2513845489000c005114990700410b00381742c200441503c04c412628800c0d6503d070386007400381c50200c00500280405c0070003200c41e100303620350764070307441c46254001c00201e000801840143d0252080c0d400c00c00c1c0c0354034081b0b660410700c528111803a0156a02d1070080040361900ca01c82e0000504040da000340c484048594618415200030500140701c3c0108107490400324a64005440c1e0080d16043e44416500402130101c015041e105503c0181100f80781041c011809001148d00c416840c8180c200e107042c54041944908a180382d20b12100780c0c014810016442d000c0d140c4005058031405190020213895504845045181c00da1025901c0 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 456664676 1250 456663426 456663433
    0x2070c05031b060c0a0f050a060e01061202060a0e040c0504090e0606012118060219020f25090c0203030f0f0912030910060806010518040b0f070507050f03131205 71
    0x414014400307030380d000702c00540c018800c403a01080401d1091b012601c00c80c6c86080501a019a9810643e003174642c2400c007412940d2410b2800c006241c24440510a2240d0554500f5140c1303a0b000020740300c2280c00c07c600d84e0090b0030003580c104456840310040041c0c40c00d0001c1044003408020a00d6a51401180d815000c68400d58440d815100c030040c10300100d004859000c110020103230b240551011080354111042c2d50041140130384103003082411094079003640b0040034080504109141d542a07240c00b0014800030000d5080029401c9044400251540100500a003224080000c2d41c9500444019410380b0024000c00c980494448842d400741c1c08840080000d544000d81c10703481507101a01c0c8480a01c1008858240450399000703403001091034501500c040d61401e0148410700d296a084e42e812141c80004010000760b00107134141e004043c188128040da9501d040a940e03500c24640302a01520500d2401030084200100400303520000d031f000c0c1744085540d6031004840c0303003400100402941 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 456665926 1250 456664676 456664723
    0xf01060311042c09030304120806010e030316050c01181401030209120c13020906070b040c03080f030106022109130b06040311040b03030702030d11030f0d02070c0503 73
    0x1803094205540600d0901c00c0307689401e550718600c801082c5003a5405181c0c500f264000c2070035100360820203502c04283e901861551801e82d8405003d40e2580348000141300341d517030105a40e030b4840d1808180140016003281c0d6214144000141796200d16601160244151f42c0c0d0310050b9441020050a0005400441c51919003000b4400001d03030040c603a0117041503803c0c44000c03070340e90b11150320010f0003545c04040c21550300d40200740300d09820103505c0319050f980104200d4006032201d000b2503440c0c5803c0780304810301e51200c0c034242d1903800c2035500150211001044242241a180700218100d80ca0340e001c40303820228118518520440b007841c050141d810074402c62803141031500c21150b00e0844480c001424041c4140019002d800c29001540c00760070074402a03d29040c24481c54800d074a046000758101656076000a0307940c95070a000c04200720010300b0081089100300165624242407011395a11348840f185503000940203020259000400704000054505012a100010700c80d0204000b1805 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 456667176 1250 456665926 456665939
    0x2030406050c100504060c0f230306030709050403020f010b0a0e0a0b01030e0102130501020c0a05030c060a030207210206100605190e030105010909021206070219060213080d12050f01 80
    0x180c125600310a5103020703a0703a01220040c03840c400c0501c1684521800038041f101da00c00108035000c14a529410b1200325403083c10382d00110102680c030a11100c5155a41e41d481c040424201501d60b03008074450350a21051104043d00465260002c508901c0200090744440d410030450011920444c400c4070814400300300c941001c0c0c2c100700c100040605021408084189400703003244e2000002d043e03182d0390700809002560f030600010440c0348007222103564407030904002079200c4000c031740c41c9031041400140301440036000c5d0b011f030342070070350812808691480e405150706040b100c2e9840c41c9005008001c00a103a1443d4449007409540c0c5a40c2e90504000c1c80e42070340079100981080d000c092000019403480180e4003402000e02908012001265012291041c04044404404958125045070003080803107940011441e84100860844980b01c8043e410100000e1041210600c2079090650f8040303082080001c00d203a01200680e508010401150164801c9035803d850f58940e825030100100100d = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 456668426 1250 456667176 456667187
    0x60613050901230a0e07140907180906210302070e060a09090c0816030809130b0603040b01080d03150b030a060e0906010f05010e0f010309050705040608010b0406060306050102030406 80
    0x1c21050400050b640c1840440b0f09924410b42051941c20a032600c20048000814090f8201102c02c0000516000d030034402401c11042900d082e40b801203c1620000302c801d44544221602034003540d141500450301c6d0040407001e0b05e21170142c9200700e100164542c8010b004001072103026074050740900240c0313003050211400424040d0005a0144440102098491040c880e1a44003440b400122407170701e11f4083d007141000007800b8a0784801d02041c4040001c210050100c4070314410403128441011040030141c03008144541c03031203412030004001c2000308100100000e050319048000c5801c414002c10080f0140c45408003864100481c00c202000b01d0070411024581081c00e41801046c120744072905030401728000c0702d031800d0a0380900c004000c0e8400051002018100a103480e820004035840459000d0325a40c200b181050f071785804440c140300040c080c00014060040083c031103e03999211607806805540c0c800d501c00c91510000103070450180c03003404122507040e00070703504140c0b512209454 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 456669676 1250 456668426 456668431
    0xf02040f06170109120905011205060604090c080403180f06081504150e070302030c0a11120301080a030306080c0f150c120d290d03020106050303131706061305 70
    0x46a603110900403840074007141c6400c1c82d40180d00300014011500d81000c03200d080700c0c0c500c01410300120080910048c1d17030190707581100480e6800082056181e050102c2c0041c0718a41c0060315191500d4000460f1940c00610540a540659100c44d01014440d030021f26502c014898041078403202181085080d01981c55a079001400d00e0b150044031940708081015911040d10000042441d40300038000000e1000f851508079025140c21030840c070340b402c102c110030700c02ca000b8441404400000c06404c103408100801d01c00c00001601c90300c035607603032a802e0307640c2130088001c50100e0700702071000c210310340002480e4a40d80002000c460b001c6480005100142031030385000080103c0030080e81700000e000300003880c03c00414942051391141c2003640035088480303000110802e0040d014194004440c802c8120707082400c120342941d03090350380b45820b03801001c0170b0340955010b010105010390305032034202c0c92404640b4480c0d80c9100411005400a0715050115802d0f503000c5031043e20421001e0890303200a6 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 456670926 1250 456669676 456669701
    0x1c02030102041a0702090c120103020d0203030d0c02030408070603150e100803040e0f0c0306180606041a040f0e0705030a021b1b1e030309040c05040f030f031701030f0204 75
    0x18030b45a100c103000302807002c0c4084400e44071040003442c5011420701600c419403049071010f000d030400d40700c032042521031001840041e120750320f1115010306540d82441101c6400300c8240d4208000c0f414400080d403250400e101e03642c0240a020320001c0d101340079014814404c04031085506499041a0032001b01240c00760a5098074002440f0205117210200018806018016a054440e2400003c040c001280042003020b6084042c401d01603035488000ac40e6070b1014080101c0b40340c41d03031004007080c480d00983e841000080381c034242940f10445400010003e44500080001c0605e81301d0b041c0c1280c0100650740140010000c00001e030b090101c50703002e4880007000b010301d08141034061030b00e1442c240094096288588516030014100c2c980b482c0841061450170a04c0c00c1a0240140020b449010b0003000c94011078a80c4c40e05e0300318501c20022100508001c1d83d0000016480e810620610920b20004902184801011422650031502811b040f03d610001c0c10f01e01503074960a10001e0400b80c1440b4 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 456672176 1250 456670926 456670931
    0x6020a21051605070302091806150111010204090618020a1709011d1f06060c06240e070314131b03060507030213050f0d030f1b2f1c020301 61
    0xa4002c100c000c01c24811405070004250680c10b500410080d400302901403400c40842175a2100e02c0715011034119403100f044010010240a540c0c01a2020403954174101c0455100240100e80180d1950043c006d40b4050f2740040c130311950741d40c2050100d129079000600444d031109a60b00b40c1c1c0d42c0d0304100560220b501400440c0250408944038010500d008100c4060781290905000c140e898030701603042c02e040c11005101c039030728001c5e004d00b036505d112002620981d19806107040410b4009180131404075618941045c540e42c40520314110f041c250f600c40002820807605170401141490a81d02909021803040842507160b600d120b03511090404500300c0b640a000000003040c0140304180c81128540c4016a8580710080c80031500b00c8150000e43c810244020780503056100e500a442c19580d00d030805a000030011241950707040c100c170400000b001d1080185030100500c4078080c0001501c030780c842c4492603e04010744504000d00070f02c1d10b900308407041e110203580703441a9400c1541d580003a000 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 456673426 1250 456672176 456672187
    0x221040305100f200d0926030916050a060c060f050705040f05030109080711060c0d0201140a0507080403140c03031303020708061306050a02190908060106020a2105 72
    0xc181c2402e409214030340d200742c2d031450f01c0b00b0121450b008440314060311058011201e5030000313604c0c12500901011a00b0300341e54038100010001324110782043e8107010012520308030b6920340801450380c0308407403100ca85e01409180340c2a544c01200340e84150760008009207100d03030a00d2030854410349614416101c1c9502c0389103d00d0400c48500c0307450f002d00300690783d0f0f44d640c40c181043c0e100700c124168000c60180e85002009004542d00009450500f5480b0060241d05412400016600d0045c541404840c0c011f035100e80e1241c54055211488040c048420105260b0780c400400040316001c44000020807240000200000e01c290543d00205100040e0b80c0d042090349809a860342d082142d00c01004211403402c078043c50340410511005004010003040399203030102c86240c800042610080c503a544507008688540141d0b010303a0617203480b1004c00c417a03070b44000384001e106069a1080c1d0b01140109000410301600c04104281c980390021140c0c0c6420200000c64690410403032405000c00c40c05201 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 456674676 1250 456673426 456673433
    0x6191d0714010224060105043b0112030804033515030d0e0a2d05040b010e060304060b0916030f06060f120b150a0801080d02210403 58
    0x200405101140401442100d080003200d10038500040da20605550003065086040e000400000810044160310510076448003801614a0b00072074001071000d182a00d600700e03400c4114810403908101404050b064030711200200d0301545001e0280078260b10038080c001c17020901400d00203030460712a180105c1707020301c204002100e442041c10400b80341d0a180c80c0da11203014520004a400107007501200c031001440740000703907440d50200409400d02810301143d82c0c0d282d5807050715000500c8140c0030000203002e072408004c5414000e0a20320780141c81082d02150b00d0900d03110380110440103071a01d44400011204014050704002c0c81111856102c504401a6856001c8418040e01c0c0382c0300c8411b507080b080d80d0090161221a24001415840c12000f0405994010f00b0b40804c044035041100c69403940580072405055034420594011220603004040f214050008003018140380d0340346100c07640c0f5520016119440d00711440b006a10500c1483c00006410340082d120341c0414803001d1415982e42e4 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 456675926 1250 456674676 456674711
    0x904110a140414151005040803031003030f080103172a0d1b0b070f11121306081504020903150a05010e0609040209040803061318170403050619 63
    0x1c100421506400030203a0550070300c2d02600004000800020b00540303000d203201e4007180220b1200521071040c0c000c1d0303c201d5074000c4080702d01800d42e80058070f51742c0c41c22010802040425100460000c0d40d07006500000d144035100a074140c0e94003103084130003407900d160b0f110110f8211904d80040c034414410410040400700d10360034600a0714202401d9421511407028150441040410030030308410810040003e074040e203010380c040304d40c0c2007580043c800014105c8600000001400b858450201403034050b0070f0400141204405403402249001d07201c01d02110b0700d82c400d44c0c1c002c00690518000040d07520380354024101c0c03080050700300c501d40d14004820000c10801600c18845d41c81ea10401030200c0e440006000354003100c203448003c03841c02c080d40401c4000400602c0540f1044010004c60803075a00c140007680301090b26541031100c031004035a544100040c1340c4003281e0924860a0343c0c00b074090031005036811070750000d001e031007544d86e0841201c4003c0560b81c01d4000069036100b002c3d84c07030800b50 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 456677176 1250 456675926 456675929
    0x2010b18040209010b0703021f0905061906060e0105090d060b03060c1309020a0203090409050715090801050901051306020702041d0a050708010e0d2a20011407020904110a 75
    0xd4800034a0400703006000e41580d06070040c882041d0100300e000b000c00d8000800704082011658107403011080030040d00b00030300d14440018010300940050003a40c14240c0c178201240c0390346800c2000480d0b95400c043d2110740d00e1b42460381c04250f007031043e00a2031401d0748524400c3c902409020980c0404240001d0030720808481590b80c0c9000440e4402a07403100303181d24406082e18860861030301a01010181da20b01990550b01d1103140c4410002c2c08000d41070024400a000c0320103c501c000025070302c00b030081e0480e4054854250b29000014510b11414051680100c14098902c1c0c5544010780741c42c40a58404403090742c0203510f4080500300e028910610348108d02214003e0b081050031031804505003066a4012902607040c07140c074440700c007804900c00300d02c603107075040002c40e90003241071000701505001e0256907244612206130302440082c6070b042d421011014000c2d803a000e00100191655542c08400c105001402c2c050b03603006090205441d60031a024804040090604200080240805 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 456678426 1250 456677176 456677209
    0x5071d010603060f06080a0b12010f0207110306010506041a120a0f0b09042a0b07060c0f020609120a020f0a12090f0308090f01210902011202120106080702010b 70
    0x119801003040d107a05210b514080c2c07000c094101201c80c6400002405820050180042e20381e0b201140c1003580c0d503c00403c4e40c1112180f00034070400910310407000080d0009002072b0b07102c0c58900540c0300585000f14002d030685500800c6d1605103410586150015a840319031401e6501e41008045003c401820303a1520038a2900030105000c203400c81d00d030080c0e400721000c50340990700100c02d00c80020a0070b144002c100c900c28003002a20344c01d000440d081035803180d1080a440900044000901c900f13500b200303024000c00e44454040081101c4120398518048a0a9003150014407480c144801c0c648005e101c0c2c10300500c1118000c03c00e404c121400c042c0041400c4034400007404860800b113410050b850010900c2c0940b01ca0514035546802c03140d441011309103481054450345d0319229a000e5038800c5801e040c0000010450740301c1c2c0030104002d0119080c144d0100c1c001581801032406d0b94000c5844155080c120401264a80074096032040005025101507540754020442c0940341c0064804000c40f8 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 456679676 1250 456678426 456678479
    0xd06080717030324011716030c020309030a02010e0607060f020d05010807030f0b041703090a051e0a020904022106060f15160302030d0c09050901050a030b0f060d1202030d05060a210507 81
    0x21041f00c080c0444810007103a0043d034000b07003c091004e603400b0503002155902070070003000291a03d8002100c1c2e108600000301651f00e0320f4486810192940d0240141c008840c5040100c4e90b00c810768245c0d10341991000400e040d00d04424603000070141c0c0b032a29000f5106140105888200900522083c0c108550784030065100f0421201405020040c00c40010440100202d82d0060b075000c494541c401c030040a80a481c100b80400c045403158546111f0202c034685401c2d6040000000715030702c1e08002c0e603010344141080c2d08515000e14000c1d86010301c0790051890b1510308040c49000f2045100722240550a5000602c074070314240b1214056407880307040c0c40ea514890b1506220801c5200d16041c0c015a001d00c001040c1400041c0035500502d401050b12070014280b40c0c0c6042c0040e00051030b5503030052040301010322094640d50000050800c011404809000c1e80e620032090103204c03d043d215141169444c40709503501c5100000d05140302c68098004e4035074450b11404068a261070b540e499a20151 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 456680926 1250 456679676 456679711
    0x20f0d050103030e1f17190e03071208060d06051008100c1b0b07050f07060c0809010b04110901030b130207051606030501030c0b030702030d060807170303240117 71
    0x45c190f40450380e0100080f0514001d01d0103042e00509100000c800c90251025480102c0c03100c2060600742180f001d03200c80180034503c2c12030017054803900000c80072101c0b20307650034012030032600a544940c0700b0f5001034206404001541c41d040058140a440b0070754504000c200840e400c0e8050010075480c0305969030100b007100703014400030041e002d4180362201c4013003400c2e584400110b01d4030300c00e5000701c06450541c0c0ca50a06a540315000d00c544d8100a15a41c504060000f4180d00a5840c5210f513030342c13000070400d030103c96050100342c030000b000740c850f8990708200071800356019a001c489010800344c4010744000008810500701d0384100d0040c0d416520290501b86070201c40024000070344000d160500c525490360b0340c1c1d0b8a103010113004040039114081f00040b4414802c1056840040e0b4a10341802001e40d6035540588403e81402440880700110140d41d0032917200104a0f4051016400f84040b010613600d42000f50440d418002810441c2c0002403900701000c5141442c0168100402a035841 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 456682176 1250 456680926 456680929
    0x2040903110c09060310090512030a05010905010501020c0a09150b040e040c1a070b0c0d1a100f121a101e0c0201080601112d0c0315010306020f0d050103030e 69
    0x1844405405104200d030f10200611601e0200740d6201080640300003055481140ca8070703501b81000c1c000742c84842c26021007040184c0200340c0169048a540860030407003a41c0b120700498950007018295500001c0c84e500400c082800742c3d12103003011030001c0800000f161100001c01681d03019601c40c602e900040402d00090040709800c0c074004160710260802e42e141d88011028443c05000d80181110b0140c8001503d0045444211f4681050121041044012200d2801c2005908a0001d401610b100100040040c003403411840440d106464082d0043c02c1c25014101901541e10384581e0034128002410564640e070120107460200c54803a480c0c0444020980d10444480d50110f0080056202d003000c0580d070005038094000c003003845c01c3d46040041d610311a20707041c10b0421618480d0303a10700521241e440413148100c060610341041d1840304000604156440300ca800b48418550103c800400006541d0b50082c1000c100b01c3c440241412802040201107507400d0703209401252011440c0b1125 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 456683426 1250 456682176 456682183
    0xf0c02011a0105040f1206180f0c050f030703080c0a051e06060105190e150307020f070e0108121e07060203011d040b0109020a09031220030c1009020105070204090311 73
    0x7240428a000c0b410305251903100b10f02c0990310301c170754500400c02c0c41c20a014400f0039003104400351941000070034080b4481c5403a485a03421440181c400b01c0d0b03c10030220b07003072511030303040c90704144010020142d035411a19404003e500c007410b0b01546119404c1d402d00018400d03c03800441d420107070071594100f050740e4281030034140014089410010100180341c0c0d40e8a89a010307000241d0280342105525078005c020070b542c2c6801c0104405081408010032003d01d0b4006a5441520038910699840907566101e1190b0300b882030040180303d400c00e1a04e07001003420030380605010007050030b0300100d5082400241d001a848060305841c3c0580000050004495421340400042c400d080340300e6480c0361a0b00d41e42241d46041c00740f4a403503500040c3c0900c040e40300d004034030061500407258842e00108910040c1001981d4680c480000d2001a011180900d0102c02d0302d4011110030083d154207000c564040c0002d01c501c0c032089060100a01c40c080c0035032602e10401c424144640c481d80707145100c07800e0b0b0b030b0314 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 456684676 1250 456683426 456683471
    0xb0a0f09051302030a0207020d050609070506180103150b0301060f1b120318021503070806010807080606090a0b0a09030618020102030d05060f10030f0f050903030711010f0c0201 78
    0x600504400c20001c42d1500d41192081c1d440c400001626500c880e19844080e00c540e21010b0340c4910341c00940302c140704001c030f119800b03010200110f641080d6100e00740407960040070241d602c1440b1074000808154026000801511580d0040e03116903034840e500c8000f184c000380c000340700107000504460015074210010300d121141c000c4001000f50980d95803106002d40030030241c003c041d16440a030401551044081d07101c1c0343c1c010030132481d0480040381800180c204682d000b0000d10802c0206102d540a5110240986451360b01c0ca1260382d40c03041031054035889080502d070007111200300054952800c0300680a1010107550714040d0303520b1820f002d402d660102c00100ca480714690141c0c40180e07000400c072811001e04000c0466141d80c0d0000080340f808040c60400e401960040202a040341e00d07074054200f0690454040150503c00d094040440740100d07400000c2d41e00c200042028140605408000c1042940011405902d2a41030209541c450760300480542c0d121002071022030080c104400 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 456685926 1250 456684676 456684707
    0x7081603051905060a0b010e0301061215020f0301030b06031f0b0901060216090519060e040b10150509130c05090a0e0702061914011410080103081b0f070b0a 69
    0x5a4034400c0f6102c1546a00026005a1402e0f690351914030480e4024440c40350b141000030000c00c04d00e40d8803400307042c20b80d05a502c2124508228030021110080d40d100f82da20840400b045641180c0c29551919102c02011301890360510840101000ca04110482c0540780300c0c1c00440400c2441d08801402484003041c2c0001043d500304515080e40e501442c075040c8102c0300d0205c2c003c181d580311005e030b800c08608140c1c0d000c1d0405043c00404540c20b0460201d0501541c880c201d58000b6a5482284c6c10030b6001c0c3d0b014090703071000d80e4030001c1c55861182016100b000002408041c04900301035000045605041481c008280040b400d070303100d0b2514008050040c100d2450005040c0b0307201d18025110500200006e1030f01c010010381c000642191307402000c3e600d04c1412010900e58480000d603526695040c07505102341d05480301b1410152003100414100c0e94001e80d014100281c07210402400c02c03400303a8a2000384504d1100300311102c000c00002d030041518550060750303100310480c001c150355020704048 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 456687176 1250 456685926 456685963
    0xd0c1205091903090b0f3c0708160308091b09010b030c07080d1a030307051b0310060e0a06120c15050d0507170105191202030708160305 60
    0x1040030202d094050081030500580380200c0c64a400d60340c1c0006904540e1000c040401d402d01c440d42c0400080800710440201c0d0084120307144205e0319a404002500c80443c1c1c813807101d040702d40441402400c201071150f003036242040c0040604040c49080b441003030740003c000200744100c1d40020b00085030030001c02240712054004d030002040700800c0620801000090020000700c1c907100392000d461003a0340c0400d84650322441c03100d0450140080f41d450041c0c443c0320551208a40c81e0010441d1200d561000180c0110385e042036020424240b49480c440d00b6006002042071501c4840c41000d01a01c00b00404031414144814400201c03186e903040030000803c006038036030200704080842c00490381100081c01010300b02c1c03081101c8500400500500041c1403009021400e43c01c400c4c5103c8035100201e6050a80c1e03601e404010780740250140161144006e0300051025011003411951104e0001c0d044503020b0383e58003800e40c85c00085034610101580d084c0801e0040003014050803080c0c0560003200c = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 456688426 1250 456687176 456687181
    0x603110405120a0b0f061305041a071e0203030a1b0504120302010207020a080a02040e060c0714030702180a05060303040302060a050c0106030b0702030c01051312230d0c1205 76
    0x108840344103600849104500280040282880800001c1c4505600802044050604202000d030103a02540d030b96218203450751903142221540d200300340c03103a9044031004016403c1d236410711480d410040c04a0080040310403001740c05007458603501e50f60b41d1440c0c0c0115503d1800944c10070498036400d90000c11700d074a10751030f001515441802c2e1401d9824403c2d802007400c4e07291800741d00901c9210780003504030b4080203001458201c003142108825000355001c0c841c0002a6003543d80720901214940c014090a0001d5000b050140007811841200d110442c0d1820010703800040181c8180c0b603c10701c0501c440010001544c9050140d140c000509400a42c281402d5500040f054040c400e080c2c41040740100c0c410079a0542500401300071341d04403076074028a08100314000d40b00d500926074440c09609100102d500c80f0303d00100402c2494020900142e070040d94141213a0303003203c4890075000c503910300c000100070070010401484081c03190280003c0080b4a00800380100001905503020203150a08 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 456689676 1250 456688426 456688451
    0x90f050901030209130609110907110613080d0f0b10080f060103020c0a12030225080a0819020c1606030513020f0d050312060a0f4a0609010603 63
    0x140c192039040f5110244e0360b499090302e0000d01c101c0300000d8000e5045c03480180600448040721201042c0543c1d070520260b071010f45c181d0344403411800c0184c85921030340000e14160a100145525a0f1260f59541d1900c4801085941920194800d0500c51030341d640c44c100a9103001003000c00030460318140b18089143c400c00165100300010407403030604d40c00046440d4911014130891000c154488501900900c01e507500800a41183d072441e01ca080e12481454000f425813031071520f20130340c041c4226260000042080311000c401801c0b1100e48110f805410b5007a442d01d00240160104000041c000c8506072100d07000303050051f5015906041c6003100740600f40c194400403140560301a11b1400c0400840d03408510f07007090303000014006003c0824030540348040c10800c140035410803282e01e07401c40c0c2ca07191969110b0070700d489000440410924940c00003041603a85020079400701c154a1501480c2c0703003071103410070110083c41a020b0307010010003506242c03104805016007120b16041000505a16 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 456690926 1250 456689676 456689689
    0x170403200139050d0c03180f0309050402180d02040b0d081207030501050102060a11090d030e12010c080414120a03020309010e01060b0702060f0d0912021902090103020d0f0b010f0501090f05 83
    0x1d03501494030380c518208204d01a0b0070100341c50100003074500145500b2308040080f0710140b00100e002846494000030646018001c3e01e0700504504400b06004440008000c94904e400c10704a800944440c20500940d5842c50320507501c5028041c059691401f801c60001c031500c0080800313040c146840c0060000b03036400140182e01010000001403c0750705820340215a0052061142d4000e0351142d0039810541c1c000c50880040d01e041c0c52031030042510382809400d0320300702050356000070000d40c0054007040112050b200001480d0090300c010007583e0f04500b00950200c0c0f48100825000424401e030b84c1030034400e14904e040848000c001c09810104480c1c224440c105d8040e02c170b18408101301d44600e08403c21102040c40307001c0d0401618443e0700c1d01041e40c00f0070344211409802040c5942160100380d0a030840140d900412082d2141e007590b08100100018107416140540c039885800c00180d030000d170880c0a042c600b5007204110740340500040c1006841d80100540c11440070741006a074582e075 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 456692176 1250 456690926 456690937
    0x30501060b22030b180709020f0c0f01140705210106030506030d0c020f041a060403140f01090b010e04030c02030a030216050607020603040809030f0312040c0617040320013905 77
    0x403564820171104905000e14184107a04a100e0042c80020010314490aa8009108005002c0140e500b00104c0c4070009003200c0e54000c02d16060054480041e01a500c101c0040122100001d441c04a45540c00d0745503280711401d80191010950f500144129803600300605c0d4104100c901c3c20840d040c4899000ca01d0101c010a03c690150b034580000392584540c80c008800d40030000780030192111360703d051041c040000000d810006000d24a52411030750418016102c03101c1e082064004103074602890000b01e030708001c0c015010460f030500340d500141d5050000151090003a402481e0040980e41c00030801d200d158001d03849200c04208140c0141c031010185c0e40e015030840703145612110310700d0204c1d04004921410f403ca80c0000201c480c41c1da0a4a050740d80101d0050340c1864145844450642e0380c00401403120403c0e0340d070040018006446242240411041e440f000703249016200700031800d5480e1030020001a41d40428104556840442c1c404003500038020540614190202c010b851442039 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 456693426 1250 456692176 456692191
    0x1c050c09010e0f042904060b12160c0501021303110409050c04090f020a030303140609012303010f15030b06030a0b04030807090e07050c070906050325030501060b22030b 74
    0x9400310f80005980e030342e001d80b102a603c000b020708003070501d5200c20655200260380300d12440c58000041140241d0380244c41ea23620740d86814400d00d4907101140c5a2410400c03d00d9410400740f0b40340f80d0001542030000d080c5005112031510700c05400c5180c07019400c05150465405140390081e0343c400301d00c0002e19206002c00130740700000e80c550b190921560310682401701070340220401100004160345507003c41c40100e81031010540355180c45040000840080c40340000d0400c00910300c0410b0411040200094140140001b034404074200b600415246110f00f00c04810100311020814492401d01082c3d122000b1070241451101036528408420300140028080000704000200c01d01d00030038915014110759001c8110318038050720014841e5009000d03c0352540200312000601c1d1499009000950740010080c02101e40360038080da40f803450246901d0310b5152840e41c0040070600a2150700050200d40e91503e07641c05403804814801c00300000301d14800c40300c902e020004a181d01c100280c1055a = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 456694676 1250 456693426 456693439
    0x6060109120204020f0a080709060215160e03010f061e0f031202030d0219020124090c020c0d050705011b1203090f151508030f0906070305040b1c050c09010e 69
    0x7034008500207001d0742e01d00d01c14500e00020b0302004030381c11100c1c00340f10f020030f5660380000036181c0f1002c90300c40303040c0120340c852030321000c1c0403a144139614402c5800786039a5180030415850075900280c00e6402a0a0b214601540d603172040c003508546941c500090b46565100b440090320700800000950010301c4080c001380720302c02207031500341c0c401c1c02268040d0101000a41d203614040092100c500c00007a145805076107003909000240001e03d840056804a0307a4460b4002e0345052290006031403040480d0f01140181d0059000c1544c9401084400c0da00400060010a05140000d009215400c20910b2a42003202d80c1c000020501c01c0510052002d42c031300401c2216291030700c904003107400b400c01001c1004868400b40721292581c40407103c0035000ba8030a03140c0366100384840e280e1251559401075014108600904c44c102600188041c030b100380303072052034941d480551800f16084440c14840c0c402e65280c280c82d114041d401200c0d000000a030015241511650010705069281d00e5881e00880 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 456695926 1250 456694676 456694709
    0xd050c0415020f03030c0f0705010501180c0305041a2d0901110c0d0c1109040506072007030b070c080a0806040b0f01050d200a0c0203010f18080915042606060109 71
    0x7ca1710000e0703d100f40e41c03100c000d1001e543c4601881c0300c400070000003408107a2130b102d20140c480344039001d068000e42e000b0100904020020308040c0c0001b8004000a01802c0ca01425000c000f4140345062055405501551082c0c00c01484890130354805443c0c800244e01f0500c00d142070500c0100303415030003004600344001d204416103051522003652881d2142c2c45240c060402051000105001d80f180c11650356022903514201c1c005007003800d07802c0c11112190701051041c00050401261240c1242c014144139240111644d6a104607a000398bc10074002604101802000c2c10305014030010824111008941c40c0302c4c10000030310381e020703e400203d0510707264040d410603182a00d0241e218945201002e682c0e481c0b00303020241611082d00d1007203002e50310703040d9010901c598505c9055480383c10101e42c8403038440d080c3c81d40d44c07081c5c1180caa00f6074403140d1880300034001c8003c03c0040c0000c06c12140e6450200c041c00184050b803080108e1007000716002003042010342c3c0ea02074070f14810342e51004103041484 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 456697176 1250 456695926 456695947
    0xc0121050718080a050d18090e0c04050403020304030620070b150301060801271a04241410030b190209060d06050915130b060d050c0415020f03030c 65
    0x740ca045801464156580e02040002c40844c10b02482e07800b46080303071070700c0c122840210b03414104e0018030b18001c2c101050500c00d0301c005030005a41050608115500d1406000002d01141d100340c40c12005039000050400c104500d41c0200e50b070003059510000000c0080c3c0400c01100e20600c3c0c0000c0c80c0d05020000128100c5040190f03801618024000700314064980403c1c5009110801200c1c8d810800a01840e900500c0303019250003466000b0344010740754404c0c055446505a001e03000b201c6412000100d940012010701981d50755011000002c103018030880e595440680c00a070a03805030f04001031080c00070502d460340c0240c10181200e0701107031401c0c141030010000d001d0303800241d034000000160000a103220340c010405581044601c60b44030b88400440c513007011419180340c0d81000e41c01c40c10540e42c1000c1d5000b4242000083c0140346062140184482186e00850760710103104004030302031103941146d28001d01d02e1842800100b1000700009689556408000c091603004000000d5004c0351 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 456698426 1250 456697176 456697187
    0xe100315180b0c0414030601050a0b0a0207180203180604020102071a0d050a0501050f031f020307050c010f0c110304050307030803060307080709050601032d090615170c01210507 78
    0x700e5000300b140d800c103007090080d01d0300030b034014441e84c000400c10600c5201c02c4c1c5004100700e1704070b401c01410507051510340f055512454015414072030550240e000009510498010a11840b40e1203840050b602e1400041d80325000c00d18426000c1e80713500503810000142d0b00003c40c502561803c02001803145440e0300c04038014424800504013840c180010b118940c0361036000303141a5102201c1c0f50384090440030516a032400c1d81042e00c0600e4110940369200c02d100d640c0115008201032410601d0250401000c909444200d000782903400d584030350b0120507a6001d0840051100381501840c0380c546030a0029503514000d0002404082001000c94072640d001c0041c00010304100003600c80d03c2c0d0303071521608001e000c110b841902180c203150480340800a4010040411285205218440c0500e80b0340b10b0028047c492080360180d65440003a00a0070b80c16036564020440001d81c0c400241e81d500c1c980b414003051005541c14003d90b0348060b10340c140b0f0407000c0f400c0a07140782000111542c1d40c1780119074 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 456699676 1250 456698426 456698471
    0x1104050a1d0106030b072c0406122901080c040b0402070f0b100605030c040e100513020a0314010509061912080a030c140904090606030503040e010e100315 68
    0x2541c1400e9041080401c0e0640040080300e0042c00c2805443d0307134076802a20342c000c081a000d04420701c19242c007650440645da0603054840c0240c030010b031850b1200d107107448000c0800e0054541c0c40b0b045035420010307483c2520381701c0c2c0000d807440c4110b055407400a1107640e4210051800e881162210900201915160f040d10003a40e040014941d8040d84c0d0b080156595200f50f4407440340861007840854101d01170000ca03405407141c11a8640f4181c58809a01111500980354024000c0032150004059951107800348044d03100c11401640d80d01c120501600b12020241284801c8103a030b40100300b203a0340c11840940c010410b6481c0c10444507410700011000c0f201d500062041c2c03c2a0003640144080c20010301412005071301e01f0082141c048200390340101103070180c20800d8008021442c0c0a007025081611214482e44000ca20f254880c2e842070708513007058024090950700070b00108000700003080220b4201c552600411001400c40d202c1055014000c28048080c5841e00e896a010001030840000d = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 456700926 1250 456699676 456699701
    0x5070206091306080d1d0909030c1006050f0111060703050c0f04030602040e1311060c01020706110a02010b0a0308030402010302090604150e040e0721060b06030702030903010501121104050a 83
    0x1600302e25903010510090015005610f0300e88580380c0e11036040e0740500640084201c444205600701403c0c07400b046205507005100c08601c2c0018060814102801c000b00591003076510300202d40d503801c04081c04080c0700c00e150103a0401901c4030400300500c40209a058115410340340204d0341d503980b001c04003094494000809403081000a001084c0140c65014009403059800084a65103c03031508c074400700d528450281819600c0c0509201d01d140030001040e401d05800000743c140070080d1564000c0301e02c3c10003005511840018030403800c56080c400e800c3c5800040340e800000f00c2c1140c0b20b04800d80001407009042c0b5070300042402043c0d40d03240030b071001010300c400010741080450100800014a402480d07000b1410582c09039010040070401e10191404c11190040603285129202c10400c0181c4094410300d50380c44c1084c0e400d07203c045c02035106070300c01c3d002160b4031880e003018107027110816030001c891648403542d0300000410300f240c0c1d196075800468001c55030b030704c030700170a46c0c014960017211a = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 456702176 1250 456700926 456700939
    0x20a050307050a020a05041a01030c1103040e100b030408031303090306050a0c0305090316170903010905071703120109020c010e0106090e061b250c0f0e150f010507020609 75
    0x9070700300328000800c030001920a88100701c91075039030307010300c8207583d0040c5418201c14a0300103410070651203540064200c00303880c60301d024044a00f0500c40c1c19a4000d400205240c00ea43c1c4c01c2100360402c0344185c5000f00801c00455103076282a403102503841c0400b170086241c4008040315981414820080c42703020310380140d02013013681441450360b001040403556020100b421f081c0080e1042d0004000d80c1d0301003072907556494010040b03039525142d088613400c0f800000d1805105c0250651424810284081d12803001021220f043c403541445520403000c403080558410407003d00343c1a030300300075141101c184010150701c5080540c800c501500d02095500042c2d80303030080c00100346a150b000448009840c0007964020f403500e0301240a0b81102c006000001681041900e85e010b052400030079115480260424261529a507442182c208943c00001da584c5c158006000da500000d402c990012a6a0b594060044288001c00d5513031102c5040e80c1e0520001240e03400c25074070745038100c0d0b0000c003000304034 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 456703426 1250 456702176 456702187
    0x30b09030f042c0a0608010b1e061e0406032a021525050d0f0203040c140604030501060b0d0e0d0c260403081b19060203041104050403080601030e030424020a0503 71
    0x1c4e03078001e100ca8440c1a80660800f40001c915007410100e24135008860880c0c0c03c3c01030343d2801031004aa014100022804940250280311020318001400162081d40d0b00400c2c1e1012043c01c00701b03400c40c142042e032149210072035400c0c042074001409400301007a00541424aa403003001c4202c22a0320001745240c00d14544150700d44480d4400000c00202c00d40844c05c0254076000031301e542c101d010866000f001110800010701c030310407660152003001840140003c0c94651030380d84076400d442d481c0d44004070006020071100d2985903903028412100803404020319107030f280c15100a0410381805006469211008040d006550100d036090115940b98206140e440b0b5491074025042c0d4000e19034070040300c4200880400300352020494200c4900940044000b166031a104c3c10300945c00500300321a42c0030044070088154655010b404d04c160f000e0f440385040c03854568000360540d40d425900075850342041100b444005942088024181c030b007143e640c200c0f000802c000303078a03004000c800030b0824400440c9 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 456704676 1250 456703426 456703441
    0x50702030f0616020d1b1b0b03011d06130c020325020a080706020a032604080c10050112030e04090f0c030c05030a0f030e0a0e10030b09030f042c 64
    0x1d990b030040c0300c40320994600303c007280412619a01400070400008643c0240c0401340b189181c50042a1030050260300d400c002080ca04200b00c110340d03482030b11010404401003000c000c8403c0688900455896260039900d841000944080201c81c4208a5103907507082c0b85220300e1080082d9402050100841c44001075400d08041450706020307c200d10405031450082084140070030f00c01d0460f0760903001043d40045641c2d0548050030094000e004040c1c1d0300090480351070340251014007841c080c21446541d10061909281030103911610f00400c1b90030180104190030840c1c5e0381c0f00f00950145807145c40e1640d101d00080c0600b400b01c04c054582c00304074546c0414441c1150101045a11591031214220f54078001e06403641c102003805000d1001600207900400d006041910a50a004000c5242c0350b0312111904813000c1c0c1542c0c1c02c0c42340d0103402c03024810001c0300b03410030f9000304810008504080444600c54410305c20f9010304445051000e80c4c8207178094031146100242c001503418130035903103000300 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 456705926 1250 456704676 456704683
    0xf03060d060b0a260c100f120c050c0f12031b040305011103070801091b0c14010518120f04210b09011a010e150f040503030d0c080601080c0a030c050702030f 69
    0x1130b03400c6039509512119000004001900303240c0b414000c1d104101a1040700e409941d80da84a0b1000d1081c0070441c80217070b1300051544182003070a401e58591a403509424503e992a0074142d001400c982d902004900454000c003505407070380301c001480f1100000d101030030203e034a40242d40c8001c00039824a90441401c07000700c00510f21443c03080c3c2d07488005a90710b02c07000040e91540384125640c107030307024041c0c098540f040000d080614004d95003040c6110611840e10700311981202c01c50040c4000042c103080c07080c030a03c4540c5180c281d1103602130034850b00b40b0180002e4421441356800d100e031b42e403115042200400f9955007945070040004503aa02d0000d22040c003800c218070303048234051092064800c4c0340d8007482c203003503c4580180c920060311a0490030104154010080c0e840030110a00c0001003c8d0b07802c100500a507101100c0204501062131009001000003030b0200c0c1c10f0121501c1001101810030003074600b420394900e0301184052103090300756200d1182441c0030b500760080100701d0111f4407000 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 456707176 1250 456705926 456705959
    0x50a03050d180f03020418021018091104090c020a0506101503050f1602011806230103030f050f090d0813081207140f0607020d030605060f03060d060b0a 67
    0x40d141c900b102c0a42555601485000740038084881003480000d201504081e400304040d61040180300c10100400e0b0001030816448400c0d003c0000c6102032090142c200300c402450081410000070f001e520590608107a4501903030084800480e5034040c60f001c0c040c800c200c0c808049070440241c0e05c00c2d0406216140f0306040c60301034903d01081001d44481c0c0188039210b41840f40c881c0c05641c510390784402e4400c0444d0417080c2032030000c640d20750141c038070844941c400034a03940d442014000b507814a8101315100b40095000301d101c070303a60844010030201e500403120a44040452509030381e21241080a9038003400707003118040c2c00c02041c2204000b00700c460402022258610400c10030030b655a081000e5a8606181e031510140d10144102e0b0700144000c0303c036500c0a0f40c44c20507204d48421012416161080032990303034006078850001d0020300768151041201500080d16410701d480a07100c400502484060715890240500c180c6400034400320f903000038401c18000340045d0803203907221000c14421004 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 456708426 1250 456707176 456707203
    0x61401060f14030f010603090204110a0e0f10140c0102190306050f040501032303121312050c0a0b0c1902100f140402060702010219061a06180f0307050a0305 69
    0x8620604a000c0ca032065074400c4d021910204201c5e82800011009401d6070325040b81c20030340382c5503582005440c03036010b00b26205080e03503123039154000b040801c0074411200020324010325024410080440e40a03c0f004092007400e40275a40d1044803400881c02841203982c0e040c4c0318405006200d42055164000404452041340c076080c40041900400c02215028400100803840d5149441e0110740c100a845020752038440589081c001c00c403403190304030003040300d508403d21031510004080280326007a50380840450301c2c04a09000350028460750314840d500019041806520028501c108080c040715650f0254000d2701d4940c0618000c0a590381e15007440035100c080c14080c3c1c02110744003a00c2583d110034840c0003c40c0311511540c0a11280d68040c4500383c1c1180201c0c4c001c4460380c080c64180126070391140741c0006801b04000d56000590307a40c02c40807031182008010341c1d03224000c5440704035044841181d440302803203541c80000740f50044c194080307500082d0802000007403080126214411515 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 456709676 1250 456708426 456708437
    0x30606020d0c060f0e07090e1603052d0d11060105010c0f0602031b03160e010503150f030c030d0504090507180303140d020c0a060b030102091c061401060f 68
    0x88580050307895900c22105140000c8021001c1c00c0403a400360040030032010310803400101c00400e0000203051096079040190010b0719a05601180042008030010108100035290000750655880c541c0710598660030300e400c400d810312454940352460307600841c4403285100320740811096a0010341403440c11002d10100e8002c013030001440754080d6000300340c0c080d40034646140b1044c07540c1d6100025000688210034416020030801c0700d1965000046000310550320143d40e20907540305004010000c80e9203d00d042041c10300c01d001c3e11206a4070300c8003403103408036113000c80d54040f5404a0301e042080da048641c0342c810030301d948890f40c1e04040144103440c2503d01c00d00c1140e459180c10b984403100a901ca802d2400d40d80001c10211748990348800d00101361485003407625095140d04c50903a041002400f00940012014100308450ba01c0383e4400d040060307000b98140201e007030009070980980b5a400703100c011203503980f404000555001411400c0004001401c5503140d80004100b02e0540e00c00a01146 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 456710926 1250 456709676 456709679
    0x180405100c0c060e1509070306050702010b010c0b091c0f020f19080a090b070c0503060a0e0607050a11010f0519050f070c0203031b030918061807110a05030a0306 71
    0x402078012403140310354a840d520341e006819580e01c001010000300c0300c402400392034201144113844200b090701448010000305115070850402d0800c072032000d40a5800c0d07a240980006072a600101000c100c0381e00080700e5031180c3d40d901119410401e003a110f80411560807405001c485400551030b0035101c0b0b099088811b6000003510082d600e141103100c0000090031146810006031011000303001c00310903031501c40c04607175640310340b0343c0310f03400c0504100d0349504010400e00c071a0038200100360b44040303600310500c512090852351945030440900014104080060a4502d141c0200100811030030458000c0000720180986100103200940c3c0d140301d605200d501241d00754030640612400703519605030403170f8541c079120303000d850b1021440400c1781c05000c144807007904c2c6425800040d0081d0340980c069a501d4034440708201c1484030174400c20610820841c240005a120f11942c900c900c85e03140860f490036102d0090540f500e1806410540041c8100d128000400030080040e0151a41585040c0b005d01d = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 456712176 1250 456710926 456710953
    0x60f121f1a01080f0c071e1217070906050915031905091f0b01140d0f050604180b04030e0604032d32030a050301080c040b0a0b1305180405 61
    0x1450035600013182ea00c4500200d1400c0c1e6044004094041c440d01001c0c1d400000301203d50b002c0d245110003aa83d00c01c02c11014503400e500304900a034104e400c00200150703807070040c0002d0440105409080100107020911008a0303c84c440140e1201d0100e20340e403500c91800071010f01d006031072840b5003190a0309040120341700020025001050a81388440d13210194159005040180700c240f1490b810040d503c400090302030000c3c4d00900a04848420202d500050514154159280544400c0c00382e480d03c1c200301d0303c0e40a09004001519884076000325241c44034241210b03150407802500703a020000050010400c0b40d0402000320040130301e000c1d21602027880410619450282001910b420301c40840e5050008554070207a40b5518000c000400f454900c2202a1454001c001c0032400300b40c0000042c058484d081140e0344d03c2060488050007100d106402040b1031001500c11003010800105400b140c0c0380c0881004030207400080c00c900c0610000070301e410002841500c059420f0b016105202ca001c = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 456713426 1250 456712176 456712187
    0xf080c120a0803010b0c10090b0a0b031629191409131d0708070e01240c05150c0301030209090f07050d03021608160806060f121f1a01 59
    0x54220340d4243c15a86401d40b425025800541d01080d140070700e01010340005154402c42140034007941c49250036180c0740204c0c0c4225034116418601c00d0b803140c100c24110440440c024020343d030300d445a0035848170102000c001600d07040d103c0c2010190780401d01c5070003070b80c0701a6808040341183e81c42612030b0450120342c0d25039100310482103800080180340701c0d0701c0345000d8221b058160341c132413005200408503116490422129401820280c0c220342010020f803228140b046000d0704541041030030140d02c400f81c0c4200c1222044c02142030122030401303141404401c0c01115030300b656034030004687c3c2c03411401c482c1c0719a00c00d0004a1041c030130300021500d5031100103084010410b43c0c40007400f520303084c10200501030002c03071800c504501c1400100b1003140e1007401104020301e40d517001004034100480414909003c40e0304203407060761101c0100400d541c2c4041e03c8191407031003070703803051040440360101d113042c908080c0d0b194200b28546001d0584d201087e034801c9000b201012201828102020f0044a0 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 456714676 1250 456713426 456713443
    0x6030305040e060105070204110a020f1507030c12050a020d0c02010e0a080f04050a0807140303070b0115031103090607110a0f02060f070507080c09070305070c0f05070f080c12 77
    0x14020701050001c04026081d4541008050400d81d0801e41140d00181c195200342c0c800d03c4406902040401000390100003690b00e040904000d400c1200003501c194801c908010090300030161a1408a00b01d9170044a5514000c150310a0520240c07400004510113507000300500e0000c1807900441d071501510602c62100006454406005640b05039118075145070049001c10080c1041080009441e81d41c041e1a0001004601c014051582c40d02420304141c880074841c45010b5001080030380006003402550b070b8103690340c15103003140c0000181d4048005140c9580210b40c80c842c0001807000d1000005821481000c075580c5000140c032080c0d841c43d803603a17402c00000b03019203107052890300185003002c080e1402d0146a04c400e0700b488140d0f15030a14150807940405001d8110011001e8542010040c1030340c400d015080501c898201100300800c49900000007502800c03081d54081c04101c000c0c0000002822603032503031070025807244c403a04e841c2e08201d4841480f90f40202009494910702050481 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 456715926 1250 456714676 456714683
    0x90c06030f040b06010905060703030b03010c080112060e0a020d030c0203060c0f0d0209030109050303010609060e06030408090906190627120219051c11120c010f14041509090603 78
    0x5899441da43e4a01050007406042d039410f1110200d8042882c0d140e203400f8111b000d00a41d0007041401003841850308454005041c1c2c401c00030300500500242100e000520b5000740e102e000000c182200c0303901d660901810082c020341c44800f10440c442031503444a00400240d008a050700d00d1394a4894002020b8482e0b0520526160030030b120881d614455030b0b010f000785541c0580041072000c2103903141400c5620903001b08020500004040c007809a112003050b400c3e007025503015255003071980b00c0f030040b4001c0d040d50620400103a00002c91a80350654a00695110014010344040d182c02d0003070034a144030700706501c03a5450810614541c0c7c580c2d44160080302c401002c1e5a0466995400f4856442403c601d581c001c100000400500d9455030100d01203404007103640000003800c145000d01015508005451003412001d41030b011340d40000ca9178040400003420070001e41108801c050300d00c0c008988002d02c1440380410001009220007440b500c1d83c030b040c0d83e1a00710b015112600401103505601024 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 456717176 1250 456715926 456715951
    0x1b0b120619170c0402040801020c070b0903060c031315021801391b03020f0102010207120516020603160206010f03120305040c0513060509011a031b0f0c0303090c0603 73
    0x1c1159500b8401100b07031030324540c810b0758804004500890306aa103e80e00050307280e0750008101002d00c0341480850042d03c9014811468802c20100283d036403a4083d0418400800c00000720b4004000c4140c9516081e901a10300b402850300b0081c0d40c00250040e800001305000c11340150505503200c0c01d0700032504d20a1201c0d404109102e1000a0341c1c030088446a001c0710307400e1003288008a8860404d00c00c600341650f1038601c4680c06e610501810b1445520a90f056a005020510000310182c03580021300889103000c503202d07500e18201d45c0a20088001c0650055000000e0094026407000b1110030319001e502141e642d079030395040c0c201120199102c00f0703014007912129008251b1003a040503400a0062043c1070303803a03032140009800b0210304400c00b2142c540c1c80318200301504203012040d004001c4081aa6035141c075015040f075461000600b1f28040000c5941e0342030004030072000f41c5400c00402e20780d40740c4440b0705410b1725540780e0040d21607040303610503039403080054606103080b00e02c542d0003a00903 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 456718426 1250 456717176 456717179
    0x120e010c050a200a1202010e06030c22050a0608060405090d0206160504170a0302101505040b0d0602040303080405010f06060c030315030813060e12030906071b0b120619 74
    0x91503403000801d0581035198192401100555640c3c503128005011100502221880c0c1742c8000b51100800440e442d025210501c100058004154180c503100b06070b8003194a065145c00240014485a0fa00032960106a101001c69925030000d0541d11400742030303800304100e4079900641c40c2d441c0b04428045005a001c4000101443d510a0301800150542d04000f4205911a0303584090040e190346006916440101c16100707040c0e041124110020702100b0412080746680d00c8981110612300415014540300c1200100d070f51180e040e2005c0440d04040119200c0c0d4503451700a08103442a00c05441a608042c04e00b2003110061040307d084070076948032600402481e5600350040c01c0e42010032003d00ba114040000410645401440f9140081e5200d0380d00c0c6080c9440a031200400021300c0380503e0740340000d60240e00d0000219440342d02c00f140c001d03403262801d00d4125144c000d1007d09001c031601a4400092260800f009424a16016051090346030317200d200303229241c40302c500100c8000c62175000 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 456719676 1250 456718426 456718433
    0x2030705150906030a05070f0c030806120703151b020c0303120c1204150c020c0616051e07060909051302040203060103020c06150108070c1a07030216120e010c050a 72
    0x40c0002004851600700d051804000c00141c0070b0b0001c0314000f0b078460300c0b00100441c00d54011180003c0c1540383c24144180c20b0207841c020405040104401d0044508000034401c03c10100310280c000c50340080e45c00100c0a4014965010b03000343c108000198088240016089002182c4114410400f8004608000d4900d4404081b050301078002c00b20300108110940250312034003442d6200b0b0f40500048000761100301910341c00c031502c0080e59411904142f4109500f55180d2003102d401a41c10102950414203500305941005640e44104149540140f01042e409401040800441d180c980780d04541507560603004040c0d500c00c0306c0ca4541d41c800c80b45048010f01e40356000d03581010040c5401410803280405003803812506880d01c270b4214407007003801d184035a481002c0a40c440158035081803100c684d40c0d01d401c2c600c00c01386144000245568001075019100303a040d00c010040d114007640390380e4414208002035a1007803401000080580790415555402903147c101d400b640000144402411178a = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 456720926 1250 456719676 456719689
    0x5160812030a150e100e011509030f05191a0f06030a0201120e031c0f020c0318010c1a1801050c1b0c04050405030307030b2b150e030909010803040302030705 69
    0x8080d90301c1515440008604c25040d00d1072984181d2480f018000c0355410a003d086824034140d000940c003885046950b0a4540d005541c001120360009102150f00310902d03100341051040d5040c0f00c2c0c00c0018012002c14406258881441c16541001c915841c3d100d0098030302150b9011603985400d640017000000065204044001c81413070f402c2c400007131901c01400601c0c01c6900c4000342c0c0200c2040e84c520100221194421f8604c4203000c0c4038110710b030080d10242d40d516405007148000c00c0c45400780800d041a409200c140c0304d902d034400c0f65141422201450050002c506590300a4040388401000200300014803416000316034041c011410014040c81181c0010a03040700f1020a00440c411411107071514000c0340d020f948100003860301e915126800404171072540b800180700381d10f034401690b1010700581c4030342000c0900350200104400345041880303d007841c41c5801c54043d403911201100074000070000d441102021640c2404d50b90340c4904180e41ca004c1d07404040d5158003e510104414580203 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 456722176 1250 456720926 456720941
    0x30070315140a08070909170a0804030507060b0306070507200906190f0306201303060b012601170a05030a1116030303020a0f1803020108060102031605160812030a 71
    0x100782c0c500b140d843e40c0f0014103100c450307804100401c2d103540d050020000300c401c64070381480c40306011030b051103003400004003400e101900241c14484001380b40000d02c90240c00000311880b010703088902c941041d400c010400e6000c0b10007600c1d0b5101700640490785000600c0040c00d0303004018a109216103510341000301e210244240403181303807030000703002541440c41050000154021003000501e000c1506105012404c003440c1e210408900708400408000703a403018000f40d0342c10202c0020582a1103006031100701e0286601d244194a50718a0601c0b60070083c10181610003a000281244071903040c3c07507070750b403007540d20080081e0000e00c1034a0f0f0355032040d0059100300e01080121070074034003404156100c0740c103d07800540c00a5000035101d418107070403058010340c41d02c41e45485904903034003800001d880103881c00003c0c104002c600c04078105030710800c103a43c50050000d03400d42c102c2c0340d18034245941e00004d02d418403021124200028094201040389804c50510201042c61541c40c104d0010041c02c50 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 456723426 1250 456722176 456722179
    0xc100b06070b040813061103040612270501110a120e0718020a0e0d11040c270f0801111e040b0726090a03020609063007031514 56
    0x1800100085004840d02c2402603003c0d02c0c280d55650070051045400d14400d8100400340001c08408002c2c00c07800100315800c03146246820584002841d25940141406841c03c0b80d0400c07a40180010702d00d0f41c5481c65680f0342c4194003c100c3d14002a0410900e4081c9844040c0480e0342c6c400c0741c40303051a40d07410840414200b03a05941c1541d40750134802550340e0340c501440003500da011644c0c0c81740940120150100034011503451600f00750f1070b902d801c7c00c0201088014026500c0b50044102c4a000341070401c90390480404c80e03100c1480c494100c120201413031080300700301c01403020700251459042c030039280f0070350703c1c103926526100d10079080440a0340c1e0f180e41c11490043c00c21000580d403c000f009010134031300c1142c1d4007040b600030a6621200f12001072000002000420184d4400d03a103002c0700e80c1c11242d041c0c0d0030648420410f80000c46038046c1c0c02c0301000c5d11030350007100400b0b0554031580c1a03a90340400c0040015840300d0104900b100d864040b124290404030398144404d480d180c04001c400c200 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 456724676 1250 456723426 456723439
    0xb070b090f070e040c050103050c041716140405130218130210030f0c0207050102060711100f09030219082a070611102a02070b030106020a0b06060c100b 67
    0x8803000807902e4405203500c86081c07006007009100421091050b800700401d02481c041c00b01d400e168515410512440c40f41603d00c01041b15128903c04d010301074840d061080300482120355a4601042010070740284007503100f036180c4000500303810350306880f10074000e801078400341c24400c064180c6103d00c80c02801c02d550410b0380c802484016603920010400d903803035655000c00e2110003c2c484030251501c000d0800150b401c0000c0c00d0006990010300e13142e02c10841e10340303681401000d50040382090586829140c4890911030f130700d0100305440d008070f60740511036800c4440100c0402c22514202940603130050182c5010458a42200619190441071b00d88080c0500c0c0c90041c00044245032a070280d01074808203020340300c40b500300345040c41800700c1c01c0c0f030100013807052190148400c0c811852084140703905040401c14000040e10800950000e00800c0398034a59950719242c010b50790b0030820100b2158841c801002a400381000025135401c2c8862070024061107003e00c0105000d4001903c4940d0080c1 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 456725926 1250 456724676 456724693
    0xa02030f0a0e04050c18040b0a05061204030f0c030210021c0e0106080c0f090612070f0e0912070b04060b190603020403050c03030c0a1e0b0c0c01150b070b09 69
    0x303005100030105151503444258507116802d06000c1a14002011400040d9052000f0096900640c1c000c8100e00c10859000a802d1071410004e0140265a04169001440840c1b9981c101038070f0440c86008501036116407104002c0501d00710303580f90400c40f000700140c01005809220040c9a009810941ca982c666000080c4540b0408030840f94010350480507a9141d0100b0000f5503402e0149103c002000d40d88903800280303402c080703880048044c5c090740c040e00e10710707005480080c0c09000e94406000860101c1014599a128403415520140c8000616000c2c41d4191100b02507000c040f640e509622135601c1d1010395540e120600100060384100d600619025110980d40550f0170703c04c000b074403164070700580300c80c00c0d400c09619001f00c005695010794000c000d40da0b12824001600c20b9a0707603102034101c1d0300c126408040790710710200c5240100381d160343c4003e2000000c00103016200001000c0e000704010740410f804d40b2078064551203107004001c0100031160200e0f0148500c0f507400507200302120400e0 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 456727176 1250 456725926 456725947
    0x20071a0309010f090813050103050106140319090f0c050f10050d15081011030903040317070807110f040603120c0c0f030606050a0801060e0f070c141f1404080a0203 72
    0x1d401d0300004445c5141c0000e11032640100c01c1c00400064042840e0401c155814402e0140804d00302d18181000410044001283e114110803607010540c40c09109001c6000103250807a030f050b200100413508119440c0b008200b17402c0a09400b110b4200003002802c0f03625510106640540c007490b00340d2643c030740f100101c10400440401c42001007070400021f0211151264800e001c45035603800e0f00c071503803000700140301030140d0001c2074900b940d400c031004c003002c00404842c6640b80d10800340c00510880001c03400c4024864000c00050b03030070030305488940c0c128950000300b0045034003600000f0100c84900d00e18544032072140c50303202842c620800e09100c400d07403a01e0b100e00024030a9071040b100c813034a803441801141000c4500d900109000750007800424100503210345c01400c002c160345610380340480041c034903611414601074a207400c58010300b040c26610088544922002c44101310380800c50b2a2860500124402c0103044501c16514160766103640d82e811081d90b004540c5101140310034030501c40300 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 456728426 1250 456727176 456727181
    0x406020705190c080d02010b13020a09030c090902120a051005190501031b0f06021c030615020106080d0c05120307022b0314010506031b0c010204030320071a0309010f 73
    0x140e40606008102c19181030051490005c100c28036004590502c51401141d8580030007d4401c43e00500c00035842d11040a0116040036003070380f015094030703000385000070749402c240e00170031045000b034504120280c458080560784044804004050b5031040c18410505265a803149401890212415070314080c07200021081d12400c1e0802e4030f050702004880c134035441d16604c2c1c40c00281510f240e000500c6240c81c10180d00c803191102c541003e050b560201c00c2143c2d2096002102400c045e001d0010b9000418074001e000708858000c100741842403400c40000d690042400755003665104000b0b0000c00c0c0107120035900c0340c0002d0300d40300561149c0e04007050300201038041080c5142901240f01d4015444a0004047d00c0c481c0c00750003035001b601e10042c05141c890300122907000e044c1003216100301e000d0640b50341c1c00e803040c01e00c001a40e51010401004140e0710407604046044801e45101301220351245c140e0712242a4441e991302e030440404c0400301082c070003020b940e204880c0800054808600c8604005 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 456729676 1250 456728426 456728473
    0xb1c05042a05180609010b09010219080a02100b10031d011404050d0c0317090a060f060509060609101107050a06050909090d0527030109060b090f06090406020705 71
    0x140c1c4604a0700900840c02c10800c680304070f20b09806481d08a04010340425611003043c09070180c204800244840181d000b00815944401d41a100300c40b0284141000503031a00009245c1e0018001c0d40426005070055000782400020700030164026800d0f160b409500400b001140783d1100c1400e989200c90f100400e206150a409190419102d14030741407912504000b16100707031006100c00394210703d010982c0901d1541c2406260402c80c809034035010019481c0100002c40103051909020302000d00f0490b580101c81214815104005a034407a0010000c560003444030054000c99010080303001248140f0901c89100707489825903061944030740200305021030580210000c1240003ca0220b2030916060240c2d015800001408210b00e5144008125125903181501c4400800f41f00e030440304206400705859080041c02040400303070034034109002d00084000c062154480390700041c04020f8890a081c420389004083c8610b6039210758449000b07400c1104140e40740e00c02e012404440c195548460750 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 456730926 1250 456729676 456729743
    0x60c010501080d03090309170a05010e0c130b030a080a0516060203150102060906041112030d1d0304060215040c08030c0a0507140d060e031e040501090b1c0504 70
    0x3141d604005805282000c06110034080610b040e8000300131035804070140d01601d528400b070100b907520039171000d4a480c40f2800e000e05554039090302400018000150403200c1802030b92182d4001d02261950b004880b612074201d600754006c5c2d0182c0303000954540c0100034070030890500a00b0020303498040b0b130300315040b40380445013158004280410600041d450400703281d800d2000b04140e140803c2c031f5039201d07403025000414100c00030006581c81d6031981c0c800c1044240071004c983d1500703020b1000c070300a030848021280303e04004611850ba95000881200e0a0b600681c00416261501e1120903a9102d00100706030b0f03c4101d13201002c21140410f02c010b1882e0b0100000901e07554045003003c0c2e081c0710300d40e0b008981050316031240842130b031107002e411500c0e00d410210004500107040c0e04541140314060380d000003006041c0306101480c0d031060180058480170390700d0100e51526902090180e01c2602d820f2500080f100365000c0c400512034000c0b9500a02c10111160018543c0e80d0780d04c030740748031003034000c = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 456732176 1250 456730926 456730931
    0x7021f020703030b04050103081605030d0c0201090b130b0c09010c0c03030305060a2301140c1504150b0a0b0a090b0d021e030105210a080a030e0d02010c050f0d0b060c01 74
    0x5000e02d80e050043c400d804208445c10000c82d4511750709c0c0e600910544491503040c204060034142405014010b9402c0000c4440081c00500000c00c0002d00030000c180046500b00101400300b00080316984a0014084c0c0c0100941003d4071005241a42c80e0080502d0740e0401100b035003100001400003852000a43c800e860109c0d03107043c000f040180016581c4c1019004403032000084100d8811080b6170f0600d8442030a11721015940281d42031a5485004240411482000060751444445c01030242c4500e010341480d0b5402018450000c4c140e5540c0f00c5255800318aa080a0082103041c1c00100884449414900385480c1d4400e0007040a40001400401c401d5020034000d2515440080300e540c0b180e0320404945c80c540c14500050394140702d02c040c0d965104180d10b8654036071481001000b40301034010101c81d451300001350009001e8840e002c19410240103021550301440d005004040122505882e414205107000f84001e2039904503440e0f00980d1500c0e946c0d024415201d1000030a4800040c0002 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 456733426 1250 456732176 456732187
    0x30b2214010507020c01120b04021308150a020a090506030a09061b170408160c12060f1a010e01080703110c070302041104030f080307090312080412050f03040b07021f02 74
    0x9003140e40082c0340c1c9040d5009070507200c6242c1c1e445080002c400d0803007d400920645010702241c02400303190031503080c401130364a01090785074000403001010241407420500c1a6141c00000b000c7c0d0069075080c1001c100038003020f00c1203140607000b4642c8114810f80010f05015151140d20503280011030300480311415030b40e510103059109110382c0c440000c041e480d00e80350900d0f6641100c10711500300c000c41c5c454080c2c544002000402020000100b00d054180740d450110b6040c10700052048503000c03502c0915000c4c0d080024085801c100c40080c10503120401010004c4d0300644d0044c4d0000d1075041010380c0c80c1c0d80380c441255020301601c4441084070003414400d0451052104580b41c016004040d07210034401000010b02d030504c0104190380c0030082588a40307803030405490340345098000400c290a070103891010140d00001c440d204071300036096014540801d46040c0c81600c04c440004c8084282040020040350001003c190801200c0c03049810304240c8a4104d001e2682440e02c40340e10980002d007 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 456734676 1250 456733426 456733463
    0x304150911100f080a0b0f030337021903091a0405030708030f0703030903140403080d05010b040530070b0c071e03110406031b1703090901030b22 64
    0x80d410b0045a0360500f00c09a4036001c40152424100800c20b0f8082c94a54101c46000d40392040c0408450300068226615114000e0010784c81001c080c0d2500c3c051a00031442031420101004004800c001c6500a0111040c0e040b22101c0c0001400d0b80c26020b010712244002440c0c0745410109103a10345811091340c403542807204050070b0042d41d07404402c45501c280920302c081c8040c0c01c100c80301d00b5414140020214500e2500780c2d041250040108034005002c20004140586000200381c4011441000c2040340c0e00c034196000c0a00880c01140c1d0441e000702c81c0c264013a103692200012440c040c2a82c2628800d800d002c90303140030038507040400160001300307050120074020008400642440a450a140f00103000025480c00d60340c80090b00c0c0001c68145944d180d102d61f40188091504a08120388040114071940b5814220340303d0400da05420040c880003019000c01074944c17807440102141c40a0b480d5490700000b00d580076281c4000c400700c0760f043c86110080c0c000108401c41c840c3e002d1208400040c070 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 456735926 1250 456734676 456734689
    0xc0c080c0a03110105010e010e18070e01050f0d03051c02280f0e1f110a030f11061b0307050f030901090614090a060f06030206130816030b010b0304150911 68
    0x3c05803880ea81404018000014912921030540314451440d03000c50782c503201c45a07290030f02451030022500030880c0118259800040c01c5050f01c1b015140c2c0304c0c107d4641d8082c00108081a000640018400c9c00762404107641c503901440100d01d8600003504240d8022921044200c03a54140c028000b070b4803d8a07407006805c500864020791031424803260703180c1623901040f00a072140c044d4655041148040c041181e000c1c200103c02a14403000b192024071030361502400030240d65050001046514001407104c8800040d0503200300307400070710303500c8589015000218a0708054030300c9040c440280400c1022239a4007020b14440e08413040007007054081414041c00300c80c007130726515200891400411023561300c0010742070182903100c2d20000c2c00d070024182000007003c10f900002e6200c04005684006007540b000e0030300565951401751070000c8441c0c14011109010780c03000404203900c1c1001000400310301d001450307001e0300449040d00e4990758504032004442d50410116480909030021086030705244 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 456737176 1250 456735926 456735947
    0xa1805012405330d09120216081b03030715090b0a0e031c180606090f0507020a06021305131a0303130e0615030910050615030a0c0c080c0a03 62
    0x2034030003101550955a0f803c04200b403c01d4000900040f03880c02c0c521221584044481600c20a03808015007850707032030444e005034242c900030701c0140f1800300c2000b0f480c20b0b91a01e1104581540001f03020000e0303644c01c40316101e100e1010b003a070300d80000d1041c200410b041c1000040072002c00000041c00010038035242407100e801600400c074030761501c0e12101c21074100000319a842c5c0c5944042e6807040750781c01c0c0074602030511080711070141d00101f1201020040c090300004c0c140c8044403028403407108007400f000d04442c0220f9440740103900903034024000c43c020b6030062500c810110a11209691103501007503002c06084e04005810741d07580c800440c1d10748504460641107000300c01441c90090ba49036000c0da58501405202d240084042c00b0503582d60b2580462010003500034417171903c038034000201d50f4580300300c119041c11160400300010b04526260310560010310250039102d0031a20703003402c1c41004052100264040c00000900000070075030324009404103010510052180d00300c40d02d401025030401 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 456738426 1250 456737176 456737179
    0x30c03060e040305070203010f0c030c020c030c06040b22060c051504030918020d05160f0c0203031905130905100906050a06030905030d05131403120a1805012405 71
    0x40c0541400301094680025401507094a0071030307110811400040c0c014225240032805207407810800b40c18454250704441c0112084d5020344d81114060400e06444043d88130720340354440e06c101300a03c0740c1210b582c09883c4071151141001c141d124410440f242c2d03520940c2000380400d43c02180102044810004604075003410400d00b5001d0a1644d0040e20264860082c4400002070000c3c405241625506694040203d000240400d0501300750340e0107440600c030032200008a80d80045801c440c01460007618441d8058002e603e002d0800c6100b8001c030b9120341c40c51003040400c120384c181e6a0300e4540070308060141100d000443c1e040c407014000751040150300c0041d113503080150402c925a80c0d01c943d98100c1e6450304002ca10300b4554900281584582c015480c2450b08d0a0140b0080d6079000991400c028401c4101e0104a108803500340d40d01e02803501880c3c04584c4a80019081d85c04030303003049a0b0030440c80125445a07d032075807580e0030341c0c00303215040300e48001000840000031141816a40103010 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 456739676 1250 456738426 456738431
    0x70b0d0e0309010905060901050904020711180c1207210c031506020a0f1a0a060f14030615031002070803270d0e0a090504080306130c021b060408030a020d030c03 71
    0x40c0e29001814180c850b101c5d50b8031401000c16880b015901030070442c3d2180c5002007045503101c80a24025410202e0a40310a00400d0303c411181c85110700400a6401212000c42090800c0c01c2511112034400b001001401017241c102d14103814600080004c1404112140300401c10100034900207040b20000307c00e551071081250400c0040c2c03a00442c00303070f04941d0464407403000d00d81c1b2030800c0709004a04c0191814a503001c0300400916181c140d0106d020b5400c8030340c3d20407a0964611189100b60200e0a5003a8542c010308041880c11120031010480b00f42c014040c2d542074107090b4420002ca0704100401c0d01d000f9000010410038441180801e4401e0040c42c1c9071030364100349800b40c15500c01441c21010705011080b2034401003995525500c60040001010038061071400d07140138075a039001620641d0080c100e480450040b012107020301c0752494281c2d4004c08900061351005544090600b0141d60014401c02003c2031481d8244001d04c04400c590b00104480071a10318010101da0042820720105032 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 456740926 1250 456739676 456739687
    0x90f010b0607020111121902060c0306180a0e0f0703020103110408030f0a020a4d220c0e0901081b0f01050d0603111c05120318070b0d0e03 61
    0x261050161a111030b021700c0c000a02400d0030080718a40704070000120010329012403004010345000141a011502c554203580940d1541803d1203143d0100740c445642c06003000c0b9412002e60492001e990f8072050038240451445840e0310828203203001c4100c3c01802d5044410280700795601409810300b0380b4030070904145420f142042a80c4c4a0081031003040c0c3c5500c002070a00042031082151040890700201004c01e20030883c5408800c07407840880681d40240024141d00030f8010071042d8940d000c203020b441c2c00c1a100b0300810004041d0411326006409511000401c0b0750b41075901c07801d030400c6200c3d20356850550040081007a0284144c2c4064001d070b102d5014940c40d089203142030850300c1c0c1e007652002c3c44003545000603a8140112041d01108610f003e0001041c01304c00f1402e141410019103501c404030350b54140890341900c0701003000e4550703801094401c03036404005000315403000342418101c00505a1000190400c141984a240e0320b020100d020305068046116920402e80032500662410 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 456742176 1250 456740926 456740929
    0x40c0503090a14070f0806011a0307021c02070e0903030a0605060304030912030e1002100e0307020108010e070509120709050604140f062b060b04020901050d240608090f010b 76
    0x42400d02030007401070485000702c075100328003040803101400c540700e01031741c0043d26103414039a940c0e0244901d1268900116050684400d118102d034000c400b030703901030f08150a140e100e1244112095072240118800d00c00c00080009448a03114051410203025540e24180000c800c0c080d42c5032a00014842c0908009000c0025004880403044a240a134240ba1101603070030203480e860800011260401c9500e1913072080d10781e000c0b0b0340c5c41000e01c0e03e0008104016002c40380e1503aa0080c400003d0202d00320a005020a0002d9818103a220080e45803603403078000a400418407034080c50b070043c000e03644520740911500b5203900506e580901d061f181004500040003103140f400390041d05070b5044a00241c0400d05588030501184070a01181401009042442940120218071108141da400340341102c1c030703c070915140c0211110320070140e64503800c003880310400c0c03002000034100c4a10725151240404210340780c0d151070070004060300d0700c42d24032030700d469031035142850409450344045034505070f0541ca80d07 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 456743426 1250 456742176 456742183
    0x3030609110a08040f050a0609081b030a09090b0402070210020f12030c09040e150907030515091f090f0308010501080a0c091406070501090b070f180605071109010b0306040c050309 79
    0x49170b00b20400015642941c10002e08026103604080c0080d410501c610060081c03aa0007042108848070342c2203c0f4900d1604416101d00444401d0000a42d00e802c0811140c04d15030007211040000410052418255a00040400c1d100030201d20147c3c01801c16404103503010301c00302220039800c4018030301d940f03400c40901e00644507004103030b0b1040341c1c1d03859030301800c0c84104401c0e07514540c03089010045080000300b03641d42e0740c540d210454140c802c1100b98001042c450b030744103010b400d1340b10090084040c40a8183c0040c0081c1c80424040c990b6114440d000c1402c0f00c0314403801c2d5000341c4528903254180b50005000d054000c11580c00c081c140200c03004560ba20409040c01c4030b80031045101030300c02c00000510f561150b000040c280d0b41c05c103801c8105210308602620302811954403142140d9940c1042900c0071482c1a69000b89040428000c201d4136000784018240144291009142c00030003d00242110f0002e8102003d00d4002008014490a0511584007400c0c1d441c108103056140281d41240c0c2d = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 456744676 1250 456743426 456743431
    0x4120201030c3c0302071e0f080a03020315030c13020a050906040b092b0f030c140d0f1b1b0e0103030e03010c090503100e0f010903030609110a08 64
    0x1019910030740e02510381e01c1050070b0840a1619400282c64041c080704600c80b1407000c5992600c0983d42c400303480f6480b8080e108894000c1d41c842c609880320004144403800000202609079003120034543e0040004110100401403440d5541f070041c1c5a04104498001000000040c64000c0e4032441a90141703680b1090500d900e613408038005a981c0d44548011580c50061041c2c4940040c0080380c00f06040c40040060600b20505440b0711009a280f104d07481d81c1c231440c0660b151882d0030000304a00c040717036600c43c03aa1000f500038107285105025590300c4e08206d9400001c1000c2c190401c1301005030701d0b940601010320704000c1d450010081e42c0e00c4105940904030600d0024008a80c24100200f83c14900180c2d030010044850182d00b250703500d040250000040b003400521951a01120b014142d014086170b1042d110050b0050864200140e520030060550071172546c00c51080e091700400300002406201041e510a031740100d1003619044a03002640c0d9404180c1d400b0160610498030b400e40c1c440d01040c0d = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 456745926 1250 456744676 456744679
    0xe03073c0309080705180a111b0105010504050f0609010e04060b1f0216080c060d0914060a05010b040b0301090c1e0c030908010507050f0a0306091416030501080c06091206101703041202 81
    0x58000c8203113422841e00e100740364003027070b030790011003086480381074198800f5040f41c02c01c0c0c600344425a0364202466801d02c0c21258668040042c0b0014000c1020360b03d02e180e4007502c5598001001c0c1041d00015050030500c0b40c40380403180081548000079903040c0609012000280e603402413090070000400d40f91024a0006130050360003045500c5c6610042d00700440c15030b001030303a83c00751a4060568a86448003190b0125010341480000039006054200300e40440340c809650905590a202401c0b001c2c2800c00c0c030b44810848406007040505038a400a81c52084180e15001c00c0031000d460068081403003035005400e1645000104040a43c10008464401c0e240e0362085548030840c0e001580185940e80101c00f506180060303500d0040c4400c50018016070410035204061546200110140e80090050f0055030300203200c41441c604207007000c0c0c003058070028014201c5050718640945010400c40799130990180041d81001407201501e2015110381c03d540285140c5401e00703480d0000c240c060740000307 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 456747176 1250 456745926 456745931
    0x2030d0c03050d02071b08030412122606010216030f02330703091e0306020306220b0f0909060105012102130303030e03073c0309080705180a 62
    0x1001054880c9007220001c3c035040c0340854480c4e10074108040c0740b1074120303e4904014540751011580500c0001610100d640b5426440c181c031107203903551900203003c40240004c0c0120780026030032142c1103103641a120320000506803814038111000915000c1c0302e16039406404144602070020500d41c0d4100c2000c1a016502481040343c00d11a16104812032a0019684810351501c800e09038030305001009154020340c3e0b0307280310540329030b400c031610700e040c1c000c4014402044004000107459900a0b50f03000c04000c0580c40202c010200c10940c0340381080200505940c0c0740d04e080c00c2c6280c00900e00a00103000d59030901d4500d01040f0041d81e542040c05040d041c00200420303805100c07241d1320361905840070100155100c2e500b10511100b654490301080700400e0030f1030304c800c009020010a0b00c0c4010340210031020904520030558000140c01481c50b02088440e03d68448038015031100d1200d21407013641c0b9908030303074075081101c0e0522090390801ca1140410300942890400400c0d05c00d81c005510b41c000 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 456748426 1250 456747176 456747197
    0x610090905061605070b010f0608060927010b061c060e04050a0f05030702100c0201170c091c06110705010e010506060d020d09020909101a01020d11070f09020307020f0a02030d 77
    0x791454000c0c05c600501c16210b450000c92805086900d00d03045130090b0b1501300468844a003004511030080754150008100030494224615a91000c405407046100000401c14602b40200b04a984504082603401d098020101303944181442200c00814076084d0a407002d0030315685590701e46107e06805091030714041094400d101052049a55843d4000d014480d15502254050703c4056488010b074049150300001800e41042d48040034401c0700c201490500d00b40d52714042103503240c1400b585100b800d52149408000030514460441e02c01241c90500382c85117003070b1030401c1c2503030300114007002079034101010f110341c1c7c0d01c610040d6030041005404c05038030f039200300103003400030044078002075802611501840603031b42c80400d00454600c03541000b84903980c80601074046180010380c46a0060380030380c0045020300d119070311380700207404104150b0300c240369260701861500d40150400c0780340b9a800402d000e01d00f5010000d00641050600103420140f400f500001e40b1010b1104181041c040c1d00300b107 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 456749676 1250 456748426 456748471
    0xf03060f07090b0307110f01050403081602070306021201180b15031e0f16030612030c0309170c0a05010315090522050a020f01020604082b0c02061009090506 69
    0x403103801a03c405202141c5034035010200400c1d45400d004001414020b520040500030740c18020b5911440e0161140c4009407070340c80301030559481a001800c02c50185600200c001a941d0004009180c0014a1550f442d41810001807002c1c0702140001581440c1c01c094030400d4841c5804281c2e101c0209103940d0300c0f079541c0e00c041e0204c0709a500540d03d003407a102c0b0030082c0aa40512010303001c0d80f01c0824403010701010000507801c03102c10b4040e201c0740703034259014a00001d100383d0101c3d4202d48280f500c0b00e8419542c3c00c403110480c030240c402209076000402c2c0c9840d141400d06425006042c24030301801401103140d841c0a0032070f118000c1c0741805d034854000442c582c1d840c40035404440d118401301100011942003032901c4180c818402c030311502c41c11940810135807001401600481d0001c01c02d40c50404211906000b440703845070040d903d50028000340c280c541c01da103c0c0170175116194015000610f400750041c600d804035500958411031400c805040400e40005099901000d00d11220849070f204a1 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 456750926 1250 456749676 456749687
    0xf091012021302191d01090512010e060717070e1e150a080f060a0302090f10051305070e011b031b060603120e0f0105070f02130c021b0f03060f07 64
    0x2102c035124000604001c0c040d810920800b2a40140c1c0d40d45000303e0180d00c100704000030380c0b200140c0000c0200c182809503181038051114285c13011000003441c8003240700f0450401204844401c08109035001944460100c4444e1580c40002403034055001650013002072006210031400000d805e40e80b04036292035458007821142e2801c00c600ca0b940e21580c050200800c5c0c200200c1f118448484a000400c805007000000d848c1900c1c0d0040078800c0e141e0340c1b50070a01040c1001028800c044c112503a0006e06a01d030710402c2011901075000104081c508180040d2109401002607030402c50707000424030195100390603c0c09060b41c580341a02485441c0c80c0e07140c00300101c104001d485d031860410004200006040140485800d0b522600340d10040c0c0b8041010003070290b681c1c14007003001000388000003014100040101480105002c03182400880d94800f01e1301542d442c200564004d0481d94407407005914800391480c2d00700d611154505136403011913102c41d40a48a00700c40811a40464021801030 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 456752176 1250 456750926 456750949
    0xc0e04030207081603021207060c0b1918030e01090e0115020309030f2a1e0607060c080702190206040605160501021611090f070813021306050f09101202 67
    0x100495509a412100307000e4030955605c4100e11842c01e50074501800c0b007001c2940400c0300d0094807102e002850f42d0321803e4074001b006140002e036202c102400886103440d44608a01c800d421402043c1801561501a10404500400c2810711489681c1049900b102d05011415156840740c0e03c040041d080c1816807a501600607043d6140c0075040075684000800180e0420390701402c3e00c0707c040007202003d641003030046104c0f41d50300000c05003410403540014102000006074003608140c0b401413107444070011510101004070004580c0c5051200082d8100026400b031044074110381da001280d41d00190b220700c2148103180a00c003000c60100d00000a502c0d0004215410000075035031800e50725061840001850801c5447c17080c2d03508480f5803401c0c4400c80e6803041c101480700e51999202d00c0d10030b80d485c290041c0a542c50301d00e9074403c000161078000007901318800380c40d030100e480390420003040100050400c0d1240a030604103b0044103040d0030401b18111840d51107141c02058613400440d41d80d44d80d2 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 456753426 1250 456752176 456752189
    0x30304030f2109060509042304110901080d17040609021c05060f061c020f06070501061701020a0c0f2603070e01020d0215100302090108031801050301030c0e04030207 73
    0x85035105402e01003160060491021091060300d0800c2d40140c094650094074000c40001401c02e120301422800c1c903a01c6080d50320b0600c90804030206400ca565525030343c0458003101c00700850440454503040441106000d1700000001e0f080320040c1c1b0000034504419208000c214100810109061000580c030140e20140c020300175095900e540300d0041044065508200c8440c4180d20000345210030150049005000c002c09203440784080080002858036500400c1c3d0f805500030350401c4556540d00000c0c01211303c80e00004c240c1c18038141d0b044d420800c1c003a600c03c00d070f40d0041100e244080d92013039804140c650b01c94a1260017007210305044540010744070240e09002c4880060480d150343c0300001c0c5114020a560340c41e800c140f003100480e210380504504c175016074494440301e0000c0b800c1c110301681c04030700d0744041c418680c0e507600010315032442030303001d40095000014038003c10040310308541c0b8030b9102800c0c0a451545142d440729030344003540c0b1961580744010380211b001c0600c24800100142030 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 456754676 1250 456753426 456753443
    0xd0204030b0421140919090c03060e09030a230c010c0518010929070204150303090902040302090703090204021303030206150d08040e180a0b041a0411010e03030403 72
    0x100b524040c020300408492010100440c0d85030300b0f016a2080c044120440c28201e02e0a003011071030000c0c480c0290b0001c401d10084020490007240c10300d1548908204082d491b600400d1191901d41161039070070001d4480e02c40381d00108076141d10241c02c560b196040480d5103048030b44c2500c644140d959140188200e0340110750800025644159100d400b8006540d014040380481c1c07556100155603035122480f4400d4039182c140c48602640040300c24181e0401008003200b880c04100e54001003c89000d010b80d2001d807420700c182441459402480d030340142004810441c902400c40c0c00081407800c2c0103108108140e192001d083c00c548450301614a080440c0b51011101c644a18019403224412100754203101206000c04190b45403580c1041e17002c0d41c00510301443c060a010185800c9072006181344124044403081c2d000c0c9400800900c00001d010389810010f030704040c907050010301d1141c808114180c00c00c1c0d00b40320200301200c02c02d4100c800709081c581c03944210b8030086030850281d5400a0304a45 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 456755926 1250 456754676 456754681
    0x117070903020a080f15070239030f0a020f04111602091b030604090201110303070306080d0c0302031206150738010608040302341a0a050d0204030b 65
    0x642010804055074403c8a111001c2525580e81c142c0e1400886801100d544c008062003040c0780b00b00e46295000030b03070341c03040d503020303a00c0c2c04103895034610410040035200c500d54107401103d501d0407000343c5c0180d8048001d002164024884c003541c9408864019204a244619100c038076610350b448416020175822070035403203420140b41950079007543c10099024074100c3d00014104140075040c1c40c94080110401800c5481e0b8205201c01402014000ca05004a01d094081d80b40410400b440c403415003607801246c3d5034180070322141400c0040c0103031010b20414184444c0001d4020007607580046a41a160010741d8602001440199000d4640c00080d00002170704c40c103018a15080c81c014141d010480300481990050000c440449002e54001c1c5074503d00050201901c90300e0500c0d0064000d104403440e0074a11412000303110781030200102d8248003010b50280e41d00c031600d0304030010b05011914024100f0541c0b03102c441c1d03200d0302100c4c1c07003048000a010152110f036035040c1c0380510340144c4c18204d2031 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 456757176 1250 456755926 456755941
    0x122a0e010803091e060f0702130216031115010e061504120201020c0a0806010501080910060909021c05030306011407080c010203072019030e04050903030a0f0b1e0117 73
    0x7540f102d00400d000743e51680d0301026400800c642071002c2000a0180c6180084590410f0000e17009000220307031101d9030302d128900f07114503400501024180001c14030300ca001e0525000c2c21207040140c0c0790801b50403210700d042000010114140c11100b8a410101280d81e50000041300c0110780450714200b4a8081004181d4520721450842d145200703808541e40402400100300c1150414480c1e1491603100e0401400b0300e510131440c80d80c00200244c100d032050300b504042d00003519102d803c40c40ba02540d07030700e8110651400880f40080603ca484109040480646070140c59100003440c0c6030501140c0003004a040c3c08000c2140c5440350041c0c1d80c10346506402004074041e5006540c07050004600070b000b1820904418403100c200d0843d50001e01032003243e03810601c900c2c03030300600c194140000d10015991546550082d24031660310000595a0b91500b40c8500c030442e0502d440105401d40b9154803105103445ea007644100f0000a90b045c003003141c080c480100d0311900c400380001e030200bc0781130612018 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 456758426 1250 456757176 456757183
    0xf150f10022a0d1b0f09051611060f060d05100f0e03180d030302090301020d09061109011407021f0507061103060d0308040c1205030d06122a0e0108 65
    0xa18000800025665460101e0b5100074026009540c0c484a07080c401e60000e0f91021210115142c88400000500c0e6181c43c10103445005a010a5056031074000704500203441c480d410840c14002d0902031b80d40882011040c1c1d55080081c0700314031909612010501c5039940300c210360006680030003103c003d40d10000d44c603000341403142c0c0c1c4241154245140e030f80c00c280c1c020083d603000b03044502c8040300d2002040104140344810301d1090341410350130403003861291001c0c00100010500e180e03012982c004c01d4640103044400c0e581c110442441c0500001540782e83c82842600030850454074030343c4619041c000695203000b01c032215a1506500026407a800c0c1d0802c0c00340502c240a030104100090110169031050311080301c0c22917000c4003403001440001d015904058001d03000c0c0d030150407801c1d255001401c80c002c5101c0103844e40da0001c1101380320000301d401004090400d8149240f01206580c0d540c0450120b00c842c18030009035000c0219034595070100248005040e2103520702419652050306c2034a = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 456759676 1250 456758426 456758443
    0x100e03012a0c020612060a12050f10061d090f030412030807080403051c0e03030a06170c0607030c0302010e3a0207170a081201050a0e0f150f1002 64
    0x520000c414403032015018003140b0b5440c03a0081c06807440c048a020340500781d080c008100c1944140c00c0c203008500c11204402c0860124890f40c01041e00c0108400268646003090400c40c000c80d080c01418060103281449014810915014000d8251103051a0504045d99051386414502c0049000103940d00784010102000b80241c6500803243c0350360108841c903081c00c842c040c012502c100214078000f01501c3e82c00c88072a4029400003040e821400f065400c503030080d41c11000ba0754070303020107004040504844d81e02c080c102e1001880540c0c8203401143c580c4c02000400703028040c0800f0100c0a05000f03400681d02c080188080c0c60b01544540c1c0000b501030700d20310300b52917500c1040468540c4102c8040c10540006035680041810f10300e0002e032000200ba840b145042d09004440c10b610003e4101805401520650390081d41598140f0050141c480025030010b01c807403002c81c0502a002d0409549182c022560182001c005100a0f000c41d00c0e0002c210f96543d0840e4001015100302c5070f01150f81e51 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 456760926 1250 456759676 456759731
    0x106051e010f030513032703050106051002010b0f0405040f0b040c172b0908030c06041a010f050112090209070c1e030215151512010e01030809100e0301 67
    0x1c840c0e42100c2c0b0200d040703540c111000e2a030400c811507040040790188000503c6107100c5072180c080ca94103840c40d500c04286e25402161541e444140900c604d28060903004114030040c802045842c0003100000d9802030324680d010301807540c5002013002d00291004400c00140c12070700160701420035180c02a2804c15a10400303100300007805525802200100e4200c140d81031107810411100707003010440d032200781c04064010034010b81e002c00141e68242440030b07000c07014080000d040301e80303860b0402003a1400d07a03004844001c545a801031002c071880c0034480068901c01e19011322112030000d00c0e40014940c1d800040d60198614007004006940000410030b00d0344150003500751603240606010b0800c2c400c400080168106d401004283d00e40070030030304d502c4011080200102c5201c040460314900c40034901c101d04d45000a00303800d0b511040e43c3c81c2801801d0b45941c9000079859600d40c0b040d1405620400b9100d0040c07803600d107203c03038840c410010010340020001c1101c0618005560040440400300e003 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 456762176 1250 456760926 456760937
    0x10329030705060405030d110f010e0c031002030c030a09020a0e01091a061e030402131404030801150f0c02040605030709020702030c0a0602120c1f02070501050603061501030c020106051e01 83
    0x842d180c1804000d89048560180c024082809001400c1e02c4000c041030440c8968442c00e030388440c0004003405582c4521048034043c14078100c00e00e0615083c00061611a000c8a004005001180d80c1d4002102c0d0300010040000800412510001340342001341d900c0748035a0000390380045001011940716540b0104142803884040c1010300138040b0314001c01d00d500c4108082200607003058510b01e0021a406440104241c1030902c424002c18200c1d14244800007501418004110400d50404140d40c00f400102c100095854a0b103c002041840c400b0907003410444813110300c1c01152903907001007010b00001810f4405803a216240d2000035004202d00307074800d101ea0b14203031699040c0034641c3c4082d04c0c01e6a000d080103124054078850981e1060841080c580f00d8a1100c072100c01c055000104080b0008502603601c11190806c0303802d41d000131389194840d802c08000c1c0111501d9024542c0400752003820089200702d00c100d01640148911781c4070315045151900d0a804070359a00e440c03400007200907240c6 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 456763426 1250 456762176 456762179
    0x5010801050a0b0a0605091c1a101202060901030912050a0207060509030d030e120c0c010806010305070f0f0512040f0314042123060709060f17060103290307 69
    0x40342c05503080c603480f02e504203010130700603c201c1d03215030004e20512001919020700480440388900181d40c0c10a41a50758640740c00c0d081c3c083c0345001c21804d03000207641504c072014909001d20003030040001d0800074406c039000500146980d00940280c500e00750402c2007822100707100c100140180d0700001b01030005010710b403c003049050089080e6424064080d00030420b0300301d49c43c010b80c014000d10005103183e00c0740c0c030b403001c02d02040c12005040d08013941c4080c02c0507042440c000340080364094040c905040c14070f001c1008942e0f1100407034000030b003186081e040500e10190309491900c0744a90052052040f1300c1000300b031100c3c101d016115544650358030b808001c904684807019014500981c185103800075004450070900840c0070410743e000b1440c5098552070200180c0160111100200003500004108020250495141001004207042c108280d00e04000c004040741350000900700003421500101e08135900c80c2c4d001d120071a03142d00114007070030714490603c1d189840c40398041d4483d2090400 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 456764676 1250 456763426 456763441
    0x17010801090809040b01030e0a030f0e15190e0315041a09030301122f0a051e1201090b011710060308070206030a0906060b1218030a2304090501080105 66
    0x9032800090b08007103128281440c0b807080101410140300824101130300c8880d200603aa078240305c00d5400500c02e84480e5003068045e60b0140031a0041441648503101c1c05003000b404607608001c4030312440c003001c076200a0340111007056502c01100990560144540b000c03502030f40303000070441030060f030240e610b0208004160940082d070040445d0050002d0b0024401000142d41540003204460303c0b403041c01c0064034059400201a1080b400560000142c00e260740c103150820b1103803a07020340300540d54004464480540082c4807004865030900400201090060120303003035100c0b0b810301c0c0e0304ca008a100f03941d60386c1041c24181036850301d4040a004d039400c00101c161084c03117104105ca51060307045003415226020011146c00041c28031403100c0d2034500c040d000600c58031402001d0000d07030a15585800c001c1c100082d25420003410748005440c500c156014443c000010755001c480641781c032890480c8418600711821810b4030450035000e402207400303c1d0100c05608100e050742c08850080285035142707107 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 456765926 1250 456764676 456764681
    0xe01080a060e07030c150203040915090b09062407150c020f0f0d0c080c0a062f0409090201050408060408030f0708040c03030f0509130e0618060a092117010801 70
    0x400100180c045c01c0c0d04010b600004880002100c526005403410155a506010107031021003000d403040b020140003c5c450300d102480b51544514043e9182007c03854036601140140d0031030300c140c030401c1601c017110303040c80f801060448070354650286403540246944400f0402030030001c1c9001025000e407281e4075141ea080000c2040a80a2000040c0840342510301c080d174051664003c1030340e070407804001e0360403212802c10004c00040c0c842c010000711340050169480741c041403850030b10400c90213002008414440c41c0281c1c1d042d100c040c100061203a403e03200507185e45c0f00d144d00100150094008000902c0034071000780d44070300400341400b259035031580022641890b040710020078100c80d014050011038412001015014003900702940f5290480e0009800083c4a01d110070030943c41d0701040f0315090080c000c1d1600105070700484040f00c01e00e01c190646595005000c60a015911a0700406000c58035000301154103c010109140b1010800000c01c5000c1c03400741041a0410f6900000d111903052 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 456767176 1250 456765926 456765929
    0x190f030c0f051507020d080918060415050d2315040c0902030c40080705061e0a02010908070b0a062102040908090423070e010f05130e01080a060e07 65
    0x1104102c0c64481645e00700501030860b1402079842113018010400390740c6071041d100d10640e00b20201d1100c2440e014040006032100810300950300054000c041040d51184c2e0741e50711040d5400585040700d840042e1480141203008400304d5001d1142c0709602c000220784038540d6000c0c3c0c0c01102d151900710307140c0030854268802502d845907500b60410242d004054103102d4910441c42407a034004e050484031b5030380601d410003a5000100c423102c02004100f008402c120b040300418090b00d40c241040a000082228095180c440e040aa10005420f100c4540300390b0000c181141d019000c103446001504241005281c201c0385c42c22400c0c5030003400305100060040e1042d8004c09008007844409a60382031002903c801102102c010b0800e10030310740f261b50783c2d01400e40e1400000d235440c00b540119401d90720f00d54030702500c14010300c2409514600701c2d0340d2140c4005955460781c01c1582d6510f03800b10b5212050845a4440301079020380c00c0020580110106444076100d0280b01309004000c8418110364441c10107 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 456768426 1250 456767176 456767209
    0xa0c0c021302030a0b0307140406080106141210060f061220090f180601080c030c0304240c030209030714060406030c020a060c08010501080901050411190f030c0f05 72
    0x80408410700c07580c40350000d60340454100d0000c2a80c061a20109103030130072540089044070b030030640b00c0341c0b070781854810030300100401d900a00c0100d181120660005800c041c030703207000703041d0441450070550b01040580481d42d110380c0d00300510395031501c07014409141d6014080018596042e120740e0310b40c507406440d5211034807440f100038980a002c440741e030799032000740b2654202c07845007000041c0d90b44800a148003d00808401e007008e1130031030001013050900805008290f4411b0007031040c4540518241c13588954070040344200b080f218104440c070a1501c1144c03480e514204801c03000100d0389500903008044003a0210350360310342c0b02d02042c1c2c4044404507540d5009481480b0400010307109400c40e44075030701070740140d86d1400b5060310b8103420b4603040b1030868045403400004000c1564007002455010003004005c0025060980c1c50003101440740105034070440c001409042002d40c809442d00080c1804001144415603d1400b42054521440341940a01e01031034001001c1c05c0450f50402030020 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 456769676 1250 456768426 456768439
    0x1030e0625030905060c040317070308072003071203060501090515070f020d08090307150c060b0109051002060f0c071205220b0903060601020c030703031110140a0c0c02 74
    0x7100008100902445011003040507101d0f0032880201d4000d00406028803801500380740d40314218103220502012810302004518070810030140440c1d400300c1a9a00308400b031801040240500300854110b40d2024440401c80c040003614504020040350343d80b200100d07a4074140004e903a541d006641020f250300c9000d07000070900c0005010880303840018202148500c0c1c0076110f110303103600421000c2c0b800b007008540d04440001c06040b18503082006c41d00400c0c40c84030140c0c1d400c40f14000142200d8084500500054854070700c4040ba81c010803600c006444098040e04412442400003562624140c40382c050202814020600030b640719000c4890700c540102d01031400240c142002ca55691203440a42c156002034a0030707000114450300c0900080058105081d15844160109030a061010b0400d41c103550003041041e800b40c4003c91410112501404c0202d89105002d40d0241000549640c0200b00c41c034000c0d0480c103100032070300e0321406204295001c0024421800702503d450150f5000070394000d0 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 456770926 1250 456769676 456769711
    0xc09091506081b0a050705070f0513020c01140c0a1b0206121803041d0f09191106041e090c090b070807050601030809042f0702060c0a050303040201030e06 68
    0x5026880300c607000300d9030b10080c2002c04820500c40324280c214144c03040006400050050501c20704100768405801c107081c000d10110f2415000444c0242e9020001c440e654001c28032401d044000e6001440701030905101d031949281c0008034503500c5e404203019001144406220701411594000e2504030380350701820251405c61151000342208600400c8c5010b114100b0109034464202070024000504244800143e0600003864891040d540203200a5a203030100080020700f40000a480b800f50b8080100e500e00000079052440c88507005410550b001080041d0000c2c0c2c850b4101070503140301c046030008141090f100e0004034281d8001d401200d00180d2035a00504c00e445c0b84138010211640b00d6000e0624102240c1c1e10203007821800d90081d12076000216a403003060038107000f604d07074880c9003043d201c070b00780d50201e042ca021111021505040c1c00010404e80c0864030f13144c08907052800381600301c40c061105031504683c0d80d4012a0228002420080348002c10039000030382030b00841184040c460100c = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 456772176 1250 456770926 456770939
    0x4150503120c070807060206010906080a03020a060e12070b0103050105010b030c07030f0c050a03080f070f0234030c140d020f13020d060915060c15200d0c090915 71
    0x15001415100c0c00303030083d05030004e60f01e0010008a80149003540240000b503241620640841c2e91903032107044140c200b000000300180e404603d5010440e4800c400054020500001c9441d00101d000c4c803d620140028001003400100000241201d1040c4024041c030780c0c0b1003143d000180001e0354a000c0110b02440b492000030b00415a80751404118904100c048a1580f20b15143c0503411105030003050340c800c01d002811699440c0c140e482030040c1480e0135007509030b0b24001e5844c29003081142c12010031001055002001d000170751413284140b40c68640c81358490400100e104c480344551b410514010403c540d003400e002c8004151a6001000d044050262805014440c410703d0300034180035074204101c24500c2561320406000d044802000210703100f0b0340b80b0462480b000b9130018414480d01c00d8032200055440d1201c62a1961010350210f21040c225420390102c03100710340e00d4100514003207510010110b0b01d0740400c084400d556684101d09951740f00c6041111010400005103800345034050200 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 456773426 1250 456772176 456772213
    0x50a110d050601030906020d050f070906140c01090210020312100e0a0f110a090512061012050304030605011404050609070207140d050703030c1703060d0f0809030d080604150503 78
    0x800103050104100e40c60f1ba0b03521080380d0108403c246400e40d02ea09009c000803080d503030103500480904081207414100000078003804071002e40100341d00c0300000c40059854080d0040002203030301600c000d802d20140f607800394480d007040840d40c11040e420400905c400324440400c00446440708441d10081d1035100c1c03140d01030602d07410b101450340c0d201c3c1180180700c280c0b03030010024030602c0e0399042503a60070141080168001d036080035000d60f10038030601c40c0b078404221300c410446501c1d030130242e00c044951401c1400c5024079480032300803601d401d00010303c14074041035010300314508031001c02c4143d0b0780c4001c000901e078050307078500d00503030188800703000e85202c6256400c81c10320020440c0c15901c0c600e80d10390b4904409504218000341d90301700f41000b013004000145a440c4d040c401c0d500c0c1540f070202c000c1004070300f21100c064910144440702da018412428219020141c01078142c403c28642110b000e0054181503601c2c6010b0f902d805422400510031100050940780010043d02c03000f83e258960f801e0 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 456774676 1250 456773426 456773431
    0x180f0d081e041415070b0108031c05040503221205030306040b0d05060f06010908070902120903070506040b250c0309080703030e06090a18050604060e06010e1504230301050a110d05 79
    0x714501d0800050000c40d8441e06c45074003c3c43c200c4011590707040195411030800e44524610b0343c00c03c2c2488241300001d00e001c400c2c0c40102041512600c04006006c4401d8102185940070142d405c1e40d1850f900144140403008510030f41e0282c4042c4020740c1c0e03400500c224034642100c040c1940d000100440c00f070000f0510303201c1e00071805141883d00c1070740b2006114100a55540219441580010500682903003c03141c0ea502c0381c0e4540284d400e00075503460782c3c0c0d21030400400092543e0031807400290542c06150343c00440d0609401440c1c3c02c0c07842281c0240034070394600826800b04007031721b03c0082c90b107800240f1441030304c1d4142e9405503890b40c450107000081e0403050701160310410440b00400e0f82c86a140001c9650005010041003c0c20100e060008480c416000382003c10488020400c0303d98202c16050803150040e1003401200c400c040c01100300c0d00507a0001d4010040100005040c51000803078000e100400310000c01068882410aa088944601404003441001d01c40850106400d920055 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 456775926 1250 456774676 456774709
    0xf020a03080907150e0a1a0a0c06020d02030901050906090d1706030c04230c0403030503010302060304030e300d08010308070305090d0609050d03060b180f0d081e0414 73
    0x2808191200c08500302e940c804000c1100042c0085c1a4108a2514180b03903401171448682004004510180c00751281c460301c100001404580306d0341c0d00810170150704032074544001c03100031502c1e8141000254040c040c16031300c1024520506011500c5180e010410240887c5140ca8018000a01442c0f03118a03910080034503626004512540c035154a49000700084e00020b528071104016100012114030000580280c180b81000e0106100298000f01160f056a4044800070707165039031480c0c1100d600c0001d10340144c0002036070104030004405d0000c50301e6038030f211300780d5103900c641c1c03d84030741e1b03034540000c060314000030039503070040000c140480b004111940c080d142061070404560301140c610207a90904840007030391080b4031418000b050000749000100780ca018444149441480105d500428034440c0d40035100d058181c016070303240580e8001c58403000d00040c202800c50f00301200150000c00fa1203800100c007c5442d44120700100c22074042c0d036003462000d90a1401c80043c40301c000114001407 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 456777176 1250 456775926 456775933
    0xc0e1003090c050d081207031103070c140f1b040e0607110a060507021006080316061805062707031a042a030303060f05060f0702011418100f020a030809 67
    0x10810b41ca81030380040c50346006052082d46c50001300303400c003140440140a10700305803070002407040b0040c1500840342c20026610701210050010309000d0705a000c2854100080d1040a800700c10007a004180c2c20b03002d182e1008451a114146000e00058411824048480e034000310700188615006502c5440410055070841e041e454180c1e03105400c13203a01703540079005644503011280d6861070b070f400789201500f80740002d5800e20319011012030305100d42c004028040c80d160350518045442803000b800b201c80d005002c458076400d003030b00740300080c2c44100b01903491030b400c4540034441c44000041c0002102e500c240110f48001480c4a003014500c00580100d41d82c01148401c0c0444101c0400d403403086001c0810b2402203145980b6016040319140e031300000c68510300940410440d80c4140c15550314034400050726658040d80d10049805d01052103000445120200306680950408000003045403001d40340035954007103000081d5440e10280d148040107900071501000064403806c4c0342c5d500310a038101207 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 456778426 1250 456777176 456777179
    0xd1b020909190b0f06010c050607030b191214060402010804110a1517150303090d0c120b0f071d010c02210307170711061606050109020d0c0e1003090c 66
    0x4820b9140d42281c0944041c10040c05001c0700454400c4410f82000007428410500b840c1561002e440707000003031283c018150707202c81c0000140c4845c1003008080b135961020b80f4106440b480950480c45003100203648130340180c0c40144014070300040306806550144c4070107603181d586580f841d03c008011900070f90031013003206000528000080341c609400c14507071590a4840e60089151030490402048030a001055951030119a20f0120440e002000140c40d050551012410000400030403940402c000e520413000000600800098542c01900c00c001c1c0c1440d152100b0700308071400654140c2042100f8804071616070307298015501c00c42d07403510203040c4c0a210403006013100c002c082503400b510300e2034000040200400403010026a450080303d0306550a1980300e07140e50302510790502a0600914000070190345040301008480d90380c80d4090f60078449580c50701170601c041c0d001001488001c90401c954846e0840c003640c60b078900f001c0b0151002601c4060f16030214040e00b9000170617034404808910 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 456779676 1250 456778426 456778453
    0xf040b0307140703080402030114070f0f09080706030e19110d0203190b181b0607150204290901140a0e060c03070314130323150106020d1b020909 64
    0x40c0100fa806074950140741d03d414014582900c040d00d1a100401d6600c00030015125041090545203101e1482c2c41402c42c0c1c04100309940c3c11900780c101c0180b40c4209500090003c3c1d241c1c0210b0001da01080c10303100c1c8481d22507210144a0b0704000010464401d0700d00c1d10031582002c42248004074002000c032001103c83d10360702c0034480044a03040d0b540ca505201040b0703c03e85c501e0b003c098828202401000d84000000001104118003d5400e1041000043c4d00f410310100c1c02003841c17541c060200840d0fa907661071505100c0508028007690101c03203030200c0300103810118000d40c5c0b032025044c0c540c140600402c00d00b01c00344d503002c1080d039800d0040240030780f00503888860180000d50141001160344843c90b04016041c2e000180440c0943c2d070302000801011144594400200e0340d104a818442100c1644202e0402413485410f541c42c0c404d80901101003c1314242c468100c8041e502038407003141d18804110761070313501c0007000b580707018003030100720b006040a1203000e921000c400259800c5411280c1c = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 456780926 1250 456779676 456779717
    0x30f12051e18060c0105010f050f2101090c0602030c01230a090314120a0e03070201050d020a020a14100b060f04030b2a0307030b090618060a0f0603021206060f040b0307 74
    0x404042983e992003005101180440800c007000d45002ca0700e1070321040ad1000001d1580d040e50105e42d80d885d107000c0c040034188070250408901e040d808000c007440d0360f0319008000e40da5041402c2e0040300e90700746941c00d440329a42012206070300188500c2881c0e03996481c402c0c00080d210600d8204c0030080e60300c10280c1c04100802c003514074040f10341c42c036141a05041400d401a070b80e80840464040d0010040c44005030b030020101c5050300c1d0070303450150700c510309440c0582c1804034020000e06081000a505640e407800481e45414000400d80200050181c401c02c0c40f41038005c80300d4522101c08100720602c041101a4041f9504c1021400001000e00000c44d411000c8480303820308a9070000040244050035405026600c000d0400759485e0205113400000a20300d18040c0d900103001440034070200710710392101028140900028079580d41490740d05c0340014000d5200f0301c1c044c00c8010420020401504c1d04804807204580900039507130070141840409105c0d54409410380301808110720804003c0350400c3d = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 456782176 1250 456780926 456780937
    0x10306231810050f030c0a030f050316060c0809120405040f060f0303020102040503060114010c080a031b0909060e01030b0c0c03040909050304090f1418100501030f12051e1806 77
    0x2e006810000c0c90007080c0403107800b6800d80184240c20076501c90350107407210585c50049a40100c5e5441b1401d41e5800d190741903110710b1030380320a191510740442e03060000580050640764090340e10404582c0e100002c5a85030045002c6503800c40008120410140c034094109015026919200042555540d07030b42b9800e400803544102c01517500800c04000070700c1c1c103004090043c200d00c1180c804000c55200020715801903a803000707006102c0441c0f80e100703051003a0300c400481e0b8000042da4681e2000d801002d4200c3c0b442d0303c10b00d1510303400e00e00041000708015071110b040b42d6000c1c50001c0d007038485548085643c0c10240c5d804c00b0704c0c40b084c0800a0b0700c00860040e90039860203035010b16070b80c07424050380900342c403110380103210200d090540c040004421045801e500880c82c00864a00480ba82c8905041071443c21642152604100022080c01030070907000c4145403141e01c1d000401d014912003903490b80a050f0741e691140404030b20750411351100100070f152602a081d10115560030800001c0e0f07054108 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 456783426 1250 456782176 456782191
    0x1311101803120f0207060807140415030e0c030307030519020a0804060305070306050901050f040902011b150c1e08041a0c03060f1e04110417060708060103062318 71
    0x204181d82e58000d4000407249501501840982442d5003032030f1026000f204083d00040800c181002250022448074058601629803807941594401c0c40400041c058101c441c154495030048441070032080c940001111207650741900c0306401e04015044210305004021030704015801852481400200e00c2d80041018002d107031000501410700101c0141140c406812842c003980481006124541c0c0e4a00fa01d10031038422140890030f40d80501c0120750f10010549840303444400c004401040141248500500f19101881000050300a80c4103e5117100c60a8005c1d9410f0000041111000e21a0b840e0079441070107120340c08010100118403401d00b040407152240410008002d00c070703a40c40c007201400c000000484003416401000c0d103051550070404001d052159170388045a03003001c032513141a0303002007041c941c5e072500c4412080e0740c0d15103480040750703844000f5090000255031507002c0e202d00c1058940402254510301c5c60355200a0b28011003034201031303110701000851251680010f8070984682c59 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 456784676 1250 456783426 456783443
    0x5030307140f06040b010e04031403090307031e081609050d0803010e090601260c03030415080a06080d0e01120f0c1b05061501050c01050405151311101803 68
    0x92010308208068800c0b10031500884107200200d03c981050310f055a058220440642e1290b00d8103070388000802d1074164091802004100d15550040007030052103000e6118541542c2d08104250001c985011007080842c000401040d05007a5040445480100d60300f010b0814036110400644076582c0000e040714480700000040c415501030b0584182c124141100400d8070707505002c0a00b08880d0108810869114981c0c130451085004204101d0060703c0981030b2035849464119105403104203c0f00d4002003001d510208010b040300748184011506404007070a890103032000111080c82d520f40101c0d042210403104075007602450322070882c3e19041c407a40051140991103020b001c5407004000045549520030822021402c0807500941c051000c00d408403000b0f24840c016202801014101300081d813a2800300410800002841c00744500411005091035507030040481e15041101001010000c1c0c03000d0600082c10300b9800ca142d010f46908062010301c440d81d980e100d240c1c01a40c03055605d00c1 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 456785926 1250 456784676 456784703
    0x1b1f120204090b0a090507021c090e0a0906050730060306140108060a09030c060b030a15050f0604090302031606020405031b04050a0c091203141206012c060d0605030307 74
    0x20707208000c1e00003085e20b1030007403100c0e1500e075a0194aa40c0050304000541c2d011440451510b8403491098015022182d80341c4003038140b261500d4018000c4060444595141501041017903003da0032040051420303090b214141044030800c0342020301e812034a055980d0f110100800041c0050251481b032851070151101d81e0b40c903242c0300c01e140c404042c1c04601e0706490070004001290b0302c4680a8240c42e008800410941118000b2a01d0070041c0340c000340a1100035005c0660a000035000140502c10608040c080c58071072404002c211600c2c140b0040240c0d00c2000b664104490905501a425025180040c100380e601e9000c40d04210594441c0702054042c3d070603224451506104a54205102c2e403000c000900c04440e0244c51031105000f01c0e040d0403000802d40b01018450301d9500941d101c3d00130744030f8403002e40b0540304100344010380701e05022407541c6600b0482c082940d02000562226240403403c114240e1060114690150b035480c85c2e000c0c3c90b1800812039484c204000c04107184108140f01b0300c903 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 456787176 1250 456785926 456785929
    0x81e0d09060e0706050f090910030b0408042d090e070305031c1805030403020603040611072103111606020409110a17040507090e0a020d030504081b1f120204090b 71
    0x40310313030000810703c1014001482c840072060305644a61740155201091511002081008a18140d0008040c94480320030003080000150240c81103d90320601c05140c0b00b02001c1011001c45020146803880d040203404000384046500174906840e160400d4a070b8081e1030b51034882c00c551000e400c1c5580d00c000600d6041207410359200d00d8004070100c6d550300480e00f6081d9112a228401c3d0700c0064420100400443c1c10311180d5442803916410705c805c41d07987d842c400d1500b24105000070002c0128006444030031442c81e8082e0083d80d0f0281c001101703217894003088840310510143c00c3c00c400e80b0072039400e000104a005c0c1d06d11410304084040700b1001d40382c46040c54003c06541081401e50307150071240c000e01000981c00250b01058490700f48000c10344292401169292000310788003e540f00300c80b260058185900b040083c03003580c8051054030035041408503907145d141207140499401c40d8014083c0d08004204019101c28403035285400303450002c19581c4031040c0c2c1c0003a0450a80c2580c3d071a1000300c3d0303 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 456788426 1250 456787176 456787183
    0x140a021c060b0702091b0c0c01030605041e2f03150102070b09040507050d050f06031903170901020403050304080304050a06030507051c020f0d0504050c010903081e0d09060e 76
    0x10501100c0e0280086030a1070b015903068060381400a0140c1c100c88080340e4002a50300414041800704160750f0f0b241c864020000c6c1c1e41e021500b03129070201e880d01001283e141000e018010032117108812400c2d084140310b010100130010701101400650007148200e20301315060b1039480e860b03071010807511b03203e01b803291141d600088012141c40c195800003000301b11402d294400c0d60f01c49041201c1c0003400313544e841c0064540d4821010854095813428080203a1a160170903114007644007a02210404880c0d0282c4a2406940b0100a404201410390700b0b4280c840b6000c00546c041840d000150130195030342d40d480d2454000c0c3c3c01200f21030704007003001c0c0501c1c00c10015100090401d803070180010b0a0540b80600981b003071090280e07a400b80c22512682c10311854046401c50103020703400f10340d20900e4080c504000d06044c1c40451b601d000344c00345030603030f9031150160f072003a20b400020961500e40300c60940640d8004441030540500710a02c045814140584076210465028000c0418135402034051a0305 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 456789676 1250 456788426 456788467
    0x30c010c05030f0c031603020f13090905061b0d24123008040f120c060f0b060307050c190b0103121e0c0503040e0403170109090f0f020103140a02 64
    0x4201300030b200b0406104051000105041c456003001603a40445c0720503410188201d01d0b01900f414554000015000030f20ba0000583d40d0286080d03861a40325203403048249200307408000d94030542030100000c081c08950207281140d10585107000c922441e441d40c1365125003164400201c1a522611131400c0c42014600c0c1d4201c00d0005240d294066000e001c074600141001c1d4200c1704000c401400181007042c0f09001c50344503a0055640d4045404c10100141504800002102c0050600c83c1444100d030f150b01072188001c900502080c21a03652450883d40d0f508007502405592244941c00c03104a040700744c114821901402100529604506194003c0801245100e08100101c520790664000110349030041044620304501d1224941c1080c41c9180240d03046684038040791400e0001301508120315046000d40d14501603d681c3e0f07148803413401c030340c5100c0c8050401408502a00c0000d03950180041010b4814140040e91503151800c4100c242d20071900c100606900290016200107910010032 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 456790926 1250 456789676 456789691
    0x513150e101401050d0911030a0b060a0909020f0409020a0906060909110c1506040e0709050714130302040b04181a0a0605010210020c12030903180603070804020f03030c010c05030f 79
    0x4040c00b90000000700288940c0030301440d066900c22106d030801201138290000094028215500e101050401c030000e48416203610340b1421410384000b901004600071003541540042101d000c4204c6401484050140c880040703030300500700352012564005a11500d0b014043c1e942e07955480031b041181010840321880240c8030a21001d0107002019140010300040407100700000c0d0a55844400128000d1f011400c0c1e0413041e1b010b01180070a083d8a96404544034103200d5845e401d0242075010f04030040c0c0f0410003449078079441c031354091025080a40006190550180c800902d240c201049500a904941c10495080040300354a21281004910715034000c41500c41c2084030a2814001070b6076004110b04001d0110b40104091040880511a40200c211100e52060b40c07450310300b83c1103480fa800843c0f001d400070941554000c41e0309265080d2071058046031210b61050300c582c1c00304982c59541d010319503032601c01005034000c0040c00380a600e01403c2240c0b03519440703080011103400310034002003070741 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 456792176 1250 456790926 456790949
    0x504050105040e0618030f0c010510062a050c10030209130e03090d0609021504091410090e0f070f050906090903070209040c0b03010b0d0510030c0513150e10 69
    0x6440c00c41c80440d41300c1c1c0090b28580c60740c035200c0103d40c2950640c0503100c44a600c0c240d010a4440c80711806400803442080300e2411060007607112501034882d213a0111049041c0c1d41c10396407a4901103c01c6c0e4a0f140394034051001c640281183d00c4c0064460450449400006500810110100e05100740200011603140300e05200c0303240b60b03041d000c0d078078000ca41c1402d2062003988030031014064990b100e07928440d000b070040d4040c0c0c815044070106030713403044c86108416031525940480032040b401c042406451220200a0403070720f800050b8001e40240002c00368a0b0140101c90501c0f00010025640100f080d0484084060724020070001500401050b090198030003800300915104040216009a5070490358104651618104400c48016540000320100750020001c2026225403001d40240384060320103001036503c03030f240300715500250711000309a013019480500043c90b080c0104621050418400038511032031000401201004e90310a44070202ca01050244194130410300c40044c4c180015030 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 456793426 1250 456792176 456792191
    0xa020a0f090303230c0307050a02090a0c232a07050108010e01092d0504110409020a171002070f0201110d120b011b0318060c032c030307060501050405010504 69
    0x2900360f0100040e0544218003400806104c64034200c207483c0b090403100308a03521100e0614003070340c0e180c005c14000d070b21900b10413002400e00c80983c02280102165580c8500f96400d40c2c0318580c000450a100e400301c1c1e003105102c0382d1105000c2464031071070080504050f288400a0400060500500703420484c1007100510041c0040141c01e5402d0781100c0060000060541804c00d04180ca0440040003100c00800d8030070160b51040981c02541c041d074002c1c40030500350305282003003004a91000c2c100941181c070751101040a03071000000b8403c200d00860a03109041c5200c94850b04076440458200c400d44441442c4405650b40300310070078070300c40011005004180325210050041c486041d03d148049883d92490038080c2d00c031321503400f00036040302c0000300704821b5894054249140c103032044103100b4a04200140b40351240c40b80108054064685488040c42111490400e180303100302403580c0d107d800b4031602c440d1002c00092048034050310001805504000421080c1c41040e44170502c9103050100 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 456794676 1250 456793426 456793433
    0x4050a090b010b040e060609040608121206040203090a23011d060c04180b0604120f0b0609130f020f0603010e0406060b03040201050a0c02041134030912030e06030a020a0f0903 77
    0x5511b1340210007116030780d803111310001c0010040e20b42604604c5207401581551000304903400080c000120140301050b559658236002e2000300e0100f00c4008809900240c240808035005010103156594034032035200030101d00380344071b5095804015082d01541c07842049801024000d110207500f049013119014a000c0c500300c81c003400c043e001b40e00413411550707070001c640781d40e5902800c48009100308000e42c102212141448021340d449500c0641d810001c0c80001105440d2074070002e88956803034500b4012690381912610701d2560002c0c0100e8110344a249080740310b1341c0b210003840c02016803c0d403009291525244c030fa4141d61041d4058100c4440a105000050382c001081e12046074061800c17103090310a40c00042c0207001c42c0980d03510350b00d07400940103420528050412032201802e17242c1079629502c1a141c1c8030094510a409400907a80840500140d41c0360505140428003c0c40d00701c1c2501c0a110004030240c0c419500c0041041e4001407440502c0d40008100d90050741c942440e6003254076686 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 456795926 1250 456794676 456794699
    0x1c030f09030b2724100306050f0124140d021204051e0703030c150b120c040e070506040506070305040305120714060402030d03020d060909050a2d030804030e04050a090b010b04 77
    0x404c0004030b225480c001000c0900c09140203000796040341c400d00441c14141e070b07001090142070141c220608011540a0340651414040c41c00c2c1900903580d544160003e217030400f0f41c58001905050206408201d00507802d0072000c0907034003990203000640300340b40301c10f40318207003c8035015040015030300085000c00c04260410300244140b60000410800d0364a00e1100c100100f1000e400305910082102c0314070f8a80d1030010b0000302010301503804100c01090545075656900c080c0c4502d41c0d11400401c414850760904002070301c5c003144a400c18030b050a840e07664150400c00781035007424660401140f1901401003031468402a100100c0150419003000e40100c1e4403803112010b00d2040c0354000840c0e89c4031003590f601110062112507070801004007039207852502c1d0340d42d019051715007240d01000b01482c00b464025142c0c021103503a0262001404641d0180d4400200800581c24840040340101e800e859038010103124a03420075002401d00c4462400402008041c6c001c0d0042c0ba070709010a000040506 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 456797176 1250 456795926 456795973
    0x6060f080d0210050703140702060a0c0e0901030611161109010f15081f061101110a021005040807061103040b0c0903030d1107021005040807051c030f09030b27 70
    0xe0300081442c5d503421209801410a030344081220302c01240811600356400f00c2e402d07018880030b0800303116043d4410001c461503021900d000c2c1d808200700c00100002103040e4801031520009066150030141c42d000340454041c81d035803050701c1b14070010740440440e1501036001400340c1040745004084d9800c00300880d40c00c002e00c0c1100810700c03540700003040d8481d1000455107000d071104105007150985800d40184004240c1c5840e1281c0d60812a0780b82d504440c540681c2c5078050b260b4000e003240711500c402c00c405080c002d00701356a6210108820004580c5038000c4e01960001304003480e80c2da007881c1c5000100120020704c3e031074491000344140c90003a50040112401900c00043c04501241217006007081ca10a40303a00070740c007120032160481040d03084400f6004445200c0300ba9200035546030140b0801d0300c101c3c0e4a5003141000590704000080c0189480e81a050041c0381100c401d070b80325034a00c24241401d40b0b40e1044941d0000c45052840c42000c081d080075401140a004904001e000039070380d10418 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 456798426 1250 456797176 456797203
    0x307090807061b061d07230306060102061303032027010813050304180507080c040302060714031603020705030721060b190f06110a05060a0e010905060406060f080d02 73
    0x4c0d405c00120105240002c400004545000d948405903100c0d26101720303080343c90b0044140881d00844030443c1c079010071058801c0c001a0054680d03903884010300088038820b44000c03014141d40d0031098551070807444480c51031160184100f95216400c41c11610760180b062011034400080c14401d11440e60b04c61003280d000710920305840080c12041ca001801d60003950490b410009074002808800b402c26004907020701c00039164060326403200710b001e00c500c0c07051b4000039410580411007400000c40380c6d1841105103000728141c0c0d08003400a000202a101d81c003109600503480114144450301d03050042000504072410001b601913034450071004081e03c1d40b04041e0a040c0e851780400e40a85900020040030a0300320200c1d42410b4a80b40b030009280401c0c06160001100781d000303050302c84000500d40741c100350400018200307961841d0014001d410360b800b9003074043d506e074002c0c00300048040080c1d41c0118030601c13010503d1410469088a008020b81c4200204e42c0b01b066448841340d008034180d40c2c000752 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 456799676 1250 456798426 456798431
    0x1f020c011206031b0f050d030c030f03090f03020709050601030903090b030604141e0f1e190603050105061216030b0406090212030a030f0c020c060706060b0307090807061b06 76
    0x205040800100820b038000341c0790249400760148030080700b074038060661700514180d403c02c640f0350040c800610389540b40100071410000d85d040102e07020b8580361360034040c180380200d120b040c10b40e140308803c030306180202d02580c404c0c0003d1000c628180a030543c000003e180800c02c1d09440d8a008000d0001c80c030030802c6801002000c6580c0351141c1c0c01c006981c0720007015070103c90900454064111466206e815003240302e0601082c00d201682e0f2045001e131851079081d11100d400503048200c0c41901501180750960400302c0880f056180d809100011030080c000020a0310304441440400302c0b6420100780d881d0440c20308101d034440d4003920041900d40210050160395075078580407004000003030340607501003800c000f00c2070070340c1c4c1c0000280b19040d41c5603000e0140072881990041035520645240015807c101040c2d0403504000003e010600c0c0211404a003980d5180d840da42c3e85e03441980d180001514601050211440804c0303c4c0008080d1840c2000c01c3c400741c8001038100c80010b180042540f43c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 456800926 1250 456799676 456799697
    0x706230304080904022205010311040302061803010507050c011a030717030d0911040f0515012708010603020102070e0f060105030403110f010b13061214100e03091f020c01 75
    0x21002c0681d5107066029104541d00ea481c0c40b00e08074020300711651200b095a401320003103960f52081c0140c811b00e407140394945081a0840d400c000e1140c01070705d00f000251403103681c1c5d94400e0b6824010680103a089469841c0d441070300c00225800d465110456581401c0d00004807196a200090303808200c0b596503441e1049850f040003114154810445480a118184940345c014402d03150500701040104aa040091810210040d002e0714400c688100901085070203940c85035024040a07001c0102c1200c01140d107040c1c11000102204480d001041d80b82e548580c01d1045580400c03046010b040b154200714001e261404e00da009041004088504028003c004101094010051407900b454900182d55030000041c1c6c1d800d000307007006a015442a21104400c1000758102d219003010b40e28000c0c0310121120042e03e0301c002c0f82c960310510004511075500c07450742d1007003103120b0b8070740d246000e0000d03640d6040c0c103000f0003030360078407208401003051190f8005160b0341c2e4000480d85002482800e060303c015 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 456802176 1250 456800926 456800933
    0x10c1e030903090b040605130501030b18060f0a03060501031a0c09010309030509042d1e0b061902010501150e1804050f0313081209010807031821020706230304 70
    0x3c0d0041c0d4800c901005001c0703130109410707411102802c86141d00d00e62022400e650382004409132642c0b0050603401900c540c511500313140000c1d1410b1b900c4000601885008801d440200f1b4203180681d1040e9a480d907240018003c10250440e1454600380f40341c1c00408a003030412201c10340b8403503203009074145176031041d580b42018081c0b4281c584101005004001001d1450381000343d19114224251190b0380d14a040740d41000705101d002c2262007950041c021034120401450000e0902055940c5c0c014003d00092000321440d5041144c2c00070f01c0c1d4000b24440d45070181d002c40001000440030180084002c20446075107030a22400310034042076005102c20303151400c08604091001102800c0b034000025012481d20040182004507005c180454601440407401c01b5807034054810702c140003a800c2008201d0b924030903005000807014405a11427494583e5849003c140403011240d8031002c509400081250380500c03040c4000c09240c100440602c90080d0b0212181c28a009a9045180d0100105061 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 456803426 1250 456802176 456802187
    0x40902160602070b0405060c0a1205060402190908151501050a0309050607020a0512030708060120010c0801180b0604060513080a050609060c131401180b0903010c1e030903 75
    0x5030760804011550b814a509003420700410844040c0d07014801c00001c158024510021540c41c152995aa00d04c9600c800c0c1d145006083c0103405154065001e00200d40c600308440c03011400260f558030b0300c00f40c86207071030160380c1042e403d8544001608281c0042111151008020004815091034880d541d806400d5080d00107101d071450192451048604000c80c50b0340004040295502601c100e0f00d0003072800d8043c0d6200d200890302880056076030700105590754003455086106040340d000082182e07042c20001c6003104c500c040d094002448180c01086004200083c10f052203503500c10600c14030300320402080c07580c40b0301d200d070a080040008088081c4201020980003411a0000303a8013814030500b005a83d444082d18621100d00440c000f08041513087d104a8609408103007a500c01c0b107141886c828140c03c2c4503508681849000544d25003071030b07805502d403030103003e0241149445602042c149421074194000031014012489500e8130140c9106200c0e00081e4900d00e0040741e460080c1c42c04840 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 456804676 1250 456803426 456803467
    0x3140109050f010b0a0603091b080708010e060411150706051f0501110c3006010503060c120106120e0f0a110a0b1206040908120601180b091216030f12050f040902 71
    0x30001094280070514040114010382114100f4cc000d00c1145d000d0030040d9107915080c1c4000300039901c8a01c0210845c104120320400d1b10450303020300350a00c031854a40b102034840480701c2c07440c1d100c01c164031814244c040c0c00b0b00f040035000030329100c02d000c500110003950703c0c0c6103e0f07545445600140c4107044002002040300881c85a003030b800800c40c04601204617a640028042d0300c0c401d024000c0060312103203103141039400700e44c5039403c4000301e0307403070440d0548000d400210384800e1240c03101860706410408019082076218090002c00c0c5070b01890030f10051000c030518007544580d0b209942080711301c4419090320210140c0f498140891340f203110005008000b00c0d2002032443d0804218504a41c0346200c203244103200030780344e203048825881003000103603800c0d014041f018441400040054103012040500d010340620444018864410b41e41d200342009230b1040320440ea071214444108003c120031440c80c0f601a04001c0e04000c402c070803810843c0039502452510503404240500d00101d812400f14 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 456805926 1250 456804676 456804713
    0x91e1302040617060a2c030c100207081b0312070806010e040c14030c0909010e100b0702060417071721121315140a0c021b040b040603140109050f010b0a060309 70
    0x1070701600782031b0416106e070003030712910072140244980b070301000c1d2140c001c584030302d54004a041c2c81c041881030124080180d0f01c01b102d1962205000c030000c0303465a01201d50040c2c03441c4d158180180383c00c200062208404001c03c174040c40c01c1c15600d000c0e640d003111500c11509400c7d4480c5440340d030344601c41081d900406403110b900940500c000501d140c4001402402622604155160f0a4031103a41019612924000a400a9081104100000d01c03a100524409201d4058404d00340d030340c4030f983da510300f0050a070b90025040746000b0a81c462030720001844101c0c00380310242c1070125801e441c04400d1001062200c1d0780141c041800104801010701781700007044110100241c440c006440800044c044400118581c030b0801140c1e0160700000d0208020200b02c460483c601e6415402d02c40640f54940300113402c9030702c4100c003000140e45503000e103c811500b0341c000600640d0604100f80703005681c5404000591402c00c1100268803130380303100f105464860401107200d1115113855844c0d40034030042c2c0d0 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 456807176 1250 456805926 456805991
    0x50f18010603061509050102060637140301060f03020f1503131a040506010605090301110f07230307020d032106170705090402091e1302040617060a 65
    0x4500307a41c140d48014155150b010f04841102440d032810b481aa4880c018107000d030b030001d400141180387c00c60120180e003141e102407100140720300c8203800340460100b030403504400101d213041c4002c80c803002c07410119020440003440722134600720040d000c035580d60002a010700c0380000301c2823490300c5d0302e020216a0078064604c0344d581d141c403104008000410321003c4500c1c420903030103074020030308103c0000d00607030700400031748150f91074a031060310f095220303501054045d501c82c0300790a901031241c00a8034615403401e15a40d603540027450041942000c800c40c009003100311001c4001303c0c1d8800030503510318980c1500c83d09901c00090a0aa44c1c0003211505540456005100c4501c4040117400507800c0f43c82c075a81c82d28500380307510036898403040d107405100c1d00030075618001005407030008074080d004080303004c04180c281098405140e05c00c0c8100e03001075803281c220142c1c0b42181864891180102020780000003110360385017034541c451802604403407800c0d4441a80080080529a283e18a00d41a4822 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 456808426 1250 456807176 456807179
    0x212040515070807021504050f03040e0609060402070f0b04050c090c09030d14090d0204061a12220212010e161d0c190201180f0605060103090804050f1801 68
    0x9990341d000c810540c82200c01c101c801040c2101d00443c1030340d0140a598010b04041d0b507080d2000034101c18024030699052250800002051106000900140401548520403850a8010303c004550040c2540b401544100304010204200c03040510007a58440c0c00c400c220789460500600d000e40c200380160f84035502d00180403c0c400e400c8006d2441c4d00054007035079000c0c0c9030940305480601429000a0141c081040b6940ca603190011f10b00c90418401400010f5040d160b21818001c03002c90b000c01c0003d01800075107043c02c2021500c030310340c0c050741c0020900020b00300b500000212240b0400024042ca0207a01da01d8543e413806e421241c42641503408850ba5030f9024440b41c40d5600540c829550000e05100100d144564025500c1303109000040d0060b180400602d2140e4542620803000c0c011956185069405154060001c610448c0613603441441c1403024100381040b20b0300070b09000c0c141440c00b808400042d003114240e9003103038000c451032080740b524080030580c048070083d1622106000c0900 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 456809676 1250 456808426 456808433
    0x50a0e0a06030c030507020109021509040e0106060203070512030c040501032f090f0f15070c08060114040f050f041e02090f090601270b12010c0f020c0105120613021204 74
    0x1c0f044030606940c0c203000c5a15200001e0b804c8840300e0340081d420102c2010b00c01c3d40c2021350320040c946204064400601c54a0301c5082d503003121029003007900180c000107900000d1010070411080700c0c100c2506040c0c41d42c00c2054a43c100c52140d8410981417644942107144a22001103880100b180d07007040c055060340c02c02ca50880d03264410204907100b2421000900700314140300c054590000c0001d0308208401000706000115600b047d04100e951050504011a210106010b4140200600015200d007002c9260812041d80d4501c80298003192400c010808480c040c5011035401540141e801041040b4658520f1040d4040da036019410903021000d00c00c1b08412480980d200307082c80c0003a160680d8845006640342c1c081520140c807925401d000c0514140700941c000400c00d40c00919880340e101c19001041e09407801c2881e401c001c81c400c000c43e0b007500340d0107201c1348103842800d281507888c00409900310004150003901040c00354510900108a845040c0c0c101c50525144901c004120b141924 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 456810926 1250 456809676 456809681
    0x3050708070b060a15051b0a0f030509010305070e0f0135160903050a060c09170d09060e0117060303040504060f0305281e020402030a060603061703040303050a0e0a0603 74
    0x160b00c2c50083d0644030740024804000040c405c0e03a40c4055071458079244440b03040c402e00000d58214002035002c0c4101510010381c0040889110b03c0c82512071a890b10448000501152030040060081c0980c1e596880c9091b501e841c041940070009003411070310400a40101030400a1034908054001000d5210740400e00c103101d1844c8c8140e0100d808003440c103030705940403900f40c1c106d0301c8001c16603803100d11104001051500b00701800402864023041c105e0b41c0701504582a2542c0b03594841c0d542187c901c01582542c41011640540801d04004403c880d4000c0024886c100c03840c1d405003c00400760101d81c080d5010300444004141c014000e10407980c98000884042c0c0b4288011141e80c801c041e03102c00e480c2c10a44130201c1062a42d008510400e8658a0f84910303400d040001050101020110700300581c2c0b544003460050805040000c1d000782407103000703021a400c942200c82002e4080d010340344800030010803036040d29494a00503888840301002502c029070341c0c0105540c0040381c503001142460380b55 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 456812176 1250 456810926 456810931
    0x30c050610050411070c0314010b0301020f190f12020f1603090f0602060c0712030e06070905030708210903070b0406020615222c0f0708030f030601080403050708070b 73
    0xc071400c0282c2c00201380004410310031000014203900300c0800400101e003849520140c00c005000001c21030040302c000207400c90740810041c612513040440e12128060403050511082e5046041212000460b1715002e8170603940e9200c0e54000036000500502d00c442a141a84c40c1707100c0b20f07000500364102519014218180a005544160650300380c0029494400100796015140e04425646400001d407186001c501180c00041c0c24151102d0300c29a00e4102000035611400d050340c1e91007240c0741810100342c200081540300103540d502c8801c040c0601850700408511480f000b440059590500303d0100e0306108582c0d0241440200c08600020341c07030340101e1041d1084010314281720030b80302d404c0e042040031a41c4c1005118444d02c07000d441f03402050300f80d1110030b0964070f102190151507811000c03201c0c110081171445669030820680013891072400c10160015125800c051030604040030307900d5669001c000e11807410401890003040c285801141141e03060754011004035600c6d1454245080114000d = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 456813426 1250 456812176 456812179
    0x140103021b1e210a03090f060906110f12060d05100e070b030411010809030d150305060f0403020a0b06060f2107030c0f030911030601080601030b0f010f050d030c05061005 75
    0x102c02c0921080031003c90a142c51240f9007201c44203002149030048100d4200500301d80c24590b4072990000459591040080e40c184581c10208010784580341c90000e641105034494219a4207002d81d0441403500c00a42e01c0c41c5a8001d0070340b20a5480800150008034440310142c801c0c02401c0c45011900381c00d4001d00c2c8035401c0d00d8120340c00b056030b03200490f5480c0700c1290080d1110f001d295054034290310810344603402c4014001143d013012080394241c0c2c00c982020181035203555502200f04104a402d0001590224140030b4401b4981740a45002e9220030708120020624811b05000601550303c09055894481c2100d4043d83c981e40c45145120044040c025800d04e81101c010003d214184203010388408490b040d942d21414070041281a0090036031500c0032078050580841804481d1070802c234031402812107070002c1c2229403441c245007051a2024200c5800900d409006010801c02c01644d00100c8205540115000c500c0b405e04990718022441c00070681d014080911405009040900058490 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 456814676 1250 456813426 456813463
    0x40503030f061504090213090c050909100617101a0a1106040c17010207080a0c0b0c043605041127060103090215030f040624140103021b 60
    0x2212410019903d0001c5140051000100400d001d45c07405500070b0000d00000d401140e40c6681c5800c002000c1c0d40c4aa903600000410120750f5200508c3c088000d541c02201441c8028200760074031741c005000c102801c0c1d411043c0311554020885101104c0103010081170014101d5442c3d200c0181c078041598425a14800060911035414030509004101a80100c3d8001002e005080c640038031003219400f003a4862003555424803002011805240041803004d02035510681092030707038540000c44000182140441000a1105024117003a402d05000313201c541d0310002861541146c405640258604051a801030810050004121400152030720b2a07004542d002200600003107949500f04018200c000071014040c00b10f1402e50095002604070f600260a403a454011098a0340c0039600554502e0311000d90300c0304000030f100c0e00b03103e40c2c00c4240c008207810b41e4410280d440040d1078487c0c2d0184401d8070f1a0415590080e030301a90445e40034203000c00c043c5e981084188100390711000e442052002040 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 456815926 1250 456814676 456814681
    0xd051201080606010c0201030e01110c1509031608180607061b0e061e0708030114011e05030415060f0e04050c010f02250e09030c010605100c06090f060203040503030f 73
    0x71000c00c0300c92140c6010381d151102d00c94140c0044020300741001e0100610b540e035078402c0780300501c104001c000b04081a03004022403005103460110a140050260703000c0d400600051400f81420465649010341001c0120703280e058902c0000082c804a0082c507034455400542c603010000c494011f800710700100007200d00c42ca4031000702603494040101c00c46502c4581000b204655130000305503000f000d00c0f0201846d040c40095501c4080d540e200b130300000008a00340c21804000d44e8022100e24994000e607080c0741100c1d03054140a007281c000604001d04c2c110700c0b400b4030307080502e00d544a000185041034031420303039980d2a0452030812500340da0941c0c1e1f500a011604816500a0380020101030040d8000c204003d4108246400209000d07044181c10720981c070002002004480814082c029510281d0741c0d4528440c211030840b50540d0041e8003810582c050600c034281c11075252100290080760115841030213280071440389a2400000785098404000d210501600001071445010070301441400d94 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 456817176 1250 456815926 456815939
    0x301060b09011b0807050f030309070807030b070e030f12070c09050f01050603041e061b0306080727050c09012a02012708061b03010825080d051201 65
    0x80c441e4003105400700380448040038000d04110000c0100d103019605203400e20b10603590b03140c181004d00216810350342c80403081c001100d00c1402504028001c1800410030700c0d1460366040f5070b0003801042c1030144842d44403c0d090644060202e42d8004580000780c031144070f00c201540000b500111415242070510001c00301c0c0102e41c92140b1070143c0f818030601b18503a864041003000329440144112401030468907184101c001d81d6191b101224030962000c50300741c05462403c580d00c02c0d4010014100741c10980108181007021a16006680a04608079603c01915405650480c031400726031103601e00c0c0808100c449542030020f80001c0400b40d035030b1542254014031284821910a04ca4240e48142c201d0a60056000300d043d0040701d260b8811000440e482108103144022080e801180076800c10740803c14844204c26520510b0106080005e00b5941840013030395859195096000c0340c01b680000c0300c2d00d05030300a14020000d00711081194a1008c040c00018480c1d082020f9901c0729524410001c00c61 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 456818426 1250 456817176 456817199
    0x11e05030a0209041509050105010e09030909240d1b0506040b0d0507090302030a03080702010e010c020615031617070512250906081c0804050604080a030b0d0f02030106 74
    0x1118001002000c2501040d0200101a50050801c0700c8120728582581c0c10a49540100c1101d140203000009140d850006608080e11004014221079001001150b043c0d5544405c0e194000e10603004e02c84280c01c0034880d43c903185004000c0698000d409040789020000002800509240d01c103800f60003295a45042c08850b000744e01803002440790030700c4000045403d07680325582c810003a01d407941400e03580e40c000c641086000c00d002d90000d81003800b0000300304d4090240d4555050100c0081189000300d4900a40b104c2c00a070252000100e005070f002e20075507042040d6982c1c0455600345032025640c0f041101841c0f850204080c0190207070000006951502c0507400600111000142c404423440b010304002c2c0342130030844000341d4a10000b01040e1903007076101e11005802e50300000c12803d4840c1c4100d03004210b01d4004c2c001000701034401c103c001980400c2081c1c10603070103000303192100505903041d0081d1130f401d406a504602c0300c174220740a1014485081e030801c4d000343c1c002c020054031201340c40b11 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 456819676 1250 456818426 456818429
    0x20d0608030c0d0f0302070212060a05010609120308194b0203070c060e15061c0f030c021c120201050702031c0b06070f05151512160b03011e 62
    0x305600411000d030301042c0941c91403804d1841d0b170301d001031900380ba0b80e001944141202c00040e070580d0000082100040c0350f841000d0250159090286c0214174002c10340721185820140202005141d2020501407410711807118020a02000c061110048203c180c0192035104046803042e98544000c00c5032040070100c2c1401420340000f180b80d160a0303254040b202035403026207800d04000f041110703040400c0c494460301c1030511050780600055020907040100c0c03040058851840b41442e12054402205900c001d01c500d6a0b1103041d003020240745e4101641c0f45510f40d10045e42204900c04207480e524a191001c008941c850003950f1a40300380f80340204c1c201c5c1c80440e08040541d000308800540750803da000d800003d110858040740420040313000c1415a00301d08412100d03540c444194900b002030070701903400704a070100f500707806500c1c05d000940c8118500c901103038058151411604d5220805000e60940021207912040c111555040c0031000c55109103d01c0101c002060424041140341104200 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 456820926 1250 456819676 456819697
    0x403050702120f06070908101a0f0a0909080a030e010c0c0b091e01020316020a0b22020603040b0601022103061018080a06150b120424020d060803 64
    0x1400c103821030382440101e107001002003460384a1020510481001000141d00c100740c5079035020303440c0745002a00c07450071840407170744140c1d05d080008000000725401c030754131042d5800312611400000d00b4004203d20310b8030b03600007090060610580106204405000303020b2205031b03540070001102045142422900d03140144030010305190a01008241344405690f0082000000d4406143c90700c80141140f00364140300d0f07001c60350040200450008244101445141640064400d031041a030703440c514072070000d101044400d03c040043d107210f282003c8505030a079000d4940c0765a03041c1814081e0309213004550341401442212003e03503600544071618611440300105090039903c1e64400c1000c2400c1041c80c0c08204036640c1c03002c142041d14150544001c040601c05060001c8143c00c00b80f0541d0005004a000d60020075420050a00d40400721192a6204008022692a54a0314400c03402200c003602c1020031410010f4400c0003840d500900c13031021040410803010b81c1e80c1070110703168085d561410 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 456822176 1250 456820926 456820937
    0x5040f0b1e0405030d0809010e030a0c0b0f1009020a020309060f0304020406080c0121020922110a0e010c110301050a0f05150303090105160b0103060f0b120d0e01020a060e0d170403 79
    0xc052081c090540b5940240c1f41c9000400c0120b501e0f40110300c2c0d60450911180080c80c001004028080b10152040d00540710528514403490018400788240c2d1a61040c81c4040d03030b00051400035184284207032940c00e0b900030003441e80c940d0003a03004002d540080c3c505a204520b005070001c0c02600c00034140b4404241a151111003015510203554450700c0c0d8240720307241a03020410300001d9541c00c15810075410250540c407481f11803540e50072044801a0482c450814020003602410036002145084038050900e01182c480c0010301d01034041600c0068042d03010760800f424000c20b582c83d5000801949900142000250fa400c0c64a50180b1100e284c010b800d81c00030002070945512420081c40031190010002d0812402c2d540c805c081d0741403d80c004e40e01c0b590769100320100c2903000c0c01071201c643c0c411a510351180700560f0141d900c460b0350515040c2440028041d420700e85c1d00901400b0702840c0c01030b00800440a0840503191a82801140f120003c0c06000c9800c1e452628151444d000d00d405a0340c2 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 456823426 1250 456822176 456822193
    0x11a0f01050a0302040503060f070809060106021207050109050114090d0c0b010905040c0e0403080a0e1507030c02071e1401050307090306020904020f192006150105040f0b1e040503 79
    0x54a050b4000011a020507408000118050f01d0410078103001c0c00c00d10240001c5d1b8645508000e2017650098500d5506c0c0d0400801080001c0d40017490007600c204402c06990341340b4003850254014040a6001441c6508203403e031100081940201845090f1500950394100c41d00d0f8811202401241c1700200300049803001400030105682c041e40e81305e44900e016400807030719000101400382c000c07202180003c0f2158100305180d2914020800140c400900804c5070b4034204411686840d0000d294608169482e25030b114071500c204000001042d480e45050302c841e0459510144104143c024412054900300344108554407032400c5900c50003d585d52049400c0c00c3d9502c0c0400b950140c200781d41d20a809210305414220310f00c0c000d24134101109440550281e0748000903000c03080d40c102c2141c5054502c0b180341c42e00400482d0f04c5038007511009000c107c801070345c130040c0c0d02805a500f2804000c0010500403466840384402410040400170503400d01007030143c400541849240036440c1c00d504003540 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 456824676 1250 456823426 456823429
    0x6070b0a1a0301230a18060b010e0d050604030e1318170a200106050a0b0c010608060c070b1308160507080d1e0306050603090c04061e29040e0603011a0f 67
    0x4095402029040303006c5410358084504595208140c2015280287e80314a0030a1540c0c10054021250006075088008003880f911855100c890080000e800d00031481030419141d80d840c5100106c205c414001040910525140480d4582c070703500c0b0488000a090b00c10001c61b8000c03500b540c416500a64030103105550030400d80d070281103002071035240c0c0d40d22000c010410341c1d15a0941405041100b01080d01c40700d00c004442c0c25101035500c06445a0040000d100c0350144110480d600345da000750f840502d540300c18104034460508000003074010003000c80d21196440702a40341d0344425000d401101d4605440c0c1c0350f010341356091220007801080c10071601c0301e070184c0d00020400c45603015040002d402a070300e03c04515075610032100e106850301310103181d0b08549094407a481c054060285101c10010240f0898480c0207924001c07110410007400342032107020200e01e8071807512907600c0461a101ca45d030305407080512500703551440c465400c0820700c05000a003090ba02520600040101115107003090 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 456825926 1250 456824676 456824741
    0x40c0f030c0e270a05040b18160e090c0901050307050127060f09080c010e0904060e010e0d090b03101215020f07060b0d170f04051e0316030c0902030606070b0a1a0301 73
    0x10b81c0e81d801e1302501e6130030a10303045042044001003800ac90801810b1401c96100f90800105541e840d1050615400502298500044007000c2d1282800d1078220141c5c494080b03191624040c000f020140000368021920541c000720400ca0182b054031121b0b00103889007422a2509407010a050000307501c080400c0f59460403034007094100d03002d10400545c9900003501d450a50785981c94026050303002400071003400b0790101400c1d0040c1038000d1114214189031134a0190100c980c0704000030b0f01c2d440d44014060040c4030408692801031410700710f644220301640ca80f110741000e8801d8861900c0c2c040034039000e00f410300710b0720a2198080f82554048032040140c8100307400c8601d0b1107028000600001c1000e8644200c0c0d10361401341080f0500c20400d0100c03c0501d0a04506509110503681b45810800200145400030568580d8040544c80780d407020040791050040d81d202424011707548042c00030000071a0701c140e410f004088403640c01448014141030903130702d44115210740c0c00080802e080c170070305544 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 456827176 1250 456825926 456825961
    0x103030e0d03090503061008070605250c080303041b0501030c08061e0315040b060d030f0f0c0b0f0402090f060d11150406110c040c0f030c0e270a05040b 67
    0x20b00300030f16142d4441001ca858804221854a0b200c007202d002486a058200318840c0101030500e40140381c16403000701c60003800070107138415210300225418007040001071070021005e040008102c907141c4c6094248100c584020305101e0324148060398011601d54400e01038806080a19240c1300691f07100c44090102000307440c01e514101440e560515041558248400030145814088459443c03c00e81011181804040d004510232440c000b07030800042c0d00f2580382400c41c0380c0ca0804403500101c660081c3ca880c21102c00042c0354a94100403c0003442d07070001030038060b600a07a003030031040d40d58000d00800014240d821991101505540ca40007441c1101c1c59044520050b00c051a00b4020f60200402a00030780c01507004100d80c0030140c051401c0070021200c02d08003c0314140610030714400f024102c0c42e01d61548204051315160304513801c0c1e01644018404030030290003020a140c0b41130882401c116400082c01041c3c0d030b25008035000d1ba900e40600740c0561f800501c200490b4444c2c00b078450760807000 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 456828426 1250 456827176 456827183
    0x1707060e120c040204150815010c0305030a1b050406110a0206090d020f06030702032808070809160e0912030108190218130b0609070207090c03062117030103030e0d 72
    0x202c1c0442c0446440b10b00203000205580c0410715a81809100082c040001c01042441e0710b80001f03c0210702d0f0b80e80a191054400c0e01400c18540d80d0b2516011072010304124600030f806500c191142d18400c0e54403100400c1107c8080e0785241704503d03070100c010b49a108800020303500c640c0c18000b07140703986040700020404510041c210342e00701c080d15000ca0241d410803035046015800105d994080040c00c58600d84000c0c0c8044441c030300e0841d100f100a4551030014120804100b01c2400040c000b00c0c4c1000480d500650f041034030200359907121500c044150080301d42d9800e80c00f900702c40d100b8450b14441503c0c169088200944031145041d840411401c22011060ba4031100b104070f82138218044e50640d50040716087d8080d680c00080d8200100c20340005050300c3c0c042da030302c0c10802c031700360b40d022404005807406100c000c6001104480200c024110a412908803008402d0800d2a05da031200080704040348508140100d1102820307005813240001d1001801080380210790303880b103181031001c05d80003520 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 456829676 1250 456828426 456828433
    0x30609020a08151c0b0a050106080c070f0c050306040f0501061a091002070f0306090c060c0b0601080402060d060803030a111c0b2704110303030702150402060c010e071707060e12 78
    0x641300e0781c00b9441c3d44254090702da01e00741c2010b1025a400d603006c0c65004d01058148103d041c1044027403004144100d00000d4402001d00b00071204008500404600606008040b1056402c2604103d5400986c41d1400c4031103610b02040014040c2136401007039a0740352064041401d1400d042c042c0140041d40c1f4030640c007180146500403803201c0000f075640000d140601400201d40e0a603140151910140c2d800c00d100344030100f403800300003d1152090940c4208203181002c26500c1d00d2000ca01140a8407410b02c0071241801e138080752168001024600c11200400b080c00392049040b094a40c9100703034000d00450b012408000030014106803c02c6c140030202903c1e100c5241c5c2d90a900d13048000c0e000050084000c90a005d10080c409055864000600120007079455404d014002035554a820704082c0d040803410800036007950f44020070754114400460080c00503501417091603846150502038007440d1490f5441221104e20f00045081c1501c81c2c070f848400c4900140700800c00300c410b202511140b0ba10 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 456830926 1250 456829676 456829699
    0x20c090105010c0807063b1605061308011a03120301050105121306060e06010e0a0503101a181b03091b130f200c0303040602030c1612030609020a0815 66
    0x38181c00b80982801c0390348031040d81c541080004124461861f0680707410750254490040c80080d11801b40111101100d10f556141800103002c40c40e54816440006039501c8c0651004414006424000740c51504405035034000c1000c1c0c50341d100e00d0200f07018050001d4401c0c0003035101e0500e54012a600841030713560420505040c0e0f1f5961041e03e440f50080c3e4200500740c0280720440d41c01280c01289007104403005403a6500780f402203070ba40c1c5208220080080e0311180d45083c5070880e40319a01c000e00015003001844440080e4003104640c06a4843d6039402080d050f406560f090001074a02038000c0300050606507203803401c3c244c11a005158210b80c07100c202c07841203007146454482c0041c0820800c0012502510400b070300c011540c12128590403803901004140c414141c080101d07948a5407104c0016126218031a00d501a40114903400b40c452032080340b0721044c001c2c0385d08603002c9140309035000c0c880c803070320b41c030744c0c08240e0050311540c2d00455014404603280d465480b00010030510701401e0480a007 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 456832176 1250 456830926 456830951
    0x12018220203040c030c0f030611180411120c07050c0d350705060105031905070506031512030405090c18210304090506040f09050a0305070501110d0c020c090105010c080706 76
    0xd04c0d0341f1850007018560002c00070040c1074003074444c110751200c00c190b042c4280140d40d403040004079031030b4500c215a50010070b1000c07c0707060241c4400958024407a26a480c002d0032280b400d900c000e0080d6035900c40c84e8809000c502d031020700d500b8819404100100800e01004c800300c5d490b084451600075016045031b40d9040820450090440c8500490042c00254540028141403034860705d04580304804080441011880014170329003120f405981c125580d0b0745590f61050304819100c80a98004402c41c040042403100001900c15180100e41c601c0580c0c5405d0200d41d400e20801c185500e120f0030b4035081d0540d80ca4030451848003030109012004c07032559800040f900b160300c00e4025a21065881080c0180d5050078030172048400d40000041200f103032203440311a40c0f21201c504c01000c000c3c0000301e1401b080001c0d001520002d0221030f0464413000c00940520107000310041000042c45406e808010a10300b80301140d040f01e606865407072b4800700949400d049940004000c4d91201c3c1c4624100029 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 456833426 1250 456832176 456832193
    0x3060909080702040e0d02150901020408070f090b01051806030601022b110303011409100f0906061d091305010209090408070c0902090901051002012018220203040c03 73
    0x80c03889510600c2e901c440500c1008121000403c416600703500500c0c48048130380e000203201180b402c40d018125000d44e150f0802c0c43c06803040b031f04040224050300700c000544c84a121003800507a00100024400d0b40ca0000044509010344e40c098a2450032142c5001c00500b04003004542104043c03058829243c5907500c1010701034011201026140c1d0842c2e07202401c0395102c8800805030803040c01071451540f40900c0152444200340645100740d4486000c150b02680d0180360600a125907100844125922440b90b8010201881150081040044128401003040781603120f28000140f9035415512126100382d40c05000f00000c6519640c2001000c12950701c943c0c2c100c2c403440c400e601090381c0b14107600c0d000f030a1032140c0d0b00c502c0420340148000041c41d5501ca41090565500742d5542245001d004801c038050300003041a400c10402807000901e003011010f00910108813560b1020003c5a03a0070b0501c9122020b0314a21842e8004d8040b0150036040c082e002150001c3c0108482d0109a8480d1112103d = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 456834532 1106 456833426 456833441
    0x1203060b090d021c050109080a1d150a090506040314010b09090d05030a110310030201090f03080f07020a080d050c0624010c031209060e07050d080d090201030609 71
    0x2c00b81110b201c5507007520b4000c0c0c001d001101031f03800c0080c0ca641c031802c002400205094984415148c1d080d8401501c0100a051a02581203050361800c054215005042c1002806807002403d0740e120340144c40698025600c02d00103034410880c00c4c0c01c68488041e102d0042c1c0072881000001c4102152601e84607400f4140650f480d91807611080050079601d0090614420200501c4244001110f801090728400e032142034400391181075070101441c0740c0c032008080f14010049812000c01c010040d01040d0310191920003481c0d15070084909010141202000043c000b2860360009441004800e07000703545580340c400c90b0b10480d03000900501c410180719040c0320092a0f01420140700e1048000da800259500b00070001d11403a0401c05440f24981400310b038030440401007080c0c07501016407040a40c0c080c0003203180039202c0c0003080c0600600d040981c18182d81e40c0b80092500c240d07008080 = true := by decide +kernel

theorem cover : BRFrame.Cov 456654676 456834532 := by
  have h0 := BRFrame.cov_init 456654676
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456654676 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456654676 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456654676 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456654676 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456654676 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456654676 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456654676 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456654676 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456654676 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456654676 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456654676 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456654676 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456654676 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456654676 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456654676 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456654676 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456654676 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456654676 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456654676 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456654676 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456654676 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456654676 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456654676 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456654676 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456654676 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456654676 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456654676 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456654676 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456654676 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456654676 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456654676 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456654676 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456654676 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456654676 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456654676 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456654676 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456654676 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456654676 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456654676 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456654676 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456654676 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456654676 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456654676 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456654676 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456654676 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456654676 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456654676 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456654676 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456654676 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456654676 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456654676 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456654676 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456654676 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456654676 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456654676 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456654676 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456654676 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456654676 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456654676 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456654676 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456654676 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456654676 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456654676 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456654676 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456654676 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456654676 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456654676 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456654676 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456654676 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456654676 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456654676 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456654676 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456654676 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456654676 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456654676 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456654676 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456654676 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456654676 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456654676 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456654676 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456654676 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456654676 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456654676 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456654676 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456654676 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456654676 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456654676 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456654676 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456654676 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456654676 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456654676 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456654676 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456654676 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456654676 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456654676 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456654676 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456654676 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456654676 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456654676 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456654676 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456654676 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456654676 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456654676 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456654676 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456654676 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456654676 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456654676 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456654676 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456654676 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456654676 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456654676 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456654676 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456654676 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456654676 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456654676 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456654676 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456654676 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456654676 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456654676 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456654676 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456654676 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456654676 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456654676 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456654676 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456654676 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456654676 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456654676 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456654676 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456654676 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456654676 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456654676 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456654676 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456654676 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456654676 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456654676 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456654676 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456654676 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456654676 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456654676 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456654676 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456654676 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456654676 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456654676 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 456654676 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 456654676 ≤ n) (h2 : n < 456834532) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
