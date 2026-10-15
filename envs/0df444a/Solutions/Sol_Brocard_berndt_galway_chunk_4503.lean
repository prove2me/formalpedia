-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4503
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T12:49:59.65763+00:00
-- url     : https://prove2.me/submissions/891c11a0-8bfc-400b-a447-e3f5585dd452

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 809712230 ≤ n < 809892086 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 809713480 1250 809712230 809712257
    0x130507120e0f0303270303070e04090204060e161d0105070b280204031b1a1b150f1e010b0a12060303050a140310050f0d12050a1202031006 61
    0x1000b00015050703400040d640c69044c01c1004907401010076444420000080c140440e10aa0200c1100e014540a072100c100c1c041c012420700000e4a07482c001680d01c6669107900084056108020341d1050b00800c8100031100484100604007004401c80810320b9001d820708a41c0302e036000400c0310400c581001400c64642d403200c40d403003901d18500d45030107030384011961112014002500500281d82c0300e01540c0e0309040b00c04488460b007280c1c03449400c80310070080040d02401161480105107180c0c1c0c00703100c803a50141501e005840c1040852903580445036000801804078044c50f00030b9000242180f5003010818200d0404a5044040c0511a0256000a4411140c501603440007144000c02c110600c5207566a007400b802c6070308104081004590005039215407a0b1301c2c2d408a0744501d400c010b11380c13a198140418000c041003028022034100d2503106c500c002166150358400c85015442d510280d0340d145003440100346603101c0061440041c018400d00150740000041d80083c2c9a25191034030001990 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 809714730 1250 809713480 809713483
    0x609062a0109060b010804050c150d0e0607030b220b0f040e0d18060206150103111219051e0702070b0a0e0a0b0c060c031e0a0b130507120e 61
    0x2201515040c01014012003194041034006050203406140c007009424400c10055850b140125001001074004403080d014501e400714400d440300098924a909010200140d0704c21aa07150740e0004656000d041000400341c2e00d03004840003198142c1d0408849030070340c840a090307907900380950100b075038680c1007910a135160031010000e03148004100348480007501e10190303116241805c2600010322100c810540300c41e01c2585090032550154000c00c0c07941d880808c0c694680c00c4880c0c8490401d17441d0750405122040490241202405158085030103040100120384400d815242c0850407a04203410486065000804004041020b07000440c156503081c00407402e00080707410928071b000000c240303e014039a0040540c0e15440c03060316040d1050340c43d80314886090160818600c607543c03100000855a24540000d186c00c54642c00000412054101c44030701040c008a5190048940d102c95003045850046c0d140ca6042601190801050030038040c010020075400408085650701c0c3c17108504150f00 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 809715980 1250 809714730 809714767
    0x16050403060b06280f09080d05030c04030c03120e0d080906220602010e0708060c03070c0602040504020a0518240f040e1044010e060a0b040e0c060906 66
    0x182500440c00e40e54131050540d400030b40800e0300d20002028016091101e5000702e0a070021380382400000d02c644d04500004071240e91000308440d410000074000040085c545200c4107010710b00c654110990440104801400d00001c081064800c010350140740c004520103d0844042e8a8280c0762156510600e0544482c074581c90f426421029159000c0003c03d19419846480c4803058602540c160641d034019469480d1000c1d6521109504200041102140140c1d03107451a07910034807026007041e503183d0000742280c2000035000081000080c080c405110107090001283e842151040340d88814580c03448501c0b00c08800c019013516000962813024650201943c1c010460140d814580d0324100c0003c400d242030500c10b0010700416140900c2401c88024606800c8000c0001e500800a401c50010480039a501c01540d80c00c0d507940007000c3e06040d0501000344039039420980450a060321005000c01c890f11010900030390b4210025249070307551000211413060100f1a986038407a1a0075511154401 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 809717230 1250 809715980 809715997
    0x61810060f1203031e061701020309070e040c0e1620060105010f031e02070201031d250e090a1e0209010302040902150d0e0705040c08280e030903010516050403060b06 73
    0x118140761111482c945034115400343e0b031f0004414016142c101c00c0c0c9600343c0c081526000d605070440e034018041d19a982110710740c024000d50190134038a031703108882001040140c030307191504048002a0324145420880f100158080217094072103070404c070003105441e10010f000356410400000c15072445244070b500045004405104034407208005014070764000d5011038001c90100e81040e0769500b00c440b05003108120040c082000d8851361070b540201d8034000c2460300051305440714000c804104540b0102c80e03288280c000e10001c003150100d9080120100a071506484008441400100016158491b550341102d5040d54085450f85042c0f000030312041140c43c1050020b074000c1000480c03019103030042c0b00300a803100e0907241c2003070325442808184c8040303070000008038100b0004501c88040040c44410001d4142480084003400400c51500f5240200340c07442041e400411010a103150a1240743d400107208050100c0724984460042c025000b00e20018140d595242c03043c5a00351a05001c403003100 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 809718480 1250 809717230 809717261
    0x10605091f032003060301141003110114030906091002040b0901030e070902070506010906080307020d02090a0b03120a12050105010c0f1403030a050a05070f08150a030203061810060f120303 83
    0x3001c0d0710001c0d90454000b115110b2096091a0848000c1c3e030a44c01810b002780c180381c00083d1020706688484000369001021241040b88150030340040300580c030003450241d01090b001e0042c906280c10344515090018000307200c1140b040004220800303044084408005080c00c1c0840c4007a40740031403a0038a10154000740035030b400001c8075820484003150403070503504403000801810751103554a83c0e682c01940c90003908500e501000d2000341ca4001e03409a8080f814030004a8081d484c08082400e14928905000c013007400410910341d45900054891501c0c3c20080080040b50f240200017080441d0440e030103005640c0b8054038200340aa10441601195410340032a07a80b401c19828041c010700040302d9480032285021701003042540710320001e0780c0040f082e41c1c075001c640d101c80103842c0b0030001041c9800d80c0306440c840c0000c0140c078217001051080d02d90700f01012509151002c45030a249241000085240c58001d050003a140e404150002303540f0301b4040c64440041d14602600142100c0c0f4944425 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 809719730 1250 809718480 809718521
    0x80306090a0c0912030c3002150703180507060801050f030f0c33094002070c030803060a12080d1d0610031209030308130f0212060708010605091f03 65
    0xc00304a000d0340004414400d2407c0b001051074100b207032180369481da5070105256040100d043d051181c1c00a03800c60701c2c1c016220801101d035548207490300090343e01207000f090046004221a180604541d0030b00c510aa01038003c0809181c0015140c001600d00540704100d0001d1a910058203042050030f403083c0c5404500c9496100f1658014580007400076611a10f0040000503038846000e00b0703c54910703014000c078540e210f0060f4400413000c07428406200156402d000c00800304502442c000000c1d80143c6e4035a03542c0c106042400503040d40754110080641c0d1b540d1f0001c00180a44084030340350030b0b500a00151403c500c80703210070300c1d20700840e00000e5403084406208101094040d254100d81c415203c02843c03d24000e01514103103098480039000c03603e1100001c0781d2a146c2980d03d03080318030a5000390600c400ba540004d940082a503101e0b40746502c21420801b420350401c2c0c4560140c5141d0502074205181d00000440240104d9545c00015101c0303444550002d01035006149008100c00d041e090 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 809720980 1250 809719730 809719763
    0x70602071d0a0c0e1c0b0a090b06011d0607200411040b070303060e01150306080105070f0e040609091a0703020f0d0b03011b03020a080c0403120804050a0609080306090a0c0912030c 79
    0x108500c176140103031000104000032518a10b4988034844045a0000364602244c0d101c1c001940c04d40c0706584454410401600307000400d80d218001010b00510452150100e074a4121803074012070280c169041c0203506d0151080c03d11801a0140d50440c0d0908022030340ea441c0902d421800741445600c001c07140c015840001c06d5001c0c41c80161624213805645c104002503a0b10103c030b0a94009884010100703086420201100e072254031031840740c090261010400c0da695094030003c4803065031007501c0300d965103182034492607402c202490f001141d505d02076007021801c00703c0403a40e01c145101e8a410b55510586203020341c070300390044140710341c0c40c00880c554455003a502802941c0680b214500103091000011144c0340d00009481c25a90040180b03070003540d001e03401f0f4030110405041900c040c030600c3c000d00e000451500403101d5591150311901c0c0c403400d03c40c0611180480141c49880341500307056201c41140d900082080031075401d0100c3c1c600e0165281410b0f0f079141d903020409000981030417154003 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 809722230 1250 809720980 809721019
    0x11b022505090a0b0103150e130203210a09080105090c0607150c030b0a050406031e081204110a0803121f030803152b06020a0e03010e070602071d0a0c0e 67
    0x1804075001e803403e22540e507c1940e41004141031740a904030081048010440118400e11081042440a0100c0302c100e48071603194034150929404c0e06a0814001800d8040c10f40e04c48900e000504a1400031302040c1001116192240440f40c2c940d400340502060300c00c1404a00c0c00031000d0300662803005c010701c1d042c503000100030f4000074100c40d01030450381800203001d040c548a030380201e03504208003021401000080c160008004141079a07156028000300d000100c0500c0349a001d68132402600004056036014032880d01030360790007200d8540003400006401c0c807444040325070010380741401c81f44d10980350500a4402030250400381c0101004003c00074190040507000c0c0c1000412180c15801c40401e070715011224001c8400b40021091251100000590130f030090901c40c0c4050034950307641034202004c40e084a0845911080b00e6101900401c00e96806009403030140c1001300035a0041484c00910a02ca80405010a10429a9601e0b1041030520079100c3d19a102e0009040c007400510300c00859 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 809723480 1250 809722230 809722241
    0x4050708010e090c010c12232d09191a031e060d080309071502011e020f0f130e1e01050904031707020a0602040602010e011b022505090a 60
    0x800b5071109000c00700b00c031504001040001400d0503903074003000103896a40c4400a0301c43c0a00c07503051284500c0103000250b02c02c003000012144001e12030362a10210010403c00325602c1c2e00001480240c010901d0f01070082c01c0c11103441150a50340e480d1010031043c1c0780d12144245510104241100943c030115285200b801580250f05000031803515802a81c41000900e0003a10391239400030210340c580d400548400040c6174000d8140381070f246120350b50413500e8410840104200c0061750341d07054217903800300c0e07015098894aa08290441c1004e1039041010241e02c030700400481464408103860408002c410781c448040c0c0104420050182010b4801c20b240205240307200e9600901c510010500d8103044696501c1507405550f6071810726100c00600d68802009000f18003140140180b10012443c240014001050030381d00024001e11410b5600e421288011001142035a10301c0c55981c5455000a1400c21123950441e841c213081901400c00c0c8215071694000b03130308000c0540c01c10140585c5580b08 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 809724730 1250 809723480 809723489
    0x181a0408010605060f0405150c1e010c0e09011802190203191701030809030a21030b270c07060f0204030c14031e0c0603090615010903050c010813020405070801 70
    0x81c04042e0301c070f10400209000b0501c001041d034001780400c000c0d501d020141c9000c0f4514090107540783c054070340705483c00d04144490b80d031840203040079900070140c000d01c98001c0300b08152900702c02019260000a60180040c41781102c0303c0900390360068400c1d260b40c115140503805800d10f076241181e45c0c40180d101d403c1070400c0d10301301100c4016844c17828060f6485e06400c004034540810103a00b113658140440c2c025541094041c412009403030009804199078600c103000c05043d03000c030780300c0300032004040c0c0d180d0803100f0b40950711702d03425118024150928a5003004e190003482c2220381d030f0404212010f028461000d4403850030000003d00040e038590081c015a4010f042104209403544401025050700001c0c0e280c150b4001003003169a103c15030b20310b1140c562000b0507030385800001c000040c401e80042e01e20f0702c015000042840b02520762160b13070070b614480c00e00b88400481e20359150161614404541c850600500c0c0000952801030452400d500c1c0b54014020046810403000050070881c6c24000e = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 809725980 1250 809724730 809724733
    0x1081e15031c050d020f0d2a0f0c0b07020a0506040807230a1b0515090a0911031b0909010e06040b040e0a1e0501020415030c050702090106181a0408 65
    0x840d205119140603006081c00980e0f2102c41c076104041503000000e501816204005450610049007980d10300d005604241d0110342e51020219a60901a032281c216040305100380008030790640c2240703420200310001640c100104852035954603070160304121160130300400324000c40b81000300b001a840c0203055941c0c091085001d20340e6910300c1d40b410400c00310031411440e51205c010303540003503420782a4100040702c02d14900646542c55002c10a0003c400781180c080d102c0100c1e0060480c20908505030080c2401182800500c0034100c000c501480b0240030a40000e032010000000368000d1801c8401c52000501071780303586d40e035a40350356042110568081c0e100e0350802001402c245060f000d00172040150304c000d80000349180c0d81d03440340030310100d52200480c194000e101d00800c100b0701c0680010402c40044c0c4c0c9614410210040407580b0304499801030210a101c2e000c0542c0f5032500c8941528030720306103c080712903c0d80c000da1580311103a0000c0f40e4618801c5410249100b4280900115440d490 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 809727230 1250 809725980 809725993
    0xf020d020a11160e01032a06113c070312030902010e011106071b021201051605070b040605040807060906150b1c0203070c05030c03070c17070501081e1503 68
    0x41e003c410100c4603100b100c81c1000c2d180e0062001c13442407144201d0300100204c801201e00106815014907003a40e91108010891200c0d1140c10a1420300c1a0034010300641d1001098001c10011010108610072942c0013402050034000c40f02c01d000c00c07140700990340100d80e0000300c1030311b45402000b51051100072800100c2c03102071004554000d80c5421958441c0001500c103a6503031003811a40c0355040940b4041c0303125400b8400303001d6120a882c401d00c10000100219003840c0001c94030342c410324900d80c480c00f0488100030390408124007000d19030f04958002c0011600741c580f401c00a00d9400303401d40140c0a01c5c5005c0c4124100b08107030303200d141074a010008244d502c0b41d03100e072051418002c4442c42c841114452800300e4031001294000c540c0a400760801d55a460200d032150761960704140c040806d035910001d00b01c000d103c0f0381c0800c500202110040200003900b8a00f456494100a10805040c01100e40c08260706048881c1079405e40c3d01103042d48003a03458008480381103521409284c5000b0300410 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 809728480 1250 809727230 809727253
    0x8040e040b0402100305190c090f0b0a02060906041a0402040f180302060601020a02030303221202011e06080307060c0e0303070303050103020f090615030402060d020a050a020d09180f020d020a11 85
    0x9011b00b51051000340f41026581c003400c901030018140032032520b03081100310308001c544903800b1014200a00240e50703016071200c5401d00040e01d0444068030700c0c5081d9110000f0000090030000048915915040c881e068030744452011901910700c4440b07a00d01a410306180211075000207035030030021070080d801c642460300c8803001681c40300320050001e03405801c1040000c049110400c101d0b100428061800400e0f201c07541c59002681e840d44c1d42400050751225140403030312082174200c15450703811b00c00c100000392030469400c1c0d880c4155140102055152402c0c90100c6008500c000e103003007c0901580d548070582c3c9130040082c04240000c078801c0780c0c01410003000b410300101651140f00d01400242d5034211035001000345800062040380e01c0704080209410012050001d8141c500850302c07100e440d105264406800d020b210f43c120006c01011030740c01c2000402101190001d400821000910a046145c000740a0300c03996890034901c40c000100003540640c0400d00c10750206402055449103800d1 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 809729730 1250 809728480 809728487
    0x1b0d0f140f100905040807061112010b0a0c110f0a150305010b0403020d151e050403020d03050408160f0206130f0f080309011d041508070803040503060a0908040e040b040210 76
    0x1940c1d1a40d10900000b014402d926642e0b0001e0b402602500c02641082519614003003a20340c0b0020384488c1ea0404511030364035074007200d1941d01502c20303c04814101001c2c200001c020240943c00540700503094840c5606e59181c1c1c00c4c0daa561044060321044103180c4030640070000241d46900341e00024680700c0002040c2c0d00c0075064030180d0b94010b014444c0850552500c443e800d071081d00d0540c0300c9503281b0f04940484c200e4101d001880c0001c01d8040b442c0d103401d0070003900b0046060742140030705042c0780800c4001403400c02114280d8003074019444d40c0031100c0c1000700160b0101c0030b00075000200010380407649009a0400005c541e20f02126180f240e0700d91035010601c0c0e210788103140c102c3e801802034803072642c001c001d01c10078240d58003102035400d42c500b0000780903100e0401c0c0c0900c50804050043c8480c0d88248034110213400f80c1c0000710b1a00e850440403a513036610042c4101c11507507a942805e02005140030840b40101030f0b0400180c0c8a040c01d04040203006030a880882c0320700c0801c240c03071009a00 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 809730980 1250 809729730 809729761
    0x1401091a0d0503040b09011704120e060705060403230408070e090a0c05040c0c1e110604060e0904210908100b0603040b1b0a17010807030b1b0d0f14 65
    0xa118003c3c6080600c0e0084103217440c0c12408800781440b0350010354405040722030400754800d0307025482d000300c454a460701c044d00007c02d0700c10b09802a43c0400c41c09010410009240307030803da06142c003280049966030411154040c500c984000c00100083c00200300308001101c0040c3c85106402101d503071100b80743e0396078807809018001c1c1081c80d298010000d0782b809510420181d052401e01106108450303a94055581205401007081584c1c0c11449050103140c12200d10182c0e8180c48042c605030801e10090000b01d9000d008610030710003400000c0407c00c0c00c210412010000d440e4203000318150010140c0403080c2802048a0344c810b00c00040e100004074060050000e2010b00044d1542d201d544661b010b0b040001c000e20b0781440d0002403070400030307845002840e1400300da540300c1440e50398442210121a1040e40301103140d601052080c008200e05d8901c040c0c00a24894080503c101d0030945210140284500c025965150080307042e4400100d400441000d1034145400c035056480310350004510302c = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 809732230 1250 809730980 809730983
    0x506090304031502030613021617090a09090503120f0403080906070801091d0d031a030303060f09090705041b02010e120d09062909010b03090c0607061401091a0d 71
    0xf40300c1e0f441c030b0034100013580110b4110380054914102c00c00344104040aa070b01c103015050400b195030550174140214200310f54070321740c0301b02e240c1850100010009580d0080318000c3c1c0e812941d0303c81c2c1503810842d00708100d508109a00301f004202303117400211202e05540031181540821034000005440d03200214610b4460304032521600c0c000c0e400d01008100034485034041c24071003404e108102e001542e08001c2681c11081d10b603404110f8040900710601e03070218840080340243d00c01c1c410b00060341d44c1c149034090722346020745000081e0765032803007050b140c410954030194105207000b03289030b4100c10a071020224140960002d000e18840d125105545a2002c9056000e140c0144140e410841d20740d08861103882c0980c0000c01c580c10303520320303082c403242000d010340044000a036804106420071420f454010001034020908503d01b900c0d25507180e08481c2c000f10710881c0001020b1041240302d40c01102800c0d5114105501d03507850701c04440040c04140303c80580003880d000740c0c0c2950728000c080400010b = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 809733480 1250 809732230 809732243
    0x1314010608010b071a0c070f060605010e120304030f02190e160503040f08030c13090605121b01200615040b030705030c040c200a0c09062405091002030304050609030403 74
    0x340324080c1e172100b0b018409031200f001034908010b41000f080a03a500011414002c04000071b03042c0c9000005030544903a80c50b940e0148035220945030f0425804025507040300d420143c03000021019100080310900c045a02d6040c2d00b07496000426903407140c0c0b1001c0c0c41000c441c485c0c04002c0000c05000d80b81400b0440723008050a8103840300c0f0001500d400d0146811000e402149828500c1e0707514004061000c5800116a49603600010403035441d05828901c4040001005000c0d1503001d181e0580e88011011040d03814001001c0006104184514580303030a0480c400546100382017840c010b05c1c08503d0460b03d10311403410300018030000e103004104242200c0006004241000c404001d00c005441d403d2280814004660402543c2c031002044c80c040c8021190094100c0380080d2401d0600c0100340e401c4a8091881e1410901480f580d2201c88160a001c10741050f0980c2103440045410303101c1c81955a400081004000841031f400002641c01103100300d0075164155101500039640b802079200203401d1 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 809734730 1250 809733480 809733503
    0x302010323041218030b100b030c0a0e0312030106020102031806070905120c0301090c09050c09060301030303150f180e010c08040b13050703120314071d1314010608010b07 75
    0x103006120f0551445a40307003442c03400008a40100300d48000f031603205071901500d040c104080d400b8984454006072210b14661070550401130354251490040c2140e800c24007925031607001d80740da000c011290038681d0860081707981c0c0d82c440300028040c3d08161150846490009000302d4048404107401e48a00066550010807526100410480005540c28040341e40034001c04046191020701039618410301900c9905071203890311100c0400c80341c00810000e07031508180003e8040d035503040704880c112034251501094541032301c082c2400c0d0224640c044040400c450000103803442c0074802490308088030368801c20130320620790162800c1c0d41c1101384800010b071455002030000360601e070106400c00d040d1800103004440e5607035514600440c03a007040d90200c601e184030011040e458010341d11504544a00100c140c10a4031000d000361840101c240440001900c110f20240c030381c207082040b8503800361024001d061001d11540c0e44408280504000540000d00101c1c2d07000d424001c0b01e952560101e4200341 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 809735980 1250 809734730 809734733
    0x10f0c080904181407030b07020102121b1308010c26010302011817330601030c032702040e030414060d0605190806070906050706021b0f0601030201032304 68
    0x1400481e869080d151003883c544000300b079541e02e15044000301000100707020b0342141030034400d224000308183c0841e8010000d11000841110312a0380002c0c500550a038041c1c5184101c42d03c5029280000304100680c1000007000c1c28150001e4144040740d071100010003154030b21050803c12a40451002c140382400104010f51281050301e8280c01817025842240f46c9400c0181802409048008101d034080b000319030711802c842c0e40b5102e80d000d148444040c004412860074110607402090301d41419610708441010901a4200c07032140b140c3e8030300b280c01191110782c1408401c408000c0690040d4035010b0f00d0804240008102c500351100c51008810001503901040840e51000142c2c540e15611544001030303907200c0b40e48501400300c4144d001500142416200340c03410784010800300404c6880ea07c10411150040704680c05c03d900030030003507503821001145240600c4c0121245003d031092402d05000410041076060680c0d100340c3c4e0510000382074100241c009411244031114000b1040003080 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 809737230 1250 809735980 809735989
    0x7030c0b0705030405100215280f15030506041a240a120b150402181201330e280603020909031305030d0801031b080a0809010f0c0809 59
    0x140c802d2040380d1074640c0710008038100c400345110b68005a4044000240c618010350f91665010b03103501d08055480034024a140c0300d020305c940104241c0f95a604000074240309940015601c507608441580702c255a0780350896590604680c1550300344030b43c2110b00c196070f408610b0f0a01410b511016041c0404080d203190029901040070300b94040b03540c40002800c58154030074000e48500a0360800e206140071010988003420714414039205920406c00d01c89030300390003040120000d00940700380440b141d5004280b0300400d01c00030b580c22184800b1070503101304000c1c041e20781507403540d000c06d6a80482e610400c0200c01803003541c40340c14800ca070380c03c00005254089102042c401e1000c4000c100140c0e41e03000705420800a940070041e50f0030024101c0040054107690342e008020503401004500b5401b48010038401c010b020092690061142e412200110303583c0c000d001d4407145082c0c64610b04a13103413507020382d4050315072076000c21400d85441040d540284d2141c41c3c507540104003180350181070010007 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 809738480 1250 809737230 809737237
    0x2c0117100e010e041202010516030902030c0603040b060a060305090304030f05031303150c081302150d020d02040918030c140304120f020306060901030c0605210a0c0e0307030c0b 78
    0x61803680503800001400c0d84951640d18000c05280c110b4007014102805d01e21783e2411260340354020b6a0500017032240360008440f150310400d61030301e40011a03210910000703040450020066034804000f1040c081800140803407c0c6c0181d40c1100c401c0c40442c2e5418042c0c0540f082100c0c840e0003a0814002040400c801c019580109031288007520f00d000b48001d000c21000449402c00d50320300325038182c1d074180b4801d90701c00c003600d4450b681050780c40c902d828040301c204c02180b03a50003809000e84a007490030700e40c42d80054810f100c01e00f050035900d40022030303600c078004c1d0000c1c07095910301424001c036405111007420903a50b1a80d0940ea030345503800301c251221981c541c1aa21140c1c4548405c110010f401c1001401d046080c034414466001030954500400d8174150028000034854454400100001602c0d40e074014104c45141c18071980f500410301149180038101035044e914480c0c62010032440d03201c00d5218640145454451070501c03400c510a06507a5121404010030307041040605100070b5010f88041c = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 809739730 1250 809738480 809738491
    0xc0403060906091406090708010e0304090f06031e02040f0b09070804110a182a0c0501110301090504050d140d0e030c0d09080f0102091f030605040c2c0117 68
    0x4503409080c0c0c1d9034546405420034422032031760010360a0040071082071007404024107031040240101e200040e2941d4480c81184079010583d903990018030240040c58220030004c41e0080414448505808003403020203441070412445940f42c4080501d1517074503440b40300080d00c40648401c445c1e07a100f1005881c240f20181042d00c00c8039000100c000d0300d0b40c0b814000c60140c1015402c12403a03613040800c40c010355402111054414504043e003a4100040100c0302240b0020391400280000103420b00ca80108011903c0790002080080042040c04207a00300d07a000314450b10840e0b000039610a0120b80b1800b114012100800d401c00c11038100d4000703500140381ca022070b041924500502040c0070f030300e0404180e850001141d4850300030081d02c50107001200501c845c000081d40740c608818001140c9080c045646030902c2030111050fa40184690310110150801400810400390444e10150020891103080040c164880b03a44080700003e0501e107403030b00700c030684504400c51a81c40f1107900000c001800d = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 809740980 1250 809739730 809739743
    0x10020c0f15221b09140f06010c080d0b09040804140301090308060f030f011d0f0a0b010306050901200421020a030305030c07050a0317010902031501081902031f0e0c04030609 76
    0xc4071640780c40b82401001440341c013030000381001d203a40e0032540307400c0000e0844846035055410409a642c02804644010790300c0022142c0c1c07040c40080b03400042c00d04813585a000300c059000c10042000c610300900c252030000381548200500c03941014244ca425102c014000342c50203000c90130340d0070310168400c40000c4c01001e41d4410904084594212207486407801a9145000454560b10000b0b00c4251905040503000e02000381c41070315400c840c00f206110007003119507218001404840b083d80a400148070002d50311040c1401c945030395a964120740942074881c0100301c0a12aa802ca108081c1021603000c0c2c60b00080e10b24684043d01c2903003000b0506807240c00c0030040100052030500c0482020b51003034451f45a01141d122001d00c000038140c02801086204209210b884000c0e00e01c11051a90b09207016801c641c1c1d10800b1f0700740c94510505500302d040c008018009604a046800c1c6030b007050b16207210303101643e601e89500090f44145c4003508007420402c414000b04009400103440c2500504 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 809742230 1250 809740980 809741003
    0x40309090e0d1b0203060c07170f07110d050f060a0c110a0f03031112150d030c0209060f03010207060f11090d06230103081b0304050a06050c10020c0f1522 68
    0x4010a01b0a80c0454040502d07110000b01002000021030042060b4002040041e05124070344c040700c0031520803c10041c040148003a080b07000317692100c0d01c40b01001c0d0f0150030b44030321101c2c0301902075568006459030002e5900380b1b140a00b2051040c0000003602c4100e100410031000261910f0240410415007681050b4079100031011400240e001440c0c0d60410103200344541ca4020789068215500c0600c0034030030b0311004c1d8500042603015141280003a011561400640c8540002840c081006c20003d03825500120f8002c051000b5070348100d421180405046c44611100320045015119082c0d150340c0c00244140c80358003060103980006a400e4420945400322411900600350900c800d80c01222a81c0c800140002002c018001d031007174201c4020300840c2080d003420700042130000d590103030b90304002c8042040b03210002c0c00c01501005060000d000c41d87e41c408d03600815119400f1911681d002d1007841c503100040c034200c3c034604e4403039802e040e008448044152282c0d4802c40d02e15905445074640103 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 809743480 1250 809742230 809742233
    0xf1b13060b0a0203071203140c03101502011a091e0a0b1c050c010e030c01030e01090c091d060f070507031808030307090e011d0705120f040309090e0d1b 67
    0x96005025080b100e8000b1074850100740b80107142261a1003040781003604000340c602c40030030903030301b00750300003e800c1659512540e031000c01c1a5030f0600340d0f000e240000c0341403090101c025019400111080a00d950750714880c0011403e0210b008000d4031143c8801812a0300748218040c900382e00c5421850269011812600340c40001c0c04100c95241011a01c0ca4112160300401130708000d44011a8000c1c00c20104030806800040d84816551102606054803008424061903080d840304130310313030381c032003500703054291100c5080b401003007076803100300080024041412046100044491090140d81c00b03e1b086a80ca4103402c40342500520401c40a1262038100222800d0b4903000c1c0c4009070400d00b00440d124a043d8000502120a50344070304600e041c004018031051840070101203003510012143c0c1c00c6601d80c404c0c2205c040c0308040200d620350000205001d0180d0301d180020340242d000b0741e101ca409a0f22000c100d030465103100d40d00800e03a4480c40f90f40700d0550040801002e03d10a4400078401e04030075 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 809744730 1250 809743480 809743499
    0x20a020a050a0506101e090b060d1d010b061204170913051005010e03060406200f070b0a060e2e0e011a0307020706080a090f06020307020f1b1306 64
    0x42a00f10b860303410080400201411400307480000300b11b4071504801003005015001d1034003680b40650500d19844001c0392601740c42c0d0b401203400b041346601c0200140341c8002181d1a19118081e0305006550800c50404040d01d040000e46141c51080440e005860720f603541c400c01c0c1800d1204540d640d00c403050050101503656880c07020072201080c207010034145400604403144220300c0c1c204a041c0510880b03640c4058400260702079100b50703c0640043c15950031000f80038101d01141207000c90050010b5111001c0150002400f8a14030030114100240c0750810382c1c000780c031b0842c094881041040b4000650301b80c241a000031081e20180845d0701020702078086c100e404c5019070003950300e2405000041010302689803100101387d500581c20707400c5081c601c1c4d00948030000741c4940c500b00301c50840850140300c0343c2d03403000003407d600c0000310500303250920302440030750000c039200c8000d1700032807030103e05d0004003041030340da05010311000b140070b090400100085241c513682c404c03040664882000c21010744 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 809745980 1250 809744730 809744743
    0x21090b0f0601090e0403451a1606020403030909111204030e2209020f27090c03010614090f090706050a02100501120524010b0a11010915060b090d06020a020a05 70
    0x25001c2e610741150f81855000100445e00b0080503441c4c1403911400c02c10345c8c0c2140541201c80940d0714a00d543c0b2090b40c0001d294001c040b1402800d814070002d400010107401c15940d41c200c4d8900881440140703642000340855000d1b1812444060012000003000030b071080140c112501c0009001500c005842550920155178174030581506594035104001546050b81104c002c100040f95804144121a1a80340202010300d5418414900b13040200301d003810700340300b03911041d10050000c00c0496641c0c84941e0850340841a070b140903060410101d540712140748442c900c2900d0010041520524190084507154007800f004011030050304c180000b001054001e49000b040300c2ca052407000ba26a05000d400c1c213000f12800c008807900139421220710600e41c419181180c04e00f9141d551124a11141900c000c041039120800c2540ba1206d80c80030000d0382c0c1d089044102d10250200011910340310301c3d03015403040c441d960390301c01000031580e00003503040d80041081c0c140c034ac410303602008070b242e03102441d014 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 809747230 1250 809745980 809746037
    0x1090f0b01050103110c15091504260703140d15030c081c0207050118151805010203040b0f0c0316201c0204090321090b0f0601090e0403 60
    0x9030104010041036a15020710151000c1542c1102d191250204906075100460005000106030710000515690428060002400100b114403025072500d45001c841600384514171500452020203140c1e02e02540d08240c07080c1c294592a40c03050402d0003811104d55800c000e45020b5541c0e01c800c030085665056040310300095205103c403d200606000348942041d414070b4020b40c8007041c203904014031582c0085d2450071910300b82800054860100d000100d000040d800142c24040c0100c410341045a000c0c2e04100700c450307000160154641c60310012600ca12540c410194607841c18049213261201e014003c1883c80b0140c07044a2400801c0c40f0405c81084000c3e0f829240500700d0048980f01440004000703c410f0000c4514a000070030710000b100c4260550540030340070765622074509041500410b902245038140709049440800b0002e01c4a0107800d1350001241c5180701d110110314800c103125070305e078050007058688008040c1081c8103501e120b500103100b40d0401c005a10380c0610b43c15044581c07541c01 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 809748480 1250 809747230 809747243
    0x141e1c05030304050c090402130b0d08041e0503060c0d1508060112060b0901051305130b010b07210819090c0e0105030d0905030c040b011103040909050d0306050607060e01090f 77
    0x786004e0a2030307401c040c402200140103010040030030005170f40d02d0709030150300c040700d84001a41031000d074081480054104001401114000707004102e40c448010300c082400b4410b140250300a484805150321110b0599441c45030801c2481000194202500700024426500b6620210540d07140340381c500d040c00a901084035182c008265a040c000680940350840c0404c1e0741c40c00712549800041001e5041c1c140c0252141a50740d008960400700d40b03100c41e5001a04450345a10650312005a10b0b00b5504c45001140d0341d03691014189414500d80c0440d1075281c40b603445518803030352024210456100200c00040e5000d2765450300764001200c07081080082d014031110004135605001c103251030005190741e400107000322940c0030003681c0d9001078540c40a072415180428202c603207400684d071407581c4110b4442c46000110303010078803856551210360818010301c102c0d12000500365003582198994041e01ea04400e082066001085d11a0400154101040c000060000281d200c0050f92605c0440880e400c = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 809749730 1250 809748480 809748487
    0xc051e0616110604060512010603090203071206090b04060c0e030c210708060a09020f03150c09060405030f060717070f231c060906050d06090302010e12040f141e1c0503 74
    0x241d047c2801e6131800342c565402d0411a01c035554000968902041c414504440d5020040201700401e41e0018048d2540c809041034060500c1d1400201810b42511007500189407284034030740c41e290009070002d051030b0281442d0303002c1c039000741c2c2d17444034030031845500155124040340000c0c0d1035401c1264a129034101c2c80300046000651042041c1c1d04850281e0f2440380d4441d03094002007030304c217201d4240c00410806c0c2c400c1d65401050040303196401980e0056034980582c400869400401041c40c0b8420039044d1784240180c2648150701300c6200041c0d070804001040010070000c6a0302485c005108880d80c1d54604110107405545800ba952100b0b0b5454020040266500d00c644881d01a04000d009443e41c284a0b2905001c00720b081464250005003c20ba1210113040074903000b940080c024161050130348211900342c62000e00d15601601c620704080940744e400044071050700c0c241b0b41c0079200003800c0600f10007c030343d52601c107243c152030942d500c240041c4450254030104242008007030b121f140610344 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 809750980 1250 809749730 809749747
    0xd141b03091801080c04050403050a1d0307030b0f091612030e09011508070806030309061b062502030405010818070b0316080a0204050607080d06120c051e06161106040605 75
    0x2405e41c0e042c0c502e40202d04140034040000d810009862103204103103041a401600407000810440c40c6480503900740c003d5501c04824880b07020004ca10808404901e6819501c500c190b260381d42c00d0709641d84445011b03990081c0030804e1000b01103e000741c06032400300303940c490181c0000c0742c07550280d10008403a8280f01030500f5031a0010061076109440d820030302c0c241c3c41d0400210b6264495034503550b22503000050644686c28800d010b591503448601c048484a00c0d0042c0c00706c2230707030151107280e400003001d21601ca2011440081101d0a45906070340308000da8448006100c82401c54071116803e50081c803001054054111014510605041041a000700b460690140c050500900030745c4086004200030720551321018200c035030540e0710001140d0703600402c4022800400325500443d0018643c066110244150300d4426410303103401300c2d094100204660080724410207902c09164100c0d070180074031091000d68a40420f1058001c054181d4800c83c5003000030b0559006d9082800420804902041c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 809752230 1250 809750980 809750983
    0xa1704110414150307230402120109090203190201093602130806010b090105030709120606090c181406071a040c08191704091406030d141b0309180108 66
    0x319440c3e00f5000780c00554280303182458082e45210500d0040f403202000400251074960440c6c101c1d8601403102462540c49807006c6016008255050b40b080c1b151078200c9500340038680745421510b1b41619105015403416000030002410341140152030046446281c0101840e9a000014500320301d8005a45011481d40c00700c1d500e00355080403841c2d40c0580018441c40d415403048885255003401d00544947e80c20364122440c00d507540041c002400e0850242c5c080000c1074201c1001e9070b0040300309002c00e210071141151900c20b0b01d008001c0041f160b074010068101c98011405141d60094100340c9800c602e80c44441043c02203014040101452a08000502c02d0184100c0080c200b240c010308442d007407004014034510251900607009501031841c00304184868002c4900801c0b5a540a20003168084440d80001c00200c0c1c1c2c0074000d00410203584803051041204c003106401c1044080d04021a4403444400c1d108000045100c61008100b480d01c0c640d00c9800c2d04400d208a030580d01103560401180e00d = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 809753480 1250 809752230 809752261
    0x1404060903030f0c0503010909050304081507030615020303071119030c0b010b0c0a08030a0b10180602012c0705180a0c0203091305060d0c17120a1704110414 69
    0xf0200e5840d1014602130301d40e1000450b411240740c0c03600030a401c8041d0030300e14158071495021411a201b080032070150340320f8584e0500e20444160702d04001c0c403a83d41c40e0004a80110901b0000140c00800005421500969040140c2d10503401101c0342e2007006101401c040740403420035404501d9450a1004100800b1560b6002d00718800449040c204000b90552317950400c08802425003002000042880246510990011000411002c0000d024000240c815005401e41c020320090a81c1c003c9a11401401041e6502c49016803640184220f810f9409941e000c5680701e0300103008604001031150b94110848905d03001c9803074213207801e051400c503031021074504184020030b5400600c100c0ba45075480f19880c0c040340840d0f00c2c0104107951698001403078680790000c014610124103030049880c54179183c80c08154116601202c81d5401001c220403400d015081514000400b600d501d12030100c0030080c4150441d2140103c01c40c00007a140000b01560780407844d00e4800c074812010400f00d581c803440c02 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 809754730 1250 809753480 809753501
    0x90b10032306040f050102090306040602030906150604090c0909020c0309030708190206090d060e1c0c0f110111070b0a091211060f07080c160e01080606090604140406090303 76
    0x2a03820220710001c0c1c180c540b000100090504045569038109100c800c0d0101c42c0c81030401420340d502403405142040080d0016144200148105c00c0012803041c2824070107100141e0003042581401d140c4600940980313408161181000803161001415400a001800540c40c8907009152a04260800d02d440d00c0a6503000c1c1d1519440003083c40c1c0d540880c140001d1101d90140d985698a00f184804210a502e042d00014a41490941c0c0562043c4c40418009800208a460042d9024060b44200c0d1403840c03590015110031840d9000000007085203100401051040c145001410000d42c0d0f018200300a540c03010400038400107083c0c40c03040d8801d00800180501a42064181d042c0da140c440303214001c6030782d680c090000040c0296900120b0029a401301e03034017188040c0c0d0b40da11a91001e03151414040c016444a48000d00030540e100441841340c107844030700380100f62907038030102000250b02d4007510b003035001543e41d03d50303094000c800100180300b280106404900c0b94203074a4000c0880741421072 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 809755980 1250 809754730 809754773
    0x1a0c010e06070905130209033c120d090206030103030201090b06060301150324080c12012703051c1a03210715090302060103120201090f080a03090b1003 67
    0x204810b95400c091440c0a9a0055562180f200c0309081004028030031a20240ea0520401c801c50060300e10f161101d00400300303003444c0f6954005041c01c1041100704003e10700b440c2500010305541101503884090304241c5071001021640100540114260f0343c801e8005900507510f8402c180f040c440d040034000e070051010380e071140c074540c541510503208649007400ca004040d200c44900b002c85483c040454043c00302451118101d950f590100d603276501a0380900c500480c1401380424031381c40103124a1952420b9200303049001d0841003d20940c2803003004d01103061150500c28820f840c40d0718811071740040207804c00001e1032451140317814004803011031041d2096215140c1c1c8404040703101084000310400000700c3e03858000380d15220b42d50f0300707031014840c038054036203240801410b0340050794504980c0594842a400442c0d0fa008070b00342e83c20004003a021400001c50f107400500c4901c02041c0e071105901e00020349501c2d0340d4680c00391107000d9581020061010800344284206c610707607070160b9100e051 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 809757230 1250 809755980 809755993
    0x1030b090c0d080904021b1603020f03011802104503120f2c010f1d0f0d05010606031b0201021c050402030a0503120103030809031309050604061a0c010e 67
    0x5442d4502c510404c0e0045000c1c9801049181c5290354124007042940c2000c820354040c501018001e54107041035100a9100354a09409200c070b509040c0f01d414070030011300196902151003070b001e000c41c0400d00030060003082840c2c036070f4280d00740e20000c00040640080c0001c00554400051030500340002240e00c994400c10301030100000f801064007100e80c0304150404062082c1403050507540781c108480034090226200d031100034000003205142544680988420381d003032540440880f84030904500d0544492039034060800c4520b07200e0724100207090f0040460001840d40c0d554182960301030340c00320f80802d03200c100c07001c07a800e4108d00400368148030b07100171820170085c00d1880246006164080310f16a540f50049019520b0520030881850380110403207543d2a04202103840b40c00b824801503002640b4640800e0b00b1f50400301c00c4450001c207004160014a0800040304020b0001a240755446580c4003c001001903003504801c076840d09140000f030b210962200140d0a440031140b43c94000e41020 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 809758480 1250 809757230 809757233
    0x50a1203021209190320060a0510060906020c0105161407050306011e0e04030504080a050303010e1608190e0a060506100306030308040f0206070819030e06070228060501030b090c0d 79
    0x1555069130701da42614203107801c003450882031800000b0090000000d40113a07800c00400e00d41c160049405041500d121805403960358030129810811401004010b1700715510001c001c2d807103680500060780c0d584800a20210150f40c03003800d044030648640955400c590780801c6140340a101850052254440415031400b20030361489441901d40035243e00001140c0100302418881d209450207004004125042c000312420a942e0b241c00920405407500b032594002004240511151007481c0e6540c1c80d641c50325124510301e01030b09500314150051403561052807040d11a000c0185038a003900840b070000305810407005100f040c0d40911100e03c00d0505004041001075840585203a0141c1c022010480f80011403000541130b2007000006860040c1c089040342d0003003138511150580e4002a10700300300540009290640b0764004540744405604136013000d8559801c0001e800b07001d048010100d0b52184500e50315a02155000e803c242c464601c00c001300281c14038104242c801e5600102d03500046016035 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 809759730 1250 809758480 809758513
    0x90b15091804060212100911160308060112020a05130e0f0402010f0314040b070e0d110d0609060603050a0b0a060f0b09060d0606020c130b0303030105010c050a1203021209 75
    0x34000760319058407000006020b000e0240d043d0780d080d200003002c000990030103c0300980c0510042c021031812510f03040183c2d0072068035100300c038141602160380b144c0c0f00e00561070a0b640120002c28090600100d4012450169124030041c000b0351140d0710b840d0b803904592090751290700380350340115062104120a00024510555001780c0c400e9091801c10402d01d00c84070100c01a006400f02c0d411003070306d604107000401210918191082c071481e510003000440290422111040c1d4280242c0646100c95001100d03042018000002501968010400c400c4075500c3c0c6045031055801a1034a4200c926480d041141480c03505800000e41d0300c0a008050034104d00c0920b042d030714400d00c215240000340d680000d40310b4805462100400d0703502000f026a0300e2001035219034207650550710810000107039200e92029446140c080200140017141540e081000655140050321001e450362b12500f2003800004100049114542020381c1d40503848040e0000145c072400390150146400e50000d0040d03800c90180c = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 809760980 1250 809759730 809759749
    0xc020c0a0e0c120937110d0c090c080c0a02101e14040516031e0807080d0911060405030d030f0b210d020d09062304090b1509 55
    0x81000034007107035221400324460a1182d50b118020500400d030803c40962030100c1c80400b80d00d402040020ba03c145041841c0060a081ca01540c0511200340c40101180041d41400da0200014041d1121040c150300c03407604084441e403240c808a510340c100d1046043e0700c200507a811040c00c4c4921814000000c401a4482c0d1851f15540c80c8155a40a080040c0200e0005000f074200882810030131a00c040c540705215000c111001e46c4c80d8445c0a242c15900260250380c070046941210840c0d00003488481b80540c1e403a8000025076000e8000d0002d80d0210340380c007000f07100031418440002040b5100d1724080100103003182040748030b800d092104000c0c540303002c564200001c5072441c00090006503003090301c00609912480c9a04080b2a0340e040c295211a016103884500c030000440f410401030b03030800c0b0b17035400d4040c00f40c0380000d003640c504100c25401a060003010b04101c41004032140302070031107012550483e6001d510195202c084410850429402200074510080d606034645500030000c54260708 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 809762230 1250 809760980 809760989
    0x180615021f0e070b0d0207020918030409020309011119020709060e01120201031b0504050a0b0306180907150807080a05060603010b070201261b030910090303180302060702010c020c0a 80
    0xa0300c2c0d8061500c002d40610088026095800c4016154a2001c4e001002500440f1007280100300e5031001c182c0e00c0c000215546507502230380c2c0003145424101208203010f50005000b03001c1e90b6403180000781c84440d800e0060700300803c1d0000361700f289806031200240b41503800c1c0d00c54a03034249446000d0040001000ca9241903400101c0382807626411480124020200e00c5e0350054105000107030f40304099840360083c0210341040b0380c2074070301a0b16003042244910083d1002030b408135440c010070020380340210550743c0c048100c2e4103560344143d45007011420280403040c07243c00900c541c01005445134012225603003010040508005519001c80401d4962006000703500c1038407004102034045a20405c20481080440300b0500040c0c590201500307240030741a9005041c2c281180441000c80100c5401e50307201c0c040700d0004100d0f01c003041c21b60b02d0052400403816020580c407156006400c180c001200741101c0e04c40c0c1d000340920305d401c1c04020b0841c0c401110b5002190000d4080759003d9071448a65810368 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 809763480 1250 809762230 809762293
    0x9020909130318080f010c02011404060504080f03010603060510031503080c030c100207060e030c21070506040308071206050d140c0312070c050603010b07061518061502 74
    0x2080c18103003070302c14910040350940c1d91891900007007000000418031040c0001c17078100a0000800c03601040e07080c0c485180c892090200e4540000d00491101d400654106014070300c0d1b989020b0a0040405481c0c0c0246c10a2010030f40320007080041d4100340303401051002d40703440d08011644480f040c01e080586540320103483c010001c20b4005413500300348101c41d007510704841100c41090443c9a428040e4002120a0301c3d0b0710f00c2e210060521242c08021034a0203680007001d485009180420300003221060041d4040c0c41d8010308c8503400061040040c140540d00076110340d41e40b031a01039401801111112a26000e1a04200301000540c07624141c1e0807155600a5041694050030341180340380c150f2010000d580351140c21401c609160104008042c418020480c10420913121014402039200c00c0c465034015800400014001c65590b03840603580800c90a1000000c81e07030360234070300c2900348000e448200299844504000c1c6035039840030300300511480d0020f03143c04c44000071450040841019040c644 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 809764730 1250 809763480 809763511
    0xe030a11060c0f0106030c090c050412060f050114090115050d02161a010611070b0a0309060605060430021f0309120f1b020a0510021204140a09020909 66
    0x80d6911000c2c1d03000359a03841c00b114425a290007840380070704031601c02a603040c5440303280401d100074030f8002ca04001c50b0707035110180740505e001c0040c074403d6540c00041c3c1e446551001c800c201cac0350260107007034001c200f41c20020309050005010406d41c44410b03444401038095060111503450f80110031307102c0034580b030940103031980f0000c22103110904400c00001c00090100005450700100c612165058940369613411242d05015001c29503608054011031514200900411346424440d400c003d4241e80304080114049a07510302044e070a80194014500001c0014410070700d81a844068074440c1c50003060b4040400b032035801048409401d00680d203440c007046200040c403240139802108001c2d42c0243e0f0408200722400d0000c01c1c41c10880d55007000143d00a5860540d264514a0b00d2022600107140c854400d241074204102403294100d07410940c02407040030441041a1b101420043c824050110310700300f0f0080401c40408400e8102c0c41445105021003005a200c044456500642c0380b04002d21 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 809765980 1250 809764730 809764763
    0x507020112050c0703021c021b1f031a030304180b060c07060e0f0301050907150e09010f03020301110403080717190e2b110f060c01090507060e030a 65
    0xd1410002011450940c181000c0c49902c3d41e0000c000e0407200e010740d0a403406860001c40101110241d00208030040e44200c05101415024a4881e0300e880130091004803d24040c600400403c00741c101610040303942c0c0c000a40105400302c50101e0895003c034043c61509017041621421850704000700e2403010795030f540351805502e80c00203c407284a40b03407044074506a40c82800416400100443c5800b50803006100002d03402c050090034011070580c0064001e450402201c0b10310611b2509100c401c110001141d034440351103040002c0d0190502065141203d4154014903003500c408401d4000d0280c000c2200304041445003042e00c14550344081088211000d407903060300f050040101021811070055011007040d5005070100724802410b68000803442020403054440300e008855100300f00352072421680000d8081c0f101d4032080b1500a250055880001001c074031030b03802c400342080c0340b69920016442800030030020000101039515003903000e400101c0c0403d0f00c0341c3c42d081c4001e21480c0d5500c007146 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 809767230 1250 809765980 809765987
    0x5060a140c18191a030115080402012a02030618030403110d06020d050a0c090b090603090106240e030714120111130501170c03180a0609061b090f050105070201 70
    0x65485401800b0110071924011508005070492248a07600c0100500d4070030f0844c1c040043d03a0498507815620008131120780815601d052008200301d04200c81e11219441e615507011291080c0b090110362250b0013850f920500d4034268015003500600d6485c0c164602c1d40d0320b0004102c8050703950140180d420070603a00c0109601070201030300241074500124414900742d4090703010343d109587c3da10061005200c0d904095030080da481c020300003150700c100715107401800c100005682100b83c0c2c40c00060026501c4045405500c40982e40c201c501284400e0420060752208040410070003c074041c058003403034110618160355003010170f280501c40f90050f0315180c110a6124001317034410600c2c0b03103a559070b05070045850b80e2070300d000d03503400b103a2440541101c0203030004600740715424202d250703850360315200c0d0100c0d0400c9282569010600c5011010400140f060155020340c901c5540c0200340e5801d080c6542e41c200740d602e1002c600300006031784200302203a8240070f0740302124828242150f6902e410b00048 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 809768480 1250 809767230 809767267
    0x10f0212221a07030f201b0a031e021b0d050c09010632030a0504020d051b1e01140c010905030c030a200d030f020705150405060a140c 59
    0x3800b103826582d810400d00d000306080b20710504203694100200c80300c0b010700714122069518100c050b0103a40c84241507418450000303111607800290584010041c0c03040c50380c23800000e1001280060081800071404840340403015800064a0000c1c0443c405806800e071000d59a10540900c1011050081e10512005001903681450040c05040b0f4540e11391f0000b030b08040201000011006d0980e8040c2540c003444000000c40001003010a0702c1c0d6240e2041c0140070b48009030060784d0207840b0409200003d07104011614000078840c030320400d40303510003080000204102c40e0841000c13084507032240700c9a071b100100340f07074041a4840301c60b100d1112080c454010712080310000d04034800003078500c04c08031001010b450750814583c1c07000d40c0c00c801048801a440c101d000384008940c0000c0c020003045020317401003a140c0e030b202c0c2001810300f00030782c0380c051030b1030200d50007044410b000f0010b00003484824400036038040d0480720240885003140304015407440c0010540310242202050384242c106071403280303 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 809769730 1250 809768480 809768483
    0x10309060c0207080607050a1d03030405090f0105090c1207111906060807081914010f021204050c15070f0c1d1603140103060b0a0509011502010f021222 67
    0x100010840301070003954483d03040c007819003503201d040005a0001e00c5a42152440200340d80c0b481003101d200d0000240180d951059164540018031010445882e403121182c81203407030000400089d403501083c0005034a0281010b6500e900c20000b50302d50641c05400c070381c0c200e01107150200e008401400f0036410400d82d10201d204101e030400541d42400001e80045050310b1508041c0c0c0e20711651411565a91b0600b001c9074000038806000140215154205160325031422100100d00c900d1185001d504a9202092094070280018240018010708111240903c141510b1180d807505581b602c0486034000c682c8010000440e00562000b00050040381c1001881da22903a601c4080d41514003640721002181c1040009656003080c03000140710740910306407034000c8190321880741d00710784580300a45200708800d070b005004100000b4440e00c441d0282d5000304800c0c0d0702d20004281c1c0c1c1400900391181c001c04189184d005020b00340c10707103a03034050342ca802c00d030b007041c140800240c410107012007034550303110 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 809770980 1250 809769730 809769743
    0xe01031b0305061504050603300d1b0f081b0a020304030f0c0806070c0c1505090a06080601030b09090d0c051f05060f01080411010e0d051c0e061206060306010309 71
    0x501c000c02103551090b180000040320144401d984110a15035a011031102c608415481c1030003900522750083c160602071080606010b15000100c0c0f00c040c180ca56828000f103d50400c0d03810003000590020414980b0f00043c5407650b00b906064449a0ad401c0b10810ba02c0c0000704c001810321a0381c0d0007081290000d69100c1c0c20448034112905101c4007201c0584544100381c003070000011141b601c940c030764400480d40015500c24142c140301040c00c928090b82c01303203410700000704802021540d4a425802c000c088660b215501440e0000004003230310004100f07540109801024003d14000c04140300751b502c0b1140c500008001400d050003480d000d000401104524041410500c2c60849500316520849040d80e107505036503880c800442d541ca000f00e8010301140d10309031781d4002641c0300b90181d0007480300080070031401d03002c9500c4003400c0c02c4c0079034240c40c03064410320004600c01f40c100b04d07048050b200032a41503041c03003590920a000064020200c0388102000400140c00e68041e81c44034034015000305 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 809772230 1250 809770980 809770993
    0x9070e010302120c0301170a0807080313080715110c0a06050601030213081605010e13050c040519080708030c031204060f0e0c0103140601020d05090a09111e03010e01031b0305 77
    0x61004e0394001e00409002c64460002d1480c030300c0f000180740041e103900856103032400c103031611400b041d50000341061892440c1748103a00d011450040180654130300481504039200c983d9203842c01112200b01c071184015000348510441d42902044840c169600720001061507546d20004030b000340302c1d000c0410040d4000c1e00010421140024008401d00414041c0c041003070744031b00c010740320030400c61002580020100f1004d01902e4132900181e0700129101021420b042d00e9074006001c0601c0e1824880105040c0d42c0104103922080003c031005206020155207031a0103503040070380300d21800b0803442d0380c010103602140c20030816034818000051645020884450042c0507503844032055584280041d00b0300d0f9078044a0350708011001e004410503002402c4030161444d00361141e0700701666481e845621601c001411000c02c4c0208415818070314a11030340d03640c4c1314199002c9120b02d04c0141d4100c00040c001800001d410742032a9044d44d400c200720841c1e01140c0901030116024581004000780a4807 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 809773480 1250 809772230 809772241
    0x20f0c120f01111b031c0b010e03030d0e070e131410090f0209070809060a09110612010f06170601210e0c210d0c0302031204030e040f0b09070e01030212 67
    0x320003518180c10002c40c18401c20711100d260b00d90b0303405031256036448484007071b412151b0040d01e94040c00c405c20041c180303c0440391000c0b00090031900b01880c000d0078181c03121090b4200c030f00d01b40604c03005040f982880c5a600d013065080c121051800310801062650114007154516408002c042050740c0d8200d0140205030452409403104078240004a00a0f1250804168910700171b014140c450b0186000520543d03442441040c050641194251510844030850708000d45607070004189420507a080452254941640350607860440d40c001000c00c0b04c04c44020111002c007000c0c0541054091038181a00c1d0483c40c101c100c1e0380074030041182c6076407a1000302c419100d4085151403c4582c1150b100780e2080000c02c1c030342210405150319030301e0703038001c1040100902d009600e075203045030181c03040304d0a09a260740f080a0040c2e06680507004210070010f2401c3c07924250003514125151020305020600e000c2000c66007581000d41401c0900410b29102e4130759901c281e05a4520301d60010404a250500 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 809774730 1250 809773480 809773511
    0x1f020a1806031a100e22181a1003021005040519050f0f220e10050603010b040b01021504021f120e061009020306220e0c01020f0c120f01 60
    0x8010080710f948001072032a40c1c0c030300660064081000c4d5203858054000280420524505c5448920346d2801220350345030b030f01c0c04c00f44140c2451406069816446030140c0c2461421550203280c0724010320102001c000c80e500c941302710841101d506560805104403000400e41e49401940c00554004003200504040c18104201c0141110001d4802e000032000d4802401204007035500050340003405280e208072031f0343c241c0c460003c0c0907155600018a0280e05003829080004040200e451070703444000703120a501e0b0a200e15a0f40c504121010484d058030700700080e4a0b401e001403803551014403c0002019911101029a41d055030800c1c011b6400c0c0d210742001e00882c0d111080300c10118904441d1030001a4000ba81d140200d880e101d0001c280c91400380781e03601a40c0010079658004090045401351f000e10b81c0d900a0540da600c00f80890100c0c900e4062614007120700000078119440301403010120071010a11006928050310300e0040300c40c007003091526018941035049255031805490321600942c = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 809775980 1250 809774730 809774741
    0x203070302130605090a060e03030903161a07020a060c030c080d0903110a08093d111c0f18080a02010809010e03090d020102211306021f020a180603 65
    0x1d64a030b030000b030b40c2d02c419046440d8012400346a80081c1458402e2041038024001a1001e40005007164a0000d203030000c01d04105980a204400303040d0381e14140b0600901405540c03c00311004013082c10000c007a00050300c42e02180c4505005c7c08204415038003414800c52128210b070707403c00040c0b9600d44900403040001c100c030903400d40c0003034808454400302140108030b401145030840310301410036882d0000c10031162100d8980c4010070300b0100e08160b0030f07072800180390320b4650a4494036070603c03000350024004810115034122a0740000c07864440c1c140741c1c001039181e09105480c0c6454511031f510000d5880d80950070f04213100c0d222800e40040c03045400254407603a14400c0e070704c0844c0782e103501d0441c030b0a0300c030010b0034440c8940080c002910241890459013541034014030460b041d03070300c444081083c0102e00700381c403030b041510000f2031400c6181c19400807401007007148001c1c2995903141d01c0501c0c3c1400c034408c8003640d00c6c0e00000c503030440030701c50603081c2045081c3c01c1c0048101562614040c00414 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 809777230 1250 809775980 809775997
    0xe010503011409101d0d0503070e0607211b081905070308010308070305040e161d03070b070602070209340c0b0c0415022503030c20040203070302 64
    0x1801c142c000c0082c2c41c0b41e6180b460040c0514401003400040058550001e444e1200c0d040c911040724141100840c003003080307601b001c0403507030716500e603282850900280940c0540d48a107006200030030006002440f440d8244200e220b1040c41102b450303a50b60000c0707036200700300c1c0f10500c40e03070007086201001c0c04506030041500cbca40710391724441007009030361041e201c40c0118600079021405540040010940090003003007800d00c02d151141c82d00d0307240c5802c1200007a05807038807042c0140c0b100150080e03e420045813000c04400e81a051201064040060303910616400307904400c0360089036001c1006071980580d0410f50380148843c01a18120502502c102070000c1c4100140b498144040d880001c400b003c0c058801950b69443e80c260040c2d2240e008070100502101c500c00320800c8006032020004c1c0c6241c5514070785034041d144090200060108081c1140150380740082043e1003000000d800546420300c40c0c2d88410800c6200081500c8840b03401d064603001e6800c14000401c000c402c40d4503030700414072389 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 809778480 1250 809777230 809777233
    0x1206080114100f0b16030c0c1203020c0103060f141212030a050c030103080a111519050906061f0201090203030703090e0a090b0604150b0f03040b0f060a0303081e010e010503 76
    0x90b0f0b0345545002489480e8070072800890030800c911401c10b414592542400f03402411b051010b14406e030349288401c6000e0740608081e405000800007090b60501820700c44070b0702441e05002a074100850548181c0c1540b180d62101c800c2c4040c20700c501d40303034030440c2c841c4103071460151b039088104000000010707441128000e00313841c9004001020301032520f041d81d05894101c5503075424549460419a000346044000c48841e11a0503e45400d04602d242424422090b0504420f002c18203007180400b904d9000e0403050264010748100910303520303428401c111415111020a403210901c1c0c505900418010f18069010701001406009054005c0c600b00210740403200fa44050343c0d64040001c080301c40c4064010804d0300c0d010040303012071610b0341191000d0b140c5021410780c21a91151203603a0360b48000d800c180c1200c408402c01c401d001084444aa201401c859644e0641c5030000c0000c18140c0e80f07010090600400402003600d03030940300041c64444906181140750307940c441003076100d22682441024800d = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 809779730 1250 809778480 809778511
    0x310090b01052106010b030c1b0309101713020a090509060121020132070b071b081603120e0a140a030e1e030604030c050114040308071206080114 64
    0x16808002c04030800e5035410310281585900b05102030105600142113038030549020f201d0980e0a03c940a004e1824025020003941d0f80e00d85441808991810300c0403500a0137403154071801d9021180400c00d901c5030759620040c114140d944009511070603145c002110301d0f8980020000c0c0d005001400320b041e9014290818114070009154903569089400004c0c00580d03c02e0705441100700d850050440003110641a803100d29103007403a0119900300701e1003526404c0070320090143c01600107000444044a0000d120002121074483d41100c0c402c8800c01400301c428104040140340c80f403070000041c0294040284142c045c03075500503a55500d88001546c0c900d14181281352030040018910082d95032540b20b070a20501000e003002501c04200c0e407240e000940e80c0e8900185960140402c52240d0310a4031050001151401c0c5a402c40c0e0281c1c0d45032640d40c944400b404003180c3c1200e090340d80a8204d140c6001480035039440d400c042e15041d8052031841d800c4c010410a1040304201d1103100303452100070801c8 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 809780980 1250 809779730 809779759
    0x19140a050d150b060f070c05180108120c15010b0309011a15340506060405010b120403021f020403110306060d02061608040f030210020c01020d0e0310090b0105 70
    0x4481c0c0c030500004001481d0440c805084070352641000c500d402c0c00030801c5003880030461482219a2200e0422954060750f40d074280709a1034101204201480c1988001c0d0a540c1072241060b598140c3c040165549280440d0440790004100241c00016029a10862065a4410031317140c8a420680b01c01c00254200886c01e400880131070800b086a1000500c0f00452504102e070703143c0c079544010380b101c0380350510808203080040710b80c0600d80562038003a0f030511a82107a05200342880c01c0600800c1c0328078106001000f024815105072402c8441c800c00402d01c43c3c54528060340ba1107070480c1000900075100e07490a540030856405401200e0103a0403850341e0580c20b104060322140304a8905500a142c0341554001d801d0400c040d1140694054484501e0507054032440d9180d0080d91000c0340704001d0031010300c01c6041910381c8001a010742c0c001804c0c49a01c00001030745170b10110b10103000300920360000c00648c0c0d80801031400f080c207a506040000d00798500340403090f07803801d008481c0103103100a010711 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 809782230 1250 809780980 809780989
    0x20a050301140909061303030e030f0301031707020102100b21100f0504021809120705162117270a050a08030315150d0c1d090a020919140a05 62
    0x44c45007101c0406080c01da80c07215422014414030b018150b04065a07032850b08101102040107243e25508800d50703d4580d803442c90700f440305401c481d6022075400414080b03240140d030001081c8040900d00c40b00425010000d0001c50005403101c000c14020a21052101d68152400b24070090302e40c25204003400503440144500007940c0083ea80290042c10b007061035240400d01203926030b003007864a016188250701644c503640c2c50f90861001956142c020181c6007001c403501c205140d00411042c900e000a0085814012600828401e40a00342c80450742d010f00c42800381508440b8119101c056011200100500043c04000c10480e224020406003a0200e45850440412400c4400c0b6400442c035558501100d040c2c01440d40030201e070000381003e50506d01c003a07010080d0401e02d045d03500004005a603072070300800481c0d901035284000a59a80007000f2030311416070442c2c4c0060781d184056507030f10751500481e00e0300e40c1c140b449050301292100040f500c103000b055841202d607000c9a158034600d40311020807 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 809783480 1250 809782230 809782249
    0x403081305030301030b1026060106092103020304091505040b12030703110c060a0513090209031e070f080d0e1c0b04030c0503030106032408070605071104020a05030114 74
    0x1d082903105200400024442011455000898680c58002940e8514003010100d01d5130080f8250100c1c4000030f403900800804c4054010034440c6002c090f2149050180c2d07002c030714084042c0f100c9045942c400010305008004860082441d080100401408203004d213803441040c0c0510ad01c91810002c441c00140b82210a44d403400102e80e014628050569a003a00c809000600c207807a64080c000401c820f42c0e46000143c00707660619180d45665041119205640034015000b212803a481440318824984002410405103055004480110002d178540c3c0d03440e20070345a00c41c0c03213541c2018a0105400f000802c11b580c1d600c459854007000c07507658000300075901490803c65042d040c00b50f840c00c00403076000d1140035041802814210503c001c01d07110182194806d0704108041f0b0b0701d580001d00c42a8900001c0440c605c58111005c1d40745007010a99900c1c7d000c0c03445050f042000c0840e2078014882042c10213059401d006204540c1d07200d4044019199401c04d204d0100103030313a84182e4a040c1d00b0303c050007 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 809784730 1250 809783480 809783483
    0x13020103060b0a021504110603010306050604050a06060f110f120c0706021f0b060705010905030406091d04230a03020d03050601050705101113120210020304271b0804030813 76
    0x940303000c1c0c40e809006124036170010819034004a0b2001203106070b84405000794043c60007100e0100e0940380203001d00c4207490010b0001c20f410340c40c01504010f00b50340450900301119861402d95540072114903600e1424100d02816910f1340100000200026041c4004150f000d00100035a84443d6860310140e07114411005002d4a103626000c2407940c0c08100d91000000700c1000304100d0400c86140c41e05401c41e031040b40b003111560b00000701400035641142c0c01d20001c0c0300400000108600d10354104010a0000d40010406001c1107401071341c102d01202e201c20341d12200000c41c2e035003512608009540d91000100700700803918141c080350312940f14800b01d54580e9084001411494800c11944006001c03624041004060138003100c4841c0c80402e038030600404031000d44a0000285004110707242d001007901e2015540b041101f08490131510072409101301c00d40000c803601c2c5018800c08005018445405603400a241c500910900c0e001100700340124000d6a5003850340d0384144d00a280150440030 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 809785980 1250 809784730 809784733
    0x60906011a04060f0c080705010c09030209010b0f1206030a0213020d050112050c13110d0f0605010203030402031510090507050c0601052b06020408030f07060b100f050a09030b13020103060b0a02 85
    0x1c0e07088007038000c5c03081c0040c02e4030595440c1e1520300301e42ca41c2800c44460189030070025280038410010b61400120f01b5014004801d0700f070740341070317044203241c12a440f4084210a8450782800000c2141d5000d0001a030000d8000d40020302540c400301904000354020045061424074200002c54540e18450b0311200f0a50b01000500755110f42c0e00410079442c5804145141251303c0b001068064401c0b1406130080707100880d40461880e50301c0d21140309980c80740c0c1003030f030466209004000241e07030001420710100754049185c00d60b58440c1103540c02e01d40c02c990400c42d1f40038286018031050682c050000c0491450300c6041d20070716602c9608011711102a10303c84007208106002130350a80718500c0d40301d11100d00c1038500600d015030351100e050440e00103402c210031709080400c1e980c091000074002c0c690045022181000e2a0f25004000f902da0401748603080c00300840445e0340202076008000d80320243d50042007894603131814040014a9080d2013400f01d0019081000000f860020181601d030440d68640 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 809787230 1250 809785980 809785997
    0x307050d0c150f0b190612020a17070903050111071a0403050d020f040f0608090d05040f0e060f0310061703030411120a1703181614010908060906011a0406 68
    0x140320001e40803086458507038550711880d411316a41c42046050380c0107040c94044240614010010340016038034030303500d51843d0041101d0882d00c1d6005046a08400502c443c00555480d280300842c0d100c9000d802c000c0942d841c00350103004804601000d01702c86032203845031002030f910b0205041c0790001c0075038006001c01c2d01480b800e406101c031a00500007408484000d50b0078030380d0707403429451030708401e51048020448040a11003920030030300010180c0e07141802e02a00d05441c003111011219064414460301122001c003013280c95075207102e45030508078001c08450000e1110b4000f44003c014a00c281d142c1c0d82c6014108100d107203404000e483c4074582046031002901041402e1000102104009c15400c1c05080303104000100380e55003c00588005000d003544901d0203c460300d03101d402321800d6000a5020b5032411151041c030342c400106913070001e040ba820712000c55005a90400c0d49070400c0c102030003004200300c0e0702d150005074103040b600069420418403c451070301c103905d807149001e42400241401d = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 809788480 1250 809787230 809787263
    0x50916110a061401081c0e01020c0904060e010606080412050a030f09061a030115230a0807080c010504320604030524100b07080f0a050705101803080907050907020307050d0c 76
    0x401171491f40342d0060054805200361480001c1900c142100e04940e0303250385000c00c0e4440c0d042442008003421041c1403404032428180c8524407201c051400340c1080000018031500018441d070407100120104400c1405203c0c071901d0500085c0a01d07000d8030825040c00d00c2d64460f140307014000e5001004000c00c00100303003030400302c00400c0f40c0e50080c40a0b12280446840103460b80310f441c8482c0080c40d010001c0c001007820000110704120301c0f010324031f040140622013400b004110624001d5010540e4a000c40720040240d54007202c500282034185e8881c0c0042800410b0040c0800c0c0d00304d000c00210030341c400c1c94492a000d110a2881910011400203c4280030f0000b20402001042c0e854010070101d42824101070300d0715115804406440c0010394042440c0c01000010401c0c1b03004000c51b0041030180314000c144400142d2041000030342000034400c0840d10145086c00140c0140c440030b814a83d05207007031400170b55603600c900812680c612954039115186842002e11805c20340d800310b07510500844a = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 809789730 1250 809788480 809788487
    0x150406121a030a0c0602070e06012f030a0903061d0a121814090a0e120d0b040203070f0801080f100b01172e050916110a061401081c 58
    0x181001d0001c10100100407116541000820740c03943c4100c46407008581441740c02030400b0785a40c052100c0d00c1000044c401c05a070003200e051200e0380900c0c41c040165180d850105034903031003181d030090a03000018402c80e81e560b01900d4030050303a00030001400040102c0103c04080003480010084d960042100d020004401002c09584001d0a1810074040f41c406036114412074060340c406002c6e84c0c01c00700100302c241460035034035510400782042082510140c800080d240c082c0382415907018400018100510035466200b006001c01c041c008648920740800007406d150310f41000800030400744800022894000105043c0000141c006003025641040003180a8550000c1c0c2505008001c00c9416078501105c0d5814480c1c0072800201104201d000640c4810001607446d200c0c0d02c640c081410300503038480105081e0058807003030810603084a10581202c05500811a400e9540a408074200502c400350f0000160080642c0043d25180d0f658041280d0343c2d00040181e055260302c580380304041500 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 809790980 1250 809789730 809789741
    0x102070f170307170711010509132d0609111303060b0112151509050d0b04020109030506101e080d030e0c04450b09010f060303050915040612 62
    0x20158100c0781040c601390348841038010080080000710798080b03082e205110884c5a44007180074207082c0985403000240108103070111154804201d03548503000720b16088400e0202c0800d07002d050217908584130990403258090241c52082e413509508050654448503220b100300c038244140003417510301c018515981d6801504e64944440e040c0810500fa05448108134080c1181c502c2489043c04103a50819101915412400250360100103034881305214a45850b0040290300d41c200742d4404195a0300d02c0126503540d91600700034501d00840f000d00c24824501120131003030b10100004940000c40e40c001d84210700307d00e071052003507035070000003038504050007a4040c100040c4504203484d0703031a0b040400318003900d01c06680910091360b40907101c6c428038444072000301c105c0007621403550603400e4103160350300c5004260009003103122054003207007040d0340950004415401e0003e041c01919620308014000360089104c550180060a2815641142201c04c94050310032a4403882680c4040f020581e00818 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 809792230 1250 809790980 809791019
    0x3080c04050d0f151b080a0216050d08011e1401020c030616111903050c0106080a140625030c0507050312010f0e010b12060d0f0b0a0b0102070f 63
    0x19020000866070307850b284001d00500d4001d8a603001500c840d460914600505903452031101441e11581c00c00300048008103421111091820110715226558010001c0c8503140090500c42c2c1545100420004041043d481c1c00c1620380fa0f01e041c0c0d82ea0b44000300c4100418208641244c19868000c1c8840c0c5074000e00502c04440601c129007824400c800841e15110302542e03803000b10300c2c050201540d005da02c0b00644583c90f90500c090f1100c3c4402214028078100e403488014140035000c20090003403682540000c0061041600312410020141000607660001e0805404c580c003d101c0000e001e800f451400c2c842221030109994160075401000310000e004000e80241009010014040810002c002070042180403010417100c03075260001c44440580e01e070b448242c405990b0f40c01001180d0404081c3d5802e4800300c11203003041d0359070324005060724401100040a104001d104035041c41590035404d8030541c00c88404200b0010f183c401aa5101503e10400101075000c0c1d1060040c1030346036100000d240c = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 809793480 1250 809792230 809792251
    0x4140a020a0902031b07050604061806090c030221060612150f09010b12061b040801050a05040b0a060819050111040909060507031a0d02030304050411130e060a030308 73
    0x640565000a06044656001d204070a402000380903820020401d4511903a00c0c45e580700d850004540e550342c3d00c0d100005c1000d030002c0e41d115071007540400e00c0d0200300060b6500c44000c20902e4060703d081034076042a0f0005a0050501800f000d6416000007003c0403107a040d0380042c046a0f445408000c41e42c0440d0780780c2089400b444020711400405018094010041c2010f00c40311842c1400c01103007100c01d030100b0180b0030141c19401000b4464081810750f04031b8800402c006140d4207039904040319108a13889103465610b424204143c60145074001d5020b07611072100c1e1a40c94031b0342c55120082e00c0d00d600800c20941c204004100e0b030765045450300300c0100d109a00124009040e0158005250030960040122070b840b82c0160041040c10b110341c42d801000c5080030003907208061000c0c2e0829a00410180c01441c0c5040c030401950360400aa60081030300601c10302122400180f00c1c03202d40c000710202c04460480072004641c170542d4071540c610032407000c1d1521110342e246071000c0710035070341c00b81207007000c1c = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 809794730 1250 809793480 809793493
    0x40506011101021611061309230915060a0803180d0609080c0d020304060c08130b030a0b0a0f06082d070503041a0103020303090d03030612140615090414 67
    0x714000b800905860702c0b294004411420903401c005c0506540c0c0e92030760340320b60420800c61a5441050f02004240c640c07003c0000341640341c00780f091081c0c0318416600001007029000700040c1c8031000508a21105016003e900305031200070034132100d07800310b00403100c44c3d42050203405448852040c0814403a1002040d642408105407a02000c480254a040d0b030b4521000520724207050003003001c0b001c8080035100841c135041c501600280303400c89410009010700c0000a9429119402040280190000032038941c0c0c0c0741010b000039002020b0041d180750103201031030000204906048001c0003142c440362550400c503a00c80c0d00010710800d28241a032140010800240c0080144e80c42003882000c7c030303440d120b81e207040c2030915000850015402c0c038030706c80c00600180300581b0044140c2e0131a0341c05488042e40101070f441d003034001c1c0195800c0001000e14010303019088c00440c50305d68401003100c0054a556813203503000c0501b000c050901da40d8120b03140001203800104080386070096503d00009a844 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 809795980 1250 809794730 809794757
    0x18090f051f0f1a0f160210020f0c0f0d1b050a050a05060307050f0c0a0303050604050a09051002030c0c03031306050609390304060b010807050c07140d1202070e010b04031104050601 79
    0x8aa42100a104038800c4120301c1740e0085007801c0d500000b0b071091030700003040462140700341107940c0d21203512041c0c05000c41c10591040354961034181014940d000d28008424080c2442401079180c51340f0032148074007900c0d00c00066904018503400c1c1030f108050035191441da80d10105407a0b95101c4e60007040c400504010382d80c40c0001c24881c02c00241d10968000c100d50405004103c00e0ba1400b6104001b428030b004040000904002444048950000030150b00c0c0e07996404803002c7c0340588181880c95002c000b04201403102e41d8115100b0711403207802d081120340c481c80244201b00208489072094180854401e40780248006924500f461010f035007003a000c003040361805880d42007548d0855400e0b40340e4424070701a41c6c210540c6a4810024644581040b0b012900259610a6403044c1801400a041c1020494407074410410050b60003080300c1c1c6054080d01002550b40c074151203804500c540220000c82c848040380704480c01c40741c00c0140058088203180400000b44005803061307040c00300015a105 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 809797230 1250 809795980 809796007
    0x5060601090807090b0a0b0a020d080a0501050f131d0604020a06020316061505040603060f110a0e1e03030c0a14030702011d04062705091501030318090f051f0f1a 71
    0xe0708c03a501d501824001c9951800a000f6000c08ac00940009003407800500c41621a09080031b00400c0031502075040c4140e85a0103001000004038402c0d00141010901c07188050000e081d5000d18400c1d03070081c5101e6944c2070100c0c3c03a800343d13041c40c040d50f21041c07120101050311500017444c1c2d1034401c10512060f654500004080381c40c80d5004940481d00c0d6903600c1180c981c2d078443c02c80e090781400c825901d0415010802130000380401e659620400b10950910f02040302e902d103030b1290307203805012641c1d1402c80c2050b00d0307600d0303082102c21200d195845005c40d003014004415a060079a060319a1503a41424200081600100300003094001d40d4500001900c0020000c1c0300d81007008000c01803172180724914401c000c0c2c0c1c90080c50302d41c16171300440108400c1e41101d04064112905440d00101018003c045880c074010142d00001030f084c10300a48204200c00c030b84c8030500071030850380005a03440790009080c00c1902c0c0b6129410b6500c5c500801000903040c0d5400f5407500c0707001d1501c0b240c034100b104011403 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 809798480 1250 809797230 809797237
    0x904050319091403060411010324091b0f0504261209181902070213020309070510020a0b220f0b060118030f060f09120c05060601090807090b0a0b 64
    0x141d000806040e000c000c0c00303007002088200b440055018102d180f405440c0c8005020007140014100b41da141502d807004d9041d0302d0705014041c0514541e0741c09a54902c0b078400a40040f0b00d0748100c000c65280040d132050700580c144e00c1300702c3c5581c03141c6040900e400441d03c1d40d5808030195214111000781c0b00111078100307000141ca01840402165220341d2903005001841d80f00c0f4040705264a604003e204900020708801c940b0030304840c0001d42d40d0a00c1e0700c04030396110207030541030110600110a1100090b4049008000d8507015070741d5108088074120101c0c3d461941000107000d5207001c50204840c02e01e07082c045403500c022079030300400c000515528100344903507142059810703103640b00500c24550f0348614074456410511652070350503415a01d84d40305030910800b0081550f50b03030340d0070090080a41e0b0482d091580d0000701c5c1c00103801071036a024142405002c000c807014043c002c0022160b601400360407054407002c10050820b07a003042030617402400400541c0f43c1c004441600005d02c0070545005 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 809799730 1250 809798480 809798527
    0x70e13111c14280623060f0a0e04030c020312130e01080c030d05210a1b1b14030403050d1d0f220b0a080a1703070e09040503 55
    0x20985031510900380031291007034580c9500b03400d8010400c01480000500c10071102203c5403442003801d28020300d016402800f02540304604009603140f1a816101083c52961054205559428803404008104503d8a0184c0180040c020301007001c85c000c04d03c103070030f1a0030b60340c405000c9030b901090070410b80c20a500241c000d41c82050a000c42030200c209000002801071046c800204411003001000030340700c40c1006000b00412502043d01420010340c1e241052983d500383c2803815180c02d100f60454064000c14201380d485060030309803128520b10501024000f094003140c2c4001c5a40d090b51040d00d1b8098078140d180662100388404004100181300d48025003526807a01409003040440e0411440c040480803842a0300e9845c04c5070741c64035004112008030060700d40142802144a54803c02061540c40c4943c2001c41004045091040011032852050082c40e9621240c130305074a641d480c81c48221880c0300004c1303d00b0328403442d0f07042c410300c03080c0c04c41d1003231055a06180c800340f85100000038144a = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 809800980 1250 809799730 809799769
    0x30f14010801090204141b030403051c0c1d2107080609010e0f0705181314030307030b0906060f1c05041b06050a0e0f04020d020708040e09070e1311 65
    0x1a04000c524146c4140c009200c1004e1a02c400e80c5040482402e107903000c03c00312041440004002400c040c8110211414214400400036843e50803210a8005204200200000c9005800613010210341215180101d9000a0100310f10041c5840c24902c2189403000c030280c9442080b0f80440c814409100041c0700c0c50102c0b00019200040810f140e2802035a0494416190000141841541c88030018004003041c8206a58855100c070700000c1c10305500c018003c2d050400742554515041c01c044021400f44281d90f905000801450003045030035802603031003035407160003040042560050540684012140380b04a4981880c01117002000c0d5441150b003207a40c504480c0e8031031650441e0812613800f03003040e868480d05000030450044d000603124203c0340d00c12091030701d181c03009680d590100c4158505c400d6080d0f45a40c2c0300e00c0d200010b80c00c80e0255240c09010a00021051000080c5241c201c404144c400c8685807140c1b02000308a0020030010703a0b0105045045c0ba00b56241e681755110504646c03507 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 809802230 1250 809800980 809800991
    0xa05060d020705010615020c01030207030c0218090c0f0a1811040e04121b140c030703060b040b12100f0902102f070311030a0507060c1a0f07030f14010801 68
    0xf50103070031100950032680c1030008451000780b0407640044c541404081c207081c01a50b0744100d05084c0c40414401d20001d500444000380e1540d4240e018180c2d6008040001c00c851841d00712208000130369210105840c1c00002c200d400300a411010b4010100394016184002000312a202040c4402d40c8240c00c949084090403051004210200c252001c4d1440c043c580815001409042a006c40160318405807040010a09216410000740403125410b01c0003012140250f03620724003038002d4050b03800c610784902d00c0d1000754480b0303040200101d04941d5030303040070302a18842480c075180104140f01d00d021000e81c0d0b80c0c895500603241d01407103ca0080054030703a42d00e01d050201407110b05d050846603008041560f16480c803200703040000c0720300640390b002500c402a000000003003841e00807002d00242580c413a01da0002500342c2c20000e0418070074084c3c0c801c00c071020116030b4000d0090406480801032111580c0014442d0740c460340c41001072741d01c9180045003100800003003000581c003e801004031070355900d = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 809803480 1250 809802230 809802233
    0x103081206010311040302120f061006021e0a0b0a1b080a0f0e0d1d030a03030b090c0f04150201090209330603040605040503070f08040603111602010e0a05060d0207 72
    0x3544841d8008002d20782809842e01c4074024407054062031200a0240c41c5240a403141c40005024000d4018141021198546000d5000c43c0c0590a18407030380300940903441249ca8140c0314016510800c0c1c0b02c940003032000c40341540d9030701240d000080c101d00019650700c01d1600c2c44400d28107192a2140e05a40702281070825125910845180d04500444035140100307007200700b44082080d00d9100c010341848814401c009131001c074040b11450b00e440c0c0c507004480d4050205505a40400e9801d101a5510383c4907560343c03459038049210303408004c003c002d0305100c1041442c420301940400a071241c4000f00d0b002032241e005c1031054005881103d07a075444000b4898510030350072002c03070084400f541e03161541855540402c0f014440600b01400c000d454034000f07410710104104440105600000000c50404d040c2808035070f83d00075004010000341004007060302800c05a083d5503060541c05115010b000c102c0d40103460300c07040303400600c1d04100400c1e0b002400d607944502400e00e903c50040c001da80c0b403c19 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 809804730 1250 809803480 809803507
    0x80601030b07110c190e0a1401060f08150a0509090d1e0912060b06040b0a080a05070e30010e0715122a0c0b09010c120203150603010308 60
    0x2c0011080041280301284444030020356041040c0041d540700c810825207113107510110f00c003600842c0014204100344103010792a90b10005a00e40b074004003289698950008890803003c4410b0040000d03102d802007500803034010348241409000500c41d0b09065516800319009880440d1a036805400154aa0504642106888040800b00c0501346104119a180030b0588000d500441540074411311002041200710f6104541c115002842c880d00c46540380f4102015900054280e8002201103001c10721200303e600030140a041e032510744200b90071062040c802810510140304a20800c080c2001c0443c00c0150b8600c1d0001c0030079030000c140c00754840302d001d203044030740c0d400b00020341e55401c450200294482c0608132812095013001c6904008009000381d100c1c03802031001c00d0b06c01c041520040482e04101d0108030030b841603a04002680d9590a40c908070345150000380301103490a841c0740a5075503968019a0301904140180b5020481c030300124903190801d81040b90b200c2070005800184030075 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 809805980 1250 809804730 809804753
    0x90b09010b0105030603031c060b070f050c061e0307030f0f0b01020c06040608061201020c0115031505090d0c0c0320090c04061d0315040c170111120711030408060103 73
    0x3400c3c01d1407469404c140d4003003030b03880c451595504c00b003802142c3d0584285090307030000c40040490551590b240d001a081900064441d0342d01100c05100c0e0028034035850401209542c0401c070000c9510700c5200b00f07103c0040a541c00200b50004150740d9069208185519100f41c00104a0961000490484100029140900000000d4440c0d0000d010401c080c0307602151a981c080015210030303690285a400060180c068115191070035401c00316003035020070003140c00c0d40490b8000e00c60140e600059120401c211003094988843c242c01488011501074003415041d081140310741c054504c000e0f6a85c44295602842e6480038806601600e808241403405a0720940c001580610f80e520301840c0000c00703007804408062400502c8a840c0d01e52404c2d6500340406030b41034807085200c0e2024942450881c0201d110b40c042c1201c001500203600280715414810103140d14134100c0c45601d04051401080550a80245800104500c04e40300007210101400030b00001d00f10007005024a5040d4641500a81d1 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 809807230 1250 809805980 809806001
    0x6082a0a1205060d1103071205010203160f0c170f0c0106030615080a0b0601050c010c080106030c03020906070204090204092a1706070f0504170a0c06050931090b0901 73
    0x605207018402c541c0d491100304c004c03040c0d000712540203020082002c0783c00c18106502c10300964600965003c10b11106400441c03140b8a13810126a02880e064000e035404146c10815500240305d104513080000d1442200101400042e900142401102000040070350720208960380280d440d00010006c01550b0700030b02400550700d0041b03903215030074024015550004280c018000702c00d07100105040b41d01500864000c0925403009001054501c040548800c03030078425000040c0c50040904030b910720900c2660f500f0040181b448e890400c0369000c2002800410340180c1c0d219544a0846001828400c2c400c07010915a5032038901c0d05206a1440010009980c000f440d40d20910585589181c1b000c00c100e86c0c84056402c1202c00428031480880302030040d42c00440c518040003c5690880e000020304c01d668a218030064400705403a50001c07220380c0125104d041c0c00086000d08802c29040d100712100300b05040310101d0b010658810400000e690001c0301c180c0b114041001405140d40c000c4c0241010070 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 809808480 1250 809807230 809807267
    0x8030d15030206032d070f021005010b120c09040c091a09090619031b08060c040501050a0c1407060c02040b010309050c060711130501080f120406082a0a 67
    0x5407440d008210984001040704400c07562800c4083d204504d401c1e00b413060003a040042d14101d1804400103051548803084010143c460f4400d10042c0b008140103042c1641c610b005c6050401e84a0b0320b1629a840d0040c200c415070300320a000105058403544070740c0c0103c08490380d41c0385140f81b0b003a1106051181d86412000070400401403070040b61505032901c0d0300032106582d5091021203110f100c120f041c8107030b0001480000c40380c1001c60b880e020844071009507034808007504c1650310f644030080d0f2284518416140421001d00400760f440e401101e40d9a040340c0070780004580f101401c0e4a035030500c403440d08030030042084c41c0121800e504092040d2400d4020a090800000703c0c142c8034941e80d03401e100c0c030040c8106c00000700704040120464108024910180c503040b07851203951000800342009009005451140c842090020903000517000280202c07525154640781c06d100d0200c8820400800058144c030703a5211404964140b94407290846a0b0314801c00e031100040c400043c48580029540001c6 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 809809730 1250 809808480 809808521
    0xa06020a030c0b1f030305090f06070c031b180204090b03060f0a0e031303051506090403121a060d0e010e16051c050a0804030b070c1a061908030d 64
    0xa508034594034601600320080480d0b96a8450103d16040c13070b6410100c1c03861110130303000800c140d000b401901070b0043c1180c03c840d07281040000c4c090740d405844005005441c480c40c0400100700110990903032020b80025050029842e82042c400312030a802c4a614001e038005030030030410005204400400604038094201ea040000054000d200040c2141707604940e2071046101d000010011206c21099210a9140c41681c4e4149181c490500c5162007070720640b16800900d90389400c041c06441190b16840318040d9580e8a10824000e04088034030016005222850104c0c0369607034805040007034101038012030700c403802c200d215080d1118a0281c00b4580d01120801400800125494041c1c413420754200402c44291800500107100944000d8014011000180140f025210003401920701a18014a09444200c2c040702c9840020074050210030742c16241c4240c100f41040d105811105c002c1c140b04030070742c24506511041d2481c1c1d01581056100040c803111010841c0a2200003a00c40b040b00d0380d8 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 809810980 1250 809809730 809809733
    0xf06070b0f0115110d0815040e071d011206050901021234090302040f02192616030b0a030803070507031d030718090b04080d0515031b15070b060a06020a 67
    0x13502d41d00185010148151031b0005500140c190104407041040104207010340384440032000d8944c0458000d0f102c0c0c4083e60358010f07100001102116040340c0342d00002d005020b1a0b0740714003004140280101120303540811491078664980c00d149801a08025a0009404154020b40c48494404c9124009801e101c0090002c07003900f14034040101d03174050b1004210b07152011140c01c002d204011210403000481c00414030044d520803030b80c0160407407410842500c0000302000d6801b1042c1281c08000f40203565032444200c51203034002a0b49508054681c01103252a69100003064104079582030000d40041410418503a101c54051082417a140c5040c1c60f0300310300c00100343c80c4d02140c0117054003503c0306280141c500400d9400100225080056042c4604091411400c00d90254028403026828540450001e0040301c60080d6042e8000380103005030207084800d01e011844801c00d02d50f1010704005e070781c903a00d030a100003080020b20880b21881546040420011040d02c503400150441d48049003040 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 809812230 1250 809810980 809810983
    0x5100f1707081902270109080109170c010f060603021c0e061303021908090406051c02120a02031209030d0804080315121009020108060f0f0f06070b0f011511 69
    0x540100c10030403e03080200d8034110f094040e01c21441a14600071800000d400b0307440120508550000003661100310300390352841124203884d40c652019115910b4100521b11810b000b4004007021070300c1c2000480d1038030444c0c0121080340c08540c0301e0f2001c02d4002603540160003440280a20f503c5117108108040c148a4040c0c95a408008047d1641100c0e04050f1038103244c0200300c00700c88010012141c01050010303180c40700140e080070a1a6000f070741800b1b0007056078a0000f45143c210036500e000520b001c00281c08100d100f5040302d0790250280240ca21490260b107050140c618900602c808681d9250501001c3c5443d060034130082c0c0c400c1000520a1000283ca904100ca030028450010f1901c0b904022002810031090040810f40c1d91080e8402c1c0c00798203115802000c3c099000741c80c0c0c420f10742d0303079402440031445040080701d50124007442c016030a840c1c000e00c003003c402000b41490b401d140450355010802d10003610b00c8482c84c04ca120040120402c140c036480c40300f222501d481040c12185d80c0e030b400e = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 809813480 1250 809812230 809812247
    0x10801150e0901092411270f0406090203010e09033f01030b04061109010929070b10150905041e020d020406090807080c010c0c05100f1707 61
    0x12035110800a021855808003500848000740d0032545410866007015800c07204012046003201c08142001290030700030714181b003a90600c104050142c01c1d20007100703003591f6500c00043d6400798403d00c489800500d03516123100c6c074806844000001a5203504105049103840380c01001071a080d031041101900024450150301406d850004005028804100b00502d96640001c00c4444800d40c640000060140000620f40194060b81e01086040d00c120507103002403003000c00060220b062400708000c41c04200054035107201c1e031151003503000c441c50000165154800442640c0507400c4da42400300e614191501c0d0001005030300d020b040d01c000801320192002c4410300c2254810303507542d07024122220403600d01101002415034219500c50300711049070000d401c140503003070028a0138000422508000241c01003a20b03954402000240051801100c4a00365082c3c11a2000c11030b10000500761036510707602032503007920b844040001900c4031000f8081c8110309008000c4240341700c05d011140d85c100703114 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 809814730 1250 809813480 809813489
    0x902030c0c151b030c04051e010f180b0703050c06042913140c03120a090503070e221e0b0c0304021f02190c05030c0910050405040c030203012301080115 67
    0x3d690700c0795155122030003e4040e40d07200b560880840c1c1900b80042d2054038640c004843d09880c1c040e621441c0304400c5407420b1400358100841d41131001c0500078a1004005805050711038a851440d000c10070460b641013101c2600c088a05445036500c8801070321455024003040510b51140042d9480c1802404130041a2701c04064208a00c400184a1140c4d0a00204204080c00703000ca514100e240ea103203d05039400706226000041c101c440c003180a01c1d001c40c01a041ba41e600b80134031601c0d20340408000038074120000c03944400380301c0c003a003038002100f801c0c01c54144943d00c0140c17404680e0600f4804003546008103000d81102c010400c100041e503549480e1410000b508901d071b050036060a000341d00d061118517600d0649001908424100801002000251003086c0c0541d00c844641d0b00070301c85c1106003030b52085403080d403243c018030a9042a42c001d07139101d8020901c8003891aa6900481c0c00c41e001c0c2700d80151549039100b91038141c003454045540c01005520020080c00d0400c0d511b114044569005 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 809815980 1250 809814730 809814781
    0x5090c0c0706180302030a03200c0d0209090114010806150a261207140c0d050d1d101206150e0118030c0b0301090c020607081501090902030c0c15 64
    0xa02031807840e41d0f20440074550280c00c40b0807500c41410094042a829400d0b0181d848414032105003080011036a92001c8802401d003c91002c016820051542001404c140d140d41d0b0b600500c94912611a170180d0003800d4290280221342003182d49000c08246008079140105200502009450355100010072080f4480404040c880e090000c614203200b1000c442120603030010400340148020218a00c0e6403054031000c80359203048050034410320400080018009400c07141802c02c0e294040c440c210003644000000c550090000c400141c00e0462044403103001440c80107416100031503910401019103a400320910103907110740310042c10600140101410448451141200b5410300d40780031014682c800440c805003a20340c0703544c00d1650002d01c104030186003001c0c15071061a0000ca115409401070365111b680360b03030f01c2030410005800d0190781c00b410410500b43c0011400c5151000d103000c3c8444089442c0c3c3c07036041544441c603280a041703041d0440304451040c41100b900800142e00915031192 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 809817230 1250 809815980 809815997
    0x201060b0415181805010503010b0a03080a031b090602061503030a050904090203010c030506090a0b0f0607111315240309050f01090b100902070209072f0705090c0c0706 74
    0x30300c221820010712031051008590100013003200d00741d0004004d0311288034581000603a0741e41d0101401da80c074003900247c00044600050000c107520ba802003101e1000c0d07041c04105000c500040006039054450781e10005520301e1814040d0aa0600080e074002117244000a9500443c0d000245c880c4204511841030203800160001e40d40c031250845000c90350014003c0100001844019010300000c855036071003200d40d02d0006007101c0c3c082c4103452200001801c5400240181c0050103607a600c030f49000d54421803403a281094a07034803103148000c8465003210100746201000040501c24990f500544030076038a180035211614882600142c070b080080c94041081e05c401d0400318101284108014465401c0552803410300401454003030050000015814203135684145140c00c85c054504020741c8400e09101189055200c1d4455101c3c2094500340440b00400d09545d0a510340c0c0344407504c550790b81040c0420407461902202113a03202c81e2242c121440c0800e103491031511102680103d600b40700700708 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 809818480 1250 809817230 809817269
    0x15030f1f030503070b070801050d1e0c030b131103030c1015030219050901050d0b060108040204020d060e150103020a2007170327030712021c030f020105070201060b04 73
    0xc2880c004541010a4036514841d43c1029280c524048821001145020000203000d08003a09075640c0150400c20040c2c4141c40c108108070103112810080e2240903d0341004000308d0001001d981c02890b6500d03c0b480490030034607240e00c1441a82da00184aa0418003803203008600101e850140715072000b10005900c0c23039210784000402c3d0b040d00040c0d0403580d11031050300007100030b1350b00b5419150101c80c80d01540ea40c4400300004c0070903940008044c86103030300c00b0030815401a480303150850300c0104007504021550b50020100c6540d030740b240740156074074024044040781c004000320f11a102031805519242d0000000703840c0e41c4601250480152420308882444641801040094a00184005481280c444815649410503521020141d0091044c65038032000300712120410070b00034015004180c980f11481c65200001c00342641c0100b8810f02e41c0390384207820750140180c07910036143c2d600c074099021802800c542d0020a61400d5a242c10803c3c0b00c4074a90b5020f42d02142d16500c040d20480310308 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 809819730 1250 809818480 809818531
    0x209040f060e0303071403161b051006210807140c0a120b0702010606080a0b0d080c0105010608010801140c0705010e0607020606040c0302031006030c090803070b0615030f 75
    0x10180c0039161500d00702065107001d60100045000702c00641d140349a04000c1407a82c64184825a01c8600740480890020035a50198402d01000f4000550102000d4940e45440b800c24500c00b0f22041e0740c5075030b1101030042d030800c040341001d040320171808070100105603a6410140e00c41d4101c050610703804203803130003940c9000f00079604003001d020305a4584a540c901c0702c20180c140b0700004035500485c0000290b0342e24414800c20003101c44540e2000d04948800192000421140e9115500403940390610000700c2d40001c0205484107228000007205d40c54440000c05c02441a048550300b0707414410700f4080d20f5503803942190450740a200b40b80d13449905140844c01801c000c801e000b43d40c050601000202a0003142c85485013006460a04c07000c85000401c408a11044441b1041c0129800c810300400b8825030180b80c6070f1405040c0390342c1c440d44503185946142c11007601240d01d114101d0420400e414504c04044001c480e04011904504141d280004a8100100f103c08050540c1c550448091007 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 809820980 1250 809819730 809819753
    0xd030b06041208032e09110f032e0b0a030f060503060f0402130c1d01050408070b0c010609061d06030c04090b0411120604060504240e10020412020904 66
    0x400c2e00708102d5000c1030386002d02141c1c0045480c0313004003840c80d400d140c00404031690720010190341c030001c40d001806c2240c040000c2c01d90a40b240e40c044814450b0340daa03540013800a40c0600e0020500351032032400b800b000342c0c40380618110114460390045040019401c541c0c159000041e1178180800da1301d100540e001c00030f00c41a881a0390500c500002d10070101342c0460544d00890090b00d400c0c01d980c10700203c10040e240303900c2000e40003810269a0122165001c07541038503010b0145130043c5090f556141c01440e104081c0c01000c03d000300041c01c1d0003890b90034860326004202c04501485075502d015686800e0641e10281200f1203c211b8002520705e036414840d44800c254020402c200005542c1410394520a00311000c03521140da0400030340c01403510805140381c0c41118002031403a0f40c1c0b1035807002c005d081c0140c41200c0300724500001900c406290340d01d440e4500c618002c001440e11a2114040ca084603d1020b000324501c1040240300c213907100100816510b4058070b50305d426880b9460706240e10103 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 809822230 1250 809820980 809820989
    0x903150f020915030601090b0309030f070204230f010e070e2107080d120209090115020f07030b070807030501141504050d060203040c080f030d0b0316090c110606030d030b0604 77
    0x2500200f008111140f030145000d054207076510840e481c0c031070f0311100c0a032001380c5402c1710079071045c040c00c5480c1481c0001445d00610140c804107071543c0312003001d01c2543e000460b04580c00907100410042e107038900000c5005107000b81c100d5803a4100040c3c090082024052507c3c010301d442d11100c901110490843c0080040e008112850f850707a0715043ca8460791110800710000c1d21070003d9001d03035903080c02581d034011401825240c81c0d03441e190307004da18500504a04000e50162000007083e1000c1404140d000b1409074003000010314000b80024441100140070f02c0a152a103c0140960f80400c2d04510308517009580d04145100718030003615080c0655030005501031207200e11401008403030f4000e035009a00c15040041d01546600509e6101d182040d980314107603105122200c000c004c942c02c00300207900090280c480310a100d0303040d0b0100020b80c1e0041220309803101c03501501c5c5c952011100e111051300c80094892402d11100007500c1e504d4100d0385a003095100c40d4862041d5403601c040303c0060 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 809823480 1250 809822230 809822239
    0x50c090103030807020c0f06040b03060118150f0f14030c071509140604050c010e0604051e090702190204020a140a030c1e0e190b0c070f060903150f0209 67
    0x190780d20b14008080c00300c2210f181c0010f0003003e443c0520b82c10f200f4000850408010045400e080c148411481c6035040141010f04000148508441030101c5002d01d0015000c1d00110f140e800305008000307400812081600020090010380c03050403603900c00d0300014808000d4806e01c1e600e440382000465030b8001e400c40940010070011802d075908280303902050003507108104140028a460394542c3d00ca880440e009401900999082000f0b58414038000142003002040305080ca80c41d0780200e22103040c4420382c00038054900c40c91000c14a0300542407a8003260740d10060030924080c6c00e400b0035115164030000e001d070780c000c612031681d44c0c0540081035042c40b4980d21039451b00b12a060040240030500403120101d1490070b00700f810700181c1031601455503502c0d240c105a654450003449800e10106401030142070b02072102180215010f00200001c0c0550402004582c0c20300c1c2098480303a0003a80040c0a00407411020000650000b9002d00c00d80c010010018020f1b103203001d81d002a00c20b01c030341d06030b11 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 809824730 1250 809823480 809823499
    0x10509240910200706080a110f03150a0503010e031c090b0403120c051608070f050d03090b060d0506071808191b180f1401090c0813020a030b04050c 65
    0xc0e0780c0140c3c0150089418101c02218035200665151942e030356005400010b901400051051b407103942044101d002c8803105149000d403445c0740010b03c0d4000342c4804001450701903046c101450840c7d0000040d20f400c400030414502460744d003c1e5030307200d901e200c040e003008644880421844075074440c1070140d4100034840781d646810700d0700510002d81401c000e280f2603d00186070204921a4047c0c4e072002d1154582e82c0c07100c03455070b200c495140e003001c503080b0780c0c4d041c4035220703000050b005010030380202d085501d001c07603201e08901d800d80003014002c1c0614014020f0149407001b00307000140c800c2d0025800d05240754800700c9c0020b490540380f0660000b03143d511507080001c0a03c0260140020000d0098883d86511038505a1503410b0f40500c1c0700e161074144103011176602e080c00d40e500c0407000840308040012105001c400320103000380c09038003030700b03035070350340382c00c84500c0c00d801004080d0f010002a0390300d00100003a900041010205010140032181b103240040d0412100304015441c0c030000a000c002c4 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 809825980 1250 809824730 809824759
    0x8030703020306090a05070807052d040f080a05070302090438010504090c15030b03011107050c01230f04081b0a05030d0c080d021605060a06050105092409 68
    0x20b5442524118002d001c003000045110003e44034480c080d00e65a929480240ca4030001210703160007421310610076000c3d8601910042180030410b41c4c3c10414402016150382c0380802205032000d9951051205400035030310180004c0020840c101981da04640d0040345071103e0901c203448007842038850188801d900048400090001040d1030030f52400402e00b813490381c80344140000d0f5140040c000b0007524006409128490b012228038024014078500040d40420800000e82519149034100e203240e100040c110003881018024850420800c0c20400c0e010050240048000c0c00501f07160000c161011a00c01c14501d10300089900901504044405c0c0e0080300b503c200310001c2e0090610320580510400040ca42070100720701442c03048940354217010859580710009039900c44c00141d0401a401c0049640d8034103050013165907280038400034411481d00c813003080304856442d040641404014002d584007070f542d010b00360304940c02d051042840c0030980080502c80340104003c4a62204200b4030198 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 809827230 1250 809825980 809825987
    0x51201020702040510053706050309160605160206070602070b0a0e060106121d0607020714010206040f06020d2a1407210c0507030305091f0801140a03080307 69
    0x1c40e008803010406610b8100d0300915442140c420103401204103420b0010b8980710050759940300e1126440c1c0c4460302d241c624031840c408580e41001c0082000130085c804407840801040100303081d00882c84800390308180c4050054010159404408442070314940e04649400e03007610001c9500500540d19007003a0700d001051144200c0c0d06e0f1228a24100c00d0342600500042c18604949581d00c030180c0d0091481c027108003170300d0a0341041c1507070703825100d104208000400c90301d132142c4426030180c000c0604043c15040c250f4040d50030541154405018017020648081c900010b03660700400043c2e603810f07041814070103070040a400d50304050000ca030258614001c50b00302700c4044031903514400100402806100702d4001c14501806100b031104558201c040c602d11402c0c1010241c3c00c041d000c006455039a1840c002d100c0d00100d00140740070402500310b041c01d240240c0c880c05440f0071056a42d802c2c1d4002001e030f610510800b065900d0811582c542e0f80c0780c1c004241301440d0000340456aa242003240174 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 809828480 1250 809827230 809827237
    0x1090c0f18090b06010e1f081006140912010e0109031d091017070b071a0f063703060c1b0503030a0f0219080f07030603050c04110405120102 62
    0x8040d0207022810301d00d031002407041e0002541d105400c501d054595000445000500e409240d400c401060720041103c0c0190350590725401c010750b220203541c60051403111102030b80e07602100070300620410040035842a0300035120300300020f481d1805000340102d40303940034003983d5401803030759407900c1c205005042d40301420030031042801f0840f41c00d4401160070700c1100c810403103a4210900c5088402d12039540103581d50b4031040c0d03c5e417040342c80517500c40f203000c82c180c4d0160350100e074440480d104502020812180150b030004400052150034680b440204a503405815002072814040811031440e24042d0007590414035000c5aa1051558881c0b07841e200030441001d6001c0030403800690810f5940403a00c24405103540300010314115242c0304a0040070342244000198101e4080c00700d100c868089081c20f0010b80210b6880c0c41d840e08005c80130030303007407400905204201820010144080381c0c0c0000c00700d002d0002036a00041d280b0040248c05240d0140d50030465001c21340c40e000806030841500038 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 809829730 1250 809828480 809828489
    0x1909150302120d050f0c1213090609020309060414120d0e0105010801150b090f0d08091305090316021906050a0224010e1f080304180203040b041401090c0f 68
    0x12650601100700180d580d0b81154407103100280b000c00c40f483d20109817001910854213031302c04440c2164402c1c00044265000f2030f0400481800612041005602c2801120020200d24208502d0b5041030030040d51a44001040a01040060a078207450003500304074081c540c2d04100c05580d03c552a40d4044e078050a500c0308d0005480d8242400410003000612401422444c2e03d0030407041c43c1d01d0005021031075001600100d9105422581110081c2c03a41c070601d010461144181d503981d024a0800c00804a2505400d2481645400100104d540c800022220850b4142c400140c0c030803807d00c0011313000c00d550450341d0402420040d001980f50703000409441700300360a4080d210558407004002c006850301080803000540c40000400c190b940d446003050300881800041c0002c4a001980c6400c440040d038040c800ca135200013000c01248821402c41800314059000c113525504058507284102000608060f141c0e81840c49001c00c145000d6104402080c0d100700210b49682d0344688103c1c0302580d5104 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 809830980 1250 809829730 809829739
    0x1e0f0c09021309181b050415030218040c170109150e300f0904060f0807050114030105040e19060618020a0f05090301091709010e0a03030e1909150302 66
    0x24041158640f60040e80e5490304881d40341080125541c403142058043c540b10304041c0703881104003217020307183c03409070034145503408444400242c51071060080c04900300c42e03d0403d0303850410601000496840044044820043c25483d401c00c41403055801001c02460082542c020b030301048401c4c035040d07041075031000043d40664196080001b2910680d2000192040e6194445041c440001030803001900b03542d0104007a02d4204600800820111440c0e41c2110600c080303103080c20082c18070204040d201501c2d080c68080060a1002ca400c0d5440c001805038074030075919076180d43e100203410807200080c0e02c000c252078485003550b0304051004005c1070080094030038482c484c2c40c20143c1103001700d0300c41c50410740d0740200c40030744a4412145500032031032003a495501c1d40340d41808201b010084180200700b413081e0700d80d6440060000b401d0400e510b13814a0040707403585010400700f50040c840f01d040324403e45650594a101c203402c101a00c20641240b040700e0f1414220105022101c4420000d40348280c2d03 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 809832230 1250 809830980 809831017
    0xf030f050d080708070315030f05150601020304030c0b0d0207021908010f11070b0711010221101802130e0405030904050c03100605130b03130309050d1e0f0c0902 71
    0x101c040702d00c440b0840750039010580d120301240040344254000030840419032030940103241c0f04e03912058a1b20900e14151815406000401d1410405c54142600103a0900003149070614580c0c41c00031150340392080c40c488000200f9041d00c1881ca0382c0480d0440e650043c008024078084006001048480b4014039060358a002803082c0d511080d440344841c1038011114550403c0280d617500102c040008100070308000d1801944e080d008824009443c114041c2c9a5403010500c00c502c0500040d4001854111600d031171103000c002101d00c0c2003a007901c107a044140966600c00a4075a541200500e42c000700122023484200f20030f000e40400600302c1e0040c02c84040c801901c4440402d01d2500041d6500e41050148820030451280142e00500020b8035540814542550300c4030300202682044841d0622028903002d0001010703800014113014000442c1e401c0d0300044035446d103139100c1055804840101198a05034000e211901c4500c10140380c0c401c40a1802c6070b11150035030040d4200203074442030400d140 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 809833480 1250 809832230 809832253
    0xb040f0e07051611040609020d0e0c03070302010537090305150c0306010e011202030108010510091a0127180f180b0415090f02210d030e070f030f05 65
    0x1c5084030f6848860320884480941c0e903440322091504241d0000c3d52183d40e07420001781d0038000e4000703405405100c2d00b00255103407848049604082c016440c5e035200ea004142c0520060380c004003900c1e0300183c8010781c0c0b003058000540000f41c125074119154110f81206406291403603002c0880003c0da44110256a140c20848555200c0000c06403044650400140002a001d510510854262460525002e244c00c1d03034142001089a10a80041e10180d44440800081c0080c0081200040054090400c40a900c1c0c0c80e2454000e91b000c1141410880041d01036280c401180f001581400f05e08000c450400c2d1ba5040039040e90441082c4800b00e0a00707140e0000000c04c1039214103000c00005e9034441c190f5151030740c0c50003001503005008840c01034030400d04444044d1144114008980724dc850811a0560741c010410401c17070140505500741d502000c0d1080d1620041017244c0140a1418081145c0001060301d80c1843c207141c0100c83c8190112100005110a640b5480700c0b25000d04195810643c42 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 809834730 1250 809833480 809833487
    0x3100803040807030c0909030f030506030a08031003050c150406210f1b0c0f08070807080409020901021204060c030c020120060109061d01062609060a0506370b040f0e07 74
    0x1e07c401502260b41c0180b41071005010390031450b0b000e40024143c8100003003030740e540e8215801c00c0d01e40700c00c3c2109060003070040010800480c800c80e0011a215100c11010204036809031049000d104100130051100d040d80103c20030012440002c00e51040c4046882102070340700414000851900003010f003002104c1d5036003e2584040c1654001d42101c8890500e61035880b51580841411104002e081100a0102d280e1502900181440d59400750b60741403580c00081c5010420001d1a01207082000100002c54000301151107090341420084ca119100d400142c0d44035001140512552030000b1000c881440d010861078180d800d000c0c4200201501ea59061500300c1445450311180402c240040c04500c0c058010014083e1400f01003600b1080402100300c40022306a070071f02c40541c00f4806011060b8441d000e0035a1216096031170582c012140d41d855540f04505460329000e6a8200c5400c82489500200c1900544114281555555658803400c5800d1a40e80b040e0b40808403c2030200d41410321 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 809835980 1250 809834730 809834741
    0xc2301091e0e1909050d03060504110306010813020a12031403010e1906150914030606130903050d1802090703051302040e0c09010b13050a080a030503100803040807030c09 75
    0x41c48403505040c1c100352100003210300152a0a00c15940d2140c1c030710105885009030861948a1000360802d0314108102905861142e0400c0b445103013800d0000c050a24500107503076000c07009181c1401e10780c9034035104032200042207070b019412030007240c00400c01414035640b203e1410f1180c3d583c550076494040c00d80d00c60f0301080c010204448086000710302ca03111140840b81d10364003400c6001400540d900c84218441d90aa540c6030302140400c2c00401014840c91a000100c21054001d40444c0c80d00800190760350200a249402440c0e0390100d4500703061140080e2030140107030110400c600800050482c100e0355501c0b10880c8111200d50004402c00d02ca03000d518064003608580c004001d0240d800c12019003107a14054850b44118968518ac0c0e45d2960700481c0205250317090280c3d2646040c0e1701501003101508941e010b07404840040004400c005000c400064041c500261240c40e040c1c0781040001a40c1e0003140c091102290104040002040d600c00f160300c900d1040c4d01443e6140f078488103440 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 809837230 1250 809835980 809836019
    0x4061d03030f0117100507030501180e0d14160c140d050d0c0303090b25030b030712110607110103060906050919151212020109080f070c230109 63
    0x107071560010482c1d907080b0721032406640210020340340001002d44050003206c0d0100c0d40b4200190315100104031100c440f02c50912003c1c00100c05024401c0c040c110107a544000b54201c0d41041008144100c00080003001c0d03584060b00c281c0440c454402c1030400051141290260030362100807801c003003d080c644009080c3e80141e100c0051704000c0c885074016500451580c41c1170b028185c461a03601c0c0040d0410804921602500c0c18402c0d840740c80d400b011500d0401c03541c50800341440c0c4020040d00b0340d0009042d4003224450020f600c5944d203540f030070541710366208088a0b0051008242481042504000f2019201003a6410040d5542d0364012200341d40d0705200f115000000803000c07454030700a65080354002d4103105400b0507031880c40008481440030a902995a10401584601c10465038040000d86450184000c1c083c06006448024403485a12103c1c01d1500307000500d00b04002003000607030000e10395044a0012034400c1e00d003103522044012031080c001109c0003c04241d0104180704058000c = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 809838480 1250 809837230 809837251
    0x304082d0615150304031e0f090509100b030c2206050f2107050d11180d03020a05030a05181e1002010b0307030623090a0303020f09040504061d0303 65
    0x41e140c1419407500001c01d0710703849810143c0c62000c40303070500c0c0031401903008034440d5548131081e99840701078141c80744544580c0c804008805024605450784080a075007a10003c4800015907250410070070801041580f10380d0660201004021a5203585405028420003032449001781e50b20840390140988428080c0034041131081c4038104809100101030902d0101642184041c410802d1080d0483c5600b07e03100c00008500203580b4402c0e40d1f01c1d000e030641040101c1d003a5030800c00f82c0100740b49134500444019004010800e85181418401c1258542c0c190b084012349070350314642c0400520360791108400c1031440700711081540050409201c00c00c030b03813100c0510310120130607208200074140d240121348500319034940700d9542e155681031280e0340085101c1d00002035003107220b032051424429880a980000f0380450100103180c080400e407000800d42c940b1740160f48450200c12504180926119035070070038645410041009210b90041c1410a400d00200002418030f082891380d0f0301c4115880080d1 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 809839730 1250 809838480 809838493
    0x801090209160e09010306020307110106260a1b150c05060a0f020408070902070b071b120306170d0206160c1412070303090b010506270307080304082d 66
    0x1100020303030003444880d850303141000d00d0014141c0007504074002a002551f01681c00411b0200c066040b41442040200040081c00a1407038000242a071107000c2000f44411814001c81104682080c00610800340d40610452001844000800c080d200700303000380f01c56030030303007900e1031100300d005204407a44182d010000f8985591000001d0b0064000d41000482c813a0b000d01000c15039000900c10013020348407404005031610094102b02618250142c0914140502003400c101c000c0040020114a1350708503d90300c1035500030050440040905d0f07801010070320003400303400600c4d2002150b200d400e0761440e801c64546498088400307070f07910b88581c1b00e0300c0030038044100080000c0980101049000e0b043c0240d4805102c42d00780d0304110b5210101c00c6002031340c0c505442d41046007882405000d4003090710003a04004241044841511115a00118a800c001440300040d0f40c100712020160040c902940d882d00d640d40c0d012584ca12031542515024a5485203d410030081c14942c0d18400994900510a = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 809840980 1250 809839730 809839741
    0x31e08071206081b0120010504150b0306010e0c070b0c03060306070905030d11031201031b1202010f051303023d14030408090405180d030903020d18090c11070801090209 74
    0x54444504c400038184200a004400600e014950f6001c0c1e00c85a9000801da9140600c3c02d044444004000114480c5ca0442d00c141180c50000e00c25054505440d000b032825254003911410b40d00400000421041c00001080044002213024600610060301128819160800240d400101500036a500740d4401d45c0c40c40c080d00d10030403400a4031075440c41030340d2820041480715461745400360000e540c001d14500c900c84d2400d1540c01c018009140440c074100c88940c095000920304441c00340c401041000c0070403a0120b80ba0307002c4010006644c003c0100d40c03000c0d80c0110b61102381440d050b1000d0b94003070f2090b046400c2c480c0c0714120080d4014035518000341c14540c00a0184135003000e402560f8404084c0322016268030f40d4895103001d040001d40c242c10b00c0d410780080b00d00d414081f06c1c010003054108100c1d01c0001345c0001d51520644040c2c00c0200702d0410410400c8249031a90740250001c0303061000841503550402100d00c1d5802c00401074461941d100c030001400e0b1038150070001d401100740e00000d030 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 809842230 1250 809840980 809841013
    0xb070c0b09151504020c0d020309190503030409050402041e0f060501081009020304051908130519050f0301110d051005010906120203060402071a0f0604061809031e0807120608 77
    0x343d42c0c10006000508000280750194a0318807003540d03000241c5d000045050044c03515018102c0301e2001404410800d504100200e91640203510501c100c00b6143c04c04a01195a69001010b520b038200c01d806003004110301d40c100240c00c502d204210020300e40400440c055100307058891041500c2500c1d5000c2500e40710040f0300075030009005481600442010002841000c01c820030614000c1a03d26141c2290356401402d508880e40518801d105401441d00c20252800c000e80484d80d080700c019582c0d04400d00841d01602d540c1c18200510b01001452101c115895488a801a204000d805100907240c400548540005001c0d0401180140c0301d00c9802d807800e46c0085521200140c80075050581c140d41e0400185128100e844600c2c0300b201c1000040040c541e8090380c801c1d000c44080c0491803820f6141280383d10740084064405440c1c144410915009001040300c0c11a00c8403510340800c100500180408026070740c41d000030361580f1003561030032494022641a50800d00192040000110030311 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 809843480 1250 809842230 809842261
    0x90607030c020307030b0402180f0a090201030609020a0801080f060c0d320405010e07060c0201050d090206160c0905070921140714060403110108040c030b070c0b0915 73
    0x21010800e0700d500900040e1410702070343c401140708012544150600f8810040c5030320044407911182c0804000f0464503a016440560b0800504007000038212000d00048000d010241c00452040340001b458458542e032102d5081d0480d9000c1e0150f600021601800940300c0c00b055031100146881480800301103805a40190760785c3e20b84042c01200518040142241150341d00004588000b002c010013061000038041c0b43c8500664201919141e4100040501081c042040c06410084089002d8405408035800a0900d54004050544070a403d5101600160621000320f402c0b10040318000707000c280e14040e0754007404082d21400e070014200104c6486070f000e01c1120b41080c0700c50340c00711400308480500e1401d000340000d002d001480c1c100710703d0001d0102400165402040104000c00124003844140c002c606400d01e861323405911503041240841100341c2010b81030a4154091001c599085a9500c40700c0f44a029100490758521002c01c0e01c4d41d250000100c01c91005038000fa40101148000 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 809844730 1250 809843480 809843483
    0xa0203040f050d080720030703030c0506070c42060602120a090e040827030c0a0f030b09030d021908280f0f05040c0302090f090304060807121517010908090607 70
    0x446c0303440b841400092038007005070f009401054a05290b80180402800350b160b01c06c516007080058400250b42e00000d6420f030b41d89903101d07135080207945210805a1400d60800600041080340d403181e07002000401032000d4426000035224a6a00008031484001a1408003201e41ca89107207180c81c0a405a84648000f4001c9801010401075600000a002401c086100d04101c481c1007990031034090510b00380841e4403007032103070120000800042c900d420380744098a620034904c004507110420303094607500400301e11003841400401c5c10050800c122803880f084a00603940d941a0ba00c40b4075108802e1252000c400500c14000200c1c4588001305412268819100c00c00029160b80102030340c1c02110400c0d58125450008068200154908985400e8000b159501010b26504000034002d40da441603200e1442408041000592070a005641d101c0510007016400d1042c50565141e0368612440360140c040c8000b03404020701e055100520588500a51020100349060490001c10040c0e4000d43e10 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 809845980 1250 809844730 809844773
    0x50d05160f0f09092a030e0c0f06091207080703052a03030706151706010f0e0906070c0302120438123417060d02010f02010e01020a0203040f050d0807 66
    0xf0350440103164150511000c081b03a60006070b0302e1200f44000e043c07407001d000c00c0784034600c201d1030b03440d95540722000c807502e0120032200f400c4504500c0e6184c0381000c5d26680650b5290046903400070500001040d0380034501c1c202d1610303c840340d1120880c801c0c2e0060300d030049501036005124040019406070b00070103660b0b5070710031081801c1c3d5940c1c0c01c259480803540050b65840d04001c0042100f440301c80f01c071001400c404e00c0250040c0c41c211480a0361440000c1200c1c081004940440051500a22a0301015200c46001c25529a29911075012494290900e0003000411400703228810a224141c1340c650204662854902003404510079507210018001320980c0200d004000c2c0030098000a0510044c1b0a032030b048540740080c100605424005444190502c484408100300d956452150400180d82424180007030303980c41c2812030040c086500c5c02c9a0540c80002c108040d29000000f502c11204164400b8009580300d40500c080e02c140010000c1113130a0901004000400302c10188080c0306421300d = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 809847230 1250 809845980 809846021
    0xa09110d050715091707030812101809030e030a05061f18090c06030501030804090203090a0b010e0105030c031c05090d0510060e0c070309090b01050d05160f0f0909 72
    0x2a5503550821070f580d100b1000c0395504d80100044410880540d0545a040c80900203c601c1c5445a02c0d061003000540b428811030000000c1442850105502c05001582a0858a20812800c500c001c140c2c001094020850301c814a035440d150000e06200c42aa000d0040c0c040b0780c541400040319400324080c3c6005a800031000420034992010300346020038a4203a0110310041603081005013a141c0d074121901b01410b01006101060905040740c04079100100300603502d60320440007c2c00c140340301c0301c003d2904010000005410402c440200e059030001c03030a03503101e441030004255484240c80c90501d4041070850250b410180503601501c00550041c2085250724000d0b40c9184c02d184034074809203907050359802c0a200c502000c0b012070754840c051a4071145440c0054602510b07001c0944106540ea54403000b60a145910400607100d8a400d40381c0d040c099070800b8003124510b008400624000548a50460011940b241404100035200c54a0b41e14505042500c5000a000c00b101c3e214085070804 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 809848480 1250 809847230 809847239
    0xd0c1208070b0f1b031e1905240d030306121a0601051213020d0b07080f0c0703021b060f04030609050f0114040b06010320211e18071d0a09110d0507 65
    0x6c0103a44100c4035000034011085021910804481000d00501d5240c0d0080c074506030640003d400303281e0041411540340003951081d1404601400c404d411207860460100403100070401d4618220400c8588000c2c007010303554660004440c0c90040d500000e070440d90b1680862101e01c400351002c401140082e04c0444a2501500c1d90801440261055400038508800300300c0f852030010390081c0c101031304441036403500b4402d440c002c0d03454078084101c8400001c19200012541d407210211101114001030141e181d035502d042440c01803411150940307050246440d101400c1c1c8040c0301c3c264132103482c3e01c0310f22000c2d10f558444081e9820028005030601d032740c800c428100180b68410201032141c00a9103140e440302c495003485000441d8406031413036000444144103802008141a850101c04101c0302c02d00da035141011580c10142c26960000700707024180020821910303007d80c4a012840520030285162a040400d004507200b01601070503048080500009514201d18902d5009024000b203502c1c03540c0301c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 809849730 1250 809848480 809848531
    0x11010f210930090602061018090203011a01020106050406081c020309030102130512060106021902010903080a08012408070e2d040c08060f0d0c1208070b0f1b03 70
    0x602d1000c55418044202c00c12032254082060400b8040741d02c060301c01030130003418210140c2c13030714007a02d03056201d82c21801c00c44098940c056031a031900200244804803001d201000c1c181100391102c0d005500b003203800700303903400c09014110841394400010040c010481002c01c81d502c42405030101140001c01024202c0c0c1d609001402041c2d15002400075020700e407000304911101c00d102d0004898106100421132207030041041400c00c4d2032824070350407030807040c801200d07070745001e8000414200c1c02254101440d90f00c090000e069502169030a0700c80e60311880a0385440010110810000d000080051405480b03103840c1610480050060b00c40c2e1083e01d03102c046207004d100858603100b0014810298580742c1409a03d4030f140060608000710308209002c80d80050490000303d0152020038448010440c01c8048400107044a070981c80b1a04440e1812547d02d9201d001f0699110300c6030740208131102da0207007a550050404e03858110140c0304d440900b103402c2e0030040007070554040c05064081c28404 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 809850980 1250 809849730 809849783
    0x803070212100501180b04150509070e13020d15150f0e0306130203010b010e09061005040b040e0a0b060a0f030e0717030702030d02060112061a040911010f2109 70
    0x9000c88002d040311601c003541704490b06a07006030300c154103100c01d01c80d6103203103403030f003c010b58000340e800c06515510b2080070703500401031003001c540081328044218821745850b400f40840054a04040c0115050112010415000c501404541c144051825001e803401580c02203100341c13890401070908007118001070f0800c5411940e02c007203100c1c3e210b455401c42c9030030310900c020300d5000d00b80141840350340c1020880914000f4484d6000d00d203060110200742d0301a4050b1002000010882d0359501c0e20f0b9080c03c0c52154003910701c1400a41030100d41d00c450b103030400503602003910a42e00e42d11a074088a204038090b207002c281b082102c0c0a09840491158440a24504c0301103a05004583e68812481072518044903d405401150440d400520105004c082d039050b40381e4121070086400c258182005039250010421a641f00d464050381c5810800c041c3c4020503402404d807202141d60300440750582e1140703101c40701c0948840800303008100c58589940006039041c02003444100444201044e502401c1 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 809852230 1250 809850980 809850989
    0xf02250504141501051603030207060906021303030e0409120806150d0c090803030c03040201081f0f060f020f07090905030f0f0c0d03110703050a11060a051e010803070212100501 78
    0x4507000403c1420349032801c5405030b0342001c1c40c00758500034401d40340328240c030705264000307081580000300c2d030701480b0064005034200c54016404641d07c1803a224908628140380c40103c0101d00010144a21458684103e802e0710380c10610381c486405c8041021289984010102070340f0444620340340c2524400200a0007026454050028610349282c0004d040352f001d0364030030400d81e40200104110754100b042034a80013603081c00c0420300398581e68481411390400561400e4003500004000440508001d00d06046400548812450043c0c0050483e1100404400c030180d584c0155810441444d066002c40388040c0580181d1f03090010400061006074002c0b010004018800f08029120040a0220b03c500300f40c0d5040c100111420440748240c2e501078180c0282c00e108000c121104660300a03100c244001d0030600a030350b1140760080446000346415144c1c0030f504441d4140d0000740d00d4550220505840000c0003e40c102a407a5080040c4240d0f030070000d11050065041a0901c00341c14010325000c2c1 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 809853480 1250 809852230 809852261
    0x18191b0b030106030b03010e0705060a21020d0b01020a020916020a1502090a0e01030c0b0d020d05070c050106080114010b030709050306160f030b010503060d0201030e0a0c080d0f02250504 82
    0x80d4540318005068405d001421840390740360484913007084138002101001c540d4160fa8081d12011a80820ba9102401404ca0820a400500e2003174480c52294010031714003503400307020008a44071a004980e14941040e0080d003100303903c1d0105030440c0d40407194a446500d140f040700d0295130286e840245d0014901c03008007550340c001c6180c0116152415802c8058140c0520341c0e00e60758503586503094186080d200754403e0050000d000c030320101c40c6404a07074074a002c00c1410710440c00c12440c001d140c1c41c28800c00360b5495203403803001314196034180283c101c08030152400320607507400d103c410b000d15840034164406010315103c00040f640c0701440901c5c46001005881042d5010501000d800d101c0706400d410100751a00040c0400d0340c0c0c0000279a80c1001c01514240c141600c03902c0141c0080420750040b07038603440303101d100700d0401109046080a845002041c1c1c2d914014809058039600842c01901d030250f00104482041000800c2035008802020740b15001c41c142d580740443c1c200c3d50109281c41a1 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 809854730 1250 809853480 809853487
    0xd02040801140a11120c0f0403050a0b0c09010212030a0605120d080c13120c08060112050709140c070f020d0b01091406031903180b0c0618191b0b 64
    0xc80c890000b001d90000c00c08406010080d00054400601c0c0b05a84030300d0040040e544c007142141e0401015030710510b29240035540e40c0c98481c10b00503501d00808008594030001c12000690010010b415a0074611040c3c001701010b21310748a85601c0d90304000e000d20b200716501c410001c0d1b26503483c21000501c01c20301004d40301ca648001002030900500405101e0741c40030420100e4107490740352240d00204ca8051840c0402d5152138030300040c00e140a60f00c8040280b149400104801c010000e0249081d0310810071039140582c1c41180703d060f01c0580700b104102401603000100b41060308001800800c2c418620f00082e01016800a41500d510240541d0103103500340051141c0c04061007049504042a1035425251030440c0001c1da842030b01b00441c00b48110305107040420180518410f50340b89481082a130368094484000844a8105105082940c45004003042c190700800f4a40f0654020303110240080d10000c29015a07140c070b1080c0c04aa0b0300b10080951500000d5244042010309100e0702c81958 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 809855980 1250 809854730 809854751
    0x4090506101809111201020c100617070e040204050408070804090b090603060f0106050a020106080a060e0601060c0b0103080721020f0d091d0a0204120b060102060a0e0d12020d02040801 81
    0x9515500c04000b0703000520384010b8001092822880010348001100e0941c0419052920b03540a030103004480d81092050748259a04000b403900080241ca6507800c2080141c400003540c60b554401901c90399414040c1000402d01504003500000d40c89030262000d40c5c5400c8150382c3e803203100e90242d4003003d01182e5903a00c1c2c0b042450080b564640080c2e0803401802141010444010300090620504090101c00140346420318000e4100e100142401c6d4180c4003100071509001002c0d010700c0786008568040c4100101c0d03c2c5000308181c49420790000202021030303083da036403c142c2d0390240c80c09032038881005422281c580618400f40d10768403201d90284c103013503004522951800d420b00c0b03030803818095101010302c1400007a00c004849800080c45050b001e44818080100038800ca03040000348040c0c5100f0034051081c00031145004250a07800c54080d44e81ea00380d40310403101d030755100f400c1d540c03c084078400e580c40c030070382c042c01a600150a0040c03901c144101150b089a0242c0e1201601c0d94407031310442c0 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 809857230 1250 809855980 809855999
    0x240309070e190f05010b19120608030d0f2913020a12060e090c0f150f03101208071101030f0e070e090d020712240509100b0604140409050610 62
    0x20f0404000c480511180d4101811000240943c0341d45400840304440c0400f90700b84241d15a203140388203010f0800c103039501c0d600e4140c0c0f2940400e40040d007442c1000e0100b607091300b041c40b458002e500010070300312001d069485034203941c40d040c00c034880e030020440e941d460101244c0e00c02420121169111854203400d62040001034a481d58070007007911030141d0400000c408003080402103010220344010070001c20702c00198802c040c2d26110070039207001203550282d0000c00001507000350352280005944965601150741c2141e00143e009152040071311a041c0021140118a80c00c04414100810f014901c1d4103d41c0884d1072910380303900250b01c920b004202a0500402c02c40d00003440102a00300041200000380d82d40f5407501c603c10f030100b542540f142c14081c2c1d040841c802084004100f050303403070542006801404d020b40c0c10b42c906000d00381c0c404061280302c0c401c80340341c62005800b81e418149007480110b1790a02410f201074020b40c07a1155980060b909008aa10513076480c19040005800c121004 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 809858480 1250 809857230 809857241
    0x70602161b0f05040f1b0c05210d020a03200414010801050a030212070e0f1b030403080721060b030406050601090b07111309110f240309070e19 63
    0x16412454000060014040b601d0302242900c1042d00c000c40e00b0a006090709008160040e001ca0f0f0010440d520a00b01551241c0c1100d0341b41d005070200ca803485840303d039282c9034200c00342000c005514104051002500d01d500600314522050500080b00307a5225103000380300500d2000a4020300300068103000359003020f01c40c89004d5800707103440c1042d507041074007140701e2508900000e0f1040348600c0844141e203c042007920301030881d85022440c1801e0000103030308026030548002174006140d05c1001c01c14031412060f680714503015580d80c81e1341d48601806584907230038a00c0b098041e008503803904084c80c0441c051030780141011401e02e0742d2031429041c80700498802500c12810806000c4003000074000000607101c6054024076094904240e600004a4000030340e6040d070b42c0a42440741c018203002c040c00340b038a80780d041a100010100c41d44410002d0502e0000c03142000303030111541020354840f07480c0145611000300c03400c60703414545419001c803c0100c00c49031038041d40d61040c0304400c6e104c0b041c06003 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 809859730 1250 809858480 809858513
    0x60108030f0d0b040e10020304020f0d05030a18050307080f06010e060d120c0b0f0a05090606010507060513080c1e01020406080c0702180108030c2a130207060216 71
    0x20318180a041d50941c99184a801080d100d160384450341c80a107a80e480d03001c03e0741040310310304840d0701d40da200c1b075104040e42040b00c00741e05c10188241828010f04241c91918051923100002d1485c01d20256001d68200e001c03080c151040c400c16141c00708641e1420080c070310290840800030845010b081c500c8a10b8080d0581040003507401c840c0c18000343e61940700000355803a501042c8440500b5014404481084000a01402d424a1101404044c1c2c090701c020070f01a0b00c545a05102c25590303d02404e64071803050302c1c4180083c40800221000c15103039404280c11a00a60b10300002004030b4807040780a411291030000150080c00d103c03540b1a44850b0049074880b6104020741c10315103402e0b40038203e410010035007044100001900c10841d0350725145250074807000c1c250a04696103d0800342da43c2d8014001e40d010520410b001000d040d0a0302c1303142c04c1c200302c040c00380c0d00148148034148135068100300c079050b10340358090100c080012000d00103840d441c000c4070b503d140351a1040c1003d00a041c0d1080f00f = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 809860980 1250 809859730 809859733
    0x1e0c1e010903080c07030e0a0335090d030e06031e010f0b041503090501110d110f0a0c020d06090b07080f0f0a0b01090918031107061227050d02060108 66
    0x354600081c0c001c940541e2101340ca00c9040d03101c402c01d06060729000321b4900741950281c64050007104015070790113204c5541c060210320350038203807440c000d4040d00c403442000000b84003024001e6410318a0100345090040388a8a401a0600701c1800411050707001035a90038004c1d036036501303000c0503d0702c0c100060340100b002d854074080440c0f41141c0944540700324003a444a1821014181c5a028040e4115a07449a4448001c122400c45044081141d07080100844602420040701c1103092000000355004180d0500c54030349011403140c0300395400c021109040703070003880440040000c524070344030340c40400d8000c60300803003d03141058000700400350007441c6604408019080c41012140c03115180d6009441c1c000008141c409000180d80700f48095004101041c10000c4124845400c0c0c480440c110740329445912005851003200c944401c0f640c0900d000103031054600003046610780d0010b00604860803c1e0118030642031149400096800d44243c5290f400010b0f0f80300da17150304100b041d004008800 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 809862230 1250 809860980 809860991
    0x180607050301061209210c0c090b010207050613030f0b06010207060305040812040804090c2a020d111309050f0f010203070906122307090503060601080a021e0c1e01 72
    0x5000d82a07081110b4900c13052943c480400e01040041c1241290007400f42841c407103500084c00c8020146400c00e00c084070203140d41140080c2001460165410340c00f4141c000d0300660b030401c41485107581100e00320b1400e994840380c0001c00b0030164040701c2e001a0149981010f18035066002903d02002907000900305031800040101140c0c0c1241036844840841c100d2560645442c1802c2d141e5020f590889480145007030701d00d12010341c00009447c40901481d00a41503030102c000307480e410500045000c3e41019030a0301c0640001c0c1003540042c0114001400b0004600b19078058000700c4400070412074031a03000d0ba240c031420303e0080140306200103020000354618603003810000c10403c480d1241c5828131411040098a503542c40c0c0007c0441d0588072014500200d8141c05003102c400709a42c100c0100f81c01034404580381c10080350003489507906848a03000790310345480000013075208105001d08000d021100d1104900503800030b0091908842c01820f0521060f6001c3c529034907500703542c5800da850003 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 809863480 1250 809862230 809862239
    0xb0c0306060301092d0b010809060f010312020f07141c08182704030908030a09170f012408060613020901051605150703141803040905180607050301 65
    0x30708aa05440c20720304085080c1c400b0305c1020b075400d04c25180c0406800000041c540004000c0d5200d04680d80e02640c1d810302c01e131a40c0d00f1040e242c00055030762000e500d00c81001440441c0c081003a080146020b403045403941c135803201c0c1e69414030a040d027200c05c1c40e18122a14071120328020001401e100b0521014664200c902e58580c0b402e48105040907482007081041c00383d040e950700f001c840e4140349091049004050520340ea150074141120300700c0128211240c0881c06000010035030b1102807498035001200307070130244010001c001c5810407180a200c2c0c0d40c1c03d40c121030800c0c020b20503452207a820681e003103800d80c0d202940720480e903002500907138007104c1009400c0c1d403100c078014004420f00c040180d55085520040f5036520600b81784484030401d001c4040c1c20441c0028840101d04130004c3c0c414041d0b2035000b030850aa80c1d40c0030701071100c00040c002240d801031188014001c040c0c0b014040305c0c5440e035541c00c41c1e000c3e14400c0b110f065140401e43d48a240c29217003071240d40d074000403d00d05a032556041 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 809864730 1250 809863480 809863489
    0x1a0a0815010e0f0a0b03040b0405010e060907060315030819080106030e0c04050a0b03070803070605070518010e21012003010b1210090504050d0306050a050f010c060f06030305070b0c0306 82
    0x500a002d4400e9141d401c1030980c548490b102d100191005a041990300d107000e00304192a194196822900380d03190001c108541d25010070a14060f040f0000a001080d00d001070440c0034118815800200c40203460001001815000040044c0c07480300184030740d00010301c40083c0224074141d200c6001d041c02c0030b50001e00b005000c1486001008110307800140e544500c00c03000020030305d03440990303054031800002142f0220000b000d0b050003449460203001d550380381c0302c0480d0325000304642c80b40798409140204c8403640c02203e4103020620043c2107040c00c85122243c0040343c0048544000c7d49943d16504076001d4205050140e407000c0c9481c0155203503500d04041a8800c2c451400c0d042449081c0d600440c42500d001c1c0480310040072a00400e004904281c01c01d0703a1202c401c4004080840d24243c8005110706204150f00215a030080030003424801b2100150382c110000d8030101d441554510b0551a121024810030020b14000c0d6600c1c0d480f1021840c0c03841a0940280000625140c01d000b0000c0684c3e4 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 809865980 1250 809864730 809864747
    0x1031b020307300c0b0a11040603020309100c113d11040303030236150c150103020a06091a09180708060a0e0105091501091a0a081501 59
    0x240074105512100703d50318802440d02000c1201c1401c60030f006120000507611040440c02640642c850492503140c481466040791030315182d0715940c40040c84104a4a4003d03400b660740311428509a40c0310305070003880c090032100068405004034400c1c1c000c41e1040103041000e01c50050440c0000d40c54075070350002d4941184212420008094000a100500c0400640051849405640010352116203c2c98040c010b50440c5817010301c0481800c03032341101001c090118602c2041d01d4154401e40c004000c050010140d4070140c11165040100702c0340140e00410000c49200c1400e80d90074404d1b65040d80304201780c000c0b0682c001c808202c2e041c181070085e082da0782c21015206040d1008142d50380349040208403001100d5044003080da41e080c0070000429006161a0f202d07a1048413142e910b00d840e0010024100c0d801c1c00342941103100e4000090403400e40300640d10000c40305051010038140c0d101c081100f404840c60242000708004120300c081355400180013a000119500b44060409550000a04c080c0 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 809867230 1250 809865980 809865983
    0xf18050705040504170d0f05151f03021201080703060b0306040b0106080a0e1f060803071a06030106081902011b1a15062a120d0b062701031b020307 65
    0x40c3d6600c04070702003183c201068110100e404a606465440304401400240000d4404d070091071704010000d1070000310314818904625004000403090f00c0c540160580e4018400003500c00d040d82084540c1d019207402051600a0000e400205003090862410f00300395800940514000c0d4040c005200020786c22100c4141034a41e1480d02e0840c40d543c030008a4041d20300e02c015208180102e4a1380000010703002d0380d0442010704400c00744071300c130fa0b507003c1d42d9980d00c200b42020308108420840500040c60a4011380d0b0050001000429566101d4050b00d09000982d484042c0b014224903500b0210350b00420110469809146400044000c0c3d8481c070001030409000310180790745160000f03080f03008600a0746c1e01122301500341500c0303100c140300e4400c2ca400c0350010000e004c80405100300f00c800780040c1424516000c00c800ba401c101440d1102c5001c1c0090558055002800303000410301000071913080e42c0c44807000401c0701070250300c51001408070f5404d00d4a022040080100380b01100303800008035449035 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 809868480 1250 809867230 809867239
    0x19050421030e0a1d011a09130e011b1e050405061b010501080c150906070201210203130b181e0c03070602011d01051005010c06021b010f18050705 64
    0xc0d605150403120884000c0c90103a00200201001c2490524600e0b10440c06410111030714040e40c0303e110900c000807952402041c50041004000420b003030080300d12003c6000002c010a03610301c03002c10303a425211841c801c241c100c004900c04040785030340082c0041401c42c18620020086261000c014441d1141d4080c0b18000c80e000036140494034a02c1609a9902003c900200810358440c10581d40314207102c19001e1094205443e41ca4190101a044841d50751000b403105141025640c015205003441c4880390081c0e00a5201c0f0600d0401c441c00114442c003601010310305072404601c1d10084004000e0b202e101800c812940041d05480002892440700340120b4800d42c040e1042520300e46030078200070055405000700a000500e40b501500140c00d0b0900f100b00207040c2c040345803402030880e0780858580c0c08401b0040c108104950240d004028011302541015180c40e10740300d0908400741001e02c046419a65034940e28401800307604c180e010345c0c50344031902185070489440d1680c1d220003d002e1244034 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 809869730 1250 809868480 809868539
    0x1128150b1c020d06050c0c010c02030c162d0906081c110703060e0304050a030b070206061203123402071e051002011e0b03010c1121040504060b190504 66
    0x1901e14106c2a5054600f5100086c071044111920081d22900212842809841803098921100c002e126a19003500c40c4010388891050704072600d0381c204488000d22100388001690042000c19240c007814000e020311000034903075010420100026651810307200410000c0e1301c00c04803402840410180100c035082000410918a006c0744207045120740d900c80b5602c00801540081081404604140b0940c8560281c0305656910420700c000c4010002400c1c1d41ca8100704540070510f09090502600940c0e4800d48103070000007440d620103c0c003410301c400c03c8540f1a01c1d000112041e8100505030192162407200a00030b5100d122141d88100d0070700030f40c4c0c419141d03e0661050a4400d602041c540116408404441c0c00442403031001440f1041c1440e019500f440c038803424050040841c1300c90034000c41c0040a4444203152070846100103c6010100010100300c0001e441e52030f4060720b8040c1041c5401c140e65283c031a040c10b0080e02d80f040e924803c2c06405d00040003001c41401c40c040407202c0003040d2481c0e = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 809870980 1250 809869730 809869741
    0x40c0806011404150314090312130305120408070506010b0c1b1207120b0a09120806030109021003020d150807061110020d060302010f1128150b1c020d0605 68
    0x680140e40020804e1100c803904c01e03110320b62580241188803041e181c8000c0c15124030400b00d8a900c19418520800082e450100d03040510228505103264024904581001195001000f800a00740e9050784c01d1240070401c281441000c0c0b103001d0040c55070726040d82c03400d4200710752140c07140455001740c042030340c05502d41d80c0e4a4030f85885c04003280180c0401c1c1c524071071315400c25106444442c20180c82c00301d0480f000642440c91441042e40407034003c130b4001d5240c103282000b2100e01c44014942c9805540340c0446000684429611a000614035240035882c3d01400888004450041c041c10b070002d030400c10104034080c400300d030311001c2d610399240921161030b201c42c0c440d1805000314541140c451000985462207403240d804001528800d07a80c17403900d8285488101c1e01c00c240c00a2060194200c04c1e802d44d01c0d8003103090f18511141a110203076044124a46503904481c0b521954010788545405000003503250041410b4460151924018103180b002d07000729040034901c020041040d03907201c02240 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 809872230 1250 809870980 809871017
    0x12030a180201350c0a0f031a0d050a0b01090203180c060904110c060403020307060e0610170123150306010326090d0624030f060f1113080c040c080601 66
    0x3501d0b140b0f50120748040c0c10a0030b0322201d030ba8050601c50300040c400015205d04c044c070901480161402e15030400013204400310410035003103c6500112514070603003042c0c00010302c59000b541d000b8071026400580341c2c548403070b403c003800200000484845d001031240c88031613610709042d01d0b81c1540a40740000e1001c4000c00019440c07007500441c806910070f00d02000b0400da0300000510100d03100c0c010038071010705a44e001d01d0303540800b40c0d98071410034000c10050020400f04168050308130138100002c52200209180ca4030220a40e840280440d0b00d800108054618a0f0504209081c015030041015600d1074965a62245640b040c420140d0503214105441440c9541580c0c0110b00040c0900120411317860310300020f09481e01c40080240e10031101d2100709082030503107401c50750403140c0348103010495034a000c0180041c0e0305c049401c5542d520368036aa1078082c5d015009104558908030511401d00354564680003520340c1c050700c034604102071000180e5200709825000002130034403002004a001200 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 809873480 1250 809872230 809872307
    0xa2d032d0207020d0228091404030e01020118030806040b0a1d0411130f1428110c1006150509091305030a03140a0c08040308150312030a180201 63
    0x6540000c6d42454240304501100a481c100100716101d001660303510400341d41520000200c403180300b142c0a00041c0400d000740d2610480010501c000a246209070304000340020000805070000342c83e070003c1001c0c0e801c2520800c03d0707049040781d8416401b450030310100c803d000200024810408081c2c04102000100840c0d07090044c0010081400d01c400740da07801d4024805085030580407820320704030380403003284211000e02071070032094001737205001c03c0c00c00e103030010910414641c0d0f903036101d0f51240702c3c299140203480c00036250350242240601020004042d2820382d006440401c102e03400d00c030101600242100e5460406a0384440207a80c0c030712021a66a201070f001034824003001070f00000752a072591102d10388541d032100b900c0c56611051180ea0803a039010310340002240781c0b40085004240aa5500c1d80d1011b07000241441008900c000709040050036529084d42070404010300c800010f80d4040d071180605500f103100750400301600020b0000160081154002d10040301c1302a01110402c440d = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 809874730 1250 809873480 809873483
    0x1b0d080c010c03020c010f09080901110708010c2001180605070c02132c0a0b180709060312030203090606101103121f060f050a2d032d0207020d 63
    0x7000000b0001501802942c8014140745080d46003005003a440703502d620860302d105401003030150400402e4401541c58001800403548640316004001a00c007209000c1c2e011f8000382c958030420104200d040000000300d41d0050350344c59904000070005c1c1244041c4a000c0190340282c001b00d03854403070301000e4686142c00080650806208186039000040541168840d00d403241540031003100340d18004402c1c050f4411014a840d0451101c0c42d005c00d5503820030a400c000c800100001c003100307040851f80341c405958018105191502c00400c00d0201d012400c80300042e01e170401b54614071341000b50f0358444400400092140620f2882a02014440d54000398100d40b82000c603555800780d02e2800425203412181c100c98800d03004004030703020a4100407802250001d072641404400310717440540d81d50300710030b1200d010000342031032b56003903645000c00c0d80031003040301e24884401d8910b4a1000301501c6808a82250004c6a4041081340c1c2019007112103c0d00346800e00184c1b9650180700003950242115070 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 809875980 1250 809874730 809874733
    0x140a0c06050f090c010302070807060e0f0a060606020d0302031e07200c04230a0c180308030601091e090911040c0801060806090402010c030c03030f051f081b0d080c 72
    0x2004980041444564024402c65013282c0303a01c889a0011400d9200300c08005201502c00c0c09400002041d54004045010114013541c00602205202a2411003c070f80c0954540e40c49080c200602901401541c0b01185186415450351400080590001c1c0745c0c1080140e1620b0000002030800e071080362084079040300452100e01d01d6025615040d5100805001e480c4194038000d2103c0e40149504482c01c541c02503824107170320903659100c02e90b000300a4107016400344040c54140312840248070290b1400b4500c0f45290f15100e0500d040010106100340c0c2001c0100103c4041281c0170790a0b00c43c006c400c13034200c000e01140107465407400c45003401e01d201545400605007402101c0c21a00015114180c4801e5075409141e65250010060740070f07030079034010780801c03000032841e00071900c14001d60020a01900700820220908600c4500300c3da004c07280c5140600f50145100c101150312034207403008281010040184c2d0070102c9001c92090010202c0e1441a035128030604100041001507910f400113050 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 809877230 1250 809875980 809875991
    0x80c1c2a02010809250e06060307140304080d0203040b01030302010513020105040b1e0c030301030302060c12150d0b10181104090b0a030c030f0b090d02100f02040f08030c1c140a0c06 80
    0x1414544582086c0a001e805900c10f00000b0490704241c0c003500d03c940740726690919165810140c0c240b555102500c2503c1e0000e04120303100b0b24042030b00056005130f02c240080c070794075032440c140282100c80c040d11050481d10144c643d500944c1c2e202c070546054a420707204a030395861018801115028500200100303411002c910b803080844084040d5040ba4080c0e0261005a81c0308440b600061103030950703030004041000c020071440340c0e19007055040d038000540300c0307a58079a081e1035062006004a488401d0300d50141c6060055140ca010085584000390005100003074a4407280861030107180141205103544d50148411a921a90084020354004a0100d501503c1c6d00784801c5c10025080305642c1c2500c907001058034850b00064101420105a01a00c2510303038103000c45000e03114048020780c5a640a00c00851124024082440104030450003141e85060181400e82400800040d034030905548041300100c2c6500042100310440603052490f81d10920005d00b40c81814040310054506031614 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 809878480 1250 809877230 809877283
    0x20127031403070f0c0f060f05010306200301050906060f0a0f091a0901080403200312060402281e02060603070503010b010516080c1c2a02010809 64
    0x510024040c02a80c62440030490800440141d20080d02c800000806011141350300078451a0318015181c458540c1074401c04898a0781c000390355480c800d003200d25540d40d004104010940c440c51307149030410982c4e9114280c082d40d118046010510450b80038005141c0000d0307980d84d0361030444803810000c0342016124845180000d00002d4009041801304800c0c1d1404203042d0403080100110003904045a0702c1c1c88410001118501f4010b8411414010349140c418801402d52a4840400c004400119295031540306003606c0c0720300242541c1d02992041150f51400d01502ca6000d100e2080340d031541c241e036242802c1c102ca24400e030318800c0006800c0003101403c040c3c0e0104142d806071501301c0403941043d440e00101400ca80c5400c0d2035a0102d102040b0340c254070801d40c01d2a86030180541455420403418409107800d01000c00c0706042450031028100f004a074100034102d1807468160362548040c000c064444802c459816030117818081c40c032001031076422080000741c00f48a90250246040c40b0803 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 809879730 1250 809878480 809878541
    0x801021b07050d0b150d06111c0203060a031205190806010f110303070f17010e0601091d0f0a02070c0b091203030f0105060708070b0c07020406080f0a0b070201 70
    0x352040d00403640100400010749242140e030b03803850650080040061611103400c1441c80070040030540e900880004e800f903000c125548034400c002681c808030180d075100114940d0440654107403040c81e10034414828445a91074014521080d260302122540010013040010384450050440c4581101004802039203015400303021140148002c2c9c80791090321581030ba00341d403c1e10040e0401c803620b034805e000050700f461007a4000d182c800014105040d00609403201180800001d810158003078040c1d40900c80d441d64814410401000407180301d0706200248100d041c0041d10240c01010800d5203040440c07160000eaa04664005030301580c6003111a544a441d0070090700310007100d0b80b080b01100000e50720840d001c01200e100703103060b07410300c2801d80c201800c07c40700f5040f620003544d0f160024002c440004030030010441c00f541414a5468840d0203601c104400e0b11081d40218095420414000c140410002411000c2651200ca050304942d01c241c3d00300d004011a40c0101c60b080515100040300080 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 809880980 1250 809879730 809879767
    0xc02120304110901050616032001020310050907050c0d0305061206130b0a0b0a15050c120c010f020a120506060c0106140f01031104060302130f0303110c0a0b040915080102 75
    0x40c1074075440c843d0380e0b0b1a02001494000c0b050f0070303500c0ca003030768803128002840f54000d60f0400c1d4403064070200760000300a2481c2260802c5501101c44100b0000500092814121b0168421110315200c1c0c64145880080c3c0e0310340c190300c0300c0002410707260400b2460683d01c207078030f04130740390722130000c4488502d01550848829025a00156152040d001c0440e20306005030013020080c3c00064610140d0914110480c0d401180e07043e42d80c000c100080c015000c003020281300c552590b12442c0410b41d00c960f0585c198608450b03089a1390a0b0343da1042044c1c183c3c80380c00c2561180c40c000744103400030345070b0f44250106003540300d09254550035510302000803400b00e40034035259982c2c010544100910055410066044402c09000c564100605100804c2a64803940061400303191034010082855580c009480301540c4a03082140800c8904061245035203041140702441d010032528100d0040c83e00b41c041407184500d0240604298695040807418501003051400420090000719907409498104490800 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 809882230 1250 809880980 809881013
    0x20a0606050108130f020d05030412140313090c02070810140a02072a1e090f110915130f1509050102100b010c0210030c020f0102070f03030c02120304 66
    0x289003180100d803652080302c500b440748901920742e510f60070325078a030100d5849803240c4c1268420041403100300090f4050000d071008020300c039070160000549103050b0070240070f184c40c81449540305014030a00716401c000110111201100300040102c20003400300d0410a046c3c21024140c402c003a10380c0020502540b242000c00d00a1001e00c0c2281c031680d40c50400d82c41641e4020385040c80c00c0a0140100c40c1d8400072070010095400d000030720596034071103a01d00c0c5410602450031070f06840e104110b2074405026280030020405000c05c10b091320414151a280602d070ac0503805203c09407484990b10040808851b01c4800358209201500c0d910551403122709400e0046030078841103900b069002c00d02541400003035403c160080c03c4100b400300461001400f0308000c0740d041203103401041001d40c071070340990142c001040d600460540751101c4064a80230014240800300c1c1e204022000204503620101a20294903240204001000d480220325198080c011003100d0000001413004200060480710041d1 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 809883480 1250 809882230 809882243
    0x20105070f2a0b01140a0b03041b030f0c0302090711060f06040207060f0f06122604030204020712020601080a0b010312020f0618010b0109050d02040507030e010c230a0207290703020a 80
    0x900c00c0f4006d004c440030303103440780c588445001c0c80420f00080200c441c05e40b1088100072081e082c19030301d07110360700003110180c000e0701c0001046e2420b00a604020801d02d0b4881e043e42840c1074800f03400204507a54036401405509402482008200a9515501140c1d2000d4100704240a00c0f0f402c130306d6010003400001310191007a40340c0000001ca64902502c5200c0490300400c1c3c0020602c4d405c5070b001030718580341c000388525803410040400182c0c0d491003d03092150040c1f0000012104041c1c1c040e14100042e00900c801e58040b44051001900340c241407415241c2c40040600304002e18101a0f10305062802c00d0106030241901f0402c60355082d00000000c0c1020f4802400305040100041d02c40326124098603030000e042c403580e84090f00340358100d59000140d0b032074005401d1411602641c2160000300822001036105c00d00c0d9071010020b139680c8400a64940324141c0382002c2d010001e5650b204070303c58250400c071030120300d850310022503000031340c5032480c4034009917107003414034000b5221448480219a00c = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 809884730 1250 809883480 809883509
    0xa03020606030c10050a0c0201050702090708040b010819061a1807021204060806041e06090e07080303012607030206130305060a09051207020307090e01020405010807020105070f2a0b01 81
    0x2580341c40c266400744c034940da496443c0307804005042203805203200075042e81440f00411248005072180004607215500c150356042c01401c007880d00e1031039803506a001c0405c590101d4407044419002c0190700302040e0340007600140303038a94010103551041e031000c18a40c1c049a001240185c0900703071071406101d8a260780c281c854900c800503484205004900441e40004c030420000f900604156214080c1d8030064203460300d064820009180a481507604400051a2900100c0b20004010403455014000f1140a10308640c1400c071501e550780312144d90040e1400400410b45c400104c1404204003654000d015281d03600803000368689503c2c0d10b40300464003442028009141611684030316166181d0000c090270360059409401d6403241c010000c1a64140107023000061ba043d007034032804014011200000da216450000050590301e4001c280308150390401c400c0010143d8802c078560000503040c00e0150b0382292610701030003c9041082c22011003121414481c1c188000034400c01c1c101c520180c5603041c0d = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 809885980 1250 809884730 809884753
    0x321020307021504050109200a060801030f0209130501020f03160c03020a080c0c03030c010c030b0307032604150c060c11060a110c070f06032a0f110a0302060603 71
    0x200d00c0101d40d040010b80204035000107110415080c00d8104d030203030002060340c0c03149403100c07100d4503040760fa0844c90a8038460900014104240300341300401031800c0c502681e600d50344417194a201807000003480342c3d26040014400101e100c29045805420500841d245c080e600382c2c41c1b040303a009450480ea90060b040740c000780b043c89201d072512103d525601070001451160381d040020740107503168441a001d5607980d0201070b2010800780800741c0c03903407002081919a1000141c00c40d007081a07030320301076088090140045074400c0100445031402d000303c82d48001d5250001450f84c0280e8101c10307002852204001001a848044440e4942c01540c0c00c2040540707505003616568520040c000050300040001390440003141d04c02040e50001411151030640e1403070501e801e181d25500a409079158180041c4004d65261003484428807480c9082031642000c000328503c21600c8089600070000c1d20000b004080e481070701d90040c5200410102d60400c00c541c50080cad11102d044450b64000e100b0595110f0 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 809887230 1250 809885980 809886047
    0x5101103060d0209101e0e010f0806150109090c05071103190201050d0b0a1e05040b061c110d0606030e01050c0403031d030d120b0d0201050d020a1205010303 69
    0xa010703200c000c100407141140b540c00d000b250a4003e259945103c822800000d09140c0d409040c1c3c03420b480030304002c0c07100341400b030709852001c07068101410b840c0841d20184407580d8000344080d00300c4001c04100509641c2c007401220061505d030410003071b280c20b0941e00c50185400a001d014014410743c6a03c00c800049810f00d95210307a4060031200c0c10540002c1030000d5401207000701740d401c0352071401003000e50700d4101003458400254808a00000c1d0010204100c2d1021503116014040c116014042d041070400055540e005c1c01000400d510454421400b90007950342c00001c00f90b0301991556261705103220250028012440381c000440c0c106804042d90420609c2154442d402480501e4103150a64a0807030751082d0252054003031007441d513005280d66604002e011aa0045651080100f248441490050f150110005400340c5100e42000e00140c0c0c2081c1600c1280361071100050300c4260000707007222412038000b015201c0391300d810008000c0c0f6038009202c0500c0c01d500c1891030802c888825459 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 809888480 1250 809887230 809887237
    0x2040f080d02060606031503030c1c0801090b090a110910180b250201090902030907030c060c02010f030f020d0f091a0c03010e0604020f0d2a0516140a051011 69
    0x9605c880708000181c1c04464005451685200140851381400208802e180c60f01d411070841604000340901200061948410400e014002e8560309111030110640401c000c480040c10107204131b500c440a011010000a090702c0042d01c0040a00c404440b0000002e00b00c040280400e4000c0e201a00300130982da24810111104000c00414601d04014000c031002142c22941c2c20132070402c0100070000910040c0341c00514043d06060014148440c0385140291a070072941c1d018805009071007032110003503a00030007188840d050601b00841e43c01100040c5030f000748513210700300c01114a4041040782c66070382940480344582c89480d4000c00810750303591443e24008116aa40e17a0320344100014461000307001c80b05504104041c20140c10139103a04116401500442280b81c0341070380e41d402d070a116107a24090220400e04c08082d40c00100000b01005000344200c00c181034001d070b004160300d42006a0914140301c90900c41082c0c0707140403294680251144006102000c40d075003400290000d0b28400f4088 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 809889730 1250 809888480 809888491
    0x2d0f021f05180103090b0103080d2016050c030313083f0412080702040506010e0a2c0f0a0501230d170c070302031e0c010c0f050102040f080d0206 64
    0x101c034208640911250000b500c91040e0904054407500000c00042c05014014041d600c102c0055481d41d0110203c00216031400000b240102d0000301842030b552181c00481f005134003064404413010245050040c94200c80c8940c0c1e5400d84000610381d140d107030b00c07290101d0980303905034141c131071100d901c400c803a804511901e480c410b04e8080507441c0050b07030000a85260740e00800245582402d9903115014141c500a40c019503198034000381c250118a4540308980e80000c09090600b607544680001c201d51000c00e004081c040100014042b91038500d106048802607070718001480310b031614544145018009413a101d003580d06280c0081060003c03546200350304801c1e4508503145056541c10001c2100c113501054800034040c884424174815204000c24602c20402c00402516107544145490709004440e030b40c00c14401e4003001d05103040d01044584590401b440c06007001c0300796041404002c22a20700c000c1456100040014004c2c0504501c101115010b01c19a500e900002c1803d980b40c0030111071 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 809890980 1250 809889730 809889737
    0x2040f111215100f11070608060f030a08070804050306090a02011d01111507120605031203190204060c0c06050a0801051201090510050624072d0f021f 66
    0x1901c41c0e49821040d1070780e400400c55100151060308a004a007030400340b4007401d400654400f80444d40c41c0e0b0081000c5001034681401001c0e0207203030180003010040b0182806105016408028206680c2000348035a03480d00001d125646054515080b041c5600c103205650082c01601c0000b00030490128440b14215010707140c5412100d0140c00c00d2602c190f908103410b045c0214140000821001006038001e4224180303000d030440d003004030024103400d2400c400d4036001c60400d141808a81c4002c83c2d5041000c000d200390079200d40b500300540d880140c044130a00e0840c0c2c808603000500d954003041c80e40c05a030040511203405603c0e504104d03410b100345101c01020400a00040119091403a4660700c01001c0400000e0120841d82c1c1e40c6d410b000c24080d600c0c2c2e030192103006114941c64200070142c8080e518840083c5a2642c0d945080c1503030003001e002414034000c0c41c07086582d030441030314003444040003e10010a2201c40e40342032032001123004000da004412080203500501c51107016036403550303825203 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 809892086 1106 809890980 809890987
    0x14090a0311010b060d150e04240c080711030d110903010b0102011803031a090108010c0f0206130b130803070f11070e040b0907050a060c02040f11 64
    0x14a8880e07034905184411903035261811551081c4540c08040f51251030030703010340e01b0384400340d001002c1d501060040004110052850a840031741c80f0340742e440a00310030b07d1174808a50344900a04085284036011843d1103000701800c03803a1035030f000304492800110480d28010381c1d001c0300300c81c0214400805c9c940d2281c03400f13020b600803000c001e200812000244055200411414260140078107035648001000c60100341c1414048008c090a41c5a095075640010340c024041d00c1c03111340c0003030b1000c1c2c0c6200b545031000c0740c1603008607043e0325030f070208000c540c540300310404001e4043d4500450034030451001030480400b03144181801d40b142e03203603450f8540002c0d0000807071565817055600700304401c0c4480a41004125001604440d031541d860b540e40c82c10034584105070304056844080301c04006862a488100c81041c0781c420344041c081c405995401d10281ea030005d140c01250703c01131 = true := by decide +kernel

theorem cover : BRFrame.Cov 809712230 809892086 := by
  have h0 := BRFrame.cov_init 809712230
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809712230 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809712230 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809712230 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809712230 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809712230 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809712230 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809712230 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809712230 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809712230 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809712230 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809712230 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809712230 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809712230 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809712230 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809712230 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809712230 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809712230 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809712230 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809712230 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809712230 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809712230 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809712230 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809712230 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809712230 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809712230 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809712230 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809712230 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809712230 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809712230 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809712230 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809712230 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809712230 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809712230 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809712230 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809712230 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809712230 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809712230 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809712230 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809712230 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809712230 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809712230 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809712230 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809712230 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809712230 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809712230 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809712230 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809712230 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809712230 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809712230 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809712230 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809712230 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809712230 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809712230 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809712230 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809712230 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809712230 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809712230 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809712230 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809712230 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809712230 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809712230 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809712230 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809712230 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809712230 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809712230 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809712230 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809712230 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809712230 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809712230 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809712230 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809712230 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809712230 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809712230 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809712230 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809712230 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809712230 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809712230 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809712230 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809712230 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809712230 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809712230 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809712230 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809712230 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809712230 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809712230 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809712230 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809712230 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809712230 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809712230 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809712230 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809712230 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809712230 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809712230 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809712230 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809712230 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809712230 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809712230 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809712230 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809712230 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809712230 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809712230 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809712230 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809712230 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809712230 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809712230 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809712230 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809712230 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809712230 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809712230 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809712230 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809712230 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809712230 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809712230 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809712230 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809712230 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809712230 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809712230 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809712230 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809712230 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809712230 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809712230 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809712230 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809712230 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809712230 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809712230 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809712230 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809712230 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809712230 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809712230 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809712230 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809712230 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809712230 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809712230 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809712230 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809712230 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809712230 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809712230 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809712230 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809712230 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809712230 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809712230 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809712230 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809712230 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809712230 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 809712230 ≤ n) (h2 : n < 809892086) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
